(* ========================================================================= *)
(* Unit pc_p4_width: the elementary area and width facts of Part 4:          *)
(* nonnegativity and boundedness of slice areas (P4_CM_NONNEG_STATEMENT),    *)
(* areas under pinch maps (P4_PINCH_AREA_STATEMENT), isometry invariance of  *)
(* the width (P4_CM_ISOMETRY_STATEMENT), continuity of the width along a     *)
(* Ricci flow (P4_WIDTH_CONTINUITY_STATEMENT) and the second-order Taylor    *)
(* bound for slice areas (P4_AREA_TAYLOR_STATEMENT).                         *)
(*                                                                           *)
(* First the algebra of e2 (the second elementary symmetric function) and of *)
(* its polarization on positive semidefinite matrices (library               *)
(* positive_semidefinite of Multivariate/determinants.ml).                   *)
(* ========================================================================= *)

needs "src/pc_p4_defs.ml";;
needs "src/pc_grg_isom.ml";;
needs "src/pc_mfd_diff.ml";;

prioritize_real();;
type_invention_error := true;;

let P4_E2_PSD = prove
 (`!A:real^3^3. positive_semidefinite A ==> &0 <= p4_e2 A`,
  GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP TRACE_SQUARE_POSITIVE_SEMIDEFINITE_LE) THEN
  REWRITE_TAC[p4_e2] THEN REAL_ARITH_TAC);;

let P4_E2_POL_PSD = prove
 (`!A B:real^3^3.
        positive_semidefinite A /\ positive_semidefinite B
        ==> &0 <= p4_e2_pol A B`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP TRACE_MUL_POSITIVE_SEMIDEFINITE_LE) THEN
  REWRITE_TAC[p4_e2_pol] THEN REAL_ARITH_TAC);;

let P4_E2_POL_ADD = prove
 (`!a b c:real^3^3. p4_e2_pol a (b + c) = p4_e2_pol a b + p4_e2_pol a c`,
  REWRITE_TAC[p4_e2_pol; TRACE_ADD; MATRIX_ADD_LDISTRIB] THEN REAL_ARITH_TAC);;

let P4_E2_POL_SUB = prove
 (`!a b c:real^3^3. p4_e2_pol a (b - c) = p4_e2_pol a b - p4_e2_pol a c`,
  REWRITE_TAC[p4_e2_pol; TRACE_SUB; MATRIX_SUB_LDISTRIB] THEN REAL_ARITH_TAC);;

let P4_E2_POL_CMUL = prove
 (`!a b:real^3^3 k. p4_e2_pol a (k %% b) = k * p4_e2_pol a b`,
  REWRITE_TAC[p4_e2_pol; TRACE_CMUL; MATRIX_MUL_RMUL] THEN REAL_ARITH_TAC);;

let P4_E2_POL_LCMUL = prove
 (`!a b:real^3^3 k. p4_e2_pol (k %% a) b = k * p4_e2_pol a b`,
  REWRITE_TAC[p4_e2_pol; TRACE_CMUL; MATRIX_MUL_LMUL] THEN REAL_ARITH_TAC);;

let P4_E2_POL_REFL = prove
 (`!a:real^3^3. p4_e2_pol a a = &2 * p4_e2 a`,
  REWRITE_TAC[p4_e2_pol; p4_e2] THEN REAL_ARITH_TAC);;

let P4_E2_SUB = prove
 (`!a b:real^3^3. p4_e2(a - b) = p4_e2 a - p4_e2_pol a b + p4_e2 b`,
  REWRITE_TAC[p4_e2; p4_e2_pol; TRACE_SUB; MATRIX_SUB_LDISTRIB;
              MATRIX_SUB_RDISTRIB; TRACE_MUL_SYM] THEN REAL_ARITH_TAC);;

(* Monotonicity of e2 in the Loewner order. *)

let P4_E2_MONO = prove
 (`!A B:real^3^3.
        positive_semidefinite A /\ positive_semidefinite(B - A)
        ==> p4_e2 A <= p4_e2 B`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `B:real^3^3 = A + (B - A)` SUBST1_TAC THENL
   [MATRIX_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[P4_E2_ADD; REAL_ARITH `a <= a + b + c <=> &0 <= b + c`] THEN
  MATCH_MP_TAC REAL_LE_ADD THEN
  ASM_SIMP_TAC[P4_E2_POL_PSD; P4_E2_PSD]);;

(* Quadratic-form bounds: if |v.Bv| <= C v.Av for a positive semidefinite  *)
(* A and a symmetric B, then |e2_pol(A,B)| <= 2C e2(A) and                  *)
(* |e2(B)| <= 3 C^2 e2(A) (A +/- B/C lie between 0 and 2A).                 *)

let P4_E2_BOUNDS_1 = prove
 (`!A D:real^3^3.
        positive_semidefinite A /\ symmetric_matrix D /\
        (!v. abs(v dot (D ** v)) <= v dot (A ** v))
        ==> abs(p4_e2_pol A D) <= &2 * p4_e2 A /\
            abs(p4_e2 D) <= &3 * p4_e2 A`,
  REPEAT GEN_TAC THEN REWRITE_TAC[positive_semidefinite; symmetric_matrix] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `positive_semidefinite(A + D:real^3^3) /\ positive_semidefinite(A - D:real^3^3) /\
    positive_semidefinite(&2 %% A - (A + D):real^3^3) /\
    positive_semidefinite(&2 %% A - (A - D):real^3^3)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[positive_semidefinite; symmetric_matrix] THEN
    ASM_REWRITE_TAC[TRANSP_MATRIX_ADD; TRANSP_MATRIX_SUB; TRANSP_MATRIX_CMUL] THEN
    REWRITE_TAC[MATRIX_VECTOR_MUL_ADD_RDISTRIB; MATRIX_VECTOR_MUL_SUB_RDISTRIB;
                MATRIX_VECTOR_LMUL; DOT_RADD; DOT_RSUB; DOT_RMUL] THEN
    REPEAT CONJ_TAC THEN X_GEN_TAC `v:real^3` THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `v:real^3`)) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `positive_semidefinite(A:real^3^3)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[positive_semidefinite; symmetric_matrix]; ALL_TAC] THEN
  MP_TAC(ISPECL [`A + D:real^3^3`; `&2 %% A:real^3^3`] P4_E2_MONO) THEN
  MP_TAC(ISPECL [`A - D:real^3^3`; `&2 %% A:real^3^3`] P4_E2_MONO) THEN
  MP_TAC(ISPEC `A + D:real^3^3` P4_E2_PSD) THEN
  MP_TAC(ISPEC `A - D:real^3^3` P4_E2_PSD) THEN
  MP_TAC(ISPEC `A:real^3^3` P4_E2_PSD) THEN
  ASM_REWRITE_TAC[P4_E2_ADD; P4_E2_SUB; P4_E2_CMUL] THEN
  REWRITE_TAC[REAL_ARITH `&2 pow 2 = &4`] THEN REAL_ARITH_TAC);;

let P4_E2_BOUNDS = prove
 (`!A B:real^3^3 C.
        positive_semidefinite A /\ symmetric_matrix B /\ &0 <= C /\
        (!v. abs(v dot (B ** v)) <= C * (v dot (A ** v)))
        ==> abs(p4_e2_pol A B) <= &2 * C * p4_e2 A /\
            abs(p4_e2 B) <= &3 * C pow 2 * p4_e2 A`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= p4_e2(A:real^3^3)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[P4_E2_PSD]; ALL_TAC] THEN
  ASM_CASES_TAC `C = &0` THENL
   [SUBGOAL_THEN `B:real^3^3 = mat 0` SUBST1_TAC THENL
     [RULE_ASSUM_TAC(REWRITE_RULE[symmetric_matrix]) THEN
      MP_TAC(ISPEC `B:real^3^3` POSITIVE_SEMIDEFINITE_ANTISYM) THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      REWRITE_TAC[positive_semidefinite; symmetric_matrix; TRANSP_MATRIX_NEG] THEN
      ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_LNEG; DOT_RNEG] THEN
      CONJ_TAC THEN X_GEN_TAC `v:real^3` THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `v:real^3`) THEN ASM_REWRITE_TAC[REAL_MUL_LZERO] THEN
      REAL_ARITH_TAC;
      REWRITE_TAC[p4_e2; p4_e2_pol; MATRIX_MUL_LZERO; MATRIX_MUL_RZERO;
                  TRACE_0] THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < C` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`A:real^3^3`; `inv C %% B:real^3^3`] P4_E2_BOUNDS_1) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [RULE_ASSUM_TAC(REWRITE_RULE[symmetric_matrix]) THEN
      ASM_REWRITE_TAC[symmetric_matrix; TRANSP_MATRIX_CMUL];
      ALL_TAC] THEN
    X_GEN_TAC `v:real^3` THEN
    REWRITE_TAC[MATRIX_VECTOR_LMUL; DOT_RMUL; REAL_ABS_MUL; REAL_ABS_INV] THEN
    SUBGOAL_THEN `abs C = C` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `inv C * C * (v dot ((A:real^3^3) ** v))` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE];
      ASM_SIMP_TAC[REAL_MUL_ASSOC; REAL_MUL_LINV; REAL_LT_IMP_NZ; REAL_MUL_LID;
                   REAL_LE_REFL]];
    ALL_TAC] THEN
  REWRITE_TAC[P4_E2_POL_CMUL; P4_E2_CMUL; REAL_ABS_MUL; REAL_ABS_POW;
              REAL_ABS_INV] THEN
  SUBGOAL_THEN `abs C = C` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_POW_INV] THEN STRIP_TAC THEN CONJ_TAC THENL
   [SUBGOAL_THEN `abs(p4_e2_pol A (B:real^3^3)) = C * (inv C * abs(p4_e2_pol A B))`
    SUBST1_TAC THENL
     [ASM_SIMP_TAC[REAL_MUL_ASSOC; REAL_MUL_RINV; REAL_LT_IMP_NZ; REAL_MUL_LID];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `C * &2 * p4_e2(A:real^3^3)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; REAL_ARITH_TAC];
    SUBGOAL_THEN `abs(p4_e2(B:real^3^3)) = C pow 2 * (inv(C pow 2) * abs(p4_e2 B))`
    SUBST1_TAC THENL
     [ASM_SIMP_TAC[REAL_MUL_ASSOC; REAL_MUL_RINV; REAL_POW_NZ; REAL_LT_IMP_NZ;
                   REAL_MUL_LID];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `C pow 2 * &3 * p4_e2(A:real^3^3)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2]; REAL_ARITH_TAC]]);;

(* ========================================================================= *)
(* Radial composites, chart independence of the Gram matrix                  *)
(* (P4_S2_JAC_CHART, P4_S2_GRAM_CHART), slices of sweepouts (P4_SWEEP_C1),  *)
(* continuity of matrix expressions and of e2, and joint continuity of the  *)
(* slice Gram matrices on S^2 x [0,1] (P4_SWEEP_GRAM_CONT).                 *)
(* ========================================================================= *)

let P4_RADIAL_SPHERE = prove
 (`!z:real^3. ~(z = vec 0) ==> inv(norm z) % z IN sphere(vec 0,&1)`,
  SIMP_TAC[IN_SPHERE_0; NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM; REAL_MUL_LINV;
           NORM_EQ_0]);;

let P4_RADIAL_FIX = prove
 (`!y:real^3. y IN sphere(vec 0,&1) ==> inv(norm y) % y = y`,
  SIMP_TAC[IN_SPHERE_0; REAL_INV_1; VECTOR_MUL_LID]);;

let P4_SPHERE_NONZERO = prove
 (`!y:real^3. y IN sphere(vec 0,&1) ==> ~(y = vec 0)`,
  GEN_TAC THEN REWRITE_TAC[IN_SPHERE_0] THEN
  MESON_TAC[NORM_0; REAL_ARITH `~(&0 = &1)`]);;

let P4_RADIAL_CONTINUOUS = prove
 (`(\z:real^3. inv(norm z) % z) continuous_on ((:real^3) DIFF {vec 0})`,
  MATCH_MP_TAC CONTINUOUS_ON_MUL THEN REWRITE_TAC[CONTINUOUS_ON_ID] THEN
  SUBGOAL_THEN `(lift o (\z:real^3. inv(norm z))) = lift o inv o norm`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_INV THEN REWRITE_TAC[CONTINUOUS_ON_LIFT_NORM] THEN
  SIMP_TAC[IN_DIFF; IN_SING; NORM_EQ_0]);;

let P4_RADIAL_COMPOSE = prove
 (`!top (u:real^3->A).
        continuous_map (subtopology euclidean (sphere(vec 0,&1)),top) u
        ==> continuous_map (subtopology euclidean ((:real^3) DIFF {vec 0}),top)
                           (\z. u(inv(norm z) % z))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\z:real^3. (u:real^3->A)(inv(norm z) % z)) =
                u o (\z. inv(norm z) % z)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
  EXISTS_TAC `subtopology euclidean (sphere(vec 0:real^3,&1))` THEN
  ASM_REWRITE_TAC[CONTINUOUS_MAP_EUCLIDEAN2; P4_RADIAL_CONTINUOUS] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_DIFF; IN_SING; IN_UNIV] THEN
  SIMP_TAC[P4_RADIAL_SPHERE]);;

let P4_RADIAL_CHART_OPEN = prove
 (`!top atlas (u:real^3->A) (c:(A->bool)#(A->real^N)).
        smooth_manifold_atlas top atlas /\ c IN atlas /\
        continuous_map (subtopology euclidean (sphere(vec 0,&1)),top) u
        ==> open {z:real^3 | ~(z = vec 0) /\ u(inv(norm z) % z) IN FST c}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC OPEN_IN_OPEN_TRANS THEN
  EXISTS_TAC `(:real^3) DIFF {vec 0}` THEN
  SIMP_TAC[OPEN_DIFF; OPEN_UNIV; CLOSED_SING] THEN
  MP_TAC(ISPECL [`\z:real^3. (u:real^3->A)(inv(norm z) % z)`;
                 `subtopology euclidean ((:real^3) DIFF {vec 0})`; `top:A topology`;
                 `FST(c:(A->bool)#(A->real^N))`] OPEN_IN_CONTINUOUS_MAP_PREIMAGE) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[P4_RADIAL_COMPOSE] THEN ASM_MESON_TAC[GRGD_ATLAS_CHART];
    REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY; IN_DIFF; IN_UNIV; IN_SING]]);;

(* Points of the sphere lie in topspace; the radial composite near y. *)

let P4_S2_IN_TOPSPACE = prove
 (`!top (u:real^3->A) y.
        continuous_map (subtopology euclidean (sphere(vec 0,&1)),top) u /\
        y IN sphere(vec 0,&1)
        ==> u y IN topspace top`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP CONTINUOUS_MAP_IMAGE_SUBSET_TOPSPACE) THEN
  REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN ASM SET_TAC[]);;

let P4_RADIAL_BALL = prove
 (`!top atlas (u:real^3->A) (U:A->bool) (phi:A->real^N) V (psi:A->real^N) y.
        smooth_manifold_atlas top atlas /\ (U,phi) IN atlas /\ (V,psi) IN atlas /\
        continuous_map (subtopology euclidean (sphere(vec 0,&1)),top) u /\
        y IN sphere(vec 0,&1) /\ u y IN U /\ u y IN V
        ==> ?d. &0 < d /\
                !z. dist(z,y) < d
                    ==> ~(z = vec 0) /\ u(inv(norm z) % z) IN U /\
                        u(inv(norm z) % z) IN V`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `u:real^3->A`; `(U:A->bool,phi:A->real^N)`] P4_RADIAL_CHART_OPEN) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `u:real^3->A`; `(V:A->bool,psi:A->real^N)`] P4_RADIAL_CHART_OPEN) THEN
  ASM_REWRITE_TAC[FST; IMP_IMP] THEN DISCH_THEN(MP_TAC o MATCH_MP OPEN_INTER) THEN
  REWRITE_TAC[OPEN_CONTAINS_BALL] THEN DISCH_THEN(MP_TAC o SPEC `y:real^3`) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN
    ASM_SIMP_TAC[P4_SPHERE_NONZERO; P4_RADIAL_FIX];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN
  REWRITE_TAC[SUBSET; IN_BALL; IN_INTER; IN_ELIM_THM] THEN
  MESON_TAC[DIST_SYM]);;

(* The preferred-chart Jacobian through any chart containing u y. *)

let P4_S2_JAC_CHART = prove
 (`!top atlas (u:real^3->A) (U:A->bool) (phi:A->real^N) y.
        smooth_manifold_atlas top atlas /\ (U,phi) IN atlas /\
        continuous_map (subtopology euclidean (sphere(vec 0,&1)),top) u /\
        y IN sphere(vec 0,&1) /\ u y IN U /\
        (\z. phi(u(inv(norm z) % z))) differentiable (at y)
        ==> ((\z. SND (chart_at atlas (u y)) (u(inv(norm z) % z))) has_derivative
             (chart_jac (U,phi) (chart_at atlas (u y)) (u y) o
              frechet_derivative (\z. phi(u(inv(norm z) % z))) (at y))) (at y) /\
            p4_s2_jac atlas u y =
            matrix(chart_jac (U,phi) (chart_at atlas (u y)) (u y)) **
            jacobian (\z. phi(u(inv(norm z) % z))) (at y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(u:real^3->A) y IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[P4_S2_IN_TOPSPACE]; ALL_TAC] THEN
  MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                `(u:real^3->A) y`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `chart_at (atlas:((A->bool)#(A->real^N))->bool) ((u:real^3->A) y)`
               PAIR_SURJECTIVE) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`V:A->bool`; `psi:A->real^N`] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th] THEN ASSUME_TAC th) THEN
  REWRITE_TAC[FST; SND] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `((\z. (psi:A->real^N)((u:real^3->A)(inv(norm z) % z))) has_derivative
     (chart_jac (U,phi) (V,psi) (u y) o
      frechet_derivative (\z. (phi:A->real^N)(u(inv(norm z) % z))) (at y))) (at y)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_AT THEN
    EXISTS_TAC `chart_trans (U:A->bool,phi:A->real^N) (V,psi) o
                (\z. phi((u:real^3->A)(inv(norm z) % z)))` THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `u:real^3->A`; `U:A->bool`; `phi:A->real^N`; `V:A->bool`;
                   `psi:A->real^N`; `y:real^3`] P4_RADIAL_BALL) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN
      MATCH_MP_TAC CHART_TRANS_AT THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
      ASM_MESON_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC DIFF_CHAIN_AT THEN
    ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
    ASM_SIMP_TAC[P4_RADIAL_FIX] THEN
    MATCH_MP_TAC CHART_TRANS_HAS_DERIVATIVE THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
    ASM_REWRITE_TAC[IN_INTER];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[p4_s2_jac; SND; jacobian] THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
  MATCH_MP_TAC MATRIX_COMPOSE THEN CONJ_TAC THENL
   [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC CHART_JAC_LINEAR THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
    ASM_REWRITE_TAC[IN_INTER]]);;

let P4_S2_GRAM_CHART = prove
 (`!top atlas (Q:A->real^N^N) (u:real^3->A) (U:A->bool) (phi:A->real^N) y.
        smooth_manifold_atlas top atlas /\ (U,phi) IN atlas /\
        continuous_map (subtopology euclidean (sphere(vec 0,&1)),top) u /\
        y IN sphere(vec 0,&1) /\ u y IN U /\
        (\z. phi(u(inv(norm z) % z))) differentiable (at y)
        ==> p4_s2_gram atlas Q u y =
            transp(jacobian (\z. phi(u(inv(norm z) % z))) (at y)) **
            metric_local atlas (U,phi) Q (phi(u y)) **
            jacobian (\z. phi(u(inv(norm z) % z))) (at y)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `u:real^3->A`; `U:A->bool`; `phi:A->real^N`; `y:real^3`]
                P4_S2_JAC_CHART) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT2) THEN
  ASM_REWRITE_TAC[p4_s2_gram; metric_local] THEN BETA_TAC THEN
  SUBGOAL_THEN `chart_inv (U:A->bool,phi:A->real^N) (phi((u:real^3->A) y)) = u y`
  SUBST1_TAC THENL
   [MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                  `U:A->bool`; `phi:A->real^N`] CHART_INV) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[MATRIX_TRANSP_MUL; MATRIX_MUL_ASSOC]);;

(* ------------------------------------------------------------------------- *)
(* Slices of sweepouts: continuity, and derivatives of the radial chart      *)
(* composites from the joint C^1 condition.                                  *)
(* ------------------------------------------------------------------------- *)

let P4_SWEEP_SLICE_CONT = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (sigma:real^3->real->A) t.
        p4_sweepout (top,atlas) sigma /\ t IN real_interval[&0,&1]
        ==> continuous_map (subtopology euclidean (sphere(vec 0,&1)),top)
                           (\y. sigma y t)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\y. (sigma:real^3->real->A) y t) =
                (\(y,t). sigma y t) o (\y:real^3. (y,t:real))` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
  EXISTS_TAC `prod_topology (subtopology euclidean (sphere(vec 0:real^3,&1)))
                            (subtopology euclideanreal (real_interval[&0,&1]))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[CONTINUOUS_MAP_PAIRWISE; o_DEF; CONTINUOUS_MAP_ID] THEN
    REWRITE_TAC[CONTINUOUS_MAP_CONST; TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY] THEN
    ASM_REWRITE_TAC[];
    ASM_MESON_TAC[p4_sweepout]]);;

let P4_SWEEP_C1 = prove
 (`!top atlas (sigma:real^3->real->A) (U:A->bool) (phi:A->real^N).
        smooth_manifold_atlas top atlas /\ p4_sweepout (top,atlas) sigma /\
        (U,phi) IN atlas
        ==> ?f':real^(3,1)finite_sum->real^(3,1)finite_sum->real^N.
                 (!y t. y IN sphere(vec 0,&1) /\ t IN real_interval[&0,&1] /\
                        sigma y t IN U
                        ==> ((\z. phi(sigma (inv(norm z) % z) t)) has_derivative
                             (\h. f' (pastecart y (lift t)) (pastecart h (vec 0))))
                            (at y)) /\
                 (!x. x IN {x | ~(fstcart x = vec 0) /\
                                drop(sndcart x) IN real_interval[&0,&1] /\
                                sigma (inv(norm(fstcart x)) % fstcart x) (drop(sndcart x))
                                IN U}
                      ==> linear(f' x)) /\
                 (!h. (\x. f' x h) continuous_on
                      {x | ~(fstcart x = vec 0) /\
                           drop(sndcart x) IN real_interval[&0,&1] /\
                           sigma (inv(norm(fstcart x)) % fstcart x) (drop(sndcart x))
                           IN U}) /\
                 (\x. phi(sigma (inv(norm(fstcart x)) % fstcart x) (drop(sndcart x))))
                 continuous_on
                      {x | ~(fstcart x = vec 0) /\
                           drop(sndcart x) IN real_interval[&0,&1] /\
                           sigma (inv(norm(fstcart x)) % fstcart x) (drop(sndcart x))
                           IN U}`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `(U:A->bool,phi:A->real^N)` o CONJUNCT2 o CONJUNCT2 o
    GEN_REWRITE_RULE I [p4_sweepout]) THEN
  ASM_REWRITE_TAC[FST; SND] THEN
  DISCH_THEN(fun th ->
    ASSUME_TAC(MATCH_MP CONTINUOUSLY_DIFFERENTIABLE_IMP_CONTINUOUS_ON th) THEN
    MP_TAC(REWRITE_RULE[CONTINUOUSLY_DIFFERENTIABLE_1] th)) THEN
  DISCH_THEN(X_CHOOSE_THEN
    `f':real^(3,1)finite_sum->real^(3,1)finite_sum->real^N` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `f':real^(3,1)finite_sum->real^(3,1)finite_sum->real^N` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ALL_TAC; ASM_MESON_TAC[has_derivative]] THEN
  MAP_EVERY X_GEN_TAC [`y:real^3`; `t:real`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `continuous_map (subtopology euclidean (sphere(vec 0,&1)),top)
                               (\y. (sigma:real^3->real->A) y t)`
  ASSUME_TAC THENL [ASM_MESON_TAC[P4_SWEEP_SLICE_CONT]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `\y. (sigma:real^3->real->A) y t`; `U:A->bool`; `phi:A->real^N`;
                 `U:A->bool`; `phi:A->real^N`; `y:real^3`] P4_RADIAL_BALL) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `(\z. (phi:A->real^N)((sigma:real^3->real->A) (inv(norm z) % z) t)) =
    (\x. phi(sigma (inv(norm(fstcart x)) % fstcart x) (drop(sndcart x)))) o
    (\z:real^3. pastecart z (lift t))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\h. (f':real^(3,1)finite_sum->real^(3,1)finite_sum->real^N)
           (pastecart y (lift t)) (pastecart h (vec 0))) =
    f' (pastecart y (lift t)) o (\h:real^3. pastecart h (vec 0))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MP_TAC(ISPECL
   [`(\x. (phi:A->real^N)((sigma:real^3->real->A) (inv(norm(fstcart x)) % fstcart x)
                                                (drop(sndcart x)))) o
     (\z:real^3. pastecart z (lift t))`;
    `(f':real^(3,1)finite_sum->real^(3,1)finite_sum->real^N) (pastecart y (lift t)) o
     (\h:real^3. pastecart h (vec 0))`;
    `y:real^3`; `ball(y:real^3,d)`] HAS_DERIVATIVE_WITHIN_OPEN) THEN
  ASM_REWRITE_TAC[OPEN_BALL; CENTRE_IN_BALL] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC DIFF_CHAIN_WITHIN THEN BETA_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC HAS_DERIVATIVE_AT_WITHIN THEN
    MATCH_MP_TAC HAS_DERIVATIVE_PASTECART THEN
    REWRITE_TAC[HAS_DERIVATIVE_ID; HAS_DERIVATIVE_CONST];
    ALL_TAC] THEN
  MATCH_MP_TAC HAS_DERIVATIVE_WITHIN_SUBSET THEN
  EXISTS_TAC
   `{x | ~(fstcart x = vec 0) /\ drop(sndcart x) IN real_interval[&0,&1] /\
         (sigma:real^3->real->A) (inv(norm(fstcart x)) % fstcart x) (drop(sndcart x))
         IN U}` THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[IN_ELIM_THM; FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
    ASM_SIMP_TAC[P4_SPHERE_NONZERO; P4_RADIAL_FIX];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_BALL; IN_ELIM_THM; FSTCART_PASTECART;
                SNDCART_PASTECART; LIFT_DROP] THEN
    ASM_MESON_TAC[DIST_SYM]]);;

(* ------------------------------------------------------------------------- *)
(* Continuity of matrix expressions (through vectorize) and of e2.          *)
(* ------------------------------------------------------------------------- *)

let P4_TRANSP_CONTINUOUS = prove
 (`!(A:real^P->real^N^M) s.
        (\x. vectorize(A x)) continuous_on s
        ==> (\x. vectorize(transp(A x))) continuous_on s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CONTINUOUS_ON_VECTORIZE_COMPONENTWISE] THEN
  DISCH_TAC THEN MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
  REWRITE_TAC[TRANSP_COMPONENT] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[]);;

let P4_GRAM_CONTINUOUS = prove
 (`!(J:real^P->real^3^N) (G:real^P->real^N^N) s.
        (\x. vectorize(J x)) continuous_on s /\
        (\x. vectorize(G x)) continuous_on s
        ==> (\x. vectorize(transp(J x) ** G x ** J x)) continuous_on s`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC CONTINUOUS_ON_MATRIX_MUL THEN REWRITE_TAC[o_DEF] THEN
  ASM_SIMP_TAC[P4_TRANSP_CONTINUOUS] THEN
  MATCH_MP_TAC CONTINUOUS_ON_MATRIX_MUL THEN ASM_REWRITE_TAC[o_DEF]);;

let P4_TRACE_CONTINUOUS = prove
 (`!(A:real^P->real^N^N) s.
        (\x. vectorize(A x)) continuous_on s
        ==> (\x. lift(trace(A x))) continuous_on s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CONTINUOUS_ON_VECTORIZE_COMPONENTWISE] THEN
  DISCH_TAC THEN REWRITE_TAC[trace; LIFT_SUM; o_DEF] THEN
  MATCH_MP_TAC CONTINUOUS_ON_VSUM THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN BETA_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let P4_E2_CONTINUOUS = prove
 (`!(A:real^P->real^3^3) s.
        (\x. vectorize(A x)) continuous_on s
        ==> (\x. lift(p4_e2(A x))) continuous_on s`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `(\x. lift(p4_e2((A:real^P->real^3^3) x))) =
    (\x. inv(&2) % (lift(trace(A x) pow 2) - lift(trace(A x ** A x))))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; p4_e2; GSYM LIFT_SUB; GSYM LIFT_CMUL] THEN
    GEN_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN MATCH_MP_TAC CONTINUOUS_ON_SUB THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_LIFT_POW THEN ASM_SIMP_TAC[P4_TRACE_CONTINUOUS];
    MATCH_MP_TAC P4_TRACE_CONTINUOUS THEN
    MATCH_MP_TAC CONTINUOUS_ON_MATRIX_MUL THEN ASM_REWRITE_TAC[o_DEF]]);;

let P4_E2_POL_CONTINUOUS = prove
 (`!(A:real^P->real^3^3) B s.
        (\x. vectorize(A x)) continuous_on s /\
        (\x. vectorize(B x)) continuous_on s
        ==> (\x. lift(p4_e2_pol (A x) (B x))) continuous_on s`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `(\x. lift(p4_e2_pol ((A:real^P->real^3^3) x) (B x))) =
    (\x. trace(A x) % lift(trace(B x)) - lift(trace(A x ** B x)))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; p4_e2_pol; LIFT_SUB; LIFT_CMUL]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_SUB THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
    ASM_SIMP_TAC[P4_TRACE_CONTINUOUS; o_DEF];
    MATCH_MP_TAC P4_TRACE_CONTINUOUS THEN
    MATCH_MP_TAC CONTINUOUS_ON_MATRIX_MUL THEN ASM_REWRITE_TAC[o_DEF]]);;

(* A function dominated by a nonnegative continuous g, and continuous where *)
(* g does not vanish, is continuous.                                        *)

let P4_CONT_DOMINATED = prove
 (`!(f:real^P->real) g s.
        (\x. lift(g x)) continuous_on s /\
        (!x. x IN s ==> abs(f x) <= g x) /\
        (!x. x IN s /\ ~(g x = &0) ==> (\x. lift(f x)) continuous (at x within s))
        ==> (\x. lift(f x)) continuous_on s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "gc")
    (CONJUNCTS_THEN2 (LABEL_TAC "dom") (LABEL_TAC "fc"))) THEN
  X_GEN_TAC `x:real^P` THEN DISCH_TAC THEN
  ASM_CASES_TAC `(g:real^P->real) x = &0` THENL
   [ALL_TAC; USE_THEN "fc" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]] THEN
  SUBGOAL_THEN `(f:real^P->real) x = &0` ASSUME_TAC THENL
   [USE_THEN "dom" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(x:real^P) IN s`))) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[continuous_within] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  USE_THEN "gc" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(x:real^P) IN s`))) THEN
  REWRITE_TAC[continuous_within] THEN
  DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN
  REWRITE_TAC[DIST_LIFT] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `y:real^P` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `y:real^P`) THEN ASM_REWRITE_TAC[] THEN
  USE_THEN "dom" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(y:real^P) IN s`))) THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The parameter set S^2 x [0,1] of a sweepout as a compact subset of        *)
(* real^(3,1)finite_sum, and joint continuity of slice Gram matrices.        *)
(* ------------------------------------------------------------------------- *)

let P4_IN_SLAB = prove
 (`!x:real^(3,1)finite_sum.
        x IN sphere(vec 0,&1) PCROSS interval[vec 0,vec 1] <=>
        fstcart x IN sphere(vec 0,&1) /\ drop(sndcart x) IN real_interval[&0,&1]`,
  GEN_TAC THEN GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [GSYM PASTECART_FST_SND] THEN
  REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; IN_REAL_INTERVAL; DROP_VEC]);;

let P4_SLAB_COMPACT = prove
 (`compact(sphere(vec 0:real^3,&1) PCROSS interval[vec 0:real^1,vec 1])`,
  SIMP_TAC[COMPACT_PCROSS; COMPACT_SPHERE; COMPACT_INTERVAL]);;

let P4_SWEEP_CONTK = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (sigma:real^3->real->A).
        p4_sweepout (top,atlas) sigma
        ==> continuous_map
              (subtopology euclidean (sphere(vec 0,&1) PCROSS interval[vec 0,vec 1]),
               top)
              (\x. sigma (fstcart x) (drop(sndcart x)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `(\x. (sigma:real^3->real->A) (fstcart x) (drop(sndcart x))) =
    (\(y,t). sigma y t) o (\x:real^(3,1)finite_sum. (fstcart x, drop(sndcart x)))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
  EXISTS_TAC `prod_topology (subtopology euclidean (sphere(vec 0:real^3,&1)))
                            (subtopology euclideanreal (real_interval[&0,&1]))` THEN
  CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[p4_sweepout]] THEN
  REWRITE_TAC[CONTINUOUS_MAP_PAIRWISE; o_DEF; FST; SND] THEN CONJ_TAC THENL
   [REWRITE_TAC[CONTINUOUS_MAP_EUCLIDEAN2; ETA_AX] THEN
    SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_FSTCART] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; P4_IN_SLAB] THEN SIMP_TAC[];
    REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY; CONTINUOUS_MAP_EQ_LIFT] THEN
    REWRITE_TAC[o_DEF; LIFT_DROP; CONTINUOUS_MAP_EUCLIDEAN; ETA_AX] THEN
    SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_SNDCART] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; P4_IN_SLAB;
                TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
    SIMP_TAC[]]);;

let P4_SWEEP_GRAM_CONT = prove
 (`!top atlas (Q:A->real^N^N) (sigma:real^3->real->A).
        smooth_manifold_atlas top atlas /\ p4_sweepout (top,atlas) sigma /\
        (!c. c IN atlas
             ==> (\w. vectorize(metric_local atlas c Q w)) continuous_on
                 IMAGE (SND c) (FST c))
        ==> (\x. vectorize(p4_s2_gram atlas Q (\y. sigma y (drop(sndcart x)))
                                      (fstcart x)))
            continuous_on (sphere(vec 0,&1) PCROSS interval[vec 0,vec 1])`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
  X_GEN_TAC `x0:real^(3,1)finite_sum` THEN DISCH_TAC THEN
  SUBGOAL_THEN `continuous_map
                 (subtopology euclidean (sphere(vec 0,&1) PCROSS interval[vec 0,vec 1]),
                  top)
                 (\x. (sigma:real^3->real->A) (fstcart x) (drop(sndcart x)))`
  ASSUME_TAC THENL [ASM_MESON_TAC[P4_SWEEP_CONTK]; ALL_TAC] THEN
  SUBGOAL_THEN `(sigma:real^3->real->A) (fstcart x0) (drop(sndcart x0)) IN topspace top`
  ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP CONTINUOUS_MAP_IMAGE_SUBSET_TOPSPACE) THEN
    REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                `(sigma:real^3->real->A) (fstcart x0) (drop(sndcart x0))`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `chart_at (atlas:((A->bool)#(A->real^N))->bool)
                 ((sigma:real^3->real->A) (fstcart x0) (drop(sndcart x0)))`
               PAIR_SURJECTIVE) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`U:A->bool`; `phi:A->real^N`] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[FST] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `sigma:real^3->real->A`; `U:A->bool`; `phi:A->real^N`] P4_SWEEP_C1) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC
   `S = {x:real^(3,1)finite_sum | ~(fstcart x = vec 0) /\
                                  drop(sndcart x) IN real_interval[&0,&1] /\
                                  (sigma:real^3->real->A)
                                    (inv(norm(fstcart x)) % fstcart x)
                                    (drop(sndcart x)) IN U}` THEN
  DISCH_THEN(X_CHOOSE_THEN `f':real^(3,1)finite_sum->real^(3,1)finite_sum->real^N`
    (CONJUNCTS_THEN2 (LABEL_TAC "der") (CONJUNCTS_THEN2 (LABEL_TAC "lin")
      (CONJUNCTS_THEN2 (LABEL_TAC "fc") (LABEL_TAC "Fc"))))) THEN
  ABBREV_TAC
   `J = \x. matrix(\h. (f':real^(3,1)finite_sum->real^(3,1)finite_sum->real^N) x
                         (pastecart h (vec 0)))` THEN
  ABBREV_TAC
   `H = \x. transp((J:real^(3,1)finite_sum->real^3^N) x) **
            metric_local atlas (U,phi) (Q:A->real^N^N)
              ((phi:A->real^N)((sigma:real^3->real->A)
                  (inv(norm(fstcart x)) % fstcart x) (drop(sndcart x)))) **
            J x` THEN
  (* A: H is continuous on S *)
  SUBGOAL_THEN `(\x. vectorize((H:real^(3,1)finite_sum->real^3^3) x)) continuous_on S`
  ASSUME_TAC THENL
   [EXPAND_TAC "H" THEN MATCH_MP_TAC P4_GRAM_CONTINUOUS THEN CONJ_TAC THENL
     [REWRITE_TAC[GSYM CONTINUOUS_ON_MATRIX_VECTORIZE] THEN X_GEN_TAC `v:real^3` THEN
      MATCH_MP_TAC CONTINUOUS_ON_EQ THEN
      EXISTS_TAC `\x. (f':real^(3,1)finite_sum->real^(3,1)finite_sum->real^N) x
                        (pastecart v (vec 0))` THEN
      USE_THEN "fc" (fun th -> REWRITE_TAC[th]) THEN
      X_GEN_TAC `x:real^(3,1)finite_sum` THEN DISCH_TAC THEN EXPAND_TAC "J" THEN
      BETA_TAC THEN CONV_TAC SYM_CONV THEN
      MP_TAC(ISPEC `\h:real^3. (f':real^(3,1)finite_sum->real^(3,1)finite_sum->real^N) x
                                  (pastecart h (vec 0))` MATRIX_WORKS) THEN
      ANTS_TAC THENL
       [SUBGOAL_THEN `(\h:real^3. (f':real^(3,1)finite_sum->real^(3,1)finite_sum->real^N) x
                                   (pastecart h (vec 0))) =
                      f' x o (\h. pastecart h (vec 0))` SUBST1_TAC THENL
         [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
        MATCH_MP_TAC LINEAR_COMPOSE THEN REWRITE_TAC[LINEAR_PASTECART_VEC0_L] THEN
        USE_THEN "lin" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        DISCH_THEN(fun th -> REWRITE_TAC[th])];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `(\x. vectorize(metric_local atlas (U,phi) (Q:A->real^N^N)
             ((phi:A->real^N)((sigma:real^3->real->A)
                (inv(norm(fstcart x)) % fstcart x) (drop(sndcart x)))))) =
      (\w. vectorize(metric_local atlas (U,phi) Q w)) o
      (\x. phi(sigma (inv(norm(fstcart x)) % fstcart x) (drop(sndcart x))))`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN USE_THEN "Fc" (fun th -> REWRITE_TAC[th]) THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `IMAGE (SND(U:A->bool,phi:A->real^N)) (FST(U,phi))` THEN CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    EXPAND_TAC "S" THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; FST; SND] THEN
    MESON_TAC[FUN_IN_IMAGE];
    ALL_TAC] THEN
  (* B: the relatively open piece W of the parameter set *)
  ABBREV_TAC
   `W = {x | x IN sphere(vec 0:real^3,&1) PCROSS interval[vec 0:real^1,vec 1] /\
             (sigma:real^3->real->A) (fstcart x) (drop(sndcart x)) IN U}` THEN
  SUBGOAL_THEN
   `open_in (subtopology euclidean
              (sphere(vec 0:real^3,&1) PCROSS interval[vec 0:real^1,vec 1])) W`
  ASSUME_TAC THENL
   [EXPAND_TAC "W" THEN
    MP_TAC(ISPECL [`\x. (sigma:real^3->real->A) (fstcart x) (drop(sndcart x))`;
                   `subtopology euclidean
                     (sphere(vec 0:real^3,&1) PCROSS interval[vec 0:real^1,vec 1])`;
                   `top:A topology`; `U:A->bool`] OPEN_IN_CONTINUOUS_MAP_PREIMAGE) THEN
    ASM_REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_MESON_TAC[SMOOTH_MANIFOLD_ATLAS_CHART];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x0:real^(3,1)finite_sum) IN W /\ W SUBSET S` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["W"; "S"] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM; P4_IN_SLAB] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[P4_IN_SLAB]) THEN ASM_REWRITE_TAC[] THEN
    SIMP_TAC[P4_SPHERE_NONZERO; P4_RADIAL_FIX];
    ALL_TAC] THEN
  (* C: the Gram matrix is H on W *)
  SUBGOAL_THEN
   `!x. x IN W
        ==> p4_s2_gram atlas (Q:A->real^N^N)
              (\y. (sigma:real^3->real->A) y (drop(sndcart x))) (fstcart x) =
            (H:real^(3,1)finite_sum->real^3^3) x`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^(3,1)finite_sum` THEN EXPAND_TAC "W" THEN
    REWRITE_TAC[IN_ELIM_THM; P4_IN_SLAB] THEN STRIP_TAC THEN
    USE_THEN "der" (MP_TAC o SPECL [`fstcart(x:real^(3,1)finite_sum)`;
                                     `drop(sndcart(x:real^(3,1)finite_sum))`]) THEN
    REWRITE_TAC[LIFT_DROP; PASTECART_FST_SND] THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `Q:A->real^N^N`;
                   `\y. (sigma:real^3->real->A) y (drop(sndcart(x:real^(3,1)finite_sum)))`;
                   `U:A->bool`; `phi:A->real^N`; `fstcart(x:real^(3,1)finite_sum)`]
                  P4_S2_GRAM_CHART) THEN
    BETA_TAC THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC P4_SWEEP_SLICE_CONT THEN ASM_MESON_TAC[];
        REWRITE_TAC[differentiable] THEN ASM_MESON_TAC[]];
      DISCH_THEN SUBST1_TAC] THEN
    MAP_EVERY EXPAND_TAC ["H"; "J"] THEN BETA_TAC THEN REWRITE_TAC[jacobian] THEN
    FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
    ASM_SIMP_TAC[P4_RADIAL_FIX];
    ALL_TAC] THEN
  (* D: conclusion *)
  MP_TAC(ISPECL
   [`\x. vectorize(p4_s2_gram atlas (Q:A->real^N^N)
                    (\y. (sigma:real^3->real->A) y (drop(sndcart x))) (fstcart x))`;
    `x0:real^(3,1)finite_sum`;
    `sphere(vec 0:real^3,&1) PCROSS interval[vec 0:real^1,vec 1]`;
    `W:real^(3,1)finite_sum->bool`] CONTINUOUS_WITHIN_OPEN_IN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC CONTINUOUS_TRANSFORM_WITHIN THEN
  EXISTS_TAC `\x. vectorize((H:real^(3,1)finite_sum->real^3^3) x)` THEN
  EXISTS_TAC `&1` THEN ASM_SIMP_TAC[REAL_LT_01] THEN
  MATCH_MP_TAC CONTINUOUS_WITHIN_SUBSET THEN
  EXISTS_TAC `S:real^(3,1)finite_sum->bool` THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] o
    check (fun th -> can (find_term (fun t -> t = `S:real^(3,1)finite_sum->bool`)) (concl th) &&
                     can (find_term (fun t -> try fst(dest_const t) = "continuous_on"
                                              with Failure _ -> false)) (concl th))) THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM SET_TAC[]);;

(* ========================================================================= *)
(* Pointwise facts about Gram matrices and densities, their                  *)
(* joint continuity on S^2 x [0,1], integrals over S^2, and                 *)
(* P4_CM_NONNEG_STATEMENT.                                                   *)
(* ========================================================================= *)

let P4_GRAM_QF = prove
 (`!atlas (Q:A->real^N^N) (u:real^3->A) y w.
        w dot (p4_s2_gram atlas Q u y ** w) =
        (p4_s2_jac atlas u y ** w) dot (Q(u y) ** (p4_s2_jac atlas u y ** w))`,
  REWRITE_TAC[p4_s2_gram; GSYM MATRIX_VECTOR_MUL_ASSOC; DOT_MATRIX_TRANSP_RMUL]);;

let P4_GRAM_PSD = prove
 (`!atlas (g:A->real^N^N) (u:real^3->A) y.
        positive_semidefinite(g(u y))
        ==> positive_semidefinite(p4_s2_gram atlas g u y)`,
  SIMP_TAC[p4_s2_gram; POSITIVE_SEMIDEFINITE_SIMILAR]);;

let P4_GRAM_SYM = prove
 (`!atlas (Q:A->real^N^N) (u:real^3->A) y.
        transp(Q(u y)) = Q(u y)
        ==> symmetric_matrix(p4_s2_gram atlas Q u y)`,
  SIMP_TAC[p4_s2_gram; symmetric_matrix; MATRIX_TRANSP_MUL; TRANSP_TRANSP;
           MATRIX_MUL_ASSOC]);;

let P4_RIEMANNIAN_PSD = prove
 (`!top atlas (g:A->real^N^N) x.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        x IN topspace top
        ==> positive_semidefinite(g x)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP RIEMANNIAN_METRIC_POS) THEN
  REWRITE_TAC[positive_semidefinite; symmetric_matrix] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `v:real^N` THEN
  ASM_CASES_TAC `v:real^N = vec 0` THEN
  ASM_SIMP_TAC[DOT_LZERO; REAL_LE_REFL; REAL_LT_IMP_LE]);;

let P4_RIEMANNIAN_LOCAL_CONT = prove
 (`!atlas (g:A->real^N^N) c.
        riemannian_metric atlas g /\ c IN atlas
        ==> (\w. vectorize(metric_local atlas c g w)) continuous_on
            IMAGE (SND c) (FST c)`,
  REWRITE_TAC[riemannian_metric; metric_field] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `c:(A->bool)#(A->real^N)`) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o MATCH_MP SMOOTH_MAP_ON_CONTINUOUS_ON o CONJUNCT1 o CONJUNCT2) THEN
  REWRITE_TAC[o_DEF]);;

let P4_DENSITY_POS = prove
 (`!atlas (g:A->real^N^N) (u:real^3->A) y.
        positive_semidefinite(g(u y)) ==> &0 <= p4_s2_density atlas g u y`,
  SIMP_TAC[p4_s2_density; SQRT_POS_LE; P4_E2_PSD; P4_GRAM_PSD]);;

let P4_TRDENSITY_ALT = prove
 (`!atlas (g:A->real^N^N) Q (u:real^3->A) y.
        p4_s2_trdensity atlas g Q u y =
        p4_e2_pol (p4_s2_gram atlas g u y) (p4_s2_gram atlas Q u y) /
        sqrt(p4_e2(p4_s2_gram atlas g u y))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p4_s2_trdensity] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[SQRT_0; real_div; REAL_INV_0; REAL_MUL_RZERO]);;

(* The Ricci tangential trace is controlled by the area density when Q is  *)
(* bounded by C g as a quadratic form.                                      *)

let P4_GRAM_QF_BOUND = prove
 (`!atlas (g:A->real^N^N) Q (u:real^3->A) y C.
        (!v. abs(v dot (Q(u y) ** v)) <= C * (v dot (g(u y) ** v)))
        ==> !w. abs(w dot (p4_s2_gram atlas Q u y ** w)) <=
                C * (w dot (p4_s2_gram atlas g u y ** w))`,
  REWRITE_TAC[P4_GRAM_QF] THEN MESON_TAC[]);;

let P4_TRDENSITY_BOUND = prove
 (`!atlas (g:A->real^N^N) Q (u:real^3->A) y C.
        positive_semidefinite(g(u y)) /\ transp(Q(u y)) = Q(u y) /\ &0 <= C /\
        (!v. abs(v dot (Q(u y) ** v)) <= C * (v dot (g(u y) ** v)))
        ==> abs(p4_s2_trdensity atlas g Q u y) <=
            &2 * C * p4_s2_density atlas g u y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`p4_s2_gram atlas (g:A->real^N^N) (u:real^3->A) y`;
                 `p4_s2_gram atlas (Q:A->real^N^N) (u:real^3->A) y`; `C:real`]
                P4_E2_BOUNDS) THEN
  ASM_SIMP_TAC[P4_GRAM_PSD; P4_GRAM_SYM; P4_GRAM_QF_BOUND] THEN
  DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  SUBGOAL_THEN `&0 <= p4_e2(p4_s2_gram atlas (g:A->real^N^N) (u:real^3->A) y)`
  ASSUME_TAC THENL [ASM_SIMP_TAC[P4_E2_PSD; P4_GRAM_PSD]; ALL_TAC] THEN
  REWRITE_TAC[p4_s2_trdensity; p4_s2_density] THEN COND_CASES_TAC THENL
   [ASM_REWRITE_TAC[SQRT_0; REAL_ABS_0; REAL_MUL_RZERO; REAL_LE_REFL];
    ALL_TAC] THEN
  ABBREV_TAC `e = p4_e2(p4_s2_gram atlas (g:A->real^N^N) (u:real^3->A) y)` THEN
  ABBREV_TAC `p = p4_e2_pol (p4_s2_gram atlas (g:A->real^N^N) (u:real^3->A) y)
                            (p4_s2_gram atlas Q u y)` THEN
  SUBGOAL_THEN `&0 < e` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt e` ASSUME_TAC THENL [ASM_SIMP_TAC[SQRT_POS_LT]; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_ABS_DIV; REAL_ARITH `&0 < x ==> abs x = x`; REAL_LE_LDIV_EQ] THEN
  SUBGOAL_THEN `(&2 * C * sqrt e) * sqrt e = &2 * C * sqrt e pow 2`
  SUBST1_TAC THENL [REAL_ARITH_TAC; ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE]]);;

(* Joint continuity of the slice densities on S^2 x [0,1]. *)

let P4_SWEEP_DENSITY_CONT = prove
 (`!top atlas (g:A->real^N^N) (sigma:real^3->real->A).
        smooth_manifold_atlas top atlas /\ p4_sweepout (top,atlas) sigma /\
        riemannian_metric atlas g
        ==> (\x. lift(p4_s2_density atlas g (\y. sigma y (drop(sndcart x)))
                                     (fstcart x)))
            continuous_on (sphere(vec 0,&1) PCROSS interval[vec 0,vec 1])`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p4_s2_density] THEN
  MATCH_MP_TAC CONTINUOUS_ON_LIFT_SQRT_COMPOSE THEN REWRITE_TAC[o_DEF] THEN
  MATCH_MP_TAC P4_E2_CONTINUOUS THEN MATCH_MP_TAC P4_SWEEP_GRAM_CONT THEN
  EXISTS_TAC `top:A topology` THEN ASM_SIMP_TAC[P4_RIEMANNIAN_LOCAL_CONT]);;

let P4_SWEEP_IN_TOPSPACE = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (sigma:real^3->real->A) x.
        p4_sweepout (top,atlas) sigma /\
        x IN sphere(vec 0,&1) PCROSS interval[vec 0,vec 1]
        ==> sigma (fstcart x) (drop(sndcart x)) IN topspace top`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `sigma:real^3->real->A`] P4_SWEEP_CONTK) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o MATCH_MP CONTINUOUS_MAP_IMAGE_SUBSET_TOPSPACE) THEN
  REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN ASM SET_TAC[]);;

let P4_SWEEP_TRDENSITY_CONT = prove
 (`!top atlas (g:A->real^N^N) Q (sigma:real^3->real->A) C.
        smooth_manifold_atlas top atlas /\ p4_sweepout (top,atlas) sigma /\
        riemannian_metric atlas g /\
        (!c. c IN atlas
             ==> (\w. vectorize(metric_local atlas c Q w)) continuous_on
                 IMAGE (SND c) (FST c)) /\
        &0 <= C /\
        (!x. x IN topspace top
             ==> transp(Q x) = Q x /\
                 !v. abs(v dot (Q x ** v)) <= C * (v dot (g x ** v)))
        ==> (\x. lift(p4_s2_trdensity atlas g Q (\y. sigma y (drop(sndcart x)))
                                       (fstcart x)))
            continuous_on (sphere(vec 0,&1) PCROSS interval[vec 0,vec 1])`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC P4_CONT_DOMINATED THEN
  EXISTS_TAC `\x. &2 * C * p4_s2_density atlas (g:A->real^N^N)
                    (\y. (sigma:real^3->real->A) y (drop(sndcart x))) (fstcart x)` THEN
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[LIFT_CMUL] THEN REPEAT(MATCH_MP_TAC CONTINUOUS_ON_CMUL) THEN
    MATCH_MP_TAC P4_SWEEP_DENSITY_CONT THEN ASM_MESON_TAC[];
    X_GEN_TAC `x:real^(3,1)finite_sum` THEN DISCH_TAC THEN
    MATCH_MP_TAC P4_TRDENSITY_BOUND THEN BETA_TAC THEN
    SUBGOAL_THEN `(sigma:real^3->real->A) (fstcart x) (drop(sndcart x)) IN topspace top`
    ASSUME_TAC THENL [ASM_MESON_TAC[P4_SWEEP_IN_TOPSPACE]; ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN MATCH_MP_TAC P4_RIEMANNIAN_PSD THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `x:real^(3,1)finite_sum` THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(\x. lift(p4_s2_trdensity atlas (g:A->real^N^N) Q
               (\y. (sigma:real^3->real->A) y (drop(sndcart x))) (fstcart x))) =
    (\x. inv(p4_s2_density atlas g (\y. sigma y (drop(sndcart x))) (fstcart x)) %
         lift(p4_e2_pol (p4_s2_gram atlas g (\y. sigma y (drop(sndcart x))) (fstcart x))
                        (p4_s2_gram atlas Q (\y. sigma y (drop(sndcart x))) (fstcart x))))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; P4_TRDENSITY_ALT; GSYM LIFT_CMUL; p4_s2_density] THEN
    GEN_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[real_div] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_MUL THEN CONJ_TAC THENL
   [SUBGOAL_THEN
     `(lift o (\x. inv(p4_s2_density atlas (g:A->real^N^N)
                       (\y. (sigma:real^3->real->A) y (drop(sndcart x))) (fstcart x)))) =
      lift o inv o (\x. p4_s2_density atlas g (\y. sigma y (drop(sndcart x))) (fstcart x))`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_AT_WITHIN_INV THEN
    CONJ_TAC THENL [ALL_TAC; BETA_TAC THEN POP_ASSUM MP_TAC THEN
                     REWRITE_TAC[REAL_ENTIRE; DE_MORGAN_THM] THEN SIMP_TAC[]] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `sigma:real^3->real->A`] P4_SWEEP_DENSITY_CONT) THEN
    ASM_REWRITE_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN; o_DEF] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    MP_TAC(ISPECL
     [`\x. p4_s2_gram atlas (g:A->real^N^N)
             (\y. (sigma:real^3->real->A) y (drop(sndcart x))) (fstcart x)`;
      `\x. p4_s2_gram atlas (Q:A->real^N^N)
             (\y. (sigma:real^3->real->A) y (drop(sndcart x))) (fstcart x)`;
      `sphere(vec 0:real^3,&1) PCROSS interval[vec 0:real^1,vec 1]`]
     P4_E2_POL_CONTINUOUS) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC P4_SWEEP_GRAM_CONT THEN
      EXISTS_TAC `top:A topology` THEN ASM_SIMP_TAC[P4_RIEMANNIAN_LOCAL_CONT];
      REWRITE_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* Integrals over S^2 (3 times ball integrals of radial extensions) of      *)
(* functions continuous on S^2.                                              *)
(* ------------------------------------------------------------------------- *)

let P4_RADIAL_EXT_CONTINUOUS = prove
 (`!f:real^3->real.
        (\y. lift(f y)) continuous_on sphere(vec 0,&1)
        ==> (\z. lift(f(inv(norm z) % z))) continuous_on ((:real^3) DIFF {vec 0})`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\z. lift((f:real^3->real)(inv(norm z) % z))) =
                (\y. lift(f y)) o (\z. inv(norm z) % z)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN REWRITE_TAC[P4_RADIAL_CONTINUOUS] THEN
  MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `sphere(vec 0:real^3,&1)` THEN
  ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_DIFF; IN_UNIV; IN_SING] THEN
  SIMP_TAC[P4_RADIAL_SPHERE]);;

let P4_S2_INTEGRABLE = prove
 (`!f:real^3->real.
        (\y. lift(f y)) continuous_on sphere(vec 0,&1)
        ==> (\z. lift(f(inv(norm z) % z))) integrable_on ball(vec 0,&1)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\y. lift((f:real^3->real) y)`; `sphere(vec 0:real^3,&1)`]
                COMPACT_CONTINUOUS_IMAGE) THEN
  ASM_REWRITE_TAC[COMPACT_SPHERE] THEN
  DISCH_THEN(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
  REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE; NORM_LIFT] THEN
  DISCH_THEN(X_CHOOSE_THEN `M:real` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_INTEGRABLE THEN
  EXISTS_TAC `\z:real^3. lift(max M (abs((f:real^3->real)(vec 0))))` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] MEASURABLE_ON_SPIKE_SET) THEN
    EXISTS_TAC `ball(vec 0:real^3,&1) DIFF {vec 0}` THEN CONJ_TAC THENL
     [MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN EXISTS_TAC `{vec 0:real^3}` THEN
      REWRITE_TAC[NEGLIGIBLE_SING] THEN SET_TAC[];
      MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
      SIMP_TAC[LEBESGUE_MEASURABLE_OPEN; OPEN_DIFF; OPEN_BALL; CLOSED_SING] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `(:real^3) DIFF {vec 0}` THEN
      ASM_SIMP_TAC[P4_RADIAL_EXT_CONTINUOUS] THEN SET_TAC[]];
    REWRITE_TAC[INTEGRABLE_ON_CONST; MEASURABLE_BALL];
    X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN REWRITE_TAC[NORM_LIFT; LIFT_DROP] THEN
    ASM_CASES_TAC `z:real^3 = vec 0` THENL
     [ASM_REWRITE_TAC[VECTOR_MUL_RZERO] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC(REAL_ARITH `x <= M ==> x <= max M y`) THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[P4_RADIAL_SPHERE]]]);;

let P4_S2_INTEGRAL_MONO = prove
 (`!f g:real^3->real.
        (\y. lift(f y)) continuous_on sphere(vec 0,&1) /\
        (\y. lift(g y)) continuous_on sphere(vec 0,&1) /\
        (!y. y IN sphere(vec 0,&1) ==> f y <= g y)
        ==> p4_s2_integral f <= p4_s2_integral g`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p4_s2_integral] THEN
  MATCH_MP_TAC(REAL_ARITH `x <= y ==> &3 * x <= &3 * y`) THEN
  MATCH_MP_TAC INTEGRAL_DROP_LE_AE THEN EXISTS_TAC `{vec 0:real^3}` THEN
  ASM_SIMP_TAC[P4_S2_INTEGRABLE; NEGLIGIBLE_SING; LIFT_DROP] THEN
  REWRITE_TAC[IN_DIFF; IN_SING] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[P4_RADIAL_SPHERE]);;

let P4_S2_INTEGRAL_ADD = prove
 (`!f g:real^3->real.
        (\y. lift(f y)) continuous_on sphere(vec 0,&1) /\
        (\y. lift(g y)) continuous_on sphere(vec 0,&1)
        ==> p4_s2_integral (\y. f y + g y) = p4_s2_integral f + p4_s2_integral g`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p4_s2_integral; LIFT_ADD] THEN
  ASM_SIMP_TAC[INTEGRAL_ADD; P4_S2_INTEGRABLE; DROP_ADD] THEN REAL_ARITH_TAC);;

let P4_S2_INTEGRAL_SUB = prove
 (`!f g:real^3->real.
        (\y. lift(f y)) continuous_on sphere(vec 0,&1) /\
        (\y. lift(g y)) continuous_on sphere(vec 0,&1)
        ==> p4_s2_integral (\y. f y - g y) = p4_s2_integral f - p4_s2_integral g`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p4_s2_integral; LIFT_SUB] THEN
  ASM_SIMP_TAC[INTEGRAL_SUB; P4_S2_INTEGRABLE; DROP_SUB] THEN REAL_ARITH_TAC);;

let P4_S2_INTEGRAL_CMUL = prove
 (`!f:real^3->real c.
        (\y. lift(f y)) continuous_on sphere(vec 0,&1)
        ==> p4_s2_integral (\y. c * f y) = c * p4_s2_integral f`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p4_s2_integral; LIFT_CMUL] THEN
  ASM_SIMP_TAC[INTEGRAL_CMUL; P4_S2_INTEGRABLE; DROP_CMUL] THEN REAL_ARITH_TAC);;

let P4_S2_INTEGRAL_CONST = prove
 (`!c. p4_s2_integral (\y. c) = &3 * measure(ball(vec 0:real^3,&1)) * c`,
  SIMP_TAC[p4_s2_integral; INTEGRAL_CONST_GEN; MEASURABLE_BALL; DROP_CMUL;
           LIFT_DROP] THEN
  REAL_ARITH_TAC);;

let P4_S2_INTEGRAL_POS = prove
 (`!f:real^3->real.
        (\y. lift(f y)) continuous_on sphere(vec 0,&1) /\
        (!y. y IN sphere(vec 0,&1) ==> &0 <= f y)
        ==> &0 <= p4_s2_integral f`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\y:real^3. &0`; `f:real^3->real`] P4_S2_INTEGRAL_MONO) THEN
  ASM_REWRITE_TAC[CONTINUOUS_ON_CONST; P4_S2_INTEGRAL_CONST; REAL_MUL_RZERO]);;

let P4_S2_INTEGRAL_ABS = prove
 (`!f:real^3->real.
        (\y. lift(f y)) continuous_on sphere(vec 0,&1)
        ==> abs(p4_s2_integral f) <= p4_s2_integral (\y. abs(f y))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p4_s2_integral; REAL_ABS_MUL; REAL_ABS_NUM] THEN
  MATCH_MP_TAC(REAL_ARITH `x <= y ==> &3 * x <= &3 * y`) THEN
  REWRITE_TAC[GSYM NORM_1] THEN MATCH_MP_TAC INTEGRAL_NORM_BOUND_INTEGRAL THEN
  ASM_SIMP_TAC[P4_S2_INTEGRABLE; NORM_LIFT; LIFT_DROP; REAL_LE_REFL] THEN
  MATCH_MP_TAC P4_S2_INTEGRABLE THEN REWRITE_TAC[GSYM NORM_LIFT] THEN
  MATCH_MP_TAC CONTINUOUS_ON_LIFT_NORM_COMPOSE THEN ASM_REWRITE_TAC[]);;

(* Slices of functions continuous on S^2 x [0,1]. *)

let P4_SLAB_SLICE = prove
 (`!f:real^(3,1)finite_sum->real t.
        (\x. lift(f x)) continuous_on (sphere(vec 0,&1) PCROSS interval[vec 0,vec 1]) /\
        t IN real_interval[&0,&1]
        ==> (\y. lift(f(pastecart y (lift t)))) continuous_on sphere(vec 0,&1)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\y. lift((f:real^(3,1)finite_sum->real)(pastecart y (lift t)))) =
                (\x. lift(f x)) o (\y:real^3. pastecart y (lift t))` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN
    REWRITE_TAC[CONTINUOUS_ON_ID; CONTINUOUS_ON_CONST];
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `sphere(vec 0:real^3,&1) PCROSS interval[vec 0:real^1,vec 1]` THEN
    ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; P4_IN_SLAB; FSTCART_PASTECART;
                    SNDCART_PASTECART; LIFT_DROP]]);;

(* ------------------------------------------------------------------------- *)
(* Slice densities and P4_CM_NONNEG_STATEMENT.                               *)
(* ------------------------------------------------------------------------- *)

let P4_SLAB_PASTECART = prove
 (`!y t. pastecart y (lift t) IN sphere(vec 0:real^3,&1) PCROSS interval[vec 0,vec 1] <=>
         y IN sphere(vec 0,&1) /\ t IN real_interval[&0,&1]`,
  REWRITE_TAC[P4_IN_SLAB; FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP]);;

let P4_SLICE_DENSITY_CONT = prove
 (`!top atlas (g:A->real^N^N) (sigma:real^3->real->A) t.
        smooth_manifold_atlas top atlas /\ p4_sweepout (top,atlas) sigma /\
        riemannian_metric atlas g /\ t IN real_interval[&0,&1]
        ==> (\y. lift(p4_s2_density atlas g (\y. sigma y t) y)) continuous_on
            sphere(vec 0,&1)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\x. p4_s2_density atlas (g:A->real^N^N)
                        (\y. (sigma:real^3->real->A) y (drop(sndcart x))) (fstcart x)`;
                 `t:real`] P4_SLAB_SLICE) THEN
  REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC P4_SWEEP_DENSITY_CONT THEN ASM_MESON_TAC[]);;

let P4_SLICE_IN_TOPSPACE = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (sigma:real^3->real->A) y t.
        p4_sweepout (top,atlas) sigma /\
        y IN sphere(vec 0,&1) /\ t IN real_interval[&0,&1]
        ==> sigma y t IN topspace top`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `sigma:real^3->real->A`; `pastecart (y:real^3) (lift t)`]
                P4_SWEEP_IN_TOPSPACE) THEN
  ASM_REWRITE_TAC[P4_SLAB_PASTECART; FSTCART_PASTECART; SNDCART_PASTECART;
                  LIFT_DROP]);;

let P4_SLICE_DENSITY_POS = prove
 (`!top atlas (g:A->real^N^N) (sigma:real^3->real->A) y t.
        smooth_manifold_atlas top atlas /\ p4_sweepout (top,atlas) sigma /\
        riemannian_metric atlas g /\
        y IN sphere(vec 0,&1) /\ t IN real_interval[&0,&1]
        ==> &0 <= p4_s2_density atlas g (\y. sigma y t) y`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC P4_DENSITY_POS THEN BETA_TAC THEN
  MATCH_MP_TAC P4_RIEMANNIAN_PSD THEN ASM_MESON_TAC[P4_SLICE_IN_TOPSPACE]);;

let P4_SWEEP_DENSITY_BOUND = prove
 (`!top atlas (g:A->real^N^N) (sigma:real^3->real->A).
        smooth_manifold_atlas top atlas /\ p4_sweepout (top,atlas) sigma /\
        riemannian_metric atlas g
        ==> ?M. &0 < M /\
                !y t. y IN sphere(vec 0,&1) /\ t IN real_interval[&0,&1]
                      ==> p4_s2_density atlas g (\y. sigma y t) y <= M`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `sigma:real^3->real->A`] P4_SWEEP_DENSITY_CONT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] COMPACT_CONTINUOUS_IMAGE)) THEN
  REWRITE_TAC[P4_SLAB_COMPACT] THEN
  DISCH_THEN(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
  REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE; NORM_LIFT] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `M:real` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN MAP_EVERY X_GEN_TAC [`y:real^3`; `t:real`] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `pastecart (y:real^3) (lift t)`) THEN
  ASM_REWRITE_TAC[P4_SLAB_PASTECART; FSTCART_PASTECART; SNDCART_PASTECART;
                  LIFT_DROP] THEN
  MATCH_ACCEPT_TAC(REAL_ARITH `!x M. abs x <= M ==> x <= M`));;

let P4_SLICE_AREA_POS = prove
 (`!top atlas (g:A->real^N^N) (sigma:real^3->real->A) t.
        smooth_manifold_atlas top atlas /\ p4_sweepout (top,atlas) sigma /\
        riemannian_metric atlas g /\ t IN real_interval[&0,&1]
        ==> &0 <= p4_s2_area atlas g (\y. sigma y t)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p4_s2_area] THEN
  MATCH_MP_TAC P4_S2_INTEGRAL_POS THEN CONJ_TAC THENL
   [MATCH_MP_TAC P4_SLICE_DENSITY_CONT THEN ASM_MESON_TAC[];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC P4_SLICE_DENSITY_POS THEN ASM_MESON_TAC[]]);;

let P4_SWEEP_AREA_BOUND = prove
 (`!top atlas (g:A->real^N^N) (sigma:real^3->real->A).
        smooth_manifold_atlas top atlas /\ p4_sweepout (top,atlas) sigma /\
        riemannian_metric atlas g
        ==> ?B. !t. t IN real_interval[&0,&1]
                    ==> p4_s2_area atlas g (\y. sigma y t) <= B`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `sigma:real^3->real->A`] P4_SWEEP_DENSITY_BOUND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `M:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `p4_s2_integral (\y:real^3. M)` THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[p4_s2_area] THEN MATCH_MP_TAC P4_S2_INTEGRAL_MONO THEN
  ASM_SIMP_TAC[CONTINUOUS_ON_CONST] THEN
  MATCH_MP_TAC P4_SLICE_DENSITY_CONT THEN ASM_MESON_TAC[]);;

let P4_CM_NONNEG = prove
 (`P4_CM_NONNEG_STATEMENT (:A)`,
  REWRITE_TAC[P4_CM_NONNEG_STATEMENT] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC P4_SLICE_AREA_POS THEN ASM_MESON_TAC[];
    MATCH_MP_TAC P4_SWEEP_AREA_BOUND THEN ASM_MESON_TAC[]]);;

(* ========================================================================= *)
(* C^1 maps on relatively open subsets of the sweepout domain                *)
(* D = (real^3 - 0) x [0,1] (uniqueness of derivatives within such sets,     *)
(* locality, composition), and push-forward of sweepouts by smooth maps.     *)
(* ========================================================================= *)

let P4_REAL_STEP = prove
 (`!t s dl. &0 <= t /\ t <= &1 /\ abs s <= &1 /\ &0 < dl /\ dl <= &1 / &4
            ==> ?d. abs d = dl /\ &0 <= t + d * s /\ t + d * s <= &1`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `abs(dl * s) <= dl` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_ABS_MUL] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `abs dl * &1` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_ABS_POS];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_CASES_TAC `&0 <= s` THENL
   [SUBGOAL_THEN `&0 <= dl * s` ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE]; ALL_TAC];
    SUBGOAL_THEN `dl * s <= &0` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_ARITH `x * y <= &0 <=> &0 <= x * --y`] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      ALL_TAC]] THEN
  (ASM_CASES_TAC `t <= &1 / &2` THENL
    [EXISTS_TAC `if &0 <= s then dl else --dl`;
     EXISTS_TAC `if &0 <= s then --dl else dl`]) THEN
  ASM_REWRITE_TAC[REAL_ABS_NEG; REAL_MUL_LNEG] THEN ASM_REAL_ARITH_TAC);;

let P4_SLAB_DIRS = prove
 (`!S (x:real^(3,1)finite_sum).
        open_in (subtopology euclidean
                  {x:real^(3,1)finite_sum | ~(fstcart x = vec 0) /\
                                             drop(sndcart x) IN real_interval[&0,&1]})
                S /\
        x IN S
        ==> !i e. 1 <= i /\ i <= dimindex(:(3,1)finite_sum) /\ &0 < e
                  ==> ?d. &0 < abs d /\ abs d < e /\ x + d % basis i IN S`,
  REPEAT GEN_TAC THEN REWRITE_TAC[OPEN_IN_CONTAINS_BALL] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `x:real^(3,1)finite_sum`))
    ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  MAP_EVERY X_GEN_TAC [`i:num`; `e:real`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(fstcart(x:real^(3,1)finite_sum) = vec 0) /\
                drop(sndcart x) IN real_interval[&0,&1]`
  STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `a = norm(fstcart(x:real^(3,1)finite_sum))` THEN
  SUBGOAL_THEN `&0 < a` ASSUME_TAC THENL
   [EXPAND_TAC "a" THEN ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  ABBREV_TAC `dl = min (min e r) (min a (&1 / &2)) / &2` THEN
  SUBGOAL_THEN `&0 < dl /\ dl < e /\ dl < r /\ dl < a /\ dl <= &1 / &4`
  STRIP_ASSUME_TAC THENL [EXPAND_TAC "dl" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `norm(basis i:real^(3,1)finite_sum) = &1` ASSUME_TAC THENL
   [ASM_SIMP_TAC[NORM_BASIS]; ALL_TAC] THEN
  MP_TAC(SPECL [`drop(sndcart(x:real^(3,1)finite_sum))`;
                `drop(sndcart(basis i:real^(3,1)finite_sum))`; `dl:real`]
               P4_REAL_STEP) THEN
  ANTS_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[IN_REAL_INTERVAL]) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM NORM_1] THEN ASM_MESON_TAC[NORM_SNDCART];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
  REWRITE_TAC[IN_INTER; IN_BALL; IN_ELIM_THM] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[NORM_ARITH `dist(x:real^N,x + y) = norm y`; NORM_MUL] THEN
    ASM_REWRITE_TAC[REAL_MUL_RID];
    REWRITE_TAC[FSTCART_ADD; FSTCART_CMUL] THEN DISCH_TAC THEN
    SUBGOAL_THEN `norm(fstcart(basis i:real^(3,1)finite_sum)) <= &1` ASSUME_TAC THENL
     [ASM_MESON_TAC[NORM_FSTCART]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o AP_TERM `norm:real^3->real` o MATCH_MP (VECTOR_ARITH
      `a + b:real^N = vec 0 ==> a = --b`)) THEN
    ASM_REWRITE_TAC[NORM_NEG; NORM_MUL] THEN DISCH_TAC THEN
    MP_TAC(SPECL [`dl:real`; `norm(fstcart(basis i:real^(3,1)finite_sum))`; `&1`]
                 REAL_LE_LMUL) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[SNDCART_ADD; SNDCART_CMUL; DROP_ADD; DROP_CMUL; IN_REAL_INTERVAL] THEN
    ASM_REWRITE_TAC[]]);;

let P4_SLAB_DERIV_UNIQUE = prove
 (`!(f:real^(3,1)finite_sum->real^N) f' f'' S x.
        open_in (subtopology euclidean
                  {x:real^(3,1)finite_sum | ~(fstcart x = vec 0) /\
                                             drop(sndcart x) IN real_interval[&0,&1]})
                S /\
        x IN S /\
        (f has_derivative f') (at x within S) /\
        (f has_derivative f'') (at x within S)
        ==> f' = f''`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FRECHET_DERIVATIVE_UNIQUE_WITHIN THEN
  MAP_EVERY EXISTS_TAC [`f:real^(3,1)finite_sum->real^N`; `x:real^(3,1)finite_sum`;
                        `S:real^(3,1)finite_sum->bool`] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P4_SLAB_DIRS THEN ASM_REWRITE_TAC[]);;

(* C^1 on relatively open subsets of D is a local property. *)

let P4_SLAB_C1_LOCAL = prove
 (`!(Fm:real^(3,1)finite_sum->real^N) S.
        open_in (subtopology euclidean
                  {x:real^(3,1)finite_sum | ~(fstcart x = vec 0) /\
                                             drop(sndcart x) IN real_interval[&0,&1]})
                S /\
        (!x. x IN S
             ==> ?V. open_in (subtopology euclidean
                        {x:real^(3,1)finite_sum | ~(fstcart x = vec 0) /\
                                                   drop(sndcart x) IN
                                                   real_interval[&0,&1]}) V /\
                     x IN V /\ V SUBSET S /\ continuously_differentiable 1 V Fm)
        ==> continuously_differentiable 1 S Fm`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "loc")) THEN
  ABBREV_TAC `D = {x:real^(3,1)finite_sum | ~(fstcart x = vec 0) /\
                                             drop(sndcart x) IN real_interval[&0,&1]}` THEN
  SUBGOAL_THEN `(S:real^(3,1)finite_sum->bool) SUBSET D` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_IMP_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!x V (g':real^(3,1)finite_sum->real^N).
        x IN V /\ open_in (subtopology euclidean D) V /\ V SUBSET S /\
        ((Fm:real^(3,1)finite_sum->real^N) has_derivative g') (at x within V)
        ==> (Fm has_derivative g') (at x within S)`
  (LABEL_TAC "up") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`Fm:real^(3,1)finite_sum->real^N`;
                   `g':real^(3,1)finite_sum->real^N`; `x:real^(3,1)finite_sum`;
                   `V:real^(3,1)finite_sum->bool`; `S:real^(3,1)finite_sum->bool`]
                  HAS_DERIVATIVE_WITHIN_OPEN_IN) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC OPEN_IN_SUBSET_TRANS THEN
      EXISTS_TAC `D:real^(3,1)finite_sum->bool` THEN ASM_REWRITE_TAC[];
      DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN S
        ==> ((Fm:real^(3,1)finite_sum->real^N) has_derivative
             frechet_derivative Fm (at x within S)) (at x within S)`
  (LABEL_TAC "der") THENL
   [X_GEN_TAC `x:real^(3,1)finite_sum` THEN DISCH_TAC THEN
    USE_THEN "loc" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(x:real^(3,1)finite_sum) IN S`))) THEN
    DISCH_THEN(X_CHOOSE_THEN `V:real^(3,1)finite_sum->bool` STRIP_ASSUME_TAC) THEN
    REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS; differentiable] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [CONTINUOUSLY_DIFFERENTIABLE_1]) THEN
    DISCH_THEN(X_CHOOSE_THEN `g':real^(3,1)finite_sum->real^(3,1)finite_sum->real^N`
      STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `(g':real^(3,1)finite_sum->real^(3,1)finite_sum->real^N) x` THEN
    USE_THEN "up" MATCH_MP_TAC THEN EXISTS_TAC `V:real^(3,1)finite_sum->bool` THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[CONTINUOUSLY_DIFFERENTIABLE_1] THEN
  EXISTS_TAC `\x. frechet_derivative (Fm:real^(3,1)finite_sum->real^N) (at x within S)` THEN
  BETA_TAC THEN ASM_SIMP_TAC[] THEN X_GEN_TAC `h:real^(3,1)finite_sum` THEN
  REWRITE_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
  X_GEN_TAC `x0:real^(3,1)finite_sum` THEN DISCH_TAC THEN
  USE_THEN "loc" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(x0:real^(3,1)finite_sum) IN S`))) THEN
  DISCH_THEN(X_CHOOSE_THEN `V:real^(3,1)finite_sum->bool` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [CONTINUOUSLY_DIFFERENTIABLE_1]) THEN
  DISCH_THEN(X_CHOOSE_THEN `g':real^(3,1)finite_sum->real^(3,1)finite_sum->real^N`
    STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `open_in (subtopology euclidean S) (V:real^(3,1)finite_sum->bool)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC OPEN_IN_SUBSET_TRANS THEN
    EXISTS_TAC `D:real^(3,1)finite_sum->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN V
        ==> frechet_derivative (Fm:real^(3,1)finite_sum->real^N) (at x within S) =
            (g':real^(3,1)finite_sum->real^(3,1)finite_sum->real^N) x`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^(3,1)finite_sum` THEN DISCH_TAC THEN
    MATCH_MP_TAC P4_SLAB_DERIV_UNIQUE THEN
    MAP_EVERY EXISTS_TAC [`Fm:real^(3,1)finite_sum->real^N`;
                          `S:real^(3,1)finite_sum->bool`; `x:real^(3,1)finite_sum`] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(x:real^(3,1)finite_sum) IN S` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN USE_THEN "up" MATCH_MP_TAC THEN
    EXISTS_TAC `V:real^(3,1)finite_sum->bool` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\x. frechet_derivative (Fm:real^(3,1)finite_sum->real^N)
                        (at x within S) h`;
                 `x0:real^(3,1)finite_sum`; `S:real^(3,1)finite_sum->bool`;
                 `V:real^(3,1)finite_sum->bool`] CONTINUOUS_WITHIN_OPEN_IN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC CONTINUOUS_TRANSFORM_WITHIN THEN
  EXISTS_TAC `\x. (g':real^(3,1)finite_sum->real^(3,1)finite_sum->real^N) x h` THEN
  EXISTS_TAC `&1` THEN ASM_SIMP_TAC[REAL_LT_01] THEN
  ASM_MESON_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN]);;

(* Composition of a map C^1 within s with a smooth map on an open set. *)

let P4_C1_COMPOSE_WITHIN = prove
 (`!(f:real^M->real^N) (g:real^N->real^P) s t.
        continuously_differentiable 1 s f /\ open t /\ IMAGE f s SUBSET t /\
        smooth_map_on t g
        ==> continuously_differentiable 1 s (g o f)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP CONTINUOUSLY_DIFFERENTIABLE_IMP_CONTINUOUS_ON) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [CONTINUOUSLY_DIFFERENTIABLE_1]) THEN
  DISCH_THEN(X_CHOOSE_THEN `f':real^M->real^M->real^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!w. w IN t ==> ((g:real^N->real^P) has_derivative
                                frechet_derivative g (at w)) (at w)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[CONTINUOUSLY_DIFFERENTIABLE_1] THEN
  EXISTS_TAC `\x. frechet_derivative (g:real^N->real^P) (at ((f:real^M->real^N) x)) o
                  (f':real^M->real^M->real^N) x` THEN
  CONJ_TAC THENL
   [X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC DIFF_CHAIN_WITHIN THEN ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC HAS_DERIVATIVE_AT_WITHIN THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `h:real^M` THEN MATCH_MP_TAC CONTINUOUS_ON_EQ THEN
  EXISTS_TAC `\x. matrix(frechet_derivative (g:real^N->real^P)
                           (at ((f:real^M->real^N) x))) **
                  (f':real^M->real^M->real^N) x h` THEN
  CONJ_TAC THENL
   [X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN
    SUBGOAL_THEN `linear(frechet_derivative (g:real^N->real^P)
                           (at ((f:real^M->real^N) x)))`
    (fun th -> REWRITE_TAC[MATCH_MP MATRIX_WORKS th]) THEN
    SUBGOAL_THEN `((g:real^N->real^P) has_derivative
                   frechet_derivative g (at ((f:real^M->real^N) x))) (at (f x))`
    MP_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]; ALL_TAC] THEN
    SIMP_TAC[has_derivative];
    ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_MATRIX_VECTOR_MUL THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `(vectorize o (\x. matrix(frechet_derivative (g:real^N->real^P)
                               (at ((f:real^M->real^N) x))))) =
    (vectorize o (\z. matrix(frechet_derivative g (at z)))) o f`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `t:real^N->bool` THEN
  ASM_SIMP_TAC[GRGD_JACOBIAN_CONTINUOUS]);;

let P4_C1_EQ_WITHIN = prove
 (`!(f:real^M->real^N) g s.
        (!x. x IN s ==> f x = g x) /\ continuously_differentiable 1 s f
        ==> continuously_differentiable 1 s g`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CONTINUOUSLY_DIFFERENTIABLE_1] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `f':real^M->real^M->real^N` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `f':real^M->real^M->real^N` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
  MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_WITHIN THEN
  MAP_EVERY EXISTS_TAC [`f:real^M->real^N`; `&1`] THEN
  ASM_SIMP_TAC[REAL_LT_01]);;

(* Continuity of the sweepout on the whole domain D. *)

let P4_SWEEP_CONTD = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (sigma:real^3->real->A).
        p4_sweepout (top,atlas) sigma
        ==> continuous_map
              (subtopology euclidean
                 {x:real^(3,1)finite_sum | ~(fstcart x = vec 0) /\
                                            drop(sndcart x) IN real_interval[&0,&1]},
               top)
              (\x. sigma (inv(norm(fstcart x)) % fstcart x) (drop(sndcart x)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `(\x. (sigma:real^3->real->A) (inv(norm(fstcart x)) % fstcart x) (drop(sndcart x))) =
    (\(y,t). sigma y t) o
    (\x:real^(3,1)finite_sum. (inv(norm(fstcart x)) % fstcart x, drop(sndcart x)))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
  EXISTS_TAC `prod_topology (subtopology euclidean (sphere(vec 0:real^3,&1)))
                            (subtopology euclideanreal (real_interval[&0,&1]))` THEN
  CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[p4_sweepout]] THEN
  REWRITE_TAC[CONTINUOUS_MAP_PAIRWISE; o_DEF; FST; SND] THEN CONJ_TAC THENL
   [REWRITE_TAC[CONTINUOUS_MAP_EUCLIDEAN2] THEN CONJ_TAC THENL
     [SUBGOAL_THEN `(\x:real^(3,1)finite_sum. inv(norm(fstcart x)) % fstcart x) =
                    (\z. inv(norm z) % z) o fstcart` SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
      SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_FSTCART] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^3) DIFF {vec 0}` THEN
      REWRITE_TAC[P4_RADIAL_CONTINUOUS] THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; IN_DIFF; IN_UNIV; IN_SING] THEN
      SIMP_TAC[];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
      SIMP_TAC[P4_RADIAL_SPHERE]];
    REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY; CONTINUOUS_MAP_EQ_LIFT] THEN
    REWRITE_TAC[o_DEF; LIFT_DROP; CONTINUOUS_MAP_EUCLIDEAN; ETA_AX] THEN
    SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_SNDCART] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM;
                TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
    SIMP_TAC[]]);;

(* The chart pieces of a sweepout (and of its composite with a map          *)
(* continuous on W) are open in D.                                           *)

let P4_SWEEP_PIECE_OPEN = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (sigma:real^3->real->A) V.
        p4_sweepout (top,atlas) sigma /\ open_in top V
        ==> open_in (subtopology euclidean
                       {x:real^(3,1)finite_sum | ~(fstcart x = vec 0) /\
                                                  drop(sndcart x) IN real_interval[&0,&1]})
                    {x | ~(fstcart x = vec 0) /\
                         drop(sndcart x) IN real_interval[&0,&1] /\
                         sigma (inv(norm(fstcart x)) % fstcart x) (drop(sndcart x)) IN V}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\x. (sigma:real^3->real->A) (inv(norm(fstcart x)) % fstcart x)
                                               (drop(sndcart x))`;
                 `subtopology euclidean
                    {x:real^(3,1)finite_sum | ~(fstcart x = vec 0) /\
                                               drop(sndcart x) IN real_interval[&0,&1]}`;
                 `top:A topology`; `V:A->bool`] OPEN_IN_CONTINUOUS_MAP_PREIMAGE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P4_SWEEP_CONTD THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; CONJ_ASSOC]);;

let P4_SWEEP_PUSH_PIECE_OPEN = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) top' W (f:A->B)
    (sigma:real^3->real->A) V.
        p4_sweepout (top,atlas) sigma /\
        continuous_map (subtopology top W,top') f /\
        (!y t. y IN sphere(vec 0,&1) /\ t IN real_interval[&0,&1] ==> sigma y t IN W) /\
        open_in top' V
        ==> open_in (subtopology euclidean
                       {x:real^(3,1)finite_sum | ~(fstcart x = vec 0) /\
                                                  drop(sndcart x) IN real_interval[&0,&1]})
                    {x | ~(fstcart x = vec 0) /\
                         drop(sndcart x) IN real_interval[&0,&1] /\
                         f(sigma (inv(norm(fstcart x)) % fstcart x) (drop(sndcart x))) IN V}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\x. (f:A->B)((sigma:real^3->real->A) (inv(norm(fstcart x)) % fstcart x)
                                                       (drop(sndcart x)))`;
                 `subtopology euclidean
                    {x:real^(3,1)finite_sum | ~(fstcart x = vec 0) /\
                                               drop(sndcart x) IN real_interval[&0,&1]}`;
                 `top':B topology`; `V:B->bool`] OPEN_IN_CONTINUOUS_MAP_PREIMAGE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `(\x. (f:A->B)((sigma:real^3->real->A) (inv(norm(fstcart x)) % fstcart x)
                                           (drop(sndcart x)))) =
      f o (\x. sigma (inv(norm(fstcart x)) % fstcart x) (drop(sndcart x)))`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN EXISTS_TAC `subtopology top (W:A->bool)` THEN
    ASM_REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN CONJ_TAC THENL
     [MATCH_MP_TAC P4_SWEEP_CONTD THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY; IN_ELIM_THM] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_SIMP_TAC[P4_RADIAL_SPHERE];
    REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; CONJ_ASSOC]]);;

(* Push-forward of a sweepout by a map smooth on an open set W containing   *)
(* its values.                                                               *)

let P4_SWEEP_PUSH_C1 = prove
 (`!top atlas top' atlas' W (f:A->B) (sigma:real^3->real->A) c'.
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
        smooth_manifold_atlas top' (atlas':((B->bool)#(B->real^M))->bool) /\
        open_in top W /\ continuous_map (subtopology top W,top') f /\
        mfd_smooth_map atlas atlas' W f /\
        p4_sweepout (top,atlas) sigma /\
        (!y t. y IN sphere(vec 0,&1) /\ t IN real_interval[&0,&1] ==> sigma y t IN W) /\
        c' IN atlas'
        ==> continuously_differentiable 1
              {x | ~(fstcart x = vec 0) /\ drop(sndcart x) IN real_interval[&0,&1] /\
                   f(sigma (inv(norm(fstcart x)) % fstcart x) (drop(sndcart x)))
                   IN FST c'}
              (\x. SND c' (f(sigma (inv(norm(fstcart x)) % fstcart x)
                                   (drop(sndcart x)))))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC P4_SLAB_C1_LOCAL THEN CONJ_TAC THENL
   [MATCH_MP_TAC P4_SWEEP_PUSH_PIECE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                          `top':B topology`; `W:A->bool`] THEN
    ASM_MESON_TAC[GRGD_ATLAS_CHART];
    ALL_TAC] THEN
  X_GEN_TAC `x0:real^(3,1)finite_sum` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
  ABBREV_TAC `p0 = (sigma:real^3->real->A)
                     (inv(norm(fstcart(x0:real^(3,1)finite_sum))) % fstcart x0)
                     (drop(sndcart x0))` THEN
  SUBGOAL_THEN `(p0:A) IN W /\ p0 IN topspace top` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "p0" THEN CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[P4_RADIAL_SPHERE];
      MATCH_MP_TAC P4_SLICE_IN_TOPSPACE THEN
      EXISTS_TAC `atlas:((A->bool)#(A->real^N))->bool` THEN
      ASM_SIMP_TAC[P4_RADIAL_SPHERE]];
    ALL_TAC] THEN
  MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `p0:A`]
               CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `chart_at (atlas:((A->bool)#(A->real^N))->bool) (p0:A)` PAIR_SURJECTIVE) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`U:A->bool`; `phi:A->real^N`] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[FST] THEN STRIP_TAC THEN
  EXISTS_TAC
   `{x | ~(fstcart x = vec 0) /\ drop(sndcart x) IN real_interval[&0,&1] /\
         (f:A->B)((sigma:real^3->real->A) (inv(norm(fstcart x)) % fstcart x)
                                          (drop(sndcart x))) IN FST (c':(B->bool)#(B->real^M)) /\
         sigma (inv(norm(fstcart x)) % fstcart x) (drop(sndcart x)) IN U}` THEN
  REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN
     `{x | ~(fstcart x = vec 0) /\ drop(sndcart x) IN real_interval[&0,&1] /\
           (f:A->B)((sigma:real^3->real->A) (inv(norm(fstcart x)) % fstcart x)
                                            (drop(sndcart x))) IN FST (c':(B->bool)#(B->real^M)) /\
           sigma (inv(norm(fstcart x)) % fstcart x) (drop(sndcart x)) IN U} =
      {x | ~(fstcart x = vec 0) /\ drop(sndcart x) IN real_interval[&0,&1] /\
           f(sigma (inv(norm(fstcart x)) % fstcart x) (drop(sndcart x))) IN FST (c':(B->bool)#(B->real^M))}
      INTER
      {x | ~(fstcart x = vec 0) /\ drop(sndcart x) IN real_interval[&0,&1] /\
           sigma (inv(norm(fstcart x)) % fstcart x) (drop(sndcart x)) IN U}`
    SUBST1_TAC THENL [SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC OPEN_IN_INTER THEN CONJ_TAC THENL
     [MATCH_MP_TAC P4_SWEEP_PUSH_PIECE_OPEN THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                            `top':B topology`; `W:A->bool`] THEN
      ASM_MESON_TAC[GRGD_ATLAS_CHART];
      MATCH_MP_TAC P4_SWEEP_PIECE_OPEN THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
      ASM_MESON_TAC[SMOOTH_MANIFOLD_ATLAS_CHART]];
    REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[];
    SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC P4_C1_EQ_WITHIN THEN
  EXISTS_TAC
   `(SND (c':(B->bool)#(B->real^M)) o (f:A->B) o chart_inv (U:A->bool,phi:A->real^N)) o
    (\x. phi((sigma:real^3->real->A) (inv(norm(fstcart x)) % fstcart x)
                                     (drop(sndcart x))))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM; o_THM] THEN REPEAT STRIP_TAC THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN
    MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                  `U:A->bool`; `phi:A->real^N`] CHART_INV) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC P4_C1_COMPOSE_WITHIN THEN
  EXISTS_TAC `IMAGE (SND(U:A->bool,phi:A->real^N))
                    {x | x IN FST(U,phi) INTER W /\ (f:A->B) x IN FST (c':(B->bool)#(B->real^M))}` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_SUBSET THEN
    EXISTS_TAC
     `{x | ~(fstcart x = vec 0) /\ drop(sndcart x) IN real_interval[&0,&1] /\
           (sigma:real^3->real->A) (inv(norm(fstcart x)) % fstcart x)
                                   (drop(sndcart x)) IN U}` THEN
    CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o SPEC `(U:A->bool,phi:A->real^N)` o CONJUNCT2 o CONJUNCT2 o
      GEN_REWRITE_RULE I [p4_sweepout]) THEN
    ASM_REWRITE_TAC[FST; SND];
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `top':B topology`; `atlas':((B->bool)#(B->real^M))->bool`;
                   `(U:A->bool,phi:A->real^N)`; `c':(B->bool)#(B->real^M)`;
                   `W:A->bool`; `f:A->B`] MFDM_CHART_DOMAIN_OPEN) THEN
    ASM_SIMP_TAC[];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; FST; SND; IN_INTER] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
    REWRITE_TAC[IN_ELIM_THM; IN_INTER] THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[P4_RADIAL_SPHERE];
    FIRST_X_ASSUM(MP_TAC o SPECL [`(U:A->bool,phi:A->real^N)`;
                                  `c':(B->bool)#(B->real^M)`] o
      GEN_REWRITE_RULE I [mfd_smooth_map]) THEN
    ASM_REWRITE_TAC[]]);;

let P4_SWEEPOUT_PUSH = prove
 (`!top atlas top' atlas' W (f:A->B) (sigma:real^3->real->A).
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
        smooth_manifold_atlas top' (atlas':((B->bool)#(B->real^M))->bool) /\
        open_in top W /\ continuous_map (subtopology top W,top') f /\
        mfd_smooth_map atlas atlas' W f /\
        p4_sweepout (top,atlas) sigma /\
        (!y t. y IN sphere(vec 0,&1) /\ t IN real_interval[&0,&1] ==> sigma y t IN W)
        ==> p4_sweepout (top',atlas') (\y t. f(sigma y t))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p4_sweepout] THEN BETA_TAC THEN
  REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN `(\(y,t). (f:A->B)((sigma:real^3->real->A) y t)) =
                  f o (\(y,t). sigma y t)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
    EXISTS_TAC `subtopology top (W:A->bool)` THEN
    ASM_REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[p4_sweepout];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; TOPSPACE_PROD_TOPOLOGY; FORALL_PAIR_THM;
                  IN_CROSS; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY;
                  TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY] THEN
      ASM_SIMP_TAC[]];
    ASM_MESON_TAC[p4_sweepout];
    X_GEN_TAC `c':(B->bool)#(B->real^M)` THEN DISCH_TAC THEN
    MATCH_MP_TAC P4_SWEEP_PUSH_C1 THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                          `top':B topology`; `atlas':((B->bool)#(B->real^M))->bool`;
                          `W:A->bool`] THEN
    ASM_REWRITE_TAC[]]);;

(* The preferred-chart Jacobian of a composite f o u. *)

let P4_S2_COMPOSE_CONT = prove
 (`!top top' W (f:A->B) (u:real^3->A).
        continuous_map (subtopology top W,top') f /\
        continuous_map (subtopology euclidean (sphere(vec 0,&1)),top) u /\
        (!y. y IN sphere(vec 0,&1) ==> u y IN W)
        ==> continuous_map (subtopology euclidean (sphere(vec 0,&1)),top')
                           (\y. f(u y))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\y. (f:A->B)((u:real^3->A) y)) = f o u` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN EXISTS_TAC `subtopology top (W:A->bool)` THEN
  ASM_REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
  ASM_SIMP_TAC[]);;

let P4_S2_JAC_PUSH = prove
 (`!top atlas top' atlas' W (f:A->B) (u:real^3->A) y.
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
        smooth_manifold_atlas top' (atlas':((B->bool)#(B->real^M))->bool) /\
        open_in top W /\ continuous_map (subtopology top W,top') f /\
        mfd_smooth_map atlas atlas' W f /\
        continuous_map (subtopology euclidean (sphere(vec 0,&1)),top) u /\
        (!y. y IN sphere(vec 0,&1) ==> u y IN W) /\ y IN sphere(vec 0,&1) /\
        (\z. SND (chart_at atlas (u y)) (u(inv(norm z) % z))) differentiable (at y)
        ==> p4_s2_jac atlas' (\y. f(u y)) y =
            matrix(frechet_derivative
                    (SND (chart_at atlas' (f(u y))) o f o
                     chart_inv (chart_at atlas (u y)))
                    (at (SND (chart_at atlas (u y)) (u y)))) **
            p4_s2_jac atlas u y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p4_s2_jac] THEN BETA_TAC THEN
  SUBGOAL_THEN `(u:real^3->A) y IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[P4_S2_IN_TOPSPACE]; ALL_TAC] THEN
  SUBGOAL_THEN `continuous_map (subtopology euclidean (sphere(vec 0,&1)),top')
                               (\y. (f:A->B)((u:real^3->A) y))`
  ASSUME_TAC THENL [ASM_MESON_TAC[P4_S2_COMPOSE_CONT]; ALL_TAC] THEN
  SUBGOAL_THEN `(f:A->B)((u:real^3->A) y) IN topspace top'` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top':B topology`; `\y. (f:A->B)((u:real^3->A) y)`; `y:real^3`]
                  P4_S2_IN_TOPSPACE) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                `(u:real^3->A) y`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `chart_at (atlas:((A->bool)#(A->real^N))->bool) ((u:real^3->A) y)`
               PAIR_SURJECTIVE) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`U:A->bool`; `phi:A->real^N`] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th] THEN RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN
                       ASSUME_TAC th) THEN
  REWRITE_TAC[FST; SND] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^M))->bool`;
                 `(f:A->B)((u:real^3->A) y)`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `chart_at (atlas':((B->bool)#(B->real^M))->bool)
                         ((f:A->B)((u:real^3->A) y))` PAIR_SURJECTIVE) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`V:B->bool`; `psi:B->real^M`] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th] THEN ASSUME_TAC th) THEN
  REWRITE_TAC[FST; SND] THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SND]) THEN
  SUBGOAL_THEN
   `?d. &0 < d /\
        !z. dist(z,y) < d
            ==> ~(z = vec 0) /\ (u:real^3->A)(inv(norm z) % z) IN U /\
                (f:A->B)(u(inv(norm z) % z)) IN V`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `u:real^3->A`; `(U:A->bool,phi:A->real^N)`] P4_RADIAL_CHART_OPEN) THEN
    MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^M))->bool`;
                   `\y. (f:A->B)((u:real^3->A) y)`; `(V:B->bool,psi:B->real^M)`]
                  P4_RADIAL_CHART_OPEN) THEN
    ASM_REWRITE_TAC[FST; IMP_IMP] THEN DISCH_THEN(MP_TAC o MATCH_MP OPEN_INTER) THEN
    REWRITE_TAC[OPEN_CONTAINS_BALL] THEN DISCH_THEN(MP_TAC o SPEC `y:real^3`) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN
      ASM_SIMP_TAC[P4_SPHERE_NONZERO; P4_RADIAL_FIX];
      ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN
    REWRITE_TAC[SUBSET; IN_BALL; IN_INTER; IN_ELIM_THM] THEN
    MESON_TAC[DIST_SYM];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\z. (psi:B->real^M)((f:A->B)((u:real^3->A)(inv(norm z) % z)))) has_derivative
     (frechet_derivative (psi o f o chart_inv (U:A->bool,phi:A->real^N))
                         (at (phi(u y))) o
      frechet_derivative (\z. phi(u(inv(norm z) % z))) (at y))) (at y)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_AT THEN
    EXISTS_TAC `((psi:B->real^M) o (f:A->B) o chart_inv (U:A->bool,phi:A->real^N)) o
                (\z. phi((u:real^3->A)(inv(norm z) % z)))` THEN
    EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN
      AP_TERM_TAC THEN AP_TERM_TAC THEN
      MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                    `U:A->bool`; `phi:A->real^N`] CHART_INV) THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC DIFF_CHAIN_AT THEN
    ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
    ASM_SIMP_TAC[P4_RADIAL_FIX] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `top':B topology`; `atlas':((B->bool)#(B->real^M))->bool`;
                   `W:A->bool`; `f:A->B`; `(U:A->bool,phi:A->real^N)`;
                   `(V:B->bool,psi:B->real^M)`; `(u:real^3->A) y`]
                  GRGD_CHART_MAP_DIFF) THEN
    ASM_SIMP_TAC[FST; SND];
    ALL_TAC] THEN
  REWRITE_TAC[jacobian] THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
  MATCH_MP_TAC MATRIX_COMPOSE THEN CONJ_TAC THEN
  MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[differentiable] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `top':B topology`; `atlas':((B->bool)#(B->real^M))->bool`;
                 `W:A->bool`; `f:A->B`; `(U:A->bool,phi:A->real^N)`;
                 `(V:B->bool,psi:B->real^M)`; `(u:real^3->A) y`]
                GRGD_CHART_MAP_DIFF) THEN
  ASM_SIMP_TAC[FST; SND] THEN MESON_TAC[]);;

(* Connected components of a smooth manifold are open (as APX_COMPONENT_OPEN *)
(* of pc_apx_event, from GEO_MANIFOLD_LOCALLY_PATH_CONNECTED of pc_mfd_diff). *)

let P4_COMPONENT_OPEN = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) C.
        smooth_manifold_atlas top atlas /\ C IN connected_components_of top
        ==> open_in top C`,
  MESON_TAC[OPEN_IN_CONNECTED_COMPONENTS_OF_LOCALLY_CONNECTED_SPACE;
            LOCALLY_PATH_CONNECTED_IMP_LOCALLY_CONNECTED_SPACE;
            GEO_MANIFOLD_LOCALLY_PATH_CONNECTED]);;

(* ------------------------------------------------------------------------- *)
(* Densities under pinch maps.                                               *)
(* ------------------------------------------------------------------------- *)

let P4_DENSITY_LOEWNER = prove
 (`!A B:real^3^3 k.
        positive_semidefinite A /\ positive_semidefinite B /\ &0 <= k /\
        (!w. w dot (B ** w) <= k * (w dot (A ** w)))
        ==> sqrt(p4_e2 B) <= k * sqrt(p4_e2 A)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `p4_e2 B <= k pow 2 * p4_e2(A:real^3^3)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM P4_E2_CMUL] THEN MATCH_MP_TAC P4_E2_MONO THEN
    ASM_REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[positive_semidefinite; symmetric_matrix]) THEN
    ASM_REWRITE_TAC[positive_semidefinite; symmetric_matrix; TRANSP_MATRIX_SUB;
                    TRANSP_MATRIX_CMUL; MATRIX_VECTOR_MUL_SUB_RDISTRIB;
                    MATRIX_VECTOR_LMUL; DOT_RSUB; DOT_RMUL; REAL_SUB_LE];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt(k pow 2 * p4_e2(A:real^3^3))` THEN
  ASM_SIMP_TAC[SQRT_MONO_LE; SQRT_MUL; POW_2_SQRT; REAL_LE_REFL]);;

let P4_SWEEP_SLICE_DIFF = prove
 (`!top atlas (sigma:real^3->real->A) y t.
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
        p4_sweepout (top,atlas) sigma /\
        y IN sphere(vec 0,&1) /\ t IN real_interval[&0,&1]
        ==> (\z. SND (chart_at atlas (sigma y t)) (sigma (inv(norm z) % z) t))
            differentiable (at y)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(sigma:real^3->real->A) y t IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[P4_SLICE_IN_TOPSPACE]; ALL_TAC] THEN
  MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                `(sigma:real^3->real->A) y t`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `chart_at (atlas:((A->bool)#(A->real^N))->bool)
                         ((sigma:real^3->real->A) y t)` PAIR_SURJECTIVE) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`U:A->bool`; `phi:A->real^N`] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[FST; SND] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `sigma:real^3->real->A`; `U:A->bool`; `phi:A->real^N`] P4_SWEEP_C1) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `f':real^(3,1)finite_sum->real^(3,1)finite_sum->real^N`
    (MP_TAC o SPECL [`y:real^3`; `t:real`] o CONJUNCT1)) THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[differentiable]);;

let P4_PINCH_DENSITY = prove
 (`!topX atlasX (gX:A->real^3^3) X topY atlasY (gY:B->real^3^3) Y L p
    (sigma:real^3->real->A) y t.
        smooth_manifold_atlas topX atlasX /\ smooth_manifold_atlas topY atlasY /\
        riemannian_metric atlasX gX /\ riemannian_metric atlasY gY /\
        open_in topX X /\ &0 <= L /\
        p4_pinch_map (topX,atlasX) gX X (topY,atlasY) gY Y L p /\
        p4_sweepout (topX,atlasX) sigma /\
        (!y t. y IN sphere(vec 0,&1) /\ t IN real_interval[&0,&1] ==> sigma y t IN X) /\
        y IN sphere(vec 0,&1) /\ t IN real_interval[&0,&1]
        ==> p4_s2_density atlasY gY (\y. p(sigma y t)) y <=
            L pow 2 * p4_s2_density atlasX gX (\y. sigma y t) y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p4_pinch_map]) THEN
  SUBGOAL_THEN `continuous_map (subtopology topX X,topY) (p:A->B)` ASSUME_TAC THENL
   [ASM_MESON_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY]; ALL_TAC] THEN
  ABBREV_TAC `x = (sigma:real^3->real->A) y t` THEN
  SUBGOAL_THEN `(x:A) IN X /\ x IN topspace topX /\ (p:A->B) x IN topspace topY`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `a /\ (a ==> b /\ c) ==> a /\ b /\ c`) THEN CONJ_TAC THENL
     [EXPAND_TAC "x" THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      DISCH_TAC THEN CONJ_TAC THENL
       [MP_TAC(ISPECL [`topX:A topology`; `X:A->bool`] OPEN_IN_SUBSET) THEN
        ASM_REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        MP_TAC(MATCH_MP CONTINUOUS_MAP_IMAGE_SUBSET_TOPSPACE
          (ASSUME `continuous_map (subtopology topX X,topY) (p:A->B)`)) THEN
        REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; SUBSET; FORALL_IN_IMAGE; IN_INTER] THEN
        DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
        MP_TAC(ISPECL [`topX:A topology`; `X:A->bool`] OPEN_IN_SUBSET) THEN
        ASM_REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                 `topY:B topology`; `atlasY:((B->bool)#(B->real^3))->bool`;
                 `X:A->bool`; `p:A->B`; `\y. (sigma:real^3->real->A) y t`; `y:real^3`]
                P4_S2_JAC_PUSH) THEN
  BETA_TAC THEN ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`]
                           P4_SWEEP_SLICE_CONT) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    EXPAND_TAC "x" THEN
    MATCH_MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`]
                        P4_SWEEP_SLICE_DIFF) THEN ASM_REWRITE_TAC[];
    DISCH_TAC] THEN
  REWRITE_TAC[p4_s2_density] THEN MATCH_MP_TAC P4_DENSITY_LOEWNER THEN
  SIMP_TAC[REAL_LE_POW_2] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC P4_GRAM_PSD THEN BETA_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC P4_RIEMANNIAN_PSD THEN
    MAP_EVERY EXISTS_TAC [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`] THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC P4_GRAM_PSD THEN BETA_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC P4_RIEMANNIAN_PSD THEN
    MAP_EVERY EXISTS_TAC [`topY:B topology`; `atlasY:((B->bool)#(B->real^3))->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `w:real^3` THEN REWRITE_TAC[P4_GRAM_QF] THEN BETA_TAC THEN
  ASM_REWRITE_TAC[GSYM MATRIX_VECTOR_MUL_ASSOC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`x:A`; `p4_s2_jac (atlasX:((A->bool)#(A->real^3))->bool) (\y. (sigma:real^3->real->A) y t) y ** w`] o
    check (fun th -> can (find_term (fun t -> t = `L:real`)) (concl th) &&
                     is_forall(concl th))) THEN
  ASM_REWRITE_TAC[jacobian] THEN
  SUBGOAL_THEN
   `(\y. SND (chart_at (atlasY:((B->bool)#(B->real^3))->bool) ((p:A->B) x))
           (p (chart_inv (chart_at (atlasX:((A->bool)#(A->real^3))->bool) x) y))) =
    SND (chart_at atlasY (p x)) o p o chart_inv (chart_at atlasX x)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Sweep areas under pinch maps: P4_PINCH_AREA_STATEMENT.                   *)
(* ------------------------------------------------------------------------- *)

let P4_SUP_SCALE_LE = prove
 (`!f g k. &0 <= k /\ (?B. !t. t IN real_interval[&0,&1] ==> g t <= B) /\
           (!t. t IN real_interval[&0,&1] ==> f t <= k * g t)
           ==> sup {f t | t IN real_interval[&0,&1]} <=
               k * sup {g t | t IN real_interval[&0,&1]}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_SUP_LE THEN
  REWRITE_TAC[FORALL_IN_GSPEC; SIMPLE_IMAGE; IMAGE_EQ_EMPTY; REAL_INTERVAL_EQ_EMPTY] THEN
  CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `t:real` THEN DISCH_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `k * (g:real->real) t` THEN ASM_SIMP_TAC[] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC ELEMENT_LE_SUP THEN CONJ_TAC THENL
   [EXISTS_TAC `B:real` THEN REWRITE_TAC[FORALL_IN_IMAGE] THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]]);;

let P4_PINCH_AREA = prove
 (`P4_PINCH_AREA_STATEMENT (:A) (:B)`,
  REWRITE_TAC[P4_PINCH_AREA_STATEMENT] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `open_in topX (X:A->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`]
                        P4_COMPONENT_OPEN) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p4_pinch_map]) THEN
  SUBGOAL_THEN `continuous_map (subtopology topX X,topY) (p:A->B)` ASSUME_TAC THENL
   [ASM_MESON_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!y t. y IN sphere(vec 0,&1) /\ t IN real_interval[&0,&1]
          ==> (p:A->B)((sigma:real^3->real->A) y t) IN Y`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(MATCH_MP CONTINUOUS_MAP_IMAGE_SUBSET_TOPSPACE
      (ASSUME `continuous_map (subtopology topX X,subtopology topY Y) (p:A->B)`)) THEN
    REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; SUBSET; FORALL_IN_IMAGE; IN_INTER] THEN
    DISCH_THEN(MP_TAC o SPEC `(sigma:real^3->real->A) y t`) THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN CONJ_TAC THENL
     [MATCH_MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`]
                          P4_SLICE_IN_TOPSPACE) THEN ASM_REWRITE_TAC[];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `p4_sweepout (topY,atlasY:((B->bool)#(B->real^3))->bool)
                             (\y t. (p:A->B)((sigma:real^3->real->A) y t))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`]
                        P4_SWEEPOUT_PUSH) THEN
    EXISTS_TAC `X:A->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[p4_sweep_area] THEN BETA_TAC THEN
  MATCH_MP_TAC P4_SUP_SCALE_LE THEN REWRITE_TAC[REAL_LE_POW_2] THEN CONJ_TAC THENL
   [MATCH_MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`]
                        P4_SWEEP_AREA_BOUND) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `t:real` THEN DISCH_TAC THEN REWRITE_TAC[p4_s2_area] THEN
  SUBGOAL_THEN
   `(\y. lift(p4_s2_density (atlasX:((A->bool)#(A->real^3))->bool) (gX:A->real^3^3)
                (\y. (sigma:real^3->real->A) y t) y))
    continuous_on sphere(vec 0,&1) /\
    (\y. lift(p4_s2_density (atlasY:((B->bool)#(B->real^3))->bool) (gY:B->real^3^3)
                (\y. (p:A->B)(sigma y t)) y))
    continuous_on sphere(vec 0,&1)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`]
                          P4_SLICE_DENSITY_CONT) THEN ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`topY:B topology`; `atlasY:((B->bool)#(B->real^3))->bool`;
                     `gY:B->real^3^3`;
                     `\y t. (p:A->B)((sigma:real^3->real->A) y t)`; `t:real`]
                    P4_SLICE_DENSITY_CONT) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `p4_s2_integral (\y. L pow 2 *
                p4_s2_density (atlasX:((A->bool)#(A->real^3))->bool) (gX:A->real^3^3)
                  (\y. (sigma:real^3->real->A) y t) y)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC P4_S2_INTEGRAL_MONO THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[LIFT_CMUL] THEN MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN
      ASM_REWRITE_TAC[];
      X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN MATCH_MP_TAC P4_PINCH_DENSITY THEN
      MAP_EVERY EXISTS_TAC [`topX:A topology`; `X:A->bool`; `topY:B topology`;
                            `Y:B->bool`] THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC P4_S2_INTEGRAL_CMUL THEN
    ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* Isometry invariance of the width                                          *)
(* (P4_CM_ISOMETRY_STATEMENT): essential maps under homeomorphisms, Gram    *)
(* matrices under isometries, sweep areas and widths.                        *)
(* ========================================================================= *)

let P4_S2_INTEGRAL_EQ = prove
 (`!f g:real^3->real.
        (!y. y IN sphere(vec 0,&1) ==> f y = g y)
        ==> p4_s2_integral f = p4_s2_integral g`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p4_s2_integral] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC INTEGRAL_SPIKE THEN
  EXISTS_TAC `{vec 0:real^3}` THEN REWRITE_TAC[NEGLIGIBLE_SING] THEN
  REWRITE_TAC[IN_DIFF; IN_SING] THEN REPEAT STRIP_TAC THEN
  AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_SIMP_TAC[P4_RADIAL_SPHERE]);;

let P4_ESSENTIAL_HOMEO = prove
 (`!top top' (f:A->B) (e3:real^4->A).
        homeomorphic_map (top,top') f /\ p4_essential top e3
        ==> p4_essential top' (f o e3)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p4_essential] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  SUBGOAL_THEN `continuous_map (top,top') (f:A->B)` ASSUME_TAC THENL
   [ASM_MESON_TAC[HOMEOMORPHIC_IMP_CONTINUOUS_MAP]; ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `a /\ (b ==> c) ==> b ==> a /\ c`) THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`&3:int`; `subtopology euclidean (sphere(vec 0:real^4,&1))`;
                 `top:A topology`; `top':B topology`; `e3:real^4->A`; `f:A->B`]
                HOM_INDUCED_COMPOSE_EMPTY) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[o_THM] THEN
  MP_TAC(ISPECL [`&3:int`; `top:A topology`; `top':B topology`; `f:A->B`]
                HOMEOMORPHIC_MAP_HOMOLOGY_GROUP_ISOMORPHISM) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o MATCH_MP GROUP_ISOMORPHISM_IMP_MONOMORPHISM) THEN
  REWRITE_TAC[group_monomorphism] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (STRIP_ASSUME_TAC o REWRITE_RULE[group_homomorphism])
    ASSUME_TAC) THEN
  MP_TAC(ISPECL [`&3:int`; `subtopology euclidean (sphere(vec 0:real^4,&1))`;
                 `top:A topology`; `e3:real^4->A`]
                GROUP_HOMOMORPHISM_HOM_INDUCED_EMPTY) THEN
  REWRITE_TAC[group_homomorphism; SUBSET; FORALL_IN_IMAGE] THEN
  DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  ASM_MESON_TAC[GROUP_ID]);;

(* Gram matrices of slices are preserved by isometries. *)

let P4_ISOMETRY_METRIC = prove
 (`!top atlas (g:A->real^N^N) top' atlas' (g':B->real^N^N) f f' x.
        smooth_manifold_atlas top atlas /\ smooth_manifold_atlas top' atlas' /\
        mfd_isometry (top,atlas) g (top',atlas') g' f f' /\ x IN topspace top
        ==> g x =
            transp(matrix(frechet_derivative
                    (SND (chart_at atlas' (f x)) o f o chart_inv (chart_at atlas x))
                    (at (SND (chart_at atlas x) x)))) **
            g'(f x) **
            matrix(frechet_derivative
                    (SND (chart_at atlas' (f x)) o f o chart_inv (chart_at atlas x))
                    (at (SND (chart_at atlas x) x)))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP GRGD_ISOMETRY_FACTS) THEN
  SUBGOAL_THEN `(f:A->B) x IN topspace top'` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`]
                CHART_AT) THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                 `(f:A->B) x`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o CONJUNCT2 o GEN_REWRITE_RULE I [mfd_isometry]) THEN
  DISCH_THEN(MP_TAC o SPECL
   [`chart_at (atlas:((A->bool)#(A->real^N))->bool) x`;
    `chart_at (atlas':((B->bool)#(B->real^N))->bool) ((f:A->B) x)`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `SND (chart_at (atlas:((A->bool)#(A->real^N))->bool) x) x`) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`] METRIC_LOCAL_AT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[mpullback; o_THM] THEN
  SUBGOAL_THEN
   `chart_inv (chart_at (atlas:((A->bool)#(A->real^N))->bool) x)
              (SND (chart_at atlas x) x) = x`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `chart_at (atlas:((A->bool)#(A->real^N))->bool) x`] MFDM_CHART) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                 `g':B->real^N^N`; `(f:A->B) x`] METRIC_LOCAL_AT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[]);;

let P4_ISOMETRY_GRAM = prove
 (`!top atlas (g:A->real^N^N) top' atlas' (g':B->real^N^N) f f' (u:real^3->A) y.
        smooth_manifold_atlas top atlas /\ smooth_manifold_atlas top' atlas' /\
        mfd_isometry (top,atlas) g (top',atlas') g' f f' /\
        continuous_map (subtopology euclidean (sphere(vec 0,&1)),top) u /\
        y IN sphere(vec 0,&1) /\
        (\z. SND (chart_at atlas (u y)) (u(inv(norm z) % z))) differentiable (at y)
        ==> p4_s2_gram atlas' g' (\y. f(u y)) y = p4_s2_gram atlas g u y`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP GRGD_ISOMETRY_FACTS) THEN
  SUBGOAL_THEN `!y. y IN sphere(vec 0,&1) ==> (u:real^3->A) y IN topspace top`
  ASSUME_TAC THENL [ASM_MESON_TAC[P4_S2_IN_TOPSPACE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                 `topspace top:A->bool`; `f:A->B`; `u:real^3->A`; `y:real^3`]
                P4_S2_JAC_PUSH) THEN
  ASM_REWRITE_TAC[OPEN_IN_TOPSPACE] THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[p4_s2_gram] THEN BETA_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `top':B topology`;
                 `atlas':((B->bool)#(B->real^N))->bool`; `g':B->real^N^N`;
                 `f:A->B`; `f':B->A`; `(u:real^3->A) y`] P4_ISOMETRY_METRIC) THEN
  ASM_SIMP_TAC[] THEN DISCH_THEN(K ALL_TAC) THEN
  REWRITE_TAC[MATRIX_TRANSP_MUL; MATRIX_MUL_ASSOC]);;

(* Sweepouts and sweep areas transported by isometries. *)

let P4_ISOMETRY_HOMEO = prove
 (`!top atlas (g:A->real^N^N) top' atlas' (g':B->real^N^N) f f'.
        mfd_isometry (top,atlas) g (top',atlas') g' f f'
        ==> homeomorphic_map (top,top') f`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mfd_isometry; mfd_diffeo; SUBTOPOLOGY_TOPSPACE] THEN
  MESON_TAC[HOMEOMORPHIC_MAPS_MAP]);;

let P4_ISOMETRY_SWEEP = prove
 (`!top atlas (g:A->real^N^N) top' atlas' (g':B->real^N^N) f f'
    (sigma:real^3->real->A).
        smooth_manifold_atlas top atlas /\ smooth_manifold_atlas top' atlas' /\
        mfd_isometry (top,atlas) g (top',atlas') g' f f' /\
        p4_sweepout_in (top,atlas) (topspace top) sigma
        ==> p4_sweepout_in (top',atlas') (topspace top') (\y t. f(sigma y t)) /\
            p4_sweep_area atlas' g' (\y t. f(sigma y t)) = p4_sweep_area atlas g sigma`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p4_sweepout_in] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP GRGD_ISOMETRY_FACTS) THEN
  SUBGOAL_THEN `p4_sweepout (top',atlas':((B->bool)#(B->real^N))->bool)
                             (\y t. (f:A->B)((sigma:real^3->real->A) y t))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`]
                        P4_SWEEPOUT_PUSH) THEN
    EXISTS_TAC `topspace top:A->bool` THEN ASM_REWRITE_TAC[OPEN_IN_TOPSPACE];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET; FORALL_IN_IMAGE] o
      check (fun th -> can (find_term ((=) `f:A->B`)) (concl th) &&
                       can (find_term ((=) `IMAGE:(A->B)->(A->bool)->B->bool`)) (concl th))) THEN
    ASM_SIMP_TAC[];
    RULE_ASSUM_TAC(REWRITE_RULE[SUBTOPOLOGY_TOPSPACE]) THEN
    REWRITE_TAC[SUBTOPOLOGY_TOPSPACE; P4_SUSP_COMPOSE] THEN
    MATCH_MP_TAC P4_ESSENTIAL_HOMEO THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P4_ISOMETRY_HOMEO THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                          `atlas':((B->bool)#(B->real^N))->bool`; `g':B->real^N^N`;
                          `f':B->A`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[p4_sweep_area] THEN BETA_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC(SET_RULE
   `(!t:real. t IN s ==> (f:real->real) t = g t)
    ==> {f t | t IN s} = {g t | t IN s}`) THEN
  X_GEN_TAC `t:real` THEN DISCH_TAC THEN REWRITE_TAC[p4_s2_area] THEN
  MATCH_MP_TAC P4_S2_INTEGRAL_EQ THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
  REWRITE_TAC[p4_s2_density] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `top':B topology`;
                 `atlas':((B->bool)#(B->real^N))->bool`; `g':B->real^N^N`;
                 `f:A->B`; `f':B->A`; `\y. (sigma:real^3->real->A) y t`; `y:real^3`]
                P4_ISOMETRY_GRAM) THEN
  BETA_TAC THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`]
                        P4_SWEEP_SLICE_CONT) THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`]
                        P4_SWEEP_SLICE_DIFF) THEN ASM_REWRITE_TAC[]]);;

let P4_CM_ISOMETRY = prove
 (`P4_CM_ISOMETRY_STATEMENT (:A) (:B)`,
  REWRITE_TAC[P4_CM_ISOMETRY_STATEMENT] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `mfd_isometry (top',atlas') (g':B->real^3^3) (top,atlas) (g:A->real^3^3)
                 iota' iota`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_ISOMETRY_INVERSE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `{p4_sweep_area atlas' (g':B->real^3^3) sigma' | sigma' |
     p4_sweepout_in (top',atlas') (topspace top') sigma'} =
    {p4_sweep_area atlas (g:A->real^3^3) sigma | sigma |
     p4_sweepout_in (top,atlas) (topspace top) sigma}`
  ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `w:real` THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `sigma':real^3->real->B` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `\y t. (iota':B->A)((sigma':real^3->real->B) y t)` THEN
      MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                     `g':B->real^3^3`; `top:A topology`;
                     `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                     `iota':B->A`; `iota:A->B`; `sigma':real^3->real->B`]
                    P4_ISOMETRY_SWEEP) THEN
      ASM_SIMP_TAC[];
      DISCH_THEN(X_CHOOSE_THEN `sigma:real^3->real->A` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `\y t. (iota:A->B)((sigma:real^3->real->A) y t)` THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                     `g:A->real^3^3`; `top':B topology`;
                     `atlas':((B->bool)#(B->real^3))->bool`; `g':B->real^3^3`;
                     `iota:A->B`; `iota':B->A`; `sigma:real^3->real->A`]
                    P4_ISOMETRY_SWEEP) THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[p4_cm_width; REAL_LE_REFL] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [p4_cm_adm] o
    check (fun th -> can (find_term (fun t -> try fst(dest_const t) = "p4_cm_adm"
                                              with Failure _ -> false)) (concl th))) THEN
  REWRITE_TAC[p4_cm_adm] THEN
  DISCH_THEN(X_CHOOSE_THEN `sigma:real^3->real->A` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `\y t. (iota:A->B)((sigma:real^3->real->A) y t)` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `top':B topology`;
                 `atlas':((B->bool)#(B->real^3))->bool`; `g':B->real^3^3`;
                 `iota:A->B`; `iota':B->A`; `sigma:real^3->real->A`]
                P4_ISOMETRY_SWEEP) THEN
  ASM_SIMP_TAC[]);;

(* ========================================================================= *)
(* Uniform bounds along a Ricci flow on a compact manifold:                  *)
(* families of quadratic forms on compact parameter sets, time slices of     *)
(* jointly smooth maps, the chart pieces of a compact manifold, and the      *)
(* comparison of the metrics g(s), g(t) and of the Ricci forms with g(t)    *)
(* (first and second order in s - t).                                       *)
(* ========================================================================= *)

let P4_QF_NORM_BOUND = prove
 (`!(A:real^N^N) v. abs(v dot (A ** v)) <= norm(vectorize A) * norm v pow 2`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `norm(v:real^N) * norm((A:real^N^N) ** v)` THEN
  REWRITE_TAC[NORM_CAUCHY_SCHWARZ_ABS] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `norm(v:real^N) * (norm(vectorize(A:real^N^N)) * norm v)` THEN
  SIMP_TAC[REAL_LE_LMUL; NORM_POS_LE; COMPATIBLE_NORM_VECTORIZE] THEN
  REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC);;

(* Uniform upper bound for a continuous family of quadratic forms. *)

let P4_FAMILY_UPPER = prove
 (`!(H:real^M->real^N^N) S.
        compact S /\ (\z. vectorize(H z)) continuous_on S
        ==> ?M. &0 <= M /\
                !z v. z IN S ==> abs(v dot (H z ** v)) <= M * norm v pow 2`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `IMAGE (\z. vectorize((H:real^M->real^N^N) z)) S` COMPACT_IMP_BOUNDED) THEN
  ASM_SIMP_TAC[COMPACT_CONTINUOUS_IMAGE] THEN
  REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `M:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `M:real` THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `norm(vectorize((H:real^M->real^N^N) z)) * norm(v:real^N) pow 2` THEN
  REWRITE_TAC[P4_QF_NORM_BOUND] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
  ASM_SIMP_TAC[REAL_LE_POW_2]);;

(* Uniform positive lower bound for a continuous family of positive definite *)
(* quadratic forms on a compact parameter set.                               *)

let P4_FAMILY_LOWER = prove
 (`!(G:real^M->real^N^N) S.
        compact S /\ (\z. vectorize(G z)) continuous_on S /\
        (!z v. z IN S /\ ~(v = vec 0) ==> &0 < v dot (G z ** v))
        ==> ?m. &0 < m /\
                !z v. z IN S ==> m * norm v pow 2 <= v dot (G z ** v)`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `S:real^M->bool = {}` THENL
   [EXISTS_TAC `&1` THEN ASM_REWRITE_TAC[NOT_IN_EMPTY; REAL_LT_01]; ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\p:real^(M,N)finite_sum.
       sndcart p dot ((G:real^M->real^N^N) (fstcart p) ** sndcart p)`;
    `(S:real^M->bool) PCROSS sphere(vec 0:real^N,&1)`] CONTINUOUS_ATTAINS_INF) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_PCROSS THEN ASM_REWRITE_TAC[COMPACT_SPHERE];
      ASM_REWRITE_TAC[PCROSS_EQ_EMPTY; SPHERE_EQ_EMPTY] THEN REAL_ARITH_TAC;
      REWRITE_TAC[o_DEF] THEN MATCH_MP_TAC CONTINUOUS_ON_LIFT_DOT2 THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN REWRITE_TAC[LINEAR_SNDCART];
        ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_ON_MATRIX_VECTOR_MUL THEN CONJ_TAC THENL
       [ALL_TAC;
        MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN REWRITE_TAC[LINEAR_SNDCART]] THEN
      SUBGOAL_THEN
       `(vectorize:real^N^N->real^(N,N)finite_prod) o
        (\p:real^(M,N)finite_sum. (G:real^M->real^N^N) (fstcart p)) =
        (\z. vectorize(G z)) o fstcart`
      SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
       [MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN REWRITE_TAC[LINEAR_FSTCART];
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `S:real^M->bool` THEN
        ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_PCROSS; FSTCART_PASTECART] THEN
        SIMP_TAC[]]];
    ALL_TAC] THEN
  REWRITE_TAC[EXISTS_IN_PCROSS; FORALL_IN_PCROSS; FSTCART_PASTECART;
              SNDCART_PASTECART; IN_SPHERE_0] THEN
  DISCH_THEN(X_CHOOSE_THEN `z0:real^M` (X_CHOOSE_THEN `u0:real^N`
    STRIP_ASSUME_TAC)) THEN
  ABBREV_TAC `m = u0 dot ((G:real^M->real^N^N) z0 ** u0)` THEN
  SUBGOAL_THEN `&0 < m` ASSUME_TAC THENL
   [EXPAND_TAC "m" THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN UNDISCH_TAC `norm(u0:real^N) = &1` THEN
    ASM_REWRITE_TAC[NORM_0] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `m:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`z:real^M`; `v:real^N`] THEN DISCH_TAC THEN
  ASM_CASES_TAC `v:real^N = vec 0` THENL
   [ASM_REWRITE_TAC[NORM_0; DOT_LZERO] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`z:real^M`; `inv(norm v) % v:real^N`]) THEN
  ASM_REWRITE_TAC[NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM] THEN
  ASM_SIMP_TAC[REAL_MUL_LINV; NORM_EQ_0; GRGD_QUAD_HOMOG] THEN
  SUBGOAL_THEN `&0 < norm(v:real^N)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  ABBREV_TAC `q = v dot ((G:real^M->real^N^N) z ** v)` THEN
  ABBREV_TAC `n = norm(v:real^N)` THEN DISCH_TAC THEN
  SUBGOAL_THEN `q = (inv n * inv n * q) * n pow 2` SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < n` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
  ASM_REWRITE_TAC[REAL_MUL_ASSOC]);;

(* Time slices of a jointly differentiable map on real^1 x real^N, through   *)
(* a linear functional.                                                      *)

let P4_TIME_SLICE_DERIV = prove
 (`!(Fm:real^(1,N)finite_sum->real^P) (lam:real^P->real^1) t w.
        Fm differentiable (at (pastecart (lift t) w)) /\ linear lam
        ==> ((\s. drop(lam(Fm(pastecart (lift s) w)))) has_real_derivative
             drop(lam(frechet_derivative Fm (at (pastecart (lift t) w))
                                            (pastecart (vec 1) (vec 0)))))
            (atreal t)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[HAS_REAL_VECTOR_DERIVATIVE_AT] THEN
  REWRITE_TAC[o_DEF; LIFT_DROP] THEN REWRITE_TAC[has_vector_derivative] THEN
  ABBREV_TAC `D = frechet_derivative (Fm:real^(1,N)finite_sum->real^P)
                    (at (pastecart (lift t) w))` THEN
  SUBGOAL_THEN `linear(D:real^(1,N)finite_sum->real^P)` ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\h:real^1. drop h % (lam:real^P->real^1)
                  ((D:real^(1,N)finite_sum->real^P) (pastecart (vec 1) (vec 0)))) =
    lam o D o (\h. pastecart h (vec 0:real^N))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM] THEN X_GEN_TAC `h:real^1` THEN
    SUBGOAL_THEN `pastecart (h:real^1) (vec 0:real^N) =
                  drop h % pastecart (vec 1) (vec 0)` SUBST1_TAC THENL
     [REWRITE_TAC[GSYM PASTECART_CMUL; VECTOR_MUL_RZERO] THEN
      REWRITE_TAC[GSYM LIFT_EQ_CMUL; LIFT_DROP];
      ASM_SIMP_TAC[LINEAR_CMUL]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\x:real^1. (lam:real^P->real^1)((Fm:real^(1,N)finite_sum->real^P)
                                      (pastecart x w))) =
    lam o Fm o (\x. pastecart x w)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC DIFF_CHAIN_AT THEN CONJ_TAC THENL
   [ALL_TAC; ASM_SIMP_TAC[HAS_DERIVATIVE_LINEAR]] THEN
  MATCH_MP_TAC DIFF_CHAIN_AT THEN CONJ_TAC THENL
   [MATCH_MP_TAC HAS_DERIVATIVE_PASTECART THEN
    REWRITE_TAC[HAS_DERIVATIVE_ID; HAS_DERIVATIVE_CONST];
    EXPAND_TAC "D" THEN ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS]]);;

(* The quadratic form of a vectorized matrix is a linear functional. *)

let P4_LINEAR_QF = prove
 (`!u:real^N. linear (\x:real^(N,N)finite_prod. lift(u dot (matrify x ** u)))`,
  REWRITE_TAC[linear; MATRIFY_ADD; MATRIFY_CMUL; MATRIX_VECTOR_MUL_ADD_RDISTRIB;
              MATRIX_VECTOR_LMUL; DOT_RADD; DOT_RMUL; LIFT_ADD; LIFT_CMUL]);;

(* Chart preimages of open sets are open; finitely many compact chart       *)
(* pieces cover a compact manifold.                                          *)

let P4_CHART_PREIMAGE_OPEN = prove
 (`!top atlas (U:A->bool) (phi:A->real^N) B.
        smooth_manifold_atlas top atlas /\ (U,phi) IN atlas /\ open B
        ==> open_in top {y | y IN U /\ phi y IN B}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                `U:A->bool`; `phi:A->real^N`] SMOOTH_MANIFOLD_ATLAS_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN MATCH_MP_TAC OPEN_IN_TRANS_FULL THEN
  EXISTS_TAC `U:A->bool` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`phi:A->real^N`; `subtopology top (U:A->bool)`;
                 `euclidean:(real^N)topology`; `B:real^N->bool`]
                OPEN_IN_CONTINUOUS_MAP_PREIMAGE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[OPEN_IN_EUCLIDEAN] THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP HOMEOMORPHIC_IMP_CONTINUOUS_MAP) THEN
    SIMP_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY];
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
    REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; EXTENSION; IN_ELIM_THM; IN_INTER] THEN
    X_GEN_TAC `z:A` THEN
    MP_TAC(ISPECL [`top:A topology`; `U:A->bool`] OPEN_IN_SUBSET) THEN
    ASM_REWRITE_TAC[SUBSET] THEN MESON_TAC[]]);;

let P4_CHART_PIECES = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool).
        compact_space top /\ smooth_manifold_atlas top atlas
        ==> ?k r. FINITE k /\ k SUBSET topspace top /\
                  (!x. x IN k
                       ==> &0 < r x /\
                           cball(SND(chart_at atlas x) x,r x) SUBSET
                           IMAGE (SND(chart_at atlas x)) (FST(chart_at atlas x))) /\
                  (!y. y IN topspace top
                       ==> ?x. x IN k /\ y IN FST(chart_at atlas x) /\
                               SND(chart_at atlas x) y IN
                               cball(SND(chart_at atlas x) x,r x))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!x. ?r. x IN topspace top
            ==> &0 < r /\
                cball(SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) x) x,r)
                SUBSET IMAGE (SND(chart_at atlas x)) (FST(chart_at atlas x))`
  MP_TAC THENL
   [X_GEN_TAC `x:A` THEN REWRITE_TAC[RIGHT_EXISTS_IMP_THM] THEN DISCH_TAC THEN
    MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`]
                 CHART_AT) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `chart_at (atlas:((A->bool)#(A->real^N))->bool) x`] MFDM_CHART) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_CONTAINS_CBALL] o
      check (fun th -> can (find_term (fun t -> try fst(dest_const t) = "open"
                                                with Failure _ -> false)) (concl th) &&
                       not (is_forall(concl th)))) THEN
    DISCH_THEN MATCH_MP_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[SKOLEM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `r:A->real` (LABEL_TAC "r"))] THEN
  ABBREV_TAC
   `O = \x:A. {y | y IN FST(chart_at (atlas:((A->bool)#(A->real^N))->bool) x) /\
                   SND(chart_at atlas x) y IN ball(SND(chart_at atlas x) x,r x)}` THEN
  SUBGOAL_THEN `!x:A. x IN topspace top ==> open_in top (O x) /\ x IN O x`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`]
                 CHART_AT) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN EXPAND_TAC "O" THEN CONJ_TAC THENL
     [MP_TAC(ISPEC `chart_at (atlas:((A->bool)#(A->real^N))->bool) x` PAIR_SURJECTIVE) THEN
      REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [`U:A->bool`; `phi:A->real^N`] THEN
      DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th]) THEN
      REWRITE_TAC[FST; SND] THEN MATCH_MP_TAC P4_CHART_PREIMAGE_OPEN THEN
      EXISTS_TAC `atlas:((A->bool)#(A->real^N))->bool` THEN
      ASM_REWRITE_TAC[OPEN_BALL];
      REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[CENTRE_IN_BALL] THEN
      USE_THEN "r" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(x:A) IN topspace top`))) THEN
      SIMP_TAC[]];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT2 o GEN_REWRITE_RULE I [compact_in] o
    GEN_REWRITE_RULE I [compact_space]) THEN
  DISCH_THEN(MP_TAC o SPEC `IMAGE (O:A->A->bool) (topspace top)`) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FORALL_IN_IMAGE; SUBSET; IN_UNIONS; EXISTS_IN_IMAGE] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `V:(A->bool)->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`O:A->A->bool`; `topspace top:A->bool`; `V:(A->bool)->bool`]
                FINITE_SUBSET_IMAGE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:A->bool` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`k:A->bool`; `r:A->real`] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `x:A` THEN DISCH_TAC THEN USE_THEN "r" MATCH_MP_TAC THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `y:A` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(y:A) IN UNIONS (IMAGE (O:A->A->bool) k)` MP_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[IN_UNIONS; EXISTS_IN_IMAGE] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `x:A` THEN
  EXPAND_TAC "O" THEN REWRITE_TAC[IN_ELIM_THM] THEN
  SIMP_TAC[REWRITE_RULE[SUBSET] BALL_SUBSET_CBALL]);;

let P4_RF_RIEMANNIAN = prove
 (`!top atlas (g:real->A->real^N^N) a b t.
        ricci_flow_from (top,atlas) a b g /\ a <= t /\ t < b
        ==> riemannian_metric atlas (g t)`,
  REWRITE_TAC[ricci_flow_from; ricci_flow_on] THEN REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `t:real = a` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC);;

(* A matrix field at x through any chart containing x. *)

let P4_METRIC_LOCAL_CHANGE = prove
 (`!top atlas (Q:A->real^N^N) (U:A->bool) (phi:A->real^N) x.
        smooth_manifold_atlas top atlas /\ (U,phi) IN atlas /\ x IN U
        ==> Q x = transp(matrix(chart_jac (chart_at atlas x) (U,phi) x)) **
                  metric_local atlas (U,phi) Q (phi x) **
                  matrix(chart_jac (chart_at atlas x) (U,phi) x)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[SMOOTH_MANIFOLD_ATLAS_CHART; OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
  MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                `Q:A->real^N^N`; `x:A`] METRIC_LOCAL_AT) THEN
  MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`]
               CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)` PAIR_SURJECTIVE) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`V:A->bool`; `psi:A->real^N`] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[FST; SND] THEN STRIP_TAC THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC METRIC_LOCAL_JAC THEN EXISTS_TAC `top:A topology` THEN
  ASM_REWRITE_TAC[IN_INTER]);;

let P4_QF_SUM = prove
 (`!(A:real^N^N) v.
        v dot (A ** v) =
        sum(1..dimindex(:N)) (\i. sum(1..dimindex(:N)) (\j. v$i * A$i$j * v$j))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[dot] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  ASM_SIMP_TAC[matrix_vector_mul; LAMBDA_BETA; GSYM SUM_LMUL] THEN
  REWRITE_TAC[REAL_MUL_ASSOC]);;

(* The flow equation on quadratic forms in preferred coordinates. *)

let P4_RF_PREFERRED_DERIV = prove
 (`!top atlas (g:real->A->real^N^N) a b t x v.
        ricci_flow_on (top,atlas) a b g /\ a < t /\ t < b /\ x IN topspace top
        ==> ((\s. v dot (g s x ** v)) has_real_derivative
             (v dot ((--(&2) %% mfd_ricci_matrix atlas (g t) x) ** v))) (atreal t)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o
    GEN_REWRITE_RULE I [ricci_flow_on]) THEN
  DISCH_THEN(MP_TAC o SPECL [`t:real`; `x:A`]) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN REWRITE_TAC[P4_QF_SUM] THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUM THEN
  REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  BETA_TAC THEN MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUM THEN
  REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  BETA_TAC THEN ASM_SIMP_TAC[MATRIX_CMUL_COMPONENT] THEN
  SUBGOAL_THEN
   `(\s. (v:real^N)$i * (g:real->A->real^N^N) s x$i$j * v$j) =
    (\s. (v$i * v$j) * g s x$i$j)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `(v:real^N)$i * (--(&2) * mfd_ricci_matrix atlas ((g:real->A->real^N^N) t) x$i$j) * v$j =
    (v$i * v$j) * (--(&2) * mfd_ricci_matrix atlas (g t) x$i$j)`
  SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_LMUL_ATREAL THEN ASM_SIMP_TAC[]);;

(* First- and second-order bounds for a real function with bounded first   *)
(* and second derivatives on an interval.                                    *)

let P4_REAL_TAYLOR2 = prove
 (`!psi psi1 psi2 a t1 B1 B2.
        (!x. x IN real_interval[a,t1]
             ==> (psi has_real_derivative psi1 x) (atreal x within real_interval[a,t1]) /\
                 (psi1 has_real_derivative psi2 x) (atreal x within real_interval[a,t1]) /\
                 abs(psi1 x) <= B1 /\ abs(psi2 x) <= B2)
        ==> (!s t. s IN real_interval[a,t1] /\ t IN real_interval[a,t1]
                   ==> abs(psi s - psi t) <= B1 * abs(s - t)) /\
            (!s t. s IN real_interval[a,t1] /\ t IN real_interval[a,t1] /\ t <= s
                   ==> abs(psi s - psi t - (s - t) * psi1 t) <= B2 * (s - t) pow 2)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!s t. s IN real_interval[a,t1] /\ t IN real_interval[a,t1]
          ==> abs((psi1:real->real) s - psi1 t) <= B2 * abs(s - t)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_DIFFERENTIABLE_BOUND THEN EXISTS_TAC `psi2:real->real` THEN
    ASM_SIMP_TAC[IS_REALINTERVAL_INTERVAL];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_DIFFERENTIABLE_BOUND THEN EXISTS_TAC `psi1:real->real` THEN
    ASM_SIMP_TAC[IS_REALINTERVAL_INTERVAL];
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `real_interval[t,s] SUBSET real_interval[a,t1]` ASSUME_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[IN_REAL_INTERVAL]) THEN
    REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\x. (psi:real->real) x - x * psi1(t:real)`;
                 `\x. (psi1:real->real) x - psi1(t:real)`;
                 `real_interval[t,s]`; `B2 * (s - t)`] REAL_DIFFERENTIABLE_BOUND) THEN
  REWRITE_TAC[IS_REALINTERVAL_INTERVAL] THEN ANTS_TAC THENL
   [X_GEN_TAC `x:real` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:real) IN real_interval[a,t1]` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUB THEN CONJ_TAC THENL
       [MATCH_MP_TAC HAS_REAL_DERIVATIVE_WITHIN_SUBSET THEN
        EXISTS_TAC `real_interval[a,t1]` THEN ASM_SIMP_TAC[];
        MP_TAC(ISPECL [`\x:real. x`; `&1`; `(psi1:real->real) t`; `x:real`;
                       `real_interval[t,s]`] HAS_REAL_DERIVATIVE_RMUL_WITHIN) THEN
        REWRITE_TAC[HAS_REAL_DERIVATIVE_ID; REAL_MUL_LID]];
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `B2 * abs(x - t)` THEN
      ASM_SIMP_TAC[] THEN
      SUBGOAL_THEN `&0 <= B2` ASSUME_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o SPEC `t:real` o
          check (fun th -> can (find_term ((=) `psi2:real->real`)) (concl th))) THEN
        ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[IN_REAL_INTERVAL]) THEN ASM_REAL_ARITH_TAC];
    DISCH_THEN(MP_TAC o SPECL [`s:real`; `t:real`]) THEN
    REWRITE_TAC[IN_REAL_INTERVAL; REAL_LE_REFL] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `x = x' /\ y = y' ==> x <= y ==> x' <= y'`) THEN
    CONJ_TAC THENL [AP_TERM_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_ARITH `t <= s ==> abs(s - t) = s - t`] THEN
    REWRITE_TAC[REAL_POW_2; REAL_MUL_ASSOC]]);;

let P4_RATIO_ARITH = prove
 (`!M1 M2 m n2 P d.
        &0 <= M1 /\ &0 <= M2 /\ &0 < m /\ &0 <= n2 /\ m * n2 <= P /\ &0 <= d
        ==> M1 * n2 * d <= (M1 + M2) / m * d * P /\
            M2 * n2 * d <= (M1 + M2) / m * d * P`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(M1 + M2) * n2 * d <= (M1 + M2) / m * d * P` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(M1 + M2) / m * d * (m * n2)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_EQ_IMP_LE THEN UNDISCH_TAC `&0 < m` THEN CONV_TAC REAL_FIELD;
      MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  CONJ_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(M1 + M2) * n2 * d` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC);;

(* Bounds on one compact chart piece. *)

let P4_RF_PIECE = prove
 (`!top atlas (g:real->A->real^3^3) a b t1 (U:A->bool) (phi:A->real^3) K.
        ricci_flow_from (top,atlas) a b g /\ a <= t1 /\ t1 < b /\
        (U,phi) IN atlas /\ compact K /\ K SUBSET IMAGE phi U
        ==> ?C. &0 <= C /\
                !x s t v.
                   x IN U /\ phi x IN K /\
                   s IN real_interval[a,t1] /\ t IN real_interval[a,t1]
                   ==> abs(v dot ((g s x - g t x) ** v))
                       <= C * abs(s - t) * (v dot (g t x ** v)) /\
                       (a < t
                        ==> abs(v dot (mfd_ricci_matrix atlas (g t) x ** v))
                            <= C * (v dot (g t x ** v))) /\
                       (a < t /\ t <= s
                        ==> abs(v dot ((g s x - g t x -
                                        (s - t) %% (--(&2) %%
                                         mfd_ricci_matrix atlas (g t) x)) ** v))
                            <= C * (s - t) pow 2 * (v dot (g t x ** v)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `(U:A->bool,phi:A->real^3)` (CONJUNCT2(CONJUNCT2(GEN_REWRITE_RULE I
    [ricci_flow_from] (ASSUME `ricci_flow_from (top,atlas) a b (g:real->A->real^3^3)`))))) THEN
  ASM_REWRITE_TAC[FST; SND] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` (X_CHOOSE_THEN
    `Fm:real^(1,3)finite_sum->real^(3,3)finite_prod` STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [ricci_flow_from]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [ricci_flow_on]) THEN
  SUBGOAL_THEN `open_in top (U:A->bool) /\ open(IMAGE (phi:A->real^3) U)`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[SMOOTH_MANIFOLD_ATLAS_CHART]; ALL_TAC] THEN
  ABBREV_TAC `O = interval(lift(a - e),lift b) PCROSS IMAGE (phi:A->real^3) U` THEN
  ABBREV_TAC `S = interval[lift a,lift t1] PCROSS (K:real^3->bool)` THEN
  ABBREV_TAC `D1 = \z. frechet_derivative
                      (Fm:real^(1,3)finite_sum->real^(3,3)finite_prod) (at z)
                      (pastecart (vec 1) (vec 0))` THEN
  ABBREV_TAC `D11 = \z. frechet_derivative
                       (D1:real^(1,3)finite_sum->real^(3,3)finite_prod) (at z)
                       (pastecart (vec 1) (vec 0))` THEN
  SUBGOAL_THEN `open(O:real^(1,3)finite_sum->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "O" THEN MATCH_MP_TAC OPEN_PCROSS THEN ASM_REWRITE_TAC[OPEN_INTERVAL];
    ALL_TAC] THEN
  SUBGOAL_THEN `(S:real^(1,3)finite_sum->bool) SUBSET O /\ compact S` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MAP_EVERY EXPAND_TAC ["O"; "S"] THEN
      REWRITE_TAC[SUBSET; FORALL_IN_PCROSS; PASTECART_IN_PCROSS; IN_INTERVAL_1;
                  LIFT_DROP] THEN
      REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; ASM SET_TAC[]];
      EXPAND_TAC "S" THEN MATCH_MP_TAC COMPACT_PCROSS THEN
      REWRITE_TAC[COMPACT_INTERVAL] THEN FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on O (D1:real^(1,3)finite_sum->real^(3,3)finite_prod) /\
    smooth_map_on O (D11:real^(1,3)finite_sum->real^(3,3)finite_prod)`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
     [EXPAND_TAC "D1" THEN ASM_SIMP_TAC[SMOOTH_MAP_ON_FRECHET_DERIVATIVE];
      DISCH_TAC THEN EXPAND_TAC "D11" THEN
      ASM_SIMP_TAC[SMOOTH_MAP_ON_FRECHET_DERIVATIVE]];
    ALL_TAC] THEN
  (* bounds *)
  MP_TAC(ISPECL [`\z. (matrify:real^(3,3)finite_prod->real^3^3)
                        ((D1:real^(1,3)finite_sum->real^(3,3)finite_prod) z)`;
                 `S:real^(1,3)finite_sum->bool`] P4_FAMILY_UPPER) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[VECTORIZE_MATRIFY; ETA_AX] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `O:real^(1,3)finite_sum->bool` THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON];
    DISCH_THEN(X_CHOOSE_THEN `M1:real` STRIP_ASSUME_TAC)] THEN
  MP_TAC(ISPECL [`\z. (matrify:real^(3,3)finite_prod->real^3^3)
                        ((D11:real^(1,3)finite_sum->real^(3,3)finite_prod) z)`;
                 `S:real^(1,3)finite_sum->bool`] P4_FAMILY_UPPER) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[VECTORIZE_MATRIFY; ETA_AX] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `O:real^(1,3)finite_sum->bool` THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON];
    DISCH_THEN(X_CHOOSE_THEN `M2:real` STRIP_ASSUME_TAC)] THEN
  MP_TAC(ISPECL [`\z. (matrify:real^(3,3)finite_prod->real^3^3)
                        ((Fm:real^(1,3)finite_sum->real^(3,3)finite_prod) z)`;
                 `S:real^(1,3)finite_sum->bool`] P4_FAMILY_LOWER) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[VECTORIZE_MATRIFY; ETA_AX] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `O:real^(1,3)finite_sum->bool` THEN
      ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON];
      ALL_TAC] THEN
    EXPAND_TAC "S" THEN REWRITE_TAC[FORALL_IN_PCROSS; IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
    REWRITE_TAC[FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP] THEN
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
    X_GEN_TAC `u:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(w:real^3) IN IMAGE (phi:A->real^3) U` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `(Fm:real^(1,3)finite_sum->real^(3,3)finite_prod) (pastecart (lift s) w) =
      vectorize(metric_local atlas (U,phi) ((g:real->A->real^3^3) s) w)`
    SUBST1_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[MATRIFY_VECTORIZE]] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `g:real->A->real^3^3`; `a:real`; `b:real`; `s:real`]
                  P4_RF_RIEMANNIAN) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[riemannian_metric; metric_field] THEN
    DISCH_THEN(MP_TAC o SPEC `(U:A->bool,phi:A->real^3)`) THEN
    ASM_REWRITE_TAC[FST; SND] THEN ASM_MESON_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `m:real` STRIP_ASSUME_TAC)] THEN
  EXISTS_TAC `(M1 + M2) / m` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  RULE_ASSUM_TAC BETA_RULE THEN
  MAP_EVERY X_GEN_TAC [`x:A`; `s:real`; `t:real`; `v:real^3`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(phi:A->real^3) x IN IMAGE phi U /\ (x:A) IN topspace top`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
                    ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]];
    ALL_TAC] THEN
  ABBREV_TAC `J = matrix(chart_jac (chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A))
                                   (U,phi) x)` THEN
  ABBREV_TAC `u:real^3 = (J:real^3^3) ** (v:real^3)` THEN
  (* E1: the quadratic form of g xi x through the chart representative *)
  SUBGOAL_THEN
   `!xi. a <= xi /\ xi < b
         ==> v dot ((g:real->A->real^3^3) xi x ** v) =
             u dot (matrify((Fm:real^(1,3)finite_sum->real^(3,3)finite_prod)
                              (pastecart (lift xi) (phi x))) ** u)`
  (LABEL_TAC "E1") THENL
   [X_GEN_TAC `xi:real` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `(g:real->A->real^3^3) xi`; `U:A->bool`; `phi:A->real^3`; `x:A`]
                  P4_METRIC_LOCAL_CHANGE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    SUBGOAL_THEN
     `(Fm:real^(1,3)finite_sum->real^(3,3)finite_prod) (pastecart (lift xi) (phi x)) =
      vectorize(metric_local atlas (U,phi) ((g:real->A->real^3^3) xi) ((phi:A->real^3) x))`
    SUBST1_TAC THENL
     [FIRST_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (find_term ((=) `Fm:real^(1,3)finite_sum->real^(3,3)finite_prod`)) (concl th) &&
        is_forall(concl th))) THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[MATRIFY_VECTORIZE]] THEN
    EXPAND_TAC "u" THEN
    REWRITE_TAC[GSYM MATRIX_VECTOR_MUL_ASSOC; DOT_MATRIX_TRANSP_RMUL];
    ALL_TAC] THEN
  ABBREV_TAC
   `psi = \xi. (u:real^3) dot (matrify((Fm:real^(1,3)finite_sum->real^(3,3)finite_prod)
                                        (pastecart (lift xi) ((phi:A->real^3) x))) ** u)` THEN
  ABBREV_TAC
   `psi1 = \xi. (u:real^3) dot (matrify((D1:real^(1,3)finite_sum->real^(3,3)finite_prod)
                                         (pastecart (lift xi) ((phi:A->real^3) x))) ** u)` THEN
  ABBREV_TAC
   `psi2 = \xi. (u:real^3) dot (matrify((D11:real^(1,3)finite_sum->real^(3,3)finite_prod)
                                         (pastecart (lift xi) ((phi:A->real^3) x))) ** u)` THEN
  SUBGOAL_THEN
   `!xi. xi IN real_interval[a,t1]
         ==> pastecart (lift xi) ((phi:A->real^3) x) IN S`
  ASSUME_TAC THENL
   [X_GEN_TAC `xi:real` THEN DISCH_TAC THEN EXPAND_TAC "S" THEN
    REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IN_REAL_INTERVAL]) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* derivatives of psi and psi1 on [a,t1] *)
  SUBGOAL_THEN
   `!xi. xi IN real_interval[a,t1]
         ==> ((psi:real->real) has_real_derivative psi1 xi) (atreal xi) /\
             ((psi1:real->real) has_real_derivative psi2 xi) (atreal xi)`
  (LABEL_TAC "DER") THENL
   [X_GEN_TAC `xi:real` THEN DISCH_TAC THEN
    SUBGOAL_THEN `pastecart (lift xi) ((phi:A->real^3) x) IN O` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`Fm:real^(1,3)finite_sum->real^(3,3)finite_prod`;
                     `\X:real^(3,3)finite_prod. lift((u:real^3) dot (matrify X ** u))`;
                     `xi:real`; `(phi:A->real^3) x`] P4_TIME_SLICE_DERIV) THEN
      REWRITE_TAC[P4_LINEAR_QF; LIFT_DROP] THEN ANTS_TAC THENL
       [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
        EXISTS_TAC `O:real^(1,3)finite_sum->bool` THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      MAP_EVERY EXPAND_TAC ["psi"; "psi1"; "D1"] THEN REWRITE_TAC[ETA_AX];
      MP_TAC(ISPECL [`D1:real^(1,3)finite_sum->real^(3,3)finite_prod`;
                     `\X:real^(3,3)finite_prod. lift((u:real^3) dot (matrify X ** u))`;
                     `xi:real`; `(phi:A->real^3) x`] P4_TIME_SLICE_DERIV) THEN
      REWRITE_TAC[P4_LINEAR_QF; LIFT_DROP] THEN ANTS_TAC THENL
       [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
        EXISTS_TAC `O:real^(1,3)finite_sum->bool` THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      MAP_EVERY EXPAND_TAC ["psi1"; "psi2"; "D11"] THEN REWRITE_TAC[ETA_AX]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!xi. xi IN real_interval[a,t1]
         ==> abs((psi1:real->real) xi) <= M1 * norm(u:real^3) pow 2 /\
             abs((psi2:real->real) xi) <= M2 * norm u pow 2`
  (LABEL_TAC "BD") THENL
   [X_GEN_TAC `xi:real` THEN DISCH_TAC THEN MAP_EVERY EXPAND_TAC ["psi1"; "psi2"] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`psi:real->real`; `psi1:real->real`; `psi2:real->real`;
                 `a:real`; `t1:real`; `M1 * norm(u:real^3) pow 2`;
                 `M2 * norm(u:real^3) pow 2`] P4_REAL_TAYLOR2) THEN
  ANTS_TAC THENL
   [X_GEN_TAC `xi:real` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[HAS_REAL_DERIVATIVE_ATREAL_WITHIN];
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "TA") (LABEL_TAC "TB"))] THEN
  SUBGOAL_THEN
   `v dot ((g:real->A->real^3^3) s x ** v) = psi s /\
    v dot (g t x ** v) = psi t /\
    m * norm(u:real^3) pow 2 <= psi t`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN EXPAND_TAC "psi" THENL
     [USE_THEN "E1" MATCH_MP_TAC THEN
      RULE_ASSUM_TAC(REWRITE_RULE[IN_REAL_INTERVAL]) THEN ASM_REAL_ARITH_TAC;
      USE_THEN "E1" MATCH_MP_TAC THEN
      RULE_ASSUM_TAC(REWRITE_RULE[IN_REAL_INTERVAL]) THEN ASM_REAL_ARITH_TAC;
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (find_term ((=) `m:real`)) (concl th) && is_forall(concl th))) THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `a < t
    ==> (psi1:real->real) t =
        --(&2) * (v dot (mfd_ricci_matrix atlas ((g:real->A->real^3^3) t) x ** v))`
  (LABEL_TAC "RIC") THENL
   [DISCH_TAC THEN MATCH_MP_TAC REAL_DERIVATIVE_UNIQUE_ATREAL THEN
    MAP_EVERY EXISTS_TAC [`psi:real->real`; `t:real`] THEN CONJ_TAC THENL
     [USE_THEN "DER" (fun th -> MP_TAC(MATCH_MP th
        (ASSUME `t IN real_interval[a,t1]`))) THEN SIMP_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_TRANSFORM_ATREAL THEN
    EXISTS_TAC `\xi. v dot ((g:real->A->real^3^3) xi x ** v)` THEN
    EXISTS_TAC `min (t - a) (b - t)` THEN
    SUBGOAL_THEN `a <= t /\ t <= t1` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[IN_REAL_INTERVAL]; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      X_GEN_TAC `xi:real` THEN DISCH_TAC THEN EXPAND_TAC "psi" THEN BETA_TAC THEN
      USE_THEN "E1" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                     `g:real->A->real^3^3`; `a:real`; `b:real`; `t:real`; `x:A`;
                     `v:real^3`] P4_RF_PREFERRED_DERIV) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[MATRIX_VECTOR_LMUL; DOT_RMUL]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= norm(u:real^3) pow 2` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_LE_POW_2]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[MATRIX_VECTOR_MUL_SUB_RDISTRIB; DOT_RSUB] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `M1 * norm(u:real^3) pow 2 * abs(s - t)` THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_MUL_ASSOC] THEN USE_THEN "TA" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      MP_TAC(SPECL [`M1:real`; `M2:real`; `m:real`; `norm(u:real^3) pow 2`;
                    `(psi:real->real) t`; `abs(s - t)`] P4_RATIO_ARITH) THEN
      ASM_SIMP_TAC[REAL_ABS_POS]];
    DISCH_TAC THEN USE_THEN "RIC" (fun th -> MP_TAC(MATCH_MP th
      (ASSUME `a < t`))) THEN
    USE_THEN "BD" (fun th -> MP_TAC(CONJUNCT1(MATCH_MP th
      (ASSUME `t IN real_interval[a,t1]`)))) THEN
    MP_TAC(SPECL [`M1:real`; `M2:real`; `m:real`; `norm(u:real^3) pow 2`;
                  `(psi:real->real) t`; `&1`] P4_RATIO_ARITH) THEN
    ASM_REWRITE_TAC[REAL_POS; REAL_MUL_RID] THEN ASM_REAL_ARITH_TAC;
    STRIP_TAC THEN
    REWRITE_TAC[MATRIX_VECTOR_MUL_SUB_RDISTRIB; DOT_RSUB; MATRIX_VECTOR_LMUL;
                DOT_RMUL] THEN
    ASM_REWRITE_TAC[] THEN
    USE_THEN "RIC" (fun th -> REWRITE_TAC[GSYM(MATCH_MP th (ASSUME `a < t`))]) THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `M2 * norm(u:real^3) pow 2 * (s - t) pow 2` THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_MUL_ASSOC] THEN USE_THEN "TB" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      MP_TAC(SPECL [`M1:real`; `M2:real`; `m:real`; `norm(u:real^3) pow 2`;
                    `(psi:real->real) t`; `(s - t) pow 2`] P4_RATIO_ARITH) THEN
      ASM_SIMP_TAC[REAL_LE_POW_2]]]);;

(* The bounds globally on a compact manifold. *)

let P4_RF_UNIFORM = prove
 (`!top atlas (g:real->A->real^3^3) a b t1.
        compact_space top /\ ricci_flow_from (top,atlas) a b g /\
        a <= t1 /\ t1 < b
        ==> ?C. &0 <= C /\
                !x s t v.
                   x IN topspace top /\
                   s IN real_interval[a,t1] /\ t IN real_interval[a,t1]
                   ==> abs(v dot ((g s x - g t x) ** v))
                       <= C * abs(s - t) * (v dot (g t x ** v)) /\
                       (a < t
                        ==> abs(v dot (mfd_ricci_matrix atlas (g t) x ** v))
                            <= C * (v dot (g t x ** v))) /\
                       (a < t /\ t <= s
                        ==> abs(v dot ((g s x - g t x -
                                        (s - t) %% (--(&2) %%
                                         mfd_ricci_matrix atlas (g t) x)) ** v))
                            <= C * (s - t) pow 2 * (v dot (g t x ** v)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool)`
  ASSUME_TAC THENL [ASM_MESON_TAC[ricci_flow_from; ricci_flow_on]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`]
                P4_CHART_PIECES) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:A->bool` (X_CHOOSE_THEN `r:A->real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (LABEL_TAC "rad") (LABEL_TAC "cov")))))) THEN
  SUBGOAL_THEN
   `!x0. ?C. x0 IN k
             ==> &0 <= C /\
                 !x s t v.
                   x IN FST(chart_at atlas x0) /\
                   SND(chart_at atlas x0) x IN
                   cball(SND(chart_at atlas x0) x0,r x0) /\
                   s IN real_interval[a,t1] /\ t IN real_interval[a,t1]
                   ==> abs(v dot (((g:real->A->real^3^3) s x - g t x) ** v))
                       <= C * abs(s - t) * (v dot (g t x ** v)) /\
                       (a < t
                        ==> abs(v dot (mfd_ricci_matrix atlas (g t) x ** v))
                            <= C * (v dot (g t x ** v))) /\
                       (a < t /\ t <= s
                        ==> abs(v dot ((g s x - g t x -
                                        (s - t) %% (--(&2) %%
                                         mfd_ricci_matrix atlas (g t) x)) ** v))
                            <= C * (s - t) pow 2 * (v dot (g t x ** v)))`
  MP_TAC THENL
   [X_GEN_TAC `x0:A` THEN REWRITE_TAC[RIGHT_EXISTS_IMP_THM] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `g:real->A->real^3^3`; `a:real`; `b:real`; `t1:real`;
                   `FST(chart_at (atlas:((A->bool)#(A->real^3))->bool) x0)`;
                   `SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) x0)`;
                   `cball(SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) x0) x0,
                          r x0)`] P4_RF_PIECE) THEN
    REWRITE_TAC[PAIR; COMPACT_CBALL] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `x0:A`]
                   CHART_AT) THEN
      ANTS_TAC THENL [ASM SET_TAC[]; SIMP_TAC[]];
      USE_THEN "rad" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(x0:A) IN k`))) THEN
      SIMP_TAC[]];
    REWRITE_TAC[SKOLEM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `Cf:A->real` (LABEL_TAC "piece"))] THEN
  EXISTS_TAC `sum k (Cf:A->real)` THEN
  SUBGOAL_THEN `!x0. x0 IN k ==> &0 <= (Cf:A->real) x0` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!x0. x0 IN k ==> (Cf:A->real) x0 <= sum k Cf` ASSUME_TAC THENL
   [MATCH_MP_TAC SUM_POS_BOUND THEN ASM_REWRITE_TAC[REAL_LE_REFL]; ALL_TAC] THEN
  CONJ_TAC THENL [MATCH_MP_TAC SUM_POS_LE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`x:A`; `s:real`; `t:real`; `v:real^3`] THEN STRIP_TAC THEN
  USE_THEN "cov" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(x:A) IN topspace top`))) THEN
  DISCH_THEN(X_CHOOSE_THEN `x0:A` STRIP_ASSUME_TAC) THEN
  USE_THEN "piece" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(x0:A) IN k`))) THEN
  DISCH_THEN(MP_TAC o SPECL [`x:A`; `s:real`; `t:real`; `v:real^3`] o CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 <= v dot ((g:real->A->real^3^3) t x ** v)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `(g:real->A->real^3^3) t`; `x:A`] P4_RIEMANNIAN_PSD) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P4_RF_RIEMANNIAN THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `a:real`; `b:real`] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[IN_REAL_INTERVAL]) THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC;
      SIMP_TAC[positive_semidefinite]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(Cf:A->real) x0 <= sum k Cf` ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!z. &0 <= z ==> (Cf:A->real) x0 * z <= sum k Cf * z`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THENL
   [EXISTS_TAC `(Cf:A->real) x0 * abs(s - t) * (v dot ((g:real->A->real^3^3) t x ** v))` THEN
    ASM_SIMP_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_ABS_POS];
    EXISTS_TAC `(Cf:A->real) x0 * (v dot ((g:real->A->real^3^3) t x ** v))` THEN
    ASM_SIMP_TAC[];
    EXISTS_TAC `(Cf:A->real) x0 * (s - t) pow 2 *
                (v dot ((g:real->A->real^3^3) t x ** v))` THEN
    ASM_SIMP_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2]]);;


(* ========================================================================= *)
(* The Ricci form in a chart along the flow, continuity of the               *)
(* width (P4_WIDTH_CONTINUITY_STATEMENT) and the Taylor bound for slice     *)
(* areas (P4_AREA_TAYLOR_STATEMENT).                                         *)
(* ========================================================================= *)

let P4_CONGRUENCE_ENTRY = prove
 (`!(J:real^N^N) (M:real^N^N) i j.
        1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
        ==> (transp J ** M ** J)$i$j =
            sum(1..dimindex(:N))
             (\p. sum(1..dimindex(:N)) (\q. J$p$i * M$p$q * J$q$j))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[matrix_mul; LAMBDA_BETA] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `p:num` THEN STRIP_TAC THEN
  ASM_SIMP_TAC[transp; LAMBDA_BETA; GSYM SUM_LMUL] THEN REWRITE_TAC[REAL_MUL_ASSOC]);;

(* The chart representative of the Ricci form along the flow is -1/2 the    *)
(* time derivative of the chart representative of the metric.               *)

let P4_RF_RICCI_LOCAL = prove
 (`!top atlas (g:real->A->real^N^N) a b t (c:(A->bool)#(A->real^N)) w.
        ricci_flow_on (top,atlas) a b g /\ a < t /\ t < b /\
        c IN atlas /\ w IN IMAGE (SND c) (FST c)
        ==> metric_local atlas c (mfd_ricci_matrix atlas (g t)) w =
            --(inv(&2)) %%
            matrify(frechet_derivative
                     (\z. vectorize(metric_local atlas c (g(drop(fstcart z)))
                                                 (sndcart z)))
                     (at (pastecart (lift t) w)) (pastecart (vec 1) (vec 0)))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [ricci_flow_on]) THEN
  ABBREV_TAC `Fc = \z. (vectorize:real^N^N->real^(N,N)finite_prod)
                       (metric_local atlas c ((g:real->A->real^N^N) (drop(fstcart z)))
                                     (sndcart z))` THEN
  SUBGOAL_THEN
   `smooth_map_on (interval(lift a,lift b) PCROSS
                   IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c))
                  (Fc:real^(1,N)finite_sum->real^(N,N)finite_prod)`
  ASSUME_TAC THENL [EXPAND_TAC "Fc" THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(Fc:real^(1,N)finite_sum->real^(N,N)finite_prod) differentiable
    (at (pastecart (lift t) w))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `interval(lift a,lift b) PCROSS IMAGE (SND c) (FST (c:(A->bool)#(A->real^N)))` THEN
    ASM_REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP] THEN
    MATCH_MP_TAC OPEN_PCROSS THEN REWRITE_TAC[OPEN_INTERVAL] THEN
    ASM_MESON_TAC[GRGD_ATLAS_CHART];
    ALL_TAC] THEN
  ABBREV_TAC `x = chart_inv (c:(A->bool)#(A->real^N)) w` THEN
  SUBGOAL_THEN `(x:A) IN FST(c:(A->bool)#(A->real^N)) /\ SND c x = w /\ x IN topspace top`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN EXPAND_TAC "x" THEN
    ASM_SIMP_TAC[] THEN ASM_MESON_TAC[GRGD_ATLAS_CHART; SUBSET];
    ALL_TAC] THEN
  ABBREV_TAC `M = matrix(chart_jac (c:(A->bool)#(A->real^N))
                                   (chart_at atlas (x:A)) x)` THEN
  SUBGOAL_THEN
   `!Q:A->real^N^N. metric_local atlas c Q w = transp M ** Q x ** M`
  ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[metric_local] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SIMP_TAC[CART_EQ; MATRIX_CMUL_COMPONENT] THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `((\s. ((transp M ** (g:real->A->real^N^N) s x ** M):real^N^N)$i$j)
     has_real_derivative
     (matrify((frechet_derivative (Fc:real^(1,N)finite_sum->real^(N,N)finite_prod)
               (at (pastecart (lift t) w)) (pastecart (vec 1) (vec 0)))):real^N^N)$i$j)
    (atreal t)`
  MP_TAC THENL
   [MATCH_MP_TAC HAS_REAL_DERIVATIVE_TRANSFORM_ATREAL THEN
    EXISTS_TAC `\s. drop((\X. lift((matrify X:real^N^N)$i$j))
                         ((Fc:real^(1,N)finite_sum->real^(N,N)finite_prod)
                          (pastecart (lift s) w)))` THEN
    EXISTS_TAC `min (t - a) (b - t)` THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      X_GEN_TAC `s:real` THEN DISCH_TAC THEN EXPAND_TAC "Fc" THEN
      REWRITE_TAC[LIFT_DROP; FSTCART_PASTECART; SNDCART_PASTECART; MATRIFY_VECTORIZE] THEN
      ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`Fc:real^(1,N)finite_sum->real^(N,N)finite_prod`;
                     `\X. lift((matrify X:real^N^N)$i$j)`; `t:real`; `w:real^N`]
                    P4_TIME_SLICE_DERIV) THEN
      REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[LRG_LINEAR_MATRIFY_ENTRY]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\s. ((transp M ** (g:real->A->real^N^N) s x ** M):real^N^N)$i$j)
     has_real_derivative
     ((transp M ** (--(&2) %% mfd_ricci_matrix atlas (g t) x) ** M):real^N^N)$i$j)
    (atreal t)`
  MP_TAC THENL
   [ASM_SIMP_TAC[P4_CONGRUENCE_ENTRY] THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUM THEN
    REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN X_GEN_TAC `p:num` THEN STRIP_TAC THEN
    BETA_TAC THEN MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUM THEN
    REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN X_GEN_TAC `q:num` THEN STRIP_TAC THEN
    BETA_TAC THEN ASM_SIMP_TAC[MATRIX_CMUL_COMPONENT] THEN
    SUBGOAL_THEN
     `(\s. (M:real^N^N)$p$i * (g:real->A->real^N^N) s x$p$q * M$q$j) =
      (\s. (M$p$i * M$q$j) * g s x$p$q)`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN
     `(M:real^N^N)$p$i *
      (--(&2) * mfd_ricci_matrix atlas ((g:real->A->real^N^N) t) x$p$q) * M$q$j =
      (M$p$i * M$q$j) * (--(&2) * mfd_ricci_matrix atlas (g t) x$p$q)`
    SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_LMUL_ATREAL THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (find_term ((=) `has_real_derivative`)) (concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[IMP_IMP] THEN DISCH_THEN(MP_TAC o MATCH_MP REAL_DERIVATIVE_UNIQUE_ATREAL) THEN
  ASM_SIMP_TAC[MATRIX_MUL_LMUL; MATRIX_MUL_RMUL; MATRIX_CMUL_COMPONENT] THEN
  CONV_TAC REAL_FIELD);;

let P4_RICCI_MATRIX_SYM = prove
 (`!top atlas (g:A->real^N^N) x.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        x IN topspace top
        ==> transp(mfd_ricci_matrix atlas g x) = mfd_ricci_matrix atlas g x`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`]
               CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SIMP_TAC[CART_EQ; TRANSP_COMPONENT; mfd_ricci_matrix; LAMBDA_BETA] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[LAMBDA_BETA; mfd_ricci] THEN
  MATCH_MP_TAC LRICCI_SYM THEN
  EXISTS_TAC `IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) x))
                    (FST(chart_at atlas x))` THEN
  ASM_SIMP_TAC[FUN_IN_IMAGE] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[riemannian_metric]) THEN ASM_SIMP_TAC[]);;

let P4_RF_RICCI_CONT = prove
 (`!top atlas (g:real->A->real^N^N) a b t (c:(A->bool)#(A->real^N)).
        ricci_flow_on (top,atlas) a b g /\ a < t /\ t < b /\ c IN atlas
        ==> (\w. vectorize(metric_local atlas c (mfd_ricci_matrix atlas (g t)) w))
            continuous_on IMAGE (SND c) (FST c)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_EQ THEN
  EXISTS_TAC
   `\w. --(inv(&2)) %
        frechet_derivative
         (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
              (metric_local atlas c ((g:real->A->real^N^N) (drop(fstcart z)))
                            (sndcart z)))
         (at (pastecart (lift t) w)) (pastecart (vec 1) (vec 0))` THEN
  CONJ_TAC THENL
   [X_GEN_TAC `w:real^N` THEN DISCH_TAC THEN BETA_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:real->A->real^N^N`; `a:real`; `b:real`; `t:real`;
                   `c:(A->bool)#(A->real^N)`; `w:real^N`] P4_RF_RICCI_LOCAL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[VECTORIZE_CMUL; VECTORIZE_MATRIFY];
    ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [ricci_flow_on]) THEN
  SUBGOAL_THEN
   `open(interval(lift a,lift b) PCROSS
         IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC OPEN_PCROSS THEN REWRITE_TAC[OPEN_INTERVAL] THEN
    ASM_MESON_TAC[GRGD_ATLAS_CHART];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\w. frechet_derivative
          (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
               (metric_local atlas c ((g:real->A->real^N^N) (drop(fstcart z)))
                             (sndcart z)))
          (at (pastecart (lift t) w)) (pastecart (vec 1) (vec 0))) =
    (\z. frechet_derivative
          (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
               (metric_local atlas c ((g:real->A->real^N^N) (drop(fstcart z)))
                             (sndcart z)))
          (at z) (pastecart (vec 1) (vec 0))) o (\w:real^N. pastecart (lift t) w)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN
    REWRITE_TAC[CONTINUOUS_ON_ID; CONTINUOUS_ON_CONST];
    ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
  EXISTS_TAC `interval(lift a,lift b) PCROSS
              IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_FRECHET_DERIVATIVE THEN ASM_SIMP_TAC[];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; PASTECART_IN_PCROSS; IN_INTERVAL_1;
                LIFT_DROP] THEN
    ASM_SIMP_TAC[FUN_IN_IMAGE]]);;

(* Comparison of slice areas, sweep areas and widths for two metrics. *)

let P4_SWEEP_AREA_POS = prove
 (`!top atlas (g:A->real^N^N) (sigma:real^3->real->A).
        smooth_manifold_atlas top atlas /\ p4_sweepout (top,atlas) sigma /\
        riemannian_metric atlas g
        ==> &0 <= p4_sweep_area atlas g sigma`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p4_sweep_area] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `p4_s2_area atlas (g:A->real^N^N) (\y. (sigma:real^3->real->A) y (&0))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`]
                        P4_SLICE_AREA_POS) THEN
    ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN REAL_ARITH_TAC;
    MATCH_MP_TAC ELEMENT_LE_SUP THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `g:A->real^N^N`; `sigma:real^3->real->A`] P4_SWEEP_AREA_BOUND) THEN
      ASM_REWRITE_TAC[FORALL_IN_GSPEC];
      REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `&0` THEN
      REWRITE_TAC[IN_REAL_INTERVAL] THEN REAL_ARITH_TAC]]);;

let P4_SLICE_AREA_COMPARE = prove
 (`!top atlas (g1:A->real^N^N) g2 (sigma:real^3->real->A) k t.
        smooth_manifold_atlas top atlas /\ p4_sweepout (top,atlas) sigma /\
        riemannian_metric atlas g1 /\ riemannian_metric atlas g2 /\ &0 <= k /\
        (!x v. x IN topspace top ==> v dot (g1 x ** v) <= k * (v dot (g2 x ** v))) /\
        t IN real_interval[&0,&1]
        ==> p4_s2_area atlas g1 (\y. sigma y t) <=
            k * p4_s2_area atlas g2 (\y. sigma y t)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p4_s2_area] THEN
  SUBGOAL_THEN
   `(\y. lift(p4_s2_density atlas (g1:A->real^N^N) (\y. (sigma:real^3->real->A) y t) y))
    continuous_on sphere(vec 0,&1) /\
    (\y. lift(p4_s2_density atlas (g2:A->real^N^N) (\y. sigma y t) y))
    continuous_on sphere(vec 0,&1)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN
    MATCH_MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`]
                        P4_SLICE_DENSITY_CONT) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `p4_s2_integral
               (\y. k * p4_s2_density atlas (g2:A->real^N^N)
                          (\y. (sigma:real^3->real->A) y t) y)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC P4_S2_INTEGRAL_MONO THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[LIFT_CMUL] THEN MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(sigma:real^3->real->A) y t IN topspace top` ASSUME_TAC THENL
     [MATCH_MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`]
                          P4_SLICE_IN_TOPSPACE) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[p4_s2_density] THEN MATCH_MP_TAC P4_DENSITY_LOEWNER THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC P4_GRAM_PSD THEN BETA_TAC THEN
      MATCH_MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`]
                          P4_RIEMANNIAN_PSD) THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC P4_GRAM_PSD THEN BETA_TAC THEN
      MATCH_MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`]
                          P4_RIEMANNIAN_PSD) THEN ASM_REWRITE_TAC[];
      GEN_TAC THEN REWRITE_TAC[P4_GRAM_QF] THEN BETA_TAC THEN ASM_SIMP_TAC[]];
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC P4_S2_INTEGRAL_CMUL THEN
    ASM_REWRITE_TAC[]]);;

let P4_SWEEP_AREA_COMPARE = prove
 (`!top atlas (g1:A->real^N^N) g2 (sigma:real^3->real->A) k.
        smooth_manifold_atlas top atlas /\ p4_sweepout (top,atlas) sigma /\
        riemannian_metric atlas g1 /\ riemannian_metric atlas g2 /\ &0 <= k /\
        (!x v. x IN topspace top ==> v dot (g1 x ** v) <= k * (v dot (g2 x ** v)))
        ==> p4_sweep_area atlas g1 sigma <= k * p4_sweep_area atlas g2 sigma`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p4_sweep_area] THEN
  MATCH_MP_TAC P4_SUP_SCALE_LE THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`]
                        P4_SWEEP_AREA_BOUND) THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`]
                        P4_SLICE_AREA_COMPARE) THEN
    ASM_REWRITE_TAC[]]);;

let P4_WIDTH_POS = prove
 (`!top atlas (g:A->real^N^N) U.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        p4_cm_adm (top,atlas) U
        ==> &0 <= p4_cm_width (top,atlas) g U`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p4_cm_width] THEN
  MATCH_MP_TAC REAL_LE_INF THEN
  GEN_REWRITE_TAC ONCE_DEPTH_CONV [SIMPLE_IMAGE_GEN] THEN
  REWRITE_TAC[IMAGE_EQ_EMPTY; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN ASM_MESON_TAC[p4_cm_adm];
    REWRITE_TAC[p4_sweepout_in] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`]
                        P4_SWEEP_AREA_POS) THEN ASM_REWRITE_TAC[]]);;

let P4_WIDTH_COMPARE = prove
 (`!top atlas (g1:A->real^N^N) g2 U k.
        smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g1 /\ riemannian_metric atlas g2 /\ &0 < k /\
        (!x v. x IN topspace top ==> v dot (g1 x ** v) <= k * (v dot (g2 x ** v))) /\
        p4_cm_adm (top,atlas) U
        ==> p4_cm_width (top,atlas) g1 U <= k * p4_cm_width (top,atlas) g2 U`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `p4_cm_width (top,atlas) (g1:A->real^N^N) U / k <=
                p4_cm_width (top,atlas) (g2:A->real^N^N) U` MP_TAC THENL
   [ALL_TAC; ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN REAL_ARITH_TAC] THEN
  GEN_REWRITE_TAC RAND_CONV [p4_cm_width] THEN MATCH_MP_TAC REAL_LE_INF THEN
  GEN_REWRITE_TAC ONCE_DEPTH_CONV [SIMPLE_IMAGE_GEN] THEN
  REWRITE_TAC[IMAGE_EQ_EMPTY; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN ASM_MESON_TAC[p4_cm_adm];
    ALL_TAC] THEN
  X_GEN_TAC `sigma:real^3->real->A` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `p4_sweep_area atlas (g1:A->real^N^N) sigma` THEN CONJ_TAC THENL
   [REWRITE_TAC[p4_cm_width] THEN MATCH_MP_TAC INF_LE_ELEMENT THEN CONJ_TAC THENL
     [EXISTS_TAC `&0` THEN REWRITE_TAC[FORALL_IN_GSPEC; p4_sweepout_in] THEN
      REPEAT STRIP_TAC THEN
      MATCH_MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`]
                          P4_SWEEP_AREA_POS) THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `sigma:real^3->real->A` THEN
      ASM_REWRITE_TAC[]];
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    MATCH_MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`]
                        P4_SWEEP_AREA_COMPARE) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[p4_sweepout_in]) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE]]);;

(* Continuity of the width along the flow, on [a,t1] including t = a. *)

let P4_WIDTH_CONTINUITY = prove
 (`P4_WIDTH_CONTINUITY_STATEMENT (:A)`,
  REWRITE_TAC[P4_WIDTH_CONTINUITY_STATEMENT] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:real->A->real^3^3`; `a:real`; `b:real`; `t1:real`] P4_RF_UNIFORM) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `C:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "unif"))) THEN
  SUBGOAL_THEN `!t. t IN real_interval[a,t1]
                    ==> riemannian_metric atlas ((g:real->A->real^3^3) t)`
  (LABEL_TAC "rm") THENL
   [REWRITE_TAC[IN_REAL_INTERVAL] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC P4_RF_RIEMANNIAN THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `a:real`; `b:real`] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `W = \t. p4_cm_width (top,atlas) ((g:real->A->real^3^3) t) U` THEN
  SUBGOAL_THEN
   `!s t. s IN real_interval[a,t1] /\ t IN real_interval[a,t1]
          ==> &0 <= (W:real->real) t /\ W s <= W t + C * abs(s - t) * W t`
  (LABEL_TAC "cmp") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN EXPAND_TAC "W" THEN CONJ_TAC THENL
     [MATCH_MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`]
                          P4_WIDTH_POS) THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[REAL_ARITH `w + c * d * w = (&1 + c * d) * w`] THEN
    MATCH_MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`]
                        P4_WIDTH_COMPARE) THEN
    ASM_SIMP_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 < &1 + x`) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_ABS_POS];
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`x:A`; `v:real^3`] THEN DISCH_TAC THEN
    USE_THEN "unif" (fun th -> MP_TAC(CONJUNCT1(SPEC `v:real^3` (MATCH_MP th
      (CONJ (ASSUME `(x:A) IN topspace top`)
            (CONJ (ASSUME `s IN real_interval[a,t1]`)
                  (ASSUME `t IN real_interval[a,t1]`))))))) THEN
    REWRITE_TAC[MATRIX_VECTOR_MUL_SUB_RDISTRIB; DOT_RSUB] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `a IN real_interval[a,t1]` ASSUME_TAC THENL
   [REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `B = (W:real->real) a + C * (t1 - a) * W a` THEN
  SUBGOAL_THEN `!t. t IN real_interval[a,t1] ==> (W:real->real) t <= B`
  (LABEL_TAC "bd") THENL
   [REPEAT STRIP_TAC THEN
    USE_THEN "cmp" (fun th -> MP_TAC(MATCH_MP th
      (CONJ (ASSUME `t IN real_interval[a,t1]`) (ASSUME `a IN real_interval[a,t1]`)))) THEN
    STRIP_TAC THEN EXPAND_TAC "B" THEN
    MATCH_MP_TAC(REAL_ARITH `!x y p q:real. x <= y + p /\ p <= q ==> x <= y + q`) THEN
    EXISTS_TAC `C * abs(t - a) * (W:real->real) a` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IN_REAL_INTERVAL]) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= B` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(W:real->real) a` THEN
    USE_THEN "cmp" (fun th -> MP_TAC(MATCH_MP th
      (CONJ (ASSUME `a IN real_interval[a,t1]`) (ASSUME `a IN real_interval[a,t1]`)))) THEN
    USE_THEN "bd" (fun th -> MP_TAC(MATCH_MP th (ASSUME `a IN real_interval[a,t1]`))) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= C * B` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[real_continuous_on] THEN X_GEN_TAC `x:real` THEN DISCH_TAC THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN EXISTS_TAC `e / (C * B + &1)` THEN
  CONJ_TAC THENL [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `y:real` THEN STRIP_TAC THEN
  USE_THEN "cmp" (fun th -> MP_TAC(MATCH_MP th
    (CONJ (ASSUME `y IN real_interval[a,t1]`) (ASSUME `x IN real_interval[a,t1]`)))) THEN
  USE_THEN "cmp" (fun th -> MP_TAC(MATCH_MP th
    (CONJ (ASSUME `x IN real_interval[a,t1]`) (ASSUME `y IN real_interval[a,t1]`)))) THEN
  USE_THEN "bd" (fun th -> MP_TAC(MATCH_MP th (ASSUME `x IN real_interval[a,t1]`))) THEN
  USE_THEN "bd" (fun th -> MP_TAC(MATCH_MP th (ASSUME `y IN real_interval[a,t1]`))) THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `C * abs(y - x) * (W:real->real) x <= C * B * abs(y - x) /\
    C * abs(x - y) * W y <= C * B * abs(y - x)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[ISPECL [`x:real`; `y:real`] REAL_ABS_SUB] THEN
    SUBGOAL_THEN `!w d. w <= B /\ &0 <= d ==> C * d * w <= C * B * d`
    (fun th -> CONJ_TAC THEN MATCH_MP_TAC th THEN ASM_REWRITE_TAC[REAL_ABS_POS]) THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `C * d * B` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(C * B) * abs(y - x) <= (C * B) * (e / (C * B + &1))` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(C * B) * (e / (C * B + &1)) < e` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < C * B + &1` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(C * B) * (e / (C * B + &1)) = e - e / (C * B + &1)` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < C * B + &1` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 < y ==> x - y < x`) THEN
    MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* Pointwise second-order bound for the area density along the flow. *)

let P4_SQRT_CONCAVE = prove
 (`!X E. &0 <= X /\ &0 < E ==> sqrt X <= sqrt E + (X - E) / (&2 * sqrt E)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < sqrt E /\ &0 <= sqrt X` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LT; SQRT_POS_LE]; ALL_TAC] THEN
  MP_TAC(SPEC `X:real` SQRT_POW_2) THEN MP_TAC(SPEC `E:real` SQRT_POW_2) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
  ABBREV_TAC `r = sqrt E` THEN ABBREV_TAC `q = sqrt X` THEN
  REPEAT(DISCH_THEN(SUBST1_TAC o SYM)) THEN
  MATCH_MP_TAC(REAL_ARITH `q - r <= x ==> q <= r + x`) THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_ARITH `&0 < r ==> &0 < &2 * r`] THEN
  MP_TAC(SPEC `q - r:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC);;

let P4_GRAM_QF_GEN = prove
 (`!(J:real^3^N) (X:real^N^N) w.
        w dot ((transp J ** X ** J) ** w) = (J ** w) dot (X ** (J ** w))`,
  REWRITE_TAC[GSYM MATRIX_VECTOR_MUL_ASSOC; DOT_MATRIX_TRANSP_RMUL]);;

let P4_SYM_CONGRUENCE = prove
 (`!(J:real^M^N) (X:real^N^N).
        symmetric_matrix X ==> symmetric_matrix(transp J ** X ** J)`,
  SIMP_TAC[symmetric_matrix; MATRIX_TRANSP_MUL; TRANSP_TRANSP; MATRIX_MUL_ASSOC]);;

let P4_TAYLOR_POINT = prove
 (`!(J:real^3^N) (G0:real^N^N) G1 Ric C0 h.
        positive_semidefinite G0 /\ positive_semidefinite G1 /\
        symmetric_matrix Ric /\ &0 <= C0 /\ &0 <= h /\
        (!v. abs(v dot (Ric ** v)) <= C0 * (v dot (G0 ** v))) /\
        (!v. abs(v dot ((G1 - G0) ** v)) <= C0 * h * (v dot (G0 ** v))) /\
        (!v. abs(v dot ((G1 - G0 - h %% (--(&2) %% Ric)) ** v))
             <= C0 * h pow 2 * (v dot (G0 ** v)))
        ==> sqrt(p4_e2(transp J ** G1 ** J)) <=
            sqrt(p4_e2(transp J ** G0 ** J)) -
            h * (if p4_e2(transp J ** G0 ** J) = &0 then &0
                 else p4_e2_pol (transp J ** G0 ** J) (transp J ** Ric ** J) /
                      sqrt(p4_e2(transp J ** G0 ** J))) +
            (&2 * C0 + &3 * C0 pow 2) * h pow 2 * sqrt(p4_e2(transp J ** G0 ** J))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `positive_semidefinite(transp(J:real^3^N) ** (G0:real^N^N) ** J) /\
    positive_semidefinite(transp(J:real^3^N) ** (G1:real^N^N) ** J) /\
    symmetric_matrix(transp(J:real^3^N) ** (Ric:real^N^N) ** J) /\
    symmetric_matrix(transp(J:real^3^N) ** ((G1:real^N^N) - G0) ** J) /\
    symmetric_matrix(transp(J:real^3^N) **
                     ((G1:real^N^N) - G0 - h %% (--(&2) %% Ric)) ** J)`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[POSITIVE_SEMIDEFINITE_SIMILAR] THEN REPEAT CONJ_TAC THEN
    MATCH_MP_TAC P4_SYM_CONGRUENCE THEN
    RULE_ASSUM_TAC(REWRITE_RULE[positive_semidefinite]) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[symmetric_matrix]) THEN
    ASM_REWRITE_TAC[symmetric_matrix; TRANSP_MATRIX_SUB; TRANSP_MATRIX_CMUL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(!w. abs(w dot ((transp(J:real^3^N) ** (Ric:real^N^N) ** J) ** w)) <=
         C0 * (w dot ((transp J ** (G0:real^N^N) ** J) ** w))) /\
    (!w. abs(w dot ((transp(J:real^3^N) ** ((G1:real^N^N) - G0) ** J) ** w)) <=
         (C0 * h) * (w dot ((transp J ** G0 ** J) ** w))) /\
    (!w. abs(w dot ((transp(J:real^3^N) ** ((G1:real^N^N) - G0 - h %% (--(&2) %% Ric)) **
                     J) ** w)) <=
         (C0 * h pow 2) * (w dot ((transp J ** G0 ** J) ** w)))`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[P4_GRAM_QF_GEN; GSYM REAL_MUL_ASSOC] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `transp(J:real^3^N) ** (G1:real^N^N) ** J =
    transp J ** G0 ** J + transp J ** (G1 - G0) ** J`
  ASSUME_TAC THENL
   [REWRITE_TAC[MATRIX_SUB_LDISTRIB; MATRIX_SUB_RDISTRIB] THEN MATRIX_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `A = transp(J:real^3^N) ** (G0:real^N^N) ** J` THEN
  ABBREV_TAC `QJ = transp(J:real^3^N) ** (Ric:real^N^N) ** J` THEN
  ABBREV_TAC `B = transp(J:real^3^N) ** ((G1:real^N^N) - G0) ** J` THEN
  ABBREV_TAC `R = transp(J:real^3^N) ** ((G1:real^N^N) - G0 - h %% (--(&2) %% Ric)) ** J` THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`A:real^3^3`; `R:real^3^3`; `C0 * h pow 2`] P4_E2_BOUNDS) THEN
  MP_TAC(ISPECL [`A:real^3^3`; `B:real^3^3`; `C0 * h`] P4_E2_BOUNDS) THEN
  MP_TAC(ISPECL [`A:real^3^3`; `QJ:real^3^3`; `C0:real`] P4_E2_BOUNDS) THEN
  ASM_SIMP_TAC[REAL_LE_MUL; REAL_LE_POW_2] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= p4_e2(A:real^3^3) /\ &0 <= p4_e2(A + B:real^3^3)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC P4_E2_PSD THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `positive_semidefinite(transp(J:real^3^N) ** (G1:real^N^N) ** J)` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `p4_e2(A + B:real^3^3) <=
    p4_e2 A - &2 * h * p4_e2_pol A QJ + (&2 * C0 + &3 * C0 pow 2) * h pow 2 * p4_e2 A`
  ASSUME_TAC THENL
   [REWRITE_TAC[P4_E2_ADD] THEN
    SUBGOAL_THEN `p4_e2_pol (A:real^3^3) B = p4_e2_pol A R - (&2 * h) * p4_e2_pol A QJ`
    SUBST1_TAC THENL
     [SUBGOAL_THEN `B:real^3^3 = R - (&2 * h) %% QJ` SUBST1_TAC THENL
       [MAP_EVERY EXPAND_TAC ["B"; "R"; "QJ"] THEN
        REWRITE_TAC[MATRIX_SUB_LDISTRIB; MATRIX_SUB_RDISTRIB; MATRIX_MUL_LMUL;
                    MATRIX_MUL_RMUL; MATRIX_CMUL_ASSOC] THEN
        MATRIX_ARITH_TAC;
        REWRITE_TAC[P4_E2_POL_SUB; P4_E2_POL_CMUL]];
      ALL_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_MUL]) THEN
    SUBGOAL_THEN `(&2 * C0 + &3 * C0 pow 2) * h pow 2 * p4_e2(A:real^3^3) =
                  &2 * (C0 * h pow 2) * p4_e2 A + &3 * (C0 pow 2 * h pow 2) * p4_e2 A`
    SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `E = p4_e2(A:real^3^3)` THEN ABBREV_TAC `P = p4_e2_pol (A:real^3^3) QJ` THEN
  ASM_CASES_TAC `E = &0` THENL
   [UNDISCH_TAC `E = &0` THEN DISCH_THEN SUBST_ALL_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[REAL_MUL_RZERO]) THEN
    SUBGOAL_THEN `P = &0` SUBST_ALL_TAC THENL
     [UNDISCH_TAC `abs(P) <= &0` THEN REAL_ARITH_TAC; ALL_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[REAL_MUL_RZERO; REAL_SUB_RZERO; REAL_ADD_RID]) THEN
    REWRITE_TAC[SQRT_0; REAL_MUL_RZERO; REAL_SUB_RZERO; REAL_ADD_RID] THEN
    SUBGOAL_THEN `p4_e2(A + B:real^3^3) = &0` SUBST1_TAC THENL
     [ASM_REAL_ARITH_TAC; REWRITE_TAC[SQRT_0; REAL_LE_REFL]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 < E /\ &0 < sqrt E` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; MATCH_MP_TAC SQRT_POS_LT THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sqrt E + (p4_e2(A + B:real^3^3) - E) / (&2 * sqrt E)` THEN
  ASM_SIMP_TAC[P4_SQRT_CONCAVE] THEN
  ABBREV_TAC `K = &2 * C0 + &3 * C0 pow 2` THEN
  SUBGOAL_THEN `&0 <= K` ASSUME_TAC THENL
   [EXPAND_TAC "K" THEN MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `E = sqrt E pow 2` ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE]; ALL_TAC] THEN
  ABBREV_TAC `r = sqrt E` THEN ABBREV_TAC `X = p4_e2(A + B:real^3^3)` THEN
  SUBGOAL_THEN `(X - E) / (&2 * r) <= --(h * (P / r)) + K * h pow 2 * r` MP_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `&0 < r ==> &0 < &2 * r`] THEN
    SUBGOAL_THEN `(--(h * (P / r)) + K * h pow 2 * r) * (&2 * r) =
                  --(&2) * h * P + &2 * K * h pow 2 * r pow 2`
    SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < r` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= K * h pow 2 * r pow 2` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2];
      ALL_TAC] THEN
    UNDISCH_TAC `X <= E - &2 * h * P + K * h pow 2 * E` THEN
    UNDISCH_TAC `E = r pow 2` THEN DISCH_THEN SUBST1_TAC THEN
    UNDISCH_TAC `&0 <= K * h pow 2 * r pow 2` THEN REAL_ARITH_TAC;
    REAL_ARITH_TAC]);;

(* The second-order Taylor bound for slice areas along the flow. *)

let P4_AREA_TAYLOR = prove
 (`P4_AREA_TAYLOR_STATEMENT (:A)`,
  REWRITE_TAC[P4_AREA_TAYLOR_STATEMENT] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:real->A->real^3^3`; `a:real`; `b:real`; `t1:real`] P4_RF_UNIFORM) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `C0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "unif"))) THEN
  ABBREV_TAC `K = &2 * C0 + &3 * C0 pow 2` THEN
  SUBGOAL_THEN `&0 <= K /\ &2 * C0 <= K` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "K" THEN
    SUBGOAL_THEN `&0 <= &3 * C0 pow 2` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  EXISTS_TAC `K:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`sigma:real^3->real->A`; `s:real`; `t:real`; `h:real`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool) /\
                ricci_flow_on (top,atlas) a b (g:real->A->real^3^3)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[ricci_flow_from; ricci_flow_on]; ALL_TAC] THEN
  SUBGOAL_THEN `t IN real_interval[a,t1] /\ t + h IN real_interval[a,t1] /\
                a < t /\ t < b /\ t <= t + h`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `riemannian_metric atlas ((g:real->A->real^3^3) t) /\
                riemannian_metric atlas (g(t + h))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC P4_RF_RIEMANNIAN THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `a:real`; `b:real`] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `Q = mfd_ricci_matrix atlas ((g:real->A->real^3^3) t)` THEN
  SUBGOAL_THEN
   `!x. x IN topspace top
        ==> transp((Q:A->real^3^3) x) = Q x /\
            !v. abs(v dot (Q x ** v)) <= C0 * (v dot ((g:real->A->real^3^3) t x ** v))`
  (LABEL_TAC "Qprop") THENL
   [X_GEN_TAC `x:A` THEN DISCH_TAC THEN CONJ_TAC THENL
     [EXPAND_TAC "Q" THEN MATCH_MP_TAC P4_RICCI_MATRIX_SYM THEN
      EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `v:real^3` THEN EXPAND_TAC "Q" THEN
      USE_THEN "unif" (fun th -> MP_TAC(SPEC `v:real^3` (MATCH_MP th
        (CONJ (ASSUME `(x:A) IN topspace top`)
          (CONJ (ASSUME `t IN real_interval[a,t1]`) (ASSUME `t IN real_interval[a,t1]`)))))) THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `u = \y. (sigma:real^3->real->A) y s` THEN
  (* continuity of the three densities on S^2 *)
  SUBGOAL_THEN
   `(\y. lift(p4_s2_density atlas ((g:real->A->real^3^3) t) (u:real^3->A) y))
    continuous_on sphere(vec 0,&1) /\
    (\y. lift(p4_s2_density atlas ((g:real->A->real^3^3) (t + h)) (u:real^3->A) y))
    continuous_on sphere(vec 0,&1) /\
    (\y. lift(p4_s2_trdensity atlas ((g:real->A->real^3^3) t) (Q:A->real^3^3)
                                (u:real^3->A) y))
    continuous_on sphere(vec 0,&1)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "u" THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`]
                          P4_SLICE_DENSITY_CONT) THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`]
                          P4_SLICE_DENSITY_CONT) THEN ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`\x. p4_s2_trdensity atlas ((g:real->A->real^3^3) t) (Q:A->real^3^3)
                           (\y. (sigma:real^3->real->A) y (drop(sndcart x))) (fstcart x)`;
                     `s:real`] P4_SLAB_SLICE) THEN
      REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`]
                          P4_SWEEP_TRDENSITY_CONT) THEN
      EXISTS_TAC `C0:real` THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `c:(A->bool)#(A->real^3)` THEN DISCH_TAC THEN EXPAND_TAC "Q" THEN
      MATCH_MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`]
                          P4_RF_RICCI_CONT) THEN
      MAP_EVERY EXISTS_TAC [`a:real`; `b:real`] THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* pointwise bounds *)
  SUBGOAL_THEN
   `!y. y IN sphere(vec 0,&1)
        ==> abs(p4_s2_trdensity atlas ((g:real->A->real^3^3) t) (Q:A->real^3^3) u y) <=
            &2 * C0 * p4_s2_density atlas (g t) (u:real^3->A) y /\
            p4_s2_density atlas (g(t + h)) u y <=
            p4_s2_density atlas (g t) u y -
            h * p4_s2_trdensity atlas (g t) Q u y +
            K * h pow 2 * p4_s2_density atlas (g t) u y`
  (LABEL_TAC "PT") THENL
   [X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(u:real^3->A) y IN topspace top` ASSUME_TAC THENL
     [EXPAND_TAC "u" THEN
      MATCH_MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`]
                          P4_SLICE_IN_TOPSPACE) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    USE_THEN "Qprop" (fun th -> MP_TAC(MATCH_MP th
      (ASSUME `(u:real^3->A) y IN topspace top`))) THEN
    DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC P4_TRDENSITY_BOUND THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`]
                          P4_RIEMANNIAN_PSD) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[p4_s2_density; p4_s2_trdensity; p4_s2_gram] THEN
    EXPAND_TAC "K" THEN MATCH_MP_TAC P4_TAYLOR_POINT THEN
    ASM_REWRITE_TAC[symmetric_matrix] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`]
                          P4_RIEMANNIAN_PSD) THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`]
                          P4_RIEMANNIAN_PSD) THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `v:real^3` THEN
      USE_THEN "unif" (fun th -> MP_TAC(CONJUNCT1(SPEC `v:real^3` (MATCH_MP th
        (CONJ (ASSUME `(u:real^3->A) y IN topspace top`)
          (CONJ (ASSUME `t + h IN real_interval[a,t1]`)
                (ASSUME `t IN real_interval[a,t1]`))))))) THEN
      REWRITE_TAC[REAL_ARITH `(t + h) - t = h`] THEN
      ASM_SIMP_TAC[REAL_ARITH `&0 <= h ==> abs h = h`];
      X_GEN_TAC `v:real^3` THEN
      USE_THEN "unif" (fun th -> MP_TAC(CONJUNCT2(CONJUNCT2(SPEC `v:real^3` (MATCH_MP th
        (CONJ (ASSUME `(u:real^3->A) y IN topspace top`)
          (CONJ (ASSUME `t + h IN real_interval[a,t1]`)
                (ASSUME `t IN real_interval[a,t1]`)))))))) THEN
      ASM_REWRITE_TAC[REAL_ARITH `(t + h) - t = h`] THEN EXPAND_TAC "Q" THEN
      REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[p4_s2_area; p4_s2_trint] THEN
  ABBREV_TAC `d0 = p4_s2_density atlas ((g:real->A->real^3^3) t) (u:real^3->A)` THEN
  ABBREV_TAC `d1 = p4_s2_density atlas ((g:real->A->real^3^3) (t + h)) (u:real^3->A)` THEN
  ABBREV_TAC `td = p4_s2_trdensity atlas ((g:real->A->real^3^3) t) (Q:A->real^3^3)
                                   (u:real^3->A)` THEN
  SUBGOAL_THEN `!y. y IN sphere(vec 0,&1) ==> &0 <= (d0:real^3->real) y` ASSUME_TAC THENL
   [X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN MAP_EVERY EXPAND_TAC ["d0"; "u"] THEN
    MATCH_MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`]
                        P4_SLICE_DENSITY_POS) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= p4_s2_integral (d0:real^3->real)` ASSUME_TAC THENL
   [MATCH_MP_TAC P4_S2_INTEGRAL_POS THEN ASM_REWRITE_TAC[ETA_AX] THEN
    ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(\y. lift(abs((td:real^3->real) y))) continuous_on sphere(vec 0,&1) /\
    (\y. lift((&2 * C0) * (d0:real^3->real) y)) continuous_on sphere(vec 0,&1) /\
    (\y. lift(h * (td:real^3->real) y)) continuous_on sphere(vec 0,&1) /\
    (\y. lift((d0:real^3->real) y - h * td y)) continuous_on sphere(vec 0,&1) /\
    (\y. lift((K * h pow 2) * (d0:real^3->real) y)) continuous_on sphere(vec 0,&1) /\
    (\y. lift(((d0:real^3->real) y - h * td y) + (K * h pow 2) * d0 y))
    continuous_on sphere(vec 0,&1)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[LIFT_ADD; LIFT_SUB; LIFT_CMUL; GSYM NORM_LIFT] THEN
    REPEAT CONJ_TAC THEN
    REPEAT((MATCH_MP_TAC CONTINUOUS_ON_ADD THEN CONJ_TAC) ORELSE
           (MATCH_MP_TAC CONTINUOUS_ON_SUB THEN CONJ_TAC) ORELSE
           MATCH_MP_TAC CONTINUOUS_ON_CMUL ORELSE
           MATCH_MP_TAC CONTINUOUS_ON_LIFT_NORM_COMPOSE) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `p4_s2_integral (\y. abs((td:real^3->real) y))` THEN CONJ_TAC THENL
     [MATCH_MP_TAC P4_S2_INTEGRAL_ABS THEN ASM_REWRITE_TAC[ETA_AX]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `p4_s2_integral (\y. (&2 * C0) * (d0:real^3->real) y)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC P4_S2_INTEGRAL_MONO THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
      USE_THEN "PT" (fun th -> MP_TAC(CONJUNCT1(MATCH_MP th
        (ASSUME `y IN sphere(vec 0:real^3,&1)`)))) THEN
      REWRITE_TAC[REAL_MUL_ASSOC];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`d0:real^3->real`; `&2 * C0`] P4_S2_INTEGRAL_CMUL) THEN
    ASM_REWRITE_TAC[ETA_AX] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `p4_s2_integral (\y. ((d0:real^3->real) y - h * td y) + (K * h pow 2) * d0 y)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC P4_S2_INTEGRAL_MONO THEN ASM_REWRITE_TAC[ETA_AX] THEN
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    USE_THEN "PT" (fun th -> MP_TAC(CONJUNCT2(MATCH_MP th
      (ASSUME `y IN sphere(vec 0:real^3,&1)`)))) THEN
    REWRITE_TAC[REAL_MUL_ASSOC];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_EQ_IMP_LE THEN
  MP_TAC(ISPECL [`\y. (d0:real^3->real) y - h * td y`; `\y. (K * h pow 2) * (d0:real^3->real) y`]
                P4_S2_INTEGRAL_ADD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`d0:real^3->real`; `\y. h * (td:real^3->real) y`] P4_S2_INTEGRAL_SUB) THEN
  ASM_REWRITE_TAC[ETA_AX] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`td:real^3->real`; `h:real`] P4_S2_INTEGRAL_CMUL) THEN
  ASM_REWRITE_TAC[ETA_AX] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`d0:real^3->real`; `K * h pow 2`] P4_S2_INTEGRAL_CMUL) THEN
  ASM_REWRITE_TAC[ETA_AX] THEN DISCH_THEN SUBST1_TAC THEN
  REAL_ARITH_TAC);;


