(* ========================================================================= *)
(* Unit pc_cmr_crit (a unit of the replacement chain of pc_cm_replacement):  *)
(* spheres that are critical on the caps of a finite chart cover are         *)
(* cm_sharmonic (CMR_SHARMONIC_FROM_CAPS, shared with pc_cm_compactness),    *)
(* the first variation of cm_sen through two hemisphere charts               *)
(* (HMC_FIRST_VARIATION), and the energy lower bound for harmonic spheres    *)
(* from CM_EPS_REG.                                                          *)
(*                                                                           *)
(* Smoothness through the rotated stereographic charts.                      *)
(* ========================================================================= *)

needs "src/pc_cmr_ball.ml";;
needs "src/pc_hm_convexity.ml";;
needs "src/pc_smt_sphere.ml";;

prioritize_real();;
type_invention_error := true;;

let CMR_CAPMAP_SMOOTH = prove
 (`!Q:real^3^3. smooth_map_on (:real^2) (cm_capmap Q)`,
  GEN_TAC THEN
  SUBGOAL_THEN `cm_capmap (Q:real^3^3) = (\y:real^3. Q ** y) o stereo2_n_inv`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM; cm_capmap]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_LINEAR_O THEN
  REWRITE_TAC[OPEN_UNIV; MATRIX_VECTOR_MUL_LINEAR; STEX_STEREO2_N_INV_SMOOTH]);;

let CMR_SPHERE_CHART_SMOOTH = prove
 (`!(Q:real^3^3) (u:real^3->real^K).
     orthogonal_matrix Q /\ smooth_map_on {z:real^3 | ~(z = vec 0)} (wan_rext u)
     ==> smooth_map_on (:real^2) (\x. u(cm_capmap Q x))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
  EXISTS_TAC `wan_rext (u:real^3->real^K) o cm_capmap (Q:real^3^3)` THEN CONJ_TAC THENL
   [X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN REWRITE_TAC[o_THM; wan_rext] THEN
    FIRST_ASSUM(MP_TAC o CONJUNCT1 o MATCH_MP CMR_CAPMAP_FACTS) THEN
    DISCH_THEN(MP_TAC o CONJUNCT1 o SPEC `x:real^2`) THEN
    SIMP_TAC[IN_SPHERE_0; REAL_INV_1; VECTOR_MUL_LID];
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `{z:real^3 | ~(z = vec 0)}` THEN
    ASM_REWRITE_TAC[OPEN_UNIV; OPEN_NONZERO; CMR_CAPMAP_SMOOTH] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; IN_UNIV] THEN
    X_GEN_TAC `x:real^2` THEN
    FIRST_ASSUM(MP_TAC o CONJUNCT1 o MATCH_MP CMR_CAPMAP_FACTS) THEN
    DISCH_THEN(MP_TAC o CONJUNCT1 o SPEC `x:real^2`) THEN
    REWRITE_TAC[IN_SPHERE_0] THEN CONV_TAC NORM_ARITH]);;

let CMR_UNIT_NE_E3 = prove
 (`!w:real^3. norm w = &1 /\ ~(w = basis 3) ==> w$3 < &1`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  UNDISCH_TAC `~(w:real^3 = basis 3)` THEN REWRITE_TAC[] THEN
  UNDISCH_TAC `norm(w:real^3) = &1` THEN
  REWRITE_TAC[NORM_EQ_1; dot; DIMINDEX_3; SUM_3] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(w:real^3)$3 = &1` ASSUME_TAC THENL
   [MP_TAC(SPECL [`(w:real^3)$3`; `(w:real^3)$3 - &1`] REAL_LE_MUL) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MAP_EVERY (fun t -> MP_TAC(SPEC t REAL_LE_SQUARE)) [`(w:real^3)$1`; `(w:real^3)$2`] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(w:real^3)$1 * w$1 = &0 /\ (w:real^3)$2 * w$2 = &0` MP_TAC THENL
   [UNDISCH_TAC `(w:real^3)$1 * w$1 + w$2 * w$2 + w$3 * w$3 = &1` THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY (fun t -> MP_TAC(SPEC t REAL_LE_SQUARE)) [`(w:real^3)$1`; `(w:real^3)$2`] THEN
    REAL_ARITH_TAC;
    REWRITE_TAC[REAL_ENTIRE] THEN STRIP_TAC] THEN
  SIMP_TAC[CART_EQ; DIMINDEX_3; FORALL_3; BASIS_COMPONENT; ARITH] THEN
  ASM_REWRITE_TAC[]);;

let CMR_CHART_SET_OPEN = prove
 (`!Q:real^3^3. open {z:real^3 | ~(z = vec 0) /\ ~(inv(norm z) % z = Q ** basis 3)}`,
  GEN_TAC THEN
  SUBGOAL_THEN
   `{z:real^3 | ~(z = vec 0) /\ ~(inv(norm z) % z = (Q:real^3^3) ** basis 3)} =
    {z | z IN {z:real^3 | ~(z = vec 0)} /\
         (\z. inv(norm z) % z) z IN (:real^3) DELETE ((Q:real^3^3) ** basis 3)}`
  SUBST1_TAC THENL [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_DELETE; IN_UNIV]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN
  SIMP_TAC[OPEN_NONZERO; OPEN_DELETE; OPEN_UNIV] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN REWRITE_TAC[SMOOTH_MAP_ON_NORMALIZE]);;

let CMR_CHART_NORMALIZE_SMOOTH = prove
 (`!Q:real^3^3.
     orthogonal_matrix Q
     ==> smooth_map_on {z:real^3 | ~(z = vec 0) /\ ~(inv(norm z) % z = Q ** basis 3)}
                       (\z. cmr_chart Q (inv(norm z) % z))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
  EXISTS_TAC `(\x:real^3. stereo2_n(inv(norm x) % x)) o (\z:real^3. transp(Q:real^3^3) ** z)` THEN
  CONJ_TAC THENL
   [X_GEN_TAC `z:real^3` THEN REWRITE_TAC[IN_ELIM_THM; o_THM; cmr_chart] THEN STRIP_TAC THEN
    AP_TERM_TAC THEN
    ASM_SIMP_TAC[ORTHOGONAL_MATRIX_NORM; ORTHOGONAL_MATRIX_TRANSP; MATRIX_VECTOR_MUL_RMUL];
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
  EXISTS_TAC `{x:real^3 | ~(x = vec 0) /\ (inv(norm x) % x)$3 < &1}` THEN
  REWRITE_TAC[CMR_CHART_SET_OPEN; SMT_OPEN_NORMALIZED_HALFSPACES;
              SMT_STEREO_NORMALIZED_SMOOTH] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN X_GEN_TAC `z:real^3` THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `~(transp(Q:real^3^3) ** z:real^3 = vec 0)` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM NORM_EQ_0] THEN
      ASM_SIMP_TAC[ORTHOGONAL_MATRIX_NORM; ORTHOGONAL_MATRIX_TRANSP] THEN
      ASM_REWRITE_TAC[NORM_EQ_0];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CMR_UNIT_NE_E3 THEN CONJ_TAC THENL
     [REWRITE_TAC[NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM] THEN
      MATCH_MP_TAC REAL_MUL_LINV THEN ASM_REWRITE_TAC[NORM_EQ_0];
      ALL_TAC] THEN
    ASM_SIMP_TAC[ORTHOGONAL_MATRIX_NORM; ORTHOGONAL_MATRIX_TRANSP; GSYM MATRIX_VECTOR_MUL_RMUL] THEN
    DISCH_TAC THEN UNDISCH_TAC `~(inv(norm z) % z:real^3 = (Q:real^3^3) ** basis 3)` THEN
    REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o AP_TERM `\v:real^3. (Q:real^3^3) ** v`) THEN
    REWRITE_TAC[MATRIX_VECTOR_MUL_ASSOC] THEN
    ASM_SIMP_TAC[ORTHOGONAL_MATRIX_TRANSP_RMUL; MATRIX_VECTOR_MUL_LID];
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^3)` THEN
    REWRITE_TAC[SUBSET_UNIV] THEN
    SUBGOAL_THEN `(\z:real^3. transp(Q:real^3^3) ** z) = (\z. transp(Q:real^3^3) ** z) o (\z. z)`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_LINEAR_O THEN
    REWRITE_TAC[OPEN_UNIV; MATRIX_VECTOR_MUL_LINEAR; SMOOTH_MAP_ON_ID]]);;

let CMR_REXT_FROM_CHARTS = prove
 (`!(u:real^3->real^K) n (Q:num->real^3^3) (D:num->real^2->bool).
     (!k. 1 <= k /\ k <= n
          ==> orthogonal_matrix(Q k) /\ open(D k) /\
              smooth_map_on (D k) (\x. u(cm_capmap (Q k) x))) /\
     (!y. y IN sphere(vec 0,&1)
          ==> ?k. 1 <= k /\ k <= n /\ y IN IMAGE (cm_capmap (Q k)) (D k))
     ==> smooth_map_on {z:real^3 | ~(z = vec 0)} (wan_rext u)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN
  REWRITE_TAC[OPEN_NONZERO; IN_ELIM_THM] THEN X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `inv(norm z) % z:real^3`) THEN
  ASM_SIMP_TAC[SMT_NORMALIZE_SPHERE; IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `x0:real^2` STRIP_ASSUME_TAC)))) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `k:num`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CMR_CAPMAP_FACTS) THEN
  EXISTS_TAC `{w:real^3 | w IN {z:real^3 | ~(z = vec 0) /\
                                          ~(inv(norm z) % z = (Q:num->real^3^3) k ** basis 3)} /\
                          (\z. cmr_chart (Q k) (inv(norm z) % z)) w IN (D:num->real^2->bool) k}` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN ASM_REWRITE_TAC[CMR_CHART_SET_OPEN] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN ASM_SIMP_TAC[CMR_CHART_NORMALIZE_SMOOTH];
    REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
  EXISTS_TAC `(\x. (u:real^3->real^K)(cm_capmap ((Q:num->real^3^3) k) x)) o
              (\z. cmr_chart (Q k) (inv(norm z) % z))` THEN
  CONJ_TAC THENL
   [X_GEN_TAC `w:real^3` THEN REWRITE_TAC[IN_ELIM_THM; o_THM; wan_rext] THEN STRIP_TAC THEN
    AP_TERM_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[SMT_NORMALIZE_SPHERE];
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
  EXISTS_TAC `(D:num->real^2->bool) k` THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN ASM_REWRITE_TAC[CMR_CHART_SET_OPEN] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN ASM_SIMP_TAC[CMR_CHART_NORMALIZE_SMOOTH];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN SIMP_TAC[];
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
    EXISTS_TAC `{z:real^3 | ~(z = vec 0) /\
                            ~(inv(norm z) % z = (Q:num->real^3^3) k ** basis 3)}` THEN
    ASM_SIMP_TAC[CMR_CHART_NORMALIZE_SMOOTH] THEN SET_TAC[]]);;


(* ========================================================================= *)
(* The two hemisphere charts.  cm_capmap (mat 1) maps the open               *)
(* unit disc onto the open southern hemisphere, cm_capmap cmr_qb onto the   *)
(* open northern one (cmr_qb = diag(1,-1,-1)); the equator is negligible   *)
(* for cmr_sen_on, so cm_sen is the sum of two planar disc energies.        *)
(* ========================================================================= *)

let cmr_qb = new_definition
 `cmr_qb = (lambda i j. if i = j then (if i = 1 then &1 else -- &1) else &0):real^3^3`;;

let CMR_QB_FACTS = prove
 (`(!x:real^3. cmr_qb ** x = vector[x$1; --(x$2); --(x$3)]) /\
   orthogonal_matrix cmr_qb /\ cmr_qb ** basis 3 = --(basis 3)`,
  SUBGOAL_THEN `!x:real^3. cmr_qb ** x = vector[x$1; --(x$2); --(x$3)]` ASSUME_TAC THENL
   [GEN_TAC THEN
    SIMP_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3; matrix_vector_mul; LAMBDA_BETA;
             cmr_qb; ARITH; SUM_3] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[ORTHOGONAL_MATRIX_NORM_EQ; NORM_EQ] THEN CONJ_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[dot; DIMINDEX_3; SUM_3; VECTOR_3] THEN REAL_ARITH_TAC;
    SIMP_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3; VECTOR_NEG_COMPONENT;
             BASIS_COMPONENT; ARITH] THEN
    REAL_ARITH_TAC]);;

let CMR_STEREO_HEIGHT = prove
 (`!x:real^2. (stereo2_n_inv x)$3 < &0 <=> norm x < &1`,
  GEN_TAC THEN REWRITE_TAC[STEX_STEREO2_N_INV_COMPONENTS] THEN
  SUBGOAL_THEN `&0 < norm(x:real^2) pow 2 + &1` ASSUME_TAC THENL
   [MP_TAC(SPEC `norm(x:real^2)` REAL_LE_POW_2) THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_MUL_LZERO; REAL_SUB_LT] THEN
  REWRITE_TAC[REAL_ARITH `n - &1 < &0 <=> n < &1`; ABS_SQUARE_LT_1; REAL_ABS_NORM]);;

let CMR_HEMI_SOUTH = prove
 (`IMAGE (cm_capmap (mat 1)) (ball(vec 0,&1)) =
   {y:real^3 | y IN sphere(vec 0,&1) /\ y$3 < &0}`,
  MP_TAC(SPEC `mat 1:real^3^3` CMR_CAPMAP_FACTS) THEN
  REWRITE_TAC[ORTHOGONAL_MATRIX_ID; MATRIX_VECTOR_MUL_LID] THEN STRIP_TAC THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM; IN_BALL_0] THEN X_GEN_TAC `y:real^3` THEN
  EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `x:real^2` STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[cm_capmap; MATRIX_VECTOR_MUL_LID; CMR_STEREO_HEIGHT] THEN
    ASM_REWRITE_TAC[GSYM cm_capmap];
    STRIP_TAC THEN EXISTS_TAC `cmr_chart (mat 1) (y:real^3)` THEN
    SUBGOAL_THEN `~(y:real^3 = basis 3)` ASSUME_TAC THENL
     [DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `(basis 3:real^3)$3 < &0` THEN
      SIMP_TAC[BASIS_COMPONENT; DIMINDEX_3; ARITH] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `cm_capmap (mat 1) (cmr_chart (mat 1) y) = y:real^3` ASSUME_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM CMR_STEREO_HEIGHT] THEN
    UNDISCH_TAC `cm_capmap (mat 1) (cmr_chart (mat 1) y) = y:real^3` THEN
    REWRITE_TAC[cm_capmap; MATRIX_VECTOR_MUL_LID] THEN DISCH_THEN SUBST1_TAC THEN
    ASM_REWRITE_TAC[]]);;

let CMR_HEMI_NORTH = prove
 (`IMAGE (cm_capmap cmr_qb) (ball(vec 0,&1)) =
   {y:real^3 | y IN sphere(vec 0,&1) /\ &0 < y$3}`,
  STRIP_ASSUME_TAC CMR_QB_FACTS THEN
  MP_TAC(SPEC `cmr_qb` CMR_CAPMAP_FACTS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM; IN_BALL_0] THEN X_GEN_TAC `y:real^3` THEN
  SUBGOAL_THEN `!x:real^2. (cm_capmap cmr_qb x)$3 = --((stereo2_n_inv x)$3)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[cm_capmap; VECTOR_3]; ALL_TAC] THEN
  EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `x:real^2` STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[REAL_ARITH `&0 < --a <=> a < &0`; CMR_STEREO_HEIGHT] THEN
    ASM_REWRITE_TAC[];
    STRIP_TAC THEN EXISTS_TAC `cmr_chart cmr_qb (y:real^3)` THEN
    SUBGOAL_THEN `~(y:real^3 = --(basis 3))` ASSUME_TAC THENL
     [DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `&0 < (--(basis 3):real^3)$3` THEN
      SIMP_TAC[VECTOR_NEG_COMPONENT; BASIS_COMPONENT; DIMINDEX_3; ARITH] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `cm_capmap cmr_qb (cmr_chart cmr_qb y) = y:real^3` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `cmr_chart`)) (concl th) && is_imp(snd(strip_forall(concl th))))) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[GSYM CMR_STEREO_HEIGHT] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `cmr_chart cmr_qb (y:real^3)` o
      check (fun th -> is_forall(concl th) &&
                       can (find_term ((=) `--`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `&0 < (y:real^3)$3` THEN REAL_ARITH_TAC]);;

let CMR_EQUATOR_CONE = prove
 (`negligible(cmr_cone {y:real^3 | y IN sphere(vec 0,&1) /\ y$3 = &0})`,
  MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN EXISTS_TAC `{z:real^3 | z$3 = &0}` THEN
  REWRITE_TAC[NEGLIGIBLE_STANDARD_HYPERPLANE] THEN
  REWRITE_TAC[SUBSET; cmr_cone; IN_ELIM_THM; VECTOR_MUL_COMPONENT; REAL_ENTIRE] THEN
  X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `inv(norm(z:real^3)) = &0` THEN
  REWRITE_TAC[REAL_INV_EQ_0; NORM_EQ_0] THEN ASM_MESON_TAC[CMT_SHELL_NONZERO]);;

let CMR_SEN_HEMIS = prove
 (`!(G:real^K->real^K^K) (w:real^3->real^K) Lam.
     wan_s2_w12 w /\ CMR_GCOND G Lam
     ==> cm_sen G w = cm_gen G (ball(vec 0,&1)) (\x. w(cm_capmap (mat 1) x)) +
                      cm_gen G (ball(vec 0,&1)) (\x. w(cm_capmap cmr_qb x))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[CMR_GCOND]) THEN
  STRIP_ASSUME_TAC CMR_QB_FACTS THEN
  MP_TAC(ISPECL [`G:real^K->real^K^K`; `w:real^3->real^K`; `Lam:real`] CMR_SEN_DENS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN
  ABBREV_TAC `E = {y:real^3 | y IN sphere(vec 0,&1) /\ y$3 = &0}` THEN
  SUBGOAL_THEN
   `sphere(vec 0:real^3,&1) =
    (IMAGE (cm_capmap (mat 1)) (ball(vec 0,&1)) UNION E) UNION
    IMAGE (cm_capmap cmr_qb) (ball(vec 0,&1))`
  SUBST1_TAC THENL
   [REWRITE_TAC[CMR_HEMI_SOUTH; CMR_HEMI_NORTH] THEN EXPAND_TAC "E" THEN
    REWRITE_TAC[EXTENSION; IN_UNION; IN_ELIM_THM] THEN GEN_TAC THEN
    ASM_CASES_TAC `(x:real^3) IN sphere(vec 0,&1)` THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `negligible(cmr_cone E)` ASSUME_TAC THENL
   [EXPAND_TAC "E" THEN REWRITE_TAC[CMR_EQUATOR_CONE]; ALL_TAC] THEN
  SUBGOAL_THEN
   `lebesgue_measurable(cmr_cone(IMAGE (cm_capmap (mat 1)) (ball(vec 0,&1)))) /\
    lebesgue_measurable(cmr_cone(IMAGE (cm_capmap cmr_qb) (ball(vec 0,&1)))) /\
    lebesgue_measurable(cmr_cone E)`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[CMR_CAPMAP_CONE; ORTHOGONAL_MATRIX_ID; OPEN_BALL;
                 NEGLIGIBLE_IMP_LEBESGUE_MEASURABLE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `DISJOINT (IMAGE (cm_capmap (mat 1)) (ball(vec 0,&1)) UNION E)
             (IMAGE (cm_capmap cmr_qb) (ball(vec 0:real^2,&1))) /\
    DISJOINT (IMAGE (cm_capmap (mat 1)) (ball(vec 0:real^2,&1))) E`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[CMR_HEMI_SOUTH; CMR_HEMI_NORTH] THEN EXPAND_TAC "E" THEN
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_UNION; IN_ELIM_THM; NOT_IN_EMPTY] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`G:real^K->real^K^K`; `w:real^3->real^K`; `Lam:real`;
                 `IMAGE (cm_capmap (mat 1)) (ball(vec 0:real^2,&1)) UNION E`;
                 `IMAGE (cm_capmap cmr_qb) (ball(vec 0:real^2,&1))`] CMR_SEN_ON_UNION) THEN
  ASM_REWRITE_TAC[CMR_CONE_UNION] THEN
  ANTS_TAC THENL [MATCH_MP_TAC LEBESGUE_MEASURABLE_UNION THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`G:real^K->real^K^K`; `w:real^3->real^K`; `Lam:real`;
                 `IMAGE (cm_capmap (mat 1)) (ball(vec 0:real^2,&1))`; `E:real^3->bool`]
                CMR_SEN_ON_UNION) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `cmr_sen_on (G:real^K->real^K^K) (w:real^3->real^K) E = &0` SUBST1_TAC THENL
   [ASM_SIMP_TAC[cmr_sen_on; INTEGRAL_ON_NEGLIGIBLE; DROP_VEC] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ADD_RID; cm_gen] THEN BINOP_TAC THEN
  MATCH_MP_TAC CMR_CAP_EN THEN EXISTS_TAC `Lam:real` THEN
  ASM_REWRITE_TAC[ORTHOGONAL_MATRIX_ID; OPEN_BALL]);;


(* ========================================================================= *)
(* The first variation of cm_sen for smooth maps and smooth variations,      *)
(* computed in the two hemisphere charts with HMC_FIRST_VARIATION            *)
(* (pc_hm_convexity).                                                        *)
(* ========================================================================= *)

let cmr_fvc = new_definition
 `cmr_fvc (S:real^K->bool) (G:real^K->real^K^K) (Q:real^3^3) (u:real^3->real^K)
          (phi:real^3->real^K) =
    sum(1..2) (\i. drop(integral (ball(vec 0,&1))
       (\x. lift(hmc_ld S G (\x. u(cm_capmap Q x)) (\x. phi(cm_capmap Q x))
                       (\y. partial_derivative i (\x. phi(cm_capmap Q x)) y) i x)))) / &2`;;

let cmr_fv = new_definition
 `cmr_fv (S:real^K->bool) (G:real^K->real^K^K) (u:real^3->real^K) (phi:real^3->real^K) =
    cmr_fvc S G (mat 1) u phi + cmr_fvc S G cmr_qb u phi`;;

let CMR_TARGET_GCOND = prove
 (`!S (G:real^K->real^K^K) d. cm_target S G d ==> ?Lam. &0 <= Lam /\ CMR_GCOND G Lam`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cm_target; CMR_GCOND] THEN STRIP_TAC THEN
  EXISTS_TAC `Lam:real` THEN REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON];
    ASM_REWRITE_TAC[];
    REPEAT GEN_TAC THEN CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[]] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `lam * norm(v:real^K) pow 2` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_MUL THEN
    REWRITE_TAC[REAL_LE_POW_2] THEN ASM_REAL_ARITH_TAC]);;

let CMR_SPHERE_BOUND = prove
 (`!phi:real^3->real^K.
     smooth_map_on {z:real^3 | ~(z = vec 0)} (wan_rext phi)
     ==> ?M. &0 < M /\ !y. y IN sphere(vec 0,&1) ==> norm(phi y) <= M`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `compact(IMAGE (wan_rext (phi:real^3->real^K)) (sphere(vec 0,&1)))` MP_TAC THENL
   [MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN REWRITE_TAC[COMPACT_SPHERE] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `{z:real^3 | ~(z = vec 0)}` THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON] THEN
    REWRITE_TAC[SUBSET; IN_SPHERE_0; IN_ELIM_THM] THEN
    GEN_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[GSYM NORM_EQ_0] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
  REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `M:real` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `y:real^3`) THEN ASM_REWRITE_TAC[wan_rext] THEN
  UNDISCH_TAC `(y:real^3) IN sphere(vec 0,&1)` THEN
  SIMP_TAC[IN_SPHERE_0; REAL_INV_1; VECTOR_MUL_LID]);;

let CMR_VARIATION_W12 = prove
 (`!S (G:real^K->real^K^K) d (u:real^3->real^K) (phi:real^3->real^K) M e.
     cm_target S G d /\
     smooth_map_on {z:real^3 | ~(z = vec 0)} (wan_rext u) /\
     (!y. y IN sphere(vec 0,&1) ==> u y IN S) /\
     smooth_map_on {z:real^3 | ~(z = vec 0)} (wan_rext phi) /\
     (!y. y IN sphere(vec 0,&1) ==> norm(phi y) <= M) /\ abs e * M < d
     ==> smooth_map_on {z:real^3 | ~(z = vec 0)}
                       (wan_rext (\y. closest_point S (u y + e % phi y))) /\
         wan_s2_w12 (\y. closest_point S (u y + e % phi y))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HMC_TARGET_BASICS) THEN
  SUBGOAL_THEN
   `smooth_map_on {z:real^3 | ~(z = vec 0)}
                  (wan_rext (\y. closest_point S ((u:real^3->real^K) y + e % phi y)))`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `wan_rext (\y. closest_point S ((u:real^3->real^K) y + e % phi y)) =
      closest_point S o (\z. wan_rext u z + e % wan_rext phi z)`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM; wan_rext]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `cm_tube (S:real^K->bool) d` THEN
    ASM_REWRITE_TAC[OPEN_NONZERO] THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; cm_tube; wan_rext] THEN
      X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
      EXISTS_TAC `(u:real^3->real^K)(inv(norm z) % z)` THEN
      ASM_SIMP_TAC[SMT_NORMALIZE_SPHERE] THEN
      REWRITE_TAC[dist; VECTOR_ARITH `(a + b) - a:real^N = b`; NORM_MUL] THEN
      MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `abs e * M` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[SMT_NORMALIZE_SPHERE];
      MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN ASM_REWRITE_TAC[OPEN_NONZERO; ETA_AX] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_CMUL_OPEN THEN ASM_REWRITE_TAC[OPEN_NONZERO; ETA_AX]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `\y. closest_point S ((u:real^3->real^K) y + e % phi y)` CMT_REXT_WD_AE) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[smooth_map_on]; SIMP_TAC[wan_s2_w12]]);;

let CMR_FV = prove
 (`!S (G:real^K->real^K^K) d (u:real^3->real^K) (phi:real^3->real^K).
     cm_target S G d /\
     smooth_map_on {z:real^3 | ~(z = vec 0)} (wan_rext u) /\
     (!y. y IN sphere(vec 0,&1) ==> u y IN S) /\
     smooth_map_on {z:real^3 | ~(z = vec 0)} (wan_rext phi)
     ==> ((\e. cm_sen G (\y. closest_point S (u y + e % phi y))) has_real_derivative
          cmr_fv S G u phi) (atreal (&0))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HMC_TARGET_BASICS) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `Lam:real` STRIP_ASSUME_TAC o MATCH_MP CMR_TARGET_GCOND) THEN
  STRIP_ASSUME_TAC CMR_QB_FACTS THEN
  MP_TAC(ISPEC `phi:real^3->real^K` CMR_SPHERE_BOUND) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `M:real` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_TRANSFORM_ATREAL THEN
  MAP_EVERY EXISTS_TAC
   [`\e. cm_gen G (ball(vec 0,&1))
           (\x. closest_point S ((u:real^3->real^K)(cm_capmap (mat 1) x) +
                                 e % (phi:real^3->real^K)(cm_capmap (mat 1) x))) +
         cm_gen G (ball(vec 0,&1))
           (\x. closest_point S (u(cm_capmap cmr_qb x) + e % phi(cm_capmap cmr_qb x)))`;
    `d / M`] THEN
  ASM_SIMP_TAC[REAL_LT_DIV] THEN CONJ_TAC THENL
   [X_GEN_TAC `e:real` THEN REWRITE_TAC[REAL_SUB_RZERO] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`G:real^K->real^K^K`;
                   `\y. closest_point S ((u:real^3->real^K) y + e % phi y)`; `Lam:real`]
                  CMR_SEN_HEMIS) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `u:real^3->real^K`;
                     `phi:real^3->real^K`; `M:real`; `e:real`] CMR_VARIATION_W12) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
       [UNDISCH_TAC `abs e < d / M` THEN ASM_SIMP_TAC[REAL_LT_RDIV_EQ];
        SIMP_TAC[]];
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[cmr_fv] THEN MATCH_MP_TAC HAS_REAL_DERIVATIVE_ADD THEN
  REWRITE_TAC[cmr_fvc] THEN CONJ_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[DIMINDEX_2] HMC_FIRST_VARIATION) THEN
  EXISTS_TAC `d:real` THEN EXISTS_TAC `&2` THEN
  ASM_REWRITE_TAC[REAL_LT_01] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  ASM_SIMP_TAC[CMR_SPHERE_CHART_SMOOTH; ORTHOGONAL_MATRIX_ID] THEN
  (CONJ_TAC THENL
    [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
     ASM_SIMP_TAC[SUBSET_UNIV; CMR_SPHERE_CHART_SMOOTH; ORTHOGONAL_MATRIX_ID];
     X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
     ASM_MESON_TAC[CMR_CAPMAP_FACTS; ORTHOGONAL_MATRIX_ID]]));;


(* ========================================================================= *)
(* The first variation is additive in the variation, and it                  *)
(* vanishes for variations supported in a chart disc on which the chart    *)
(* map is cm_harmonic.                                                       *)
(* ========================================================================= *)

let CMR_SMOOTH_BALL_FACTS = prove
 (`!f:real^2->real^K.
     smooth_map_on (:real^2) f
     ==> f measurable_on ball(vec 0,&1) /\
         (?B. !x. x IN ball(vec 0,&1) ==> norm(f x) <= B) /\
         f IN lspace (ball(vec 0,&1)) (&2) /\
         (!i. (\x. partial_derivative i f x) IN lspace (ball(vec 0,&1)) (&2)) /\
         wan_w12 (ball(vec 0,&1)) f`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!g:real^2->real^K. g continuous_on (:real^2)
         ==> (?B. !x. x IN ball(vec 0,&1) ==> norm(g x) <= B) /\
             g IN lspace (ball(vec 0,&1)) (&2)`
  ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `?B. !x:real^2. x IN ball(vec 0,&1) ==> norm((g:real^2->real^K) x) <= B`
    STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN `bounded(IMAGE (g:real^2->real^K) (cball(vec 0,&1)))` MP_TAC THENL
       [MATCH_MP_TAC COMPACT_IMP_BOUNDED THEN MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
        REWRITE_TAC[COMPACT_CBALL] THEN ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_UNIV];
        REWRITE_TAC[bounded; FORALL_IN_IMAGE] THEN MATCH_MP_TAC MONO_EXISTS THEN
        MESON_TAC[SUBSET; BALL_SUBSET_CBALL]];
      ALL_TAC] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC HMC_BOUNDED_LSPACE THEN EXISTS_TAC `B:real` THEN
    ASM_REWRITE_TAC[OPEN_BALL; BOUNDED_BALL] THEN
    ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN `(f:real^2->real^K) continuous_on (:real^2) /\
                !i. (\x. partial_derivative i (f:real^2->real^K) x) continuous_on (:real^2)`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON] THEN GEN_TAC THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN REWRITE_TAC[ETA_AX] THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_PARTIAL_DERIVATIVE; OPEN_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN `(f:real^2->real^K) IN lspace (ball(vec 0,&1)) (&2) /\
                (!i. (\x. partial_derivative i (f:real^2->real^K) x) IN
                     lspace (ball(vec 0,&1)) (&2))`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
    REWRITE_TAC[LEBESGUE_MEASURABLE_BALL] THEN
    ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_UNIV];
    ASM_MESON_TAC[];
    MP_TAC(ISPECL [`(:2)`; `(:K)`] WAN_W12_C1) THEN REWRITE_TAC[WAN_W12_C1_STATEMENT] THEN
    DISCH_THEN(MP_TAC o SPECL [`ball(vec 0:real^2,&1)`; `f:real^2->real^K`]) THEN
    ASM_SIMP_TAC[OPEN_BALL] THEN ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
    MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
    ASM_MESON_TAC[smooth_map_on; SUBSET_UNIV]]);;

let CMR_FVC_TERM_INTEGRABLE = prove
 (`!S (G:real^K->real^K^K) d (v:real^2->real^K) (p:real^2->real^K) i.
     cm_target S G d /\ smooth_map_on (:real^2) v /\ smooth_map_on (:real^2) p /\
     (!x. v x IN S) /\ 1 <= i /\ i <= 2
     ==> (\x. lift(hmc_ld S G v p (\y. partial_derivative i p y) i x))
         integrable_on ball(vec 0,&1)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `v:real^2->real^K` CMR_SMOOTH_BALL_FACTS) THEN
  MP_TAC(ISPEC `p:real^2->real^K` CMR_SMOOTH_BALL_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
    (X_CHOOSE_TAC `M:real`) STRIP_ASSUME_TAC)) THEN STRIP_TAC THEN
  MATCH_MP_TAC HMC_LD_INTEGRABLE THEN
  MAP_EVERY EXISTS_TAC [`d:real`; `M:real`; `{}:real^2->bool`] THEN
  ASM_REWRITE_TAC[OPEN_BALL; NEGLIGIBLE_EMPTY; DIFF_EMPTY; DIMINDEX_2] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
  ASM_REWRITE_TAC[SUBSET_UNIV]);;

let CMR_LD_ADD = prove
 (`!S (G:real^K->real^K^K) d (v:real^2->real^K) h1 h2 (Y1:real^2->real^K) Y2 i x.
     cm_target S G d /\ v x IN S
     ==> hmc_ld S G v (\y. h1 y + h2 y) (\y. Y1 y + Y2 y) i x =
         hmc_ld S G v h1 Y1 i x + hmc_ld S G v h2 Y2 i x`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `v:real^2->real^K`;
                 `\y. (h1:real^2->real^K) y + h2 y`; `h2:real^2->real^K`;
                 `\y. (Y1:real^2->real^K) y + Y2 y`; `Y2:real^2->real^K`; `i:num`; `x:real^2`]
                HMC_LD_SUB) THEN
  ASM_REWRITE_TAC[VECTOR_ARITH `(a + b) - b:real^N = a`; ETA_AX] THEN REAL_ARITH_TAC);;

let CMR_FVC_ADD = prove
 (`!S (G:real^K->real^K^K) d (Q:real^3^3) (u:real^3->real^K) (phi1:real^3->real^K) phi2.
     cm_target S G d /\ orthogonal_matrix Q /\
     smooth_map_on {z:real^3 | ~(z = vec 0)} (wan_rext u) /\
     (!y. y IN sphere(vec 0,&1) ==> u y IN S) /\
     smooth_map_on {z:real^3 | ~(z = vec 0)} (wan_rext phi1) /\
     smooth_map_on {z:real^3 | ~(z = vec 0)} (wan_rext phi2)
     ==> cmr_fvc S G Q u (\y. phi1 y + phi2 y) =
         cmr_fvc S G Q u phi1 + cmr_fvc S G Q u phi2`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[cmr_fvc] THEN
  ABBREV_TAC `v = \x. (u:real^3->real^K)(cm_capmap (Q:real^3^3) x)` THEN
  ABBREV_TAC `p1 = \x. (phi1:real^3->real^K)(cm_capmap (Q:real^3^3) x)` THEN
  ABBREV_TAC `p2 = \x. (phi2:real^3->real^K)(cm_capmap (Q:real^3^3) x)` THEN
  SUBGOAL_THEN `smooth_map_on (:real^2) (v:real^2->real^K) /\
                smooth_map_on (:real^2) (p1:real^2->real^K) /\
                smooth_map_on (:real^2) (p2:real^2->real^K) /\
                (!x. (v:real^2->real^K) x IN S)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["v"; "p1"; "p2"] THEN ASM_SIMP_TAC[CMR_SPHERE_CHART_SMOOTH] THEN
    GEN_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[CMR_CAPMAP_FACTS];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\x. (phi1:real^3->real^K)(cm_capmap (Q:real^3^3) x) +
                     (phi2:real^3->real^K)(cm_capmap Q x)) =
                (\x. (p1:real^2->real^K) x + p2 x)` SUBST1_TAC THENL
   [MAP_EVERY EXPAND_TAC ["p1"; "p2"] THEN REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[real_div; GSYM REAL_ADD_RDISTRIB] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[GSYM SUM_ADD_NUMSEG] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[GSYM DROP_ADD] THEN AP_TERM_TAC THEN
  SUBGOAL_THEN
   `!x. hmc_ld S G (v:real^2->real^K) (\x. p1 x + p2 x)
          (\y. partial_derivative i (\x. (p1:real^2->real^K) x + p2 x) y) i x =
        hmc_ld S G v p1 (\y. partial_derivative i p1 y) i x +
        hmc_ld S G v p2 (\y. partial_derivative i (p2:real^2->real^K) y) i x`
  (fun th -> REWRITE_TAC[th; LIFT_ADD]) THENL
   [X_GEN_TAC `x:real^2` THEN
    SUBGOAL_THEN
     `(\y. partial_derivative i (\x. (p1:real^2->real^K) x + p2 x) y) =
      (\y. partial_derivative i p1 y + partial_derivative i (p2:real^2->real^K) y)`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `y:real^2` THEN
      MATCH_MP_TAC PARTIAL_DERIVATIVE_ADD THEN
      ASM_MESON_TAC[SMOOTH_MAP_ON_DIFFERENTIABLE; OPEN_UNIV; IN_UNIV];
      ALL_TAC] THEN
    MATCH_MP_TAC CMR_LD_ADD THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC INTEGRAL_ADD THEN CONJ_TAC THEN
  MATCH_MP_TAC CMR_FVC_TERM_INTEGRABLE THEN EXISTS_TAC `d:real` THEN
  ASM_REWRITE_TAC[]);;

let CMR_FV_ADD = prove
 (`!S (G:real^K->real^K^K) d (u:real^3->real^K) (phi1:real^3->real^K) phi2.
     cm_target S G d /\
     smooth_map_on {z:real^3 | ~(z = vec 0)} (wan_rext u) /\
     (!y. y IN sphere(vec 0,&1) ==> u y IN S) /\
     smooth_map_on {z:real^3 | ~(z = vec 0)} (wan_rext phi1) /\
     smooth_map_on {z:real^3 | ~(z = vec 0)} (wan_rext phi2)
     ==> cmr_fv S G u (\y. phi1 y + phi2 y) = cmr_fv S G u phi1 + cmr_fv S G u phi2`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[cmr_fv] THEN
  STRIP_ASSUME_TAC CMR_QB_FACTS THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `mat 1:real^3^3`;
                 `u:real^3->real^K`; `phi1:real^3->real^K`; `phi2:real^3->real^K`]
                CMR_FVC_ADD) THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `cmr_qb`;
                 `u:real^3->real^K`; `phi1:real^3->real^K`; `phi2:real^3->real^K`]
                CMR_FVC_ADD) THEN
  ASM_REWRITE_TAC[ORTHOGONAL_MATRIX_ID] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN
  REAL_ARITH_TAC);;

let CMR_FV_LOCAL = prove
 (`!S (G:real^K->real^K^K) d (u:real^3->real^K) (phi:real^3->real^K) (Q:real^3^3) D c r.
     cm_target S G d /\
     smooth_map_on {z:real^3 | ~(z = vec 0)} (wan_rext u) /\
     (!y. y IN sphere(vec 0,&1) ==> u y IN S) /\
     smooth_map_on {z:real^3 | ~(z = vec 0)} (wan_rext phi) /\
     orthogonal_matrix Q /\ cm_harmonic S G D (\x. u(cm_capmap Q x)) /\
     &0 < r /\ cball(c,r) SUBSET D /\
     (!x. ~(x IN cball(c,r / &2)) ==> phi(cm_capmap Q x) = vec 0)
     ==> cmr_fv S G u phi = &0`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HMC_TARGET_BASICS) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `Lam:real` STRIP_ASSUME_TAC o MATCH_MP CMR_TARGET_GCOND) THEN
  MP_TAC(ISPEC `phi:real^3->real^K` CMR_SPHERE_BOUND) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `M:real` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC REAL_DERIVATIVE_UNIQUE_ATREAL THEN
  EXISTS_TAC `\e. cm_sen G (\y. closest_point S ((u:real^3->real^K) y + e % phi y))` THEN
  EXISTS_TAC `&0` THEN CONJ_TAC THENL
   [MATCH_MP_TAC CMR_FV THEN EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_TRANSFORM_ATREAL THEN
  MAP_EVERY EXISTS_TAC
   [`\e. cm_gen G (ball(c,r))
           (\x. closest_point S ((u:real^3->real^K)(cm_capmap Q x) +
                                 e % (phi:real^3->real^K)(cm_capmap Q x))) +
         wan_gdir ((:real^2) DIFF cball(c,r)) G (\x. u(cm_capmap Q x)) / &2`;
    `d / M`] THEN
  ASM_SIMP_TAC[REAL_LT_DIV] THEN CONJ_TAC THENL
   [X_GEN_TAC `e:real` THEN REWRITE_TAC[REAL_SUB_RZERO] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`G:real^K->real^K^K`;
                   `\y. closest_point S ((u:real^3->real^K) y + e % phi y)`;
                   `Q:real^3^3`; `Lam:real`; `c:real^2`; `r:real`] CMR_SEN_SPLIT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `u:real^3->real^K`;
                     `phi:real^3->real^K`; `M:real`; `e:real`] CMR_VARIATION_W12) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
       [UNDISCH_TAC `abs e < d / M` THEN ASM_SIMP_TAC[REAL_LT_RDIV_EQ];
        SIMP_TAC[]];
      DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[cm_gen] THEN BINOP_TAC THENL [REWRITE_TAC[]; ALL_TAC] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC CMT_WAN_GDIR_EQ THEN
    X_GEN_TAC `x:real^2` THEN REWRITE_TAC[IN_DIFF; IN_UNIV] THEN DISCH_TAC THEN
    SUBGOAL_THEN `(phi:real^3->real^K)(cm_capmap Q x) = vec 0` SUBST1_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN UNDISCH_TAC `~((x:real^2) IN cball(c,r))` THEN
      REWRITE_TAC[IN_CBALL] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[VECTOR_MUL_RZERO; VECTOR_ADD_RID] THEN
    SUBGOAL_THEN `(u:real^3->real^K)(cm_capmap Q x) IN S` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `sphere(vec 0:real^3,&1)`)) (concl th) &&
        can (find_term ((=) `S:real^K->bool`)) (concl th))) THEN
      ASM_MESON_TAC[CMR_CAPMAP_FACTS];
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [REAL_ARITH `&0 = &0 + &0`] THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_ADD THEN REWRITE_TAC[HAS_REAL_DERIVATIVE_CONST] THEN
  UNDISCH_TAC `cm_harmonic S G D (\x. (u:real^3->real^K)(cm_capmap Q x))` THEN
  REWRITE_TAC[cm_harmonic] THEN
  DISCH_THEN(MATCH_MP_TAC o CONJUNCT2 o CONJUNCT2) THEN
  ASM_SIMP_TAC[OPEN_BALL; BOUNDED_BALL; CLOSURE_BALL] THEN
  REWRITE_TAC[wan_vtest] THEN ASM_SIMP_TAC[CMR_SPHERE_CHART_SMOOTH] THEN
  EXISTS_TAC `cball(c:real^2,r / &2)` THEN ASM_REWRITE_TAC[COMPACT_CBALL] THEN
  REWRITE_TAC[SUBSET; IN_CBALL; IN_BALL] THEN ASM_REAL_ARITH_TAC);;


(* ========================================================================= *)
(* A smooth partition of unity on S^2 subordinate to discs in                *)
(* the rotated stereographic charts of a finite chart cover.                *)
(* ========================================================================= *)

let cmr_cbump = new_definition
 `cmr_cbump (Q:real^3^3) (c:real^2) r (y:real^3) =
    if y = Q ** basis 3 then &0 else smooth_bump (r / &4) (r / &2) (cmr_chart Q y - c)`;;

let CMR_CBUMP_FACTS = prove
 (`!(Q:real^3^3) c r.
     orthogonal_matrix Q /\ &0 < r
     ==> smooth_map_on {z:real^3 | ~(z = vec 0)} (wan_rext (\y. lift(cmr_cbump Q c r y))) /\
         (!y. &0 <= cmr_cbump Q c r y) /\
         (!x. cmr_cbump Q c r (cm_capmap Q x) = smooth_bump (r / &4) (r / &2) (x - c)) /\
         (!x. x IN cball(c,r / &4) ==> cmr_cbump Q c r (cm_capmap Q x) = &1) /\
         (!x. ~(x IN ball(c,r / &2)) ==> cmr_cbump Q c r (cm_capmap Q x) = &0) /\
         cmr_cbump Q c r (Q ** basis 3) = &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CMR_CAPMAP_FACTS) THEN
  SUBGOAL_THEN `&0 <= r / &4 /\ r / &4 < r / &2` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!x. cmr_cbump Q c r (cm_capmap Q x) = smooth_bump (r / &4) (r / &2) (x - c)`
  ASSUME_TAC THENL [ASM_REWRITE_TAC[cmr_cbump]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ALL_TAC;
    GEN_TAC THEN REWRITE_TAC[cmr_cbump] THEN COND_CASES_TAC THEN
    REWRITE_TAC[REAL_LE_REFL; SMOOTH_BUMP_BOUNDS];
    REWRITE_TAC[IN_CBALL] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_BUMP_1 THEN
    ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[NORM_SUB] THEN ASM_REWRITE_TAC[GSYM dist];
    REWRITE_TAC[IN_BALL] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_BUMP_0 THEN
    ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[NORM_SUB] THEN REWRITE_TAC[GSYM dist] THEN
    ASM_REAL_ARITH_TAC;
    REWRITE_TAC[cmr_cbump]] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN REWRITE_TAC[OPEN_NONZERO; IN_ELIM_THM] THEN
  X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
  ASM_CASES_TAC `inv(norm z) % z:real^3 = (Q:real^3^3) ** basis 3` THENL
   [ALL_TAC;
    EXISTS_TAC `{z:real^3 | ~(z = vec 0) /\ ~(inv(norm z) % z = (Q:real^3^3) ** basis 3)}` THEN
    ASM_REWRITE_TAC[CMR_CHART_SET_OPEN; IN_ELIM_THM] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
    EXISTS_TAC `(\x. lift(smooth_bump (r / &4) (r / &2) x)) o
                (\z. cmr_chart (Q:real^3^3) (inv(norm z) % z) - c)` THEN
    CONJ_TAC THENL
     [X_GEN_TAC `w:real^3` THEN REWRITE_TAC[IN_ELIM_THM; o_THM; wan_rext; cmr_cbump] THEN
      SIMP_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `(:real^2)` THEN
    ASM_SIMP_TAC[CMR_CHART_SET_OPEN; OPEN_UNIV; SUBSET_UNIV; SMOOTH_BUMP_SMOOTH] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN
    ASM_SIMP_TAC[CMR_CHART_SET_OPEN; SMOOTH_MAP_ON_CONST; CMR_CHART_NORMALIZE_SMOOTH]] THEN
  ABBREV_TAC `K = IMAGE (cm_capmap (Q:real^3^3)) (cball(c,r / &2))` THEN
  SUBGOAL_THEN `compact(K:real^3->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "K" THEN MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
    REWRITE_TAC[COMPACT_CBALL] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `(:real^2)` THEN
    SIMP_TAC[SUBSET_UNIV; SMOOTH_MAP_ON_CONTINUOUS_ON; CMR_CAPMAP_SMOOTH];
    ALL_TAC] THEN
  EXISTS_TAC `{w | w IN {z:real^3 | ~(z = vec 0)} /\
                   (\z. inv(norm z) % z) w IN (:real^3) DIFF K}` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN
    ASM_SIMP_TAC[OPEN_NONZERO; GSYM closed; COMPACT_IMP_CLOSED] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN REWRITE_TAC[SMOOTH_MAP_ON_NORMALIZE];
    REWRITE_TAC[IN_ELIM_THM; IN_DIFF; IN_UNIV] THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "K" THEN REWRITE_TAC[IN_IMAGE] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN EXISTS_TAC `\w:real^3. lift(&0)` THEN
  REWRITE_TAC[SMOOTH_MAP_ON_CONST] THEN
  X_GEN_TAC `w:real^3` THEN REWRITE_TAC[IN_ELIM_THM; IN_DIFF; IN_UNIV; wan_rext] THEN
  STRIP_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[cmr_cbump] THEN COND_CASES_TAC THEN
  REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC SMOOTH_BUMP_0 THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(cmr_chart (Q:real^3^3) (inv(norm w) % w) IN cball(c,r / &2))` MP_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `~((inv(norm w) % w:real^3) IN K)` THEN
    REWRITE_TAC[] THEN EXPAND_TAC "K" THEN REWRITE_TAC[IN_IMAGE] THEN
    EXISTS_TAC `cmr_chart (Q:real^3^3) (inv(norm w) % w)` THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_SIMP_TAC[SMT_NORMALIZE_SPHERE];
    REWRITE_TAC[IN_CBALL] THEN ONCE_REWRITE_TAC[DIST_SYM] THEN REWRITE_TAC[dist] THEN
    REAL_ARITH_TAC]);;

let CMR_S2_PARTITION = prove
 (`!n (Q:num->real^3^3) (D:num->real^2->bool).
     (!k. 1 <= k /\ k <= n ==> orthogonal_matrix(Q k) /\ open(D k)) /\
     (!y. y IN sphere(vec 0,&1)
          ==> ?k. 1 <= k /\ k <= n /\ y IN IMAGE (cm_capmap (Q k)) (D k))
     ==> ?m (kk:num->num) (c:num->real^2) (r:num->real) (chi:num->real^3->real).
           (!l. 1 <= l /\ l <= m
                ==> 1 <= kk l /\ kk l <= n /\ &0 < r l /\ cball(c l,r l) SUBSET D(kk l) /\
                    smooth_map_on {z:real^3 | ~(z = vec 0)} (wan_rext (\y. lift(chi l y))) /\
                    (!x. ~(x IN cball(c l,r l / &2)) ==> chi l (cm_capmap (Q(kk l)) x) = &0)) /\
           (!y. y IN sphere(vec 0,&1) ==> sum(1..m) (\l. chi l y) = &1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `?kf (xf:real^3->real^2) rf.
      !y. y IN sphere(vec 0,&1)
          ==> 1 <= kf y /\ kf y <= n /\ y = cm_capmap ((Q:num->real^3^3)(kf y)) (xf y) /\
              &0 < rf y /\ cball(xf y,rf y) SUBSET (D:num->real^2->bool)(kf y)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM SKOLEM_THM; RIGHT_EXISTS_IMP_THM] THEN X_GEN_TAC `y:real^3` THEN
    DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `y:real^3`) THEN ASM_REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `k:num` (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `x:real^2` STRIP_ASSUME_TAC)))) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `k:num`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    UNDISCH_TAC `open((D:num->real^2->bool) k)` THEN REWRITE_TAC[OPEN_CONTAINS_CBALL] THEN
    DISCH_THEN(MP_TAC o SPEC `x:real^2`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
    MAP_EVERY EXISTS_TAC [`k:num`; `x:real^2`; `e:real`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC
   `U = \y:real^3. {w | w IN {z:real^3 | ~(z = vec 0) /\
                                       ~(inv(norm z) % z = (Q:num->real^3^3)(kf y) ** basis 3)} /\
                        (\z. cmr_chart (Q(kf y)) (inv(norm z) % z)) w IN
                        ball((xf:real^3->real^2) y,rf y / &4)}` THEN
  SUBGOAL_THEN
   `!y:real^3. y IN sphere(vec 0,&1) ==> open(U y) /\ y IN U y`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:real^3` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `kf:real^3->num`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `orthogonal_matrix((Q:num->real^3^3)(kf(y:real^3)))` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CMR_CAPMAP_FACTS) THEN
    EXPAND_TAC "U" THEN REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN
      ASM_REWRITE_TAC[CMR_CHART_SET_OPEN; OPEN_BALL] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN ASM_SIMP_TAC[CMR_CHART_NORMALIZE_SMOOTH];
      ALL_TAC] THEN
    SUBGOAL_THEN `inv(norm(y:real^3)) % y = y` ASSUME_TAC THENL
     [UNDISCH_TAC `(y:real^3) IN sphere(vec 0,&1)` THEN
      SIMP_TAC[IN_SPHERE_0; REAL_INV_1; VECTOR_MUL_LID];
      ALL_TAC] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `(y:real^3) IN sphere(vec 0,&1)` THEN
      REWRITE_TAC[IN_SPHERE_0] THEN CONV_TAC NORM_ARITH;
      ASM_MESON_TAC[];
      SUBGOAL_THEN `cmr_chart ((Q:num->real^3^3)(kf(y:real^3))) y = (xf:real^3->real^2) y`
      SUBST1_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[CENTRE_IN_BALL] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPEC `sphere(vec 0:real^3,&1)` COMPACT_IMP_HEINE_BOREL) THEN
  REWRITE_TAC[COMPACT_SPHERE] THEN
  DISCH_THEN(MP_TAC o SPEC `IMAGE (U:real^3->real^3->bool) (sphere(vec 0,&1))`) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[FORALL_IN_IMAGE] THEN REWRITE_TAC[SUBSET; IN_UNIONS; EXISTS_IN_IMAGE] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `f':(real^3->bool)->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`U:real^3->real^3->bool`; `sphere(vec 0:real^3,&1)`;
                 `f':(real^3->bool)->bool`] FINITE_SUBSET_IMAGE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^3->bool` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `FINITE(t:real^3->bool)` THEN REWRITE_TAC[FINITE_INDEX_NUMSEG] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:num->real^3` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `m = CARD(t:real^3->bool)` THEN
  ABBREV_TAC `beta = \l. cmr_cbump ((Q:num->real^3^3)(kf((g:num->real^3) l)))
                                   ((xf:real^3->real^2)(g l)) (rf(g l))` THEN
  SUBGOAL_THEN
   `!l. 1 <= l /\ l <= m
        ==> (g:num->real^3) l IN sphere(vec 0,&1) /\
            orthogonal_matrix((Q:num->real^3^3)(kf(g l))) /\ &0 < rf(g l)`
  ASSUME_TAC THENL
   [X_GEN_TAC `l:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(g:num->real^3) l IN sphere(vec 0,&1)` ASSUME_TAC THENL
     [UNDISCH_TAC `(t:real^3->bool) SUBSET sphere(vec 0,&1)` THEN
      UNDISCH_TAC `(t:real^3->bool) = IMAGE (g:num->real^3) (1..m)` THEN
      DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_NUMSEG] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!l. 1 <= l /\ l <= m
        ==> smooth_map_on {z:real^3 | ~(z = vec 0)}
                          (wan_rext (\y. lift((beta:num->real^3->real) l y))) /\
            (!y. &0 <= beta l y) /\
            (!x. ~(x IN ball((xf:real^3->real^2)(g l),rf((g:num->real^3) l) / &2))
                 ==> beta l (cm_capmap ((Q:num->real^3^3)(kf(g l))) x) = &0)`
  ASSUME_TAC THENL
   [X_GEN_TAC `l:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `l:num`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    EXPAND_TAC "beta" THEN REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`(Q:num->real^3^3)(kf((g:num->real^3) l))`; `(xf:real^3->real^2)((g:num->real^3) l)`;
                   `rf((g:num->real^3) l):real`] CMR_CBUMP_FACTS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN STRIP_TAC THEN
    REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y. y IN sphere(vec 0,&1) ==> &0 < sum(1..m) (\l. (beta:num->real^3->real) l y)`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN MATCH_MP_TAC SUM_POS_LT THEN
    REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `sphere(vec 0:real^3,&1) SUBSET UNIONS f'` THEN
    ASM_REWRITE_TAC[SUBSET; IN_UNIONS; EXISTS_IN_IMAGE] THEN
    DISCH_THEN(MP_TAC o SPEC `y:real^3`) THEN ASM_REWRITE_TAC[IN_NUMSEG] THEN
    DISCH_THEN(X_CHOOSE_THEN `l:num` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `l:num` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `l:num` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "orthogonal_matrix")) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`(Q:num->real^3^3)(kf((g:num->real^3) l))`; `(xf:real^3->real^2)((g:num->real^3) l)`;
                   `rf((g:num->real^3) l):real`] CMR_CBUMP_FACTS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    UNDISCH_TAC `(y:real^3) IN (U:real^3->real^3->bool) ((g:num->real^3) l)` THEN
    EXPAND_TAC "U" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    SUBGOAL_THEN `inv(norm(y:real^3)) % y = y` SUBST1_TAC THENL
     [UNDISCH_TAC `(y:real^3) IN sphere(vec 0,&1)` THEN
      SIMP_TAC[IN_SPHERE_0; REAL_INV_1; VECTOR_MUL_LID];
      ALL_TAC] THEN
    STRIP_TAC THEN EXPAND_TAC "beta" THEN REWRITE_TAC[] THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CMR_CAPMAP_FACTS) THEN
    SUBGOAL_THEN `cm_capmap ((Q:num->real^3^3)(kf((g:num->real^3) l)))
                    (cmr_chart (Q(kf(g l))) y) = y` (fun th -> ONCE_REWRITE_TAC[GSYM th]) THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `cmr_cbump ((Q:num->real^3^3)(kf((g:num->real^3) l))) ((xf:real^3->real^2)(g l))
                    (rf(g l)) (cm_capmap (Q(kf(g l))) (cmr_chart (Q(kf(g l))) y)) = &1`
    (fun th -> REWRITE_TAC[th; REAL_LT_01]) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `cmr_chart ((Q:num->real^3^3)(kf((g:num->real^3) l))) y IN
                 ball((xf:real^3->real^2)(g l),rf(g l) / &4)` THEN
    REWRITE_TAC[IN_BALL; IN_CBALL] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`m:num`; `\l. (kf:real^3->num)((g:num->real^3) l)`; `\l. (xf:real^3->real^2)((g:num->real^3) l)`;
    `\l. (rf:real^3->real)((g:num->real^3) l)`;
    `\l y. (beta:num->real^3->real) l y / sum(1..m) (\j. beta j y)`] THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `l:num` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `l:num` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "orthogonal_matrix")) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `(g:num->real^3) l` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `kf:real^3->num`)) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "cball")) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (K ALL_TAC) STRIP_ASSUME_TAC))) THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [SUBGOAL_THEN
       `wan_rext (\y. lift((beta:num->real^3->real) l y / sum(1..m) (\j. beta j y))) =
        (\z. lift(drop(wan_rext (\y. lift(beta l y)) z) /
                  drop(lift(sum(1..m) (\j. drop(wan_rext (\y. lift(beta j y)) z))))))`
      SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; wan_rext; LIFT_DROP]; ALL_TAC] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_LIFT_DIV THEN REWRITE_TAC[OPEN_NONZERO] THEN
      REPEAT CONJ_TAC THENL
       [REWRITE_TAC[ETA_AX] THEN ASM_MESON_TAC[];
        MATCH_MP_TAC SMOOTH_MAP_ON_LIFT_SUM THEN
        REWRITE_TAC[OPEN_NONZERO; FINITE_NUMSEG; IN_NUMSEG; ETA_AX] THEN ASM_MESON_TAC[];
        REWRITE_TAC[IN_ELIM_THM; LIFT_DROP; wan_rext] THEN X_GEN_TAC `z:real^3` THEN
        DISCH_TAC THEN MATCH_MP_TAC REAL_LT_IMP_NZ THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        ASM_SIMP_TAC[SMT_NORMALIZE_SPHERE]];
      X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(beta:num->real^3->real) l (cm_capmap ((Q:num->real^3^3)(kf((g:num->real^3) l))) x) = &0`
      (fun th -> REWRITE_TAC[th; real_div; REAL_MUL_LZERO]) THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `l:num` o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "wan_rext")) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT2 o CONJUNCT2) THEN
      UNDISCH_TAC `~((x:real^2) IN cball((xf:real^3->real^2)((g:num->real^3) l),rf(g l) / &2))` THEN
      REWRITE_TAC[IN_BALL; IN_CBALL] THEN REAL_ARITH_TAC];
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN REWRITE_TAC[real_div; SUM_RMUL] THEN
    MATCH_MP_TAC REAL_MUL_RINV THEN MATCH_MP_TAC REAL_LT_IMP_NZ THEN ASM_SIMP_TAC[]]);;


(* ========================================================================= *)
(* Spheres that are cm_harmonic in the charts of a finite                    *)
(* chart cover are cm_sharmonic (the lemma shared with pc_cm_compactness).  *)
(* ========================================================================= *)

let CMR_FV_CONG = prove
 (`!S (G:real^K->real^K^K) (u:real^3->real^K) (phi:real^3->real^K) phi'.
     (!y. y IN sphere(vec 0,&1) ==> phi y = phi' y)
     ==> cmr_fv S G u phi = cmr_fv S G u phi'`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[cmr_fv; cmr_fvc] THEN
  SUBGOAL_THEN
   `!Q:real^3^3. orthogonal_matrix Q
                 ==> (\x. (phi:real^3->real^K)(cm_capmap Q x)) = (\x. phi'(cm_capmap Q x))`
  (fun th -> STRIP_ASSUME_TAC CMR_QB_FACTS THEN
             ASM_SIMP_TAC[th; ORTHOGONAL_MATRIX_ID]) THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `x:real^2` THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[CMR_CAPMAP_FACTS]);;

let CMR_FV_ZERO = prove
 (`!S (G:real^K->real^K^K) d (u:real^3->real^K).
     cm_target S G d /\ (!y. y IN sphere(vec 0,&1) ==> u y IN S)
     ==> cmr_fv S G u (\y. vec 0) = &0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[cmr_fv; cmr_fvc; PARTIAL_DERIVATIVE_CONST] THEN
  SUBGOAL_THEN
   `!Q:real^3^3 i x. orthogonal_matrix Q
          ==> hmc_ld S G (\x. (u:real^3->real^K)(cm_capmap Q x)) (\x. vec 0) (\y. vec 0) i x =
              &0`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC HMC_LD_ZERO THEN EXISTS_TAC `d:real` THEN
    ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[CMR_CAPMAP_FACTS];
    ALL_TAC] THEN
  STRIP_ASSUME_TAC CMR_QB_FACTS THEN
  ASM_SIMP_TAC[ORTHOGONAL_MATRIX_ID; LIFT_NUM; INTEGRAL_0; DROP_VEC; SUM_0] THEN
  REAL_ARITH_TAC);;

let CMR_FV_VSUM = prove
 (`!S (G:real^K->real^K^K) d (u:real^3->real^K) (f:num->real^3->real^K) m.
     cm_target S G d /\
     smooth_map_on {z:real^3 | ~(z = vec 0)} (wan_rext u) /\
     (!y. y IN sphere(vec 0,&1) ==> u y IN S) /\
     (!l. 1 <= l /\ l <= m ==> smooth_map_on {z:real^3 | ~(z = vec 0)} (wan_rext (f l)))
     ==> cmr_fv S G u (\y. vsum(1..m) (\l. f l y)) = sum(1..m) (\l. cmr_fv S G u (f l))`,
  REPLICATE_TAC 5 GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[VSUM_CLAUSES_NUMSEG; SUM_CLAUSES_NUMSEG; ARITH] THEN
    MESON_TAC[CMR_FV_ZERO];
    ALL_TAC] THEN
  STRIP_TAC THEN
  REWRITE_TAC[VSUM_CLAUSES_NUMSEG; SUM_CLAUSES_NUMSEG; ARITH_RULE `1 <= SUC m`] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `u:real^3->real^K`;
                 `\y. vsum(1..m) (\l. (f:num->real^3->real^K) l y)`;
                 `(f:num->real^3->real^K)(SUC m)`] CMR_FV_ADD) THEN
  REWRITE_TAC[ETA_AX] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [SUBGOAL_THEN
       `wan_rext (\y. vsum(1..m) (\l. (f:num->real^3->real^K) l y)) =
        (\z. vsum(1..m) (\l. wan_rext (f l) z))`
      SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; wan_rext]; ALL_TAC] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_VSUM_OPEN THEN
      REWRITE_TAC[OPEN_NONZERO; FINITE_NUMSEG; IN_NUMSEG; ETA_AX] THEN
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC];
    DISCH_THEN SUBST1_TAC] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC);;

let CMR_SHARMONIC_FROM_CAPS = prove
 (`!S (G:real^K->real^K^K) d (u:real^3->real^K) n (Q:num->real^3^3) (D:num->real^2->bool).
     cm_target S G d /\
     (!k. 1 <= k /\ k <= n
          ==> orthogonal_matrix(Q k) /\ open(D k) /\
              cm_harmonic S G (D k) (\x. u(cm_capmap (Q k) x))) /\
     (!y. y IN sphere(vec 0,&1)
          ==> ?k. 1 <= k /\ k <= n /\ y IN IMAGE (cm_capmap (Q k)) (D k)) /\
     ~(?c. !y. y IN sphere(vec 0,&1) ==> u y = c)
     ==> cm_sharmonic S G u`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `smooth_map_on {z:real^3 | ~(z = vec 0)} (wan_rext (u:real^3->real^K))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CMR_REXT_FROM_CHARTS THEN
    MAP_EVERY EXISTS_TAC [`n:num`; `Q:num->real^3^3`; `D:num->real^2->bool`] THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `k:num`) THEN ASM_REWRITE_TAC[cm_harmonic] THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y. y IN sphere(vec 0,&1) ==> (u:real^3->real^K) y IN S` ASSUME_TAC THENL
   [X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:real^3` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "IMAGE")) (concl th))) THEN
    ASM_REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `k:num` (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `x:real^2` STRIP_ASSUME_TAC)))) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `k:num`) THEN ASM_REWRITE_TAC[cm_harmonic] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[cm_sharmonic] THEN X_GEN_TAC `phi:real^3->real^K` THEN DISCH_TAC THEN
  SUBGOAL_THEN `cmr_fv S G (u:real^3->real^K) phi = &0` (fun th ->
    MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `u:real^3->real^K`;
                   `phi:real^3->real^K`] CMR_FV) THEN ASM_REWRITE_TAC[th]) THEN
  MP_TAC(ISPECL [`n:num`; `Q:num->real^3^3`; `D:num->real^2->bool`] CMR_S2_PARTITION) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`m:num`; `kk:num->num`; `c:num->real^2`; `r:num->real`;
                       `chi:num->real^3->real`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `cmr_fv S G (u:real^3->real^K) phi =
    cmr_fv S G u (\y. vsum(1..m) (\l. (chi:num->real^3->real) l y % phi y))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC CMR_FV_CONG THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    REWRITE_TAC[VSUM_RMUL] THEN ASM_SIMP_TAC[VECTOR_MUL_LID];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!l. 1 <= l /\ l <= m
        ==> smooth_map_on {z:real^3 | ~(z = vec 0)}
              (wan_rext (\y. (chi:num->real^3->real) l y % (phi:real^3->real^K) y))`
  ASSUME_TAC THENL
   [X_GEN_TAC `l:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `wan_rext (\y. (chi:num->real^3->real) l y % (phi:real^3->real^K) y) =
      (\z. drop(wan_rext (\y. lift(chi l y)) z) % wan_rext phi z)`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; wan_rext; LIFT_DROP]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_MUL_DROP_OPEN THEN REWRITE_TAC[ETA_AX] THEN
    ASM_SIMP_TAC[OPEN_NONZERO];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `u:real^3->real^K`;
                 `\l y. (chi:num->real^3->real) l y % (phi:real^3->real^K) y`; `m:num`]
                CMR_FV_VSUM) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC SUM_EQ_0_NUMSEG THEN X_GEN_TAC `l:num` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `l:num` o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `kk:num->num`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(kk:num->num) l` o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "cm_harmonic")) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC CMR_FV_LOCAL THEN
  MAP_EVERY EXISTS_TAC [`d:real`; `(Q:num->real^3^3)((kk:num->num) l)`;
                        `(D:num->real^2->bool)((kk:num->num) l)`; `(c:num->real^2) l`;
                        `(r:num->real) l`] THEN
  ASM_SIMP_TAC[] THEN
  X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(chi:num->real^3->real) l (cm_capmap ((Q:num->real^3^3)((kk:num->num) l)) x) = &0`
  (fun th -> REWRITE_TAC[th; VECTOR_MUL_LZERO]) THEN
  ASM_SIMP_TAC[]);;

