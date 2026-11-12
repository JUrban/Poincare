(* ========================================================================= *)
(* pc_moi_pd2_loc: the analytic leaves D1-D3 of the 2D smoothing theorem    *)
(* (route M, step M6): MOI_SMO_LIN (linearization at a corner),             *)
(* MOI_SMO_VERTEX2 (vertex smoothing with fading creases) and               *)
(* MOI_SMO_CREASE (crease smoothing along a straight segment).              *)
(* First, the derivative of smooth_step and general calculus helpers.        *)
(* ========================================================================= *)

needs "src/pc_moi_smo_defs.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* The derivative of smooth_step: nonnegative, bounded, zero off (0,1).      *)
(* ------------------------------------------------------------------------- *)

let moi_pdl_dstep = new_definition
 `moi_pdl_dstep (t:real) =
    drop(frechet_derivative (lift o smooth_step o drop) (at (lift t)) (lift(&1)))`;;

let MOI_PDL_DSTEP_DERIV = prove
 (`!t. (smooth_step has_real_derivative moi_pdl_dstep t) (atreal t)`,
  GEN_TAC THEN REWRITE_TAC[HAS_REAL_FRECHET_DERIVATIVE_AT] THEN
  MP_TAC(ISPECL [`(:real^1)`; `lift o smooth_step o drop`]
    SMOOTH_MAP_ON_HAS_DERIVATIVE) THEN
  REWRITE_TAC[OPEN_UNIV; SMOOTH_STEP_SMOOTH; IN_UNIV] THEN
  DISCH_THEN(MP_TAC o SPEC `lift t`) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; moi_pdl_dstep] THEN X_GEN_TAC `h:real^1` THEN
  SUBGOAL_THEN
   `linear(frechet_derivative (lift o smooth_step o drop) (at (lift t)))`
  MP_TAC THENL
   [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `(:real^1)` THEN
    REWRITE_TAC[OPEN_UNIV; SMOOTH_STEP_SMOOTH; IN_UNIV];
    ALL_TAC] THEN
  REWRITE_TAC[LINEAR_1] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[DROP_CMUL; DROP_VEC; LIFT_DROP; REAL_MUL_RID]);;
let MOI_PDL_DSTEP_POS = prove
 (`!t. &0 <= moi_pdl_dstep t`,
  MP_TAC(ISPECL [`smooth_step`; `moi_pdl_dstep`; `(:real)`]
    HAS_REAL_DERIVATIVE_INCREASING) THEN
  REWRITE_TAC[IS_REALINTERVAL_UNIV; WITHINREAL_UNIV; IN_UNIV;
              MOI_PDL_DSTEP_DERIV; SMOOTH_STEP_MONO] THEN
  ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
  REWRITE_TAC[NOT_EXISTS_THM; EXTENSION; IN_UNIV; IN_SING] THEN
  X_GEN_TAC `a:real` THEN DISCH_THEN(MP_TAC o SPEC `a + &1`) THEN
  REAL_ARITH_TAC);;

let MOI_PDL_DSTEP_ZERO = prove
 (`!t. t < &0 \/ &1 < t ==> moi_pdl_dstep t = &0`,
  GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC REAL_DERIVATIVE_UNIQUE_ATREAL THEN
  EXISTS_TAC `smooth_step` THEN EXISTS_TAC `t:real` THEN
  REWRITE_TAC[MOI_PDL_DSTEP_DERIV] THENL
   [MATCH_MP_TAC HAS_REAL_DERIVATIVE_TRANSFORM_ATREAL THEN
    MAP_EVERY EXISTS_TAC [`\x:real. &0`; `--t:real`] THEN
    REWRITE_TAC[HAS_REAL_DERIVATIVE_CONST] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC SMOOTH_STEP_0 THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_TRANSFORM_ATREAL THEN
    MAP_EVERY EXISTS_TAC [`\x:real. &1`; `t - &1`] THEN
    REWRITE_TAC[HAS_REAL_DERIVATIVE_CONST] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC SMOOTH_STEP_1 THEN ASM_REAL_ARITH_TAC]);;

let MOI_PDL_DSTEP_CONTINUOUS = prove
 (`moi_pdl_dstep real_continuous_on (:real)`,
  REWRITE_TAC[REAL_CONTINUOUS_ON] THEN
  SUBGOAL_THEN
   `lift o moi_pdl_dstep o drop =
    (\x. frechet_derivative (lift o smooth_step o drop) (at x) (lift(&1)))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; moi_pdl_dstep; LIFT_DROP]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^1)` THEN
  REWRITE_TAC[SUBSET_UNIV] THEN MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_FRECHET_DERIVATIVE THEN
  REWRITE_TAC[OPEN_UNIV; SMOOTH_STEP_SMOOTH]);;

let MOI_PDL_DSTEP_BOUND = prove
 (`?B. &0 < B /\ !t. moi_pdl_dstep t <= B`,
  MP_TAC(ISPECL [`moi_pdl_dstep`; `real_interval[&0,&1]`]
    REAL_CONTINUOUS_ATTAINS_SUP) THEN
  REWRITE_TAC[REAL_COMPACT_INTERVAL; REAL_INTERVAL_NE_EMPTY] THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real)` THEN
    REWRITE_TAC[SUBSET_UNIV; MOI_PDL_DSTEP_CONTINUOUS];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `x0:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `moi_pdl_dstep x0 + &1` THEN
  ASSUME_TAC(SPEC `x0:real` MOI_PDL_DSTEP_POS) THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `t:real` THEN ASM_CASES_TAC `t IN real_interval[&0,&1]` THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `t:real`) THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    MP_TAC(SPEC `t:real` MOI_PDL_DSTEP_ZERO) THEN
    UNDISCH_TAC `~(t IN real_interval[&0,&1])` THEN
    REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Determinants of linear maps of the plane, in complex notation.            *)
(* ------------------------------------------------------------------------- *)

let MOI_PDL_DET_COLS = prove
 (`!A:real^2->real^2.
     det(matrix A) = A(basis 1)$1 * A(basis 2)$2 - A(basis 2)$1 * A(basis 1)$2`,
  GEN_TAC THEN REWRITE_TAC[DET_2] THEN
  SIMP_TAC[MATRIX_COMPONENT; DIMINDEX_2; ARITH] THEN REAL_ARITH_TAC);;

let MOI_PDL_DET_COMPLEX = prove
 (`!A:complex->complex. det(matrix A) = Im(cnj(A(Cx(&1))) * A ii)`,
  GEN_TAC THEN REWRITE_TAC[MOI_PDL_DET_COLS; COMPLEX_BASIS] THEN
  REWRITE_TAC[GSYM RE_DEF; GSYM IM_DEF; complex_mul; RE; IM; cnj] THEN
  REAL_ARITH_TAC);;

let MOI_PDL_COMPLEX_DECOMP = prove
 (`!z. z = Re z % Cx(&1) + Im z % ii /\ ii * z = Re z % ii - Im z % Cx(&1)`,
  GEN_TAC THEN REWRITE_TAC[COMPLEX_EQ; RE_ADD; IM_ADD; RE_SUB; IM_SUB;
    RE_CMUL; IM_CMUL; RE_CX; IM_CX; RE_II; IM_II; RE_MUL_II; IM_MUL_II] THEN
  REAL_ARITH_TAC);;

let MOI_PDL_DET_ROT = prove
 (`!A:complex->complex z.
     linear A ==> Im(cnj(A z) * A(ii * z)) = norm(z) pow 2 * det(matrix A)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[MOI_PDL_DET_COMPLEX; COMPLEX_SQNORM] THEN
  SUBGOAL_THEN
   `(A:complex->complex) z = Re z % A(Cx(&1)) + Im z % A ii /\
    A(ii * z) = Re z % A ii - Im z % A(Cx(&1))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [GEN_REWRITE_TAC (LAND_CONV o RAND_CONV)
        [CONJUNCT1(SPEC `z:complex` MOI_PDL_COMPLEX_DECOMP)];
      GEN_REWRITE_TAC (LAND_CONV o RAND_CONV)
        [CONJUNCT2(SPEC `z:complex` MOI_PDL_COMPLEX_DECOMP)]] THEN
    ASM_SIMP_TAC[LINEAR_ADD; LINEAR_SUB; LINEAR_CMUL];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[complex_mul; RE; IM; cnj; RE_ADD; IM_ADD; RE_SUB; IM_SUB;
              RE_CMUL; IM_CMUL] THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Holomorphic functions are smooth as maps of the plane; products.          *)
(* ------------------------------------------------------------------------- *)

let MOI_PDL_HOLOMORPHIC_SMOOTH = prove
 (`!f s. open s /\ f holomorphic_on s ==> smooth_map_on s f`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[smooth_map_on] THEN
  SUBGOAL_THEN
   `!n (g:complex->complex). g holomorphic_on s
         ==> continuously_differentiable n s g`
   (fun th -> ASM_MESON_TAC[th]) THEN
  INDUCT_TAC THENL
   [REWRITE_TAC[CONTINUOUSLY_DIFFERENTIABLE_0] THEN
    MESON_TAC[HOLOMORPHIC_ON_IMP_CONTINUOUS_ON];
    ALL_TAC] THEN
  X_GEN_TAC `g:complex->complex` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[CONTINUOUSLY_DIFFERENTIABLE_WITHIN_OPEN] THEN
  EXISTS_TAC `\x:complex h:complex. complex_derivative g x * h` THEN
  CONJ_TAC THENL
   [X_GEN_TAC `x:complex` THEN DISCH_TAC THEN
    REWRITE_TAC[GSYM has_complex_derivative] THEN
    REWRITE_TAC[HAS_COMPLEX_DERIVATIVE_DIFFERENTIABLE] THEN
    ASM_MESON_TAC[HOLOMORPHIC_ON_IMP_DIFFERENTIABLE_AT];
    X_GEN_TAC `h:complex` THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC HOLOMORPHIC_ON_MUL THEN
    ASM_SIMP_TAC[ETA_AX; HOLOMORPHIC_COMPLEX_DERIVATIVE; HOLOMORPHIC_ON_CONST]]);;

let MOI_PDL_SMOOTH_CMUL_FUN = prove
 (`!s (f:real^N->complex) g.
     open s /\ smooth_map_on s f /\ smooth_map_on s g
     ==> smooth_map_on s (\x. f x * g x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `complex_mul`;
                 `f:real^N->complex`; `g:real^N->complex`]
    SMOOTH_MAP_ON_BILINEAR_OPEN) THEN
  ASM_REWRITE_TAC[BILINEAR_COMPLEX_MUL]);;

(* Twin of SMT_SMOOTH_CEXP in pc_smt_rn.ml; kept here to avoid loading pc_smt_rn.ml. *)

let MOI_PDL_SMOOTH_CEXP = prove
 (`!s (f:real^N->complex).
     open s /\ smooth_map_on s f ==> smooth_map_on s (\x. cexp(f x))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\x:real^N. cexp(f x)) = cexp o f` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `(:complex)` THEN
  ASM_REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV] THEN
  MATCH_MP_TAC MOI_PDL_HOLOMORPHIC_SMOOTH THEN
  REWRITE_TAC[OPEN_UNIV; HOLOMORPHIC_ON_CEXP]);;

let MOI_PDL_SMOOTH_CX_DROP = prove
 (`!s (f:real^N->real^1).
     open s /\ smooth_map_on s f ==> smooth_map_on s (\x. Cx(drop(f x)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\x:real^N. Cx(drop(f x))) = (Cx o drop) o f` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_LINEAR_O THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[linear; o_THM; DROP_ADD; DROP_CMUL; CX_ADD; CX_MUL;
              COMPLEX_CMUL]);;

(* ========================================================================= *)
(* A smooth ramp in a logarithmic scale (zero up to p,                       *)
(* the identity from p exp q on, slope in [0, 1 + B / q]).                  *)
(* ========================================================================= *)

let moi_pdl_ramp = new_definition
 `moi_pdl_ramp (p:real) (q:real) (s:real) =
    if s <= &0 then &0 else s * smooth_step(log(s / p) / q)`;;

let moi_pdl_dramp = new_definition
 `moi_pdl_dramp (p:real) (q:real) (s:real) =
    if s <= &0 then &0
    else smooth_step(log(s / p) / q) + moi_pdl_dstep(log(s / p) / q) / q`;;

let MOI_PDL_LOG_DIV_LE_0 = prove
 (`!p s. &0 < p /\ &0 < s /\ s <= p ==> log(s / p) <= &0`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[LOG_DIV] THEN
  MATCH_MP_TAC(REAL_ARITH `x <= y ==> x - y <= &0`) THEN
  MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REWRITE_TAC[]);;

let MOI_PDL_RAMP_SMALL = prove
 (`!p q s. &0 < p /\ &0 < q /\ s <= p ==> moi_pdl_ramp p q s = &0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[moi_pdl_ramp] THEN
  COND_CASES_TAC THEN REWRITE_TAC[REAL_ENTIRE] THEN DISJ2_TAC THEN
  MATCH_MP_TAC SMOOTH_STEP_0 THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= --x ==> x <= &0`) THEN
  REWRITE_TAC[real_div; GSYM REAL_MUL_LNEG] THEN
  MATCH_MP_TAC REAL_LE_MUL THEN
  ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE; GSYM real_div] THEN
  MATCH_MP_TAC(REAL_ARITH `x <= &0 ==> &0 <= --x`) THEN
  MATCH_MP_TAC MOI_PDL_LOG_DIV_LE_0 THEN ASM_REAL_ARITH_TAC);;

let MOI_PDL_DRAMP_SMALL = prove
 (`!p q s. &0 < p /\ &0 < q /\ s < p ==> moi_pdl_dramp p q s = &0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[moi_pdl_dramp] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `log(s / p) / q < &0` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_MUL_LZERO] THEN
    ASM_SIMP_TAC[LOG_DIV; REAL_ARITH `~(s <= &0) ==> &0 < s`] THEN
    MATCH_MP_TAC(REAL_ARITH `x < y ==> x - y < &0`) THEN
    MATCH_MP_TAC LOG_MONO_LT_IMP THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[SMOOTH_STEP_0; REAL_LT_IMP_LE; MOI_PDL_DSTEP_ZERO] THEN
  REAL_ARITH_TAC);;

let MOI_PDL_RAMP_LARGE = prove
 (`!p q s. &0 < p /\ &0 < q /\ p * exp q <= s ==> moi_pdl_ramp p q s = s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[moi_pdl_ramp] THEN
  SUBGOAL_THEN `&0 < s` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `p * exp q` THEN
    ASM_SIMP_TAC[REAL_LT_MUL; REAL_EXP_POS_LT];
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < s ==> ~(s <= &0)`] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN AP_TERM_TAC THEN
  MATCH_MP_TAC SMOOTH_STEP_1 THEN ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
  REWRITE_TAC[REAL_MUL_LID] THEN
  SUBGOAL_THEN `q = log(exp q)` SUBST1_TAC THENL
   [REWRITE_TAC[LOG_EXP]; ALL_TAC] THEN
  MATCH_MP_TAC LOG_MONO_LE_IMP THEN REWRITE_TAC[REAL_EXP_POS_LT] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN ASM_REAL_ARITH_TAC);;

let MOI_PDL_RAMP_BOUNDS = prove
 (`!p q s. &0 <= moi_pdl_ramp p q s /\
           (&0 <= s ==> moi_pdl_ramp p q s <= s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_pdl_ramp] THEN COND_CASES_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPEC `log(s / p) / q` SMOOTH_STEP_BOUNDS) THEN STRIP_TAC THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    DISCH_TAC THEN GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC]);;

let MOI_PDL_DRAMP_BOUNDS = prove
 (`!p q s B. &0 < q /\ (!t. moi_pdl_dstep t <= B)
             ==> &0 <= moi_pdl_dramp p q s /\
                 moi_pdl_dramp p q s <= &1 + B / q`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[moi_pdl_dramp] THEN
  SUBGOAL_THEN `&0 <= B` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `moi_pdl_dstep(&0)` THEN
    ASM_REWRITE_TAC[MOI_PDL_DSTEP_POS];
    ALL_TAC] THEN
  COND_CASES_TAC THENL
   [CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 <= &1 + x`) THEN
    MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPEC `log(s / p) / q` SMOOTH_STEP_BOUNDS) THEN
  MP_TAC(SPEC `log(s / p) / q` MOI_PDL_DSTEP_POS) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `log(s / p) / q`) THEN
  REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC REAL_LE_ADD THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_ADD2 THEN ASM_SIMP_TAC[REAL_LE_DIV2_EQ]]);;

add_real_differentiation_theorems
  (CONJUNCTS(REWRITE_RULE[FORALL_AND_THM]
    (MATCH_MP HAS_REAL_DERIVATIVE_CHAIN_UNIV MOI_PDL_DSTEP_DERIV)));;

let MOI_PDL_RAMP_DERIV = prove
 (`!p q s. &0 < p /\ &0 < q
           ==> (moi_pdl_ramp p q has_real_derivative moi_pdl_dramp p q s)
               (atreal s)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `s < p` THENL
   [ASM_SIMP_TAC[MOI_PDL_DRAMP_SMALL] THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_TRANSFORM_ATREAL THEN
    MAP_EVERY EXISTS_TAC [`\x:real. &0`; `p - s:real`] THEN
    REWRITE_TAC[HAS_REAL_DERIVATIVE_CONST] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC MOI_PDL_RAMP_SMALL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < s` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_TRANSFORM_ATREAL THEN
  MAP_EVERY EXISTS_TAC [`\x:real. x * smooth_step(log(x / p) / q)`; `s:real`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[moi_pdl_ramp] THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[moi_pdl_dramp] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < s ==> ~(s <= &0)`] THEN
  REAL_DIFF_TAC THEN ASM_SIMP_TAC[REAL_LT_DIV] THEN
  UNDISCH_TAC `&0 < s` THEN UNDISCH_TAC `&0 < p` THEN UNDISCH_TAC `&0 < q` THEN
  CONV_TAC REAL_FIELD);;

let MOI_PDL_RAMP_SMOOTH_POS = prove
 (`!p q. &0 < p /\ &0 < q
         ==> smooth_map_on {y:real^1 | &0 < drop y}
               (\y. lift(drop y * smooth_step(log(drop y / p) / q)))`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `t = {y:real^1 | &0 < drop y}` THEN
  SUBGOAL_THEN `open(t:real^1->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "t" THEN REWRITE_TAC[OPEN_DROP_POSITIVE]; ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on t (\y:real^1. lift(inv p * drop y))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`t:real^1->bool`; `inv p`; `\y:real^1. y`]
      SMOOTH_MAP_ON_LIFT_CMUL) THEN
    ASM_REWRITE_TAC[SMOOTH_MAP_ON_ID];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on t (\y:real^1. lift(log(inv p * drop y)))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`t:real^1->bool`; `\y:real^1. lift(inv p * drop y)`]
      SMOOTH_MAP_ON_LIFT_LOG) THEN
    ASM_REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN
    EXPAND_TAC "t" THEN REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[REAL_LT_INV_EQ];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on t (\y:real^1. lift(inv q * log(inv p * drop y)))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`t:real^1->bool`; `inv q`;
                   `\y:real^1. lift(log(inv p * drop y))`]
      SMOOTH_MAP_ON_LIFT_CMUL) THEN
    ASM_REWRITE_TAC[LIFT_DROP];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on t
      (\y:real^1. lift(smooth_step(inv q * log(inv p * drop y))))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`t:real^1->bool`;
                   `\y:real^1. lift(inv q * log(inv p * drop y))`]
      SMOOTH_MAP_ON_SMOOTH_STEP_COMPOSE) THEN
    ASM_REWRITE_TAC[LIFT_DROP];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:real^1->bool`; `\y:real^1. y`;
                 `\y:real^1. lift(smooth_step(inv q * log(inv p * drop y)))`]
    SMOOTH_MAP_ON_LIFT_MUL) THEN
  ASM_REWRITE_TAC[SMOOTH_MAP_ON_ID; LIFT_DROP] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
  GEN_TAC THEN REWRITE_TAC[real_div] THEN REWRITE_TAC[REAL_MUL_AC]);;

let MOI_PDL_RAMP_SMOOTH = prove
 (`!p q. &0 < p /\ &0 < q
         ==> smooth_map_on (:real^1) (lift o moi_pdl_ramp p q o drop)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[smooth_map_on] THEN GEN_TAC THEN
  SIMP_TAC[CONTINUOUSLY_DIFFERENTIABLE_LOCAL_OPEN; OPEN_UNIV; IN_UNIV;
           SUBSET_UNIV] THEN
  X_GEN_TAC `x:real^1` THEN ASM_CASES_TAC `drop x < p` THENL
   [EXISTS_TAC `{y:real^1 | drop y < p}` THEN
    REWRITE_TAC[drop; OPEN_HALFSPACE_COMPONENT_LT; IN_ELIM_THM] THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[GSYM drop]; ALL_TAC] THEN
    SUBGOAL_THEN
     `smooth_map_on {y:real^1 | y$1 < p} (lift o moi_pdl_ramp p q o drop)`
     (fun th -> MESON_TAC[th; smooth_map_on]) THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN
    EXISTS_TAC `\y:real^1. vec 0:real^1` THEN
    REWRITE_TAC[OPEN_HALFSPACE_COMPONENT_LT; SMOOTH_MAP_ON_CONST] THEN
    REWRITE_TAC[IN_ELIM_THM; o_THM; GSYM drop] THEN REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[MOI_PDL_RAMP_SMALL; REAL_LT_IMP_LE; LIFT_NUM];
    ALL_TAC] THEN
  EXISTS_TAC `{y:real^1 | &0 < drop y}` THEN
  REWRITE_TAC[OPEN_DROP_POSITIVE; IN_ELIM_THM] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on {y:real^1 | &0 < drop y} (lift o moi_pdl_ramp p q o drop)`
   (fun th -> MESON_TAC[th; smooth_map_on]) THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN
  EXISTS_TAC `\y:real^1. lift(drop y * smooth_step(log(drop y / p) / q))` THEN
  ASM_SIMP_TAC[OPEN_DROP_POSITIVE; MOI_PDL_RAMP_SMOOTH_POS] THEN
  REWRITE_TAC[IN_ELIM_THM; o_THM; moi_pdl_ramp] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> ~(x <= &0)`]);;

(* ------------------------------------------------------------------------- *)
(* The fold theta(x) = (x$1, ramp(x$2)).                                     *)
(* ------------------------------------------------------------------------- *)

let moi_pdl_fold = new_definition
 `moi_pdl_fold (p:real) (q:real) (x:real^2) =
    vector[x$1; moi_pdl_ramp p q (x$2)]:real^2`;;

let MOI_PDL_RAMP_LIFT_DERIV = prove
 (`!p q (x:real^2). &0 < p /\ &0 < q
       ==> ((\x:real^2. lift(moi_pdl_ramp p q (x$2))) has_derivative
            (\h. lift(moi_pdl_dramp p q (x$2) * h$2))) (at x)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `(\x:real^2. lift(moi_pdl_ramp p q (x$2))) =
    (lift o moi_pdl_ramp p q o drop) o (\x:real^2. lift(x$2))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_DROP]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(\h:real^2. lift(moi_pdl_dramp p q ((x:real^2)$2) * h$2)) =
    (\h:real^1. moi_pdl_dramp p q ((x:real^2)$2) % h) o (\h:real^2. lift(h$2))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_CMUL]; ALL_TAC] THEN
  MATCH_MP_TAC DIFF_CHAIN_AT THEN
  SIMP_TAC[HAS_DERIVATIVE_LINEAR; LINEAR_LIFT_COMPONENT] THEN
  MP_TAC(ISPECL [`p:real`; `q:real`; `(x:real^2)$2`] MOI_PDL_RAMP_DERIV) THEN
  ASM_REWRITE_TAC[HAS_REAL_FRECHET_DERIVATIVE_AT]);;

let MOI_PDL_FOLD_DERIV = prove
 (`!p q (x:real^2). &0 < p /\ &0 < q
       ==> (moi_pdl_fold p q has_derivative
            (\h. vector[h$1; moi_pdl_dramp p q (x$2) * h$2]:real^2)) (at x)`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[HAS_DERIVATIVE_COMPONENTWISE_AT] THEN
  REWRITE_TAC[DIMINDEX_2; ARITH_RULE `1 <= i /\ i <= 2 <=> i = 1 \/ i = 2`] THEN
  GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[moi_pdl_fold; VECTOR_2] THENL
   [MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN REWRITE_TAC[LINEAR_LIFT_COMPONENT];
    ASM_SIMP_TAC[MOI_PDL_RAMP_LIFT_DERIV]]);;

let MOI_PDL_FOLD_SMOOTH = prove
 (`!p q. &0 < p /\ &0 < q ==> smooth_map_on (:real^2) (moi_pdl_fold p q)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`(:real^2)`; `moi_pdl_fold p q`]
    SMOOTH_MAP_ON_COMPONENTWISE) THEN
  REWRITE_TAC[OPEN_UNIV] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[DIMINDEX_2; ARITH_RULE `1 <= i /\ i <= 2 <=> i = 1 \/ i = 2`] THEN
  GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[moi_pdl_fold; VECTOR_2] THENL
   [SIMP_TAC[SMOOTH_MAP_ON_LIFT_COORDINATE; OPEN_UNIV]; ALL_TAC] THEN
  MP_TAC(ISPECL [`(:real^2)`; `(:real^1)`; `\x:real^2. lift(x$2)`;
                 `moi_pdl_ramp p q`] SMOOTH_MAP_ON_LIFT_COMPOSE_1D) THEN
  ASM_SIMP_TAC[OPEN_UNIV; IN_UNIV; SMOOTH_MAP_ON_LIFT_COORDINATE;
               MOI_PDL_RAMP_SMOOTH; LIFT_DROP]);;

(* ------------------------------------------------------------------------- *)
(* Elementary estimates for 2 x 2 determinants written by columns, and the  *)
(* vanishing of a derivative along a line on which the map vanishes.        *)
(* ------------------------------------------------------------------------- *)

let MOI_PDL_CR_BOUND = prove
 (`!u:real^2 v:real^2. abs(u$1 * v$2 - v$1 * u$2) <= &2 * norm u * norm v`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`u:real^2`; `1`] COMPONENT_LE_NORM) THEN
  MP_TAC(ISPECL [`u:real^2`; `2`] COMPONENT_LE_NORM) THEN
  MP_TAC(ISPECL [`v:real^2`; `1`] COMPONENT_LE_NORM) THEN
  MP_TAC(ISPECL [`v:real^2`; `2`] COMPONENT_LE_NORM) THEN
  REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `abs((u:real^2)$1 * (v:real^2)$2) <= norm u * norm v /\
                abs(v$1 * u$2) <= norm u * norm v`
  MP_TAC THENL
   [REWRITE_TAC[REAL_ABS_MUL] THEN CONJ_TAC THENL
     [ALL_TAC; GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM]] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_ABS_POS];
    REAL_ARITH_TAC]);;

let MOI_PDL_CR_PERTURB = prove
 (`!u:real^2 v:real^2 u0:real^2 v0:real^2.
     abs((u$1 * v$2 - v$1 * u$2) - (u0$1 * v0$2 - v0$1 * u0$2))
     <= &2 * norm(u - u0) * norm v + &2 * norm u0 * norm(v - v0)`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`u - u0:real^2`; `v:real^2`] MOI_PDL_CR_BOUND) THEN
  MP_TAC(ISPECL [`u0:real^2`; `v - v0:real^2`] MOI_PDL_CR_BOUND) THEN
  REWRITE_TAC[VECTOR_SUB_COMPONENT] THEN REAL_ARITH_TAC);;

let MOI_PDL_DERIV_ZERO_LINE = prove
 (`!(f:real^M->real^N) f' x v d.
     (f has_derivative f') (at x) /\ &0 < d /\
     (!t. abs t < d ==> f(x + t % v) = vec 0)
     ==> f' v = vec 0`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `((\t:real^1. (f:real^M->real^N)(x + drop t % v)) has_derivative
     (\t. (f':real^M->real^N)(drop t % v))) (at (vec 0))`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `(\t:real^1. (f:real^M->real^N)(x + drop t % v)) =
      f o (\t. x + drop t % v)`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    SUBGOAL_THEN
     `(\t:real^1. (f':real^M->real^N)(drop t % v)) = f' o (\t. drop t % v)`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC DIFF_CHAIN_AT THEN
    REWRITE_TAC[HAS_DERIVATIVE_LINE_PARAM; DROP_VEC; VECTOR_MUL_LZERO;
                VECTOR_ADD_RID] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\t:real^1. (f:real^M->real^N)(x + drop t % v)) has_derivative
     (\t. vec 0)) (at (vec 0))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_AT THEN
    MAP_EVERY EXISTS_TAC [`\t:real^1. vec 0:real^N`; `d:real`] THEN
    ASM_REWRITE_TAC[HAS_DERIVATIVE_CONST] THEN
    REWRITE_TAC[DIST_0; NORM_REAL; GSYM drop] THEN REPEAT STRIP_TAC THEN
    CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP FRECHET_DERIVATIVE_UNIQUE_AT o
    CONJ (ASSUME `((\t:real^1. (f:real^M->real^N)(x + drop t % v)) has_derivative
     (\t. (f':real^M->real^N)(drop t % v))) (at (vec 0))`)) THEN
  DISCH_THEN(MP_TAC o C AP_THM `lift(&1)`) THEN
  REWRITE_TAC[LIFT_DROP; VECTOR_MUL_LID]);;

(* ========================================================================= *)
(* Uniform estimates for derivatives on compact sets.                       *)
(* ========================================================================= *)

let MOI_PDL_PARTIAL_UNIF = prove
 (`!(f:real^M->real^N) u k v.
     open u /\ compact k /\ k SUBSET u /\ smooth_map_on u f
     ==> (?B. &0 < B /\
              !x. x IN k ==> norm(frechet_derivative f (at x) v) <= B) /\
         (!w. &0 < w
              ==> ?d. &0 < d /\
                      !x y. x IN k /\ y IN k /\ norm(x - y) < d
                            ==> norm(frechet_derivative f (at x) v -
                                     frechet_derivative f (at y) v) < w)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(\x. frechet_derivative (f:real^M->real^N) (at x) v) continuous_on k`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `u:real^M->bool` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_FRECHET_DERIVATIVE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`\x. frechet_derivative (f:real^M->real^N) (at x) v`;
                   `k:real^M->bool`] COMPACT_CONTINUOUS_IMAGE) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
    REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE];
    MP_TAC(ISPECL [`\x. frechet_derivative (f:real^M->real^N) (at x) v`;
                   `k:real^M->bool`] COMPACT_UNIFORMLY_CONTINUOUS) THEN
    ASM_REWRITE_TAC[uniformly_continuous_on; dist] THEN
    MESON_TAC[]]);;

let MOI_PDL_SMOOTH_RMUL = prove
 (`!s (f:real^M->real) g.
     open s /\ smooth_map_on s (\x. lift(f x)) /\ smooth_map_on s (\x. lift(g x))
     ==> smooth_map_on s (\x. lift(f x * g x))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^M->bool`; `\x:real^M. lift(f x)`;
                 `\x:real^M. lift(g x)`] SMOOTH_MAP_ON_LIFT_MUL) THEN
  ASM_REWRITE_TAC[LIFT_DROP]);;

let MOI_PDL_SMOOTH_RSUB = prove
 (`!s (f:real^M->real) g.
     open s /\ smooth_map_on s (\x. lift(f x)) /\ smooth_map_on s (\x. lift(g x))
     ==> smooth_map_on s (\x. lift(f x - g x))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^M->bool`; `\x:real^M. lift(f x)`;
                 `\x:real^M. lift(g x)`] SMOOTH_MAP_ON_LIFT_SUB) THEN
  ASM_REWRITE_TAC[LIFT_DROP]);;

let MOI_PDL_SMOOTH_RADD = prove
 (`!s (f:real^M->real) g.
     open s /\ smooth_map_on s (\x. lift(f x)) /\ smooth_map_on s (\x. lift(g x))
     ==> smooth_map_on s (\x. lift(f x + g x))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^M->bool`; `\x:real^M. lift(f x)`;
                 `\x:real^M. lift(g x)`] SMOOTH_MAP_ON_LIFT_ADD) THEN
  ASM_REWRITE_TAC[LIFT_DROP]);;

let MOI_PDL_SMOOTH_DET_JAC = prove
 (`!(f:real^2->real^2) s.
     open s /\ smooth_map_on s f
     ==> smooth_map_on s (\x. lift(det(jacobian f (at x))))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[jacobian; MOI_PDL_DET_COLS] THEN
  SUBGOAL_THEN
   `!i j. smooth_map_on s
            (\x. lift((frechet_derivative (f:real^2->real^2) (at x)
                       (basis j:real^2))$i))`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN
    MP_TAC(ISPECL [`s:real^2->bool`;
                   `\x. frechet_derivative (f:real^2->real^2) (at x)
                          (basis j:real^2)`; `i:num`]
      SMOOTH_MAP_ON_LIFT_COMPONENT) THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_FRECHET_DERIVATIVE];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_PDL_SMOOTH_RSUB THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THEN MATCH_MP_TAC MOI_PDL_SMOOTH_RMUL THEN ASM_REWRITE_TAC[]);;

let MOI_PDL_DET_LOWER = prove
 (`!(f:real^2->real^2) u k.
     open u /\ compact k /\ k SUBSET u /\ smooth_map_on u f /\
     (!x. x IN k ==> &0 < det(jacobian f (at x)))
     ==> ?m. &0 < m /\ !x. x IN k ==> m <= det(jacobian f (at x))`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `k:real^2->bool = {}` THENL
   [EXISTS_TAC `&1` THEN ASM_REWRITE_TAC[NOT_IN_EMPTY; REAL_LT_01];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\x. det(jacobian (f:real^2->real^2) (at x))`;
                 `k:real^2->bool`] CONTINUOUS_ATTAINS_INF) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[o_DEF] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `u:real^2->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
    ASM_SIMP_TAC[MOI_PDL_SMOOTH_DET_JAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `x0:real^2` (STRIP_ASSUME_TAC o BETA_RULE)) THEN
  EXISTS_TAC `det(jacobian (f:real^2->real^2) (at x0))` THEN
  ASM_SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The arithmetic of the crease estimate: perturbing the columns u0 and a   *)
(* combination v0m + lam (v0p - v0m), lam in [0, 1 + eta], keeps the 2 x 2   *)
(* determinant positive.                                                    *)
(* ------------------------------------------------------------------------- *)

let MOI_PDL_CREASE_ALG = prove
 (`!u:real^2 v:real^2 u0:real^2 v0m:real^2 v0p:real^2 lam bM m w eta.
     &1 <= bM /\ norm u0 <= bM /\ norm v0m <= bM /\ norm v0p <= bM /\
     &0 <= w /\ w <= &1 /\ &0 <= eta /\ eta <= &1 /\
     &0 <= lam /\ lam <= &1 + eta /\
     norm(u - u0) <= &3 * w /\
     norm(v - (v0m + lam % (v0p - v0m))) <= &5 * w /\
     m <= u0$1 * v0m$2 - v0m$1 * u0$2 /\
     m <= u0$1 * v0p$2 - v0p$1 * u0$2 /\
     &16 * bM pow 2 * eta <= m /\ &280 * bM * w <= m /\ &0 < m
     ==> &0 < u$1 * v$2 - v$1 * u$2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `w0:real^2 = v0m + lam % (v0p - v0m)` THEN
  ABBREV_TAC `cm = u0$1 * (v0m:real^2)$2 - v0m$1 * (u0:real^2)$2` THEN
  ABBREV_TAC `cp = u0$1 * (v0p:real^2)$2 - v0p$1 * (u0:real^2)$2` THEN
  SUBGOAL_THEN
   `u0$1 * (w0:real^2)$2 - w0$1 * (u0:real^2)$2 = (&1 - lam) * cm + lam * cp`
  ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["w0"; "cm"; "cp"] THEN
    REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
                VECTOR_SUB_COMPONENT] THEN CONV_TAC REAL_RING;
    ALL_TAC] THEN
  SUBGOAL_THEN `abs cm <= &2 * bM pow 2 /\ abs cp <= &2 * bM pow 2`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["cm"; "cp"] THEN CONJ_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THENL
     [EXISTS_TAC `&2 * norm(u0:real^2) * norm(v0m:real^2)`;
      EXISTS_TAC `&2 * norm(u0:real^2) * norm(v0p:real^2)`] THEN
    REWRITE_TAC[MOI_PDL_CR_BOUND; REAL_POW_2] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[NORM_POS_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `&3 * m / &4 <= (&1 - lam) * cm + lam * cp` ASSUME_TAC THENL
   [ASM_CASES_TAC `lam <= &1` THENL
     [SUBGOAL_THEN `(&1 - lam) * m <= (&1 - lam) * cm /\ lam * m <= lam * cp`
      MP_TAC THENL
       [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC];
      SUBGOAL_THEN `abs((lam - &1) * (cp - cm)) <= eta * (&4 * bM pow 2)`
      MP_TAC THENL
       [REWRITE_TAC[REAL_ABS_MUL] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
        REWRITE_TAC[REAL_ABS_POS] THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `(&1 - lam) * cm + lam * cp = cp + (lam - &1) * (cp - cm)`
      SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      UNDISCH_TAC `&16 * bM pow 2 * eta <= m` THEN
      UNDISCH_TAC `m <= cp` THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `norm(w0:real^2) <= &5 * bM` ASSUME_TAC THENL
   [EXPAND_TAC "w0" THEN
    MATCH_MP_TAC(NORM_ARITH
     `norm(a:real^2) <= bM /\ norm(c:real^2) <= &4 * bM
      ==> norm(a + c) <= &5 * bM`) THEN
    ASM_REWRITE_TAC[NORM_MUL] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&2 * (&2 * bM)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_ABS_POS; NORM_POS_LE] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC(NORM_ARITH
       `norm(a:real^2) <= bM /\ norm(b:real^2) <= bM
        ==> norm(b - a) <= &2 * bM`) THEN ASM_REWRITE_TAC[];
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `norm(v:real^2) <= &10 * bM` ASSUME_TAC THENL
   [UNDISCH_TAC `norm(v - w0:real^2) <= &5 * w` THEN
    UNDISCH_TAC `norm(w0:real^2) <= &5 * bM` THEN
    UNDISCH_TAC `w <= &1` THEN UNDISCH_TAC `&1 <= bM` THEN NORM_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`u:real^2`; `v:real^2`; `u0:real^2`; `w0:real^2`]
    MOI_PDL_CR_PERTURB) THEN
  SUBGOAL_THEN
   `norm(u - u0:real^2) * norm(v:real^2) <= (&3 * w) * (&10 * bM) /\
    norm(u0:real^2) * norm(v - w0:real^2) <= bM * (&5 * w)`
  MP_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
    ASM_REWRITE_TAC[NORM_POS_LE] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `&3 * m / &4 <= (&1 - lam) * cm + lam * cp` THEN
  UNDISCH_TAC `&280 * bM * w <= m` THEN UNDISCH_TAC `&0 < m` THEN
  REAL_ARITH_TAC);;

let MOI_PDL_CREASE_DET = prove
 (`!(Fp:real^2->real^2) Fm u k a b d (x:real^2) r lam d0 bM m w eta.
     open u /\ k SUBSET u /\ smooth_map_on u Fp /\ smooth_map_on u Fm /\
     (!z:real^2. z IN k <=> a <= z$1 /\ z$1 <= b /\ abs(z$2) <= d) /\
     (!t. a <= t /\ t <= b ==> Fp(vector[t; &0]) = Fm(vector[t; &0])) /\
     a < x$1 /\ x$1 < b /\ &0 <= x$2 /\ x$2 < d0 /\ x$2 <= d /\
     &0 <= r /\ r <= x$2 /\
     &1 <= bM /\ &0 <= w /\ w <= &1 /\ &0 <= eta /\ eta <= &1 /\
     &0 <= lam /\ lam <= &1 + eta /\
     &16 * bM pow 2 * eta <= m /\ &280 * bM * w <= m /\ &0 < m
     ==> (!y z j. y IN k /\ z IN k /\ norm(y - z) < d0 /\ (j = 1 \/ j = 2)
                  ==> norm(frechet_derivative Fp (at y) (basis j) -
                           frechet_derivative Fp (at z) (basis j)) <= w /\
                      norm(frechet_derivative Fm (at y) (basis j) -
                           frechet_derivative Fm (at z) (basis j)) <= w)
     ==> (!y j. y IN k /\ (j = 1 \/ j = 2)
                ==> norm(frechet_derivative Fp (at y) (basis j)) <= bM /\
                    norm(frechet_derivative Fm (at y) (basis j)) <= bM)
     ==> (!y. y IN k ==> m <= det(jacobian Fp (at y)) /\
                         m <= det(jacobian Fm (at y)))
     ==> &0 <
         let uu = frechet_derivative Fm (at x) (basis 1) +
                  frechet_derivative Fp (at (vector[x$1; r])) (basis 1) -
                  frechet_derivative Fm (at (vector[x$1; r])) (basis 1)
         and vv = frechet_derivative Fm (at x) (basis 2) +
                  lam % (frechet_derivative Fp (at (vector[x$1; r])) (basis 2) -
                         frechet_derivative Fm (at (vector[x$1; r])) (basis 2))
         in uu$1 * vv$2 - vv$1 * uu$2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  DISCH_THEN(LABEL_TAC "U") THEN DISCH_THEN(LABEL_TAC "Bd") THEN
  DISCH_THEN(LABEL_TAC "Lo") THEN REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  ABBREV_TAC `c:real^2 = vector[(x:real^2)$1; &0]` THEN
  ABBREV_TAC `y:real^2 = vector[(x:real^2)$1; r]` THEN
  SUBGOAL_THEN `(c:real^2) IN k /\ (x:real^2) IN k /\ (y:real^2) IN k`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN MAP_EVERY EXPAND_TAC ["c"; "y"] THEN
    REWRITE_TAC[VECTOR_2] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `norm(x - c:real^2) < d0 /\ norm(y - c:real^2) < d0`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["c"; "y"] THEN
    REWRITE_TAC[NORM_LT_SQUARE; dot; SUM_2; DIMINDEX_2; VECTOR_SUB_COMPONENT;
                VECTOR_2] THEN
    CONJ_TAC THEN CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
    REWRITE_TAC[REAL_SUB_REFL; REAL_MUL_LZERO; REAL_ADD_LID; REAL_SUB_RZERO] THEN
    REWRITE_TAC[GSYM REAL_POW_2] THEN MATCH_MP_TAC REAL_POW_LT2 THEN
    REWRITE_TAC[ARITH_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `frechet_derivative (Fp:real^2->real^2) (at c) (basis 1) =
    frechet_derivative (Fm:real^2->real^2) (at c) (basis 1)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL
     [`\z:real^2. (Fp:real^2->real^2) z - Fm z`;
      `\h:real^2. frechet_derivative (Fp:real^2->real^2) (at c) h -
                  frechet_derivative (Fm:real^2->real^2) (at c) h`;
      `c:real^2`; `basis 1:real^2`; `min ((x:real^2)$1 - a) (b - x$1)`]
      MOI_PDL_DERIV_ZERO_LINE) THEN
    REWRITE_TAC[VECTOR_SUB_EQ] THEN DISCH_THEN MATCH_MP_TAC THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC HAS_DERIVATIVE_SUB THEN REWRITE_TAC[ETA_AX] THEN
      CONJ_TAC THEN REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
      EXISTS_TAC `u:real^2->bool` THEN ASM SET_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `t:real` THEN DISCH_TAC THEN
    SUBGOAL_THEN `c + t % basis 1:real^2 = vector[(x:real^2)$1 + t; &0]`
    SUBST1_TAC THENL
     [EXPAND_TAC "c" THEN
      SIMP_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_ADD_COMPONENT;
               VECTOR_MUL_COMPONENT; VECTOR_2; BASIS_COMPONENT; ARITH] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "Lo" (MP_TAC o SPEC `c:real^2`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[jacobian; MOI_PDL_DET_COLS] THEN STRIP_TAC THEN
  USE_THEN "Bd" (MP_TAC o SPECL [`c:real^2`; `1`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  USE_THEN "Bd" (MP_TAC o SPECL [`c:real^2`; `2`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  USE_THEN "U" (MP_TAC o SPECL [`x:real^2`; `c:real^2`; `1`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  USE_THEN "U" (MP_TAC o SPECL [`x:real^2`; `c:real^2`; `2`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  USE_THEN "U" (MP_TAC o SPECL [`y:real^2`; `c:real^2`; `1`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  USE_THEN "U" (MP_TAC o SPECL [`y:real^2`; `c:real^2`; `2`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MATCH_MP_TAC MOI_PDL_CREASE_ALG THEN
  MAP_EVERY EXISTS_TAC
   [`frechet_derivative (Fm:real^2->real^2) (at c) (basis 1)`;
    `frechet_derivative (Fm:real^2->real^2) (at c) (basis 2)`;
    `frechet_derivative (Fp:real^2->real^2) (at c) (basis 2)`;
    `lam:real`; `bM:real`; `m:real`; `w:real`; `eta:real`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [UNDISCH_TAC
     `norm(frechet_derivative (Fp:real^2->real^2) (at y) (basis 1) -
           frechet_derivative Fp (at c) (basis 1)) <= w` THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC
     `norm(frechet_derivative (Fm:real^2->real^2) (at y) (basis 1) -
           frechet_derivative Fm (at c) (basis 1)) <= w` THEN
    UNDISCH_TAC
     `norm(frechet_derivative (Fm:real^2->real^2) (at x) (basis 1) -
           frechet_derivative Fm (at c) (basis 1)) <= w` THEN
    NORM_ARITH_TAC;
    ALL_TAC;
    UNDISCH_TAC
     `m <= frechet_derivative (Fp:real^2->real^2) (at c) (basis 1)$1 *
           frechet_derivative Fp (at c) (basis 2)$2 -
           frechet_derivative Fp (at c) (basis 2)$1 *
           frechet_derivative Fp (at c) (basis 1)$2` THEN
    ASM_REWRITE_TAC[]] THEN
  ABBREV_TAC `ep = frechet_derivative (Fp:real^2->real^2) (at y) (basis 2) -
                   frechet_derivative Fp (at c) (basis 2)` THEN
  ABBREV_TAC `em = frechet_derivative (Fm:real^2->real^2) (at y) (basis 2) -
                   frechet_derivative Fm (at c) (basis 2)` THEN
  ABBREV_TAC `e0 = frechet_derivative (Fm:real^2->real^2) (at x) (basis 2) -
                   frechet_derivative Fm (at c) (basis 2)` THEN
  SUBGOAL_THEN
   `(frechet_derivative (Fm:real^2->real^2) (at x) (basis 2) +
     lam % (frechet_derivative (Fp:real^2->real^2) (at y) (basis 2) -
            frechet_derivative Fm (at y) (basis 2))) -
    (frechet_derivative Fm (at c) (basis 2) +
     lam % (frechet_derivative Fp (at c) (basis 2) -
            frechet_derivative Fm (at c) (basis 2))) =
    e0 + lam % (ep - em)`
  SUBST1_TAC THENL
   [MAP_EVERY EXPAND_TAC ["e0"; "ep"; "em"] THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `norm(e0:real^2) + abs lam * norm(ep - em:real^2)` THEN
  CONJ_TAC THENL [REWRITE_TAC[GSYM NORM_MUL; NORM_TRIANGLE]; ALL_TAC] THEN
  SUBGOAL_THEN `abs lam * norm(ep - em:real^2) <= &2 * (&2 * w)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_ABS_POS; NORM_POS_LE] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `norm(ep:real^2) <= w` THEN UNDISCH_TAC `norm(em:real^2) <= w` THEN
    NORM_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `norm(e0:real^2) <= w` THEN REAL_ARITH_TAC);;

let MOI_PDL_FOLD_PROPS = prove
 (`!p q (x:real^2).
     &0 < p /\ &0 < q
     ==> (moi_pdl_fold p q x)$1 = x$1 /\
         (moi_pdl_fold p q x)$2 = moi_pdl_ramp p q (x$2) /\
         (p * exp q <= x$2 ==> moi_pdl_fold p q x = x) /\
         (x$2 <= p ==> moi_pdl_fold p q x = vector[x$1; &0]) /\
         &0 <= (moi_pdl_fold p q x)$2 /\
         (&0 <= x$2 ==> (moi_pdl_fold p q x)$2 <= x$2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[moi_pdl_fold; VECTOR_2] THEN
  REWRITE_TAC[MOI_PDL_RAMP_BOUNDS] THEN CONJ_TAC THEN DISCH_TAC THENL
   [ASM_SIMP_TAC[MOI_PDL_RAMP_LARGE] THEN
    REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2];
    ASM_SIMP_TAC[MOI_PDL_RAMP_SMALL]]);;

let MOI_PDL_MIN_DIV_LE = prove
 (`!c m. &0 < c ==> c * min (&1) (m / c) <= m`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `c * m / c` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_MIN_LE; REAL_LE_REFL];
    ASM_SIMP_TAC[REAL_DIV_LMUL; REAL_LT_IMP_NZ; REAL_LE_REFL]]);;

let MOI_PDL_CREASE_CONSTS = prove
 (`!bM m. &1 <= bM /\ &0 < m
          ==> ?eta w. &0 < eta /\ eta <= &1 /\ &0 < w /\ w <= &1 /\
                      &16 * bM pow 2 * eta <= m /\ &280 * bM * w <= m`,
  REPEAT STRIP_TAC THEN
  EXISTS_TAC `min (&1) (m / (&16 * bM pow 2))` THEN
  EXISTS_TAC `min (&1) (m / (&280 * bM))` THEN
  SUBGOAL_THEN `&0 < &16 * bM pow 2 /\ &0 < &280 * bM` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LT_MUL THEN
    REWRITE_TAC[REAL_OF_NUM_LT; ARITH] THEN
    TRY(MATCH_MP_TAC REAL_POW_LT) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[REAL_LT_MIN; REAL_MIN_LE; REAL_LE_REFL; REAL_LT_01] THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_MUL_ASSOC; MOI_PDL_MIN_DIV_LE]);;

(* ========================================================================= *)
(* D3, crease smoothing along a straight segment.                           *)
(* The smoothed map is Fm + (Fp - Fm) o fold, fold(x) = (x$1, ramp(x$2)),   *)
(* which equals Fm below the crease, Fp above the strip, and has the        *)
(* Jacobian of a convex-type combination of DFm and DFp near the crease.    *)
(* (The injectivity hypothesis on the crease is not needed.)                *)
(* ========================================================================= *)

let MOI_PDL_CREASE_JACF = prove
 (`!(Fp:real^2->real^2) Fm u p q (x:real^2).
     open u /\ smooth_map_on u Fp /\ smooth_map_on u Fm /\ &0 < p /\ &0 < q /\
     x IN u /\ moi_pdl_fold p q x IN u
     ==> det(jacobian (\x. Fm x + (Fp(moi_pdl_fold p q x) -
                                   Fm(moi_pdl_fold p q x))) (at x)) =
         let uu = frechet_derivative Fm (at x) (basis 1) +
                  frechet_derivative Fp
                    (at (vector[x$1; moi_pdl_ramp p q (x$2)])) (basis 1) -
                  frechet_derivative Fm
                    (at (vector[x$1; moi_pdl_ramp p q (x$2)])) (basis 1)
         and vv = frechet_derivative Fm (at x) (basis 2) +
                  moi_pdl_dramp p q (x$2) %
                  (frechet_derivative Fp
                     (at (vector[x$1; moi_pdl_ramp p q (x$2)])) (basis 2) -
                   frechet_derivative Fm
                     (at (vector[x$1; moi_pdl_ramp p q (x$2)])) (basis 2))
         in uu$1 * vv$2 - vv$1 * uu$2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  ABBREV_TAC `y:real^2 = moi_pdl_fold p q x` THEN
  SUBGOAL_THEN `(y:real^2) = vector[(x:real^2)$1; moi_pdl_ramp p q (x$2)]`
  (SUBST_ALL_TAC o SYM) THENL
   [EXPAND_TAC "y" THEN REWRITE_TAC[moi_pdl_fold]; ALL_TAC] THEN
  ABBREV_TAC `lam = moi_pdl_dramp p q ((x:real^2)$2)` THEN
  SUBGOAL_THEN
   `!g:real^2->real^2. g differentiable (at (y:real^2))
      ==> ((\x. g(moi_pdl_fold p q x)) has_derivative
           (\h. frechet_derivative g (at y) (vector[h$1; lam * h$2])))
          (at x)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
     `(\x:real^2. (g:real^2->real^2)(moi_pdl_fold p q x)) =
      g o moi_pdl_fold p q`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    SUBGOAL_THEN
     `(\h:real^2. frechet_derivative (g:real^2->real^2) (at y)
                    (vector[h$1; lam * h$2])) =
      frechet_derivative g (at y) o (\h. vector[h$1; lam * h$2])`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC DIFF_CHAIN_AT THEN
    EXPAND_TAC "lam" THEN ASM_SIMP_TAC[MOI_PDL_FOLD_DERIV] THEN
    ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(Fp:real^2->real^2) differentiable (at (y:real^2)) /\
    (Fm:real^2->real^2) differentiable (at y) /\
    (Fm:real^2->real^2) differentiable (at x)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `u:real^2->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\x. (Fm:real^2->real^2) x + (Fp(moi_pdl_fold p q x) -
                                    Fm(moi_pdl_fold p q x))) has_derivative
     (\h. frechet_derivative Fm (at x) h +
          (frechet_derivative Fp (at y) (vector[h$1; lam * h$2]) -
           frechet_derivative Fm (at y) (vector[h$1; lam * h$2]))))
    (at x)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HAS_DERIVATIVE_ADD THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC[ETA_AX; GSYM FRECHET_DERIVATIVE_WORKS];
      MATCH_MP_TAC HAS_DERIVATIVE_SUB THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[jacobian] THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
  REWRITE_TAC[MOI_PDL_DET_COLS] THEN
  SUBGOAL_THEN
   `vector[(basis 1:real^2)$1; lam * (basis 1:real^2)$2]:real^2 = basis 1 /\
    vector[(basis 2:real^2)$1; lam * (basis 2:real^2)$2]:real^2 =
    lam % basis 2`
  (fun th -> REWRITE_TAC[th]) THENL
   [SIMP_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2; VECTOR_MUL_COMPONENT;
             BASIS_COMPONENT; ARITH] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `linear(frechet_derivative (Fp:real^2->real^2) (at y)) /\
    linear(frechet_derivative (Fm:real^2->real^2) (at y))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[LINEAR_CMUL; GSYM VECTOR_SUB_LDISTRIB]);;

let MOI_PDL_OPEN_STRIP = prove
 (`!a b d. open {x:real^2 | a < x$1 /\ x$1 < b /\ abs(x$2) < d}`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN
   `{x:real^2 | a < x$1 /\ x$1 < b /\ abs(x$2) < d} =
    ({x | x$1 > a} INTER {x | x$1 < b}) INTER
    ({x | x$2 < d} INTER {x | x$2 > --d})`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM] THEN REAL_ARITH_TAC;
    REPEAT(MATCH_MP_TAC OPEN_INTER THEN CONJ_TAC) THEN
    REWRITE_TAC[OPEN_HALFSPACE_COMPONENT_LT; OPEN_HALFSPACE_COMPONENT_GT]]);;

let MOI_PDL_FOLD_ABOVE = prove
 (`!p q (x:real^2). &0 < p /\ &0 < q /\ p * exp q <= x$2
                    ==> moi_pdl_fold p q x = x`,
  MESON_TAC[MOI_PDL_FOLD_PROPS]);;

let MOI_PDL_FOLD_BELOW = prove
 (`!p q (x:real^2). &0 < p /\ &0 < q /\ x$2 <= p
                    ==> moi_pdl_fold p q x = vector[x$1; &0]`,
  MESON_TAC[MOI_PDL_FOLD_PROPS]);;
let MOI_PDL_PQ = prove
 (`!bB eta dd. &0 < bB /\ &0 < eta /\ &0 < dd
       ==> &0 < bB / eta /\ &0 < dd * exp(--(bB / eta)) /\
           dd * exp(--(bB / eta)) < dd /\
           (dd * exp(--(bB / eta))) * exp(bB / eta) = dd`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_LT_MUL; REAL_EXP_POS_LT] THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC; GSYM REAL_EXP_ADD; REAL_ADD_LINV;
              REAL_EXP_0; REAL_MUL_RID] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
  MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[GSYM REAL_EXP_0] THEN REWRITE_TAC[REAL_EXP_MONO_LT] THEN
  REWRITE_TAC[REAL_NEG_LT0] THEN ASM_SIMP_TAC[REAL_LT_DIV]);;

let MOI_SMO_CREASE = prove
 (`MOI_SMO_CREASE_STATEMENT`,
  REWRITE_TAC[MOI_SMO_CREASE_STATEMENT] THEN
  MAP_EVERY X_GEN_TAC [`Fp:real^2->real^2`; `Fm:real^2->real^2`;
    `u:real^2->bool`; `a:real`; `b:real`; `d:real`; `e:real`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `!t. a <= t /\ t <= b
        ==> (Fp:real^2->real^2)(vector[t; &0]) = (Fm:real^2->real^2)(vector[t; &0])`
  (LABEL_TAC "crease") THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!x:real^2. a <= x$1 /\ x$1 <= b /\ abs(x$2) <= d /\
               (x$1 <= a + e \/ b - e <= x$1)
               ==> (Fp:real^2->real^2) x = (Fm:real^2->real^2) x`
  (LABEL_TAC "ends") THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  ABBREV_TAC `k = {x:real^2 | a <= x$1 /\ x$1 <= b /\ abs(x$2) <= d}` THEN
  SUBGOAL_THEN `!z:real^2. z IN k <=> a <= z$1 /\ z$1 <= b /\ abs(z$2) <= d`
  (LABEL_TAC "kmem") THENL
   [EXPAND_TAC "k" THEN REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `compact(k:real^2->bool)` ASSUME_TAC THENL
   [SUBGOAL_THEN `k = interval[vector[a; --d]:real^2, vector[b; d]]`
    SUBST1_TAC THENL
     [ASM_REWRITE_TAC[EXTENSION; IN_INTERVAL; DIMINDEX_2; FORALL_2;
                      VECTOR_2] THEN REAL_ARITH_TAC;
      REWRITE_TAC[COMPACT_INTERVAL]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`Fp:real^2->real^2`; `u:real^2->bool`; `k:real^2->bool`;
                 `basis 1:real^2`] MOI_PDL_PARTIAL_UNIF) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `B1:real` STRIP_ASSUME_TAC) (LABEL_TAC "uc1")) THEN
  MP_TAC(ISPECL [`Fp:real^2->real^2`; `u:real^2->bool`; `k:real^2->bool`;
                 `basis 2:real^2`] MOI_PDL_PARTIAL_UNIF) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `B2:real` STRIP_ASSUME_TAC) (LABEL_TAC "uc2")) THEN
  MP_TAC(ISPECL [`Fm:real^2->real^2`; `u:real^2->bool`; `k:real^2->bool`;
                 `basis 1:real^2`] MOI_PDL_PARTIAL_UNIF) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `B3:real` STRIP_ASSUME_TAC) (LABEL_TAC "uc3")) THEN
  MP_TAC(ISPECL [`Fm:real^2->real^2`; `u:real^2->bool`; `k:real^2->bool`;
                 `basis 2:real^2`] MOI_PDL_PARTIAL_UNIF) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `B4:real` STRIP_ASSUME_TAC) (LABEL_TAC "uc4")) THEN
  SUBGOAL_THEN `!x:real^2. x IN k
                  ==> &0 < det(jacobian Fp (at x)) /\
                      &0 < det(jacobian Fm (at x))`
  (LABEL_TAC "jk") THENL
   [GEN_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`Fp:real^2->real^2`; `u:real^2->bool`; `k:real^2->bool`]
    MOI_PDL_DET_LOWER) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `mp:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`Fm:real^2->real^2`; `u:real^2->bool`; `k:real^2->bool`]
    MOI_PDL_DET_LOWER) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `mm:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `m = min mp mm` THEN
  ABBREV_TAC `bM = &1 + B1 + B2 + B3 + B4` THEN
  MP_TAC(ISPECL [`bM:real`; `m:real`] MOI_PDL_CREASE_CONSTS) THEN
  ANTS_TAC THENL
   [MAP_EVERY EXPAND_TAC ["m"; "bM"] THEN
    REWRITE_TAC[REAL_LT_MIN] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `eta:real` (X_CHOOSE_THEN `w:real`
    STRIP_ASSUME_TAC)) THEN
  REMOVE_THEN "uc1" (MP_TAC o SPEC `w:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` STRIP_ASSUME_TAC) THEN
  REMOVE_THEN "uc2" (MP_TAC o SPEC `w:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d2:real` STRIP_ASSUME_TAC) THEN
  REMOVE_THEN "uc3" (MP_TAC o SPEC `w:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d3:real` STRIP_ASSUME_TAC) THEN
  REMOVE_THEN "uc4" (MP_TAC o SPEC `w:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d4:real` STRIP_ASSUME_TAC) THEN
  X_CHOOSE_THEN `bB:real` STRIP_ASSUME_TAC MOI_PDL_DSTEP_BOUND THEN
  ABBREV_TAC `d0 = min d1 (min d2 (min d3 d4))` THEN
  ABBREV_TAC `dd = min (d0 / &2) (d / &2)` THEN
  ABBREV_TAC `q = bB / eta` THEN
  ABBREV_TAC `p = dd * exp(--q)` THEN
  SUBGOAL_THEN `&0 < d0 /\ &0 < dd /\ dd < d0 /\ dd < d` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["dd"; "d0"] THEN
    REWRITE_TAC[REAL_LT_MIN; REAL_MIN_LT] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`bB:real`; `eta:real`; `dd:real`] MOI_PDL_PQ) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `d0 <= d1 /\ d0 <= d2 /\ d0 <= d3 /\ d0 <= d4 /\
                m <= mp /\ m <= mm /\ &1 <= bM /\
                B1 <= bM /\ B2 <= bM /\ B3 <= bM /\ B4 <= bM`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["d0"; "m"; "bM"] THEN
    REWRITE_TAC[REAL_MIN_LE; REAL_LE_REFL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y z j. y IN k /\ z IN k /\ norm(y - z) < d0 /\ (j = 1 \/ j = 2)
            ==> norm(frechet_derivative (Fp:real^2->real^2) (at y) (basis j) -
                     frechet_derivative Fp (at z) (basis j)) <= w /\
                norm(frechet_derivative (Fm:real^2->real^2) (at y) (basis j) -
                     frechet_derivative Fm (at z) (basis j)) <= w`
  (LABEL_TAC "U") THENL
   [REPEAT GEN_TAC THEN USE_THEN "kmem" (fun th -> REWRITE_TAC[th]) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
    MATCH_MP_TAC REAL_LT_IMP_LE THEN FIRST_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y j. y IN k /\ (j = 1 \/ j = 2)
          ==> norm(frechet_derivative (Fp:real^2->real^2) (at y) (basis j))
              <= bM /\
              norm(frechet_derivative (Fm:real^2->real^2) (at y) (basis j))
              <= bM`
  (LABEL_TAC "Bd") THENL
   [REPEAT GEN_TAC THEN USE_THEN "kmem" (fun th -> REWRITE_TAC[th]) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THENL
     [EXISTS_TAC `B1:real`; EXISTS_TAC `B3:real`;
      EXISTS_TAC `B2:real`; EXISTS_TAC `B4:real`] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y. y IN k ==> m <= det(jacobian (Fp:real^2->real^2) (at y)) /\
                   m <= det(jacobian (Fm:real^2->real^2) (at y))`
  (LABEL_TAC "Lo") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THENL
     [EXISTS_TAC `mp:real`; EXISTS_TAC `mm:real`] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `\x:real^2. (Fm:real^2->real^2) x +
                         ((Fp:real^2->real^2)(moi_pdl_fold p q x) -
                          Fm(moi_pdl_fold p q x))` THEN
  EXISTS_TAC `dd:real` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!x:real^2. a < x$1 /\ x$1 < b /\ abs(x$2) < d
               ==> x IN k /\ moi_pdl_fold p q x IN k`
  (LABEL_TAC "fk") THENL
   [GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`p:real`; `q:real`; `x:real^2`] MOI_PDL_FOLD_PROPS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `&0 <= (x:real^2)$2` THENL
     [UNDISCH_TAC `&0 <= (x:real^2)$2 ==> moi_pdl_fold p q x$2 <= x$2` THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      SUBGOAL_THEN `moi_pdl_fold p q x$2 = &0` MP_TAC THENL
       [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_PDL_RAMP_SMALL THEN
        ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN REWRITE_TAC[MOI_PDL_OPEN_STRIP] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `u:real^2->bool` THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[SUBSET];
      ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN REWRITE_TAC[MOI_PDL_OPEN_STRIP] THEN
    CONJ_TAC THEN
    (MATCH_MP_TAC(REWRITE_RULE[o_DEF] SMOOTH_MAP_ON_COMPOSE_OPEN) THEN
     EXISTS_TAC `u:real^2->bool` THEN ASM_REWRITE_TAC[MOI_PDL_OPEN_STRIP] THEN
     CONJ_TAC THENL
      [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
       ASM_MESON_TAC[SUBSET];
       MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
       ASM_SIMP_TAC[SUBSET_UNIV; MOI_PDL_FOLD_SMOOTH; ETA_AX]]);
    ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `x:real^2` THEN STRIP_TAC THEN
    USE_THEN "fk" (MP_TAC o SPEC `x:real^2`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    SUBGOAL_THEN `(x:real^2) IN u /\ moi_pdl_fold p q x IN u`
    STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `!z:real^2. dist(z,x) < min ((x:real^2)$1 - a) (b - x$1)
                 ==> a < z$1 /\ z$1 < b`
    ASSUME_TAC THENL
     [GEN_TAC THEN REWRITE_TAC[dist] THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`z - x:real^2`; `1`] COMPONENT_LE_NORM) THEN
      REWRITE_TAC[VECTOR_SUB_COMPONENT] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_CASES_TAC `(x:real^2)$2 < p` THENL
     [SUBGOAL_THEN
       `jacobian (\x. (Fm:real^2->real^2) x +
                      ((Fp:real^2->real^2)(moi_pdl_fold p q x) -
                       Fm(moi_pdl_fold p q x))) (at x) =
        jacobian Fm (at x)`
      SUBST1_TAC THENL
       [REWRITE_TAC[jacobian] THEN AP_TERM_TAC THEN
        MATCH_MP_TAC FRECHET_DERIVATIVE_LOCAL THEN
        EXISTS_TAC `min (p - (x:real^2)$2) (min (x$1 - a) (b - x$1))` THEN
        CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN BETA_TAC THEN
        SUBGOAL_THEN `a < (z:real^2)$1 /\ z$1 < b /\ z$2 < p` STRIP_ASSUME_TAC
        THENL
         [CONJ_TAC THENL
           [FIRST_X_ASSUM(MP_TAC o SPEC `z:real^2`) THEN
            ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
            ALL_TAC] THEN
          UNDISCH_TAC
           `dist(z:real^2,x) < min (p - (x:real^2)$2) (min (x$1 - a) (b - x$1))` THEN
          REWRITE_TAC[dist] THEN
          MP_TAC(ISPECL [`z - x:real^2`; `1`] COMPONENT_LE_NORM) THEN
          MP_TAC(ISPECL [`z - x:real^2`; `2`] COMPONENT_LE_NORM) THEN
          REWRITE_TAC[VECTOR_SUB_COMPONENT] THEN REAL_ARITH_TAC;
          ALL_TAC] THEN
        SUBGOAL_THEN `moi_pdl_fold p q z = vector[(z:real^2)$1; &0]`
        SUBST1_TAC THENL
         [MATCH_MP_TAC MOI_PDL_FOLD_BELOW THEN ASM_REWRITE_TAC[] THEN
          ASM_REAL_ARITH_TAC;
          ALL_TAC] THEN
        SUBGOAL_THEN
         `(Fp:real^2->real^2)(vector[(z:real^2)$1; &0]) =
          (Fm:real^2->real^2)(vector[z$1; &0])`
        SUBST1_TAC THENL
         [USE_THEN "crease" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
          VECTOR_ARITH_TAC];
        USE_THEN "jk" (MP_TAC o SPEC `x:real^2`) THEN ASM_SIMP_TAC[]];
      ALL_TAC] THEN
    ASM_CASES_TAC `dd < (x:real^2)$2` THENL
     [SUBGOAL_THEN
       `jacobian (\x. (Fm:real^2->real^2) x +
                      ((Fp:real^2->real^2)(moi_pdl_fold p q x) -
                       Fm(moi_pdl_fold p q x))) (at x) =
        jacobian Fp (at x)`
      SUBST1_TAC THENL
       [REWRITE_TAC[jacobian] THEN AP_TERM_TAC THEN
        MATCH_MP_TAC FRECHET_DERIVATIVE_LOCAL THEN
        EXISTS_TAC `(x:real^2)$2 - dd` THEN
        CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        X_GEN_TAC `z:real^2` THEN REWRITE_TAC[dist] THEN DISCH_TAC THEN
        BETA_TAC THEN
        SUBGOAL_THEN `moi_pdl_fold p q z = z` SUBST1_TAC THENL
         [MATCH_MP_TAC MOI_PDL_FOLD_ABOVE THEN ASM_REWRITE_TAC[] THEN
          MP_TAC(ISPECL [`z - x:real^2`; `2`] COMPONENT_LE_NORM) THEN
          REWRITE_TAC[VECTOR_SUB_COMPONENT] THEN ASM_REAL_ARITH_TAC;
          VECTOR_ARITH_TAC];
        USE_THEN "jk" (MP_TAC o SPEC `x:real^2`) THEN ASM_SIMP_TAC[]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`Fp:real^2->real^2`; `Fm:real^2->real^2`; `u:real^2->bool`;
                   `p:real`; `q:real`; `x:real^2`] MOI_PDL_CREASE_JACF) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    MP_TAC(ISPECL [`Fp:real^2->real^2`; `Fm:real^2->real^2`; `u:real^2->bool`;
                   `k:real^2->bool`; `a:real`; `b:real`; `d:real`; `x:real^2`;
                   `moi_pdl_ramp p q ((x:real^2)$2)`;
                   `moi_pdl_dramp p q ((x:real^2)$2)`;
                   `d0:real`; `bM:real`; `m:real`; `w:real`; `eta:real`]
      MOI_PDL_CREASE_DET) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`p:real`; `q:real`; `(x:real^2)$2`] MOI_PDL_RAMP_BOUNDS) THEN
      MP_TAC(ISPECL [`p:real`; `q:real`; `(x:real^2)$2`; `bB:real`]
        MOI_PDL_DRAMP_BOUNDS) THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `bB / q = eta` SUBST1_TAC THENL
       [EXPAND_TAC "q" THEN UNDISCH_TAC `&0 < eta` THEN
        UNDISCH_TAC `&0 < bB` THEN CONV_TAC REAL_FIELD;
        ALL_TAC] THEN
      REPEAT STRIP_TAC THEN TRY(FIRST_X_ASSUM MATCH_MP_TAC) THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REPEAT(ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC]) THEN
    REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `x:real^2` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "cases")))) THEN
  USE_THEN "fk" (MP_TAC o SPEC `x:real^2`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[] THEN USE_THEN "kmem" (fun th -> REWRITE_TAC[th]) THEN
  MP_TAC(ISPECL [`p:real`; `q:real`; `x:real^2`] MOI_PDL_FOLD_PROPS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> ASSUME_TAC(CONJUNCT1 th) THEN
                       REWRITE_TAC[CONJUNCT1 th]) THEN STRIP_TAC THEN
  REMOVE_THEN "cases" STRIP_ASSUME_TAC THENL
   [ASM_CASES_TAC `&0 <= (x:real^2)$2` THEN ASM_REWRITE_TAC[] THENL
     [SUBGOAL_THEN `moi_pdl_fold p q x = x` SUBST1_TAC THENL
       [MATCH_MP_TAC MOI_PDL_FOLD_ABOVE THEN ASM_REWRITE_TAC[] THEN
        ASM_REAL_ARITH_TAC;
        VECTOR_ARITH_TAC];
      SUBGOAL_THEN `moi_pdl_fold p q x = vector[(x:real^2)$1; &0]`
      SUBST1_TAC THENL
       [MATCH_MP_TAC MOI_PDL_FOLD_BELOW THEN ASM_REWRITE_TAC[] THEN
        ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN
       `(Fp:real^2->real^2)(vector[(x:real^2)$1; &0]) =
        (Fm:real^2->real^2)(vector[x$1; &0])`
      SUBST1_TAC THENL
       [USE_THEN "crease" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
        VECTOR_ARITH_TAC]];
    ALL_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `(Fp:real^2->real^2)(moi_pdl_fold p q x) = Fm(moi_pdl_fold p q x) /\
    (Fp:real^2->real^2) x = Fm x`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN
    USE_THEN "ends" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ASM_REWRITE_TAC[COND_ID] THEN VECTOR_ARITH_TAC;
    CONJ_TAC THEN
    USE_THEN "ends" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ASM_REWRITE_TAC[COND_ID] THEN VECTOR_ARITH_TAC]);;

(* ========================================================================= *)
(* D1, linearization at a corner.                                            *)
(* ========================================================================= *)

let MOI_PDL_REAL_CHAIN = prove
 (`!(f:real^N->real) f' g g' x.
     ((\y. lift(f y)) has_derivative (\h. lift(f' h))) (at x) /\
     (g has_real_derivative g') (atreal (f x))
     ==> ((\y. lift(g(f y))) has_derivative (\h. lift(g' * f' h))) (at x)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\y:real^N. lift(g((f:real^N->real) y))) =
                (lift o g o drop) o (\y. lift(f y))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_DROP]; ALL_TAC] THEN
  SUBGOAL_THEN `(\h:real^N. lift(g' * (f':real^N->real) h)) =
                (\h. g' % h) o (\h. lift(f' h))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_CMUL]; ALL_TAC] THEN
  MATCH_MP_TAC DIFF_CHAIN_AT THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `(g has_real_derivative g') (atreal ((f:real^N->real) x))` THEN
  REWRITE_TAC[HAS_REAL_FRECHET_DERIVATIVE_AT]);;

let MOI_PDL_NORM_DERIV = prove
 (`!x:real^N. ~(x = vec 0)
       ==> ((\y. lift(norm y)) has_derivative (\h. lift((x dot h) / norm x)))
           (at x)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\y:real^N. lift(norm y)) = (\y. lift(sqrt(norm y pow 2)))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN SIMP_TAC[POW_2_SQRT; NORM_POS_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\h:real^N. lift((x dot h) / norm x)) =
                (\h. lift(inv(&2 * sqrt(norm x pow 2)) * (&2 * (x dot h))))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN SIMP_TAC[POW_2_SQRT; NORM_POS_LE] THEN
    GEN_TAC THEN AP_TERM_TAC THEN
    UNDISCH_TAC `~(x:real^N = vec 0)` THEN REWRITE_TAC[GSYM NORM_EQ_0] THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  MATCH_MP_TAC(REWRITE_RULE[] (ISPECL
   [`\y:real^N. norm y pow 2`; `\h:real^N. &2 * (x dot h)`]
   MOI_PDL_REAL_CHAIN)) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[LIFT_CMUL; HAS_DERIVATIVE_SQNORM_AT];
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_SQRT THEN
    ASM_SIMP_TAC[REAL_POW_LT; NORM_POS_LT]]);;

let MOI_PDL_CUT_DERIV = prove
 (`!r (x:real^N). &0 < r /\ ~(x = vec 0)
       ==> ((\y. lift(smooth_step(&2 * norm y / r - &1))) has_derivative
            (\h. lift(moi_pdl_dstep(&2 * norm x / r - &1) *
                      (&2 / r * (x dot h) / norm x)))) (at x)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[] (ISPECL
   [`\y:real^N. &2 * norm y / r - &1`;
    `\h:real^N. &2 / r * (x dot h) / norm x`]
   MOI_PDL_REAL_CHAIN)) THEN
  REWRITE_TAC[MOI_PDL_DSTEP_DERIV] THEN
  SUBGOAL_THEN
   `(\y:real^N. lift(&2 * norm y / r - &1)) =
    (\y. (&2 / r) % lift(norm y) - lift(&1))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; GSYM LIFT_CMUL; GSYM LIFT_SUB; LIFT_EQ] THEN
    GEN_TAC THEN REWRITE_TAC[real_div] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\h:real^N. lift(&2 / r * (x dot h) / norm x)) =
    (\h. (&2 / r) % lift((x dot h) / norm x) - vec 0)`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; VECTOR_SUB_RZERO; GSYM LIFT_CMUL] THEN
    REWRITE_TAC[real_div; REAL_MUL_AC];
    ALL_TAC] THEN
  MATCH_MP_TAC HAS_DERIVATIVE_SUB THEN REWRITE_TAC[HAS_DERIVATIVE_CONST] THEN
  MATCH_MP_TAC HAS_DERIVATIVE_CMUL THEN ASM_SIMP_TAC[MOI_PDL_NORM_DERIV]);;

let MOI_PDL_CR_NONZERO_NEAR = prove
 (`!u0:real^2 v0:real^2.
     ~(u0$1 * v0$2 - v0$1 * u0$2 = &0)
     ==> ?e. &0 < e /\
             !u v:real^2. norm(u - u0) <= e /\ norm(v - v0) <= e
                          ==> ~(u$1 * v$2 - v$1 * u$2 = &0)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `c = abs(u0$1 * (v0:real^2)$2 - v0$1 * (u0:real^2)$2)` THEN
  SUBGOAL_THEN `&0 < c` ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `kk = &4 * (norm(u0:real^2) + norm(v0:real^2) + &1)` THEN
  SUBGOAL_THEN `&0 < kk` ASSUME_TAC THENL
   [EXPAND_TAC "kk" THEN
    MP_TAC(ISPEC `u0:real^2` NORM_POS_LE) THEN
    MP_TAC(ISPEC `v0:real^2` NORM_POS_LE) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `min (&1) (c / kk)` THEN
  ASM_SIMP_TAC[REAL_LT_MIN; REAL_LT_01; REAL_LT_DIV] THEN
  MAP_EVERY X_GEN_TAC [`u:real^2`; `v:real^2`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`u:real^2`; `v:real^2`; `u0:real^2`; `v0:real^2`]
    MOI_PDL_CR_PERTURB) THEN
  SUBGOAL_THEN `kk * min (&1) (c / kk) <= c /\ min (&1) (c / kk) <= &1 /\
                &0 <= min (&1) (c / kk)` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[MOI_PDL_MIN_DIV_LE] THEN
    REWRITE_TAC[REAL_MIN_LE; REAL_LE_REFL; REAL_LE_MIN; REAL_POS] THEN
    ASM_SIMP_TAC[REAL_LE_DIV; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  ABBREV_TAC `e = min (&1) (c / kk)` THEN
  SUBGOAL_THEN
   `norm(u - u0:real^2) * norm(v:real^2) <= e * (norm(v0:real^2) + &1) /\
    norm(u0:real^2) * norm(v - v0:real^2) <= norm u0 * e`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
    ASM_REWRITE_TAC[NORM_POS_LE; REAL_LE_REFL] THEN
    UNDISCH_TAC `norm(v - v0:real^2) <= e` THEN UNDISCH_TAC `e <= &1` THEN
    NORM_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `kk * e <= c` THEN EXPAND_TAC "kk" THEN
  UNDISCH_TAC `&0 < c` THEN EXPAND_TAC "c" THEN
  UNDISCH_TAC `norm(u - u0:real^2) * norm(v:real^2) <= e * (norm(v0:real^2) + &1)` THEN
  UNDISCH_TAC `norm(u0:real^2) * norm(v - v0:real^2) <= norm u0 * e` THEN
  REAL_ARITH_TAC);;

let MOI_PDL_LIN_DERIV = prove
 (`!(G:real^2->real^2) (L:real^2->real^2) r x.
     &0 < r /\ ~(x = vec 0) /\ G differentiable (at x) /\ linear L
     ==> ((\y. L y + smooth_step(&2 * norm y / r - &1) % (G y - L y))
          has_derivative
          (\h. L h + (smooth_step(&2 * norm x / r - &1) %
                      (frechet_derivative G (at x) h - L h) +
                      (moi_pdl_dstep(&2 * norm x / r - &1) *
                       (&2 / r * (x dot h) / norm x)) % (G x - L x))))
         (at x)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_DERIVATIVE_ADD THEN
  ASM_SIMP_TAC[HAS_DERIVATIVE_LINEAR] THEN
  MP_TAC(ISPECL
   [`\y:real^2. smooth_step(&2 * norm y / r - &1)`;
    `\h:real^2. moi_pdl_dstep(&2 * norm(x:real^2) / r - &1) *
                (&2 / r * (x dot h) / norm x)`;
    `\y:real^2. (G:real^2->real^2) y - (L:real^2->real^2) y`;
    `\h:real^2. frechet_derivative (G:real^2->real^2) (at x) h -
                (L:real^2->real^2) h`;
    `x:real^2`] HAS_DERIVATIVE_MUL_AT) THEN
  REWRITE_TAC[o_DEF] THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[MOI_PDL_CUT_DERIV] THEN MATCH_MP_TAC HAS_DERIVATIVE_SUB THEN
    ASM_SIMP_TAC[HAS_DERIVATIVE_LINEAR; ETA_AX] THEN
    ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS];
    REWRITE_TAC[]]);;

let MOI_PDL_CJ_BOUND = prove
 (`!bB r (x:real^N) t h.
     &0 < r /\ ~(x = vec 0) /\ &0 <= t /\ t <= bB /\ norm h <= &1
     ==> abs(t * (&2 / r * (x dot h) / norm x)) <= &2 * bB / r`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `abs((x dot h) / norm(x:real^N)) <= &1` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_ABS_DIV; REAL_ABS_NORM; REAL_LE_LDIV_EQ; NORM_POS_LT] THEN
    REWRITE_TAC[REAL_MUL_LID] THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `norm(x:real^N) * norm(h:real^N)` THEN
    REWRITE_TAC[NORM_CAUCHY_SCHWARZ_ABS] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[NORM_POS_LE];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ABS_MUL] THEN
  SUBGOAL_THEN `abs(&2 / r) = &2 / r` SUBST1_TAC THENL
   [REWRITE_TAC[REAL_ABS_REFL] THEN ASM_SIMP_TAC[REAL_LE_DIV; REAL_POS;
                                                 REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `&2 * bB / r = bB * (&2 / r) * &1` SUBST1_TAC THENL
   [REWRITE_TAC[real_div] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_ABS_POS] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
    ASM_SIMP_TAC[REAL_LE_DIV; REAL_POS; REAL_LT_IMP_LE];
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[REAL_LE_DIV; REAL_POS; REAL_LT_IMP_LE]]);;

let MOI_PDL_LIN_ARITH = prove
 (`!bB r eta nx c g.
     &0 < bB /\ &0 < r /\ &0 < eta /\ nx <= r /\ abs c <= &2 * bB / r /\
     &0 <= g /\ g <= eta / (&4 * bB) * nx
     ==> abs c * g <= eta / &2`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(&2 * bB / r) * (eta / (&4 * bB) * r)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_ABS_POS] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `eta / (&4 * bB) * nx` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN
    UNDISCH_TAC `&0 < bB` THEN UNDISCH_TAC `&0 < r` THEN CONV_TAC REAL_FIELD]);;

let MOI_PDL_PARTIAL_CONT_AT = prove
 (`!(G:real^2->real^2) u x0 j e.
     open u /\ smooth_map_on u G /\ x0 IN u /\ &0 < e
     ==> ?d. &0 < d /\
             !x. norm(x - x0) < d
                 ==> norm(frechet_derivative G (at x) (basis j) -
                          frechet_derivative G (at x0) (basis j)) < e`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`u:real^2->bool`; `G:real^2->real^2`; `basis j:real^2`]
    SMOOTH_MAP_ON_FRECHET_DERIVATIVE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o MATCH_MP SMOOTH_MAP_ON_CONTINUOUS_ON) THEN
  ASM_SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_AT] THEN
  DISCH_THEN(MP_TAC o SPEC `x0:real^2`) THEN ASM_REWRITE_TAC[continuous_at] THEN
  DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[dist]);;

let MOI_SMO_LIN = prove
 (`MOI_SMO_LIN_STATEMENT`,
  REWRITE_TAC[MOI_SMO_LIN_STATEMENT] THEN
  MAP_EVERY X_GEN_TAC [`G:real^2->real^2`; `u:real^2->bool`;
                       `S:real^2->bool`; `R:real`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `!x. x IN S INTER cball(vec 0,R)
        ==> ~(det(jacobian (G:real^2->real^2) (at x)) = &0)`
  (LABEL_TAC "jdet") THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `S:real^2->bool = {}` THENL
   [EXISTS_TAC `&1` THEN ASM_REWRITE_TAC[INTER_EMPTY; NOT_IN_EMPTY; REAL_LT_01];
    ALL_TAC] THEN
  SUBGOAL_THEN `(vec 0:real^2) IN S` ASSUME_TAC THENL
   [ASM_MESON_TAC[CONIC_CONTAINS_0]; ALL_TAC] THEN
  SUBGOAL_THEN `(vec 0:real^2) IN u` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `L = frechet_derivative (G:real^2->real^2) (at (vec 0))` THEN
  SUBGOAL_THEN
   `((G:real^2->real^2) has_derivative L) (at (vec 0)) /\
    linear (L:real^2->real^2)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "L" THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`u:real^2->bool`; `G:real^2->real^2`]
        SMOOTH_MAP_ON_HAS_DERIVATIVE) THEN ASM_SIMP_TAC[];
      MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
      EXISTS_TAC `u:real^2->bool` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `~((L:real^2->real^2)(basis 1)$1 * L(basis 2)$2 -
      L(basis 2)$1 * L(basis 1)$2 = &0)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `(vec 0:real^2) IN S INTER cball(vec 0,R)` ASSUME_TAC THENL
     [ASM_SIMP_TAC[IN_INTER; CENTRE_IN_CBALL; REAL_LT_IMP_LE]; ALL_TAC] THEN
    USE_THEN "jdet" (MP_TAC o C MATCH_MP
      (ASSUME `(vec 0:real^2) IN S INTER cball(vec 0,R)`)) THEN
    ASM_REWRITE_TAC[jacobian; MOI_PDL_DET_COLS];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(L:real^2->real^2)(basis 1)`; `(L:real^2->real^2)(basis 2)`]
    MOI_PDL_CR_NONZERO_NEAR) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `eta:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "near"))) THEN
  X_CHOOSE_THEN `bB:real` STRIP_ASSUME_TAC MOI_PDL_DSTEP_BOUND THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL] o
    check (fun th -> concl th = `open(u:real^2->bool)`)) THEN
  DISCH_THEN(MP_TAC o SPEC `vec 0:real^2`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d0:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`G:real^2->real^2`; `u:real^2->bool`; `vec 0:real^2`; `1`;
                 `eta / &2`] MOI_PDL_PARTIAL_CONT_AT) THEN
  ASM_REWRITE_TAC[REAL_HALF; VECTOR_SUB_RZERO] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`G:real^2->real^2`; `u:real^2->bool`; `vec 0:real^2`; `2`;
                 `eta / &2`] MOI_PDL_PARTIAL_CONT_AT) THEN
  ASM_REWRITE_TAC[REAL_HALF; VECTOR_SUB_RZERO] THEN
  DISCH_THEN(X_CHOOSE_THEN `d2:real` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `((G:real^2->real^2) has_derivative L) (at (vec 0))` THEN
  REWRITE_TAC[HAS_DERIVATIVE_AT_ALT] THEN
  DISCH_THEN(MP_TAC o SPEC `eta / (&4 * bB)` o CONJUNCT2) THEN
  ANTS_TAC THENL [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[VECTOR_SUB_RZERO] THEN
  DISCH_THEN(X_CHOOSE_THEN `d3:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `min (min d0 d1) (min d2 d3)` THEN
  ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  MAP_EVERY X_GEN_TAC [`r:real`; `x:real^2`] THEN STRIP_TAC THEN
  ASM_CASES_TAC `r < norm(x:real^2)` THENL
   [SUBGOAL_THEN
     `jacobian (\y. (L:real^2->real^2) y +
                    smooth_step(&2 * norm y / r - &1) %
                    ((G:real^2->real^2) y - L y)) (at x) =
      jacobian G (at x)`
    SUBST1_TAC THENL
     [REWRITE_TAC[jacobian] THEN AP_TERM_TAC THEN
      MATCH_MP_TAC FRECHET_DERIVATIVE_LOCAL THEN
      EXISTS_TAC `norm(x:real^2) - r` THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      X_GEN_TAC `y:real^2` THEN DISCH_TAC THEN BETA_TAC THEN
      SUBGOAL_THEN `smooth_step(&2 * norm(y:real^2) / r - &1) = &1`
      SUBST1_TAC THENL
       [MATCH_MP_TAC SMOOTH_STEP_1 THEN
        SUBGOAL_THEN `r < norm(y:real^2)` MP_TAC THENL
         [UNDISCH_TAC `dist(y:real^2,x) < norm(x:real^2) - r` THEN
          REWRITE_TAC[dist] THEN NORM_ARITH_TAC;
          ALL_TAC] THEN
        DISCH_TAC THEN
        MATCH_MP_TAC(REAL_ARITH `&1 <= a ==> &1 <= &2 * a - &1`) THEN
        ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN ASM_REAL_ARITH_TAC;
        VECTOR_ARITH_TAC];
      USE_THEN "jdet" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_CASES_TAC `x:real^2 = vec 0` THENL
   [SUBGOAL_THEN
     `jacobian (\y. (L:real^2->real^2) y +
                    smooth_step(&2 * norm y / r - &1) %
                    ((G:real^2->real^2) y - L y)) (at x) =
      matrix L`
    SUBST1_TAC THENL
     [REWRITE_TAC[jacobian] THEN AP_TERM_TAC THEN
      MATCH_MP_TAC EQ_TRANS THEN
      EXISTS_TAC `frechet_derivative (L:real^2->real^2) (at x)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC FRECHET_DERIVATIVE_LOCAL THEN EXISTS_TAC `r / &2` THEN
        ASM_REWRITE_TAC[REAL_HALF] THEN
        X_GEN_TAC `y:real^2` THEN REWRITE_TAC[DIST_0] THEN DISCH_TAC THEN
        BETA_TAC THEN
        SUBGOAL_THEN `smooth_step(&2 * norm(y:real^2) / r - &1) = &0`
        SUBST1_TAC THENL
         [MATCH_MP_TAC SMOOTH_STEP_0 THEN
          MATCH_MP_TAC(REAL_ARITH `a <= &1 / &2 ==> &2 * a - &1 <= &0`) THEN
          ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
          VECTOR_ARITH_TAC];
        CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
        ASM_SIMP_TAC[HAS_DERIVATIVE_LINEAR]];
      ASM_REWRITE_TAC[MOI_PDL_DET_COLS]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^2) IN u` ASSUME_TAC THENL
   [UNDISCH_TAC `ball(vec 0:real^2,d0) SUBSET u` THEN
    REWRITE_TAC[SUBSET; IN_BALL_0] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(G:real^2->real^2) differentiable (at x)` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `u:real^2->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`G:real^2->real^2`; `L:real^2->real^2`; `r:real`;
                 `x:real^2`] MOI_PDL_LIN_DERIV) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[jacobian;
                                   GSYM(MATCH_MP FRECHET_DERIVATIVE_AT th)]) THEN
  REWRITE_TAC[MOI_PDL_DET_COLS] THEN USE_THEN "near" MATCH_MP_TAC THEN
  REWRITE_TAC[VECTOR_ARITH `((l:real^2) + (a + b)) - l = a + b`] THEN
  ABBREV_TAC `bt = smooth_step(&2 * norm(x:real^2) / r - &1)` THEN
  SUBGOAL_THEN `abs bt <= &1` ASSUME_TAC THENL
   [EXPAND_TAC "bt" THEN
    MP_TAC(SPEC `&2 * norm(x:real^2) / r - &1` SMOOTH_STEP_BOUNDS) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `norm((G:real^2->real^2) x - L x) <= eta / (&4 * bB) * norm x`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!j. (j = 1 \/ j = 2)
        ==> norm(bt % (frechet_derivative (G:real^2->real^2) (at x) (basis j) -
                       (L:real^2->real^2) (basis j)) +
                 (moi_pdl_dstep (&2 * norm x / r - &1) *
                  &2 / r * (x dot basis j) / norm x) % (G x - L x)) <= eta`
  (fun th -> CONJ_TAC THEN MATCH_MP_TAC th THEN REWRITE_TAC[]) THEN
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `norm(frechet_derivative (G:real^2->real^2) (at x) (basis j) -
         (L:real^2->real^2) (basis j)) < eta / &2`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(DISJ_CASES_THEN SUBST1_TAC) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `abs bt * norm(frechet_derivative (G:real^2->real^2) (at x) (basis j) -
                  (L:real^2->real^2) (basis j)) +
    abs(moi_pdl_dstep (&2 * norm x / r - &1) *
        &2 / r * (x dot basis j) / norm x) * norm((G:real^2->real^2) x - L x)` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM NORM_MUL; NORM_TRIANGLE]; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH
   `a <= eta / &2 /\ b <= eta / &2 ==> a + b <= eta`) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&1 * norm(frechet_derivative (G:real^2->real^2) (at x)
                          (basis j) - (L:real^2->real^2) (basis j))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[NORM_POS_LE];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_PDL_LIN_ARITH THEN
  MAP_EVERY EXISTS_TAC [`bB:real`; `r:real`; `norm(x:real^2)`] THEN
  ASM_REWRITE_TAC[NORM_POS_LE] THEN CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC MOI_PDL_CJ_BOUND THEN ASM_REWRITE_TAC[MOI_PDL_DSTEP_POS] THEN
  FIRST_X_ASSUM(DISJ_CASES_THEN SUBST1_TAC) THEN
  SIMP_TAC[NORM_BASIS; DIMINDEX_2; ARITH; REAL_LE_REFL]);;

(* ========================================================================= *)
(* D2 part I, the angular lift of a homogeneous                             *)
(* injective map of the plane (degree one from injectivity and one point    *)
(* of positive angular speed).                                              *)
(* ========================================================================= *)

let MOI_PDL_HOM_BASICS = prove
 (`!P:complex->complex.
     (!t x. &0 <= t ==> P(t % x) = t % P x) /\ (!x y. P x = P y ==> x = y)
     ==> P(Cx(&0)) = Cx(&0) /\
         (!z. ~(z = Cx(&0)) ==> ~(P z = Cx(&0))) /\
         (!t z. &0 <= t ==> P(Cx t * z) = Cx t * P z)`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(P:complex->complex)(Cx(&0)) = Cx(&0)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`&0`; `Cx(&0)`]) THEN
    REWRITE_TAC[REAL_LE_REFL; VECTOR_MUL_LZERO; COMPLEX_VEC_0];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[]; ASM_SIMP_TAC[GSYM COMPLEX_CMUL]]);;

let MOI_PDL_ANGLE_LIFT = prove
 (`!P:complex->complex.
     P continuous_on (:complex) /\ (!z. ~(z = Cx(&0)) ==> ~(P z = Cx(&0)))
     ==> ?l. (l:real^1->complex) continuous_on (:real^1) /\
             !t. P(cexp(ii * Cx(drop t))) = cexp(ii * Cx(drop t)) * cexp(l t)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`\t:real^1. (P:complex->complex)(cexp(ii * Cx(drop t))) /
                cexp(ii * Cx(drop t))`; `(:real^1)`]
   CONTINUOUS_LOGARITHM_ON_CONTRACTIBLE) THEN
  REWRITE_TAC[IN_UNIV] THEN ANTS_TAC THENL
   [SIMP_TAC[CONVEX_IMP_CONTRACTIBLE; CONVEX_UNIV] THEN CONJ_TAC THENL
     [ALL_TAC;
      GEN_TAC THEN REWRITE_TAC[COMPLEX_DIV_EQ_0; CEXP_NZ] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[CEXP_NZ]] THEN
    SUBGOAL_THEN
     `(\t:real^1. cexp(ii * Cx(drop t))) continuous_on (:real^1)`
    ASSUME_TAC THENL
     [ONCE_REWRITE_TAC[GSYM o_DEF] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
      REWRITE_TAC[CONTINUOUS_ON_CEXP] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_LMUL THEN
      MATCH_MP_TAC CONTINUOUS_ON_CX_DROP THEN REWRITE_TAC[CONTINUOUS_ON_ID];
      ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_DIV THEN
    ASM_REWRITE_TAC[CEXP_NZ] THEN
    ONCE_REWRITE_TAC[GSYM o_DEF] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:complex)` THEN
    ASM_REWRITE_TAC[SUBSET_UNIV];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `l:real^1->complex` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `t:real^1` THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o SPEC `t:real^1`) THEN BETA_TAC THEN
  MATCH_MP_TAC(GSYM COMPLEX_DIV_LMUL) THEN REWRITE_TAC[CEXP_NZ]);;

let MOI_PDL_LIFT_PERIOD = prove
 (`!(P:complex->complex) l.
     (l:real^1->complex) continuous_on (:real^1) /\
     (!t. P(cexp(ii * Cx(drop t))) = cexp(ii * Cx(drop t)) * cexp(l t))
     ==> ?k. integer k /\
             !t. l(t + lift(&2 * pi)) = l t + Cx(&2 * k * pi) * ii`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!t. ?n. integer n /\ l(t + lift(&2 * pi)) = l t + Cx(&2 * n * pi) * ii`
  ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[GSYM CEXP_EQ] THEN
    MATCH_MP_TAC(GEN_ALL(COMPLEX_RING
     `~(e = Cx(&0)) /\ e * a = e * b ==> a = b`)) THEN
    EXISTS_TAC `cexp(ii * Cx(drop(t:real^1)))` THEN
    REWRITE_TAC[CEXP_NZ] THEN
    SUBGOAL_THEN `cexp(ii * Cx(drop(t + lift(&2 * pi)))) =
                  cexp(ii * Cx(drop(t:real^1)))`
    (LABEL_TAC "e2pi") THENL
     [REWRITE_TAC[DROP_ADD; LIFT_DROP; CX_ADD; COMPLEX_ADD_LDISTRIB;
                  CEXP_ADD; CEXP_2PII; COMPLEX_MUL_RID];
      ALL_TAC] THEN
    USE_THEN "e2pi" (fun th -> GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [GSYM th]) THEN
    FIRST_ASSUM((fun th -> REWRITE_TAC[GSYM th]) o
      check (fun th -> is_forall(concl th))) THEN
    USE_THEN "e2pi" (fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\t:real^1. l(t + lift(&2 * pi)) - (l:real^1->complex) t`;
                 `(:real^1)`] CONTINUOUS_DISCRETE_RANGE_CONSTANT) THEN
  REWRITE_TAC[CONNECTED_UNIV; IN_UNIV] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUB THEN REWRITE_TAC[ETA_AX] THEN
      ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[GSYM o_DEF] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
      SIMP_TAC[CONTINUOUS_ON_ADD; CONTINUOUS_ON_ID; CONTINUOUS_ON_CONST] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^1)` THEN
      ASM_REWRITE_TAC[SUBSET_UNIV];
      ALL_TAC] THEN
    X_GEN_TAC `x:real^1` THEN EXISTS_TAC `&2 * pi` THEN
    REWRITE_TAC[REAL_ARITH `&0 < &2 * x <=> &0 < x`; PI_POS] THEN
    X_GEN_TAC `y:real^1` THEN
    FIRST_ASSUM(X_CHOOSE_THEN `n1:real` STRIP_ASSUME_TAC o SPEC `x:real^1`) THEN
    FIRST_ASSUM(X_CHOOSE_THEN `n2:real` STRIP_ASSUME_TAC o SPEC `y:real^1`) THEN
    ASM_REWRITE_TAC[COMPLEX_RING `(a + b) - a = b:complex`] THEN
    REWRITE_TAC[GSYM COMPLEX_SUB_RDISTRIB; GSYM CX_SUB; COMPLEX_NORM_MUL;
                COMPLEX_NORM_II; COMPLEX_NORM_CX; REAL_MUL_RID] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `&1 <= abs(n2 - n1)` MP_TAC THENL
     [MATCH_MP_TAC REAL_ABS_INTEGER_LEMMA THEN ASM_SIMP_TAC[INTEGER_SUB] THEN
      DISCH_TAC THEN UNDISCH_TAC
       `~(Cx(&2 * n2 * pi) * ii = Cx(&2 * n1 * pi) * ii)` THEN
      SUBGOAL_THEN `n2:real = n1` SUBST1_TAC THENL
       [ASM_REAL_ARITH_TAC; REWRITE_TAC[]];
      ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_SUB_LDISTRIB; GSYM REAL_SUB_RDISTRIB] THEN
    REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_NUM] THEN
    MP_TAC PI_POS THEN SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`] THEN
    DISCH_TAC THEN DISCH_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `&1 * p <= a * p ==> &2 * p <= &2 * a * p`) THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `a:complex`) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `k:real` STRIP_ASSUME_TAC o SPEC `vec 0:real^1`) THEN
  EXISTS_TAC `k:real` THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `t:real^1` THEN
  FIRST_X_ASSUM(fun th -> MP_TAC(SPEC `t:real^1` th) THEN
                          MP_TAC(SPEC `vec 0:real^1` th)) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC COMPLEX_RING);;

let MOI_PDL_CEXP_IM_PERIOD = prove
 (`!w n. integer n /\ Im w = &2 * n * pi ==> cexp w = Cx(exp(Re w))`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [COMPLEX_EXPAND] THEN
  ASM_REWRITE_TAC[CEXP_ADD; CX_EXP] THEN
  MATCH_MP_TAC(COMPLEX_RING `b = Cx(&1) ==> a * b = a`) THEN
  ONCE_REWRITE_TAC[COMPLEX_MUL_SYM] THEN ASM_SIMP_TAC[CEXP_INTEGER_2PI]);;

let MOI_PDL_SAME_DIR = prove
 (`!(P:complex->complex) l s1 s2 n.
     (!t z. &0 <= t ==> P(Cx t * z) = Cx t * P z) /\
     (!x y. P x = P y ==> x = y) /\
     (!t. P(cexp(ii * Cx(drop t))) = cexp(ii * Cx(drop t)) * cexp(l t)) /\
     integer n /\
     (s1 + Im(l(lift s1))) - (s2 + Im(l(lift s2))) = &2 * n * pi
     ==> cexp(ii * Cx s1) = cexp(ii * Cx s2)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `w1 = ii * Cx s1 + l(lift s1)` THEN
  ABBREV_TAC `w2 = ii * Cx s2 + l(lift s2)` THEN
  SUBGOAL_THEN `(P:complex->complex)(cexp(ii * Cx s1)) = cexp w1 /\
                P(cexp(ii * Cx s2)) = cexp w2`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["w1"; "w2"] THEN REWRITE_TAC[CEXP_ADD] THEN
    CONJ_TAC THEN
    FIRST_X_ASSUM(fun th -> MP_TAC(SPEC `lift s1` th) THEN
                            MP_TAC(SPEC `lift s2` th)) THEN
    REWRITE_TAC[LIFT_DROP] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `cexp(w1 - w2) = Cx(exp(Re(w1 - w2)))` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_PDL_CEXP_IM_PERIOD THEN EXISTS_TAC `n:real` THEN
    ASM_REWRITE_TAC[] THEN MAP_EVERY EXPAND_TAC ["w1"; "w2"] THEN
    REWRITE_TAC[IM_SUB; IM_ADD; IM_MUL_II; RE_CX] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `lam = exp(Re(w1 - w2))` THEN
  SUBGOAL_THEN `&0 < lam` ASSUME_TAC THENL
   [EXPAND_TAC "lam" THEN REWRITE_TAC[REAL_EXP_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(P:complex->complex)(cexp(ii * Cx s1)) = P(Cx lam * cexp(ii * Cx s2))`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    SUBGOAL_THEN `cexp w1 = cexp(w1 - w2) * cexp w2` SUBST1_TAC THENL
     [REWRITE_TAC[GSYM CEXP_ADD] THEN AP_TERM_TAC THEN CONV_TAC COMPLEX_RING;
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(fun th -> MP_TAC(MATCH_MP th
    (ASSUME `(P:complex->complex)(cexp(ii * Cx s1)) =
             P(Cx lam * cexp(ii * Cx s2))`))) THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `lam = &1` (fun th -> ASM_REWRITE_TAC[th; COMPLEX_MUL_LID]) THEN
  FIRST_X_ASSUM(MP_TAC o AP_TERM `norm:complex->real`) THEN
  REWRITE_TAC[COMPLEX_NORM_MUL; NORM_CEXP_II; COMPLEX_NORM_CX] THEN
  ASM_REAL_ARITH_TAC);;

let MOI_PDL_CEXP_II_INJ = prove
 (`!s1 s2 a. a <= s1 /\ s1 < a + &2 * pi /\ a <= s2 /\ s2 < a + &2 * pi /\
             cexp(ii * Cx s1) = cexp(ii * Cx s2)
             ==> s1 = s2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CEXP_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
     (X_CHOOSE_THEN `n:real` STRIP_ASSUME_TAC))))) THEN
  FIRST_X_ASSUM(MP_TAC o AP_TERM `Im`) THEN
  REWRITE_TAC[IM_ADD; IM_MUL_II; RE_CX; IM_MUL_CX; IM_II; REAL_MUL_RID] THEN
  DISCH_TAC THEN
  ASM_CASES_TAC `n = &0` THENL
   [UNDISCH_TAC `s1 = s2 + &2 * n * pi` THEN
    ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_RZERO; REAL_ADD_RID];
    ALL_TAC] THEN
  MP_TAC(SPEC `n:real` REAL_ABS_INTEGER_LEMMA) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `&2 * pi * &1 <= abs(&2 * n * pi)` MP_TAC THENL
   [REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_NUM] THEN
    MP_TAC PI_POS THEN SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`] THEN
    DISCH_TAC THEN
    ONCE_REWRITE_TAC[REAL_ARITH `&2 * pi * x = &2 * x * pi`] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ASM_REAL_ARITH_TAC]);;

let MOI_PDL_MONO_END = prove
 (`!f a b c.
     f real_continuous_on real_interval[a,b] /\ a < c /\ c < b /\
     (!x y. a <= x /\ x < b /\ a <= y /\ y < b /\ f x = f y ==> x = y) /\
     f a < f c
     ==> f a < f b`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  ABBREV_TAC `y = ((f:real->real) a + f c) / &2` THEN
  MP_TAC(ISPECL [`f:real->real`; `c:real`; `b:real`; `y:real`]
    REAL_IVT_DECREASING) THEN
  MP_TAC(ISPECL [`f:real->real`; `a:real`; `c:real`; `y:real`]
    REAL_IVT_INCREASING) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
    MATCH_MP_TAC REAL_CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `real_interval[a,b]` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t1:real`
    (STRIP_ASSUME_TAC o REWRITE_RULE[IN_REAL_INTERVAL])) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
    MATCH_MP_TAC REAL_CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `real_interval[a,b]` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t2:real`
    (STRIP_ASSUME_TAC o REWRITE_RULE[IN_REAL_INTERVAL])) THEN
  SUBGOAL_THEN `(t2:real) < b` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_LT_LE] THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN SUBST_ALL_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(t1:real) < c` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_LT_LE] THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN SUBST_ALL_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(t1:real) = t2` MP_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC]);;

let MOI_PDL_PHI_CONT = prove
 (`!l. (l:real^1->complex) continuous_on (:real^1)
       ==> (\s. s + Im(l(lift s))) real_continuous_on (:real)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_CONTINUOUS_ON; IMAGE_LIFT_UNIV] THEN
  SUBGOAL_THEN
   `lift o (\s. s + Im((l:real^1->complex)(lift s))) o drop =
    (\x. x + lift((l x)$2))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_ADD; LIFT_DROP; IM_DEF]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_ADD THEN REWRITE_TAC[CONTINUOUS_ON_ID] THEN
  MATCH_MP_TAC CONTINUOUS_ON_LIFT_COMPONENT_COMPOSE THEN ASM_REWRITE_TAC[]);;

let MOI_PDL_DEGREE_ONE = prove
 (`!(P:complex->complex) l k t0 dl.
     (!t z. &0 <= t ==> P(Cx t * z) = Cx t * P z) /\
     (!x y. P x = P y ==> x = y) /\
     (l:real^1->complex) continuous_on (:real^1) /\
     (!t. P(cexp(ii * Cx(drop t))) = cexp(ii * Cx(drop t)) * cexp(l t)) /\
     integer k /\ (!t. l(t + lift(&2 * pi)) = l t + Cx(&2 * k * pi) * ii) /\
     &0 < dl /\
     (!t. t0 < t /\ t < t0 + dl
          ==> t0 + Im(l(lift t0)) < t + Im(l(lift t)))
     ==> k = &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `phi = \s. s + Im((l:real^1->complex)(lift s))` THEN
  SUBGOAL_THEN `phi real_continuous_on (:real)` ASSUME_TAC THENL
   [EXPAND_TAC "phi" THEN ASM_SIMP_TAC[MOI_PDL_PHI_CONT]; ALL_TAC] THEN
  SUBGOAL_THEN `!s. phi(s + &2 * pi) = phi s + &2 * pi * (&1 + k)`
  ASSUME_TAC THENL
   [EXPAND_TAC "phi" THEN GEN_TAC THEN REWRITE_TAC[LIFT_ADD] THEN
    ASM_REWRITE_TAC[IM_ADD; IM_MUL_II; RE_CX] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s1 s2 n. integer n /\ phi s1 - phi s2 = &2 * n * pi
              ==> cexp(ii * Cx s1) = cexp(ii * Cx s2)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_PDL_SAME_DIR THEN
    MAP_EVERY EXISTS_TAC [`P:complex->complex`; `l:real^1->complex`;
                          `n:real`] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(phi:real->real) s1 - phi s2 = &2 * n * pi` THEN
    EXPAND_TAC "phi" THEN REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `a = t0 - pi` THEN
  SUBGOAL_THEN
   `!x y. a <= x /\ x < a + &2 * pi /\ a <= y /\ y < a + &2 * pi /\
          (phi:real->real) x = phi y ==> x = y`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_PDL_CEXP_II_INJ THEN
    EXISTS_TAC `a:real` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `&0` THEN
    ASM_REWRITE_TAC[INTEGER_CLOSED] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`phi:real->real`; `{s | a <= s /\ s < a + &2 * pi}`]
    REAL_CONTINUOUS_INJECTIVE_IFF_MONOTONIC) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real)` THEN
      ASM_REWRITE_TAC[SUBSET_UNIV];
      REWRITE_TAC[is_realinterval; IN_ELIM_THM] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  DISCH_THEN(MP_TAC o fst o EQ_IMP_RULE) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `a < a + &2 * pi /\ a < t0 /\ t0 < a + &2 * pi`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "a" THEN MP_TAC PI_POS THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(phi:real->real) t0 < phi(t0 + min dl pi / &2)` ASSUME_TAC THENL
   [EXPAND_TAC "phi" THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    MP_TAC PI_POS THEN UNDISCH_TAC `&0 < dl` THEN
    REWRITE_TAC[REAL_MIN_LT; REAL_LT_MIN] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  STRIP_TAC THENL
   [ALL_TAC;
    FIRST_X_ASSUM(MP_TAC o SPECL [`t0:real`; `t0 + min dl pi / &2`]) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [MP_TAC PI_POS THEN UNDISCH_TAC `&0 < dl` THEN EXPAND_TAC "a" THEN
      REWRITE_TAC[REAL_MIN_LT; REAL_LT_MIN] THEN REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC]] THEN
  SUBGOAL_THEN `(phi:real->real) a < phi t0` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`phi:real->real`; `a:real`; `a + &2 * pi`; `t0:real`]
    MOI_PDL_MONO_END) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real)` THEN
    ASM_REWRITE_TAC[SUBSET_UNIV];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < &1 + k` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < (&1 + k) * (&2 * pi)` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC PI_POS THEN
    SIMP_TAC[REAL_LT_MUL_EQ; REAL_ARITH `&0 < pi ==> &0 < &2 * pi`];
    ALL_TAC] THEN
  ASM_CASES_TAC `k = &0` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPEC `k:real` REAL_ABS_INTEGER_LEMMA) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN SUBGOAL_THEN `&1 <= k` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`phi:real->real`; `a:real`; `a + &2 * pi`;
                 `(phi:real->real) a + &2 * pi`] REAL_IVT_INCREASING) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MP_TAC PI_POS THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real)` THEN
      ASM_REWRITE_TAC[SUBSET_UNIV];
      MP_TAC PI_POS THEN REAL_ARITH_TAC;
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `&0 <= pi * k` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN MP_TAC PI_POS THEN ASM_REAL_ARITH_TAC;
        REAL_ARITH_TAC]];
    ALL_TAC] THEN
  REWRITE_TAC[IN_REAL_INTERVAL] THEN
  DISCH_THEN(X_CHOOSE_THEN `t1:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `t1 < a + &2 * pi` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_LT_LE] THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `phi(a + &2 * pi) = phi a + &2 * pi` THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&0 < pi * k` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN MP_TAC PI_POS THEN ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `t1:real = a` MP_TAC THENL
   [MATCH_MP_TAC MOI_PDL_CEXP_II_INJ THEN EXISTS_TAC `a:real` THEN
    ASM_REWRITE_TAC[REAL_LE_REFL] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (find_term ((=) `cexp`)) (concl th))) THEN
    EXISTS_TAC `&1` THEN ASM_REWRITE_TAC[INTEGER_CLOSED] THEN REAL_ARITH_TAC;
    DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `(phi:real->real) a = phi a + &2 * pi` THEN MP_TAC PI_POS THEN
    REAL_ARITH_TAC]);;

let MOI_PDL_E_DERIV = prove
 (`!t0. ((\t. cexp(ii * Cx(drop t))) has_vector_derivative
         (ii * cexp(ii * Cx(drop t0)))) (at t0)`,
  GEN_TAC THEN
  MP_TAC(ISPECL [`\z. cexp(ii * z)`; `ii * cexp(ii * Cx(drop t0))`;
                 `t0:real^1`] (GEN_ALL HAS_VECTOR_DERIVATIVE_REAL_COMPLEX)) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  COMPLEX_DIFF_TAC THEN REWRITE_TAC[COMPLEX_MUL_SYM; COMPLEX_MUL_RID]);;

let MOI_PDL_RADIAL_DERIV = prove
 (`!(g:real^M->real^N) x d.
     g differentiable (at x) /\ &0 < d /\
     (!t. abs(t - &1) < d ==> g(t % x) = t % g x)
     ==> frechet_derivative g (at x) x = g x`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `((\t:real^1. (g:real^M->real^N)(drop t % x)) has_derivative
     (\t. frechet_derivative g (at x) (drop t % x))) (at (lift(&1)))`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `(\t:real^1. (g:real^M->real^N)(drop t % x)) = g o (\t. drop t % x)`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    SUBGOAL_THEN
     `(\t:real^1. frechet_derivative (g:real^M->real^N) (at x) (drop t % x)) =
      frechet_derivative g (at x) o (\t. drop t % x)`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC DIFF_CHAIN_AT THEN CONJ_TAC THENL
     [MATCH_MP_TAC HAS_DERIVATIVE_VMUL_DROP THEN REWRITE_TAC[HAS_DERIVATIVE_ID];
      REWRITE_TAC[LIFT_DROP; VECTOR_MUL_LID] THEN
      ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\t:real^1. (g:real^M->real^N)(drop t % x)) has_derivative
     (\t. drop t % g x)) (at (lift(&1)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_AT THEN
    MAP_EVERY EXISTS_TAC [`\t:real^1. drop t % (g:real^M->real^N) x`; `d:real`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[dist; NORM_REAL; GSYM drop; DROP_SUB; LIFT_DROP] THEN
      REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC HAS_DERIVATIVE_VMUL_DROP THEN REWRITE_TAC[HAS_DERIVATIVE_ID]];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP FRECHET_DERIVATIVE_UNIQUE_AT o CONJ
   (ASSUME `((\t:real^1. (g:real^M->real^N)(drop t % x)) has_derivative
     (\t. frechet_derivative g (at x) (drop t % x))) (at (lift(&1)))`)) THEN
  DISCH_THEN(MP_TAC o C AP_THM `lift(&1)`) THEN
  REWRITE_TAC[LIFT_DROP; VECTOR_MUL_LID]);;

let MOI_PDL_IM_INCREASE = prove
 (`!(L:real^1->complex) L' t0.
     (L has_vector_derivative L') (at (lift t0)) /\ &0 < Im L'
     ==> ?d. &0 < d /\
             !t. t0 < t /\ t < t0 + d ==> Im(L(lift t0)) < Im(L(lift t))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[has_vector_derivative] THEN
  REWRITE_TAC[HAS_DERIVATIVE_AT_ALT] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `Im L' / &2`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `t:real` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `lift t`) THEN
  REWRITE_TAC[GSYM LIFT_SUB; NORM_LIFT; DROP_SUB; LIFT_DROP] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (REAL_ARITH
   `norm(z:complex) <= e ==> abs(Im z) <= norm z ==> abs(Im z) <= e`)) THEN
  REWRITE_TAC[COMPLEX_NORM_GE_RE_IM; IM_SUB; IM_CMUL] THEN
  SUBGOAL_THEN `abs(t - t0) = t - t0` SUBST1_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (t - t0) * Im L'` MP_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REAL_ARITH_TAC);;

let MOI_PDL_LOG_DERIV_1D = prove
 (`!(L:real^1->complex) gam gam' t0 d.
     &0 < d /\ L continuous (at t0) /\
     (!t. norm(t - t0) < d ==> cexp(L t) = gam t) /\
     (gam has_vector_derivative gam') (at t0)
     ==> (L has_vector_derivative (gam' / gam t0)) (at t0)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(gam(t0:real^1) = Cx(&0))` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `t0:real^1`) THEN
    ASM_REWRITE_TAC[VECTOR_SUB_REFL; NORM_0] THEN MESON_TAC[CEXP_NZ];
    ALL_TAC] THEN
  UNDISCH_TAC `(L:real^1->complex) continuous (at t0)` THEN
  REWRITE_TAC[continuous_at; dist] THEN
  DISCH_THEN(MP_TAC o SPEC `&1`) THEN REWRITE_TAC[REAL_LT_01] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_TRANSFORM_AT THEN
  EXISTS_TAC `\t:real^1. L t0 + clog(gam t / gam t0)` THEN
  EXISTS_TAC `min d d1` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN CONJ_TAC THENL
   [X_GEN_TAC `t:real^1` THEN REWRITE_TAC[dist] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(gam:real^1->complex) t / gam t0 = cexp(L t - L t0)`
    SUBST1_TAC THENL
     [REWRITE_TAC[CEXP_SUB] THEN BINOP_TAC THEN
      CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[VECTOR_SUB_REFL; NORM_0];
      ALL_TAC] THEN
    SUBGOAL_THEN `clog(cexp(L t - L(t0:real^1))) = L t - L t0` SUBST1_TAC THENL
     [MATCH_MP_TAC CLOG_CEXP THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `t:real^1`) THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(SPEC `(L:real^1->complex) t - L t0` COMPLEX_NORM_GE_RE_IM) THEN
      MP_TAC PI_APPROX_32 THEN REAL_ARITH_TAC;
      CONV_TAC COMPLEX_RING];
    ALL_TAC] THEN
  SUBGOAL_THEN `gam' / (gam:real^1->complex) t0 = Cx(&0) + gam' / gam t0`
  SUBST1_TAC THENL [CONV_TAC COMPLEX_RING; ALL_TAC] THEN
  MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_ADD THEN
  REWRITE_TAC[GSYM COMPLEX_VEC_0; HAS_VECTOR_DERIVATIVE_CONST] THEN
  REWRITE_TAC[COMPLEX_VEC_0; COMPLEX_ADD_LID] THEN
  UNDISCH_TAC `((gam:real^1->complex) has_vector_derivative gam') (at t0)` THEN
  REWRITE_TAC[has_vector_derivative] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `(\t:real^1. clog((gam:real^1->complex) t / gam t0)) =
    clog o (\z. inv(gam t0) * z) o gam`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; complex_div; COMPLEX_MUL_SYM]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(\x:real^1. drop x % (gam' / (gam:real^1->complex) t0)) =
    (\z. inv(Cx(&1)) * z) o (\z. inv(gam t0) * z) o (\x. drop x % gam')`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; COMPLEX_CMUL] THEN GEN_TAC THEN
    UNDISCH_TAC `~((gam:real^1->complex) t0 = Cx(&0))` THEN
    CONV_TAC COMPLEX_FIELD;
    ALL_TAC] THEN
  MATCH_MP_TAC DIFF_CHAIN_AT THEN CONJ_TAC THENL
   [MATCH_MP_TAC DIFF_CHAIN_AT THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN REWRITE_TAC[LINEAR_COMPLEX_MUL];
    ALL_TAC] THEN
  REWRITE_TAC[o_THM] THEN
  SUBGOAL_THEN `inv((gam:real^1->complex) t0) * gam t0 = Cx(&1)` SUBST1_TAC
  THENL [ASM_SIMP_TAC[COMPLEX_MUL_LINV]; ALL_TAC] THEN
  REWRITE_TAC[GSYM has_complex_derivative] THEN
  MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_CLOG THEN
  REWRITE_TAC[RE_CX] THEN REAL_ARITH_TAC);;

let MOI_PDL_SOME_INTERIOR = prove
 (`!(S:num->real^N->bool) n.
     (!i. i < n ==> closed(S i)) /\ UNIONS {S i | i < n} = (:real^N)
     ==> ?i z. i < n /\ z IN interior(S i) /\ ~(z = vec 0)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?i. i < n /\ ~(interior((S:num->real^N->bool) i) = {})`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
    DISCH_THEN(ASSUME_TAC o REWRITE_RULE
      [NOT_EXISTS_THM; TAUT `~(a /\ ~b) <=> a ==> b`]) THEN
    MP_TAC(ISPEC `{(S:num->real^N->bool) i | i < n}`
      NOWHERE_DENSE_COUNTABLE_UNIONS_CLOSED) THEN
    ASM_REWRITE_TAC[INTERIOR_UNIV; UNIV_NOT_EMPTY] THEN
    ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
    REWRITE_TAC[FORALL_IN_IMAGE; IN_ELIM_THM] THEN
    ASM_SIMP_TAC[FINITE_IMP_COUNTABLE; FINITE_IMAGE; FINITE_NUMSEG_LT];
    ALL_TAC] THEN
  MP_TAC(ISPEC `interior((S:num->real^N->bool) i)` OPEN_IMP_INFINITE) THEN
  ASM_REWRITE_TAC[OPEN_INTERIOR; INFINITE] THEN DISCH_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
  DISCH_THEN(ASSUME_TAC o REWRITE_RULE[NOT_EXISTS_THM]) THEN
  UNDISCH_TAC `~FINITE(interior((S:num->real^N->bool) i))` THEN
  REWRITE_TAC[] THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `{vec 0:real^N}` THEN REWRITE_TAC[FINITE_SING; SUBSET; IN_SING] THEN
  X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`i:num`; `z:real^N`]) THEN
  ASM_REWRITE_TAC[]);;

let MOI_PDL_ORIENT_LOCAL = prove
 (`!(g:complex->complex) u l t0 d.
     open u /\ smooth_map_on u g /\ cexp(ii * Cx t0) IN u /\ &0 < d /\
     (l:real^1->complex) continuous_on (:real^1) /\
     (!t. norm(t - lift t0) < d
          ==> g(cexp(ii * Cx(drop t))) = cexp(ii * Cx(drop t)) * cexp(l t)) /\
     (!s. abs(s - &1) < d
          ==> g(s % cexp(ii * Cx t0)) = s % g(cexp(ii * Cx t0))) /\
     &0 < det(jacobian g (at (cexp(ii * Cx t0))))
     ==> ?dl. &0 < dl /\
              !t. t0 < t /\ t < t0 + dl
                  ==> t0 + Im(l(lift t0)) < t + Im(l(lift t))`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `e0 = cexp(ii * Cx t0)` THEN
  SUBGOAL_THEN `(g:complex->complex) differentiable (at e0)` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `u:complex->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((g:complex->complex) has_derivative frechet_derivative g (at e0)) (at e0) /\
    linear (frechet_derivative (g:complex->complex) (at e0))`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[LINEAR_FRECHET_DERIVATIVE] THEN
    ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS];
    ALL_TAC] THEN
  ABBREV_TAC `T0 = frechet_derivative (g:complex->complex) (at e0)` THEN
  SUBGOAL_THEN `(T0:complex->complex) e0 = g e0` ASSUME_TAC THENL
   [EXPAND_TAC "T0" THEN MATCH_MP_TAC MOI_PDL_RADIAL_DERIV THEN
    EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\t. (g:complex->complex)(cexp(ii * Cx(drop t)))) has_vector_derivative
     (T0:complex->complex)(ii * e0)) (at (lift t0))`
  ASSUME_TAC THENL
   [MP_TAC(SPEC `lift t0` MOI_PDL_E_DERIV) THEN
    ASM_REWRITE_TAC[LIFT_DROP; has_vector_derivative] THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `(\t. (g:complex->complex)(cexp(ii * Cx(drop t)))) =
      g o (\t. cexp(ii * Cx(drop t)))`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    SUBGOAL_THEN
     `(\x:real^1. drop x % (T0:complex->complex)(ii * e0)) =
      T0 o (\x. drop x % (ii * e0))`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM] THEN ASM_SIMP_TAC[LINEAR_CMUL];
      ALL_TAC] THEN
    MATCH_MP_TAC DIFF_CHAIN_AT THEN ASM_REWRITE_TAC[LIFT_DROP];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\t. ii * Cx(drop t) + (l:real^1->complex) t) has_vector_derivative
     ((T0:complex->complex)(ii * e0) / g e0)) (at (lift t0))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL
     [`\t. ii * Cx(drop t) + (l:real^1->complex) t`;
      `\t. (g:complex->complex)(cexp(ii * Cx(drop t)))`;
      `(T0:complex->complex)(ii * e0)`; `lift t0`; `d:real`]
     MOI_PDL_LOG_DERIV_1D) THEN
    ASM_REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ADD THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_COMPLEX_MUL THEN
        REWRITE_TAC[CONTINUOUS_CONST] THEN
        MATCH_MP_TAC LINEAR_CONTINUOUS_AT THEN
        REWRITE_TAC[linear; DROP_ADD; DROP_CMUL; CX_ADD; CX_MUL;
                    COMPLEX_CMUL];
        UNDISCH_TAC `(l:real^1->complex) continuous_on (:real^1)` THEN
        SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_AT; OPEN_UNIV; IN_UNIV]];
      X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN
      ASM_SIMP_TAC[CEXP_ADD]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\t. ii * Cx(drop t) + (l:real^1->complex) t`;
                 `(T0:complex->complex)(ii * e0) / g e0`; `t0:real`]
    MOI_PDL_IM_INCREASE) THEN
  REWRITE_TAC[IM_ADD; IM_MUL_II; RE_CX; LIFT_DROP] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
    concl th = `(T0:complex->complex) e0 = g e0`)) THEN
  ONCE_REWRITE_TAC[COMPLEX_DIV_CNJ] THEN REWRITE_TAC[GSYM CX_POW; IM_DIV_CX] THEN
  MP_TAC(ISPECL [`T0:complex->complex`; `e0:complex`] MOI_PDL_DET_ROT) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `norm(e0:complex) = &1` SUBST1_TAC THENL
   [EXPAND_TAC "e0" THEN REWRITE_TAC[NORM_CEXP_II]; ALL_TAC] THEN
  UNDISCH_TAC `&0 < det(jacobian (g:complex->complex) (at e0))` THEN
  ASM_REWRITE_TAC[jacobian] THEN
  REWRITE_TAC[REAL_POW_ONE; REAL_MUL_LID] THEN REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[COMPLEX_MUL_SYM] THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_POW_LT THEN REWRITE_TAC[COMPLEX_NORM_NZ] THEN
  DISCH_TAC THEN
  UNDISCH_TAC `Im(cnj((T0:complex->complex) e0) * T0(ii * e0)) =
               det(matrix T0)` THEN
  ASM_REWRITE_TAC[CNJ_CX; COMPLEX_MUL_LZERO; IM_CX] THEN
  ASM_REAL_ARITH_TAC);;

let MOI_PDL_ORIENT = prove
 (`!(P:complex->complex) (S:num->complex->bool) n l.
     (!t z. &0 <= t ==> P(Cx t * z) = Cx t * P z) /\
     (!i. i < n ==> closed(S i) /\ conic(S i)) /\
     UNIONS {S i | i < n} = (:complex) /\
     (!i. i < n
          ==> ?u g. open u /\ S i DIFF {vec 0} SUBSET u /\ smooth_map_on u g /\
                    (!x. x IN S i ==> g x = P x) /\
                    (!x. x IN S i DIFF {vec 0}
                         ==> &0 < det(jacobian g (at x)))) /\
     (l:real^1->complex) continuous_on (:real^1) /\
     (!t. P(cexp(ii * Cx(drop t))) = cexp(ii * Cx(drop t)) * cexp(l t))
     ==> ?t0 dl. &0 < dl /\
                 !t. t0 < t /\ t < t0 + dl
                     ==> t0 + Im(l(lift t0)) < t + Im(l(lift t))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`S:num->complex->bool`; `n:num`] MOI_PDL_SOME_INTERIOR) THEN
  ASM_SIMP_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `i:num` (X_CHOOSE_THEN `z:complex`
    STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:complex->bool` (X_CHOOSE_THEN
    `g:complex->complex` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `closed((S:num->complex->bool) i) /\ conic(S i)`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  EXISTS_TAC `Arg z` THEN
  ABBREV_TAC `e0 = cexp(ii * Cx(Arg z))` THEN
  SUBGOAL_THEN `z = Cx(norm(z:complex)) * e0 /\ &0 < norm(z:complex)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "e0" THEN REWRITE_TAC[GSYM ARG] THEN
    ASM_REWRITE_TAC[NORM_POS_LT; GSYM COMPLEX_VEC_0];
    ALL_TAC] THEN
  UNDISCH_TAC `(z:complex) IN interior((S:num->complex->bool) i)` THEN
  REWRITE_TAC[IN_INTERIOR] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `?d. &0 < d /\
        !t. norm(t - lift(Arg z)) < d
            ==> norm(cexp(ii * Cx(drop t)) - e0) < r / norm(z:complex)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(SPEC `lift(Arg z)` MOI_PDL_E_DERIV) THEN
    DISCH_THEN(MP_TAC o MATCH_MP HAS_VECTOR_DERIVATIVE_IMP_DIFFERENTIABLE) THEN
    DISCH_THEN(MP_TAC o MATCH_MP DIFFERENTIABLE_IMP_CONTINUOUS_AT) THEN
    REWRITE_TAC[continuous_at; dist; LIFT_DROP] THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_SIMP_TAC[REAL_LT_DIV];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t. norm(t - lift(Arg z)) < d
        ==> cexp(ii * Cx(drop t)) IN (S:num->complex->bool) i DIFF {vec 0}`
  ASSUME_TAC THENL
   [X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN
    REWRITE_TAC[IN_DIFF; IN_SING; COMPLEX_VEC_0; CEXP_NZ] THEN
    SUBGOAL_THEN
     `Cx(norm(z:complex)) * cexp(ii * Cx(drop t)) IN (S:num->complex->bool) i`
    ASSUME_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
        can (term_match [] `ball(x:complex,e) SUBSET s`) (concl th))) THEN
      REWRITE_TAC[IN_BALL] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `t:real^1`) THEN ASM_REWRITE_TAC[] THEN
      DISCH_TAC THEN
      SUBGOAL_THEN
       `dist(z,Cx(norm(z:complex)) * cexp(ii * Cx(drop t))) =
        norm z * norm(cexp(ii * Cx(drop t)) - e0)`
      SUBST1_TAC THENL
       [GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o LAND_CONV) [ASSUME
          `z = Cx(norm(z:complex)) * e0`] THEN
        REWRITE_TAC[dist; GSYM COMPLEX_SUB_LDISTRIB; COMPLEX_NORM_MUL;
                    COMPLEX_NORM_CX; REAL_ABS_NORM] THEN
        AP_TERM_TAC THEN REWRITE_TAC[NORM_SUB];
        ALL_TAC] THEN
      UNDISCH_TAC `norm(cexp(ii * Cx(drop t)) - e0) < r / norm(z:complex)` THEN
      ASM_SIMP_TAC[REAL_LT_RDIV_EQ] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `cexp(ii * Cx(drop t)) =
      inv(norm(z:complex)) % (Cx(norm z) * cexp(ii * Cx(drop t)))`
    SUBST1_TAC THENL
     [REWRITE_TAC[COMPLEX_CMUL; COMPLEX_MUL_ASSOC; GSYM CX_MUL] THEN
      ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ; COMPLEX_MUL_LID];
      MATCH_MP_TAC CONIC_MUL THEN ASM_REWRITE_TAC[REAL_LE_INV_EQ; NORM_POS_LE]];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_PDL_ORIENT_LOCAL THEN
  MAP_EVERY EXISTS_TAC [`g:complex->complex`; `u:complex->bool`;
                        `min d (&1)`] THEN
  ASM_REWRITE_TAC[REAL_LT_MIN; REAL_LT_01] THEN
  SUBGOAL_THEN `e0 IN (S:num->complex->bool) i DIFF {vec 0}` ASSUME_TAC THENL
   [EXPAND_TAC "e0" THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `lift(Arg z)`) THEN
    ASM_REWRITE_TAC[VECTOR_SUB_REFL; NORM_0; LIFT_DROP];
    ALL_TAC] THEN
  SUBGOAL_THEN `(e0:complex) IN u /\ e0 IN (S:num->complex->bool) i`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `e0 IN (S:num->complex->bool) i DIFF {vec 0}` THEN
    UNDISCH_TAC `(S:num->complex->bool) i DIFF {vec 0} SUBSET u` THEN
    SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `t:real^1`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[IN_DIFF] THEN STRIP_TAC THEN ASM_SIMP_TAC[];
    X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    SUBGOAL_THEN `s % e0 IN (S:num->complex->bool) i` ASSUME_TAC THENL
     [MATCH_MP_TAC CONIC_MUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN REWRITE_TAC[COMPLEX_CMUL] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (term_match [] `!t z. &0 <= t ==> (P:complex->complex)(Cx t * z) = Cx t * P z`)
          (concl th))) THEN
    ASM_REAL_ARITH_TAC;
    UNDISCH_TAC `e0 IN (S:num->complex->bool) i DIFF {vec 0}` THEN
    ASM_SIMP_TAC[]]);;

let MOI_PDL_L_PERIODIC = prove
 (`!l:real^1->complex.
     (!t. l(t + lift(&2 * pi)) = l t)
     ==> !t1 t2. cexp(ii * Cx(drop t1)) = cexp(ii * Cx(drop t2))
                 ==> l t1 = l t2`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `!m t. (l:real^1->complex)(t + lift(&2 * &m * pi)) = l t`
  ASSUME_TAC THENL
   [INDUCT_TAC THEN
    REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_RZERO; LIFT_NUM; VECTOR_ADD_RID] THEN
    GEN_TAC THEN REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN
    SUBGOAL_THEN `t + lift(&2 * (&m + &1) * pi) =
                  (t + lift(&2 * &m * pi)) + lift(&2 * pi)`
    SUBST1_TAC THENL
     [REWRITE_TAC[GSYM VECTOR_ADD_ASSOC; GSYM LIFT_ADD] THEN
      AP_TERM_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[CEXP_EQ] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `t1 = t2 + lift(&2 * n * pi)` SUBST1_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o AP_TERM `Im`) THEN
    REWRITE_TAC[IM_ADD; IM_MUL_II; RE_CX; IM_MUL_CX; IM_II; REAL_MUL_RID] THEN
    REWRITE_TAC[GSYM DROP_EQ; DROP_ADD; LIFT_DROP] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(DISJ_CASES_THEN (X_CHOOSE_THEN `m:num` SUBST1_TAC) o
    GEN_REWRITE_RULE I [INTEGER_CASES]) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`m:num`; `t2 + lift(&2 * -- &m * pi)`]) THEN
  REWRITE_TAC[GSYM VECTOR_ADD_ASSOC; GSYM LIFT_ADD] THEN
  REWRITE_TAC[REAL_ARITH `&2 * -- m * pi + &2 * m * pi = &0`; LIFT_NUM;
              VECTOR_ADD_RID] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[]);;

let MOI_PDL_ARG_E = prove
 (`!z. ~(z = Cx(&0)) ==> cexp(ii * Cx(Arg z)) = z / Cx(norm z)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(Cx(norm(z:complex)) = Cx(&0))` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[CX_INJ; NORM_EQ_0; COMPLEX_VEC_0]; ALL_TAC] THEN
  MP_TAC(SPEC `z:complex` ARG) THEN
  DISCH_THEN(fun th -> GEN_REWRITE_TAC (RAND_CONV o LAND_CONV)
    [last(CONJUNCTS th)]) THEN
  UNDISCH_TAC `~(Cx(norm(z:complex)) = Cx(&0))` THEN CONV_TAC COMPLEX_FIELD);;

let MOI_PDL_ARG_E_NEG = prove
 (`!z. ~(z = Cx(&0)) ==> cexp(ii * Cx(Arg(--z) + pi)) = z / Cx(norm z)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[CX_ADD; COMPLEX_ADD_LDISTRIB; CEXP_ADD; CEXP_II_PI] THEN
  MP_TAC(SPEC `--z:complex` MOI_PDL_ARG_E) THEN
  ASM_REWRITE_TAC[COMPLEX_NEG_EQ_0; NORM_NEG] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[complex_div] THEN
  CONV_TAC COMPLEX_RING);;

let MOI_PDL_LW_CONT = prove
 (`!l:real^1->complex.
     l continuous_on (:real^1) /\
     (!t1 t2. cexp(ii * Cx(drop t1)) = cexp(ii * Cx(drop t2)) ==> l t1 = l t2)
     ==> (\z. l(lift(Arg z))) continuous_on ((:complex) DIFF {Cx(&0)})`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!x:real^1. (l:real^1->complex) continuous at x` ASSUME_TAC THENL
   [UNDISCH_TAC `(l:real^1->complex) continuous_on (:real^1)` THEN
    SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_AT; OPEN_UNIV; IN_UNIV];
    ALL_TAC] THEN
  SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_AT; OPEN_DIFF; OPEN_UNIV; CLOSED_SING] THEN
  X_GEN_TAC `z0:complex` THEN REWRITE_TAC[IN_DIFF; IN_UNIV; IN_SING] THEN
  DISCH_TAC THEN ASM_CASES_TAC `real z0 /\ &0 <= Re z0` THENL
   [ALL_TAC;
    ONCE_REWRITE_TAC[GSYM o_DEF] THEN MATCH_MP_TAC CONTINUOUS_AT_COMPOSE THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(SPEC `z0:complex` REAL_CONTINUOUS_AT_ARG) THEN
    ASM_REWRITE_TAC[REAL_CONTINUOUS_CONTINUOUS1; o_DEF]] THEN
  MATCH_MP_TAC CONTINUOUS_TRANSFORM_AT THEN
  EXISTS_TAC `\z. (l:real^1->complex)(lift(Arg(--z) + pi))` THEN
  EXISTS_TAC `norm(z0:complex)` THEN
  ASM_REWRITE_TAC[NORM_POS_LT; COMPLEX_VEC_0] THEN CONJ_TAC THENL
   [X_GEN_TAC `z:complex` THEN REWRITE_TAC[dist] THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[LIFT_DROP] THEN
    SUBGOAL_THEN `~(z = Cx(&0))` ASSUME_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC `norm(z - z0:complex) < norm z0` THEN
      ASM_REWRITE_TAC[COMPLEX_SUB_LZERO; NORM_NEG; REAL_LT_REFL];
      ASM_SIMP_TAC[MOI_PDL_ARG_E; MOI_PDL_ARG_E_NEG]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\z. (l:real^1->complex)(lift(Arg(--z) + pi))) =
                l o (\x. x + lift pi) o (lift o Arg) o (\z. --z)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_ADD]; ALL_TAC] THEN
  REPEAT(MATCH_MP_TAC CONTINUOUS_AT_COMPOSE THEN CONJ_TAC) THEN
  ASM_SIMP_TAC[CONTINUOUS_NEG; CONTINUOUS_AT_ID; CONTINUOUS_ADD;
               CONTINUOUS_CONST] THEN
  REWRITE_TAC[o_THM; GSYM REAL_CONTINUOUS_CONTINUOUS1] THEN
  MATCH_MP_TAC REAL_CONTINUOUS_AT_ARG THEN
  UNDISCH_TAC `real z0 /\ &0 <= Re z0` THEN UNDISCH_TAC `~(z0 = Cx(&0))` THEN
  REWRITE_TAC[real; RE_NEG; IM_NEG; COMPLEX_EQ; RE_CX; IM_CX] THEN
  REAL_ARITH_TAC);;

let MOI_PDL_GLOBAL_LOG = prove
 (`!(P:complex->complex) (S:num->complex->bool) n.
     P continuous_on (:complex) /\
     (!t x. &0 <= t ==> P(t % x) = t % P x) /\
     (!x y. P x = P y ==> x = y) /\
     (!i. i < n ==> closed(S i) /\ convex(S i) /\ conic(S i)) /\
     UNIONS {S i | i < n} = (:complex) /\
     (!i. i < n
          ==> ?u g. open u /\ S i DIFF {vec 0} SUBSET u /\ smooth_map_on u g /\
                    (!x. x IN S i ==> g x = P x) /\
                    (!x. x IN S i DIFF {vec 0}
                         ==> &0 < det(jacobian g (at x))))
     ==> ?lw. lw continuous_on ((:complex) DIFF {Cx(&0)}) /\
              (!z. ~(z = Cx(&0)) ==> P z = z * cexp(lw z)) /\
              (!z t. ~(z = Cx(&0)) /\ &0 < t ==> lw(Cx t * z) = lw z)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `P:complex->complex` MOI_PDL_HOM_BASICS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(SPEC `P:complex->complex` MOI_PDL_ANGLE_LIFT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `l:real^1->complex`
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "lift"))) THEN
  MP_TAC(ISPECL [`P:complex->complex`; `l:real^1->complex`]
    MOI_PDL_LIFT_PERIOD) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "per"))) THEN
  MP_TAC(ISPECL [`P:complex->complex`; `S:num->complex->bool`; `n:num`;
                 `l:real^1->complex`] MOI_PDL_ORIENT) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t0:real` (X_CHOOSE_THEN `dl:real`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`P:complex->complex`; `l:real^1->complex`; `k:real`;
                 `t0:real`; `dl:real`] MOI_PDL_DEGREE_ONE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN `!t. (l:real^1->complex)(t + lift(&2 * pi)) = l t`
  ASSUME_TAC THENL
   [GEN_TAC THEN USE_THEN "per" (fun th -> REWRITE_TAC[th]) THEN
    ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_RZERO; COMPLEX_MUL_LZERO;
                    COMPLEX_ADD_RID];
    ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MOI_PDL_L_PERIODIC) THEN
  EXISTS_TAC `\z. (l:real^1->complex)(lift(Arg z))` THEN REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MOI_PDL_LW_CONT THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `z:complex` THEN DISCH_TAC THEN
    MP_TAC(SPEC `z:complex` ARG) THEN
    DISCH_THEN(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV)
      [last(CONJUNCTS th)]) THEN
    ASM_SIMP_TAC[NORM_POS_LE] THEN
    USE_THEN "lift" (MP_TAC o SPEC `lift(Arg z)`) THEN
    REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN SUBST1_TAC THEN
    MP_TAC(SPEC `z:complex` ARG) THEN
    DISCH_THEN(fun th -> GEN_REWRITE_TAC (RAND_CONV o LAND_CONV)
      [last(CONJUNCTS th)]) THEN
    CONV_TAC COMPLEX_RING;
    SIMP_TAC[ARG_MUL_CX]]);;

(* ========================================================================= *)
(* D2 part II, smooth homogeneous logarithms on cone                        *)
(* neighbourhoods of the pieces.                                            *)
(* ========================================================================= *)

(* Twin of SMT_SMOOTH_CONTINUOUS_LOG in pc_smt_rn.ml; kept here to avoid     *)
(* loading pc_smt_rn.ml (proved here through the principal logarithm).      *)

let MOI_PDL_CLOG_SMOOTH = prove
 (`!s (f:real^N->complex) g.
     open s /\ smooth_map_on s f /\ g continuous_on s /\
     (!x. x IN s ==> f x = cexp(g x))
     ==> smooth_map_on s g`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[smooth_map_on] THEN GEN_TAC THEN
  ASM_SIMP_TAC[CONTINUOUSLY_DIFFERENTIABLE_LOCAL_OPEN] THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  SUBGOAL_THEN `~((f:real^N->complex) x = Cx(&0))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[CEXP_NZ]; ALL_TAC] THEN
  SUBGOAL_THEN
   `?d. &0 < d /\ ball(x,d) SUBSET s /\
        !y. y IN ball(x,d)
            ==> norm((g:real^N->complex) y - g x) < &1 /\
                norm((f:real^N->complex) y / f x - Cx(&1)) < &1`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(g:real^N->complex) continuous_on s` THEN
    UNDISCH_TAC `smooth_map_on s (f:real^N->complex)` THEN
    DISCH_THEN(MP_TAC o MATCH_MP SMOOTH_MAP_ON_CONTINUOUS_ON) THEN
    SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_AT; ASSUME `open(s:real^N->bool)`] THEN
    DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[continuous_at] THEN
    DISCH_THEN(MP_TAC o SPEC `norm((f:real^N->complex) x)`) THEN
    ASM_REWRITE_TAC[COMPLEX_NORM_NZ] THEN
    DISCH_THEN(X_CHOOSE_THEN `d2:real` STRIP_ASSUME_TAC) THEN
    DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `&1`) THEN REWRITE_TAC[REAL_LT_01] THEN
    DISCH_THEN(X_CHOOSE_THEN `d1:real` STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC `open(s:real^N->bool)` THEN
    REWRITE_TAC[OPEN_CONTAINS_BALL] THEN
    DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `d0:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `min d0 (min d1 d2)` THEN
    ASM_REWRITE_TAC[REAL_LT_MIN] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `ball(x:real^N,d0)` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_BALL THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    X_GEN_TAC `y:real^N` THEN REWRITE_TAC[IN_BALL; REAL_LT_MIN] THEN
    STRIP_TAC THEN CONJ_TAC THENL
     [ONCE_REWRITE_TAC[GSYM DIST_SYM] THEN REWRITE_TAC[GSYM dist] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ONCE_REWRITE_TAC[DIST_SYM] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `(f:real^N->complex) y / f x - Cx(&1) = (f y - f x) / f x`
    SUBST1_TAC THENL
     [UNDISCH_TAC `~((f:real^N->complex) x = Cx(&0))` THEN
      CONV_TAC COMPLEX_FIELD;
      ALL_TAC] THEN
    SIMP_TAC[COMPLEX_NORM_DIV; REAL_LT_LDIV_EQ; COMPLEX_NORM_NZ;
             ASSUME `~((f:real^N->complex) x = Cx(&0))`] THEN
    REWRITE_TAC[REAL_MUL_LID; GSYM dist] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ONCE_REWRITE_TAC[DIST_SYM] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `ball(x:real^N,d)` THEN
  ASM_REWRITE_TAC[OPEN_BALL; CENTRE_IN_BALL] THEN
  SUBGOAL_THEN `smooth_map_on (ball(x:real^N,d)) (g:real^N->complex)`
    (fun th -> MESON_TAC[th; smooth_map_on]) THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN
  EXISTS_TAC `\y. (g:real^N->complex) x + clog(f y / f x)` THEN
  REWRITE_TAC[OPEN_BALL] THEN CONJ_TAC THENL
   [X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:real^N`) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `(f:real^N->complex) y / f x = cexp(g y - g x)` SUBST1_TAC THENL
     [REWRITE_TAC[CEXP_SUB] THEN BINOP_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      UNDISCH_TAC `ball(x:real^N,d) SUBSET s` THEN
      UNDISCH_TAC `(y:real^N) IN ball(x,d)` THEN
      UNDISCH_TAC `(x:real^N) IN s` THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `clog(cexp((g:real^N->complex) y - g x)) = g y - g x`
    SUBST1_TAC THENL
     [MATCH_MP_TAC CLOG_CEXP THEN
      MP_TAC(SPEC `(g:real^N->complex) y - g x` COMPLEX_NORM_GE_RE_IM) THEN
      MP_TAC PI_APPROX_32 THEN ASM_REAL_ARITH_TAC;
      CONV_TAC COMPLEX_RING];
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN
  REWRITE_TAC[OPEN_BALL; SMOOTH_MAP_ON_CONST] THEN
  SUBGOAL_THEN `(\y:real^N. clog((f:real^N->complex) y / f x)) =
                clog o (\y. f y * inv(f x))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; complex_div]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
  EXISTS_TAC `ball(Cx(&1),&1)` THEN REWRITE_TAC[OPEN_BALL] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_BALL; dist] THEN
    X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:real^N`) THEN
    ASM_REWRITE_TAC[IN_BALL; dist] THEN
    REWRITE_TAC[complex_div] THEN STRIP_TAC THEN
    ONCE_REWRITE_TAC[NORM_SUB] THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOI_PDL_SMOOTH_CMUL_FUN THEN
    REWRITE_TAC[OPEN_BALL; SMOOTH_MAP_ON_CONST] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `s:real^N->bool` THEN
    ASM_REWRITE_TAC[ETA_AX];
    MATCH_MP_TAC MOI_PDL_HOLOMORPHIC_SMOOTH THEN REWRITE_TAC[OPEN_BALL] THEN
    MATCH_MP_TAC HOLOMORPHIC_ON_CLOG THEN
    REWRITE_TAC[IN_BALL; dist] THEN X_GEN_TAC `w:complex` THEN STRIP_TAC THEN
    MP_TAC(SPEC `Cx(&1) - w` COMPLEX_NORM_GE_RE_IM) THEN
    REWRITE_TAC[RE_SUB; RE_CX] THEN ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Radial normalization and the homogenized quotient g(N z) / N z.           *)
(* ------------------------------------------------------------------------- *)

let moi_pdl_nz = new_definition
 `moi_pdl_nz (z:complex) = z / Cx(norm z)`;;

let MOI_PDL_NZ_PROPS = prove
 (`!z. ~(z = Cx(&0))
       ==> norm(moi_pdl_nz z) = &1 /\ ~(moi_pdl_nz z = Cx(&0)) /\
           Cx(norm z) * moi_pdl_nz z = z /\
           (!t. &0 < t ==> moi_pdl_nz(Cx t * z) = moi_pdl_nz z)`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(Cx(norm(z:complex)) = Cx(&0))` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[CX_INJ; COMPLEX_NORM_ZERO]; ALL_TAC] THEN
  REWRITE_TAC[moi_pdl_nz] THEN REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[COMPLEX_NORM_DIV; COMPLEX_NORM_CX; REAL_ABS_NORM;
                 REAL_DIV_REFL; COMPLEX_NORM_ZERO];
    ASM_REWRITE_TAC[COMPLEX_DIV_EQ_0];
    UNDISCH_TAC `~(Cx(norm(z:complex)) = Cx(&0))` THEN CONV_TAC COMPLEX_FIELD;
    X_GEN_TAC `t:real` THEN DISCH_TAC THEN
    REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < t ==> abs t = t`; CX_MUL] THEN
    SUBGOAL_THEN `~(Cx t = Cx(&0))` MP_TAC THENL
     [ASM_SIMP_TAC[CX_INJ; REAL_LT_IMP_NZ]; ALL_TAC] THEN
    UNDISCH_TAC `~(Cx(norm(z:complex)) = Cx(&0))` THEN CONV_TAC COMPLEX_FIELD]);;

let MOI_PDL_NZ_UNIT = prove
 (`!z. norm z = &1 ==> moi_pdl_nz z = z`,
  SIMP_TAC[moi_pdl_nz; COMPLEX_DIV_1]);;

let MOI_PDL_NZ_CONT = prove
 (`moi_pdl_nz continuous_on ((:complex) DIFF {Cx(&0)})`,
  SUBGOAL_THEN `moi_pdl_nz = \z. z / Cx(norm z)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; moi_pdl_nz]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_DIV THEN
  REWRITE_TAC[CONTINUOUS_ON_ID; CONTINUOUS_ON_CX_NORM] THEN
  REWRITE_TAC[IN_DIFF; IN_UNIV; IN_SING; CX_INJ; COMPLEX_NORM_ZERO]);;

let MOI_PDL_OPEN_PUNCTURED = prove
 (`open((:complex) DIFF {Cx(&0)})`,
  SIMP_TAC[OPEN_DIFF; OPEN_UNIV; CLOSED_SING]);;

let MOI_PDL_SMOOTH_CINV = prove
 (`!s (f:real^N->complex).
     open s /\ smooth_map_on s f /\ (!x. x IN s ==> ~(f x = Cx(&0)))
     ==> smooth_map_on s (\x. inv(f x))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\x:real^N. inv((f:real^N->complex) x)) = inv o f`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
  EXISTS_TAC `(:complex) DIFF {Cx(&0)}` THEN
  ASM_REWRITE_TAC[MOI_PDL_OPEN_PUNCTURED] THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_DIFF; IN_UNIV; IN_SING] THEN
    ASM_MESON_TAC[];
    MATCH_MP_TAC MOI_PDL_HOLOMORPHIC_SMOOTH THEN
    REWRITE_TAC[MOI_PDL_OPEN_PUNCTURED] THEN
    MP_TAC(ISPECL [`\z:complex. z`; `(:complex) DIFF {Cx(&0)}`]
      HOLOMORPHIC_ON_INV) THEN
    REWRITE_TAC[HOLOMORPHIC_ON_ID; IN_DIFF; IN_UNIV; IN_SING; ETA_AX] THEN
    SIMP_TAC[]]);;

let MOI_PDL_NZ_SMOOTH = prove
 (`smooth_map_on ((:complex) DIFF {Cx(&0)}) moi_pdl_nz`,
  SUBGOAL_THEN `moi_pdl_nz = \z. z * inv(Cx(drop(lift(norm z))))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; moi_pdl_nz; complex_div; LIFT_DROP]; ALL_TAC] THEN
  MATCH_MP_TAC MOI_PDL_SMOOTH_CMUL_FUN THEN
  REWRITE_TAC[MOI_PDL_OPEN_PUNCTURED; SMOOTH_MAP_ON_ID] THEN
  MATCH_MP_TAC MOI_PDL_SMOOTH_CINV THEN
  REWRITE_TAC[MOI_PDL_OPEN_PUNCTURED] THEN CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[LIFT_DROP; CX_INJ; COMPLEX_NORM_ZERO; IN_DIFF; IN_UNIV;
                IN_SING]] THEN
  MATCH_MP_TAC MOI_PDL_SMOOTH_CX_DROP THEN
  REWRITE_TAC[MOI_PDL_OPEN_PUNCTURED] THEN
  MP_TAC(ISPECL [`(:complex) DIFF {Cx(&0)}`; `\z:complex. z`]
    SMOOTH_MAP_ON_LIFT_NORM) THEN
  REWRITE_TAC[MOI_PDL_OPEN_PUNCTURED; SMOOTH_MAP_ON_ID; IN_DIFF; IN_UNIV;
              IN_SING; COMPLEX_VEC_0]);;

let moi_pdl_wf = new_definition
 `moi_pdl_wf (g:complex->complex) (z:complex) = g(moi_pdl_nz z) / moi_pdl_nz z`;;

let moi_pdl_wdom = new_definition
 `moi_pdl_wdom (u:complex->bool) (g:complex->complex) =
    {z | ~(z = Cx(&0)) /\ moi_pdl_nz z IN u /\ ~(g(moi_pdl_nz z) = Cx(&0))}`;;

let MOI_PDL_WDOM_OPEN = prove
 (`!u (g:complex->complex).
     open u /\ g continuous_on u ==> open(moi_pdl_wdom u g)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `A = {z | z IN (:complex) DIFF {Cx(&0)} /\ moi_pdl_nz z IN u}` THEN
  SUBGOAL_THEN `open(A:complex->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "A" THEN MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN
    ASM_REWRITE_TAC[MOI_PDL_NZ_CONT; MOI_PDL_OPEN_PUNCTURED];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `moi_pdl_wdom u g =
    {z | z IN A /\ ((g:complex->complex) o moi_pdl_nz) z IN
                   (:complex) DIFF {Cx(&0)}}`
  SUBST1_TAC THENL
   [EXPAND_TAC "A" THEN
    REWRITE_TAC[moi_pdl_wdom; EXTENSION; IN_ELIM_THM; IN_DIFF; IN_UNIV;
                IN_SING; o_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN
  ASM_REWRITE_TAC[MOI_PDL_OPEN_PUNCTURED; ETA_AX] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `(:complex) DIFF {Cx(&0)}` THEN
    REWRITE_TAC[MOI_PDL_NZ_CONT] THEN EXPAND_TAC "A" THEN SET_TAC[];
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `u:complex->bool` THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "A" THEN SET_TAC[]]);;

let MOI_PDL_WDOM_CONE = prove
 (`!u (g:complex->complex) z t.
     z IN moi_pdl_wdom u g /\ &0 < t ==> Cx t * z IN moi_pdl_wdom u g`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[moi_pdl_wdom; IN_ELIM_THM; COMPLEX_ENTIRE; CX_INJ;
              DE_MORGAN_THM] THEN
  STRIP_TAC THEN ASM_SIMP_TAC[MOI_PDL_NZ_PROPS] THEN ASM_REAL_ARITH_TAC);;

let MOI_PDL_WF_HOM = prove
 (`!(g:complex->complex) z t.
     ~(z = Cx(&0)) /\ &0 < t ==> moi_pdl_wf g (Cx t * z) = moi_pdl_wf g z`,
  SIMP_TAC[moi_pdl_wf; MOI_PDL_NZ_PROPS]);;

let MOI_PDL_WF_SMOOTH = prove
 (`!u (g:complex->complex).
     open u /\ smooth_map_on u g
     ==> smooth_map_on (moi_pdl_wdom u g) (moi_pdl_wf g)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open(moi_pdl_wdom u (g:complex->complex))` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_PDL_WDOM_OPEN THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on (moi_pdl_wdom u (g:complex->complex)) moi_pdl_nz`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
    EXISTS_TAC `(:complex) DIFF {Cx(&0)}` THEN
    REWRITE_TAC[MOI_PDL_NZ_SMOOTH; moi_pdl_wdom] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_pdl_wf (g:complex->complex) =
                \z. (g o moi_pdl_nz) z * inv(moi_pdl_nz z)`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; moi_pdl_wf; o_THM; complex_div]; ALL_TAC] THEN
  MATCH_MP_TAC MOI_PDL_SMOOTH_CMUL_FUN THEN ASM_REWRITE_TAC[ETA_AX] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
    EXISTS_TAC `u:complex->bool` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; moi_pdl_wdom; IN_ELIM_THM] THEN
    SIMP_TAC[];
    MATCH_MP_TAC MOI_PDL_SMOOTH_CINV THEN ASM_REWRITE_TAC[ETA_AX] THEN
    REWRITE_TAC[moi_pdl_wdom; IN_ELIM_THM] THEN SIMP_TAC[MOI_PDL_NZ_PROPS]]);;

let MOI_PDL_WF_PIECE = prove
 (`!(P:complex->complex) (S:complex->bool) u (g:complex->complex).
     (!t z. &0 <= t ==> P(Cx t * z) = Cx t * P z) /\
     (!z. ~(z = Cx(&0)) ==> ~(P z = Cx(&0))) /\
     conic S /\ S DIFF {vec 0} SUBSET u /\ (!x. x IN S ==> g x = P x)
     ==> S DIFF {vec 0} SUBSET moi_pdl_wdom u g /\
         !z. z IN S DIFF {vec 0} ==> moi_pdl_wf g z = P z / z`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!z. z IN S DIFF {vec 0}
        ==> moi_pdl_nz z IN S DIFF {vec 0} /\
            Cx(inv(norm z)) * z = moi_pdl_nz z`
  ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[IN_DIFF; IN_SING; COMPLEX_VEC_0] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[MOI_PDL_NZ_PROPS] THEN
    SUBGOAL_THEN `Cx(inv(norm z)) * z = moi_pdl_nz z` ASSUME_TAC THENL
     [REWRITE_TAC[moi_pdl_nz; complex_div; CX_INV] THEN
      CONV_TAC COMPLEX_RING;
      ASM_REWRITE_TAC[]] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[GSYM COMPLEX_CMUL] THEN
    MATCH_MP_TAC CONIC_MUL THEN ASM_REWRITE_TAC[REAL_LE_INV_EQ; NORM_POS_LE];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; moi_pdl_wdom; IN_ELIM_THM] THEN X_GEN_TAC `z:complex` THEN
    DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `z:complex`) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `~(z = Cx(&0)) /\ ~(moi_pdl_nz z = Cx(&0)) /\ moi_pdl_nz z IN S`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(z:complex) IN S DIFF {vec 0}` THEN
      UNDISCH_TAC `moi_pdl_nz z IN S DIFF {vec 0}` THEN
      REWRITE_TAC[IN_DIFF; IN_SING; COMPLEX_VEC_0] THEN SIMP_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [UNDISCH_TAC `S DIFF {vec 0} SUBSET (u:complex->bool)` THEN
      UNDISCH_TAC `moi_pdl_nz z IN S DIFF {vec 0}` THEN SET_TAC[];
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  X_GEN_TAC `z:complex` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `z:complex`) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  UNDISCH_TAC `(z:complex) IN S DIFF {vec 0}` THEN
  REWRITE_TAC[IN_DIFF; IN_SING; COMPLEX_VEC_0] THEN STRIP_TAC THEN
  REWRITE_TAC[moi_pdl_wf] THEN
  SUBGOAL_THEN `(g:complex->complex)(moi_pdl_nz z) = P(moi_pdl_nz z)`
  SUBST1_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  ASM_SIMP_TAC[REAL_LE_INV_EQ; NORM_POS_LE] THEN
  SUBGOAL_THEN `~(Cx(inv(norm(z:complex))) = Cx(&0))` MP_TAC THENL
   [ASM_REWRITE_TAC[CX_INJ; REAL_INV_EQ_0; COMPLEX_NORM_ZERO]; ALL_TAC] THEN
  UNDISCH_TAC `~(z = Cx(&0))` THEN CONV_TAC COMPLEX_FIELD);;

(* ------------------------------------------------------------------------- *)
(* Closest points to a closed convex cone are positively homogeneous.        *)
(* ------------------------------------------------------------------------- *)

let MOI_PDL_CLOSEST_CONE = prove
 (`!(S:complex->bool) z t.
     closed S /\ convex S /\ conic S /\ ~(S = {}) /\ &0 < t
     ==> closest_point S (Cx t * z) = Cx t * closest_point S z`,
  REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC CLOSEST_POINT_UNIQUE THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM COMPLEX_CMUL] THEN MATCH_MP_TAC CONIC_MUL THEN
    ASM_SIMP_TAC[CLOSEST_POINT_IN_SET; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  X_GEN_TAC `w:complex` THEN DISCH_TAC THEN
  SUBGOAL_THEN `w = Cx t * (Cx(inv t) * w)` SUBST1_TAC THENL
   [REWRITE_TAC[COMPLEX_MUL_ASSOC; GSYM CX_MUL] THEN
    ASM_SIMP_TAC[REAL_MUL_RINV; REAL_LT_IMP_NZ; COMPLEX_MUL_LID];
    ALL_TAC] THEN
  REWRITE_TAC[dist; GSYM COMPLEX_SUB_LDISTRIB; COMPLEX_NORM_MUL;
              COMPLEX_NORM_CX] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
  REWRITE_TAC[GSYM dist] THEN MATCH_MP_TAC CLOSEST_POINT_LE THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM COMPLEX_CMUL] THEN
  MATCH_MP_TAC CONIC_MUL THEN ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE]);;

(* ------------------------------------------------------------------------- *)
(* The piece logarithm: lw at the closest point of the cone, corrected by    *)
(* the principal logarithm of the quotient of the homogenized values.        *)
(* ------------------------------------------------------------------------- *)

let moi_pdl_ldom = new_definition
 `moi_pdl_ldom (S:complex->bool) u (g:complex->complex) =
    {z | z IN moi_pdl_wdom u g /\ ~(closest_point S z = Cx(&0)) /\
         norm(moi_pdl_wf g z / moi_pdl_wf g (closest_point S z) - Cx(&1)) < &1}`;;

let moi_pdl_lwf = new_definition
 `moi_pdl_lwf (S:complex->bool) (g:complex->complex) (lw:complex->complex)
              (z:complex) =
    lw(closest_point S z) +
    clog(moi_pdl_wf g z / moi_pdl_wf g (closest_point S z))`;;

let MOI_PDL_PIECE_BASICS = prove
 (`!(P:complex->complex) (S:complex->bool) u (g:complex->complex) lw.
     (!t z. &0 <= t ==> P(Cx t * z) = Cx t * P z) /\
     (!z. ~(z = Cx(&0)) ==> ~(P z = Cx(&0))) /\
     closed S /\ conic S /\ ~(S = {}) /\
     S DIFF {vec 0} SUBSET u /\ (!x. x IN S ==> g x = P x) /\
     (!z. ~(z = Cx(&0)) ==> P z = z * cexp(lw z))
     ==> (!z. ~(closest_point S z = Cx(&0))
              ==> closest_point S z IN S DIFF {vec 0} /\
                  closest_point S z IN moi_pdl_wdom u g /\
                  moi_pdl_wf g (closest_point S z) =
                  cexp(lw(closest_point S z)) /\
                  ~(moi_pdl_wf g (closest_point S z) = Cx(&0))) /\
         (!z. z IN S DIFF {vec 0} ==> closest_point S z = z)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`P:complex->complex`; `S:complex->bool`; `u:complex->bool`;
                 `g:complex->complex`] MOI_PDL_WF_PIECE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `z:complex` THEN DISCH_TAC THEN
    SUBGOAL_THEN `closest_point S z IN (S:complex->bool) DIFF {vec 0}`
    ASSUME_TAC THENL
     [ASM_SIMP_TAC[IN_DIFF; IN_SING; CLOSEST_POINT_IN_SET; COMPLEX_VEC_0];
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      ASM SET_TAC[];
      ASM_SIMP_TAC[] THEN
      UNDISCH_TAC `~(closest_point S z = Cx(&0))` THEN
      SPEC_TAC(`closest_point S (z:complex)`,`y:complex`) THEN
      GEN_TAC THEN DISCH_TAC THEN ASM_SIMP_TAC[] THEN
      UNDISCH_TAC `~(y = Cx(&0))` THEN CONV_TAC COMPLEX_FIELD;
      ASM_SIMP_TAC[] THEN
      UNDISCH_TAC `~(closest_point S z = Cx(&0))` THEN
      SPEC_TAC(`closest_point S (z:complex)`,`y:complex`) THEN
      GEN_TAC THEN DISCH_TAC THEN ASM_SIMP_TAC[] THEN
      REWRITE_TAC[COMPLEX_DIV_EQ_0; DE_MORGAN_THM; COMPLEX_ENTIRE; CEXP_NZ] THEN
      ASM_REWRITE_TAC[]];
    X_GEN_TAC `z:complex` THEN REWRITE_TAC[IN_DIFF] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[CLOSEST_POINT_REFL]]);;

let MOI_PDL_LDOM_PROPS = prove
 (`!(P:complex->complex) (S:complex->bool) u (g:complex->complex) lw.
     (!t z. &0 <= t ==> P(Cx t * z) = Cx t * P z) /\
     (!z. ~(z = Cx(&0)) ==> ~(P z = Cx(&0))) /\
     closed S /\ convex S /\ conic S /\ ~(S = {}) /\
     open u /\ S DIFF {vec 0} SUBSET u /\ smooth_map_on u g /\
     (!x. x IN S ==> g x = P x) /\
     lw continuous_on ((:complex) DIFF {Cx(&0)}) /\
     (!z. ~(z = Cx(&0)) ==> P z = z * cexp(lw z)) /\
     (!z t. ~(z = Cx(&0)) /\ &0 < t ==> lw(Cx t * z) = lw z)
     ==> S DIFF {vec 0} SUBSET moi_pdl_ldom S u g /\
         moi_pdl_ldom S u g SUBSET moi_pdl_wdom u g /\
         open(moi_pdl_ldom S u g) /\
         (!z t. z IN moi_pdl_ldom S u g /\ &0 < t
                ==> Cx t * z IN moi_pdl_ldom S u g) /\
         (!z. z IN moi_pdl_ldom S u g
              ==> cexp(moi_pdl_lwf S g lw z) = moi_pdl_wf g z) /\
         (!z. z IN S DIFF {vec 0} ==> moi_pdl_lwf S g lw z = lw z) /\
         (!z t. z IN moi_pdl_ldom S u g /\ &0 < t
                ==> moi_pdl_lwf S g lw (Cx t * z) = moi_pdl_lwf S g lw z) /\
         smooth_map_on (moi_pdl_ldom S u g) (moi_pdl_lwf S g lw)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`P:complex->complex`; `S:complex->bool`; `u:complex->bool`;
                 `g:complex->complex`; `lw:complex->complex`]
    MOI_PDL_PIECE_BASICS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "cp") (LABEL_TAC "refl")) THEN
  MP_TAC(ISPECL [`P:complex->complex`; `S:complex->bool`; `u:complex->bool`;
                 `g:complex->complex`] MOI_PDL_WF_PIECE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "sub") (LABEL_TAC "wfp")) THEN
  SUBGOAL_THEN `!z. z IN moi_pdl_wdom u (g:complex->complex)
                    ==> ~(moi_pdl_wf g z = Cx(&0))`
  (LABEL_TAC "wnz") THENL
   [REWRITE_TAC[moi_pdl_wdom; IN_ELIM_THM; moi_pdl_wf; COMPLEX_DIV_EQ_0;
                DE_MORGAN_THM] THEN SIMP_TAC[MOI_PDL_NZ_PROPS];
    ALL_TAC] THEN
  SUBGOAL_THEN `S DIFF {vec 0} SUBSET moi_pdl_ldom S u (g:complex->complex)`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; moi_pdl_ldom; IN_ELIM_THM] THEN
    X_GEN_TAC `z:complex` THEN DISCH_TAC THEN
    SUBGOAL_THEN `~(z = Cx(&0))` ASSUME_TAC THENL
     [UNDISCH_TAC `(z:complex) IN S DIFF {vec 0}` THEN
      REWRITE_TAC[IN_DIFF; IN_SING; COMPLEX_VEC_0] THEN SIMP_TAC[];
      ALL_TAC] THEN
    USE_THEN "refl" (fun th -> REWRITE_TAC[MATCH_MP th
      (ASSUME `(z:complex) IN S DIFF {vec 0}`)]) THEN
    SUBGOAL_THEN `z IN moi_pdl_wdom u (g:complex->complex)` ASSUME_TAC THENL
     [UNDISCH_TAC `S DIFF {vec 0} SUBSET moi_pdl_wdom u (g:complex->complex)` THEN
      UNDISCH_TAC `(z:complex) IN S DIFF {vec 0}` THEN SET_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    USE_THEN "wnz" (MP_TAC o C MATCH_MP
      (ASSUME `z IN moi_pdl_wdom u (g:complex->complex)`)) THEN
    SIMP_TAC[COMPLEX_DIV_REFL; COMPLEX_SUB_REFL; COMPLEX_NORM_CX; REAL_ABS_NUM;
             REAL_LT_01];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `moi_pdl_ldom S u g SUBSET moi_pdl_wdom u (g:complex->complex)`
  ASSUME_TAC THENL
   [REWRITE_TAC[moi_pdl_ldom] THEN SET_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `open(moi_pdl_wdom u (g:complex->complex)) /\
                moi_pdl_wf g continuous_on moi_pdl_wdom u g`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC MOI_PDL_WDOM_OPEN THEN
      ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON];
      MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
      MATCH_MP_TAC MOI_PDL_WF_SMOOTH THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `D = {z | z IN moi_pdl_wdom u (g:complex->complex) /\
                       closest_point S z IN (:complex) DIFF {Cx(&0)}}` THEN
  SUBGOAL_THEN `open(D:complex->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN
    ASM_SIMP_TAC[CONTINUOUS_ON_CLOSEST_POINT; MOI_PDL_OPEN_PUNCTURED; ETA_AX];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\z. moi_pdl_wf (g:complex->complex) z /
         moi_pdl_wf g (closest_point S z)) continuous_on D /\
    (\z. (lw:complex->complex)(closest_point S z)) continuous_on D`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `(closest_point S) continuous_on (D:complex->bool) /\
                  IMAGE (closest_point S) D SUBSET
                  moi_pdl_wdom u (g:complex->complex) /\
                  IMAGE (closest_point S) D SUBSET (:complex) DIFF {Cx(&0)}`
    STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[CONTINUOUS_ON_CLOSEST_POINT] THEN
      EXPAND_TAC "D" THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; IN_DIFF; IN_UNIV;
                  IN_SING] THEN
      USE_THEN "cp" (fun th -> SIMP_TAC[th]);
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_DIV THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
        EXISTS_TAC `moi_pdl_wdom u (g:complex->complex)` THEN
        ASM_REWRITE_TAC[ETA_AX] THEN EXPAND_TAC "D" THEN SET_TAC[];
        ONCE_REWRITE_TAC[GSYM o_DEF] THEN MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
        ASM_REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
        EXISTS_TAC `moi_pdl_wdom u (g:complex->complex)` THEN ASM_REWRITE_TAC[];
        EXPAND_TAC "D" THEN REWRITE_TAC[IN_ELIM_THM; IN_DIFF; IN_UNIV; IN_SING] THEN
        USE_THEN "cp" (fun th -> SIMP_TAC[th])];
      ONCE_REWRITE_TAC[GSYM o_DEF] THEN MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
      ASM_REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `(:complex) DIFF {Cx(&0)}` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `moi_pdl_ldom S u (g:complex->complex) =
    {z | z IN D /\ (\z. moi_pdl_wf g z / moi_pdl_wf g (closest_point S z)) z
                   IN ball(Cx(&1),&1)}`
  (LABEL_TAC "ldeq") THENL
   [EXPAND_TAC "D" THEN
    REWRITE_TAC[moi_pdl_ldom; EXTENSION; IN_ELIM_THM; IN_DIFF; IN_UNIV;
                IN_SING; IN_BALL; dist] THEN
    REWRITE_TAC[NORM_SUB; CONJ_ASSOC];
    ALL_TAC] THEN
  SUBGOAL_THEN `open(moi_pdl_ldom S u (g:complex->complex))` ASSUME_TAC THENL
   [USE_THEN "ldeq" (fun th -> GEN_REWRITE_TAC RAND_CONV [th]) THEN
    MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN ASM_REWRITE_TAC[OPEN_BALL];
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_pdl_ldom S u (g:complex->complex) SUBSET D` ASSUME_TAC THENL
   [USE_THEN "ldeq" SUBST1_TAC THEN SET_TAC[]; ALL_TAC] THEN
  REMOVE_THEN "ldeq" (K ALL_TAC) THEN
  SUBGOAL_THEN
   `!z. z IN moi_pdl_ldom S u (g:complex->complex)
        ==> z IN moi_pdl_wdom u g /\ ~(z = Cx(&0)) /\
            ~(closest_point S z = Cx(&0)) /\
            norm(moi_pdl_wf g z / moi_pdl_wf g (closest_point S z) - Cx(&1)) < &1`
  (LABEL_TAC "unp") THENL
   [GEN_TAC THEN REWRITE_TAC[moi_pdl_ldom; IN_ELIM_THM] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `z IN moi_pdl_wdom u (g:complex->complex)` THEN
    REWRITE_TAC[moi_pdl_wdom; IN_ELIM_THM] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z. z IN moi_pdl_ldom S u (g:complex->complex)
        ==> cexp(moi_pdl_lwf S g lw z) = moi_pdl_wf g z`
  (LABEL_TAC "exp") THENL
   [X_GEN_TAC `z:complex` THEN DISCH_TAC THEN
    USE_THEN "unp" (STRIP_ASSUME_TAC o C MATCH_MP
      (ASSUME `z IN moi_pdl_ldom S u (g:complex->complex)`)) THEN
    USE_THEN "cp" (MP_TAC o C MATCH_MP
      (ASSUME `~(closest_point S (z:complex) = Cx(&0))`)) THEN STRIP_TAC THEN
    REWRITE_TAC[moi_pdl_lwf; CEXP_ADD] THEN
    SUBGOAL_THEN
     `~(moi_pdl_wf (g:complex->complex) z / moi_pdl_wf g (closest_point S z) =
        Cx(&0))`
    ASSUME_TAC THENL
     [DISCH_TAC THEN
      UNDISCH_TAC `norm(moi_pdl_wf (g:complex->complex) z /
                        moi_pdl_wf g (closest_point S z) - Cx(&1)) < &1` THEN
      ASM_REWRITE_TAC[COMPLEX_SUB_LZERO; NORM_NEG; COMPLEX_NORM_CX] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[CEXP_CLOG] THEN
    UNDISCH_TAC `~(moi_pdl_wf (g:complex->complex) (closest_point S z) = Cx(&0))` THEN
    UNDISCH_TAC `moi_pdl_wf (g:complex->complex) (closest_point S z) =
                 cexp(lw(closest_point S z))` THEN
    CONV_TAC COMPLEX_FIELD;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`z:complex`; `t:real`] THEN STRIP_TAC THEN
    USE_THEN "unp" (STRIP_ASSUME_TAC o C MATCH_MP
      (ASSUME `z IN moi_pdl_ldom S u (g:complex->complex)`)) THEN
    REWRITE_TAC[moi_pdl_ldom; IN_ELIM_THM] THEN
    SUBGOAL_THEN `closest_point S (Cx t * z) = Cx t * closest_point S z`
    SUBST1_TAC THENL
     [MATCH_MP_TAC MOI_PDL_CLOSEST_CONE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `moi_pdl_wf (g:complex->complex) (Cx t * z) = moi_pdl_wf g z /\
      moi_pdl_wf g (Cx t * closest_point S z) =
      moi_pdl_wf g (closest_point S z)`
    (fun th -> REWRITE_TAC[th]) THENL
     [CONJ_TAC THEN MATCH_MP_TAC MOI_PDL_WF_HOM THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MOI_PDL_WDOM_CONE THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[COMPLEX_ENTIRE; CX_INJ] THEN ASM_SIMP_TAC[REAL_LT_IMP_NZ];
      ASM_REWRITE_TAC[]];
    X_GEN_TAC `z:complex` THEN DISCH_TAC THEN REWRITE_TAC[moi_pdl_lwf] THEN
    USE_THEN "refl" (fun th -> REWRITE_TAC[MATCH_MP th
      (ASSUME `(z:complex) IN S DIFF {vec 0}`)]) THEN
    SUBGOAL_THEN `z IN moi_pdl_wdom u (g:complex->complex)` ASSUME_TAC THENL
     [UNDISCH_TAC `S DIFF {vec 0} SUBSET moi_pdl_wdom u (g:complex->complex)` THEN
      UNDISCH_TAC `(z:complex) IN S DIFF {vec 0}` THEN SET_TAC[];
      ALL_TAC] THEN
    USE_THEN "wnz" (MP_TAC o C MATCH_MP
      (ASSUME `z IN moi_pdl_wdom u (g:complex->complex)`)) THEN
    SIMP_TAC[COMPLEX_DIV_REFL; CLOG_1; COMPLEX_ADD_RID];
    MAP_EVERY X_GEN_TAC [`z:complex`; `t:real`] THEN STRIP_TAC THEN
    USE_THEN "unp" (STRIP_ASSUME_TAC o C MATCH_MP
      (ASSUME `z IN moi_pdl_ldom S u (g:complex->complex)`)) THEN REWRITE_TAC[moi_pdl_lwf] THEN
    ASM_SIMP_TAC[MOI_PDL_CLOSEST_CONE; MOI_PDL_WF_HOM];
    MATCH_MP_TAC MOI_PDL_CLOG_SMOOTH THEN
    EXISTS_TAC `moi_pdl_wf (g:complex->complex)` THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
      EXISTS_TAC `moi_pdl_wdom u (g:complex->complex)` THEN
      ASM_SIMP_TAC[MOI_PDL_WF_SMOOTH];
      ALL_TAC;
      USE_THEN "exp" (fun th -> SIMP_TAC[th])] THEN
    SUBGOAL_THEN
     `moi_pdl_lwf S (g:complex->complex) lw =
      (\z. lw(closest_point S z) +
           clog(moi_pdl_wf g z / moi_pdl_wf g (closest_point S z)))`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; moi_pdl_lwf]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_ADD THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `D:complex->bool` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ONCE_REWRITE_TAC[GSYM o_DEF] THEN MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `D:complex->bool` THEN
      ASM_REWRITE_TAC[ETA_AX];
      ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `ball(Cx(&1),&1)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_CLOG THEN
      REWRITE_TAC[IN_BALL; dist] THEN X_GEN_TAC `w:complex` THEN STRIP_TAC THEN
      MP_TAC(SPEC `Cx(&1) - w` COMPLEX_NORM_GE_RE_IM) THEN
      REWRITE_TAC[RE_SUB; RE_CX] THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; moi_pdl_ldom; IN_ELIM_THM; IN_BALL;
                  dist] THEN
      MESON_TAC[NORM_SUB]]]);;

(* ------------------------------------------------------------------------- *)
(* Derivatives of maps homogeneous of degree zero, and the angular speed.    *)
(* ------------------------------------------------------------------------- *)

let MOI_PDL_HOM0_DERIV = prove
 (`!(f:complex->complex) s z t.
     open s /\ z IN s /\ &0 < t /\
     f differentiable (at z) /\ f differentiable (at (Cx t * z)) /\
     (!y. y IN s ==> f(Cx t * y) = f y)
     ==> !h. frechet_derivative f (at (Cx t * z)) (Cx t * h) =
             frechet_derivative f (at z) h`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `((\y. (f:complex->complex)(Cx t * y)) has_derivative
     (\h. frechet_derivative f (at (Cx t * z)) (Cx t * h))) (at z)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `(\y. (f:complex->complex)(Cx t * y)) = f o (\y. Cx t * y)`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    SUBGOAL_THEN
     `(\h. frechet_derivative (f:complex->complex) (at (Cx t * z)) (Cx t * h)) =
      frechet_derivative f (at (Cx t * z)) o (\h. Cx t * h)`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC DIFF_CHAIN_AT THEN
    ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
    MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN REWRITE_TAC[LINEAR_COMPLEX_MUL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\y. (f:complex->complex)(Cx t * y)) has_derivative
     frechet_derivative f (at z)) (at z)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_AT THEN
    EXISTS_TAC `f:complex->complex` THEN
    UNDISCH_TAC `open(s:complex->bool)` THEN REWRITE_TAC[OPEN_CONTAINS_BALL] THEN
    DISCH_THEN(MP_TAC o SPEC `z:complex`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `r:real` THEN ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
    X_GEN_TAC `y:complex` THEN DISCH_TAC THEN CONV_TAC SYM_CONV THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `ball(z:complex,r) SUBSET s` THEN REWRITE_TAC[SUBSET; IN_BALL] THEN
    DISCH_THEN MATCH_MP_TAC THEN ONCE_REWRITE_TAC[DIST_SYM] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP FRECHET_DERIVATIVE_UNIQUE_AT o CONJ
   (ASSUME `((\y. (f:complex->complex)(Cx t * y)) has_derivative
     (\h. frechet_derivative f (at (Cx t * z)) (Cx t * h))) (at z)`)) THEN
  SIMP_TAC[FUN_EQ_THM]);;

let MOI_PDL_CONST_MUL_VDERIV = prove
 (`!(f:real^1->complex) f' c x.
     (f has_vector_derivative f') (at x)
     ==> ((\t. f t * c) has_vector_derivative (f' * c)) (at x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[has_vector_derivative] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(\t:real^1. (f:real^1->complex) t * c) = (\w. w * c) o f`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `(\h:real^1. drop h % (f' * c)) = (\w. w * c) o (\h. drop h % f')`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; COMPLEX_CMUL; COMPLEX_MUL_ASSOC];
    ALL_TAC] THEN
  MATCH_MP_TAC DIFF_CHAIN_AT THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN MATCH_MP_TAC LINEAR_COMPLEX_RMUL THEN
  REWRITE_TAC[LINEAR_ID]);;

let MOI_PDL_ANGSPEED = prove
 (`!(g:complex->complex) (L:complex->complex) e d.
     g differentiable (at e) /\ L differentiable (at e) /\ norm e = &1 /\
     &0 < d /\
     (!w. norm(w - e) < d /\ norm w = &1 ==> g w = w * cexp(L w)) /\
     (!s. abs(s - &1) < d ==> g(s % e) = s % g e) /\
     &0 < det(jacobian g (at e))
     ==> &0 < &1 + Im(frechet_derivative L (at e) (ii * e))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(e = Cx(&0))` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `norm(e:complex) = &1` THEN
    ASM_REWRITE_TAC[COMPLEX_NORM_CX] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((g:complex->complex) has_derivative frechet_derivative g (at e)) (at e) /\
    ((L:complex->complex) has_derivative frechet_derivative L (at e)) (at e) /\
    linear(frechet_derivative (g:complex->complex) (at e))`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[LINEAR_FRECHET_DERIVATIVE] THEN
    ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS];
    ALL_TAC] THEN
  ABBREV_TAC `T0 = frechet_derivative (g:complex->complex) (at e)` THEN
  ABBREV_TAC `L0 = frechet_derivative (L:complex->complex) (at e)` THEN
  SUBGOAL_THEN `(T0:complex->complex) e = g e` ASSUME_TAC THENL
   [EXPAND_TAC "T0" THEN MATCH_MP_TAC MOI_PDL_RADIAL_DERIV THEN
    EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `c = \t:real^1. cexp(ii * Cx(drop t)) * e` THEN
  SUBGOAL_THEN `(c has_vector_derivative (ii * e)) (at (vec 0)) /\
                c(vec 0) = e`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN
    REWRITE_TAC[DROP_VEC; COMPLEX_MUL_RZERO; CEXP_0; COMPLEX_MUL_LID] THEN
    MP_TAC(SPEC `vec 0:real^1` MOI_PDL_E_DERIV) THEN
    DISCH_THEN(MP_TAC o SPEC `e:complex` o MATCH_MP MOI_PDL_CONST_MUL_VDERIV) THEN
    REWRITE_TAC[DROP_VEC; COMPLEX_MUL_RZERO; CEXP_0; COMPLEX_MUL_RID];
    ALL_TAC] THEN
  SUBGOAL_THEN `!t. norm((c:real^1->complex) t) = &1` ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN ASM_REWRITE_TAC[COMPLEX_NORM_MUL; NORM_CEXP_II;
                                       REAL_MUL_LID];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?del. &0 < del /\
          !t. norm(t - vec 0:real^1) < del ==> norm((c:real^1->complex) t - e) < d`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(c has_vector_derivative (ii * e)) (at (vec 0))` THEN
    DISCH_THEN(MP_TAC o MATCH_MP HAS_VECTOR_DERIVATIVE_IMP_DIFFERENTIABLE) THEN
    DISCH_THEN(MP_TAC o MATCH_MP DIFFERENTIABLE_IMP_CONTINUOUS_AT) THEN
    REWRITE_TAC[continuous_at; dist] THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!F0 (F1:complex->complex). (F0 has_derivative F1) (at e)
        ==> ((\t. F0((c:real^1->complex) t)) has_vector_derivative F1(ii * e))
            (at (vec 0))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `linear(F1:complex->complex)` ASSUME_TAC THENL
     [ASM_MESON_TAC[has_derivative]; ALL_TAC] THEN
    REWRITE_TAC[has_vector_derivative] THEN
    SUBGOAL_THEN `(\t. (F0:complex->complex)((c:real^1->complex) t)) = F0 o c`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    SUBGOAL_THEN `(\x:real^1. drop x % (F1:complex->complex)(ii * e)) =
                  F1 o (\x. drop x % (ii * e))`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM] THEN ASM_SIMP_TAC[LINEAR_CMUL];
      ALL_TAC] THEN
    MATCH_MP_TAC DIFF_CHAIN_AT THEN ASM_REWRITE_TAC[GSYM has_vector_derivative];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\t. ii * Cx(drop t) + (L:complex->complex)((c:real^1->complex) t))
     has_vector_derivative (ii + (L0:complex->complex)(ii * e))) (at (vec 0))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_ADD THEN ASM_SIMP_TAC[] THEN
    REWRITE_TAC[has_vector_derivative] THEN
    SUBGOAL_THEN `(\x:real^1. drop x % ii) = (\t. ii * Cx(drop t))`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; COMPLEX_CMUL; COMPLEX_MUL_SYM]; ALL_TAC] THEN
    MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN
    REWRITE_TAC[linear; DROP_ADD; DROP_CMUL; CX_ADD; CX_MUL; COMPLEX_CMUL] THEN
    CONV_TAC COMPLEX_RING;
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\t. ii * Cx(drop t) + (L:complex->complex)((c:real^1->complex) t)`;
    `\t. (g:complex->complex)((c:real^1->complex) t) / e`;
    `(T0:complex->complex)(ii * e) / e`; `vec 0:real^1`; `del:real`]
   MOI_PDL_LOG_DERIV_1D) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN
      MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_IMP_DIFFERENTIABLE THEN
      EXISTS_TAC `ii + (L0:complex->complex)(ii * e)` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN REWRITE_TAC[CEXP_ADD] THEN
      SUBGOAL_THEN `(g:complex->complex)((c:real^1->complex) t) =
                    c t * cexp((L:complex->complex)(c t))`
      SUBST1_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
          can (term_match [] `!w. norm(w - e) < d /\ norm w = &1 ==> P w`)
              (concl th))) THEN
        ASM_SIMP_TAC[];
        ALL_TAC] THEN
      EXPAND_TAC "c" THEN UNDISCH_TAC `~(e = Cx(&0))` THEN
      CONV_TAC COMPLEX_FIELD;
      REWRITE_TAC[complex_div] THEN MATCH_MP_TAC MOI_PDL_CONST_MUL_VDERIV THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `ii + (L0:complex->complex)(ii * e) =
    ((T0:complex->complex)(ii * e) / e) / (g e / e)`
  MP_TAC THENL
   [MATCH_MP_TAC VECTOR_DERIVATIVE_UNIQUE_AT THEN
    EXISTS_TAC `\t. ii * Cx(drop t) + (L:complex->complex)((c:real^1->complex) t)` THEN
    EXISTS_TAC `vec 0:real^1` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((g:complex->complex) e = Cx(&0))` ASSUME_TAC THENL
   [DISCH_TAC THEN
    MP_TAC(ISPECL [`T0:complex->complex`; `e:complex`] MOI_PDL_DET_ROT) THEN
    ASM_REWRITE_TAC[CNJ_CX; COMPLEX_MUL_LZERO; IM_CX] THEN
    UNDISCH_TAC `&0 < det(jacobian (g:complex->complex) (at e))` THEN
    ASM_REWRITE_TAC[jacobian; REAL_POW_ONE] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((T0:complex->complex)(ii * e) / e) / (g e / e) = T0(ii * e) / T0 e`
  SUBST1_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `~((g:complex->complex) e = Cx(&0))` THEN
    UNDISCH_TAC `~(e = Cx(&0))` THEN CONV_TAC COMPLEX_FIELD;
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o AP_TERM `Im`) THEN REWRITE_TAC[IM_ADD; IM_II] THEN
  DISCH_THEN SUBST1_TAC THEN
  ONCE_REWRITE_TAC[COMPLEX_DIV_CNJ] THEN REWRITE_TAC[GSYM CX_POW; IM_DIV_CX] THEN
  SUBGOAL_THEN
   `Im((T0:complex->complex)(ii * e) * cnj(T0 e)) = det(matrix T0)`
  SUBST1_TAC THENL
   [ONCE_REWRITE_TAC[COMPLEX_MUL_SYM] THEN
    MP_TAC(ISPECL [`T0:complex->complex`; `e:complex`] MOI_PDL_DET_ROT) THEN
    ASM_REWRITE_TAC[REAL_POW_ONE; REAL_MUL_LID];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LT_DIV THEN CONJ_TAC THENL
   [UNDISCH_TAC `&0 < det(jacobian (g:complex->complex) (at e))` THEN
    ASM_REWRITE_TAC[jacobian];
    MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[COMPLEX_NORM_NZ]]);;

let MOI_PDL_PIECE_DERIVS = prove
 (`!(P:complex->complex) (S:complex->bool) u (g:complex->complex) lw.
     (!t z. &0 <= t ==> P(Cx t * z) = Cx t * P z) /\
     (!z. ~(z = Cx(&0)) ==> ~(P z = Cx(&0))) /\
     closed S /\ convex S /\ conic S /\ ~(S = {}) /\
     open u /\ S DIFF {vec 0} SUBSET u /\ smooth_map_on u g /\
     (!x. x IN S ==> g x = P x) /\
     (!x. x IN S DIFF {vec 0} ==> &0 < det(jacobian g (at x))) /\
     lw continuous_on ((:complex) DIFF {Cx(&0)}) /\
     (!z. ~(z = Cx(&0)) ==> P z = z * cexp(lw z)) /\
     (!z t. ~(z = Cx(&0)) /\ &0 < t ==> lw(Cx t * z) = lw z)
     ==> (!z. z IN moi_pdl_ldom S u g
              ==> frechet_derivative (moi_pdl_lwf S g lw) (at z) z = Cx(&0)) /\
         (!z t. z IN moi_pdl_ldom S u g /\ &0 < t
                ==> frechet_derivative (moi_pdl_lwf S g lw) (at (Cx t * z))
                      (ii * (Cx t * z)) =
                    frechet_derivative (moi_pdl_lwf S g lw) (at z) (ii * z)) /\
         (!z. z IN S DIFF {vec 0}
              ==> &0 < &1 + Im(frechet_derivative (moi_pdl_lwf S g lw) (at z)
                                 (ii * z)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`P:complex->complex`; `S:complex->bool`; `u:complex->bool`;
                 `g:complex->complex`; `lw:complex->complex`]
    MOI_PDL_LDOM_PROPS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `V = moi_pdl_ldom S u (g:complex->complex)` THEN
  ABBREV_TAC `LW = moi_pdl_lwf S (g:complex->complex) lw` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `!z. z IN V ==> (LW:complex->complex) differentiable (at z)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `V:complex->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z. z IN V ==> ~(z = Cx(&0))` ASSUME_TAC THENL
   [X_GEN_TAC `z:complex` THEN DISCH_TAC THEN
    SUBGOAL_THEN `z IN moi_pdl_wdom u (g:complex->complex)` MP_TAC THENL
     [ASM SET_TAC[]; REWRITE_TAC[moi_pdl_wdom; IN_ELIM_THM] THEN SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z t. z IN V /\ &0 < t
          ==> frechet_derivative (LW:complex->complex) (at (Cx t * z))
                (ii * (Cx t * z)) =
              frechet_derivative LW (at z) (ii * z)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `ii * (Cx t * z) = Cx t * (ii * z)` SUBST1_TAC THENL
     [CONV_TAC COMPLEX_RING; ALL_TAC] THEN
    MP_TAC(ISPECL [`LW:complex->complex`; `V:complex->bool`; `z:complex`;
                   `t:real`] MOI_PDL_HOM0_DERIV) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[]; DISCH_THEN(fun th -> REWRITE_TAC[th])];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `z:complex` THEN DISCH_TAC THEN
    REWRITE_TAC[GSYM COMPLEX_VEC_0] THEN
    MATCH_MP_TAC(GEN_ALL(REWRITE_RULE[VECTOR_SUB_RZERO] (ISPECL
     [`\y:complex. (LW:complex->complex) y - LW z`;
      `\h:complex. frechet_derivative (LW:complex->complex) (at z) h - vec 0`;
      `z:complex`; `z:complex`; `&1`] MOI_PDL_DERIV_ZERO_LINE))) THEN
    CONJ_TAC THENL
     [SUBGOAL_THEN
       `(\h:complex. frechet_derivative (LW:complex->complex) (at z) h) =
        (\h. frechet_derivative LW (at z) h - vec 0)`
      SUBST1_TAC THENL [REWRITE_TAC[VECTOR_SUB_RZERO]; ALL_TAC] THEN
      MATCH_MP_TAC HAS_DERIVATIVE_SUB THEN
      REWRITE_TAC[HAS_DERIVATIVE_CONST; ETA_AX] THEN
      ASM_SIMP_TAC[GSYM FRECHET_DERIVATIVE_WORKS];
      ALL_TAC] THEN
    REWRITE_TAC[REAL_LT_01; VECTOR_SUB_EQ] THEN X_GEN_TAC `s:real` THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `z + s % z = Cx(&1 + s) * z` SUBST1_TAC THENL
     [REWRITE_TAC[COMPLEX_CMUL; CX_ADD] THEN CONV_TAC COMPLEX_RING;
      ALL_TAC] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (term_match [] `!z t. z IN V /\ &0 < t ==> (LW:complex->complex)(Cx t * z) = LW z`)
          (concl th))) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `z:complex` THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(z = Cx(&0))` ASSUME_TAC THENL
   [UNDISCH_TAC `(z:complex) IN S DIFF {vec 0}` THEN
    REWRITE_TAC[IN_DIFF; IN_SING; COMPLEX_VEC_0] THEN SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `r = norm(z:complex)` THEN
  ABBREV_TAC `e = moi_pdl_nz z` THEN
  SUBGOAL_THEN `norm(e:complex) = &1 /\ z = Cx r * e /\ &0 < r`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["e"; "r"] THEN
    ASM_SIMP_TAC[MOI_PDL_NZ_PROPS; NORM_POS_LT; COMPLEX_VEC_0];
    ALL_TAC] THEN
  SUBGOAL_THEN `(e:complex) IN S DIFF {vec 0}` ASSUME_TAC THENL
   [REWRITE_TAC[IN_DIFF; IN_SING; COMPLEX_VEC_0] THEN CONJ_TAC THENL
     [SUBGOAL_THEN `e = inv r % (z:complex)` SUBST1_TAC THENL
       [ASM_REWRITE_TAC[COMPLEX_CMUL; COMPLEX_MUL_ASSOC; GSYM CX_MUL] THEN
        ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ; COMPLEX_MUL_LID];
        MATCH_MP_TAC CONIC_MUL THEN ASM_REWRITE_TAC[REAL_LE_INV_EQ] THEN
        CONJ_TAC THENL [ASM SET_TAC[]; ASM_REAL_ARITH_TAC]];
      DISCH_TAC THEN UNDISCH_TAC `norm(e:complex) = &1` THEN
      ASM_REWRITE_TAC[COMPLEX_NORM_CX] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(e:complex) IN V /\ e IN u` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(SUBST1_TAC o check (fun th -> concl th = `z = Cx r * e`)) THEN
  FIRST_X_ASSUM((fun th -> REWRITE_TAC[MATCH_MP th
    (CONJ (ASSUME `(e:complex) IN V`) (ASSUME `&0 < r`))]) o check (fun th ->
      can (term_match [] `!z t. z IN V /\ &0 < t
          ==> frechet_derivative (LW:complex->complex) (at (Cx t * z))
                (ii * (Cx t * z)) = frechet_derivative LW (at z) (ii * z)`)
          (concl th))) THEN
  UNDISCH_TAC `open(V:complex->bool)` THEN REWRITE_TAC[OPEN_CONTAINS_BALL] THEN
  DISCH_THEN(MP_TAC o SPEC `e:complex`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d0:real` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC MOI_PDL_ANGSPEED THEN
  MAP_EVERY EXISTS_TAC [`g:complex->complex`; `min d0 (&1)`] THEN
  ASM_SIMP_TAC[REAL_LT_MIN; REAL_LT_01] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `u:complex->bool` THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `w:complex` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(w:complex) IN V` ASSUME_TAC THENL
     [UNDISCH_TAC `ball(e:complex,d0) SUBSET V` THEN
      REWRITE_TAC[SUBSET; IN_BALL; dist] THEN DISCH_THEN MATCH_MP_TAC THEN
      ONCE_REWRITE_TAC[NORM_SUB] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `~(w = Cx(&0))` ASSUME_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC `norm(w:complex) = &1` THEN
      ASM_REWRITE_TAC[COMPLEX_NORM_CX] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `w:complex` o check (fun th ->
      can (term_match [] `!z. z IN V ==> cexp((LW:complex->complex) z) = q z`)
          (concl th))) THEN
    ASM_REWRITE_TAC[moi_pdl_wf] THEN ASM_SIMP_TAC[MOI_PDL_NZ_UNIT] THEN
    UNDISCH_TAC `~(w = Cx(&0))` THEN CONV_TAC COMPLEX_FIELD;
    X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 <= s` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `s % (e:complex) IN S /\ e IN S` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC CONIC_MUL THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
        ASM SET_TAC[]];
      ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN REWRITE_TAC[COMPLEX_CMUL] THEN ASM_SIMP_TAC[]]);;

let MOI_PDL_ANGDER_CONT = prove
 (`!(f:complex->complex) s.
     open s /\ smooth_map_on s f
     ==> (\x. frechet_derivative f (at x) (ii * x)) continuous_on s`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_EQ THEN
  EXISTS_TAC `\x. (--(x$2)) % frechet_derivative (f:complex->complex) (at x) (Cx(&1)) +
                  (x$1) % frechet_derivative f (at x) ii` THEN
  CONJ_TAC THENL
   [X_GEN_TAC `x:complex` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `linear(frechet_derivative (f:complex->complex) (at x))`
    ASSUME_TAC THENL
     [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
      EXISTS_TAC `s:complex->bool` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `ii * x = (--(x$2)) % Cx(&1) + (x$1) % ii` SUBST1_TAC THENL
     [REWRITE_TAC[COMPLEX_EQ; RE_ADD; IM_ADD; RE_CMUL; IM_CMUL; RE_CX; IM_CX;
                  RE_II; IM_II; RE_MUL_II; IM_MUL_II; RE_DEF; IM_DEF] THEN
      REAL_ARITH_TAC;
      ASM_SIMP_TAC[LINEAR_ADD; LINEAR_CMUL]];
    ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_ADD THEN CONJ_TAC THEN
  MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
  (CONJ_TAC THENL
    [REWRITE_TAC[o_DEF; LIFT_NEG] THEN
     TRY(MATCH_MP_TAC CONTINUOUS_ON_NEG) THEN
     SIMP_TAC[CONTINUOUS_ON_LIFT_COMPONENT; DIMINDEX_2; ARITH];
     MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
     MATCH_MP_TAC SMOOTH_MAP_ON_FRECHET_DERIVATIVE THEN ASM_REWRITE_TAC[]]));;

let MOI_PDL_PIECE_BOUNDS = prove
 (`!(P:complex->complex) (S:complex->bool) u (g:complex->complex) lw.
     (!t z. &0 <= t ==> P(Cx t * z) = Cx t * P z) /\
     (!z. ~(z = Cx(&0)) ==> ~(P z = Cx(&0))) /\
     closed S /\ convex S /\ conic S /\ ~(S = {}) /\
     open u /\ S DIFF {vec 0} SUBSET u /\ smooth_map_on u g /\
     (!x. x IN S ==> g x = P x) /\
     (!x. x IN S DIFF {vec 0} ==> &0 < det(jacobian g (at x))) /\
     lw continuous_on ((:complex) DIFF {Cx(&0)}) /\
     (!z. ~(z = Cx(&0)) ==> P z = z * cexp(lw z)) /\
     (!z t. ~(z = Cx(&0)) /\ &0 < t ==> lw(Cx t * z) = lw z)
     ==> ?m B. &0 < m /\ m <= &1 /\ &0 < B /\
               !z. z IN S DIFF {vec 0}
                   ==> m <= &1 + Im(frechet_derivative (moi_pdl_lwf S g lw) (at z)
                                      (ii * z)) /\
                       norm(moi_pdl_lwf S g lw z) <= B /\
                       norm(frechet_derivative (moi_pdl_lwf S g lw) (at z)
                              (ii * z)) <= B`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`P:complex->complex`; `S:complex->bool`; `u:complex->bool`;
                 `g:complex->complex`; `lw:complex->complex`]
    MOI_PDL_LDOM_PROPS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`P:complex->complex`; `S:complex->bool`; `u:complex->bool`;
                 `g:complex->complex`; `lw:complex->complex`]
    MOI_PDL_PIECE_DERIVS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `V = moi_pdl_ldom S u (g:complex->complex)` THEN
  ABBREV_TAC `LW = moi_pdl_lwf S (g:complex->complex) lw` THEN
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `K = (S:complex->bool) INTER sphere(vec 0,&1)` THEN
  SUBGOAL_THEN `compact(K:complex->bool) /\ K SUBSET V /\
                K SUBSET (S:complex->bool) DIFF {vec 0}`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [EXPAND_TAC "K" THEN ASM_SIMP_TAC[CLOSED_INTER_COMPACT; COMPACT_SPHERE];
      ALL_TAC] THEN
    SUBGOAL_THEN `K SUBSET (S:complex->bool) DIFF {vec 0}` ASSUME_TAC THENL
     [EXPAND_TAC "K" THEN
      REWRITE_TAC[SUBSET; IN_INTER; IN_DIFF; IN_SING; IN_SPHERE_0] THEN
      X_GEN_TAC `x:complex` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      DISCH_TAC THEN UNDISCH_TAC `norm(x:complex) = &1` THEN
      ASM_REWRITE_TAC[NORM_0] THEN REAL_ARITH_TAC;
      ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(LW:complex->complex) continuous_on K /\
    (\x. frechet_derivative (LW:complex->complex) (at x) (ii * x)) continuous_on K`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `V:complex->bool` THEN ASM_REWRITE_TAC[] THENL
     [ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON];
      MATCH_MP_TAC MOI_PDL_ANGDER_CONT THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?B. &0 < B /\
        !x. x IN K ==> norm((LW:complex->complex) x) <= B /\
                       norm(frechet_derivative LW (at x) (ii * x)) <= B`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`LW:complex->complex`; `K:complex->bool`]
      COMPACT_CONTINUOUS_IMAGE) THEN
    MP_TAC(ISPECL [`\x. frechet_derivative (LW:complex->complex) (at x) (ii * x)`;
                   `K:complex->bool`] COMPACT_CONTINUOUS_IMAGE) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
    REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `B1:real` STRIP_ASSUME_TAC) THEN
    DISCH_THEN(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
    REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `B2:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `B1 + B2:real` THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `x:complex` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:complex`) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:complex`) THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `&0 < B1` THEN UNDISCH_TAC `&0 < B2` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?m. &0 < m /\ m <= &1 /\
        !x. x IN K
            ==> m <= &1 + Im(frechet_derivative (LW:complex->complex) (at x) (ii * x))`
  STRIP_ASSUME_TAC THENL
   [ASM_CASES_TAC `K:complex->bool = {}` THENL
     [EXISTS_TAC `&1` THEN ASM_REWRITE_TAC[NOT_IN_EMPTY] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL
     [`\x. &1 + Im(frechet_derivative (LW:complex->complex) (at x) (ii * x))`;
      `K:complex->bool`] CONTINUOUS_ATTAINS_INF) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[o_DEF; LIFT_ADD] THEN MATCH_MP_TAC CONTINUOUS_ON_ADD THEN
      REWRITE_TAC[CONTINUOUS_ON_CONST; IM_DEF] THEN
      MATCH_MP_TAC CONTINUOUS_ON_LIFT_COMPONENT_COMPOSE THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `x0:complex` (STRIP_ASSUME_TAC o BETA_RULE)) THEN
    EXISTS_TAC `min (&1) (&1 + Im(frechet_derivative (LW:complex->complex)
                                   (at x0) (ii * x0)))` THEN
    REWRITE_TAC[REAL_LT_MIN; REAL_MIN_LE; REAL_LE_REFL; REAL_LT_01] THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (term_match [] `!z. z IN (S:complex->bool) DIFF {vec 0} ==> &0 < q z`)
            (concl th))) THEN ASM SET_TAC[];
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`m:real`; `B:real`] THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `z:complex` THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(z = Cx(&0))` ASSUME_TAC THENL
   [UNDISCH_TAC `(z:complex) IN S DIFF {vec 0}` THEN
    REWRITE_TAC[IN_DIFF; IN_SING; COMPLEX_VEC_0] THEN SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `r = norm(z:complex)` THEN
  ABBREV_TAC `e = moi_pdl_nz z` THEN
  SUBGOAL_THEN `norm(e:complex) = &1 /\ z = Cx r * e /\ &0 < r`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["e"; "r"] THEN
    ASM_SIMP_TAC[MOI_PDL_NZ_PROPS; NORM_POS_LT; COMPLEX_VEC_0];
    ALL_TAC] THEN
  SUBGOAL_THEN `(e:complex) IN K` ASSUME_TAC THENL
   [EXPAND_TAC "K" THEN REWRITE_TAC[IN_INTER; IN_SPHERE_0] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `e = inv r % (z:complex)` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[COMPLEX_CMUL; COMPLEX_MUL_ASSOC; GSYM CX_MUL] THEN
      ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ; COMPLEX_MUL_LID];
      MATCH_MP_TAC CONIC_MUL THEN ASM_REWRITE_TAC[REAL_LE_INV_EQ] THEN
      CONJ_TAC THENL [ASM SET_TAC[]; ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(e:complex) IN V` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(SUBST1_TAC o check (fun th -> concl th = `z = Cx r * e`)) THEN
  SUBGOAL_THEN
   `(LW:complex->complex)(Cx r * e) = LW e /\
    frechet_derivative LW (at (Cx r * e)) (ii * (Cx r * e)) =
    frechet_derivative LW (at e) (ii * e)`
  (fun th -> REWRITE_TAC[th]) THENL
   [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[]]);;

(* ========================================================================= *)
(* D2 part III, the radial cutoff in the logarithm of the                    *)
(* radius, the Jacobian formula for z cexp(c(z) L(z)), and the assembly.   *)
(* ========================================================================= *)

let moi_pdl_cut = new_definition
 `moi_pdl_cut a k (y:complex) = smooth_step((log(norm y) - a) / k)`;;

let MOI_PDL_CUT_BOUNDS = prove
 (`!a k y. &0 <= moi_pdl_cut a k y /\ moi_pdl_cut a k y <= &1`,
  REWRITE_TAC[moi_pdl_cut; SMOOTH_STEP_BOUNDS]);;

let MOI_PDL_CUT_ZERO = prove
 (`!a k y. &0 < k /\ ~(y = Cx(&0)) /\ norm y <= exp a
           ==> moi_pdl_cut a k y = &0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[moi_pdl_cut] THEN
  MATCH_MP_TAC SMOOTH_STEP_0 THEN ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
  REWRITE_TAC[REAL_MUL_LZERO] THEN
  MATCH_MP_TAC(REAL_ARITH `l <= a ==> l - a <= &0`) THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM LOG_EXP] THEN
  MATCH_MP_TAC LOG_MONO_LE_IMP THEN
  ASM_REWRITE_TAC[NORM_POS_LT; COMPLEX_VEC_0]);;

let MOI_PDL_CUT_ONE = prove
 (`!a k y. &0 < k /\ exp(a + k) <= norm y ==> moi_pdl_cut a k y = &1`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[moi_pdl_cut] THEN
  MATCH_MP_TAC SMOOTH_STEP_1 THEN ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
  MATCH_MP_TAC(REAL_ARITH `a + k <= l ==> &1 * k <= l - a`) THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM LOG_EXP] THEN
  MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REWRITE_TAC[REAL_EXP_POS_LT]);;

let MOI_PDL_LCUT_DERIV = prove
 (`!a k (y:complex). &0 < k /\ ~(y = Cx(&0))
       ==> ((\y. lift(moi_pdl_cut a k y)) has_derivative
            (\h. lift(moi_pdl_dstep((log(norm y) - a) / k) *
                      ((y dot h) / (k * norm y pow 2))))) (at y)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < norm(y:complex)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT; COMPLEX_VEC_0]; ALL_TAC] THEN
  REWRITE_TAC[moi_pdl_cut] THEN
  SUBGOAL_THEN
   `!h:complex. moi_pdl_dstep((log(norm y) - a) / k) *
                ((y dot h) / (k * norm y pow 2)) =
                (inv(norm y) / k * moi_pdl_dstep((log(norm y) - a) / k)) *
                ((y dot h) / norm y)`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN UNDISCH_TAC `&0 < norm(y:complex)` THEN
    UNDISCH_TAC `&0 < k` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  MATCH_MP_TAC(REWRITE_RULE[] (ISPECL
   [`\y:complex. norm y`; `\h:complex. (y dot h) / norm(y:complex)`]
   MOI_PDL_REAL_CHAIN)) THEN
  ASM_SIMP_TAC[MOI_PDL_NORM_DERIV; COMPLEX_VEC_0] THEN
  REAL_DIFF_TAC THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `&0 < norm(y:complex)` THEN UNDISCH_TAC `&0 < k` THEN
  CONV_TAC REAL_FIELD);;

let MOI_PDL_CUT_SMOOTH = prove
 (`!a k. &0 < k
         ==> smooth_map_on ((:complex) DIFF {Cx(&0)})
               (\y. lift(moi_pdl_cut a k y))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[moi_pdl_cut] THEN
  MP_TAC(ISPECL [`(:complex) DIFF {Cx(&0)}`;
                 `\y:complex. lift((log(norm y) - a) / k)`]
    SMOOTH_MAP_ON_SMOOTH_STEP_COMPOSE) THEN
  REWRITE_TAC[LIFT_DROP; MOI_PDL_OPEN_PUNCTURED] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  SUBGOAL_THEN
   `(\y:complex. lift((log(norm y) - a) / k)) =
    (\y. lift(inv k * (log(norm y) - a)))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; LIFT_EQ] THEN GEN_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC(REWRITE_RULE[LIFT_DROP] (ISPECL
   [`(:complex) DIFF {Cx(&0)}`; `inv k`;
    `\y:complex. lift(log(norm y) - a)`] SMOOTH_MAP_ON_LIFT_CMUL)) THEN
  REWRITE_TAC[MOI_PDL_OPEN_PUNCTURED] THEN
  MATCH_MP_TAC MOI_PDL_SMOOTH_RSUB THEN
  REWRITE_TAC[MOI_PDL_OPEN_PUNCTURED; SMOOTH_MAP_ON_CONST] THEN
  MP_TAC(ISPECL [`(:complex) DIFF {Cx(&0)}`; `\y:complex. lift(norm y)`]
    SMOOTH_MAP_ON_LIFT_LOG) THEN
  REWRITE_TAC[LIFT_DROP; MOI_PDL_OPEN_PUNCTURED] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[IN_DIFF; IN_UNIV; IN_SING; NORM_POS_LT; COMPLEX_VEC_0] THEN
  MP_TAC(ISPECL [`(:complex) DIFF {Cx(&0)}`; `\z:complex. z`]
    SMOOTH_MAP_ON_LIFT_NORM) THEN
  REWRITE_TAC[MOI_PDL_OPEN_PUNCTURED; SMOOTH_MAP_ON_ID; IN_DIFF; IN_UNIV;
              IN_SING; COMPLEX_VEC_0]);;

let MOI_PDL_IM_CNJ_SCALE = prove
 (`!w a b. Im(cnj(w * a) * (w * b)) = norm w pow 2 * Im(cnj a * b)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CNJ_MUL] THEN
  SUBGOAL_THEN `(cnj w * cnj a) * w * b = (cnj w * w) * (cnj a * b)`
  SUBST1_TAC THENL [CONV_TAC COMPLEX_RING; ALL_TAC] THEN
  REWRITE_TAC[COMPLEX_MUL_CNJ; GSYM CX_POW; IM_MUL_CX]);;

let MOI_PDL_IM_FORMULA = prove
 (`!L D c k. Im(cnj(Cx(&1) + Cx k * L) * (ii + Cx c * D)) =
             &1 + c * Im D + k * Re L + c * k * Im(cnj L * D)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[complex_mul; cnj; RE; IM; RE_ADD; IM_ADD; RE_CX; IM_CX; RE_II;
              IM_II] THEN
  REAL_ARITH_TAC);;

let MOI_PDL_JAC_FORMULA = prove
 (`!(L:complex->complex) DL (c:complex->real) dc z.
     ~(z = Cx(&0)) /\ (L has_derivative DL) (at z) /\
     ((\y. lift(c y)) has_derivative (\h. lift(dc h))) (at z) /\
     DL z = Cx(&0) /\ dc(ii * z) = &0
     ==> det(jacobian (\y. y * cexp(Cx(c y) * L y)) (at z)) =
         norm(cexp(Cx(c z) * L z)) pow 2 *
         (&1 + c z * Im(DL(ii * z)) + dc z * Re(L z) +
          c z * dc z * Im(cnj(L z) * DL(ii * z)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `linear(DL:complex->complex) /\ linear(\h:complex. lift((dc:complex->real) h))`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[has_derivative]; ALL_TAC] THEN
  SUBGOAL_THEN `((\y:complex. Cx((c:complex->real) y)) has_derivative (\h:complex. Cx((dc:complex->real) h))) (at z)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `(\y:complex. Cx((c:complex->real) y)) = (Cx o drop) o (\y. lift(c y))`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_DROP]; ALL_TAC] THEN
    SUBGOAL_THEN `(\h:complex. Cx((dc:complex->real) h)) = (Cx o drop) o (\h. lift(dc h))`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_DROP]; ALL_TAC] THEN
    MATCH_MP_TAC DIFF_CHAIN_AT THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN
    REWRITE_TAC[linear; o_THM; DROP_ADD; DROP_CMUL; CX_ADD; CX_MUL;
                COMPLEX_CMUL];
    ALL_TAC] THEN
  ABBREV_TAC `E = cexp(Cx((c:complex->real) z) * (L:complex->complex) z)` THEN
  SUBGOAL_THEN
   `((\y. y * cexp(Cx((c:complex->real) y) * (L:complex->complex) y)) has_derivative
     (\h. z * (E * (Cx(c z) * (DL:complex->complex) h + Cx((dc:complex->real) h) * L z)) + h * E)) (at z)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`complex_mul`; `\y:complex. y`;
                   `\y. cexp(Cx((c:complex->real) y) * (L:complex->complex) y)`;
                   `\h:complex. h`;
                   `\h. E * (Cx((c:complex->real) z) * (DL:complex->complex) h + Cx((dc:complex->real) h) * L z)`;
                   `z:complex`] HAS_DERIVATIVE_BILINEAR_AT) THEN
    REWRITE_TAC[BILINEAR_COMPLEX_MUL; HAS_DERIVATIVE_ID] THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    SUBGOAL_THEN
     `(\y. cexp(Cx((c:complex->real) y) * (L:complex->complex) y)) =
      cexp o (\y. Cx(c y) * L y)`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    SUBGOAL_THEN
     `(\h. E * (Cx((c:complex->real) z) * (DL:complex->complex) h + Cx((dc:complex->real) h) * (L:complex->complex) z)) =
      (\w. E * w) o (\h. Cx(c z) * DL h + Cx(dc h) * L z)`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC DIFF_CHAIN_AT THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`complex_mul`; `\y:complex. Cx((c:complex->real) y)`;
                     `L:complex->complex`; `\h:complex. Cx((dc:complex->real) h)`; `DL:complex->complex`;
                     `z:complex`] HAS_DERIVATIVE_BILINEAR_AT) THEN
      ASM_REWRITE_TAC[BILINEAR_COMPLEX_MUL];
      EXPAND_TAC "E" THEN REWRITE_TAC[GSYM has_complex_derivative] THEN
      REWRITE_TAC[HAS_COMPLEX_DERIVATIVE_CEXP]];
    ALL_TAC] THEN
  REWRITE_TAC[jacobian] THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
  SUBGOAL_THEN `~(norm(z:complex) pow 2 = &0)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_POW_EQ_0; COMPLEX_NORM_ZERO] THEN ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC
   `TT = \h. z * (E * (Cx((c:complex->real) z) * (DL:complex->complex) h +
                       Cx((dc:complex->real) h) * (L:complex->complex) z)) + h * E` THEN
  SUBGOAL_THEN `linear(TT:complex->complex)` ASSUME_TAC THENL
   [UNDISCH_TAC
     `((\y. y * cexp(Cx((c:complex->real) y) * (L:complex->complex) y))
       has_derivative TT) (at z)` THEN
    SIMP_TAC[has_derivative];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`TT:complex->complex`; `z:complex`] MOI_PDL_DET_ROT) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `(TT:complex->complex) z =
    (z * E) * (Cx(&1) + Cx((dc:complex->real) z) * (L:complex->complex) z) /\
    TT(ii * z) =
    (z * E) * (ii + Cx((c:complex->real) z) * (DL:complex->complex)(ii * z))`
  (fun th -> REWRITE_TAC[th]) THENL
   [EXPAND_TAC "TT" THEN ASM_REWRITE_TAC[] THEN CONV_TAC COMPLEX_RING;
    ALL_TAC] THEN
  REWRITE_TAC[MOI_PDL_IM_CNJ_SCALE; MOI_PDL_IM_FORMULA; COMPLEX_NORM_MUL;
              REAL_POW_MUL] THEN
  UNDISCH_TAC `~(norm(z:complex) pow 2 = &0)` THEN CONV_TAC REAL_FIELD);;

let MOI_PDL_JAC_EST = prove
 (`!c k m bB eta Lz D.
     &0 <= c /\ c <= &1 /\ abs k <= eta /\ &0 < m /\ m <= &1 /\
     m <= &1 + Im D /\ norm Lz <= bB /\ norm D <= bB /\
     eta * (bB + bB pow 2) < m
     ==> &0 < &1 + c * Im D + k * Re Lz + c * k * Im(cnj Lz * D)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `m <= &1 + c * Im D` ASSUME_TAC THENL
   [SUBGOAL_THEN `c * m <= c * (&1 + Im D)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(&1 - c) * m <= (&1 - c) * &1` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= eta /\ &0 <= bB` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(SPEC `k:real` REAL_ABS_POS) THEN ASM_REAL_ARITH_TAC;
      MP_TAC(ISPEC `Lz:complex` NORM_POS_LE) THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `abs(k * Re Lz) <= eta * bB` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_ABS_MUL] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
    ASM_REWRITE_TAC[REAL_ABS_POS] THEN
    MP_TAC(SPEC `Lz:complex` COMPLEX_NORM_GE_RE_IM) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `abs(c * k * Im(cnj Lz * D)) <= eta * bB pow 2` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_ABS_MUL] THEN
    SUBGOAL_THEN `abs(Im(cnj Lz * D)) <= bB pow 2` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `norm(cnj Lz * D)` THEN
      CONJ_TAC THENL [REWRITE_TAC[COMPLEX_NORM_GE_RE_IM]; ALL_TAC] THEN
      REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CNJ; REAL_POW_2] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[NORM_POS_LE];
      ALL_TAC] THEN
    SUBGOAL_THEN `abs c <= &1` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1 * eta * bB pow 2` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_ABS_POS] THEN
      CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_ABS_POS]; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_ABS_POS];
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  UNDISCH_TAC `eta * (bB + bB pow 2) < m` THEN
  REWRITE_TAC[REAL_ADD_LDISTRIB] THEN ASM_REAL_ARITH_TAC);;

let MOI_PDL_DOT_II = prove
 (`!x:complex. x dot (ii * x) = &0`,
  GEN_TAC THEN REWRITE_TAC[DOT_2; GSYM RE_DEF; GSYM IM_DEF; RE_MUL_II;
                           IM_MUL_II] THEN REAL_ARITH_TAC);;

let MOI_PDL_ZERO_DIV = prove
 (`!x. &0 / x = &0`,
  REWRITE_TAC[real_div; REAL_MUL_LZERO]);;

let MOI_PDL_PIECE_FINAL = prove
 (`!(P:complex->complex) (S:complex->bool) u (g:complex->complex) lw
    m bB a k R1 bS.
     (!t z. &0 <= t ==> P(Cx t * z) = Cx t * P z) /\
     (!z. ~(z = Cx(&0)) ==> ~(P z = Cx(&0))) /\
     closed S /\ convex S /\ conic S /\ ~(S = {}) /\
     open u /\ S DIFF {vec 0} SUBSET u /\ smooth_map_on u g /\
     (!x. x IN S ==> g x = P x) /\
     (!x. x IN S DIFF {vec 0} ==> &0 < det(jacobian g (at x))) /\
     lw continuous_on ((:complex) DIFF {Cx(&0)}) /\
     (!z. ~(z = Cx(&0)) ==> P z = z * cexp(lw z)) /\
     (!z t. ~(z = Cx(&0)) /\ &0 < t ==> lw(Cx t * z) = lw z) /\
     &0 < m /\ m <= &1 /\ &0 < bB /\
     (!z. z IN S DIFF {vec 0}
          ==> m <= &1 + Im(frechet_derivative (moi_pdl_lwf S g lw) (at z)
                             (ii * z)) /\
              norm(moi_pdl_lwf S g lw z) <= bB /\
              norm(frechet_derivative (moi_pdl_lwf S g lw) (at z) (ii * z))
              <= bB) /\
     &0 < R1 /\ &0 < k /\ exp a = &2 * R1 /\
     (!t. moi_pdl_dstep t <= bS) /\ bS / k * (bB + bB pow 2) < m
     ==> ?v G. open v /\ {x | x IN S /\ R1 / &2 <= norm x} SUBSET v /\
               smooth_map_on v G /\
               (!x. x IN S /\ R1 / &2 <= norm x
                    ==> G x = x * cexp(Cx(moi_pdl_cut a k x) * lw x)) /\
               (!x. x IN v /\ norm x < R1
                    ==> G x = x * cexp(Cx(moi_pdl_cut a k x) * lw x)) /\
               (!x. x IN S /\ R1 / &2 <= norm x
                    ==> &0 < det(jacobian G (at x)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`P:complex->complex`; `S:complex->bool`; `u:complex->bool`;
                 `g:complex->complex`; `lw:complex->complex`]
    MOI_PDL_LDOM_PROPS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`P:complex->complex`; `S:complex->bool`; `u:complex->bool`;
                 `g:complex->complex`; `lw:complex->complex`]
    MOI_PDL_PIECE_DERIVS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `V = moi_pdl_ldom S u (g:complex->complex)` THEN
  ABBREV_TAC `LW = moi_pdl_lwf S (g:complex->complex) lw` THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!z. z IN V ==> ~(z = Cx(&0))` ASSUME_TAC THENL
   [X_GEN_TAC `z:complex` THEN DISCH_TAC THEN
    SUBGOAL_THEN `z IN moi_pdl_wdom u (g:complex->complex)` MP_TAC THENL
     [ASM SET_TAC[]; REWRITE_TAC[moi_pdl_wdom; IN_ELIM_THM] THEN SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `{x | x IN S /\ R1 / &2 <= norm x} SUBSET S DIFF {vec 0:complex}`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_DIFF; IN_SING] THEN
    X_GEN_TAC `x:complex` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN UNDISCH_TAC `R1 / &2 <= norm(x:complex)` THEN
    ASM_REWRITE_TAC[NORM_0] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `V:complex->bool` THEN
  EXISTS_TAC `\z. z * cexp(Cx(moi_pdl_cut a k z) * (LW:complex->complex) z)` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM SET_TAC[];
    MATCH_MP_TAC MOI_PDL_SMOOTH_CMUL_FUN THEN
    ASM_REWRITE_TAC[SMOOTH_MAP_ON_ID] THEN
    MATCH_MP_TAC MOI_PDL_SMOOTH_CEXP THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_PDL_SMOOTH_CMUL_FUN THEN ASM_REWRITE_TAC[ETA_AX] THEN
    MP_TAC(ISPECL [`V:complex->bool`;
                   `\y:complex. lift(moi_pdl_cut a k y)`]
      MOI_PDL_SMOOTH_CX_DROP) THEN
    ASM_REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
    EXISTS_TAC `(:complex) DIFF {Cx(&0)}` THEN
    ASM_SIMP_TAC[MOI_PDL_CUT_SMOOTH] THEN
    REWRITE_TAC[SUBSET; IN_DIFF; IN_UNIV; IN_SING] THEN ASM_MESON_TAC[];
    X_GEN_TAC `x:complex` THEN STRIP_TAC THEN
    SUBGOAL_THEN `x IN (S:complex->bool) DIFF {vec 0}` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[];
    X_GEN_TAC `x:complex` THEN STRIP_TAC THEN
    SUBGOAL_THEN `moi_pdl_cut a k x = &0` (fun th -> REWRITE_TAC[th]) THENL
     [MATCH_MP_TAC MOI_PDL_CUT_ZERO THEN ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[COMPLEX_MUL_LZERO]];
    ALL_TAC] THEN
  X_GEN_TAC `x:complex` THEN STRIP_TAC THEN
  SUBGOAL_THEN `x IN (S:complex->bool) DIFF {vec 0} /\ x IN V`
  STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~(x = Cx(&0))` ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL
   [`LW:complex->complex`; `frechet_derivative (LW:complex->complex) (at x)`;
    `moi_pdl_cut a k`;
    `\h:complex. moi_pdl_dstep((log(norm(x:complex)) - a) / k) *
                 ((x dot h) / (k * norm x pow 2))`;
    `x:complex`] MOI_PDL_JAC_FORMULA) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[MOI_PDL_LCUT_DERIV; MOI_PDL_DOT_II; MOI_PDL_ZERO_DIV; REAL_MUL_LZERO;
                 REAL_MUL_RZERO] THEN
    REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `V:complex->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN REWRITE_TAC[COMPLEX_NORM_NZ; CEXP_NZ];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_PDL_JAC_EST THEN
  MAP_EVERY EXISTS_TAC [`m:real`; `bB:real`; `bS / k`] THEN
  ASM_SIMP_TAC[MOI_PDL_CUT_BOUNDS] THEN
  SUBGOAL_THEN `((x:complex) dot x) / (k * norm x pow 2) = inv(k:real)` SUBST1_TAC THENL
   [REWRITE_TAC[DOT_SQUARE_NORM] THEN
    SUBGOAL_THEN `~(norm(x:complex) pow 2 = &0)` MP_TAC THENL
     [ASM_REWRITE_TAC[REAL_POW_EQ_0; COMPLEX_NORM_ZERO] THEN ARITH_TAC;
      ALL_TAC] THEN
    UNDISCH_TAC `&0 < k` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ x <= y ==> abs x <= y`) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_SIMP_TAC[MOI_PDL_DSTEP_POS; REAL_LE_INV_EQ; REAL_LT_IMP_LE];
    REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE]]);;

let MOI_PDL_PPRIME = prove
 (`!(P:complex->complex) lw a k R1 R2.
     (!z. ~(z = Cx(&0)) ==> P z = z * cexp(lw z)) /\
     lw continuous_on ((:complex) DIFF {Cx(&0)}) /\
     &0 < k /\ &0 < R1 /\ exp a = &2 * R1 /\ exp(a + k) = R2
     ==> (\z. z * cexp(Cx(moi_pdl_cut a k z) * lw z)) continuous_on (:complex) /\
         (!x. R2 <= norm x ==> x * cexp(Cx(moi_pdl_cut a k x) * lw x) = P x) /\
         (!x. norm x < &2 * R1
              ==> x * cexp(Cx(moi_pdl_cut a k x) * lw x) = x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!x. norm x < &2 * R1 ==> x * cexp(Cx(moi_pdl_cut a k x) * lw x) = x`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:complex` THEN DISCH_TAC THEN
    ASM_CASES_TAC `x = Cx(&0)` THEN ASM_REWRITE_TAC[COMPLEX_MUL_LZERO] THEN
    SUBGOAL_THEN `moi_pdl_cut a k x = &0` SUBST1_TAC THENL
     [MATCH_MP_TAC MOI_PDL_CUT_ZERO THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC;
      REWRITE_TAC[COMPLEX_MUL_LZERO; CEXP_0; COMPLEX_MUL_RID]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ALL_TAC;
    X_GEN_TAC `x:complex` THEN DISCH_TAC THEN
    SUBGOAL_THEN `~(x = Cx(&0))` ASSUME_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC `R2 <= norm(x:complex)` THEN
      ASM_REWRITE_TAC[COMPLEX_NORM_CX; REAL_ABS_NUM] THEN
      EXPAND_TAC "R2" THEN MP_TAC(SPEC `a + k:real` REAL_EXP_POS_LT) THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `moi_pdl_cut a k x = &1` SUBST1_TAC THENL
     [MATCH_MP_TAC MOI_PDL_CUT_ONE THEN ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[COMPLEX_MUL_LID]]] THEN
  MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN
  X_GEN_TAC `x:complex` THEN DISCH_THEN(K ALL_TAC) THEN
  ASM_CASES_TAC `x = Cx(&0)` THENL
   [MATCH_MP_TAC CONTINUOUS_TRANSFORM_AT THEN
    MAP_EVERY EXISTS_TAC [`\z:complex. z`; `&2 * R1`] THEN
    REWRITE_TAC[CONTINUOUS_AT_ID] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `y:complex` THEN ASM_REWRITE_TAC[dist; COMPLEX_SUB_RZERO] THEN
    DISCH_TAC THEN CONV_TAC SYM_CONV THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_COMPLEX_MUL THEN REWRITE_TAC[CONTINUOUS_AT_ID] THEN
  ONCE_REWRITE_TAC[GSYM o_DEF] THEN MATCH_MP_TAC CONTINUOUS_AT_COMPOSE THEN
  REWRITE_TAC[CONTINUOUS_AT_CEXP] THEN
  MATCH_MP_TAC CONTINUOUS_COMPLEX_MUL THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`a:real`; `k:real`] MOI_PDL_CUT_SMOOTH) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o MATCH_MP SMOOTH_MAP_ON_CONTINUOUS_ON) THEN
    SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_AT; MOI_PDL_OPEN_PUNCTURED] THEN
    DISCH_THEN(MP_TAC o SPEC `x:complex`) THEN
    ASM_REWRITE_TAC[IN_DIFF; IN_UNIV; IN_SING] THEN DISCH_TAC THEN
    SUBGOAL_THEN `(\z:complex. Cx(moi_pdl_cut a k z)) =
                  (Cx o drop) o (\y. lift(moi_pdl_cut a k y))`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_DROP]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_AT_COMPOSE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC LINEAR_CONTINUOUS_AT THEN
    REWRITE_TAC[linear; o_THM; DROP_ADD; DROP_CMUL; CX_ADD; CX_MUL;
                COMPLEX_CMUL];
    UNDISCH_TAC `(lw:complex->complex) continuous_on ((:complex) DIFF {Cx(&0)})` THEN
    SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_AT; MOI_PDL_OPEN_PUNCTURED] THEN
    DISCH_THEN(MP_TAC o SPEC `x:complex`) THEN
    ASM_REWRITE_TAC[IN_DIFF; IN_UNIV; IN_SING; ETA_AX]]);;

let MOI_PDL_KBOUND = prove
 (`!bS X m k. &0 < m /\ &0 < k /\ bS * X / m < k ==> bS / k * X < m`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `bS / k * X = (bS * X / m) * (m / k)` SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < m` THEN UNDISCH_TAC `&0 < k` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `k * m / k` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_RMUL THEN ASM_SIMP_TAC[REAL_LT_DIV];
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN UNDISCH_TAC `&0 < k` THEN
    CONV_TAC REAL_FIELD]);;

let MOI_SMO_VERTEX2 = prove
 (`MOI_SMO_VERTEX2_STATEMENT`,
  REWRITE_TAC[MOI_SMO_VERTEX2_STATEMENT] THEN
  MAP_EVERY X_GEN_TAC [`P:real^2->real^2`; `S:num->real^2->bool`; `n:num`;
                       `R2:real`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `!i. i < n
        ==> ?u (g:real^2->real^2).
              open u /\ (S:num->real^2->bool) i DIFF {vec 0} SUBSET u /\
              smooth_map_on u g /\ (!x. x IN S i ==> g x = P x) /\
              (!x. x IN S i DIFF {vec 0} ==> &0 < det(jacobian g (at x)))`
  (LABEL_TAC "pc") THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`P:complex->complex`; `S:num->complex->bool`; `n:num`]
    MOI_PDL_GLOBAL_LOG) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `lw:complex->complex` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPEC `P:complex->complex` MOI_PDL_HOM_BASICS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN
   `!i. ?uu gg mm bb.
        i < n /\ ~((S:num->complex->bool) i = {})
        ==> open uu /\ S i DIFF {vec 0} SUBSET uu /\ smooth_map_on uu gg /\
            (!x. x IN S i ==> gg x = P x) /\
            (!x. x IN S i DIFF {vec 0} ==> &0 < det(jacobian gg (at x))) /\
            &0 < mm /\ mm <= &1 /\ &0 < bb /\
            (!z. z IN S i DIFF {vec 0}
                 ==> mm <= &1 + Im(frechet_derivative
                                     (moi_pdl_lwf (S i) gg lw) (at z) (ii * z)) /\
                     norm(moi_pdl_lwf (S i) gg lw z) <= bb /\
                     norm(frechet_derivative (moi_pdl_lwf (S i) gg lw) (at z)
                            (ii * z)) <= bb)`
  MP_TAC THENL
   [X_GEN_TAC `i:num` THEN
    ASM_CASES_TAC `i < n /\ ~((S:num->complex->bool) i = {})` THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC) THEN
    USE_THEN "pc" (MP_TAC o C MATCH_MP (ASSUME `(i:num) < n`)) THEN
    DISCH_THEN(X_CHOOSE_THEN `u0:complex->bool` (X_CHOOSE_THEN
      `g0:complex->complex` STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`u0:complex->bool`; `g0:complex->complex`] THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_PDL_PIECE_BOUNDS THEN
    MAP_EVERY EXISTS_TAC [`P:complex->complex`; `u0:complex->bool`] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `uu:num->complex->bool` (X_CHOOSE_THEN
    `gg:num->complex->complex` (X_CHOOSE_THEN `mm:num->real` (X_CHOOSE_THEN
    `bb:num->real` (LABEL_TAC "pieces"))))) THEN
  X_CHOOSE_THEN `bS:real` STRIP_ASSUME_TAC MOI_PDL_DSTEP_BOUND THEN
  MP_TAC(ISPECL [`\i:num. bS * ((bb:num->real) i + bb i pow 2) / (mm:num->real) i`;
                 `{i:num | i < n}`]
    UPPER_BOUND_FINITE_SET_REAL) THEN
  REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_TAC `b0:real`) THEN
  SUBGOAL_THEN
   `&0 < abs b0 + &1 /\ &0 < exp(log R2 - (abs b0 + &1)) / &2 /\
    exp(log R2 - (abs b0 + &1)) / &2 < R2 /\
    exp((log R2 - (abs b0 + &1)) + (abs b0 + &1)) = R2`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `exp(log R2) = R2` ASSUME_TAC THENL
     [ASM_SIMP_TAC[EXP_LOG]; ALL_TAC] THEN
    REWRITE_TAC[REAL_SUB_ADD; ASSUME `exp(log R2) = R2`] THEN
    MP_TAC(SPEC `log R2 - (abs b0 + &1)` REAL_EXP_POS_LT) THEN
    SUBGOAL_THEN `exp(log R2 - (abs b0 + &1)) < R2` MP_TAC THENL
     [GEN_REWRITE_TAC RAND_CONV [GSYM(ASSUME `exp(log R2) = R2`)] THEN
      REWRITE_TAC[REAL_EXP_MONO_LT] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `k = abs b0 + &1` THEN
  ABBREV_TAC `a = log R2 - k` THEN
  ABBREV_TAC `R1 = exp a / &2` THEN
  SUBGOAL_THEN `exp a = &2 * R1` ASSUME_TAC THENL
   [EXPAND_TAC "R1" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`P:complex->complex`; `lw:complex->complex`; `a:real`;
                 `k:real`; `R1:real`; `R2:real`] MOI_PDL_PPRIME) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  EXISTS_TAC `\z:complex. z * cexp(Cx(moi_pdl_cut a k z) * lw z)` THEN
  EXISTS_TAC `R1:real` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [EXISTS_TAC `ball(vec 0:complex,&2 * R1)` THEN REWRITE_TAC[OPEN_BALL] THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_CBALL_0; IN_BALL_0] THEN
      UNDISCH_TAC `&0 < R1` THEN REAL_ARITH_TAC;
      MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN EXISTS_TAC `\z:complex. z` THEN
      REWRITE_TAC[OPEN_BALL; SMOOTH_MAP_ON_ID; IN_BALL_0] THEN
      ASM_SIMP_TAC[];
      X_GEN_TAC `x:complex` THEN REWRITE_TAC[IN_BALL_0] THEN DISCH_TAC THEN
      SUBGOAL_THEN
       `jacobian (\z. z * cexp(Cx(moi_pdl_cut a k z) * (lw:complex->complex) z))
                 (at x) = jacobian (\z:complex. z) (at x)`
      SUBST1_TAC THENL
       [REWRITE_TAC[jacobian] THEN AP_TERM_TAC THEN
        MATCH_MP_TAC FRECHET_DERIVATIVE_LOCAL THEN
        EXISTS_TAC `&2 * R1 - norm(x:complex)` THEN
        CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        X_GEN_TAC `y:complex` THEN REWRITE_TAC[dist] THEN DISCH_TAC THEN
        REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        UNDISCH_TAC `norm(y - x:complex) < &2 * R1 - norm x` THEN
        NORM_ARITH_TAC;
        ALL_TAC] THEN
      REWRITE_TAC[jacobian] THEN
      MP_TAC(ISPEC `at(x:complex)` HAS_DERIVATIVE_ID) THEN
      DISCH_THEN(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
      REWRITE_TAC[MATRIX_ID; DET_I; REAL_LT_01]];
    ALL_TAC] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  ASM_CASES_TAC `(S:num->complex->bool) i = {}` THENL
   [ASM_REWRITE_TAC[NOT_IN_EMPTY; EMPTY_GSPEC] THEN
    MAP_EVERY EXISTS_TAC [`{}:complex->bool`; `\z:complex. z`] THEN
    REWRITE_TAC[OPEN_EMPTY; EMPTY_SUBSET; NOT_IN_EMPTY; SMOOTH_MAP_ON_ID];
    ALL_TAC] THEN
  USE_THEN "pieces" (MP_TAC o C MATCH_MP
    (CONJ (ASSUME `(i:num) < n`)
          (ASSUME `~((S:num->complex->bool) i = {})`))) THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`P:complex->complex`; `(S:num->complex->bool) i`;
                 `(uu:num->complex->bool) i`; `(gg:num->complex->complex) i`;
                 `lw:complex->complex`; `(mm:num->real) i`; `(bb:num->real) i`;
                 `a:real`; `k:real`; `R1:real`; `bS:real`]
    MOI_PDL_PIECE_FINAL) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[] THEN MATCH_MP_TAC MOI_PDL_KBOUND THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `b0:real` THEN
    ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[]]);;

