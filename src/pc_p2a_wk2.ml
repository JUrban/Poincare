(* ========================================================================= *)
(* Unit pc_p2a_wk2: comparison curves for the reduced distance of a flow     *)
(* read in a chart: a minimizer to (q, sb^2) followed in the chart near its  *)
(* end, moved by a spatial interpolation y + mu w or reparametrized in time, *)
(* gives admissible curves to nearby points; their s-form lengths are        *)
(* parametric integrals with uniform first and second order bounds.  Main    *)
(* results: the reduced distance read in a chart is locally Lipschitz (MT    *)
(* Prop 7.5(1), P2AW_LX_LOCLIP) and spatially semiconcave                    *)
(* (P2AW_LX_SEMICONC).                                                       *)
(* ========================================================================= *)

needs "src/pc_p2a_wk1.ml";;
needs "src/pc_p2a_wkdec.ml";;
needs "src/pc_p2a_lsv.ml";;
needs "src/pc_p2a_usc.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Uniform first and second order bounds for smooth functions near a compact *)
(* set, through the partial derivatives.                                     *)
(* ------------------------------------------------------------------------- *)

let P2AW_CONT_BOUND = prove
 (`!(g:real^M->real) k.
     compact k /\ (\x. lift(g x)) continuous_on k
     ==> ?B. &0 <= B /\ !x. x IN k ==> abs(g x) <= B`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\x. lift((g:real^M->real) x)`; `k:real^M->bool`] COMPACT_CONTINUOUS_IMAGE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
  REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE; NORM_LIFT] THEN
  MESON_TAC[REAL_LT_IMP_LE]);;

let P2AW_D1_EXPAND = prove
 (`!(f:real^M->real) u x.
     (\y. lift(f y)) differentiable (at x)
     ==> p2aw_d1 f u x = sum(1..dimindex(:M)) (\i. u$i * p2aw_d1 f (basis i) x)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p2aw_d1] THEN
  SUBGOAL_THEN `u = vsum(1..dimindex(:M)) (\i. (u:real^M)$i % basis i)`
   (fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV) [th]) THENL
   [REWRITE_TAC[BASIS_EXPANSION]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP LINEAR_FRECHET_DERIVATIVE) THEN
  SIMP_TAC[LINEAR_VSUM; FINITE_NUMSEG; o_DEF; LINEAR_CMUL; DROP_VSUM; DROP_CMUL]);;

let P2AW_D2_EXPAND = prove
 (`!(s:real^M->bool) (f:real^M->real) u x.
     open s /\ smooth_map_on s (\y. lift(f y)) /\ x IN s
     ==> p2aw_d2 f u x =
         sum(1..dimindex(:M)) (\i. sum(1..dimindex(:M)) (\j.
           u$i * u$j * p2aw_d1 (p2aw_d1 f (basis i)) (basis j) x))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!i. smooth_map_on s (\y. lift(p2aw_d1 (f:real^M->real) (basis i) y))`
  ASSUME_TAC THENL [ASM_SIMP_TAC[P2AW_D1_SMOOTH]; ALL_TAC] THEN
  SUBGOAL_THEN `!i. (\y. lift(p2aw_d1 (f:real^M->real) (basis i) y)) differentiable (at x)`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `s:real^M->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[P2AW_D2_D1] THEN
  SUBGOAL_THEN
   `p2aw_d1 (\y. p2aw_d1 (f:real^M->real) u y) u x =
    p2aw_d1 (\y. sum(1..dimindex(:M)) (\i. u$i * p2aw_d1 f (basis i) y)) u x`
  SUBST1_TAC THENL
   [MATCH_MP_TAC P2AW_D1_LOCAL THEN EXISTS_TAC `s:real^M->bool` THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `y:real^M` THEN DISCH_TAC THEN MATCH_MP_TAC P2AW_D1_EXPAND THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `s:real^M->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\i y. (u:real^M)$i * p2aw_d1 (f:real^M->real) (basis i) y`;
                 `1..dimindex(:M)`; `u:real^M`; `x:real^M`] P2AW_D1_SUM) THEN
  REWRITE_TAC[FINITE_NUMSEG] THEN ANTS_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN REWRITE_TAC[LIFT_CMUL] THEN
    MATCH_MP_TAC DIFFERENTIABLE_CMUL THEN ASM_REWRITE_TAC[];
    DISCH_THEN(fun th -> REWRITE_TAC[th])] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  ASM_SIMP_TAC[P2AW_D1_CMUL; ETA_AX] THEN
  MP_TAC(ISPECL [`p2aw_d1 (f:real^M->real) (basis i)`; `u:real^M`; `x:real^M`]
                P2AW_D1_EXPAND) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[ETA_AX]; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[GSYM SUM_LMUL]);;

(* Bounds of the first and second directional derivatives on a compact set. *)

let P2AW_HESS_BOUND = prove
 (`!(s:real^M->bool) (f:real^M->real) k.
     open s /\ smooth_map_on s (\y. lift(f y)) /\ compact k /\ k SUBSET s
     ==> ?B. &0 <= B /\
             !x u. x IN k
                   ==> abs(p2aw_d1 f u x) <= B * norm u /\
                       abs(p2aw_d2 f u x) <= B * norm u pow 2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!i. smooth_map_on s (\y. lift(p2aw_d1 (f:real^M->real) (basis i) y))`
  ASSUME_TAC THENL [ASM_SIMP_TAC[P2AW_D1_SMOOTH]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!i j. smooth_map_on s (\y. lift(p2aw_d1 (p2aw_d1 (f:real^M->real) (basis i)) (basis j) y))`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN MP_TAC(ISPECL [`s:real^M->bool`; `p2aw_d1 (f:real^M->real) (basis i)`;
                                       `basis j:real^M`] P2AW_D1_SMOOTH) THEN
    ASM_REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!g. smooth_map_on s (\y. lift((g:real^M->real) y)) ==> (\y. lift(g y)) continuous_on k`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `s:real^M->bool` THEN ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\x. sum(1..dimindex(:M)) (\i. abs(p2aw_d1 (f:real^M->real) (basis i) x)) +
         sum(1..dimindex(:M)) (\i. sum(1..dimindex(:M)) (\j.
           abs(p2aw_d1 (p2aw_d1 f (basis i)) (basis j) x)))`; `k:real^M->bool`] P2AW_CONT_BOUND) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[LIFT_ADD; LIFT_SUM; o_DEF] THEN
    MATCH_MP_TAC CONTINUOUS_ON_ADD THEN CONJ_TAC THEN
    MATCH_MP_TAC CONTINUOUS_ON_VSUM THEN REWRITE_TAC[FINITE_NUMSEG] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_LIFT_ABS THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC CONTINUOUS_ON_VSUM THEN REWRITE_TAC[FINITE_NUMSEG] THEN
      X_GEN_TAC `j:num` THEN DISCH_TAC THEN
      MATCH_MP_TAC CONTINUOUS_ON_LIFT_ABS THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `B:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`x:real^M`; `u:real^M`] THEN DISCH_TAC THEN
  SUBGOAL_THEN `x IN (s:real^M->bool)` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:real^M`) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `&0 <= sum(1..dimindex(:M)) (\i. abs(p2aw_d1 (f:real^M->real) (basis i) x)) /\
    &0 <= sum(1..dimindex(:M)) (\i. sum(1..dimindex(:M)) (\j.
           abs(p2aw_d1 (p2aw_d1 f (basis i)) (basis j) x)))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC[REAL_ABS_POS] THEN MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN
    REWRITE_TAC[REAL_ABS_POS];
    ALL_TAC] THEN
  DISCH_TAC THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`f:real^M->real`; `u:real^M`; `x:real^M`] P2AW_D1_EXPAND) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `s:real^M->bool` THEN
      ASM_REWRITE_TAC[];
      DISCH_THEN SUBST1_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum(1..dimindex(:M)) (\i. norm(u:real^M) *
                                         abs(p2aw_d1 (f:real^M->real) (basis i) x))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `sum(1..dimindex(:M)) (\i. abs((u:real^M)$i *
                                                p2aw_d1 (f:real^M->real) (basis i) x))` THEN
      REWRITE_TAC[SUM_ABS_NUMSEG] THEN MATCH_MP_TAC SUM_LE_NUMSEG THEN
      REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_ABS_MUL] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[COMPONENT_LE_NORM; REAL_ABS_POS];
      REWRITE_TAC[SUM_LMUL] THEN GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
      ASM_REAL_ARITH_TAC];
    MP_TAC(ISPECL [`s:real^M->bool`; `f:real^M->real`; `u:real^M`; `x:real^M`]
                  P2AW_D2_EXPAND) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum(1..dimindex(:M)) (\i. sum(1..dimindex(:M)) (\j. norm(u:real^M) pow 2 *
                  abs(p2aw_d1 (p2aw_d1 (f:real^M->real) (basis i)) (basis j) x)))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `sum(1..dimindex(:M)) (\i. abs(sum(1..dimindex(:M)) (\j.
                    (u:real^M)$i * u$j *
                    p2aw_d1 (p2aw_d1 (f:real^M->real) (basis i)) (basis j) x)))` THEN
      REWRITE_TAC[SUM_ABS_NUMSEG] THEN MATCH_MP_TAC SUM_LE_NUMSEG THEN
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `sum(1..dimindex(:M)) (\j. abs((u:real^M)$i * u$j *
                    p2aw_d1 (p2aw_d1 (f:real^M->real) (basis i)) (basis j) x))` THEN
      REWRITE_TAC[SUM_ABS_NUMSEG] THEN MATCH_MP_TAC SUM_LE_NUMSEG THEN
      X_GEN_TAC `j:num` THEN STRIP_TAC THEN REWRITE_TAC[REAL_ABS_MUL; REAL_MUL_ASSOC] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_ABS_POS; REAL_POW_2] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[COMPONENT_LE_NORM; REAL_ABS_POS];
      REWRITE_TAC[SUM_LMUL] THEN GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
      ASM_REAL_ARITH_TAC]]);;

(* A compact subset of an open set has a compact thickening inside it.      *)

let P2AW_COMPACT_THICK = prove
 (`!(s:real^M->bool) k.
     open s /\ compact k /\ k SUBSET s
     ==> ?d kk. &0 < d /\ compact kk /\ kk SUBSET s /\
                !x e. x IN k /\ norm e <= d ==> x + e IN kk`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:real^M->bool`; `(:real^M) DIFF s`] SEPARATE_COMPACT_CLOSED) THEN
  ASM_REWRITE_TAC[GSYM OPEN_CLOSED] THEN ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d0:real` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`d0 / &2`; `{x + e:real^M | x IN k /\ e IN cball(vec 0,d0 / &2)}`] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [MATCH_MP_TAC COMPACT_SUMS THEN ASM_REWRITE_TAC[COMPACT_CBALL]; ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_CBALL_0] THEN X_GEN_TAC `z:real^M` THEN
    DISCH_THEN(X_CHOOSE_THEN `x:real^M` (X_CHOOSE_THEN `e:real^M` STRIP_ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`x:real^M`; `x + e:real^M`]) THEN
    ASM_REWRITE_TAC[IN_DIFF; IN_UNIV; dist; VECTOR_ARITH `x - (x + e):real^M = --e`;
                    NORM_NEG] THEN
    ASM_CASES_TAC `x + e IN (s:real^M->bool)` THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[IN_ELIM_THM; IN_CBALL_0] THEN MESON_TAC[]]);;

(* Uniform first order, Taylor and second difference bounds near k.         *)

let P2AW_SMOOTH_DIFF_BOUNDS = prove
 (`!(s:real^M->bool) (f:real^M->real) k.
     open s /\ smooth_map_on s (\y. lift(f y)) /\ compact k /\ k SUBSET s
     ==> ?d B. &0 < d /\ &0 <= B /\
               !x e. x IN k /\ norm e <= d
                     ==> x + e IN s /\ x - e IN s /\
                         abs(f(x + e) - f x) <= B * norm e /\
                         abs(f(x + e) - f x - p2aw_d1 f e x) <= B * norm e pow 2 /\
                         abs(f(x + e) + f(x - e) - &2 * f x) <= B * norm e pow 2`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^M->bool`; `k:real^M->bool`] P2AW_COMPACT_THICK) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (X_CHOOSE_THEN `kk:real^M->bool` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`s:real^M->bool`; `f:real^M->real`; `kk:real^M->bool`] P2AW_HESS_BOUND) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `B0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "H"))) THEN
  MAP_EVERY EXISTS_TAC [`d:real`; `&3 * B0 + &3 * B0 * d`] THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 <= a /\ &0 <= b ==> &0 <= &3 * a + &3 * b`) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`x:real^M`; `e:real^M`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!t. abs t <= &1 ==> x + t % e IN (kk:real^M->bool)` (LABEL_TAC "KK") THENL
   [X_GEN_TAC `t:real` THEN DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[NORM_MUL] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1 * norm(e:real^M)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[NORM_POS_LE]; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!t. abs t <= &1 ==> x + t % e IN (s:real^M->bool)` (LABEL_TAC "S") THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `x + t % e IN (kk:real^M->bool)` MP_TAC THENL
     [USE_THEN "KK" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!t. abs t <= &1 ==> abs(p2aw_d2 (f:real^M->real) e (x + t % e)) <=
                                    B0 * norm(e:real^M) pow 2`
  (LABEL_TAC "D2B") THENL
   [REPEAT STRIP_TAC THEN USE_THEN "H" (MP_TAC o SPECL [`x + t % e:real^M`; `e:real^M`]) THEN
    ANTS_TAC THENL [USE_THEN "KK" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\t. (f:real^M->real)(x + t % e)`; `\t. p2aw_d1 (f:real^M->real) e (x + t % e)`;
                 `\t. p2aw_d2 (f:real^M->real) e (x + t % e)`; `&1`;
                 `&2 * B0 * norm(e:real^M) pow 2`] P2AW_TAYLOR2) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THEN X_GEN_TAC `t:real` THEN DISCH_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC P2AW_LINE_DERIV THEN EXISTS_TAC `s:real^M->bool` THEN
        ASM_REWRITE_TAC[] THEN USE_THEN "S" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC P2AW_LINE_DERIV2 THEN EXISTS_TAC `s:real^M->bool` THEN
        ASM_REWRITE_TAC[] THEN USE_THEN "S" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      MATCH_MP_TAC(REAL_ARITH `abs a <= b /\ abs c <= b ==> abs(a - c) <= &2 * b`) THEN
      CONJ_TAC THEN USE_THEN "D2B" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[REAL_ABS_NUM; REAL_POS]];
    DISCH_THEN(LABEL_TAC "T")] THEN
  USE_THEN "T" (fun th -> MP_TAC(SPEC `&1` th) THEN MP_TAC(SPEC `-- &1` th)) THEN
  USE_THEN "D2B" (MP_TAC o SPEC `&0`) THEN
  USE_THEN "S" (fun th -> MP_TAC(SPEC `&1` th) THEN MP_TAC(SPEC `-- &1` th)) THEN
  USE_THEN "KK" (MP_TAC o SPEC `&0`) THEN
  REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_RID; VECTOR_MUL_LID; VECTOR_MUL_LNEG;
              GSYM VECTOR_SUB; REAL_ABS_NEG; REAL_ABS_NUM; REAL_LE_REFL; REAL_POS] THEN
  REWRITE_TAC[REAL_ARITH `(-- &1) pow 2 = &1`; REAL_POW_ONE; REAL_MUL_RID; REAL_MUL_LID] THEN
  REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  USE_THEN "H" (MP_TAC o SPECL [`x:real^M`; `e:real^M`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `B0 * norm(e:real^M) pow 2 <= B0 * d * norm e /\ &0 <= B0 * d * norm e pow 2`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&0 <= B0 * n * (d - n) ==> B0 * n pow 2 <= B0 * d * n`) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_MUL THEN
      ASM_REWRITE_TAC[NORM_POS_LE] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_MUL THEN
      REWRITE_TAC[REAL_LE_POW_2] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= B0 * norm(e:real^M)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[NORM_POS_LE]; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The vector-valued version of P2AW_SMOOTH_DIFF_BOUNDS, componentwise with  *)
(* the smallest radius and the sum of the constants.                         *)
(* ------------------------------------------------------------------------- *)

let P2AW_SMOOTH_DIFF_BOUNDS_VEC = prove
 (`!(s:real^M->bool) (Fm:real^M->real^P) k.
     open s /\ smooth_map_on s Fm /\ compact k /\ k SUBSET s
     ==> ?d B. &0 < d /\ &0 <= B /\
               !x e. x IN k /\ norm e <= d
                     ==> x + e IN s /\ x - e IN s /\
                         norm(Fm(x + e) - Fm x) <= B * norm e /\
                         norm(Fm(x + e) - Fm x - frechet_derivative Fm (at x) e)
                         <= B * norm e pow 2 /\
                         norm(Fm(x + e) + Fm(x - e) - &2 % Fm x) <= B * norm e pow 2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!p. ?d B. 1 <= p /\ p <= dimindex(:P)
              ==> &0 < d /\ &0 <= B /\
                  !x e. x IN k /\ norm e <= d
                        ==> x + e IN s /\ x - e IN s /\
                            abs((Fm:real^M->real^P)(x + e)$p - Fm x$p) <= B * norm e /\
                            abs(Fm(x + e)$p - Fm x$p - p2aw_d1 (\y. Fm y$p) e x)
                            <= B * norm e pow 2 /\
                            abs(Fm(x + e)$p + Fm(x - e)$p - &2 * Fm x$p) <= B * norm e pow 2`
  MP_TAC THENL
   [X_GEN_TAC `p:num` THEN REWRITE_TAC[RIGHT_EXISTS_IMP_THM] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`s:real^M->bool`; `\y. (Fm:real^M->real^P) y$p`; `k:real^M->bool`]
                  P2AW_SMOOTH_DIFF_BOUNDS) THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_LIFT_COMPONENT];
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `dd:num->real` (X_CHOOSE_THEN `BB:num->real` (LABEL_TAC "C"))) THEN
  SUBGOAL_THEN `FINITE(IMAGE (dd:num->real) (1..dimindex(:P))) /\
                ~(IMAGE (dd:num->real) (1..dimindex(:P)) = {})`
  STRIP_ASSUME_TAC THENL
   [SIMP_TAC[FINITE_IMAGE; FINITE_NUMSEG; IMAGE_EQ_EMPTY; NUMSEG_EMPTY; NOT_LT;
             DIMINDEX_GE_1];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`inf(IMAGE (dd:num->real) (1..dimindex(:P)))`;
                        `sum(1..dimindex(:P)) (BB:num->real)`] THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_INF_FINITE; FORALL_IN_IMAGE; IN_NUMSEG] THEN
    X_GEN_TAC `p:num` THEN DISCH_TAC THEN USE_THEN "C" (MP_TAC o SPEC `p:num`) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN X_GEN_TAC `p:num` THEN DISCH_TAC THEN
    USE_THEN "C" (MP_TAC o SPEC `p:num`) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`x:real^M`; `e:real^M`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!p. 1 <= p /\ p <= dimindex(:P) ==> norm(e:real^M) <= dd p` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `inf(IMAGE (dd:num->real) (1..dimindex(:P)))` THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[REAL_INF_LE_FINITE] THEN EXISTS_TAC `(dd:num->real) p` THEN
    REWRITE_TAC[REAL_LE_REFL; IN_IMAGE; IN_NUMSEG] THEN EXISTS_TAC `p:num` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^M) IN s` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(Fm:real^M->real^P) differentiable at x` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `s:real^M->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!p. 1 <= p /\ p <= dimindex(:P)
        ==> p2aw_d1 (\y. (Fm:real^M->real^P) y$p) e x = frechet_derivative Fm (at x) e$p`
  (LABEL_TAC "DC") THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[p2aw_d1] THEN
    ASM_SIMP_TAC[FRECHET_DERIVATIVE_LIFT_VECTOR_COMPONENT; LIFT_DROP];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!p. 1 <= p /\ p <= dimindex(:P)
        ==> x + e IN s /\ x - e IN s /\
            abs((Fm:real^M->real^P)(x + e)$p - Fm x$p) <= BB p * norm e /\
            abs(Fm(x + e)$p - Fm x$p - frechet_derivative Fm (at x) e$p) <= BB p * norm e pow 2 /\
            abs(Fm(x + e)$p + Fm(x - e)$p - &2 * Fm x$p) <= BB p * norm e pow 2`
  (LABEL_TAC "P") THENL
   [X_GEN_TAC `p:num` THEN DISCH_TAC THEN
    USE_THEN "C" (MP_TAC o SPEC `p:num`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPECL [`x:real^M`; `e:real^M`] o CONJUNCT2 o CONJUNCT2) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    USE_THEN "DC" (fun th -> REWRITE_TAC[MATCH_MP th
      (ASSUME `1 <= p /\ p <= dimindex(:P)`)]);
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!V:real^P c. (!p. 1 <= p /\ p <= dimindex(:P) ==> abs(V$p) <= BB p * c)
                 ==> norm V <= sum(1..dimindex(:P)) BB * c`
  (LABEL_TAC "N") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum(1..dimindex(:P)) (\p. abs((V:real^P)$p))` THEN
    REWRITE_TAC[NORM_LE_L1; GSYM SUM_RMUL] THEN MATCH_MP_TAC SUM_LE_NUMSEG THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  USE_THEN "P" (MP_TAC o SPEC `1`) THEN REWRITE_TAC[LE_REFL; DIMINDEX_GE_1] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN USE_THEN "N" MATCH_MP_TAC THEN X_GEN_TAC `p:num` THEN DISCH_TAC THEN
  USE_THEN "P" (MP_TAC o SPEC `p:num`) THEN (ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC]) THEN
  SIMP_TAC[VECTOR_ADD_COMPONENT; VECTOR_SUB_COMPONENT; VECTOR_MUL_COMPONENT]);;

(* ------------------------------------------------------------------------- *)
(* The s-form Lagrangian as one smooth function of                           *)
(* z = ((t, y), A) on (interval x U) x R^N:                                  *)
(*    p2aw_lagf Gt tt z = A.G(t,y)A / 2 + 2 (tt - t) R(t,y),                 *)
(* so that p2a_llag Gt tt s y A is its value at t = tt - s^2.               *)
(* ------------------------------------------------------------------------- *)

let p2aw_lagf = new_definition
 `p2aw_lagf (Gt:real->real^N->real^N^N) (tt:real) (z:real^((1,N)finite_sum,N)finite_sum) =
    inv(&2) * (sndcart z dot (Gt (drop(fstcart(fstcart z))) (sndcart(fstcart z)) ** sndcart z)) +
    &2 * (tt - drop(fstcart(fstcart z))) *
    lscalar (Gt (drop(fstcart(fstcart z)))) (sndcart(fstcart z))`;;

let P2AW_LLAG_LAGF = prove
 (`!(Gt:real->real^N->real^N^N) tt s y A.
     p2a_llag Gt tt s y A = p2aw_lagf Gt tt (pastecart (pastecart (lift(tt - s pow 2)) y) A)`,
  REWRITE_TAC[p2a_llag; p2aw_lagf; FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
  REWRITE_TAC[REAL_ARITH `tt - (tt - x:real) = x`]);;

let P2AW_SMOOTH_FST = prove
 (`!(S:real^M->bool) (f:real^M->real^K).
     open S /\ smooth_map_on S f
     ==> smooth_map_on (S PCROSS (:real^N)) (\z. f(fstcart z))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\z:real^(M,N)finite_sum. (f:real^M->real^K)(fstcart z)) = f o fstcart`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `S:real^M->bool` THEN
  ASM_SIMP_TAC[OPEN_PCROSS; OPEN_UNIV] THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_PCROSS; FSTCART_PASTECART] THEN SIMP_TAC[];
    MP_TAC(ISPECL [`(S:real^M->bool) PCROSS (:real^N)`; `\x:real^(M,N)finite_sum. x`]
                  SMOOTH_MAP_ON_FSTCART_OPEN) THEN
    ASM_SIMP_TAC[OPEN_PCROSS; OPEN_UNIV; SMOOTH_MAP_ON_ID] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM; o_THM]]);;

let P2AW_SMOOTH_FSTCART = prove
 (`!(s:real^(M,N)finite_sum->bool). open s ==> smooth_map_on s fstcart`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^(M,N)finite_sum->bool`; `\x:real^(M,N)finite_sum. x`]
                SMOOTH_MAP_ON_FSTCART_OPEN) THEN
  ASM_REWRITE_TAC[SMOOTH_MAP_ON_ID] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM; o_THM]);;

let P2AW_SMOOTH_SNDCART = prove
 (`!(s:real^(M,N)finite_sum->bool). open s ==> smooth_map_on s sndcart`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^(M,N)finite_sum->bool`; `\x:real^(M,N)finite_sum. x`]
                SMOOTH_MAP_ON_SNDCART_OPEN) THEN
  ASM_REWRITE_TAC[SMOOTH_MAP_ON_ID] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM; o_THM]);;

let P2AW_LAGF_SMOOTH = prove
 (`!U ta tb (Gt:real->real^N->real^N^N) tt.
     lrg_lsmooth U ta tb Gt
     ==> smooth_map_on ((interval(lift ta,lift tb) PCROSS U) PCROSS (:real^N))
                       (\z. lift(p2aw_lagf Gt tt z))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP LRG_LSMOOTH_LSCALAR) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [lrg_lsmooth]) THEN DISCH_TAC THEN
  SUBGOAL_THEN `open(interval(lift ta,lift tb) PCROSS (U:real^N->bool))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL]; ALL_TAC] THEN
  ABBREV_TAC `S = interval(lift ta,lift tb) PCROSS (U:real^N->bool)` THEN
  SUBGOAL_THEN `open((S:real^(1,N)finite_sum->bool) PCROSS (:real^N))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[OPEN_PCROSS; OPEN_UNIV]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
          ==> smooth_map_on (S:real^(1,N)finite_sum->bool)
                (\z. lift((Gt:real->real^N->real^N^N) (drop(fstcart z)) (sndcart z)$i$j))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`S:real^(1,N)finite_sum->bool`;
                   `\z:real^(1,N)finite_sum. (Gt:real->real^N->real^N^N)
                       (drop(fstcart z)) (sndcart z)`] LRG_SMOOTH_VECTORIZE) THEN
    ASM_REWRITE_TAC[o_DEF];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
          ==> smooth_map_on ((S:real^(1,N)finite_sum->bool) PCROSS (:real^N))
                (\z. lift((Gt:real->real^N->real^N^N) (drop(fstcart(fstcart z)))
                          (sndcart(fstcart z))$i$j))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`S:real^(1,N)finite_sum->bool`;
                   `\z:real^(1,N)finite_sum. lift((Gt:real->real^N->real^N^N)
                       (drop(fstcart z)) (sndcart z)$i$j)`] P2AW_SMOOTH_FST) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!k. 1 <= k /\ k <= dimindex(:N)
        ==> smooth_map_on ((S:real^(1,N)finite_sum->bool) PCROSS (:real^N))
              (\z. (Gt:real->real^N->real^N^N) (drop(fstcart(fstcart z)))
                   (sndcart(fstcart z))$k)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`(S:real^(1,N)finite_sum->bool) PCROSS (:real^N)`;
                   `\z:real^((1,N)finite_sum,N)finite_sum. (Gt:real->real^N->real^N^N)
                       (drop(fstcart(fstcart z))) (sndcart(fstcart z))$k`]
                  SMOOTH_MAP_ON_COMPONENTWISE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on ((S:real^(1,N)finite_sum->bool) PCROSS (:real^N))
      (\z. (Gt:real->real^N->real^N^N) (drop(fstcart(fstcart z))) (sndcart(fstcart z)) **
           sndcart z)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`(S:real^(1,N)finite_sum->bool) PCROSS (:real^N)`;
                   `\z:real^((1,N)finite_sum,N)finite_sum. (Gt:real->real^N->real^N^N)
                       (drop(fstcart(fstcart z))) (sndcart(fstcart z)) ** sndcart z`]
                  SMOOTH_MAP_ON_COMPONENTWISE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[MATRIX_VECTOR_MUL_COMPONENT] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DOT_OPEN THEN ASM_SIMP_TAC[ETA_AX; P2AW_SMOOTH_SNDCART];
    ALL_TAC] THEN
  REWRITE_TAC[p2aw_lagf; LIFT_ADD] THEN MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[LIFT_CMUL] THEN MATCH_MP_TAC SMOOTH_MAP_ON_CMUL_OPEN THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SMOOTH_MAP_ON_DOT_OPEN THEN
    ASM_SIMP_TAC[ETA_AX; P2AW_SMOOTH_SNDCART];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(S:real^(1,N)finite_sum->bool) PCROSS (:real^N)`;
                 `\z:real^((1,N)finite_sum,N)finite_sum. lift(&2 * (tt - drop(fstcart(fstcart z))))`;
                 `\z:real^((1,N)finite_sum,N)finite_sum.
                    lift(lscalar ((Gt:real->real^N->real^N^N) (drop(fstcart(fstcart z))))
                                 (sndcart(fstcart z)))`] SMOOTH_MAP_ON_LIFT_MUL) THEN
  ASM_REWRITE_TAC[LIFT_DROP; REAL_MUL_ASSOC] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`(S:real^(1,N)finite_sum->bool) PCROSS (:real^N)`;
                   `\z:real^((1,N)finite_sum,N)finite_sum. drop(fstcart(fstcart z))`;
                   `-- &2`; `&2 * tt`] P2AW_AFFINE_SMOOTH) THEN
    ASM_REWRITE_TAC[LIFT_DROP; REAL_ARITH `-- &2 * x + &2 * tt = &2 * (tt - x)`] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    MP_TAC(ISPECL [`(S:real^(1,N)finite_sum->bool) PCROSS (:real^N)`; `(:real^(1,N)finite_sum)`;
                   `fstcart:real^((1,N)finite_sum,N)finite_sum->real^(1,N)finite_sum`;
                   `fstcart:real^(1,N)finite_sum->real^1`] SMOOTH_MAP_ON_COMPOSE_OPEN) THEN
    ASM_SIMP_TAC[P2AW_SMOOTH_FSTCART; OPEN_UNIV; SUBSET_UNIV] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM; o_THM];
    MP_TAC(ISPECL [`S:real^(1,N)finite_sum->bool`;
                   `\z:real^(1,N)finite_sum. lift(lscalar ((Gt:real->real^N->real^N^N)
                       (drop(fstcart z))) (sndcart z))`] P2AW_SMOOTH_FST) THEN
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The spatial interpolation family y + mu w (mu = (s - s1)/D, D = sb - s1)  *)
(* of a chart curve on [s1,sb] and its s-form length: uniform first order    *)
(* and second difference bounds in w for curves with values in a fixed       *)
(* compact set and bounded velocity.                                         *)
(* ------------------------------------------------------------------------- *)

let P2AW_AFFINE_VDERIV = prove
 (`!(w:real^N) a b net. ((\v:real^1. (a * drop v + b) % w) has_vector_derivative (a % w)) net`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `(\v:real^1. (a * drop v + b) % (w:real^N)) = (\v. drop v % (a % w) + b % w)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`\v:real^1. drop v % (a % (w:real^N))`; `a % (w:real^N)`;
                 `\v:real^1. (b:real) % (w:real^N)`; `vec 0:real^N`; `net:(real^1)net`]
                HAS_VECTOR_DERIVATIVE_ADD) THEN
  REWRITE_TAC[HAS_VECTOR_DERIVATIVE_CONST; VECTOR_ADD_RID] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[has_vector_derivative] THEN MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN
  REWRITE_TAC[linear; DROP_ADD; DROP_CMUL] THEN VECTOR_ARITH_TAC);;

let p2aw_sfam = new_definition
 `p2aw_sfam (y:real^1->real^N) (s1:real) (sb:real) (w:real^N) =
    \v:real^1. y v + ((drop v - s1) / (sb - s1)) % w`;;

let P2AW_SFAM_DERIV = prove
 (`!(y:real^1->real^N) A s1 sb w v.
     (y has_vector_derivative A) (at v)
     ==> (p2aw_sfam y s1 sb w has_vector_derivative (A + inv(sb - s1) % w)) (at v)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p2aw_sfam] THEN
  MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_ADD THEN ASM_REWRITE_TAC[ETA_AX] THEN
  MP_TAC(ISPECL [`w:real^N`; `inv(sb - s1)`; `--(s1 / (sb - s1))`; `at(v:real^1)`]
                P2AW_AFFINE_VDERIV) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[real_div] THEN REAL_ARITH_TAC);;

(* Integrability of the Lagrangian along continuous curves in the domain.  *)

let P2AW_LAGF_CURVE_INTEGRABLE = prove
 (`!U ta tb (Gt:real->real^N->real^N^N) tt (Y:real^1->real^N) (A:real^1->real^N) a b.
     lrg_lsmooth U ta tb Gt /\
     Y continuous_on interval[lift a,lift b] /\ A continuous_on interval[lift a,lift b] /\
     (!s. a <= s /\ s <= b
          ==> pastecart (lift(tt - s pow 2)) (Y(lift s)) IN interval(lift ta,lift tb) PCROSS U)
     ==> (\s. p2aw_lagf Gt tt (pastecart (pastecart (lift(tt - s pow 2)) (Y(lift s))) (A(lift s))))
         real_integrable_on real_interval[a,b]`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN
  REWRITE_TAC[REAL_CONTINUOUS_ON; IMAGE_LIFT_REAL_INTERVAL] THEN
  SUBGOAL_THEN
   `(lift o (\s. p2aw_lagf (Gt:real->real^N->real^N^N) tt
                   (pastecart (pastecart (lift(tt - s pow 2)) ((Y:real^1->real^N)(lift s)))
                              ((A:real^1->real^N)(lift s)))) o drop) =
    (\z. lift(p2aw_lagf Gt tt z)) o
    (\v. pastecart (pastecart (lift(tt - drop v pow 2)) (Y v)) (A v))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_DROP]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[LIFT_SUB] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUB THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
    MATCH_MP_TAC CONTINUOUS_ON_LIFT_POW THEN REWRITE_TAC[LIFT_DROP; CONTINUOUS_ON_ID];
    ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
  EXISTS_TAC `(interval(lift ta,lift tb) PCROSS (U:real^N->bool)) PCROSS (:real^N)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS THEN MATCH_MP_TAC P2AW_LAGF_SMOOTH THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTERVAL_1; PASTECART_IN_PCROSS; IN_UNIV;
                LIFT_DROP] THEN
    X_GEN_TAC `v:real^1` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `drop v`) THEN
    ASM_REWRITE_TAC[LIFT_DROP; PASTECART_IN_PCROSS; IN_INTERVAL_1; DROP_VEC]]);;

(* Bounds for differences of integrals from pointwise bounds.              *)

let P2AW_INTEGRAL_DIFF1 = prove
 (`!f g a b c.
     a <= b /\ &0 <= c /\
     f real_integrable_on real_interval[a,b] /\ g real_integrable_on real_interval[a,b] /\
     (!s. a <= s /\ s <= b ==> abs(f s - g s) <= c)
     ==> abs(real_integral (real_interval[a,b]) f - real_integral (real_interval[a,b]) g)
         <= c * (b - a)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[GSYM REAL_INTEGRAL_SUB] THEN
  MATCH_MP_TAC HAS_REAL_INTEGRAL_BOUND THEN EXISTS_TAC `\s:real. f s - g s:real` THEN
  ASM_SIMP_TAC[GSYM HAS_REAL_INTEGRAL_INTEGRAL; REAL_INTEGRABLE_SUB; IN_REAL_INTERVAL]);;

let P2AW_INTEGRAL_DIFF2 = prove
 (`!f g h a b c.
     a <= b /\ &0 <= c /\
     f real_integrable_on real_interval[a,b] /\ g real_integrable_on real_interval[a,b] /\
     h real_integrable_on real_interval[a,b] /\
     (!s. a <= s /\ s <= b ==> abs(f s + g s - &2 * h s) <= c)
     ==> abs(real_integral (real_interval[a,b]) f + real_integral (real_interval[a,b]) g -
             &2 * real_integral (real_interval[a,b]) h) <= c * (b - a)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `real_integral (real_interval[a,b]) f + real_integral (real_interval[a,b]) g -
    &2 * real_integral (real_interval[a,b]) h =
    real_integral (real_interval[a,b]) (\s. f s + g s - &2 * h s)`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[REAL_INTEGRAL_SUB; REAL_INTEGRAL_ADD; REAL_INTEGRAL_LMUL; REAL_INTEGRABLE_ADD;
                 REAL_INTEGRABLE_LMUL; REAL_INTEGRABLE_SUB; ETA_AX];
    ALL_TAC] THEN
  MATCH_MP_TAC HAS_REAL_INTEGRAL_BOUND THEN
  EXISTS_TAC `\s:real. f s + g s - &2 * h s:real` THEN
  ASM_SIMP_TAC[GSYM HAS_REAL_INTEGRAL_INTEGRAL; REAL_INTEGRABLE_SUB; REAL_INTEGRABLE_ADD;
               REAL_INTEGRABLE_LMUL; IN_REAL_INTERVAL; ETA_AX]);;

(* ------------------------------------------------------------------------- *)
(* Uniform bounds for the spatial interpolation family.                      *)
(* ------------------------------------------------------------------------- *)

let P2AW_SFAM_CL = prove
 (`!(Gt:real->real^N->real^N^N) tt (y:real^1->real^N) A s1 sb w.
     (!s. s1 <= s /\ s <= sb ==> (y has_vector_derivative A(lift s)) (at (lift s)))
     ==> p2a_cL Gt tt (p2aw_sfam y s1 sb w) s1 sb =
         real_integral (real_interval[s1,sb])
           (\s. p2aw_lagf Gt tt
                  (pastecart (pastecart (lift(tt - s pow 2))
                                        (y(lift s) + ((s - s1) / (sb - s1)) % w))
                             (A(lift s) + inv(sb - s1) % w)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p2a_cL; P2AW_LLAG_LAGF] THEN
  MATCH_MP_TAC REAL_INTEGRAL_EQ THEN
  X_GEN_TAC `s:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
  SUBGOAL_THEN `vector_derivative (p2aw_sfam (y:real^1->real^N) s1 sb w) (at (lift s)) =
                A(lift s) + inv(sb - s1) % w`
  SUBST1_TAC THENL
   [MATCH_MP_TAC VECTOR_DERIVATIVE_AT THEN MATCH_MP_TAC P2AW_SFAM_DERIV THEN ASM_SIMP_TAC[];
    REWRITE_TAC[p2aw_sfam; LIFT_DROP]]);;

let P2AW_SFAM_ZERO = prove
 (`!(y:real^1->real^N) s1 sb. p2aw_sfam y s1 sb (vec 0) = y`,
  REWRITE_TAC[p2aw_sfam; VECTOR_MUL_RZERO; VECTOR_ADD_RID; ETA_AX]);;

let P2AW_SFAM_BOUNDS = prove
 (`!U ta tb (Gt:real->real^N->real^N^N) tt K0 M.
     lrg_lsmooth U ta tb Gt /\ compact K0 /\
     K0 SUBSET interval(lift ta,lift tb) PCROSS U
     ==> ?d C. &0 < d /\ &0 <= C /\
           !(y:real^1->real^N) A s1 sb w.
             s1 < sb /\
             (!s. s1 <= s /\ s <= sb
                  ==> pastecart (lift(tt - s pow 2)) (y(lift s)) IN K0 /\
                      norm(A(lift s)) <= M /\
                      (y has_vector_derivative A(lift s)) (at (lift s))) /\
             A continuous_on interval[lift s1,lift sb] /\
             (&1 + inv(sb - s1)) * norm w <= d
             ==> (!s. s1 <= s /\ s <= sb
                      ==> pastecart (lift(tt - s pow 2)) (y(lift s) + ((s - s1) / (sb - s1)) % w)
                          IN interval(lift ta,lift tb) PCROSS U) /\
                 abs(p2a_cL Gt tt (p2aw_sfam y s1 sb w) s1 sb - p2a_cL Gt tt y s1 sb)
                 <= C * (sb - s1 + &1) * norm w /\
                 p2a_cL Gt tt (p2aw_sfam y s1 sb w) s1 sb +
                 p2a_cL Gt tt (p2aw_sfam y s1 sb (--w)) s1 sb - &2 * p2a_cL Gt tt y s1 sb
                 <= C * (sb - s1 + &1) pow 2 / (sb - s1) * norm w pow 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [lrg_lsmooth]) THEN
  MP_TAC(ISPECL [`(interval(lift ta,lift tb) PCROSS (U:real^N->bool)) PCROSS (:real^N)`;
                 `p2aw_lagf (Gt:real->real^N->real^N^N) tt`;
                 `(K0:real^(1,N)finite_sum->bool) PCROSS cball(vec 0:real^N,M)`]
                P2AW_SMOOTH_DIFF_BOUNDS) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[OPEN_PCROSS; OPEN_UNIV; OPEN_INTERVAL; COMPACT_PCROSS; COMPACT_CBALL;
                 P2AW_LAGF_SMOOTH; ETA_AX] THEN
    ASM_REWRITE_TAC[SUBSET_PCROSS; SUBSET_UNIV];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (X_CHOOSE_THEN `B:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "DB"))))) THEN
  MAP_EVERY EXISTS_TAC [`d:real`; `B:real`] THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`y:real^1->real^N`; `A:real^1->real^N`; `s1:real`; `sb:real`;
                       `w:real^N`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `&0 < sb - s1 /\ &0 < inv(sb - s1)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* pointwise facts *)
  SUBGOAL_THEN
   `!s. s1 <= s /\ s <= sb
        ==> pastecart (lift(tt - s pow 2)) (y(lift s) + ((s - s1) / (sb - s1)) % w)
              IN interval(lift ta,lift tb) PCROSS U /\
            pastecart (lift(tt - s pow 2)) (y(lift s) + ((s - s1) / (sb - s1)) % --w)
              IN interval(lift ta,lift tb) PCROSS U /\
            abs(p2aw_lagf (Gt:real->real^N->real^N^N) tt
                  (pastecart (pastecart (lift(tt - s pow 2))
                                        ((y:real^1->real^N)(lift s) + ((s - s1) / (sb - s1)) % w))
                             ((A:real^1->real^N)(lift s) + inv(sb - s1) % w)) -
                p2aw_lagf Gt tt (pastecart (pastecart (lift(tt - s pow 2)) (y(lift s)))
                                           (A(lift s))))
            <= B * (&1 + inv(sb - s1)) * norm w /\
            abs(p2aw_lagf Gt tt
                  (pastecart (pastecart (lift(tt - s pow 2))
                                        (y(lift s) + ((s - s1) / (sb - s1)) % w))
                             (A(lift s) + inv(sb - s1) % w)) +
                p2aw_lagf Gt tt
                  (pastecart (pastecart (lift(tt - s pow 2))
                                        (y(lift s) + ((s - s1) / (sb - s1)) % --w))
                             (A(lift s) + inv(sb - s1) % --w)) -
                &2 * p2aw_lagf Gt tt (pastecart (pastecart (lift(tt - s pow 2)) (y(lift s)))
                                                (A(lift s))))
            <= B * ((&1 + inv(sb - s1)) * norm w) pow 2`
  (LABEL_TAC "PT") THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `K0:real^(1,N)finite_sum->bool`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `&0 <= (s - s1) / (sb - s1) /\ (s - s1) / (sb - s1) <= &1`
    STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_DIV; REAL_LE_LDIV_EQ; REAL_LT_IMP_LE; REAL_SUB_LE] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `norm(pastecart (pastecart (vec 0:real^1) (((s - s1) / (sb - s1)) % (w:real^N)))
                     (inv(sb - s1) % w)) <= (&1 + inv(sb - s1)) * norm w`
    ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `norm(pastecart (vec 0:real^1) (((s - s1) / (sb - s1)) % (w:real^N))) +
                  norm(inv(sb - s1) % (w:real^N))` THEN
      REWRITE_TAC[NORM_PASTECART_LE; NORM_PASTECART_0; NORM_MUL] THEN
      ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`; REAL_LT_IMP_LE] THEN
      REWRITE_TAC[REAL_ADD_RDISTRIB] THEN MATCH_MP_TAC REAL_LE_ADD2 THEN
      REWRITE_TAC[REAL_LE_REFL] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[NORM_POS_LE];
      ALL_TAC] THEN
    USE_THEN "DB" (MP_TAC o SPECL
     [`pastecart (pastecart (lift(tt - s pow 2)) ((y:real^1->real^N)(lift s)))
                 ((A:real^1->real^N)(lift s))`;
      `pastecart (pastecart (vec 0:real^1) (((s - s1) / (sb - s1)) % (w:real^N)))
                 (inv(sb - s1) % w)`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[PASTECART_IN_PCROSS; IN_CBALL_0] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[PASTECART_ADD; PASTECART_SUB; VECTOR_ADD_RID; VECTOR_SUB_RZERO;
                PASTECART_IN_PCROSS; IN_UNIV] THEN
    REWRITE_TAC[VECTOR_MUL_RNEG; GSYM VECTOR_SUB] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `B * norm(pastecart (pastecart (vec 0:real^1)
                    (((s - s1) / (sb - s1)) % (w:real^N))) (inv(sb - s1) % w))` THEN
      ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[REAL_LE_LMUL];
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `B * norm(pastecart (pastecart (vec 0:real^1)
                    (((s - s1) / (sb - s1)) % (w:real^N))) (inv(sb - s1) % w)) pow 2` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[NORM_POS_LE]];
    ALL_TAC] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  (* the lengths as integrals *)
  SUBGOAL_THEN `p2a_cL (Gt:real->real^N->real^N^N) tt y s1 sb =
                p2a_cL Gt tt (p2aw_sfam y s1 sb (vec 0)) s1 sb`
  SUBST1_TAC THENL [REWRITE_TAC[P2AW_SFAM_ZERO]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!w':real^N. p2a_cL (Gt:real->real^N->real^N^N) tt (p2aw_sfam y s1 sb w') s1 sb =
                real_integral (real_interval[s1,sb])
                  (\s. p2aw_lagf Gt tt
                         (pastecart (pastecart (lift(tt - s pow 2))
                                               (y(lift s) + ((s - s1) / (sb - s1)) % w'))
                                    ((A:real^1->real^N)(lift s) + inv(sb - s1) % w')))`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN MATCH_MP_TAC P2AW_SFAM_CL THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[VECTOR_MUL_RZERO; VECTOR_ADD_RID] THEN
  (* integrability *)
  SUBGOAL_THEN
   `!w':real^N.
      (!s. s1 <= s /\ s <= sb
           ==> pastecart (lift(tt - s pow 2)) (y(lift s) + ((s - s1) / (sb - s1)) % w')
               IN interval(lift ta,lift tb) PCROSS U)
      ==> (\s. p2aw_lagf (Gt:real->real^N->real^N^N) tt
                 (pastecart (pastecart (lift(tt - s pow 2))
                                       ((y:real^1->real^N)(lift s) + ((s - s1) / (sb - s1)) % w'))
                            ((A:real^1->real^N)(lift s) + inv(sb - s1) % w')))
          real_integrable_on real_interval[s1,sb]`
  (LABEL_TAC "INT") THENL
   [X_GEN_TAC `w':real^N` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `ta:real`; `tb:real`; `Gt:real->real^N->real^N^N`;
                   `tt:real`; `p2aw_sfam (y:real^1->real^N) s1 sb w'`;
                   `\v:real^1. (A:real^1->real^N) v + inv(sb - s1) % w'`; `s1:real`; `sb:real`]
                  P2AW_LAGF_CURVE_INTEGRABLE) THEN
    REWRITE_TAC[p2aw_sfam; LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN
      REWRITE_TAC[FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP] THEN
      X_GEN_TAC `s:real` THEN STRIP_TAC THEN
      MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN
      MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_IMP_DIFFERENTIABLE THEN
      EXISTS_TAC `(A:real^1->real^N)(lift s) + inv(sb - s1) % w'` THEN
      MP_TAC(ISPECL [`y:real^1->real^N`; `(A:real^1->real^N)(lift s)`; `s1:real`; `sb:real`;
                     `w':real^N`; `lift s`] P2AW_SFAM_DERIV) THEN
      ASM_SIMP_TAC[p2aw_sfam];
      MATCH_MP_TAC CONTINUOUS_ON_ADD THEN ASM_REWRITE_TAC[CONTINUOUS_ON_CONST]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\s. p2aw_lagf (Gt:real->real^N->real^N^N) tt
           (pastecart (pastecart (lift(tt - s pow 2)) ((y:real^1->real^N)(lift s)))
                      ((A:real^1->real^N)(lift s))))
    real_integrable_on real_interval[s1,sb]`
  ASSUME_TAC THENL
   [USE_THEN "INT" (MP_TAC o SPEC `vec 0:real^N`) THEN
    REWRITE_TAC[VECTOR_MUL_RZERO; VECTOR_ADD_RID] THEN DISCH_THEN MATCH_MP_TAC THEN
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `K0:real^(1,N)finite_sum->bool`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(B * (&1 + inv(sb - s1)) * norm(w:real^N)) * (sb - s1)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC P2AW_INTEGRAL_DIFF1 THEN REPEAT CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_MUL THEN
        REWRITE_TAC[NORM_POS_LE] THEN ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_ARITH
          `&0 < x ==> &0 <= &1 + x`];
        USE_THEN "INT" MATCH_MP_TAC THEN ASM_MESON_TAC[];
        ASM_REWRITE_TAC[];
        X_GEN_TAC `s:real` THEN STRIP_TAC THEN ASM_SIMP_TAC[]];
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN
      UNDISCH_TAC `&0 < sb - s1` THEN CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `abs x <= c ==> x <= c`) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(B * ((&1 + inv(sb - s1)) * norm(w:real^N)) pow 2) * (sb - s1)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC P2AW_INTEGRAL_DIFF2 THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2];
      USE_THEN "INT" MATCH_MP_TAC THEN ASM_MESON_TAC[];
      USE_THEN "INT" MATCH_MP_TAC THEN ASM_MESON_TAC[];
      ASM_REWRITE_TAC[];
      X_GEN_TAC `s:real` THEN STRIP_TAC THEN ASM_SIMP_TAC[]];
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN
    UNDISCH_TAC `&0 < sb - s1` THEN CONV_TAC REAL_FIELD]);;

(* ------------------------------------------------------------------------- *)
(* Reparametrization in time.  A curve Y on [s1,sb] run on                   *)
(* [s1, s1 + k (sb - s1)] at speed 1/k has s-form length                     *)
(*    k * int_{s1}^{sb} lagf(tt - (s1 + k (s - s1))^2, Y(s), Y'(s)/k) ds.     *)
(* ------------------------------------------------------------------------- *)

let P2AW_LAGF_PATH_INTEGRABLE = prove
 (`!U ta tb (Gt:real->real^N->real^N^N) tt (Z:real^1->real^((1,N)finite_sum,N)finite_sum) a b.
     lrg_lsmooth U ta tb Gt /\ Z continuous_on interval[lift a,lift b] /\
     (!s. a <= s /\ s <= b
          ==> Z(lift s) IN (interval(lift ta,lift tb) PCROSS U) PCROSS (:real^N))
     ==> (\s. p2aw_lagf Gt tt (Z(lift s))) real_integrable_on real_interval[a,b]`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN
  REWRITE_TAC[REAL_CONTINUOUS_ON; IMAGE_LIFT_REAL_INTERVAL] THEN
  SUBGOAL_THEN
   `(lift o (\s. p2aw_lagf (Gt:real->real^N->real^N^N) tt
                   ((Z:real^1->real^((1,N)finite_sum,N)finite_sum)(lift s))) o drop) =
    (\z. lift(p2aw_lagf Gt tt z)) o Z`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_DROP]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
  EXISTS_TAC `(interval(lift ta,lift tb) PCROSS (U:real^N->bool)) PCROSS (:real^N)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS THEN MATCH_MP_TAC P2AW_LAGF_SMOOTH THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP] THEN
    ASM_SIMP_TAC[]]);;

let P2AW_TIME_PATH_CONT = prove
 (`!tt s1 k a b.
     (\v:real^1. lift(tt - (s1 + k * (drop v - s1)) pow 2)) continuous_on
     interval[lift a,lift b]`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LIFT_SUB] THEN
  MATCH_MP_TAC CONTINUOUS_ON_SUB THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
  MATCH_MP_TAC CONTINUOUS_ON_LIFT_POW THEN REWRITE_TAC[LIFT_ADD; LIFT_CMUL; LIFT_SUB] THEN
  MATCH_MP_TAC CONTINUOUS_ON_ADD THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
  MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN MATCH_MP_TAC CONTINUOUS_ON_SUB THEN
  REWRITE_TAC[CONTINUOUS_ON_CONST; LIFT_DROP; CONTINUOUS_ON_ID]);;

let P2AW_CL_REPARAM = prove
 (`!U ta tb (Gt:real->real^N->real^N^N) tt (Y:real^1->real^N) B s1 sb k.
     lrg_lsmooth U ta tb Gt /\ s1 < sb /\ &0 < k /\
     (!s. s1 <= s /\ s <= sb ==> (Y has_vector_derivative B(lift s)) (at (lift s))) /\
     B continuous_on interval[lift s1,lift sb] /\
     (!s. s1 <= s /\ s <= sb
          ==> pastecart (lift(tt - (s1 + k * (s - s1)) pow 2)) (Y(lift s))
              IN interval(lift ta,lift tb) PCROSS U)
     ==> p2a_cL Gt tt (\v. Y(lift(s1 + (drop v - s1) / k))) s1 (s1 + k * (sb - s1)) =
         k * real_integral (real_interval[s1,sb])
               (\s. p2aw_lagf Gt tt
                      (pastecart (pastecart (lift(tt - (s1 + k * (s - s1)) pow 2)) (Y(lift s)))
                                 (inv k % B(lift s))))`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC
   `g = \s. p2aw_lagf (Gt:real->real^N->real^N^N) tt
              (pastecart (pastecart (lift(tt - (s1 + k * (s - s1)) pow 2))
                                    ((Y:real^1->real^N)(lift s)))
                         (inv k % (B:real^1->real^N)(lift s)))` THEN
  SUBGOAL_THEN `g real_integrable_on real_interval[s1,sb]` ASSUME_TAC THENL
   [EXPAND_TAC "g" THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `ta:real`; `tb:real`; `Gt:real->real^N->real^N^N`; `tt:real`;
                   `\v:real^1. pastecart (pastecart (lift(tt - (s1 + k * (drop v - s1)) pow 2))
                                                    ((Y:real^1->real^N) v))
                                         (inv k % (B:real^1->real^N) v)`;
                   `s1:real`; `sb:real`] P2AW_LAGF_PATH_INTEGRABLE) THEN
    REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_SIMP_TAC[PASTECART_IN_PCROSS; IN_UNIV] THEN
    MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN REWRITE_TAC[P2AW_TIME_PATH_CONT] THEN
      MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN
      REWRITE_TAC[FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN
      MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_IMP_DIFFERENTIABLE THEN ASM_MESON_TAC[];
      MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN ASM_REWRITE_TAC[ETA_AX]];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP REAL_INTEGRABLE_INTEGRAL) THEN
  DISCH_THEN(MP_TAC o SPECL [`inv k`; `s1 - s1 * inv k`] o
    MATCH_MP (REWRITE_RULE[IMP_CONJ] HAS_REAL_INTEGRAL_AFFINITY)) THEN
  ASM_SIMP_TAC[REAL_INV_EQ_0; REAL_LT_IMP_NZ; REAL_ABS_INV; REAL_INV_INV] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < k ==> abs k = k`] THEN
  SUBGOAL_THEN
   `IMAGE (\x. k * (x - (s1 - s1 * inv k))) (real_interval[s1,sb]) =
    real_interval[s1,s1 + k * (sb - s1)]`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_REAL_INTERVAL] THEN X_GEN_TAC `r:real` THEN
    EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `s:real` STRIP_ASSUME_TAC) THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `k * (s - (s1 - s1 * inv k)) = s1 + k * (s - s1)` SUBST1_TAC THENL
       [UNDISCH_TAC `&0 < k` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC(REAL_ARITH `&0 <= y ==> x <= x + y`) THEN MATCH_MP_TAC REAL_LE_MUL THEN
        ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC(REAL_ARITH `y <= z ==> x + y <= x + z`) THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC];
      STRIP_TAC THEN EXISTS_TAC `s1 + (r - s1) / k` THEN
      CONJ_TAC THENL [UNDISCH_TAC `&0 < k` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_ARITH `x <= x + y <=> &0 <= y`; REAL_LE_DIV; REAL_LT_IMP_LE;
                   REAL_SUB_LE] THEN
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `s1 + a <= sb <=> a <= sb - s1`] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_TAC THEN REWRITE_TAC[p2a_cL] THEN MATCH_MP_TAC REAL_INTEGRAL_UNIQUE THEN
  MATCH_MP_TAC HAS_REAL_INTEGRAL_EQ THEN
  EXISTS_TAC `\x. (g:real->real)(inv k * x + (s1 - s1 * inv k))` THEN
  ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `r:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
  SUBGOAL_THEN `inv k * r + (s1 - s1 * inv k) = s1 + (r - s1) / k` SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < k` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  SUBGOAL_THEN `s1 <= s1 + (r - s1) / k /\ s1 + (r - s1) / k <= sb` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_ARITH `x <= x + y <=> &0 <= y`; REAL_LE_DIV; REAL_LT_IMP_LE;
                 REAL_SUB_LE] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `s1 + a <= sb <=> a <= sb - s1`] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXPAND_TAC "g" THEN REWRITE_TAC[P2AW_LLAG_LAGF; LIFT_DROP] THEN
  SUBGOAL_THEN `s1 + k * ((s1 + (r - s1) / k) - s1) = r` SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < k` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC VECTOR_DERIVATIVE_AT THEN
  SUBGOAL_THEN `(\v:real^1. (Y:real^1->real^N)(lift(s1 + (drop v - s1) / k))) =
                Y o (\v. lift(s1 + (drop v - s1) / k))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `inv k % (B:real^1->real^N)(lift(s1 + (r - s1) / k)) =
                drop(lift(inv k)) % B(lift(s1 + (r - s1) / k))`
  SUBST1_TAC THENL [REWRITE_TAC[LIFT_DROP]; ALL_TAC] THEN
  MATCH_MP_TAC VECTOR_DIFF_CHAIN_AT THEN REWRITE_TAC[LIFT_DROP] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`vec 1:real^1`; `inv k`; `s1 - s1 / k`; `at(lift r)`]
                  P2AW_AFFINE_VDERIV) THEN
    REWRITE_TAC[GSYM LIFT_EQ_CMUL] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[real_div] THEN REAL_ARITH_TAC;
    ASM_SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The combined family: the spatial family y + mu w run on [s1, s1 + k (sb - *)
(* s1)] at speed 1/k, and its uniform first order bound in (k - 1, w).       *)
(* ------------------------------------------------------------------------- *)

let p2aw_cfam = new_definition
 `p2aw_cfam (y:real^1->real^N) (s1:real) (sb:real) (w:real^N) (k:real) =
    \v:real^1. p2aw_sfam y s1 sb w (lift(s1 + (drop v - s1) / k))`;;

let P2AW_CFAM_CL = prove
 (`!U ta tb (Gt:real->real^N->real^N^N) tt (y:real^1->real^N) A s1 sb w k.
     lrg_lsmooth U ta tb Gt /\ s1 < sb /\ &0 < k /\
     (!s. s1 <= s /\ s <= sb ==> (y has_vector_derivative A(lift s)) (at (lift s))) /\
     A continuous_on interval[lift s1,lift sb] /\
     (!s. s1 <= s /\ s <= sb
          ==> pastecart (lift(tt - (s1 + k * (s - s1)) pow 2))
                        (y(lift s) + ((s - s1) / (sb - s1)) % w)
              IN interval(lift ta,lift tb) PCROSS U)
     ==> p2a_cL Gt tt (p2aw_cfam y s1 sb w k) s1 (s1 + k * (sb - s1)) =
         k * real_integral (real_interval[s1,sb])
               (\s. p2aw_lagf Gt tt
                      (pastecart (pastecart (lift(tt - (s1 + k * (s - s1)) pow 2))
                                            (y(lift s) + ((s - s1) / (sb - s1)) % w))
                                 (inv k % (A(lift s) + inv(sb - s1) % w))))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p2aw_cfam] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `ta:real`; `tb:real`; `Gt:real->real^N->real^N^N`; `tt:real`;
                 `p2aw_sfam (y:real^1->real^N) s1 sb w`;
                 `\v:real^1. (A:real^1->real^N) v + inv(sb - s1) % w`;
                 `s1:real`; `sb:real`; `k:real`] P2AW_CL_REPARAM) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[P2AW_SFAM_DERIV] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_ADD THEN ASM_REWRITE_TAC[CONTINUOUS_ON_CONST];
      ASM_REWRITE_TAC[p2aw_sfam; LIFT_DROP]];
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[p2aw_sfam; LIFT_DROP]]);;

let P2AW_CFAM_BOUND = prove
 (`!U ta tb (Gt:real->real^N->real^N^N) tt K0 M D0 Sm.
     lrg_lsmooth U ta tb Gt /\ compact K0 /\
     K0 SUBSET interval(lift ta,lift tb) PCROSS U /\ &0 < D0 /\ &0 <= M /\ &0 <= Sm
     ==> ?d C. &0 < d /\ &0 <= C /\
           !(y:real^1->real^N) A s1 sb w k.
             &0 <= s1 /\ s1 + D0 <= sb /\ sb <= Sm /\
             (!s. s1 <= s /\ s <= sb
                  ==> pastecart (lift(tt - s pow 2)) (y(lift s)) IN K0 /\
                      norm(A(lift s)) <= M /\
                      (y has_vector_derivative A(lift s)) (at (lift s))) /\
             A continuous_on interval[lift s1,lift sb] /\
             abs(k - &1) <= d /\ norm w <= d
             ==> (!s. s1 <= s /\ s <= sb
                      ==> pastecart (lift(tt - (s1 + k * (s - s1)) pow 2))
                                    (y(lift s) + ((s - s1) / (sb - s1)) % w)
                          IN interval(lift ta,lift tb) PCROSS U) /\
                 abs(p2a_cL Gt tt (p2aw_cfam y s1 sb w k) s1 (s1 + k * (sb - s1)) -
                     p2a_cL Gt tt y s1 sb) <= C * (abs(k - &1) + norm w)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [lrg_lsmooth]) THEN
  ABBREV_TAC `K1 = (K0:real^(1,N)finite_sum->bool) PCROSS cball(vec 0:real^N,M)` THEN
  SUBGOAL_THEN `compact(K1:real^((1,N)finite_sum,N)finite_sum->bool) /\
                K1 SUBSET (interval(lift ta,lift tb) PCROSS (U:real^N->bool)) PCROSS (:real^N)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "K1" THEN
    SIMP_TAC[COMPACT_PCROSS; COMPACT_CBALL; ASSUME `compact(K0:real^(1,N)finite_sum->bool)`] THEN
    REWRITE_TAC[SUBSET_PCROSS; SUBSET_UNIV;
                ASSUME `K0 SUBSET interval(lift ta,lift tb) PCROSS (U:real^N->bool)`];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(interval(lift ta,lift tb) PCROSS (U:real^N->bool)) PCROSS (:real^N)`;
                 `p2aw_lagf (Gt:real->real^N->real^N^N) tt`;
                 `K1:real^((1,N)finite_sum,N)finite_sum->bool`] P2AW_SMOOTH_DIFF_BOUNDS) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[OPEN_PCROSS; OPEN_UNIV; OPEN_INTERVAL; P2AW_LAGF_SMOOTH; ETA_AX];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` (X_CHOOSE_THEN `B:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "DB"))))) THEN
  MP_TAC(ISPECL [`p2aw_lagf (Gt:real->real^N->real^N^N) tt`;
                 `K1:real^((1,N)finite_sum,N)finite_sum->bool`] P2AW_CONT_BOUND) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `(interval(lift ta,lift tb) PCROSS (U:real^N->bool)) PCROSS (:real^N)` THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS; P2AW_LAGF_SMOOTH; ETA_AX];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Lm:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "LM"))) THEN
  ABBREV_TAC `Ce = &3 * Sm pow 2 + &2 * M + &1 + &2 / D0` THEN
  SUBGOAL_THEN `&0 < Ce` ASSUME_TAC THENL
   [EXPAND_TAC "Ce" THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= a /\ &0 <= b /\ &0 <= c ==> &0 < a + b + &1 + c`) THEN
    ASM_SIMP_TAC[REAL_LE_MUL; REAL_POS; REAL_LE_POW_2; REAL_LE_DIV; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`min (inv(&2)) (d1 / (&2 * Ce))`;
                        `Sm * (Lm + B * d1 + B * Ce)`] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[REAL_LT_MIN] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= a /\ &0 <= b /\ &0 <= c ==> &0 <= a + b + c`) THEN
    ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`y:real^1->real^N`; `A:real^1->real^N`; `s1:real`; `sb:real`;
                       `w:real^N`; `k:real`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `abs(k - &1) <= inv(&2) /\ abs(k - &1) <= d1 / (&2 * Ce) /\
                norm(w:real^N) <= inv(&2) /\ norm w <= d1 / (&2 * Ce)`
  STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < k /\ inv k <= &2 /\ abs(inv k - &1) <= &2 * abs(k - &1)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&1 / &2 <= k` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(&1 / &2)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC; CONV_TAC REAL_RAT_REDUCE_CONV];
      SUBGOAL_THEN `inv k - &1 = (&1 - k) * inv k` SUBST1_TAC THENL
       [MATCH_MP_TAC(REAL_FIELD `~(k = &0) ==> inv k - &1 = (&1 - k) * inv k`) THEN
        ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      REWRITE_TAC[REAL_ABS_MUL; REAL_ARITH `abs(&1 - k) = abs(k - &1)`] THEN
      GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 < x /\ x <= &2 ==> abs x <= &2`) THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(&1 / &2)` THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC; CONV_TAC REAL_RAT_REDUCE_CONV]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `s1 < sb /\ D0 <= sb - s1 /\ &0 < sb - s1` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  (* the pointwise estimate *)
  SUBGOAL_THEN
   `!s. s1 <= s /\ s <= sb
        ==> pastecart (lift(tt - (s1 + k * (s - s1)) pow 2))
                      ((y:real^1->real^N)(lift s) + ((s - s1) / (sb - s1)) % w)
              IN interval(lift ta,lift tb) PCROSS U /\
            abs(k * p2aw_lagf (Gt:real->real^N->real^N^N) tt
                      (pastecart (pastecart (lift(tt - (s1 + k * (s - s1)) pow 2))
                                            (y(lift s) + ((s - s1) / (sb - s1)) % w))
                                 (inv k % ((A:real^1->real^N)(lift s) + inv(sb - s1) % w))) -
                p2aw_lagf Gt tt (pastecart (pastecart (lift(tt - s pow 2)) (y(lift s)))
                                           (A(lift s))))
            <= (Lm + B * d1 + B * Ce) * (abs(k - &1) + norm w)`
  (LABEL_TAC "PT") THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `K0:real^(1,N)finite_sum->bool`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ABBREV_TAC `r = s1 + k * (s - s1)` THEN
    SUBGOAL_THEN `&0 <= (s - s1) / (sb - s1) /\ (s - s1) / (sb - s1) <= &1`
    STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_DIV; REAL_LE_LDIV_EQ; REAL_LT_IMP_LE; REAL_SUB_LE] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `abs(s pow 2 - r pow 2) <= &3 * Sm pow 2 * abs(k - &1)` ASSUME_TAC THENL
     [SUBGOAL_THEN `s pow 2 - r pow 2 = (s - r) * (s + r) /\ s - r = --((k - &1) * (s - s1))`
      STRIP_ASSUME_TAC THENL
       [EXPAND_TAC "r" THEN CONJ_TAC THEN CONV_TAC REAL_RING; ALL_TAC] THEN
      ASM_REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_NEG] THEN
      SUBGOAL_THEN `abs(s - s1) <= Sm /\ abs(s + r) <= &3 * Sm` STRIP_ASSUME_TAC THENL
       [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        SUBGOAL_THEN `abs((k - &1) * (s - s1)) <= Sm` MP_TAC THENL
         [REWRITE_TAC[REAL_ABS_MUL] THEN GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
          MATCH_MP_TAC REAL_LE_MUL2 THEN
          REWRITE_TAC[REAL_ABS_POS] THEN ASM_REAL_ARITH_TAC;
          EXPAND_TAC "r" THEN ASM_REAL_ARITH_TAC];
        ALL_TAC] THEN
      SUBGOAL_THEN `&0 <= Sm` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `(abs(k - &1) * Sm) * (&3 * Sm)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL2 THEN
        ASM_SIMP_TAC[REAL_ABS_POS; REAL_LE_MUL; REAL_LE_LMUL] THEN
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_ABS_POS];
        REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `norm(inv k % ((A:real^1->real^N)(lift s) + inv(sb - s1) % w) - A(lift s))
      <= &2 * M * abs(k - &1) + &2 / D0 * norm(w:real^N)`
    ASSUME_TAC THENL
     [REWRITE_TAC[VECTOR_ARITH `c % (a + d % w) - a:real^N = (c - &1) % a + (c * d) % w`] THEN
      MATCH_MP_TAC(NORM_ARITH `norm(a:real^N) <= x /\ norm(b) <= y ==> norm(a + b) <= x + y`) THEN
      REWRITE_TAC[NORM_MUL] THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&2 * abs(k - &1)) * M` THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_ABS_POS; NORM_POS_LE];
          REAL_ARITH_TAC];
        MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE; REAL_ABS_MUL] THEN
        SUBGOAL_THEN `abs(inv k) = inv k /\ abs(inv(sb - s1)) = inv(sb - s1)` (fun th ->
          REWRITE_TAC[th]) THENL
         [CONJ_TAC THEN MATCH_MP_TAC(REAL_ARITH `&0 < x ==> abs x = x`) THEN
          MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC;
          ALL_TAC] THEN
        REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
        ASM_SIMP_TAC[REAL_LE_INV2; REAL_LT_IMP_LE; REAL_LE_INV_EQ]];
      ALL_TAC] THEN
    ABBREV_TAC `x = pastecart (pastecart (lift(tt - s pow 2)) ((y:real^1->real^N)(lift s)))
                              ((A:real^1->real^N)(lift s))` THEN
    ABBREV_TAC `e = pastecart (pastecart (lift(s pow 2 - r pow 2))
                                         (((s - s1) / (sb - s1)) % (w:real^N)))
                              (inv k % ((A:real^1->real^N)(lift s) + inv(sb - s1) % w) -
                               A(lift s))` THEN
    SUBGOAL_THEN
     `pastecart (pastecart (lift(tt - r pow 2))
                           ((y:real^1->real^N)(lift s) + ((s - s1) / (sb - s1)) % w))
                (inv k % ((A:real^1->real^N)(lift s) + inv(sb - s1) % w)) = x + e`
    SUBST1_TAC THENL
     [MAP_EVERY EXPAND_TAC ["x"; "e"] THEN REWRITE_TAC[PASTECART_ADD; GSYM LIFT_ADD] THEN
      REWRITE_TAC[REAL_ARITH `(tt - s) + (s - r):real = tt - r`] THEN
      REWRITE_TAC[PASTECART_INJ; VECTOR_ARITH `a + (b - a):real^N = b`];
      ALL_TAC] THEN
    SUBGOAL_THEN `norm(e:real^((1,N)finite_sum,N)finite_sum) <= Ce * (abs(k - &1) + norm(w:real^N))`
    ASSUME_TAC THENL
     [EXPAND_TAC "e" THEN MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `(abs(s pow 2 - r pow 2) + norm(((s - s1) / (sb - s1)) % (w:real^N))) +
                  norm(inv k % ((A:real^1->real^N)(lift s) + inv(sb - s1) % w) - A(lift s))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC(REAL_ARITH `!a b b' c:real. a <= b + c /\ b <= b' ==> a <= b' + c`) THEN
        EXISTS_TAC `norm(pastecart (lift(s pow 2 - r pow 2)) (((s - s1) / (sb - s1)) % (w:real^N)))` THEN
        REWRITE_TAC[NORM_PASTECART_LE] THEN
        MP_TAC(ISPECL [`lift(s pow 2 - r pow 2)`; `((s - s1) / (sb - s1)) % (w:real^N)`]
                      NORM_PASTECART_LE) THEN
        REWRITE_TAC[NORM_LIFT];
        ALL_TAC] THEN
      REWRITE_TAC[NORM_MUL] THEN
      SUBGOAL_THEN `abs((s - s1) / (sb - s1)) * norm(w:real^N) <= norm w` ASSUME_TAC THENL
       [GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
        REWRITE_TAC[NORM_POS_LE] THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      EXPAND_TAC "Ce" THEN
      SUBGOAL_THEN `&2 / D0 * norm(w:real^N) <= (&2 / D0) * norm w /\
                    &0 <= abs(k - &1) * (&2 / D0) /\ &0 <= norm w * (&3 * Sm pow 2 + &2 * M)`
      STRIP_ASSUME_TAC THENL
       [REWRITE_TAC[REAL_LE_REFL] THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
        REWRITE_TAC[REAL_ABS_POS; NORM_POS_LE] THEN
        ASM_SIMP_TAC[REAL_LE_DIV; REAL_POS; REAL_LT_IMP_LE; REAL_LE_ADD; REAL_LE_MUL;
                     REAL_LE_POW_2];
        ALL_TAC] THEN
      SUBGOAL_THEN `&0 <= abs(k - &1) * &1 /\ &0 <= norm(w:real^N) * &1` STRIP_ASSUME_TAC THENL
       [REWRITE_TAC[REAL_MUL_RID; REAL_ABS_POS; NORM_POS_LE]; ALL_TAC] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `x IN (K1:real^((1,N)finite_sum,N)finite_sum->bool) /\
                  norm(e:real^((1,N)finite_sum,N)finite_sum) <= d1`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MAP_EVERY EXPAND_TAC ["x"; "K1"] THEN
        REWRITE_TAC[PASTECART_IN_PCROSS; IN_CBALL_0] THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `Ce * (abs(k - &1) + norm(w:real^N))` THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `Ce * (&2 * d1 / (&2 * Ce))` THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
          ASM_REAL_ARITH_TAC;
          MATCH_MP_TAC REAL_EQ_IMP_LE THEN UNDISCH_TAC `&0 < Ce` THEN CONV_TAC REAL_FIELD]];
      ALL_TAC] THEN
    USE_THEN "DB" (MP_TAC o SPECL [`x:real^((1,N)finite_sum,N)finite_sum`;
                                   `e:real^((1,N)finite_sum,N)finite_sum`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    STRIP_TAC THEN CONJ_TAC THENL
     [UNDISCH_TAC `x + e IN (interval(lift ta,lift tb) PCROSS (U:real^N->bool)) PCROSS (:real^N)` THEN
      SUBGOAL_THEN
       `x + e = pastecart (pastecart (lift(tt - r pow 2))
                                     ((y:real^1->real^N)(lift s) + ((s - s1) / (sb - s1)) % w))
                          (inv k % ((A:real^1->real^N)(lift s) + inv(sb - s1) % w))`
      SUBST1_TAC THENL
       [MAP_EVERY EXPAND_TAC ["x"; "e"] THEN REWRITE_TAC[PASTECART_ADD; GSYM LIFT_ADD] THEN
        REWRITE_TAC[REAL_ARITH `(tt - s) + (s - r):real = tt - r`] THEN
      REWRITE_TAC[PASTECART_INJ; VECTOR_ARITH `a + (b - a):real^N = b`];
        SIMP_TAC[PASTECART_IN_PCROSS]];
      ALL_TAC] THEN
    USE_THEN "LM" (MP_TAC o SPEC `x:real^((1,N)finite_sum,N)finite_sum`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    SUBGOAL_THEN
     `abs(k * p2aw_lagf (Gt:real->real^N->real^N^N) tt (x + e) - p2aw_lagf Gt tt x) <=
      abs(k - &1) * abs(p2aw_lagf Gt tt (x + e)) + abs(p2aw_lagf Gt tt (x + e) - p2aw_lagf Gt tt x)`
    MP_TAC THENL
     [REWRITE_TAC[GSYM REAL_ABS_MUL] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN
     `abs(k - &1) * abs(p2aw_lagf (Gt:real->real^N->real^N^N) tt (x + e)) <=
      abs(k - &1) * (Lm + B * d1)`
    MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
      MATCH_MP_TAC(REAL_ARITH `!a b l c:real. abs a <= l /\ abs(b - a) <= c ==> abs b <= l + c`) THEN
      EXISTS_TAC `p2aw_lagf (Gt:real->real^N->real^N^N) tt x` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `B * norm(e:real^((1,N)finite_sum,N)finite_sum)` THEN
      ASM_SIMP_TAC[REAL_LE_LMUL];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `abs(p2aw_lagf (Gt:real->real^N->real^N^N) tt (x + e) - p2aw_lagf Gt tt x) <=
      B * Ce * (abs(k - &1) + norm(w:real^N))`
    MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `B * norm(e:real^((1,N)finite_sum,N)finite_sum)` THEN
      ASM_SIMP_TAC[REAL_LE_LMUL];
      ALL_TAC] THEN
    SUBGOAL_THEN `abs(k - &1) * (Lm + B * d1) <=
                  (Lm + B * d1) * (abs(k - &1) + norm(w:real^N))`
    MP_TAC THENL
     [GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_ADD THEN ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE];
        MP_TAC(ISPEC `w:real^N` NORM_POS_LE) THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  (* integration *)
  MP_TAC(ISPECL [`U:real^N->bool`; `ta:real`; `tb:real`; `Gt:real->real^N->real^N^N`; `tt:real`;
                 `y:real^1->real^N`; `A:real^1->real^N`; `s1:real`; `sb:real`; `w:real^N`;
                 `k:real`] P2AW_CFAM_CL) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN
   `p2a_cL (Gt:real->real^N->real^N^N) tt y s1 sb =
    real_integral (real_interval[s1,sb])
      (\s. p2aw_lagf Gt tt (pastecart (pastecart (lift(tt - s pow 2)) ((y:real^1->real^N)(lift s)))
                                      ((A:real^1->real^N)(lift s))))`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [GSYM P2AW_SFAM_ZERO] THEN
    MP_TAC(ISPECL [`Gt:real->real^N->real^N^N`; `tt:real`; `y:real^1->real^N`; `A:real^1->real^N`;
                   `s1:real`; `sb:real`; `vec 0:real^N`] P2AW_SFAM_CL) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[VECTOR_MUL_RZERO; VECTOR_ADD_RID];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!w':real^N k'.
      &0 < k' /\
      (!s. s1 <= s /\ s <= sb
           ==> pastecart (lift(tt - (s1 + k' * (s - s1)) pow 2))
                         ((y:real^1->real^N)(lift s) + ((s - s1) / (sb - s1)) % w')
               IN interval(lift ta,lift tb) PCROSS U)
      ==> (\s. p2aw_lagf (Gt:real->real^N->real^N^N) tt
                 (pastecart (pastecart (lift(tt - (s1 + k' * (s - s1)) pow 2))
                                       (y(lift s) + ((s - s1) / (sb - s1)) % w'))
                            (inv k' % ((A:real^1->real^N)(lift s) + inv(sb - s1) % w'))))
          real_integrable_on real_interval[s1,sb]`
  (LABEL_TAC "INT") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `ta:real`; `tb:real`; `Gt:real->real^N->real^N^N`; `tt:real`;
                   `\v:real^1. pastecart (pastecart (lift(tt - (s1 + k' * (drop v - s1)) pow 2))
                                 ((y:real^1->real^N) v + ((drop v - s1) / (sb - s1)) % w'))
                                 (inv k' % ((A:real^1->real^N) v + inv(sb - s1) % w'))`;
                   `s1:real`; `sb:real`] P2AW_LAGF_PATH_INTEGRABLE) THEN
    REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_SIMP_TAC[PASTECART_IN_PCROSS; IN_UNIV] THEN
    MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN REWRITE_TAC[P2AW_TIME_PATH_CONT] THEN
      MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN
      REWRITE_TAC[FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP] THEN X_GEN_TAC `s:real` THEN
      STRIP_TAC THEN MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN
      MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_IMP_DIFFERENTIABLE THEN
      EXISTS_TAC `(A:real^1->real^N)(lift s) + inv(sb - s1) % w'` THEN
      MP_TAC(ISPECL [`y:real^1->real^N`; `(A:real^1->real^N)(lift s)`; `s1:real`; `sb:real`;
                     `w':real^N`; `lift s`] P2AW_SFAM_DERIV) THEN
      ASM_SIMP_TAC[p2aw_sfam];
      MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN MATCH_MP_TAC CONTINUOUS_ON_ADD THEN
      ASM_REWRITE_TAC[CONTINUOUS_ON_CONST; ETA_AX]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `k * real_integral (real_interval[s1,sb])
          (\s. p2aw_lagf (Gt:real->real^N->real^N^N) tt
                 (pastecart (pastecart (lift(tt - (s1 + k * (s - s1)) pow 2))
                                       ((y:real^1->real^N)(lift s) + ((s - s1) / (sb - s1)) % w))
                            (inv k % ((A:real^1->real^N)(lift s) + inv(sb - s1) % w)))) =
    real_integral (real_interval[s1,sb])
          (\s. k * p2aw_lagf Gt tt
                 (pastecart (pastecart (lift(tt - (s1 + k * (s - s1)) pow 2))
                                       (y(lift s) + ((s - s1) / (sb - s1)) % w))
                            (inv k % (A(lift s) + inv(sb - s1) % w))))`
  SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_INTEGRAL_LMUL THEN
    USE_THEN "INT" MATCH_MP_TAC THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `((Lm + B * d1 + B * Ce) * (abs(k - &1) + norm(w:real^N))) * (sb - s1)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC P2AW_INTEGRAL_DIFF1 THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC(REAL_ARITH `&0 <= a /\ &0 <= b /\ &0 <= c ==> &0 <= a + b + c`) THEN
        ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE];
        MP_TAC(ISPEC `w:real^N` NORM_POS_LE) THEN REAL_ARITH_TAC];
      MATCH_MP_TAC REAL_INTEGRABLE_LMUL THEN USE_THEN "INT" MATCH_MP_TAC THEN
      ASM_MESON_TAC[];
      USE_THEN "INT" (MP_TAC o SPECL [`vec 0:real^N`; `&1`]) THEN
      REWRITE_TAC[VECTOR_MUL_RZERO; VECTOR_ADD_RID; REAL_MUL_LID; REAL_INV_1;
                  VECTOR_MUL_LID; REAL_LT_01; REAL_ARITH `s1 + (s - s1) = s`] THEN
      DISCH_THEN MATCH_MP_TAC THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `K0:real^(1,N)finite_sum->bool`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      X_GEN_TAC `s:real` THEN STRIP_TAC THEN REWRITE_TAC[] THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `((Lm + B * d1 + B * Ce) * (abs(k - &1) + norm(w:real^N))) * Sm` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC(REAL_ARITH `&0 <= a /\ &0 <= b /\ &0 <= c ==> &0 <= a + b + c`) THEN
        ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE];
        MP_TAC(ISPEC `w:real^N` NORM_POS_LE) THEN REAL_ARITH_TAC];
      ASM_REAL_ARITH_TAC];
    REWRITE_TAC[REAL_MUL_AC; REAL_LE_REFL]]);;

(* ------------------------------------------------------------------------- *)
(* C^1 extension of a chart curve beyond its right end sb by its tangent     *)
(* line (the chart curve of a minimizer is only one-sided C^1 at the end     *)
(* point; P2A_CHART_CURVE_SEG needs two-sided derivatives).                  *)
(* ------------------------------------------------------------------------- *)

let P2AW_HAS_DERIVATIVE_WITHIN_UNION = prove
 (`!(f:real^M->real^N) f' x s t.
     (f has_derivative f') (at x within s) /\ (f has_derivative f') (at x within t)
     ==> (f has_derivative f') (at x within (s UNION t))`,
  REWRITE_TAC[has_derivative_within; LIM_WITHIN_UNION] THEN MESON_TAC[]);;

let P2AW_INTERVAL_SPLIT = prove
 (`!a b c. a <= b /\ b <= c
           ==> interval[lift a,lift c] = interval[lift a,lift b] UNION interval[lift b,lift c]`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[EXTENSION; IN_UNION; IN_INTERVAL_1; LIFT_DROP] THEN
  ASM_REAL_ARITH_TAC);;

let p2aw_rext = new_definition
 `p2aw_rext (Y:real^1->real^N) (A:real^1->real^N) (sb:real) =
    \v. if drop v <= sb then Y v else Y(lift sb) + (drop v - sb) % A(lift sb)`;;

let p2aw_dext = new_definition
 `p2aw_dext (A:real^1->real^N) (sb:real) =
    \v. if drop v <= sb then A v else A(lift sb)`;;

let P2AW_LINE_VDERIV = prove
 (`!(c:real^N) (d:real^N) sb net.
     ((\v:real^1. c + (drop v - sb) % d) has_vector_derivative d) net`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`d:real^N`; `&1`; `--sb`; `net:(real^1)net`] P2AW_AFFINE_VDERIV) THEN
  DISCH_THEN(MP_TAC o MATCH_MP HAS_VECTOR_DERIVATIVE_ADD o CONJ
    (ISPECL [`c:real^N`; `net:(real^1)net`] HAS_VECTOR_DERIVATIVE_CONST)) THEN
  REWRITE_TAC[VECTOR_ADD_LID; VECTOR_MUL_LID] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REAL_ARITH_TAC);;

let P2AW_C1_EXTEND = prove
 (`!(Y:real^1->real^N) A s0 sb.
     s0 < sb /\
     (!s. s0 < s /\ s < sb ==> (Y has_vector_derivative A(lift s)) (at (lift s))) /\
     (Y has_vector_derivative A(lift sb)) (at (lift sb) within interval[lift s0,lift sb]) /\
     A continuous_on interval[lift s0,lift sb]
     ==> (!s. s0 < s
              ==> (p2aw_rext Y A sb has_vector_derivative p2aw_dext A sb (lift s))
                    (at (lift s))) /\
         (!s. s0 < s ==> p2aw_dext A sb continuous (at (lift s))) /\
         (!s. s <= sb ==> p2aw_rext Y A sb (lift s) = Y(lift s)) /\
         (!s. s <= sb ==> p2aw_dext A sb (lift s) = A(lift s))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!s. s <= sb ==> p2aw_rext (Y:real^1->real^N) A sb (lift s) = Y(lift s)`
  ASSUME_TAC THENL [SIMP_TAC[p2aw_rext; LIFT_DROP]; ALL_TAC] THEN
  SUBGOAL_THEN `!s. s <= sb ==> p2aw_dext (A:real^1->real^N) sb (lift s) = A(lift s)`
  ASSUME_TAC THENL [SIMP_TAC[p2aw_dext; LIFT_DROP]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!v:real^1. sb <= drop v
               ==> p2aw_rext (Y:real^1->real^N) A sb v = Y(lift sb) + (drop v - sb) % A(lift sb) /\
                   p2aw_dext A sb v = A(lift sb)`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[p2aw_rext; p2aw_dext] THEN
    ASM_CASES_TAC `drop(v:real^1) <= sb` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `v = lift sb` SUBST1_TAC THENL
     [REWRITE_TAC[GSYM DROP_EQ; LIFT_DROP] THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[LIFT_DROP; REAL_SUB_REFL; VECTOR_MUL_LZERO; VECTOR_ADD_RID]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    ASM_CASES_TAC `s < sb` THENL
     [MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_TRANSFORM_AT THEN
      MAP_EVERY EXISTS_TAC [`Y:real^1->real^N`; `sb - s`] THEN
      ASM_SIMP_TAC[REAL_SUB_LT; REAL_LT_IMP_LE] THEN
      X_GEN_TAC `v:real^1` THEN REWRITE_TAC[DIST_REAL; GSYM drop; LIFT_DROP] THEN
      DISCH_TAC THEN CONV_TAC SYM_CONV THEN REWRITE_TAC[p2aw_rext] THEN
      COND_CASES_TAC THEN REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_CASES_TAC `sb < s` THENL
     [MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_TRANSFORM_AT THEN
      MAP_EVERY EXISTS_TAC [`\v:real^1. (Y:real^1->real^N)(lift sb) + (drop v - sb) % A(lift sb)`;
                            `s - sb`] THEN
      ASM_SIMP_TAC[REAL_SUB_LT; LIFT_DROP; REAL_LT_IMP_LE; P2AW_LINE_VDERIV] THEN
      X_GEN_TAC `v:real^1` THEN REWRITE_TAC[DIST_REAL; GSYM drop; LIFT_DROP] THEN
      DISCH_TAC THEN CONV_TAC SYM_CONV THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `v:real^1` o check (fun th ->
        can (find_term ((=) `p2aw_rext (Y:real^1->real^N) A sb`)) (concl th) &&
        is_forall(concl th))) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `s:real = sb` SUBST_ALL_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_REFL] THEN REWRITE_TAC[has_vector_derivative] THEN
    MP_TAC(ISPECL [`p2aw_rext (Y:real^1->real^N) A sb`;
                   `\h:real^1. drop h % (A:real^1->real^N)(lift sb)`; `lift sb`;
                   `interval(lift s0,lift(sb + &1))`] HAS_DERIVATIVE_WITHIN_OPEN) THEN
    REWRITE_TAC[OPEN_INTERVAL; IN_INTERVAL_1; LIFT_DROP] THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN(SUBST1_TAC o SYM)] THEN
    MATCH_MP_TAC HAS_DERIVATIVE_WITHIN_SUBSET THEN
    EXISTS_TAC `interval[lift s0,lift sb] UNION interval[lift sb,lift(sb + &1)]` THEN
    CONJ_TAC THENL
     [ALL_TAC;
      REWRITE_TAC[SUBSET; IN_UNION; IN_INTERVAL_1; LIFT_DROP] THEN REAL_ARITH_TAC] THEN
    MATCH_MP_TAC P2AW_HAS_DERIVATIVE_WITHIN_UNION THEN CONJ_TAC THENL
     [MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_WITHIN THEN
      MAP_EVERY EXISTS_TAC [`Y:real^1->real^N`; `&1`] THEN
      ASM_REWRITE_TAC[GSYM has_vector_derivative; REAL_LT_01; IN_INTERVAL_1; LIFT_DROP] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      X_GEN_TAC `v:real^1` THEN STRIP_TAC THEN CONV_TAC SYM_CONV THEN
      REWRITE_TAC[p2aw_rext] THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_WITHIN THEN
      MAP_EVERY EXISTS_TAC [`\v:real^1. (Y:real^1->real^N)(lift sb) + (drop v - sb) % A(lift sb)`;
                            `&1`] THEN
      REWRITE_TAC[GSYM has_vector_derivative; REAL_LT_01; IN_INTERVAL_1; LIFT_DROP] THEN
      REWRITE_TAC[P2AW_LINE_VDERIV] THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      X_GEN_TAC `v:real^1` THEN STRIP_TAC THEN CONV_TAC SYM_CONV THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `v:real^1` o check (fun th ->
        can (find_term ((=) `p2aw_rext (Y:real^1->real^N) A sb`)) (concl th) &&
        is_forall(concl th))) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]]];
    ALL_TAC] THEN
  X_GEN_TAC `s:real` THEN DISCH_TAC THEN
  ASM_CASES_TAC `s < sb` THENL
   [MATCH_MP_TAC CONTINUOUS_TRANSFORM_AT THEN
    MAP_EVERY EXISTS_TAC [`A:real^1->real^N`; `min (s - s0) (sb - s)`] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      X_GEN_TAC `v:real^1` THEN REWRITE_TAC[DIST_REAL; GSYM drop; LIFT_DROP] THEN
      DISCH_TAC THEN REWRITE_TAC[p2aw_dext] THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC CONTINUOUS_ON_INTERIOR THEN
      EXISTS_TAC `interval[lift s0,lift sb]` THEN
      ASM_REWRITE_TAC[INTERIOR_INTERVAL; IN_INTERVAL_1; LIFT_DROP] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_CASES_TAC `sb < s` THENL
   [MATCH_MP_TAC CONTINUOUS_TRANSFORM_AT THEN
    MAP_EVERY EXISTS_TAC [`\v:real^1. (A:real^1->real^N)(lift sb)`; `s - sb`] THEN
    REWRITE_TAC[CONTINUOUS_CONST] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `v:real^1` THEN REWRITE_TAC[DIST_REAL; GSYM drop; LIFT_DROP] THEN
    DISCH_TAC THEN CONV_TAC SYM_CONV THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `v:real^1` o check (fun th ->
      can (find_term ((=) `p2aw_rext (Y:real^1->real^N) A sb`)) (concl th) &&
      is_forall(concl th))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `s:real = sb` SUBST_ALL_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[CONTINUOUS_AT] THEN
  MP_TAC(ISPECL [`p2aw_dext (A:real^1->real^N) sb`; `p2aw_dext (A:real^1->real^N) sb (lift sb)`;
                 `interval[lift s0,lift sb] UNION interval[lift sb,lift(sb + &1)]`;
                 `lift sb`] LIM_WITHIN_INTERIOR) THEN
  ANTS_TAC THENL
   [MP_TAC(ISPECL [`s0:real`; `sb:real`; `sb + &1`] P2AW_INTERVAL_SPLIT) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN(SUBST1_TAC o SYM)] THEN
    REWRITE_TAC[INTERIOR_INTERVAL; IN_INTERVAL_1; LIFT_DROP] THEN ASM_REAL_ARITH_TAC;
    DISCH_THEN(SUBST1_TAC o SYM)] THEN
  REWRITE_TAC[LIM_WITHIN_UNION; GSYM CONTINUOUS_WITHIN] THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_TRANSFORM_WITHIN THEN
    MAP_EVERY EXISTS_TAC [`A:real^1->real^N`; `&1`] THEN
    REWRITE_TAC[REAL_LT_01; IN_INTERVAL_1; LIFT_DROP] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN CONJ_TAC THENL
     [X_GEN_TAC `v:real^1` THEN STRIP_TAC THEN REWRITE_TAC[p2aw_dext] THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `(A:real^1->real^N) continuous_on interval[lift s0,lift sb]` THEN
      REWRITE_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN DISCH_THEN MATCH_MP_TAC THEN
      REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP] THEN ASM_REAL_ARITH_TAC];
    MATCH_MP_TAC CONTINUOUS_TRANSFORM_WITHIN THEN
    MAP_EVERY EXISTS_TAC [`\v:real^1. (A:real^1->real^N)(lift sb)`; `&1`] THEN
    REWRITE_TAC[REAL_LT_01; IN_INTERVAL_1; LIFT_DROP; CONTINUOUS_CONST] THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `v:real^1` THEN STRIP_TAC THEN CONV_TAC SYM_CONV THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `v:real^1` o check (fun th ->
      can (find_term ((=) `p2aw_rext (Y:real^1->real^N) A sb`)) (concl th) &&
      is_forall(concl th))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* Gluing.  An admissible curve cut at s1^2 and continued by the chart curve *)
(* of a C^1 curve sol on [s1,s2] in a region chart is admissible on [0,s2^2] *)
(* with length L(gamma|[0,s1^2]) + cL(sol) (the pattern of P2A_JCURVE,       *)
(* pc_p2a_usc, with a general sol).                                          *)
(* ------------------------------------------------------------------------- *)

let p2aw_glue = new_definition
 `p2aw_glue (gamma:real->A) (U:A->bool) (W:A->bool) (phi:A->real^N) (sol:real^1->real^N)
            (s1:real) =
    \tau. if tau <= s1 pow 2 then gamma tau
          else chart_inv (U INTER W,phi) (sol(lift(sqrt tau)))`;;

let P2AW_GLUE = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt x b (gamma:real->A) W a' b'' U (phi:A->real^N) (sol:real^1->real^N) s1 s2 sa sb'.
     p2a_svs V /\ p2a_adm V tt x b gamma /\
     p2a_region V W a' b'' /\ (U,phi) IN p2a_vatlas V b'' /\
     &0 < s1 /\ s1 pow 2 < b /\ s1 < s2 /\ sa < s1 /\ s2 < sb' /\
     (!s. sa < s /\ s < sb' ==> a' < tt - s pow 2 /\ tt - s pow 2 < b'') /\
     gamma(s1 pow 2) IN U INTER W /\ sol(lift s1) = phi(gamma(s1 pow 2)) /\
     (!s. s1 <= s /\ s <= s2
          ==> sol(lift s) IN IMAGE phi (U INTER W) /\
              sol differentiable (at (lift s)) /\
              (\v. vector_derivative sol (at v)) continuous (at (lift s)))
     ==> p2a_adm V tt x (s2 pow 2) (p2aw_glue gamma U W phi sol s1) /\
         p2aw_glue gamma U W phi sol s1 (s2 pow 2) = chart_inv (U INTER W,phi) (sol(lift s2)) /\
         p2a_L_length V tt (p2aw_glue gamma U W phi sol s1) (s2 pow 2) =
         p2a_L_length V tt gamma (s1 pow 2) +
         p2a_cL (p2a_rlocal V W b'' (U INTER W,phi)) tt sol s1 s2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < s2 /\ s1 pow 2 < s2 pow 2` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[ARITH_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `W:A->bool`; `a':real`; `b'':real`;
                 `U:A->bool`; `phi:A->real^N`; `sol:real^1->real^N`;
                 `s1:real`; `s2:real`; `sa:real`; `sb':real`] P2A_CHART_CURVE_SEG) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `a' < b''` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `s1:real` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `a':real`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `chart_inv (U INTER W,phi:A->real^N) (phi((gamma:real->A)(s1 pow 2))) =
                gamma(s1 pow 2)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P2A_REGION_CHART_INV THEN
    MAP_EVERY EXISTS_TAC [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                             (real->A->real^N^N)`; `a':real`; `b'':real`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `x:A`;
                 `\tau. chart_inv (U INTER W,phi:A->real^N) ((sol:real^1->real^N)(lift(sqrt tau)))`;
                 `gamma:real->A`; `p2aw_glue (gamma:real->A) U W (phi:A->real^N) sol s1`;
                 `s2 pow 2`; `s1 pow 2`] P2A_SEG_GLUE) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC P2A_ADM_RESTRICT THEN EXISTS_TAC `b:real` THEN
      ASM_SIMP_TAC[REAL_POW_LT; REAL_LT_IMP_LE];
      ASM_REWRITE_TAC[];
      REWRITE_TAC[] THEN ASM_SIMP_TAC[POW_2_SQRT; REAL_LT_IMP_LE];
      X_GEN_TAC `tau:real` THEN DISCH_TAC THEN ASM_REWRITE_TAC[p2aw_glue];
      X_GEN_TAC `tau:real` THEN DISCH_TAC THEN REWRITE_TAC[p2aw_glue] THEN
      COND_CASES_TAC THEN REWRITE_TAC[] THEN
      SUBGOAL_THEN `tau = s1 pow 2` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[POW_2_SQRT; REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[p2aw_glue] THEN
    SUBGOAL_THEN `~(s2 pow 2 <= s1 pow 2)` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[POW_2_SQRT; REAL_LT_IMP_LE];
    AP_TERM_TAC THEN MATCH_MP_TAC REAL_INTEGRAL_UNIQUE THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "has_real_integral"))
          (concl th))) THEN
    REWRITE_TAC[]]);;

(* The L-length over [0,b] only depends on the curve on [0,b].              *)

let P2AW_L_LENGTH_CONG = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt (gamma1:real->A) gamma2 b.
     &0 < b /\ (!s. s IN real_interval[&0,b] ==> gamma1 s = gamma2 s)
     ==> p2a_L_length V tt gamma1 b = p2a_L_length V tt gamma2 b`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p2a_L_length] THEN
  MP_TAC(ISPECL [`p2a_L_integrand (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                    (real->A->real^N^N)) tt gamma1 b`;
                 `p2a_L_integrand (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                    (real->A->real^N^N)) tt gamma2 b`;
                 `&0`; `b:real`] P2A_REAL_INTEGRAL_OPEN_EQ) THEN
  ANTS_TAC THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN MATCH_MP_TAC P2A_LINT_LOCAL THEN
    MAP_EVERY EXISTS_TAC [`&0`; `b:real`] THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN
    ASM_REAL_ARITH_TAC;
    SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The chart curve of a minimizer of a flow near its end point: C^1 with a   *)
(* continuous derivative on [s0, sqrt tau] (one-sided at the end) solving    *)
(* the L-geodesic system (P2A_MIN_LGEOD_GEN, P2A_PC1_TAU_C1,                 *)
(* P2A_SQ_CURVE_C1, P2A_MIN_ODE_OPEN, P2A_MIN_EXTEND).                       *)
(* ------------------------------------------------------------------------- *)

let P2AW_FLOW_FACTS = prove
 (`!top atlas a b (g:real->A->real^3^3).
     p2a_cbflow (top,atlas) a b g
     ==> p2a_svs (p2a_flow_view (top,atlas) (real_interval[a,b]) g) /\
         p2a_atlas_lc (p2a_flow_view (top,atlas) (real_interval[a,b]) g) /\
         (!y. y IN topspace top
              ==> p2a_bsmooth (p2a_flow_view (top,atlas) (real_interval[a,b]) g) y b) /\
         (!t. p2a_vatlas (p2a_flow_view (top,atlas) (real_interval[a,b]) g) t = atlas) /\
         (!t. a <= t /\ t <= b
              ==> p2a_vtop (p2a_flow_view (top,atlas) (real_interval[a,b]) g) t = top) /\
         smooth_manifold_atlas top atlas /\ a < b`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`UNIV:A->bool`; `UNIV:3->bool`] P2AW_FLOW_VIEW_3) THEN
  REWRITE_TAC[P2A_FLOW_VIEW_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                            `a:real`; `b:real`; `g:real->A->real^3^3`]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[P2A_ATLAS_LC_FLOW_VIEW] THEN
  REWRITE_TAC[p2a_flow_view; p2a_vatlas; p2a_vtop] THEN
  SIMP_TAC[IN_REAL_INTERVAL] THEN
  UNDISCH_TAC `p2a_cbflow (top,atlas) a b (g:real->A->real^3^3)` THEN
  REWRITE_TAC[P2AF_CBFLOW_3; ricci_flow_from; ricci_flow_on] THEN SIMP_TAC[]);;

let SPDR13_ADM_POS = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt x b gamma.
     p2a_adm V tt x b gamma ==> &0 < b`,
  SIMP_TAC[p2a_adm]);;

let SPDR13_MIN_POS = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt x b gamma.
     p2a_min V tt x b gamma ==> &0 < b`,
  SIMP_TAC[p2a_min; p2a_adm]);;

let P2AW_FLOW_MIN_CHART = prove
 (`!top atlas a b (g:real->A->real^3^3) p tau (gamma:real->A) U (phi:A->real^3) s0.
     p2a_cbflow (top,atlas) a b g /\ p IN topspace top /\ (U,phi) IN atlas /\
     p2a_min (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p tau gamma /\
     tau < b - a /\ &0 < s0 /\ s0 < sqrt tau /\
     (!s. s0 <= s /\ s <= sqrt tau ==> gamma(s pow 2) IN U)
     ==> ?A. A continuous_on interval[lift s0,lift(sqrt tau)] /\
             (!s. s0 < s /\ s < sqrt tau
                  ==> ((\v. phi(gamma(drop v pow 2))) has_vector_derivative A(lift s))
                        (at (lift s))) /\
             ((\v. phi(gamma(drop v pow 2))) has_vector_derivative A(lift(sqrt tau)))
               (at (lift(sqrt tau)) within interval[lift s0,lift(sqrt tau)]) /\
             (!s. s0 <= s /\ s <= sqrt tau
                  ==> (A has_vector_derivative
                         p2a_lacc (p2a_rlocal (p2a_flow_view (top,atlas) (real_interval[a,b]) g)
                                              U b (U INTER U,phi)) b s
                                  (phi(gamma(s pow 2))) (A(lift s)))
                        (at (lift s) within interval[lift s0,lift(sqrt tau)]))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2AW_FLOW_FACTS) THEN
  ABBREV_TAC `V = p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3)` THEN
  SUBGOAL_THEN `open_in top (U:A->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[SMOOTH_MANIFOLD_ATLAS_CHART]; ALL_TAC] THEN
  SUBGOAL_THEN `p2a_region (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) U a b`
  ASSUME_TAC THENL
   [EXPAND_TAC "V" THEN MATCH_MP_TAC P2AW_CBFLOW_REGION THEN ASM_REWRITE_TAC[REAL_LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `(U:A->bool,phi:A->real^3) IN p2a_vatlas V b` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < tau` ASSUME_TAC THENL
   [FIRST_ASSUM(ACCEPT_TAC o MATCH_MP SPDR13_MIN_POS); ALL_TAC] THEN
  SUBGOAL_THEN `sqrt tau pow 2 = tau /\ &0 < sqrt tau` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POW_2; SQRT_POS_LT; REAL_LT_IMP_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `p2a_adm (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                           (real->A->real^3^3)) b p tau gamma`
  ASSUME_TAC THENL [ASM_MESON_TAC[p2a_min]; ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
                 `b:real`; `p:A`; `tau:real`; `gamma:real->A`] P2A_MIN_LGEOD_GEN) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Z:real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!s O. &0 <= s /\ s pow 2 <= tau /\
          open_in (p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) (b - s pow 2)) O /\
          (gamma:real->A)(s pow 2) IN O
          ==> ?d. &0 < d /\
                  !tau'. &0 <= tau' /\ tau' <= tau /\ abs(tau' - s pow 2) < d ==> gamma tau' IN O`
  (LABEL_TAC "OC") THENL
   [REPEAT STRIP_TAC THEN
    UNDISCH_TAC `p2a_adm (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                            (real->A->real^3^3)) b p tau gamma` THEN
    REWRITE_TAC[p2a_adm] THEN
    DISCH_THEN(MP_TAC o SPECL [`s pow 2`; `O:A->bool`] o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o
      CONJUNCT2) THEN
    ASM_SIMP_TAC[REAL_POW_LE];
    ALL_TAC] THEN
  (* two-sided C^1 in the interior *)
  SUBGOAL_THEN
   `!s. s0 <= s /\ s < sqrt tau
        ==> (\v. (phi:A->real^3)((gamma:real->A)(drop v pow 2))) differentiable (at (lift s)) /\
            (\v. vector_derivative (\v. phi(gamma(drop v pow 2))) (at v)) continuous (at (lift s))`
  (LABEL_TAC "C1") THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `&0 < s /\ &0 < s pow 2 /\ s pow 2 < tau` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      CONJ_TAC THENL [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      FIRST_ASSUM((fun th -> GEN_REWRITE_TAC (RAND_CONV) [GSYM th]) o
        check (fun th -> concl th = `sqrt tau pow 2 = tau`)) THEN
      MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[ARITH_EQ] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(gamma:real->A)(s pow 2) IN U` ASSUME_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                      (real->A->real^3^3)`; `b:real`; `gamma:real->A`; `tau:real`; `{}:real->bool`;
                   `s pow 2`; `&1`; `U:A->bool`; `a:real`; `b:real`; `U:A->bool`; `phi:A->real^3`]
                  P2A_PC1_TAU_C1) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[NOT_IN_EMPTY; REAL_LT_01; INTER_IDEMPOT] THEN
      REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
      X_GEN_TAC `O:A->bool` THEN STRIP_TAC THEN USE_THEN "OC" MATCH_MP_TAC THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`\t:real^1. (phi:A->real^3)((gamma:real->A)(drop t))`; `s:real`; `e:real`]
                  P2A_SQ_CURVE_C1) THEN
    ASM_REWRITE_TAC[LIFT_DROP];
    ALL_TAC] THEN
  (* the system on the open interval *)
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `b:real`; `p:A`; `tau:real`; `gamma:real->A`;
                 `U:A->bool`; `a:real`; `b:real`; `U:A->bool`; `phi:A->real^3`;
                 `s0:real`; `sqrt tau`] P2A_MIN_ODE_OPEN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[INTER_IDEMPOT; REAL_LE_REFL] THEN
    REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `&0 < s pow 2 /\ s pow 2 < tau` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      FIRST_ASSUM((fun th -> GEN_REWRITE_TAC (RAND_CONV) [GSYM th]) o
        check (fun th -> concl th = `sqrt tau pow 2 = tau`)) THEN
      MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[ARITH_EQ] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      USE_THEN "C1" (MP_TAC o SPEC `s:real`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      USE_THEN "C1" (MP_TAC o SPEC `s:real`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]]];
    DISCH_THEN(LABEL_TAC "ODE")] THEN
  (* the closed interval *)
  SUBGOAL_THEN `sqrt tau < sqrt((tau + (b - a)) / &2) /\ (tau + (b - a)) / &2 < b - a /\
                sqrt((tau + (b - a)) / &2) pow 2 = (tau + (b - a)) / &2`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_MONO_LT THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC SQRT_POW_2 THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `b:real`; `p:A`; `tau:real`; `gamma:real->A`;
                 `U:A->bool`; `a:real`; `b:real`; `U:A->bool`; `phi:A->real^3`;
                 `s0:real`; `sqrt tau`; `s0 / &2`; `sqrt((tau + (b - a)) / &2)`]
                P2A_MIN_EXTEND) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[INTER_IDEMPOT; REAL_LE_REFL] THEN
    REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THENL
     [X_GEN_TAC `r:real` THEN STRIP_TAC THEN CONJ_TAC THENL
       [SUBGOAL_THEN `r pow 2 < sqrt((tau + (b - a)) / &2) pow 2` MP_TAC THENL
         [MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[ARITH_EQ] THEN ASM_REAL_ARITH_TAC;
          ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
        MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> b - x <= b`) THEN REWRITE_TAC[REAL_LE_POW_2]]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `A:real^1->real^3` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `A:real^1->real^3` THEN ASM_SIMP_TAC[REAL_LE_REFL; REAL_LT_IMP_LE] THEN
  X_GEN_TAC `s:real` THEN STRIP_TAC THEN
  USE_THEN "ODE" (MP_TAC o SPEC `s:real`) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN ASM_SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Lower bounds of L-lengths from a lower bound m of the scalar curvature    *)
(* along the curve, and the resulting upper bound for the L-length of a      *)
(* final piece of a curve.                                                   *)
(* ------------------------------------------------------------------------- *)

let P2AW_LINT_LOWER = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    m tt (gamma:real->A) b t.
     (!tau. &0 <= tau /\ tau <= b
            ==> m <= mfd_scalar (p2a_vatlas V (tt - tau)) (p2a_vmetric V (tt - tau))
                                (gamma tau)) /\
     &0 <= t /\ t <= b
     ==> --(abs m * sqrt b) <= p2a_L_integrand V tt gamma b t`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p2a_L_integrand] THEN
  SUBGOAL_THEN
   `--abs m <= mfd_scalar (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                         (real->A->real^N^N)) (tt - t))
                          (p2a_vmetric V (tt - t)) ((gamma:real->A) t) +
               mfd_speed (p2a_vatlas V (tt - t)) (p2a_vmetric V (tt - t)) gamma (&0) b t pow 2`
  ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `m <= x /\ &0 <= y ==> --abs m <= x + y`) THEN
    REWRITE_TAC[REAL_LE_POW_2] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= sqrt t /\ sqrt t <= sqrt b` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LE; SQRT_MONO_LE]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt t * --abs m` THEN CONJ_TAC THENL
   [SUBGOAL_THEN `&0 <= (sqrt b - sqrt t) * abs m` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_ABS_POS] THEN ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC];
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]]);;

let P2AW_ADM_LOWER = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    m tt x (gamma:real->A) b.
     (!tau. &0 <= tau /\ tau <= b
            ==> m <= mfd_scalar (p2a_vatlas V (tt - tau)) (p2a_vmetric V (tt - tau))
                                (gamma tau)) /\
     p2a_adm V tt x b gamma
     ==> --(abs m * sqrt b * b) <= p2a_L_length V tt gamma b`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "M") ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2a_adm]) THEN
  REWRITE_TAC[p2a_L_length] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `real_integral (real_interval[&0,b]) (\tau:real. --(abs m * sqrt b))` THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[REAL_INTEGRAL_CONST; REAL_LT_IMP_LE] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_INTEGRAL_LE THEN ASM_REWRITE_TAC[REAL_INTEGRABLE_CONST] THEN
  X_GEN_TAC `tau:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
  MATCH_MP_TAC P2AW_LINT_LOWER THEN ASM_REWRITE_TAC[]);;

let P2AW_PIECE_UPPER = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    m tt x (gamma:real->A) b r s.
     (!tau. &0 <= tau /\ tau <= b
            ==> m <= mfd_scalar (p2a_vatlas V (tt - tau)) (p2a_vmetric V (tt - tau))
                                (gamma tau)) /\
     p2a_adm V tt x b gamma /\ &0 < r /\ r <= s /\ s pow 2 <= b
     ==> real_integral (real_interval[r pow 2,s pow 2]) (p2a_L_integrand V tt gamma b)
         <= p2a_L_length V tt gamma b + &2 * abs m * sqrt b * b`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2a_adm]) THEN
  SUBGOAL_THEN `&0 < r pow 2 /\ r pow 2 <= s pow 2 /\ r pow 2 <= b` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_POW_LT] THEN
    SUBGOAL_THEN `r pow 2 <= s pow 2`
      (fun th -> REWRITE_TAC[th] THEN MP_TAC th THEN ASM_REAL_ARITH_TAC) THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `x:A`; `gamma:real->A`; `b:real`;
                 `r pow 2`] P2A_LENGTH_SPLIT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN
   `p2a_L_integrand (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                      (real->A->real^N^N)) tt gamma b
      real_integrable_on real_interval[r pow 2,b]`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRABLE_SUBINTERVAL THEN
    MAP_EVERY EXISTS_TAC [`&0`; `b:real`] THEN ASM_REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`p2a_L_integrand (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                    (real->A->real^N^N)) tt gamma b`;
                 `r pow 2`; `b:real`; `s pow 2`] REAL_INTEGRAL_COMBINE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `m:real`; `tt:real`; `x:A`; `gamma:real->A`;
                 `r pow 2`] P2AW_ADM_LOWER) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC P2A_ADM_RESTRICT THEN EXISTS_TAC `b:real` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `--(abs m * sqrt b * (b - s pow 2)) <=
    real_integral (real_interval[s pow 2,b])
      (p2a_L_integrand (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                         (real->A->real^N^N)) tt gamma b)`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `real_integral (real_interval[s pow 2,b]) (\t:real. --(abs m * sqrt b))` THEN
    CONJ_TAC THENL
     [ASM_SIMP_TAC[REAL_INTEGRAL_CONST] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_INTEGRAL_LE THEN REWRITE_TAC[REAL_INTEGRABLE_CONST] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_INTEGRABLE_SUBINTERVAL THEN
      MAP_EVERY EXISTS_TAC [`&0`; `b:real`] THEN ASM_REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN
      MP_TAC(SPEC `s:real` REAL_LE_POW_2) THEN ASM_REAL_ARITH_TAC;
      X_GEN_TAC `t:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
      MATCH_MP_TAC P2AW_LINT_LOWER THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(SPEC `s:real` REAL_LE_POW_2) THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `abs m * sqrt(r pow 2) * r pow 2 <= abs m * sqrt b * b /\
                abs m * sqrt b * (b - s pow 2) <= abs m * sqrt b * b`
  MP_TAC THENL
   [SUBGOAL_THEN `&0 <= sqrt b /\ sqrt(r pow 2) <= sqrt b` STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[SQRT_POS_LE; SQRT_MONO_LE; REAL_LT_IMP_LE]; ALL_TAC] THEN
    CONJ_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_ABS_POS] THENL
     [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_SIMP_TAC[SQRT_POS_LE; REAL_LT_IMP_LE];
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(SPEC `s:real` REAL_LE_POW_2) THEN ASM_REAL_ARITH_TAC];
    REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Chart curves of minimizers of a flow are C^1 at interior points in the    *)
(* chart, and stay in a fixed chart ball near the end point (the exit        *)
(* argument: the displacement bound P2A_END_DISP and a continuity            *)
(* induction).                                                               *)
(* ------------------------------------------------------------------------- *)

let P2AW_FLOW_MIN_C1 = prove
 (`!top atlas a b (g:real->A->real^3^3) p tau (gamma:real->A) U (phi:A->real^3) s.
     p2a_cbflow (top,atlas) a b g /\ p IN topspace top /\ (U,phi) IN atlas /\
     p2a_min (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p tau gamma /\
     tau < b - a /\ &0 < s /\ s pow 2 < tau /\ gamma(s pow 2) IN U
     ==> (\v. phi(gamma(drop v pow 2))) differentiable (at (lift s)) /\
         (\v. vector_derivative (\v. phi(gamma(drop v pow 2))) (at v)) continuous (at (lift s))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2AW_FLOW_FACTS) THEN
  ABBREV_TAC `V = p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3)` THEN
  SUBGOAL_THEN `open_in top (U:A->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[SMOOTH_MANIFOLD_ATLAS_CHART]; ALL_TAC] THEN
  SUBGOAL_THEN `p2a_region (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) U a b`
  ASSUME_TAC THENL
   [EXPAND_TAC "V" THEN MATCH_MP_TAC P2AW_CBFLOW_REGION THEN ASM_REWRITE_TAC[REAL_LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `p2a_adm (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                           (real->A->real^3^3)) b p tau gamma`
  ASSUME_TAC THENL [ASM_MESON_TAC[p2a_min]; ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
                 `b:real`; `p:A`; `tau:real`; `gamma:real->A`] P2A_MIN_LGEOD_GEN) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Z:real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `&0 < s pow 2` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `b:real`; `gamma:real->A`; `tau:real`; `{}:real->bool`;
                 `s pow 2`; `&1`; `U:A->bool`; `a:real`; `b:real`; `U:A->bool`; `phi:A->real^3`]
                P2A_PC1_TAU_C1) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[NOT_IN_EMPTY; REAL_LT_01; INTER_IDEMPOT] THEN
    REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
    X_GEN_TAC `O:A->bool` THEN STRIP_TAC THEN
    UNDISCH_TAC `p2a_adm (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                            (real->A->real^3^3)) b p tau gamma` THEN
    REWRITE_TAC[p2a_adm] THEN
    DISCH_THEN(MP_TAC o SPECL [`s pow 2`; `O:A->bool`] o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o
      CONJUNCT2) THEN
    ASM_SIMP_TAC[REAL_POW_LE; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`\t:real^1. (phi:A->real^3)((gamma:real->A)(drop t))`; `s:real`; `e:real`]
                P2A_SQ_CURVE_C1) THEN
  ASM_REWRITE_TAC[LIFT_DROP]);;

(* ------------------------------------------------------------------------- *)
(* The exit argument.  A minimizer to (q, tau) whose final pieces have       *)
(* L-length at most Lup stays, for s in [sqrt tau - D0, sqrt tau] and D0     *)
(* small (depending only on Lup and the chart bounds), in the chart ball of  *)
(* radius r0/2 about phi q.                                                  *)
(* ------------------------------------------------------------------------- *)

let P2AW_FLOW_EXIT = prove
 (`!top atlas a b (g:real->A->real^3^3) p tau (gamma:real->A) U (phi:A->real^3)
    x0 r0 sl c Kp Lup D0.
     p2a_cbflow (top,atlas) a b g /\ p IN topspace top /\ (U,phi) IN atlas /\
     p2a_min (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p tau gamma /\
     tau < b - a /\ gamma tau IN U /\ phi(gamma tau) = x0 /\
     &0 < r0 /\ cball(x0,r0) SUBSET IMAGE phi U /\
     &0 < sl /\ &0 < D0 /\ D0 <= &1 /\ sl + D0 <= sqrt tau /\ &0 < c /\ &0 <= Kp /\
     (!r y A. sl <= r /\ r <= sqrt tau /\ y IN cball(x0,r0)
              ==> c * norm A pow 2 <=
                  A dot (p2a_rlocal (p2a_flow_view (top,atlas) (real_interval[a,b]) g) U b
                           (U,phi) (b - r pow 2) y ** A)) /\
     (!r y. sl <= r /\ r <= sqrt tau /\ y IN cball(x0,r0)
            ==> abs(p2a_llag (p2a_rlocal (p2a_flow_view (top,atlas) (real_interval[a,b]) g) U b
                                (U,phi)) b r y (vec 0)) <= Kp) /\
     (!r s. sl <= r /\ r <= s /\ s <= sqrt tau
            ==> real_integral (real_interval[r pow 2,s pow 2])
                  (p2a_L_integrand (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b gamma tau)
                <= Lup) /\
     &16 * (&4 * (abs Lup + Kp) / c + &1) * D0 < r0 pow 2
     ==> !s. sqrt tau - D0 <= s /\ s <= sqrt tau
             ==> gamma(s pow 2) IN U /\ dist(phi(gamma(s pow 2)),x0) < r0 / &2`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "GLB")
    (CONJUNCTS_THEN2 (LABEL_TAC "KP") (CONJUNCTS_THEN2 (LABEL_TAC "LUP")
       ASSUME_TAC)))))))))))))))))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2AW_FLOW_FACTS) THEN
  ABBREV_TAC `V = p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3)` THEN
  SUBGOAL_THEN `open_in top (U:A->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[SMOOTH_MANIFOLD_ATLAS_CHART]; ALL_TAC] THEN
  SUBGOAL_THEN `p2a_region (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) U a b`
  ASSUME_TAC THENL
   [EXPAND_TAC "V" THEN MATCH_MP_TAC P2AW_CBFLOW_REGION THEN ASM_REWRITE_TAC[REAL_LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `p2a_adm (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                           (real->A->real^3^3)) b p tau gamma`
  ASSUME_TAC THENL [ASM_MESON_TAC[p2a_min]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < tau` ASSUME_TAC THENL
   [FIRST_ASSUM(ACCEPT_TAC o MATCH_MP SPDR13_ADM_POS); ALL_TAC] THEN
  SUBGOAL_THEN `sqrt tau pow 2 = tau /\ &0 < sqrt tau` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POW_2; SQRT_POS_LT; REAL_LT_IMP_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `hausdorff_space (top:A topology)` ASSUME_TAC THENL
   [ASM_MESON_TAC[P2AF_CBFLOW_3]; ALL_TAC] THEN
  ABBREV_TAC `eps = &4 * (abs Lup + Kp) / c + &1` THEN
  SUBGOAL_THEN `&0 < eps /\ Lup <= c * eps / &4 /\ Kp <= c * eps / &4`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "eps" THEN
    SUBGOAL_THEN `c * (&4 * (abs Lup + Kp) / c + &1) / &4 = (abs Lup + Kp) + c / &4`
    SUBST1_TAC THENL [UNDISCH_TAC `&0 < c` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= &4 * (abs Lup + Kp) / c` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN MATCH_MP_TAC REAL_LE_DIV THEN
      ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt tau < sqrt((tau + (b - a)) / &2) /\ (tau + (b - a)) / &2 < b - a /\
                sqrt((tau + (b - a)) / &2) pow 2 = (tau + (b - a)) / &2`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_MONO_LT THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC SQRT_POW_2 THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* the displacement step *)
  SUBGOAL_THEN
   `!s1. sqrt tau - D0 <= s1 /\ s1 < sqrt tau /\
         (!r. s1 <= r /\ r <= sqrt tau
              ==> (gamma:real->A)(r pow 2) IN U /\ dist((phi:A->real^3)(gamma(r pow 2)),x0) < r0)
         ==> dist(phi(gamma(s1 pow 2)),x0) < r0 / &2`
  (LABEL_TAC "DISP") THENL
   [X_GEN_TAC `s1:real` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                      (real->A->real^3^3)`; `b:real`; `p:A`; `tau:real`; `gamma:real->A`;
                   `U:A->bool`; `a:real`; `b:real`; `U:A->bool`; `phi:A->real^3`;
                   `sl / &2`; `sqrt((tau + (b - a)) / &2)`; `s1:real`; `c:real`; `Kp:real`;
                   `eps:real`] P2A_END_DISP) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[INTER_IDEMPOT] THEN REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THENL
       [X_GEN_TAC `r:real` THEN STRIP_TAC THEN CONJ_TAC THENL
         [SUBGOAL_THEN `r pow 2 < sqrt((tau + (b - a)) / &2) pow 2` MP_TAC THENL
           [MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[ARITH_EQ] THEN ASM_REAL_ARITH_TAC;
            ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
          MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> b - x <= b`) THEN REWRITE_TAC[REAL_LE_POW_2]];
        X_GEN_TAC `r:real` THEN STRIP_TAC THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `r:real` o check (fun th -> is_forall(concl th) &&
          can (find_term ((=) `r0:real`)) (concl th) &&
          can (find_term ((=) `s1:real`)) (concl th))) THEN
        ASM_REWRITE_TAC[] THEN SIMP_TAC[];
        X_GEN_TAC `r:real` THEN STRIP_TAC THEN
        MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`;
                       `b:real`; `g:real->A->real^3^3`; `p:A`; `tau:real`; `gamma:real->A`;
                       `U:A->bool`; `phi:A->real^3`; `r:real`] P2AW_FLOW_MIN_C1) THEN
        ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
        ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
         [ASM_REAL_ARITH_TAC;
          FIRST_ASSUM((fun th -> GEN_REWRITE_TAC RAND_CONV [GSYM th]) o
            check (fun th -> concl th = `sqrt tau pow 2 = tau`)) THEN
          MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[ARITH_EQ] THEN ASM_REAL_ARITH_TAC;
          FIRST_X_ASSUM(MP_TAC o SPEC `r:real` o check (fun th -> is_forall(concl th) &&
            can (find_term ((=) `r0:real`)) (concl th) &&
            can (find_term ((=) `s1:real`)) (concl th))) THEN
          ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]]];
        MAP_EVERY X_GEN_TAC [`r:real`; `A:real^3`] THEN STRIP_TAC THEN
        USE_THEN "GLB" MATCH_MP_TAC THEN
        CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        REWRITE_TAC[IN_CBALL] THEN ONCE_REWRITE_TAC[DIST_SYM] THEN
        MATCH_MP_TAC REAL_LT_IMP_LE THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `r:real` o check (fun th -> is_forall(concl th) &&
          can (find_term ((=) `r0:real`)) (concl th) &&
          can (find_term ((=) `s1:real`)) (concl th))) THEN
        ASM_REWRITE_TAC[] THEN SIMP_TAC[];
        X_GEN_TAC `r:real` THEN STRIP_TAC THEN
        USE_THEN "KP" MATCH_MP_TAC THEN
        CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        REWRITE_TAC[IN_CBALL] THEN ONCE_REWRITE_TAC[DIST_SYM] THEN
        MATCH_MP_TAC REAL_LT_IMP_LE THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `r:real` o check (fun th -> is_forall(concl th) &&
          can (find_term ((=) `r0:real`)) (concl th) &&
          can (find_term ((=) `s1:real`)) (concl th))) THEN
        ASM_REWRITE_TAC[] THEN SIMP_TAC[];
        X_GEN_TAC `s:real` THEN STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `Lup:real` THEN ASM_REWRITE_TAC[] THEN
        USE_THEN "LUP" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `Kp * &1` THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    REWRITE_TAC[dist] THEN ONCE_REWRITE_TAC[NORM_SUB] THEN
    MATCH_MP_TAC REAL_POW_LT2_REV THEN EXISTS_TAC `2` THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `&4 * eps * (sqrt tau - s1)` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `&4 * eps * D0` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_ARITH `(r / &2) pow 2 = r pow 2 / &4`] THEN
      UNDISCH_TAC `&16 * eps * D0 < r0 pow 2` THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `D0 <= sqrt tau` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!sg. &0 <= sg /\ sg <= D0
         ==> &0 <= (sqrt tau - sg) pow 2 /\ (sqrt tau - sg) pow 2 <= tau /\
             a <= b - (sqrt tau - sg) pow 2 /\ b - (sqrt tau - sg) pow 2 <= b`
  (LABEL_TAC "RANGE") THENL
   [X_GEN_TAC `sg:real` THEN STRIP_TAC THEN REWRITE_TAC[REAL_LE_POW_2] THEN
    SUBGOAL_THEN `(sqrt tau - sg) pow 2 <= sqrt tau pow 2` MP_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN MP_TAC(SPEC `sqrt tau - sg` REAL_LE_POW_2) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!sg sg'. &0 <= sg /\ sg <= D0 /\ &0 <= sg' /\ sg' <= D0
             ==> abs((sqrt tau - sg) pow 2 - (sqrt tau - sg') pow 2) <=
                 &2 * sqrt tau * abs(sg - sg')`
  (LABEL_TAC "LIPSQ") THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(sqrt tau - sg) pow 2 - (sqrt tau - sg') pow 2 =
                  (sg' - sg) * (&2 * sqrt tau - sg - sg')` SUBST1_TAC THENL
     [REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_ABS_MUL] THEN
    SUBGOAL_THEN `abs(sg' - sg) = abs(sg - sg')` SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN
    REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    REWRITE_TAC[REAL_ABS_POS] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* local behaviour near a point of the curve in the chart *)
  SUBGOAL_THEN
   `!sg0 r. &0 <= sg0 /\ sg0 <= D0 /\ (gamma:real->A)((sqrt tau - sg0) pow 2) IN U /\ &0 < r
            ==> ?e. &0 < e /\
                    !sg. &0 <= sg /\ sg <= D0 /\ abs(sg - sg0) < e
                         ==> gamma((sqrt tau - sg) pow 2) IN U /\
                             dist((phi:A->real^3)(gamma((sqrt tau - sg) pow 2)),
                                  phi(gamma((sqrt tau - sg0) pow 2))) < r`
  (LABEL_TAC "LOC") THENL
   [REPEAT STRIP_TAC THEN
    USE_THEN "RANGE" (MP_TAC o SPEC `sg0:real`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                      (real->A->real^3^3)`; `U:A->bool`; `a:real`; `b:real`; `U:A->bool`;
                   `phi:A->real^3`; `b - (sqrt tau - sg0) pow 2`;
                   `(gamma:real->A)((sqrt tau - sg0) pow 2)`; `r:real`] P2A_CHART_PREIMAGE_OPEN) THEN
    ASM_REWRITE_TAC[INTER_IDEMPOT] THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `O:A->bool` STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC `p2a_adm (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                            (real->A->real^3^3)) b p tau gamma` THEN
    REWRITE_TAC[p2a_adm] THEN
    DISCH_THEN(MP_TAC o SPECL [`(sqrt tau - sg0) pow 2`; `O:A->bool`] o
      CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `d / (&2 * sqrt tau + &1)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `sg:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(gamma:real->A)((sqrt tau - sg) pow 2) IN O` (fun th -> ASM_SIMP_TAC[th]) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    USE_THEN "RANGE" (MP_TAC o SPEC `sg:real`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `&2 * sqrt tau * abs(sg - sg0)` THEN
    CONJ_TAC THENL [USE_THEN "LIPSQ" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `(&2 * sqrt tau + &1) * abs(sg - sg0)` THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      REWRITE_TAC[REAL_ABS_POS] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < &2 * sqrt tau + &1` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `abs(sg - sg0) < d / (&2 * sqrt tau + &1)` THEN
    ASM_SIMP_TAC[REAL_LT_RDIV_EQ] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the continuity induction *)
  MP_TAC(ISPECL [`\sg. (gamma:real->A)((sqrt tau - sg) pow 2) IN U /\
                       dist((phi:A->real^3)(gamma((sqrt tau - sg) pow 2)),x0) < r0`;
                 `D0:real`] P2A_REAL_CONT_INDUCT) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      USE_THEN "LOC" (MP_TAC o SPECL [`&0`; `r0:real`]) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[REAL_SUB_RZERO; REAL_LE_REFL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[REAL_SUB_RZERO] THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `e:real` THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `sg:real` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `sg:real`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      X_GEN_TAC `Tm:real` THEN STRIP_TAC THEN
      SUBGOAL_THEN
       `!sg. &0 <= sg /\ sg < Tm
             ==> dist((phi:A->real^3)((gamma:real->A)((sqrt tau - sg) pow 2)),x0) < r0 / &2`
      (LABEL_TAC "HALF") THENL
       [X_GEN_TAC `sg:real` THEN STRIP_TAC THEN
        ASM_CASES_TAC `sg = &0` THENL
         [ASM_REWRITE_TAC[REAL_SUB_RZERO; DIST_REFL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        USE_THEN "DISP" MATCH_MP_TAC THEN
        CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        X_GEN_TAC `r:real` THEN STRIP_TAC THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `sqrt tau - r` o check (fun th -> is_forall(concl th) &&
          can (find_term ((=) `Tm:real`)) (concl th))) THEN
        REWRITE_TAC[REAL_ARITH `sqrt tau - (sqrt tau - r) = r`] THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
        ALL_TAC] THEN
      ABBREV_TAC `C = IMAGE (chart_inv (U,phi:A->real^3)) (cball(x0,r0 / &2))` THEN
      SUBGOAL_THEN `closed_in top (C:A->bool)` ASSUME_TAC THENL
       [EXPAND_TAC "C" THEN MATCH_MP_TAC GRGD_CHART_CBALL_CLOSED THEN
        EXISTS_TAC `atlas:((A->bool)#(A->real^3))->bool` THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `cball(x0:real^3,r0)` THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_CBALL THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN
       `!y. y IN cball(x0:real^3,r0 / &2)
            ==> chart_inv (U,phi:A->real^3) y IN U /\ phi(chart_inv (U,phi) y) = y`
      (LABEL_TAC "CI") THENL
       [X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
        MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                       `U:A->bool`; `phi:A->real^3`] CHART_INV) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `y:real^3` o CONJUNCT2) THEN
        ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
        SUBGOAL_THEN `cball(x0:real^3,r0 / &2) SUBSET cball(x0,r0)` MP_TAC THENL
         [MATCH_MP_TAC SUBSET_CBALL THEN ASM_REAL_ARITH_TAC; ASM SET_TAC[]];
        ALL_TAC] THEN
      SUBGOAL_THEN
       `!sg. &0 <= sg /\ sg < Tm ==> (gamma:real->A)((sqrt tau - sg) pow 2) IN C`
      (LABEL_TAC "INC") THENL
       [X_GEN_TAC `sg:real` THEN STRIP_TAC THEN EXPAND_TAC "C" THEN REWRITE_TAC[IN_IMAGE] THEN
        EXISTS_TAC `(phi:A->real^3)((gamma:real->A)((sqrt tau - sg) pow 2))` THEN
        CONJ_TAC THENL
         [CONV_TAC SYM_CONV THEN
          MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                         `U:A->bool`; `phi:A->real^3`] CHART_INV) THEN
          ASM_REWRITE_TAC[] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN
          FIRST_X_ASSUM(MP_TAC o SPEC `sg:real` o check (fun th -> is_forall(concl th) &&
            can (find_term ((=) `Tm:real`)) (concl th) &&
            not (can (find_term ((=) `r0 / &2`)) (concl th)))) THEN
          ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
          REWRITE_TAC[IN_CBALL] THEN ONCE_REWRITE_TAC[DIST_SYM] THEN
          MATCH_MP_TAC REAL_LT_IMP_LE THEN USE_THEN "HALF" MATCH_MP_TAC THEN
          ASM_REWRITE_TAC[]];
        ALL_TAC] THEN
      SUBGOAL_THEN `(gamma:real->A)((sqrt tau - Tm) pow 2) IN C` MP_TAC THENL
       [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
        USE_THEN "RANGE" (MP_TAC o SPEC `Tm:real`) THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
        SUBGOAL_THEN `p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                  (real->A->real^3^3)) (b - (sqrt tau - Tm) pow 2) = top`
        ASSUME_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
        UNDISCH_TAC `p2a_adm (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) b p tau gamma` THEN
        REWRITE_TAC[p2a_adm] THEN
        DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC)
          (CONJUNCTS_THEN2 (LABEL_TAC "TS") (CONJUNCTS_THEN2 (LABEL_TAC "CT") (K ALL_TAC))))) THEN
        USE_THEN "CT" (MP_TAC o SPECL [`(sqrt tau - Tm) pow 2`; `topspace top DIFF (C:A->bool)`]) THEN
        ANTS_TAC THENL
         [ASM_REWRITE_TAC[] THEN
          CONJ_TAC THENL [ASM_MESON_TAC[closed_in]; ALL_TAC] THEN
          ASM_REWRITE_TAC[IN_DIFF] THEN
          USE_THEN "TS" (MP_TAC o SPEC `(sqrt tau - Tm) pow 2`) THEN
          ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]];
          ALL_TAC] THEN
        DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
        SUBGOAL_THEN `&0 < d / (&4 * sqrt tau + &1)` ASSUME_TAC THENL
         [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        ABBREV_TAC `sg = Tm - min (Tm / &2) (d / (&4 * sqrt tau + &1))` THEN
        SUBGOAL_THEN `&0 <= sg /\ sg < Tm /\ abs(sg - Tm) <= d / (&4 * sqrt tau + &1)`
        STRIP_ASSUME_TAC THENL
         [EXPAND_TAC "sg" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        USE_THEN "INC" (MP_TAC o SPEC `sg:real`) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        MATCH_MP_TAC(SET_RULE `!x:A s t. x IN t DIFF s ==> x IN s ==> F`) THEN
        EXISTS_TAC `topspace top:A->bool` THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        USE_THEN "RANGE" (MP_TAC o SPEC `sg:real`) THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `&2 * sqrt tau * abs(sg - Tm)` THEN
        CONJ_TAC THENL [USE_THEN "LIPSQ" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        SUBGOAL_THEN `&0 < &4 * sqrt tau + &1` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        UNDISCH_TAC `abs(sg - Tm) <= d / (&4 * sqrt tau + &1)` THEN
        ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
        SUBGOAL_THEN `&0 < abs(sg - Tm)` MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        SUBGOAL_THEN `&0 <= sqrt tau * abs(sg - Tm)` MP_TAC THENL
         [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_ABS_POS] THEN ASM_REAL_ARITH_TAC;
          ALL_TAC] THEN
        REAL_ARITH_TAC;
        ALL_TAC] THEN
      EXPAND_TAC "C" THEN REWRITE_TAC[IN_IMAGE] THEN
      DISCH_THEN(X_CHOOSE_THEN `y:real^3` (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC)) THEN
      USE_THEN "CI" (MP_TAC o SPEC `y:real^3`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `y IN cball(x0:real^3,r0 / &2)` THEN REWRITE_TAC[IN_CBALL] THEN
      MP_TAC(ISPECL [`x0:real^3`; `y:real^3`] DIST_SYM) THEN ASM_REAL_ARITH_TAC;
      X_GEN_TAC `Tm:real` THEN STRIP_TAC THEN
      SUBGOAL_THEN
       `(gamma:real->A)((sqrt tau - Tm) pow 2) IN U /\
        dist((phi:A->real^3)(gamma((sqrt tau - Tm) pow 2)),x0) < r0`
      STRIP_ASSUME_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      USE_THEN "LOC" (MP_TAC o SPECL
        [`Tm:real`; `r0 - dist((phi:A->real^3)((gamma:real->A)((sqrt tau - Tm) pow 2)),x0)`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `e:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "E"))) THEN
      EXISTS_TAC `e:real` THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `sg:real` THEN STRIP_TAC THEN
      USE_THEN "E" (MP_TAC o SPEC `sg:real`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`(phi:A->real^3)((gamma:real->A)((sqrt tau - sg) pow 2))`;
                     `(phi:A->real^3)((gamma:real->A)((sqrt tau - Tm) pow 2))`;
                     `x0:real^3`] DIST_TRIANGLE) THEN
      ASM_REAL_ARITH_TAC];
    DISCH_THEN(LABEL_TAC "IND")] THEN
  X_GEN_TAC `s:real` THEN STRIP_TAC THEN
  USE_THEN "IND" (MP_TAC o SPEC `sqrt tau - s`) THEN
  REWRITE_TAC[REAL_ARITH `sqrt tau - (sqrt tau - s) = s`] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `s = sqrt tau` THENL
   [ASM_REWRITE_TAC[DIST_REFL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "DISP" MATCH_MP_TAC THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `r:real` THEN STRIP_TAC THEN
  USE_THEN "IND" (MP_TAC o SPEC `sqrt tau - r`) THEN
  REWRITE_TAC[REAL_ARITH `sqrt tau - (sqrt tau - r) = r`] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]]);;


(* ------------------------------------------------------------------------- *)
(* A velocity bound for solutions of the L-geodesic system with finite       *)
(* energy (the variation bound inside P2A_LODE_EXTEND of pc_p2a_lext, copied *)
(* with an explicit constant C).                                             *)
(* ------------------------------------------------------------------------- *)

let P2AW_VEL_VAR = prove
 (`!U sa sb (Gt:real->real^N->real^N^N) tt p q Kc (Y:real^1->real^N) A C.
     p2a_lsmooth U sa sb (\s. Gt(tt - s pow 2)) /\ sa < p /\ p < q /\ q < sb /\
     compact Kc /\ Kc SUBSET U /\
     Y continuous_on interval[lift p,lift q] /\
     (!s. p <= s /\ s <= q ==> Y(lift s) IN Kc) /\
     (!s. p < s /\ s < q
          ==> (Y has_vector_derivative A(lift s)) (at (lift s)) /\
              (A has_vector_derivative p2a_lacc Gt tt s (Y(lift s)) (A(lift s)))
                (at (lift s))) /\
     (\s. norm(A(lift s)) pow 2) real_integrable_on real_interval[p,q] /\
     &0 < C /\
     (!s y a. p <= s /\ s <= q /\ y IN Kc
              ==> norm(p2a_lacc Gt tt s y a) <= C * (&1 + norm a pow 2))
     ==> !s t. p < s /\ s <= t /\ t < q
               ==> norm((A:real^1->real^N)(lift t) - A(lift s)) <=
                   C * real_integral (real_interval[s,t]) (\u. &1 + norm(A(lift u)) pow 2)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "K")
     (CONJUNCTS_THEN2 (LABEL_TAC "D") (CONJUNCTS_THEN2 ASSUME_TAC
       (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC))))))))))) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP P2A_LFIELD_SMOOTH) THEN
  (* A is continuous on the open interval *)
  SUBGOAL_THEN `!s. p < s /\ s < q ==> (A:real^1->real^N) continuous (at (lift s))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN
    REWRITE_TAC[VECTOR_DIFFERENTIABLE] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\u. &1 + norm((A:real^1->real^N)(lift u)) pow 2) real_integrable_on real_interval[p,q]`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRABLE_ADD THEN ASM_REWRITE_TAC[REAL_INTEGRABLE_CONST]; ALL_TAC] THEN
  (* the variation bound *)
  SUBGOAL_THEN
   `!s t. p < s /\ s <= t /\ t < q
          ==> norm((A:real^1->real^N)(lift t) - A(lift s)) <=
              C * real_integral (real_interval[s,t]) (\u. &1 + norm(A(lift u)) pow 2)`
  (LABEL_TAC "var") THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(A:real^1->real^N) continuous_on interval[lift s,lift t] /\
                  (Y:real^1->real^N) continuous_on interval[lift s,lift t]`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN
        REWRITE_TAC[FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP] THEN REPEAT STRIP_TAC THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `interval[lift p,lift q]` THEN
        ASM_REWRITE_TAC[SUBSET_INTERVAL_1; LIFT_DROP] THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    ABBREV_TAC `H = \v:real^1. p2a_lacc (Gt:real->real^N->real^N^N) tt (drop v)
                                        ((Y:real^1->real^N) v) ((A:real^1->real^N) v)` THEN
    SUBGOAL_THEN `(H:real^1->real^N) continuous_on interval[lift s,lift t]` ASSUME_TAC THENL
     [EXPAND_TAC "H" THEN
      SUBGOAL_THEN
       `(\v:real^1. p2a_lacc (Gt:real->real^N->real^N^N) tt (drop v) ((Y:real^1->real^N) v)
                              ((A:real^1->real^N) v)) =
        sndcart o p2a_lfield Gt tt o (\v. pastecart v (pastecart (Y v) (A v)))`
      SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; o_THM; p2a_lfield; FSTCART_PASTECART; SNDCART_PASTECART];
        ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
       [ALL_TAC; MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN REWRITE_TAC[LINEAR_SNDCART]] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN REWRITE_TAC[CONTINUOUS_ON_ID] THEN
        MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `interval(lift sa,lift sb) PCROSS ((U:real^N->bool) PCROSS (:real^N))` THEN
      ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON] THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; PASTECART_IN_PCROSS; IN_UNIV; FORALL_LIFT;
                  IN_INTERVAL_1; LIFT_DROP] THEN
      X_GEN_TAC `u:real` THEN STRIP_TAC THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `(Y:real^1->real^N)(lift u) IN Kc` MP_TAC THENL
       [USE_THEN "K" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ASM SET_TAC[]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`H:real^1->real^N`; `interval[lift s,lift t]`] COMPACT_CONTINUOUS_IMAGE) THEN
    ASM_REWRITE_TAC[COMPACT_INTERVAL] THEN DISCH_THEN(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
    REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE; FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP] THEN
    DISCH_THEN(X_CHOOSE_THEN `MH:real` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`\v:real^1. (A:real^1->real^N) v - A(lift s)`; `H:real^1->real^N`;
                   `{}:real->bool`; `s:real`; `t:real`; `MH:real`; `t:real`]
                  P2A_VNORM_FTC_BOUND_PW) THEN
    REWRITE_TAC[VECTOR_SUB_REFL; FINITE_EMPTY; NOT_IN_EMPTY; REAL_LE_REFL] THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_SUB THEN ASM_REWRITE_TAC[CONTINUOUS_ON_CONST]; ALL_TAC] THEN
      TRY(CONJ_TAC THENL [ALL_TAC; ASM_SIMP_TAC[] THEN NO_TAC]) THEN
      X_GEN_TAC `u:real` THEN STRIP_TAC THEN
      GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) [VECTOR_ARITH `v:real^N = v - vec 0`] THEN
      MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_SUB THEN REWRITE_TAC[HAS_VECTOR_DERIVATIVE_CONST] THEN
      EXPAND_TAC "H" THEN REWRITE_TAC[LIFT_DROP] THEN
      USE_THEN "D" (MP_TAC o SPEC `u:real`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `b <= c ==> a <= b ==> a <= c`) THEN
    SUBGOAL_THEN `(\u. norm((H:real^1->real^N)(lift u))) real_integrable_on real_interval[s,t]`
    ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN
      MP_TAC(ISPECL [`\x:real^1. norm((H:real^1->real^N) x)`; `s:real`; `t:real`]
                    P2A_REAL_CONT_OF_VEC) THEN
      REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_SIMP_TAC[o_DEF; CONTINUOUS_ON_LIFT_NORM_COMPOSE];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `(\u. &1 + norm((A:real^1->real^N)(lift u)) pow 2) real_integrable_on real_interval[s,t]`
    ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_INTEGRABLE_SUBINTERVAL THEN
      MAP_EVERY EXISTS_TAC [`p:real`; `q:real`] THEN
      ASM_REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[GSYM REAL_INTEGRAL_LMUL] THEN
    MATCH_MP_TAC REAL_INTEGRAL_LE THEN
    ASM_SIMP_TAC[REAL_INTEGRABLE_LMUL; IN_REAL_INTERVAL] THEN
    X_GEN_TAC `u:real` THEN STRIP_TAC THEN EXPAND_TAC "H" THEN REWRITE_TAC[LIFT_DROP] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "K" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "var" ACCEPT_TAC);;

let P2AW_VEL_BOUND = prove
 (`!U sa sb (Gt:real->real^N->real^N^N) tt p q Kc (Y:real^1->real^N) A C E.
     p2a_lsmooth U sa sb (\s. Gt(tt - s pow 2)) /\ sa < p /\ p < q /\ q < sb /\
     compact Kc /\ Kc SUBSET U /\
     Y continuous_on interval[lift p,lift q] /\
     (!s. p <= s /\ s <= q ==> Y(lift s) IN Kc) /\
     (!s. p < s /\ s < q
          ==> (Y has_vector_derivative A(lift s)) (at (lift s)) /\
              (A has_vector_derivative p2a_lacc Gt tt s (Y(lift s)) (A(lift s)))
                (at (lift s))) /\
     A continuous_on interval[lift p,lift q] /\ &0 < C /\
     (!s y a. p <= s /\ s <= q /\ y IN Kc
              ==> norm(p2a_lacc Gt tt s y a) <= C * (&1 + norm a pow 2)) /\
     real_integral (real_interval[p,q]) (\s. norm(A(lift s)) pow 2) <= E
     ==> !s. p <= s /\ s <= q
             ==> norm(A(lift s)) <= sqrt(E / (q - p) + &1) + C * ((q - p) + E)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `closure(interval(lift p,lift q)) = interval[lift p,lift q]` ASSUME_TAC THENL
   [MATCH_MP_TAC CLOSURE_OPEN_INTERVAL THEN REWRITE_TAC[INTERVAL_EQ_EMPTY_1; LIFT_DROP] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(lift o (\x. norm((A:real^1->real^N) x))) continuous_on interval[lift p,lift q] /\
                (lift o (\x. norm((A:real^1->real^N) x) pow 2)) continuous_on
                  interval[lift p,lift q]`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[o_DEF] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_LIFT_NORM_COMPOSE THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC CONTINUOUS_ON_LIFT_POW THEN
      MATCH_MP_TAC CONTINUOUS_ON_LIFT_NORM_COMPOSE THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\s. norm((A:real^1->real^N)(lift s)) pow 2) real_integrable_on real_interval[p,q]`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN
    MP_TAC(ISPECL [`\x:real^1. norm((A:real^1->real^N) x) pow 2`; `p:real`; `q:real`]
                  P2A_REAL_CONT_OF_VEC) THEN
    ANTS_TAC THENL
     [UNDISCH_TAC `(lift o (\x. norm((A:real^1->real^N) x) pow 2)) continuous_on
                     interval[lift p,lift q]` THEN REWRITE_TAC[o_DEF];
      REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\u. &1 + norm((A:real^1->real^N)(lift u)) pow 2) real_integrable_on
                real_interval[p,q]`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRABLE_ADD THEN ASM_REWRITE_TAC[REAL_INTEGRABLE_CONST]; ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `sa:real`; `sb:real`; `Gt:real->real^N->real^N^N`; `tt:real`;
                 `p:real`; `q:real`; `Kc:real^N->bool`; `Y:real^1->real^N`; `A:real^1->real^N`;
                 `C:real`] P2AW_VEL_VAR) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(LABEL_TAC "var")] THEN
  SUBGOAL_THEN `&0 <= E` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `real_integral (real_interval[p,q]) (\s. norm((A:real^1->real^N)(lift s)) pow 2)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_INTEGRAL_POS THEN
    ASM_REWRITE_TAC[REAL_LE_POW_2];
    ALL_TAC] THEN
  ABBREV_TAC `c = E / (q - p) + &1` THEN
  SUBGOAL_THEN `&0 < c` ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 < x + &1`) THEN
    MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `c * (q - p) = E + (q - p)` ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN SUBGOAL_THEN `~(q - p = &0)` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_SIMP_TAC[REAL_ADD_RDISTRIB; REAL_DIV_RMUL; REAL_MUL_LID]];
    ALL_TAC] THEN
  (* a good point *)
  SUBGOAL_THEN `?s0. p < s0 /\ s0 < q /\ norm((A:real^1->real^N)(lift s0)) pow 2 <= c`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
    DISCH_THEN(ASSUME_TAC o REWRITE_RULE[NOT_EXISTS_THM; DE_MORGAN_THM; REAL_NOT_LE;
                                         REAL_NOT_LT]) THEN
    SUBGOAL_THEN `!x. x IN interval[lift p,lift q]
                      ==> c <= (\x. norm((A:real^1->real^N) x) pow 2) x`
    ASSUME_TAC THENL
     [FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        concl th = `closure(interval(lift p,lift q)) = interval[lift p,lift q]`)) THEN
      MATCH_MP_TAC CONTINUOUS_GE_ON_CLOSURE THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP] THEN X_GEN_TAC `s:real` THEN
      STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th ->
        can (term_match [] `!s0. s0 <= p \/ q <= s0 \/ c < norm((A:real^1->real^N)(lift s0)) pow 2`)
            (concl th))) THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `real_integral (real_interval[p,q]) (\s:real. c) <=
      real_integral (real_interval[p,q]) (\s. norm((A:real^1->real^N)(lift s)) pow 2)`
    MP_TAC THENL
     [MATCH_MP_TAC REAL_INTEGRAL_LE THEN ASM_REWRITE_TAC[REAL_INTEGRABLE_CONST] THEN
      X_GEN_TAC `s:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `lift s` o check (fun th ->
        can (term_match [] `!x. x IN interval[lift p,lift q]
                                ==> c <= (\x. norm((A:real^1->real^N) x) pow 2) x`) (concl th))) THEN
      ASM_REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP];
      ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_INTEGRAL_CONST; REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the integral of 1 + |A|^2 over subintervals *)
  SUBGOAL_THEN
   `!s t. p <= s /\ s <= t /\ t <= q
          ==> real_integral (real_interval[s,t]) (\u. &1 + norm((A:real^1->real^N)(lift u)) pow 2)
              <= (q - p) + E`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `real_integral (real_interval[p,q])
                  (\u. &1 + norm((A:real^1->real^N)(lift u)) pow 2)` THEN
    CONJ_TAC THENL
     [SUBGOAL_THEN `real_interval[s,t] SUBSET real_interval[p,q]` ASSUME_TAC THENL
       [REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_INTEGRAL_SUBSET_LE THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_INTEGRABLE_SUBINTERVAL THEN
        MAP_EVERY EXISTS_TAC [`p:real`; `q:real`] THEN ASM_REWRITE_TAC[];
        X_GEN_TAC `u:real` THEN DISCH_TAC THEN
        MP_TAC(SPEC `norm((A:real^1->real^N)(lift u))` REAL_LE_POW_2) THEN REAL_ARITH_TAC];
      ASM_SIMP_TAC[REAL_INTEGRAL_ADD; REAL_INTEGRABLE_CONST; REAL_INTEGRAL_CONST;
                   REAL_LT_IMP_LE] THEN
      MATCH_MP_TAC(REAL_ARITH `x <= e ==> &1 * d + x <= d + e`) THEN
      FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `norm((A:real^1->real^N)(lift s0)) <= sqrt c` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_RSQRT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* interior points *)
  SUBGOAL_THEN
   `!s. p < s /\ s < q ==> norm((A:real^1->real^N)(lift s)) <= sqrt c + C * ((q - p) + E)`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `norm((A:real^1->real^N)(lift s) - A(lift s0)) <= C * ((q - p) + E)`
    MP_TAC THENL
     [DISJ_CASES_TAC(REAL_ARITH `s0 <= s \/ s <= s0`) THENL
       [MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `C * real_integral (real_interval[s0,s])
                          (\u. &1 + norm((A:real^1->real^N)(lift u)) pow 2)` THEN
        CONJ_TAC THENL
         [USE_THEN "var" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
          MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
          FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
        ONCE_REWRITE_TAC[NORM_SUB] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `C * real_integral (real_interval[s,s0])
                          (\u. &1 + norm((A:real^1->real^N)(lift u)) pow 2)` THEN
        CONJ_TAC THENL
         [USE_THEN "var" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
          MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
          FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC]];
      MP_TAC(ISPECL [`(A:real^1->real^N)(lift s)`; `(A:real^1->real^N)(lift s0)`]
                    NORM_TRIANGLE_SUB) THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* end points by continuity *)
  SUBGOAL_THEN `!x. x IN interval[lift p,lift q]
                    ==> (\x. norm((A:real^1->real^N) x)) x <= sqrt c + C * ((q - p) + E)`
  MP_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `closure(interval(lift p,lift q)) = interval[lift p,lift q]`)) THEN
    MATCH_MP_TAC CONTINUOUS_LE_ON_CLOSURE THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP] THEN ASM_SIMP_TAC[];
    REWRITE_TAC[FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP] THEN SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Small facts for the comparison argument: scalar lower bounds along        *)
(* admissible curves of a flow, the reduced length is at most the length of  *)
(* any admissible curve, derivatives of the combined family, C^1 from        *)
(* derivatives on an open set, and the energy bound from a lower bound of    *)
(* the metric and of the potential term.                                     *)
(* ------------------------------------------------------------------------- *)

let P2AW_FLOW_SCAL_ALONG = prove
 (`!top atlas a b (g:real->A->real^N^N) m x tau (gamma:real->A).
     (!t y. a <= t /\ t <= b /\ y IN topspace top ==> m <= mfd_scalar atlas (g t) y) /\
     p2a_adm (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b x tau gamma /\ tau <= b - a
     ==> !tau'. &0 <= tau' /\ tau' <= tau
                ==> m <= mfd_scalar
                           (p2a_vatlas (p2a_flow_view (top,atlas) (real_interval[a,b]) g) (b - tau'))
                           (p2a_vmetric (p2a_flow_view (top,atlas) (real_interval[a,b]) g) (b - tau'))
                           (gamma tau')`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `tau':real` THEN STRIP_TAC THEN
  SUBGOAL_THEN `b - tau' IN real_interval[a,b]` ASSUME_TAC THENL
   [REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(gamma:real->A) tau' IN topspace top` ASSUME_TAC THENL
   [UNDISCH_TAC `p2a_adm (p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^N^N))
                   b x tau (gamma:real->A)` THEN
    REWRITE_TAC[p2a_adm] THEN
    DISCH_THEN(MP_TAC o SPEC `tau':real` o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[p2a_flow_view; p2a_vtop];
    ALL_TAC] THEN
  REWRITE_TAC[p2a_flow_view; p2a_vatlas; p2a_vmetric] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let P2AW_FLOW_LX_LE = prove
 (`!top atlas a b (g:real->A->real^N^N) m x tau (gamma:real->A).
     (!t y. a <= t /\ t <= b /\ y IN topspace top ==> m <= mfd_scalar atlas (g t) y) /\
     p2a_adm (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b x tau gamma /\ tau <= b - a
     ==> p2a_Lx (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b x tau (gamma tau) <=
         p2a_L_length (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b gamma tau`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p2a_Lx] THEN MATCH_MP_TAC REAL_INF_LE THEN
  MAP_EVERY EXISTS_TAC
   [`--(abs m * sqrt tau * tau)`;
    `p2a_L_length (p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^N^N)) b
                  (gamma:real->A) tau`] THEN
  REWRITE_TAC[REAL_LE_REFL; IN_ELIM_THM] THEN CONJ_TAC THENL
   [EXISTS_TAC `gamma:real->A` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `l:real` THEN DISCH_THEN(X_CHOOSE_THEN `g':real->A` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P2AW_ADM_LOWER THEN EXISTS_TAC `x:A` THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC P2AW_FLOW_SCAL_ALONG THEN EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[]);;

let P2AW_VDERIV_CONT_OPEN = prove
 (`!(f:real^1->real^N) f' s x.
     open s /\ x IN s /\ (!v. v IN s ==> (f has_vector_derivative f' v) (at v)) /\
     f' continuous (at x)
     ==> f differentiable (at x) /\ (\v. vector_derivative f (at v)) continuous (at x)`,
  REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_IMP_DIFFERENTIABLE THEN ASM_MESON_TAC[];
    MATCH_MP_TAC CONTINUOUS_TRANSFORM_WITHIN_OPEN THEN
    MAP_EVERY EXISTS_TAC [`f':real^1->real^N`; `s:real^1->bool`] THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `v:real^1` THEN DISCH_TAC THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC VECTOR_DERIVATIVE_AT THEN ASM_SIMP_TAC[]]);;

let P2AW_CFAM_DERIV = prove
 (`!(y:real^1->real^N) B s1 sb w k r.
     &0 < k /\ (y has_vector_derivative B) (at (lift(s1 + (r - s1) / k)))
     ==> (p2aw_cfam y s1 sb w k has_vector_derivative (inv k % (B + inv(sb - s1) % w)))
           (at (lift r))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `p2aw_cfam (y:real^1->real^N) s1 sb w k =
                p2aw_sfam y s1 sb w o (\v. lift(s1 + (drop v - s1) / k))`
  SUBST1_TAC THENL [REWRITE_TAC[p2aw_cfam; FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `inv k % ((B:real^N) + inv(sb - s1) % w) =
                drop(lift(inv k)) % (B + inv(sb - s1) % w)`
  SUBST1_TAC THENL [REWRITE_TAC[LIFT_DROP]; ALL_TAC] THEN
  MATCH_MP_TAC VECTOR_DIFF_CHAIN_AT THEN REWRITE_TAC[LIFT_DROP] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`vec 1:real^1`; `inv k`; `s1 - s1 / k`; `at(lift r)`]
                  P2AW_AFFINE_VDERIV) THEN
    REWRITE_TAC[GSYM LIFT_EQ_CMUL] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[real_div] THEN REAL_ARITH_TAC;
    MATCH_MP_TAC P2AW_SFAM_DERIV THEN ASM_REWRITE_TAC[]]);;

let P2AW_CFAM_ONE = prove
 (`!(y:real^1->real^N) s1 sb w. p2aw_cfam y s1 sb w (&1) = p2aw_sfam y s1 sb w`,
  REWRITE_TAC[p2aw_cfam; FUN_EQ_THM; REAL_DIV_1; REAL_SUB_ADD2; LIFT_DROP]);;

let P2AW_CFAM_ENDS = prove
 (`!(y:real^1->real^N) s1 sb w k.
     &0 < k /\ s1 < sb
     ==> p2aw_cfam y s1 sb w k (lift s1) = y(lift s1) /\
         p2aw_cfam y s1 sb w k (lift(s1 + k * (sb - s1))) = y(lift sb) + w`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p2aw_cfam; p2aw_sfam; LIFT_DROP] THENL
   [REWRITE_TAC[REAL_SUB_REFL; real_div; REAL_MUL_LZERO; REAL_ADD_RID; VECTOR_MUL_LZERO;
                VECTOR_ADD_RID];
    SUBGOAL_THEN `s1 + ((s1 + k * (sb - s1)) - s1) / k = sb` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < k` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    SUBGOAL_THEN `(sb - s1) / (sb - s1) = &1` SUBST1_TAC THENL
     [MATCH_MP_TAC REAL_DIV_REFL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[LIFT_DROP; VECTOR_MUL_LID]]);;

let P2AW_ENERGY_BOUND = prove
 (`!(Gt:real->real^N->real^N^N) tt (Y:real^1->real^N) A p q c Kb.
     p < q /\ &0 < c /\
     A continuous_on interval[lift p,lift q] /\
     (\s. p2a_llag Gt tt s (Y(lift s)) (A(lift s))) real_integrable_on real_interval[p,q] /\
     (!s. p <= s /\ s <= q
          ==> c * norm(A(lift s)) pow 2 <=
              A(lift s) dot (Gt(tt - s pow 2) (Y(lift s)) ** A(lift s)) /\
              --Kb <= p2a_llag Gt tt s (Y(lift s)) (vec 0))
     ==> real_integral (real_interval[p,q]) (\s. norm(A(lift s)) pow 2) <=
         (&2 / c) * (real_integral (real_interval[p,q])
                       (\s. p2a_llag Gt tt s (Y(lift s)) (A(lift s))) + Kb * (q - p))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\s. norm((A:real^1->real^N)(lift s)) pow 2) real_integrable_on real_interval[p,q]`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN
    MP_TAC(ISPECL [`\x:real^1. norm((A:real^1->real^N) x) pow 2`; `p:real`; `q:real`]
                  P2A_REAL_CONT_OF_VEC) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    MATCH_MP_TAC CONTINUOUS_ON_LIFT_POW THEN
    MATCH_MP_TAC CONTINUOUS_ON_LIFT_NORM_COMPOSE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `En = real_integral (real_interval[p,q]) (\s. norm((A:real^1->real^N)(lift s)) pow 2)` THEN
  ABBREV_TAC `I0 = real_integral (real_interval[p,q])
                     (\s. p2a_llag (Gt:real->real^N->real^N^N) tt s ((Y:real^1->real^N)(lift s))
                                   ((A:real^1->real^N)(lift s)))` THEN
  SUBGOAL_THEN `(c / &2) * En - Kb * (q - p) <= I0` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `real_integral (real_interval[p,q])
                  (\s. (c / &2) * norm((A:real^1->real^N)(lift s)) pow 2 - Kb)` THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`\s. (c / &2) * norm((A:real^1->real^N)(lift s)) pow 2`; `\s:real. (Kb:real)`;
                     `real_interval[p,q]`] REAL_INTEGRAL_SUB) THEN
      ASM_SIMP_TAC[REAL_INTEGRABLE_LMUL; REAL_INTEGRABLE_CONST] THEN DISCH_THEN SUBST1_TAC THEN
      ASM_SIMP_TAC[REAL_INTEGRAL_LMUL; REAL_INTEGRAL_CONST; REAL_LT_IMP_LE] THEN
      REAL_ARITH_TAC;
      EXPAND_TAC "I0" THEN MATCH_MP_TAC REAL_INTEGRAL_LE THEN
      ASM_SIMP_TAC[REAL_INTEGRABLE_SUB; REAL_INTEGRABLE_LMUL; REAL_INTEGRABLE_CONST] THEN
      X_GEN_TAC `s:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
      ONCE_REWRITE_TAC[P2A_LLAG_SPLIT] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `s:real`) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < c / &2` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!X. &2 / c * X = X / (c / &2)` (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN UNDISCH_TAC `&0 < c` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The L-length of a minimizer of a flow cut at s1^2: the final piece is the *)
(* s-form length of its chart curve, which equals that of the tangent-line   *)
(* extension (p2aw_rext) on [s1, sqrt tau].                                  *)
(* ------------------------------------------------------------------------- *)

let P2AW_FLOW_CUT = prove
 (`!top atlas a b (g:real->A->real^3^3) p tau (gamma:real->A) U (phi:A->real^3) s0 s1 A.
     p2a_cbflow (top,atlas) a b g /\ p IN topspace top /\ (U,phi) IN atlas /\
     p2a_min (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p tau gamma /\
     tau < b - a /\ &0 < s0 /\ s0 < s1 /\ s1 < sqrt tau /\
     (!s. s0 <= s /\ s <= sqrt tau ==> gamma(s pow 2) IN U) /\
     A continuous_on interval[lift s0,lift(sqrt tau)] /\
     (!s. s0 < s /\ s < sqrt tau
          ==> ((\v. phi(gamma(drop v pow 2))) has_vector_derivative A(lift s)) (at (lift s))) /\
     ((\v. phi(gamma(drop v pow 2))) has_vector_derivative A(lift(sqrt tau)))
       (at (lift(sqrt tau)) within interval[lift s0,lift(sqrt tau)])
     ==> p2a_L_length (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b gamma tau =
         p2a_L_length (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b gamma (s1 pow 2) +
         p2a_cL (p2a_rlocal (p2a_flow_view (top,atlas) (real_interval[a,b]) g) U b (U,phi)) b
                (\v. phi(gamma(drop v pow 2))) s1 (sqrt tau)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2AW_FLOW_FACTS) THEN
  ABBREV_TAC `V = p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3)` THEN
  SUBGOAL_THEN `open_in top (U:A->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[SMOOTH_MANIFOLD_ATLAS_CHART]; ALL_TAC] THEN
  SUBGOAL_THEN `p2a_region (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) U a b`
  ASSUME_TAC THENL
   [EXPAND_TAC "V" THEN MATCH_MP_TAC P2AW_CBFLOW_REGION THEN ASM_REWRITE_TAC[REAL_LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `p2a_adm (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                           (real->A->real^3^3)) b p tau gamma`
  ASSUME_TAC THENL [ASM_MESON_TAC[p2a_min]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < tau` ASSUME_TAC THENL
   [FIRST_ASSUM(ACCEPT_TAC o MATCH_MP SPDR13_ADM_POS); ALL_TAC] THEN
  SUBGOAL_THEN `sqrt tau pow 2 = tau /\ &0 < sqrt tau` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POW_2; SQRT_POS_LT; REAL_LT_IMP_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < s1 pow 2 /\ s1 pow 2 <= tau` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    FIRST_ASSUM((fun th -> GEN_REWRITE_TAC (RAND_CONV) [GSYM th]) o
      check (fun th -> concl th = `sqrt tau pow 2 = tau`)) THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt tau < sqrt(b - a)` ASSUME_TAC THENL
   [MATCH_MP_TAC SQRT_MONO_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!s. &0 < s /\ s < sqrt(b - a) ==> a < b - s pow 2 /\ b - s pow 2 <= b`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `s pow 2 < sqrt(b - a) pow 2` MP_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[ARITH_EQ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `sqrt(b - a) pow 2 = b - a` SUBST1_TAC THENL
     [MATCH_MP_TAC SQRT_POW_2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPEC `s:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `?M. !s. s0 <= s /\ s <= sqrt tau ==> norm((A:real^1->real^3)(lift s)) <= M`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `IMAGE (A:real^1->real^3) (interval[lift s0,lift(sqrt tau)])`
                 COMPACT_IMP_BOUNDED) THEN
    ASM_SIMP_TAC[COMPACT_CONTINUOUS_IMAGE; COMPACT_INTERVAL] THEN
    REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE; FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
                 `b:real`; `p:A`; `gamma:real->A`; `tau:real`; `s1 pow 2`] P2A_LENGTH_SPLIT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC REAL_INTEGRAL_UNIQUE THEN
  SUBGOAL_THEN `real_interval[s1 pow 2,tau] = real_interval[s1 pow 2,sqrt tau pow 2]`
  SUBST1_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `p2a_rlocal (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) U b (U,phi) =
                p2a_rlocal V U b (U INTER U,phi)` SUBST1_TAC THENL
   [REWRITE_TAC[INTER_IDEMPOT]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < s1` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC P2A_LINT_PIECE THEN
  MAP_EVERY EXISTS_TAC [`a:real`; `{}:real->bool`; `&0`; `sqrt(b - a)`; `M:real`] THEN
  ASM_REWRITE_TAC[INTER_IDEMPOT; FINITE_EMPTY; NOT_IN_EMPTY; REAL_LE_REFL] THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    MAP_EVERY X_GEN_TAC [`s:real`; `O:A->bool`] THEN STRIP_TAC THEN
    MP_TAC(SPECL [`s:real`; `O:A->bool`] (MATCH_MP P2A_ADM_SCONT (ASSUME
      `p2a_adm (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                  (real->A->real^3^3)) b p tau gamma`))) THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    FIRST_ASSUM((fun th -> GEN_REWRITE_TAC (RAND_CONV) [GSYM th]) o
      check (fun th -> concl th = `sqrt tau pow 2 = tau`)) THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN; FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP] THEN
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    ASM_CASES_TAC `s = sqrt tau` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_WITHIN THEN
      MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_IMP_DIFFERENTIABLE THEN
      EXISTS_TAC `(A:real^1->real^3)(lift(sqrt tau))` THEN
      MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_WITHIN_SUBSET THEN
      EXISTS_TAC `interval[lift s0,lift(sqrt tau)]` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBSET_INTERVAL_1; LIFT_DROP] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC CONTINUOUS_AT_WITHIN THEN MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN
      MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_IMP_DIFFERENTIABLE THEN
      EXISTS_TAC `(A:real^1->real^3)(lift s)` THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REAL_ARITH_TAC];
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `s pow 2 < tau` ASSUME_TAC THENL
     [FIRST_ASSUM((fun th -> GEN_REWRITE_TAC (RAND_CONV) [GSYM th]) o
        check (fun th -> concl th = `sqrt tau pow 2 = tau`)) THEN
      MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[ARITH_EQ] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                   `g:real->A->real^3^3`; `p:A`; `tau:real`; `gamma:real->A`; `U:A->bool`;
                   `phi:A->real^3`; `s:real`] P2AW_FLOW_MIN_C1) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `U:A->bool`)) (concl th) &&
        not (can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_rlocal")) (concl th)))) THEN
      ASM_REAL_ARITH_TAC;
      STRIP_TAC THEN ASM_REWRITE_TAC[]] THEN
    SUBGOAL_THEN `vector_derivative (\v. (phi:A->real^3)((gamma:real->A)(drop v pow 2)))
                    (at (lift s)) = (A:real^1->real^3)(lift s)` SUBST1_TAC THENL
     [MATCH_MP_TAC VECTOR_DERIVATIVE_AT THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC]]);;

let P2AW_REXT_CL = prove
 (`!(Gt:real->real^N->real^N^N) tt (Y:real^1->real^N) A s0 s1 sb.
     s0 < s1 /\ s1 < sb /\
     (!s. s0 < s /\ s < sb ==> (Y has_vector_derivative A(lift s)) (at (lift s))) /\
     (Y has_vector_derivative A(lift sb)) (at (lift sb) within interval[lift s0,lift sb]) /\
     A continuous_on interval[lift s0,lift sb]
     ==> p2a_cL Gt tt (p2aw_rext Y A sb) s1 sb = p2a_cL Gt tt Y s1 sb`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`Y:real^1->real^N`; `A:real^1->real^N`; `s0:real`; `sb:real`]
                P2AW_C1_EXTEND) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  REWRITE_TAC[p2a_cL] THEN
  MATCH_MP_TAC(MESON[P2A_REAL_INTEGRAL_OPEN_EQ]
   `!f g:real->real a c. (!t. a < t /\ t < c ==> f t = g t)
                        ==> real_integral (real_interval[a,c]) f =
                            real_integral (real_interval[a,c]) g`) THEN
  X_GEN_TAC `s:real` THEN STRIP_TAC THEN
  SUBGOAL_THEN `vector_derivative (p2aw_rext (Y:real^1->real^N) A sb) (at (lift s)) = A(lift s) /\
                vector_derivative Y (at (lift s)) = A(lift s)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC VECTOR_DERIVATIVE_AT THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "p2aw_dext")) (concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "has_vector_derivative")) (concl th))) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "p2aw_dext")) (concl th) &&
        not (can (find_term (fun t -> is_const t && fst(dest_const t) = "has_vector_derivative")) (concl th)) &&
        not (can (find_term (fun t -> is_const t && fst(dest_const t) = "continuous")) (concl th)))) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p2aw_rext")) (concl th) &&
    not (can (find_term (fun t -> is_const t && fst(dest_const t) = "has_vector_derivative")) (concl th)))) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The comparison inequality.  A minimizer of a flow cut at s1^2 and         *)
(* continued by the combined family of the tangent extension of its chart    *)
(* curve reaches chart_inv(phi(gamma tau) + w) at time (s1 + k (sqrt tau -   *)
(* s1))^2; so the reduced length there is at most L(gamma|[0,s1^2]) +        *)
(* cL(family) (P2AW_GLUE, P2AW_FLOW_LX_LE).                                  *)
(* ------------------------------------------------------------------------- *)

let P2AW_REPAR_VDERIV = prove
 (`!s1 k net. ((\v:real^1. lift(s1 + (drop v - s1) / k)) has_vector_derivative lift(inv k)) net`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`vec 1:real^1`; `inv k`; `s1 - s1 / k`; `net:(real^1)net`]
                P2AW_AFFINE_VDERIV) THEN
  REWRITE_TAC[GSYM LIFT_EQ_CMUL] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[real_div] THEN REAL_ARITH_TAC);;

let P2AW_FLOW_CMP = prove
 (`!top atlas a b (g:real->A->real^3^3) m p tau (gamma:real->A) U (phi:A->real^3) s0 s1 A w k.
     p2a_cbflow (top,atlas) a b g /\ p IN topspace top /\ (U,phi) IN atlas /\
     (!t y. a <= t /\ t <= b /\ y IN topspace top ==> m <= mfd_scalar atlas (g t) y) /\
     p2a_min (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p tau gamma /\
     tau < b - a /\ &0 < s0 /\ s0 < s1 /\ s1 < sqrt tau /\
     (!s. s0 <= s /\ s <= sqrt tau ==> gamma(s pow 2) IN U) /\
     A continuous_on interval[lift s0,lift(sqrt tau)] /\
     (!s. s0 < s /\ s < sqrt tau
          ==> ((\v. phi(gamma(drop v pow 2))) has_vector_derivative A(lift s)) (at (lift s))) /\
     ((\v. phi(gamma(drop v pow 2))) has_vector_derivative A(lift(sqrt tau)))
       (at (lift(sqrt tau)) within interval[lift s0,lift(sqrt tau)]) /\
     &0 < k /\ (s1 + k * (sqrt tau - s1)) pow 2 < b - a /\
     (!s. s1 <= s /\ s <= sqrt tau
          ==> p2aw_rext (\v. phi(gamma(drop v pow 2))) A (sqrt tau) (lift s) +
              ((s - s1) / (sqrt tau - s1)) % w IN IMAGE phi U)
     ==> p2a_Lx (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p
                ((s1 + k * (sqrt tau - s1)) pow 2) (chart_inv (U,phi) (phi(gamma tau) + w)) <=
         p2a_L_length (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b gamma (s1 pow 2) +
         p2a_cL (p2a_rlocal (p2a_flow_view (top,atlas) (real_interval[a,b]) g) U b (U,phi)) b
                (p2aw_cfam (p2aw_rext (\v. phi(gamma(drop v pow 2))) A (sqrt tau))
                           s1 (sqrt tau) w k)
                s1 (s1 + k * (sqrt tau - s1))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2AW_FLOW_FACTS) THEN
  SUBGOAL_THEN `open_in top (U:A->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[SMOOTH_MANIFOLD_ATLAS_CHART]; ALL_TAC] THEN
  SUBGOAL_THEN `p2a_region (p2a_flow_view (top,atlas) (real_interval[a,b])
                              (g:real->A->real^3^3)) U a b` ASSUME_TAC THENL
   [MATCH_MP_TAC P2AW_CBFLOW_REGION THEN ASM_REWRITE_TAC[REAL_LE_REFL]; ALL_TAC] THEN
  ABBREV_TAC `V = p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3)` THEN
  SUBGOAL_THEN `p2a_adm (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                           (real->A->real^3^3)) b p tau gamma`
  ASSUME_TAC THENL [ASM_MESON_TAC[p2a_min]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < tau` ASSUME_TAC THENL
   [FIRST_ASSUM(ACCEPT_TAC o MATCH_MP SPDR13_ADM_POS); ALL_TAC] THEN
  SUBGOAL_THEN `sqrt tau pow 2 = tau /\ &0 < sqrt tau` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POW_2; SQRT_POS_LT; REAL_LT_IMP_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < s1 /\ s1 < s1 + k * (sqrt tau - s1)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 < x ==> s1 < s1 + x`) THEN MATCH_MP_TAC REAL_LT_MUL THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `s1 + k * (sqrt tau - s1) < sqrt(b - a)` ASSUME_TAC THENL
   [SUBGOAL_THEN `sqrt((s1 + k * (sqrt tau - s1)) pow 2) < sqrt(b - a)` MP_TAC THENL
     [MATCH_MP_TAC SQRT_MONO_LT THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      MATCH_MP_TAC POW_2_SQRT THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `s1 pow 2 < tau` ASSUME_TAC THENL
   [FIRST_ASSUM((fun th -> GEN_REWRITE_TAC (RAND_CONV) [GSYM th]) o
      check (fun th -> concl th = `sqrt tau pow 2 = tau`)) THEN
    MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[ARITH_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\v:real^1. (phi:A->real^3)((gamma:real->A)(drop v pow 2))`;
                 `A:real^1->real^3`; `s0:real`; `sqrt tau`] P2AW_C1_EXTEND) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    DISCH_THEN(STRIP_ASSUME_TAC o REWRITE_RULE[LIFT_DROP])] THEN
  ABBREV_TAC `sol = p2aw_cfam (p2aw_rext (\v:real^1. (phi:A->real^3)((gamma:real->A)(drop v pow 2)))
                                         A (sqrt tau)) s1 (sqrt tau) w k` THEN
  (* derivatives of the family *)
  SUBGOAL_THEN
   `!r. s0 < s1 + (r - s1) / k
        ==> ((sol:real^1->real^3) has_vector_derivative
             (inv k % (p2aw_dext A (sqrt tau) (lift(s1 + (r - s1) / k)) +
                       inv(sqrt tau - s1) % w))) (at (lift r))`
  (LABEL_TAC "SD") THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "sol" THEN MATCH_MP_TAC P2AW_CFAM_DERIV THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!r. s1 <= r /\ r <= s1 + k * (sqrt tau - s1)
        ==> (sol:real^1->real^3) differentiable (at (lift r)) /\
            (\v. vector_derivative sol (at v)) continuous (at (lift r))`
  (LABEL_TAC "SC1") THENL
   [X_GEN_TAC `r:real` THEN STRIP_TAC THEN MATCH_MP_TAC P2AW_VDERIV_CONT_OPEN THEN
    EXISTS_TAC `\v:real^1. inv k % (p2aw_dext (A:real^1->real^3) (sqrt tau)
                                     (lift(s1 + (drop v - s1) / k)) + inv(sqrt tau - s1) % w)` THEN
    EXISTS_TAC `interval(lift(s1 - k * (s1 - s0)),lift(s1 + k * (sqrt tau - s1) + &1))` THEN
    REWRITE_TAC[OPEN_INTERVAL; IN_INTERVAL_1; LIFT_DROP] THEN
    SUBGOAL_THEN `&0 < k * (s1 - s0)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      REWRITE_TAC[FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP] THEN X_GEN_TAC `v:real` THEN
      STRIP_TAC THEN USE_THEN "SD" MATCH_MP_TAC THEN
      MATCH_MP_TAC(REAL_ARITH `--(s1 - s0) < x ==> s0 < s1 + x`) THEN
      ASM_SIMP_TAC[REAL_LT_RDIV_EQ] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC CONTINUOUS_CMUL THEN MATCH_MP_TAC CONTINUOUS_ADD THEN
      REWRITE_TAC[CONTINUOUS_CONST] THEN
      SUBGOAL_THEN `(\v:real^1. p2aw_dext (A:real^1->real^3) (sqrt tau)
                                  (lift(s1 + (drop v - s1) / k))) =
                    p2aw_dext A (sqrt tau) o (\v. lift(s1 + (drop v - s1) / k))`
      SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_AT_COMPOSE THEN CONJ_TAC THENL
       [MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN
        MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_IMP_DIFFERENTIABLE THEN
        EXISTS_TAC `lift(inv k)` THEN REWRITE_TAC[P2AW_REPAR_VDERIV];
        REWRITE_TAC[LIFT_DROP] THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
          can (find_term (fun t -> is_const t && fst(dest_const t) = "continuous")) (concl th) &&
          can (find_term (fun t -> is_const t && fst(dest_const t) = "p2aw_dext")) (concl th))) THEN
        MATCH_MP_TAC(REAL_ARITH `s0 < s1 /\ &0 <= x ==> s0 < s1 + x`) THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  (* values of the family in the chart image *)
  SUBGOAL_THEN
   `!r. s1 <= r /\ r <= s1 + k * (sqrt tau - s1)
        ==> (sol:real^1->real^3)(lift r) IN IMAGE (phi:A->real^3) (U INTER U)`
  (LABEL_TAC "SIN") THENL
   [X_GEN_TAC `r:real` THEN STRIP_TAC THEN EXPAND_TAC "sol" THEN
    REWRITE_TAC[p2aw_cfam; p2aw_sfam; LIFT_DROP; INTER_IDEMPOT] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "IMAGE")) (concl th))) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> s1 <= s1 + x`) THEN MATCH_MP_TAC REAL_LE_DIV THEN
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC(REAL_ARITH `x <= sb - s1 ==> s1 + x <= sb`) THEN
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* the glued curve *)
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
                 `b:real`; `p:A`; `tau:real`; `gamma:real->A`; `U:A->bool`; `a:real`; `b:real`;
                 `U:A->bool`; `phi:A->real^3`; `sol:real^1->real^3`; `s1:real`;
                 `s1 + k * (sqrt tau - s1)`; `&0`; `sqrt(b - a)`] P2AW_GLUE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[INTER_IDEMPOT] THEN REPEAT CONJ_TAC THENL
     [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
      SUBGOAL_THEN `s pow 2 < sqrt(b - a) pow 2 /\ &0 < s pow 2` MP_TAC THENL
       [CONJ_TAC THENL
         [MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[ARITH_EQ] THEN ASM_REAL_ARITH_TAC;
          MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC];
        ALL_TAC] THEN
      SUBGOAL_THEN `sqrt(b - a) pow 2 = b - a` SUBST1_TAC THENL
       [MATCH_MP_TAC SQRT_POW_2 THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `U:A->bool`)) (concl th) &&
        not (can (find_term (fun t -> is_const t && fst(dest_const t) = "IMAGE")) (concl th)) &&
        not (can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_vtop")) (concl th)))) THEN
      ASM_REAL_ARITH_TAC;
      EXPAND_TAC "sol" THEN
      MP_TAC(ISPECL [`p2aw_rext (\v:real^1. (phi:A->real^3)((gamma:real->A)(drop v pow 2)))
                                (A:real^1->real^3) (sqrt tau)`;
                     `s1:real`; `sqrt tau`; `w:real^3`; `k:real`] P2AW_CFAM_ENDS) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "p2aw_rext")) (concl th) &&
        not (can (find_term (fun t -> is_const t && fst(dest_const t) = "IMAGE")) (concl th)) &&
        not (can (find_term (fun t -> is_const t && fst(dest_const t) = "has_vector_derivative"))
               (concl th)))) THEN
      ASM_REAL_ARITH_TAC;
      X_GEN_TAC `s:real` THEN STRIP_TAC THEN
      SUBGOAL_THEN `(sol:real^1->real^3)(lift s) IN IMAGE (phi:A->real^3) (U INTER U)` MP_TAC THENL
       [USE_THEN "SIN" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[INTER_IDEMPOT] THEN DISCH_TAC] THEN
      ASM_REWRITE_TAC[] THEN USE_THEN "SC1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    REWRITE_TAC[INTER_IDEMPOT] THEN STRIP_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                 `g:real->A->real^3^3`; `m:real`; `p:A`; `(s1 + k * (sqrt tau - s1)) pow 2`;
                 `p2aw_glue (gamma:real->A) U U (phi:A->real^3) sol s1`] P2AW_FLOW_LX_LE) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(sol:real^1->real^3)(lift(s1 + k * (sqrt tau - s1))) =
                phi((gamma:real->A) tau) + w`
  SUBST1_TAC THENL
   [EXPAND_TAC "sol" THEN
    MP_TAC(ISPECL [`p2aw_rext (\v:real^1. (phi:A->real^3)((gamma:real->A)(drop v pow 2)))
                              (A:real^1->real^3) (sqrt tau)`;
                   `s1:real`; `sqrt tau`; `w:real^3`; `k:real`] P2AW_CFAM_ENDS) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `sqrt tau` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "p2aw_rext")) (concl th) &&
      not (can (find_term (fun t -> is_const t && fst(dest_const t) = "IMAGE")) (concl th)) &&
      not (can (find_term (fun t -> is_const t && fst(dest_const t) = "has_vector_derivative"))
             (concl th)))) THEN
    ASM_REWRITE_TAC[REAL_LE_REFL];
    ALL_TAC] THEN
  SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Uniform end data of a minimizer of a flow.  Given a chart ball around the *)
(* end point, lower bounds of the metric, bounds of the potential and of the *)
(* geodesic acceleration on a compact chart set, and an upper bound of the   *)
(* length, the minimizer stays in the ball on the last D0 of s = sqrt(tau)   *)
(* (P2AW_FLOW_EXIT), its chart curve is C^1 there (P2AW_FLOW_MIN_CHART), and *)
(* its velocity is bounded on the last D0/2 by a constant depending only on  *)
(* the data (energy bound + P2AW_VEL_BOUND).                                 *)
(* ------------------------------------------------------------------------- *)

let P2AW_VDERIV_INTERIOR = prove
 (`!(f:real^1->real^N) f' a b s.
     a < s /\ s < b /\ (f has_vector_derivative f') (at (lift s) within interval[lift a,lift b])
     ==> (f has_vector_derivative f') (at (lift s))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^1->real^N`; `\x:real^1. drop x % (f':real^N)`; `lift s`;
                 `interval(lift a,lift b)`] HAS_DERIVATIVE_WITHIN_OPEN) THEN
  REWRITE_TAC[OPEN_INTERVAL; IN_INTERVAL_1; LIFT_DROP; GSYM has_vector_derivative] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_WITHIN_SUBSET THEN
  EXISTS_TAC `interval[lift a,lift b]` THEN ASM_REWRITE_TAC[INTERVAL_OPEN_SUBSET_CLOSED]);;

let P2AW_CHART_CURVE_CONT = prove
 (`!(Y:real^1->real^N) A s0 p sb.
     s0 < p /\ p <= sb /\
     (!s. s0 < s /\ s < sb ==> (Y has_vector_derivative A(lift s)) (at (lift s))) /\
     (Y has_vector_derivative A(lift sb)) (at (lift sb) within interval[lift s0,lift sb])
     ==> Y continuous_on interval[lift p,lift sb]`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN; FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP] THEN
  X_GEN_TAC `s:real` THEN STRIP_TAC THEN
  ASM_CASES_TAC `s:real = sb` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_WITHIN THEN
    MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_IMP_DIFFERENTIABLE THEN
    EXISTS_TAC `(A:real^1->real^N)(lift sb)` THEN
    MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_WITHIN_SUBSET THEN
    EXISTS_TAC `interval[lift s0,lift sb]` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET_INTERVAL_1; LIFT_DROP] THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC CONTINUOUS_AT_WITHIN THEN MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN
    MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_IMP_DIFFERENTIABLE THEN
    EXISTS_TAC `(A:real^1->real^N)(lift s)` THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REAL_ARITH_TAC]);;

let P2AW_FLOW_END_UNIF = prove
 (`!top atlas a b (g:real->A->real^3^3) m p tau (gamma:real->A) U (phi:A->real^3)
    K2 r0 sl sh c Kp Cacc Lup D0.
     p2a_cbflow (top,atlas) a b g /\ p IN topspace top /\ (U,phi) IN atlas /\
     (!t y. a <= t /\ t <= b /\ y IN topspace top ==> m <= mfd_scalar atlas (g t) y) /\
     p2a_min (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p tau gamma /\
     tau < b - a /\ gamma tau IN U /\
     compact K2 /\ K2 SUBSET IMAGE phi U /\ &0 < r0 /\ cball(phi(gamma tau),r0) SUBSET K2 /\
     &0 < sl /\ sl + D0 <= sqrt tau /\ sqrt tau <= sh /\ &0 < c /\ &0 <= Kp /\ &0 < Cacc /\
     (!r y A. sl <= r /\ r <= sh /\ y IN K2
              ==> c * norm A pow 2 <=
                  A dot (p2a_rlocal (p2a_flow_view (top,atlas) (real_interval[a,b]) g) U b
                           (U,phi) (b - r pow 2) y ** A)) /\
     (!r y. sl <= r /\ r <= sh /\ y IN K2
            ==> abs(p2a_llag (p2a_rlocal (p2a_flow_view (top,atlas) (real_interval[a,b]) g) U b
                                (U,phi)) b r y (vec 0)) <= Kp) /\
     (!r y A. sl <= r /\ r <= sh /\ y IN K2
              ==> norm(p2a_lacc (p2a_rlocal (p2a_flow_view (top,atlas) (real_interval[a,b]) g)
                                   U b (U,phi)) b r y A) <= Cacc * (&1 + norm A pow 2)) /\
     p2a_L_length (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b gamma tau +
       &2 * abs m * sqrt tau * tau <= Lup /\
     &0 < D0 /\ D0 <= &1 /\ &16 * (&4 * (abs Lup + Kp) / c + &1) * D0 < r0 pow 2
     ==> ?A. A continuous_on interval[lift(sqrt tau - D0),lift(sqrt tau)] /\
             (!s. sqrt tau - D0 < s /\ s < sqrt tau
                  ==> ((\v. phi(gamma(drop v pow 2))) has_vector_derivative A(lift s))
                        (at (lift s))) /\
             ((\v. phi(gamma(drop v pow 2))) has_vector_derivative A(lift(sqrt tau)))
               (at (lift(sqrt tau)) within interval[lift(sqrt tau - D0),lift(sqrt tau)]) /\
             (!s. sqrt tau - D0 <= s /\ s <= sqrt tau
                  ==> gamma(s pow 2) IN U /\ phi(gamma(s pow 2)) IN cball(phi(gamma tau),r0)) /\
             (!s. sqrt tau - D0 / &2 <= s /\ s <= sqrt tau
                  ==> norm(A(lift s)) <=
                      sqrt((&2 / c) * (Lup + Kp * (D0 / &2)) / (D0 / &2) + &1) +
                      Cacc * (D0 / &2 + (&2 / c) * (Lup + Kp * (D0 / &2))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2AW_FLOW_FACTS) THEN
  SUBGOAL_THEN `open_in top (U:A->bool) /\ open(IMAGE (phi:A->real^3) U)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[SMOOTH_MANIFOLD_ATLAS_CHART]; ALL_TAC] THEN
  SUBGOAL_THEN `p2a_region (p2a_flow_view (top,atlas) (real_interval[a,b])
                              (g:real->A->real^3^3)) U a b` ASSUME_TAC THENL
   [MATCH_MP_TAC P2AW_CBFLOW_REGION THEN ASM_REWRITE_TAC[REAL_LE_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN `p2a_adm (p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3))
                  b p tau gamma` ASSUME_TAC THENL [ASM_MESON_TAC[p2a_min]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < tau` ASSUME_TAC THENL
   [FIRST_ASSUM(ACCEPT_TAC o MATCH_MP SPDR13_ADM_POS); ALL_TAC] THEN
  SUBGOAL_THEN `sqrt tau pow 2 = tau /\ &0 < sqrt tau` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POW_2; SQRT_POS_LT; REAL_LT_IMP_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `sqrt tau < sqrt(b - a)` ASSUME_TAC THENL
   [MATCH_MP_TAC SQRT_MONO_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!s. &0 < s /\ s < sqrt(b - a) ==> a < b - s pow 2 /\ b - s pow 2 <= b`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `s pow 2 < sqrt(b - a) pow 2` MP_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[ARITH_EQ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `sqrt(b - a) pow 2 = b - a` SUBST1_TAC THENL
     [MATCH_MP_TAC SQRT_POW_2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPEC `s:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!tau'. &0 <= tau' /\ tau' <= tau
           ==> m <= mfd_scalar
                      (p2a_vatlas (p2a_flow_view (top,atlas) (real_interval[a,b])
                                     (g:real->A->real^3^3)) (b - tau'))
                      (p2a_vmetric (p2a_flow_view (top,atlas) (real_interval[a,b]) g) (b - tau'))
                      ((gamma:real->A) tau')`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P2AW_FLOW_SCAL_ALONG THEN EXISTS_TAC `p:A` THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  (* the exit argument *)
  SUBGOAL_THEN `cball((phi:A->real^3)((gamma:real->A) tau),r0) SUBSET IMAGE phi U` ASSUME_TAC THENL
   [ASM_MESON_TAC[SUBSET_TRANS]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!r y A. sl <= r /\ r <= sqrt tau /\ y IN cball((phi:A->real^3)((gamma:real->A) tau),r0)
            ==> c * norm(A:real^3) pow 2 <=
                A dot (p2a_rlocal (p2a_flow_view (top,atlas) (real_interval[a,b])
                                    (g:real->A->real^3^3)) U b (U,phi) (b - r pow 2) y ** A)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "dot")) (concl th) &&
      can (find_term ((=) `K2:real^3->bool`)) (concl th))) THEN
    REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!r y. sl <= r /\ r <= sqrt tau /\ y IN cball((phi:A->real^3)((gamma:real->A) tau),r0)
          ==> abs(p2a_llag (p2a_rlocal (p2a_flow_view (top,atlas) (real_interval[a,b])
                                         (g:real->A->real^3^3)) U b (U,phi)) b r y (vec 0))
              <= Kp`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_llag")) (concl th) &&
      can (find_term ((=) `K2:real^3->bool`)) (concl th))) THEN
    REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!r s. sl <= r /\ r <= s /\ s <= sqrt tau
          ==> real_integral (real_interval[r pow 2,s pow 2])
                (p2a_L_integrand (p2a_flow_view (top,atlas) (real_interval[a,b])
                                    (g:real->A->real^3^3)) b gamma tau) <= Lup`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `p2a_L_length (p2a_flow_view (top,atlas) (real_interval[a,b])
                                (g:real->A->real^3^3)) b gamma tau +
                &2 * abs m * sqrt tau * tau` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P2AW_PIECE_UPPER THEN EXISTS_TAC `p:A` THEN
    SUBGOAL_THEN `s pow 2 <= tau` ASSUME_TAC THENL
     [FIRST_ASSUM((fun th -> GEN_REWRITE_TAC (RAND_CONV) [GSYM th]) o
        check (fun th -> concl th = `sqrt tau pow 2 = tau`)) THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                 `g:real->A->real^3^3`; `p:A`; `tau:real`; `gamma:real->A`; `U:A->bool`;
                 `phi:A->real^3`; `(phi:A->real^3)((gamma:real->A) tau)`; `r0:real`; `sl:real`;
                 `c:real`; `Kp:real`; `Lup:real`; `D0:real`] P2AW_FLOW_EXIT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "EXIT") THEN
  (* the chart curve on the last D0 *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                 `g:real->A->real^3^3`; `p:A`; `tau:real`; `gamma:real->A`; `U:A->bool`;
                 `phi:A->real^3`; `sqrt tau - D0`] P2AW_FLOW_MIN_CHART) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
      X_GEN_TAC `s:real` THEN STRIP_TAC THEN USE_THEN "EXIT" (MP_TAC o SPEC `s:real`) THEN
      ASM_SIMP_TAC[]];
    DISCH_THEN(X_CHOOSE_THEN `A:real^1->real^3` STRIP_ASSUME_TAC)] THEN
  EXISTS_TAC `A:real^1->real^3` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!s. sqrt tau - D0 <= s /\ s <= sqrt tau
        ==> (gamma:real->A)(s pow 2) IN U /\
            (phi:A->real^3)(gamma(s pow 2)) IN cball(phi(gamma tau),r0)`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN USE_THEN "EXIT" (MP_TAC o SPEC `s:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    ASM_REWRITE_TAC[IN_CBALL] THEN
    ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REAL_ARITH_TAC;
    ASM_REWRITE_TAC[]] THEN
  (* the velocity bound on the last D0 / 2 *)
  ABBREV_TAC `p1 = sqrt tau - D0 / &2` THEN
  SUBGOAL_THEN `sqrt tau - D0 < p1 /\ p1 < sqrt tau /\ sl < p1 /\ &0 < p1 /\
                sqrt tau - p1 = D0 / &2`
  STRIP_ASSUME_TAC THENL [EXPAND_TAC "p1" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `p2a_lsmooth (IMAGE (phi:A->real^3) U) (&0) (sqrt(b - a))
      (\s. p2a_rlocal (p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3))
                      U b (U,phi) (b - s pow 2))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3)`;
                   `U:A->bool`; `a:real`; `b:real`; `U:A->bool`; `phi:A->real^3`; `b:real`;
                   `&0`; `sqrt(b - a)`] P2A_REGION_SFAMILY) THEN
    ASM_REWRITE_TAC[INTER_IDEMPOT] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `lrg_lsmooth (IMAGE (phi:A->real^3) U) a b
      (p2a_rlocal (p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3))
                  U b (U,phi))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3)`;
                   `U:A->bool`; `a:real`; `b:real`; `U:A->bool`; `phi:A->real^3`]
                  P2A_REGION_LRICCI) THEN
    ASM_REWRITE_TAC[INTER_IDEMPOT; lrg_lsmooth; p2a_lsmooth] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\v:real^1. (phi:A->real^3)((gamma:real->A)(drop v pow 2))) continuous_on
                interval[lift p1,lift(sqrt tau)]` ASSUME_TAC THENL
   [MATCH_MP_TAC P2AW_CHART_CURVE_CONT THEN
    MAP_EVERY EXISTS_TAC [`A:real^1->real^3`; `sqrt tau - D0`] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(A:real^1->real^3) continuous_on interval[lift p1,lift(sqrt tau)]` ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `interval[lift(sqrt tau - D0),lift(sqrt tau)]` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET_INTERVAL_1; LIFT_DROP] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the energy on the last D0 / 2 *)
  SUBGOAL_THEN
   `real_integral (real_interval[p1,sqrt tau]) (\s. norm((A:real^1->real^3)(lift s)) pow 2) <=
    (&2 / c) * (Lup + Kp * (D0 / &2))`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `(\s. p2a_llag (p2a_rlocal (p2a_flow_view (top,atlas) (real_interval[a,b])
                                   (g:real->A->real^3^3)) U b (U,phi)) b s
                    ((phi:A->real^3)((gamma:real->A)(s pow 2))) ((A:real^1->real^3)(lift s)))
      real_integrable_on real_interval[p1,sqrt tau]`
    ASSUME_TAC THENL
     [REWRITE_TAC[P2AW_LLAG_LAGF] THEN
      MP_TAC(ISPECL [`IMAGE (phi:A->real^3) U`; `a:real`; `b:real`;
                     `p2a_rlocal (p2a_flow_view (top,atlas) (real_interval[a,b])
                                    (g:real->A->real^3^3)) U b (U,phi)`; `b:real`;
                     `\v:real^1. pastecart (pastecart (lift(b - drop v pow 2))
                                             ((phi:A->real^3)((gamma:real->A)(drop v pow 2))))
                                           ((A:real^1->real^3) v)`;
                     `p1:real`; `sqrt tau`] P2AW_LAGF_PATH_INTEGRABLE) THEN
      REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN ASM_REWRITE_TAC[ETA_AX] THEN
        MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[LIFT_SUB] THEN MATCH_MP_TAC CONTINUOUS_ON_SUB THEN
        REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
        MATCH_MP_TAC CONTINUOUS_ON_LIFT_POW THEN REWRITE_TAC[LIFT_DROP; CONTINUOUS_ON_ID];
        X_GEN_TAC `s:real` THEN STRIP_TAC THEN
        REWRITE_TAC[PASTECART_IN_PCROSS; IN_UNIV; IN_INTERVAL_1; LIFT_DROP] THEN
        SUBGOAL_THEN `a < b - s pow 2 /\ b - s pow 2 <= b` STRIP_ASSUME_TAC THENL
         [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        SUBGOAL_THEN `&0 < s pow 2` ASSUME_TAC THENL
         [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        SUBGOAL_THEN `(phi:A->real^3)((gamma:real->A)(s pow 2)) IN
                      cball(phi(gamma tau),r0)` MP_TAC THENL
         [FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall(concl th) &&
            can (find_term (fun t -> is_const t && fst(dest_const t) = "cball")) (concl th) &&
            can (find_term ((=) `U:A->bool`)) (concl th) &&
            not (can (find_term (fun t -> is_const t && fst(dest_const t) = "dot")) (concl th)) &&
            not (can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_llag"))
                   (concl th)))) THEN
          ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
          ASM SET_TAC[]]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`p2a_rlocal (p2a_flow_view (top,atlas) (real_interval[a,b])
                                  (g:real->A->real^3^3)) U b (U,phi)`; `b:real`;
                   `\v:real^1. (phi:A->real^3)((gamma:real->A)(drop v pow 2))`;
                   `A:real^1->real^3`; `p1:real`; `sqrt tau`; `c:real`; `Kp:real`]
                  P2AW_ENERGY_BOUND) THEN
    REWRITE_TAC[LIFT_DROP] THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN
      SUBGOAL_THEN `(phi:A->real^3)((gamma:real->A)(s pow 2)) IN
                    cball(phi(gamma tau),r0)` ASSUME_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall(concl th) &&
          can (find_term (fun t -> is_const t && fst(dest_const t) = "cball")) (concl th) &&
          can (find_term ((=) `U:A->bool`)) (concl th) &&
          not (can (find_term (fun t -> is_const t && fst(dest_const t) = "dot")) (concl th)) &&
          not (can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_llag"))
                 (concl th)))) THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
        ALL_TAC] THEN
      CONJ_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
          can (find_term (fun t -> is_const t && fst(dest_const t) = "dot")) (concl th) &&
          can (find_term (fun t -> is_const t && fst(dest_const t) = "cball")) (concl th))) THEN
        ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC(REAL_ARITH `abs x <= k ==> --k <= x`) THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
          can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_llag")) (concl th) &&
          can (find_term (fun t -> is_const t && fst(dest_const t) = "cball")) (concl th))) THEN
        ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    MATCH_MP_TAC(MESON[REAL_LE_LMUL; REAL_LE_TRANS]
      `!k x y e:real. &0 <= k /\ x <= y ==> e <= k * x ==> e <= k * y`) THEN
    CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `x <= l ==> x + k * d <= l + k * d`) THEN
    (* the s-form length of the last piece *)
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                   `g:real->A->real^3^3`; `p:A`; `tau:real`; `gamma:real->A`; `U:A->bool`;
                   `phi:A->real^3`; `sqrt tau - D0`; `p1:real`; `A:real^1->real^3`]
                  P2AW_FLOW_CUT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      X_GEN_TAC `s:real` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "cball")) (concl th) &&
        can (find_term ((=) `U:A->bool`)) (concl th) &&
        not (can (find_term (fun t -> is_const t && fst(dest_const t) = "dot")) (concl th)) &&
        not (can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_llag"))
               (concl th)))) THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `p2a_cL (p2a_rlocal (p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3))
                         U b (U,phi)) b
             (\v. (phi:A->real^3)((gamma:real->A)(drop v pow 2))) p1 (sqrt tau) =
      real_integral (real_interval[p1,sqrt tau])
        (\s. p2a_llag (p2a_rlocal (p2a_flow_view (top,atlas) (real_interval[a,b]) g) U b
                                  (U,phi)) b s (phi(gamma(s pow 2))) (A(lift s)))`
    SUBST1_TAC THENL
     [REWRITE_TAC[p2a_cL; LIFT_DROP] THEN
      MATCH_MP_TAC(MESON[P2A_REAL_INTEGRAL_OPEN_EQ]
       `!f g:real->real a c. (!t. a < t /\ t < c ==> f t = g t)
                            ==> real_integral (real_interval[a,c]) f =
                                real_integral (real_interval[a,c]) g`) THEN
      X_GEN_TAC `s:real` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
      AP_TERM_TAC THEN MATCH_MP_TAC VECTOR_DERIVATIVE_AT THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "has_vector_derivative"))
            (concl th) &&
        not (can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_lacc")) (concl th)))) THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_TAC THEN
    MP_TAC(ISPECL [`p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3)`;
                   `m:real`; `b:real`; `p:A`; `gamma:real->A`; `p1 pow 2`] P2AW_ADM_LOWER) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC P2AW_FLOW_SCAL_ALONG THEN EXISTS_TAC `p:A` THEN ASM_REWRITE_TAC[] THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC P2A_ADM_RESTRICT THEN EXISTS_TAC `tau:real` THEN ASM_REWRITE_TAC[];
          ALL_TAC];
        MATCH_MP_TAC P2A_ADM_RESTRICT THEN EXISTS_TAC `tau:real` THEN ASM_REWRITE_TAC[]] THEN
      (SUBGOAL_THEN `&0 < p1 pow 2 /\ p1 pow 2 <= tau` MP_TAC THENL
        [CONJ_TAC THENL [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
         FIRST_ASSUM((fun th -> GEN_REWRITE_TAC (RAND_CONV) [GSYM th]) o
           check (fun th -> concl th = `sqrt tau pow 2 = tau`)) THEN
         MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
         ASM_REAL_ARITH_TAC]);
      ALL_TAC] THEN
    SUBGOAL_THEN `abs m * sqrt(p1 pow 2) * p1 pow 2 <= abs m * sqrt tau * tau` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
      SUBGOAL_THEN `sqrt(p1 pow 2) = p1` SUBST1_TAC THENL
       [MATCH_MP_TAC POW_2_SQRT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC;
        FIRST_ASSUM((fun th -> GEN_REWRITE_TAC (RAND_CONV) [GSYM th]) o
          check (fun th -> concl th = `sqrt tau pow 2 = tau`)) THEN
        MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= abs m * sqrt tau * tau` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[SQRT_POS_LE; REAL_LT_IMP_LE];
      ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the velocity bound *)
  MP_TAC(ISPECL [`IMAGE (phi:A->real^3) U`; `&0`; `sqrt(b - a)`;
                 `p2a_rlocal (p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3))
                             U b (U,phi)`; `b:real`; `p1:real`; `sqrt tau`; `K2:real^3->bool`;
                 `\v:real^1. (phi:A->real^3)((gamma:real->A)(drop v pow 2))`;
                 `A:real^1->real^3`; `Cacc:real`; `(&2 / c) * (Lup + Kp * (D0 / &2))`]
                P2AW_VEL_BOUND) THEN
  ASM_REWRITE_TAC[LIFT_DROP] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "cball")) (concl th) &&
        can (find_term ((=) `U:A->bool`)) (concl th) &&
        not (can (find_term (fun t -> is_const t && fst(dest_const t) = "dot")) (concl th)) &&
        not (can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_llag"))
               (concl th)))) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM SET_TAC[]];
      X_GEN_TAC `s:real` THEN STRIP_TAC THEN CONJ_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
          can (find_term (fun t -> is_const t && fst(dest_const t) = "has_vector_derivative"))
              (concl th) &&
          not (can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_lacc")) (concl th)))) THEN
        ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC P2AW_VDERIV_INTERIOR THEN
        MAP_EVERY EXISTS_TAC [`sqrt tau - D0`; `sqrt tau`] THEN
        CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall(concl th) &&
          can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_lacc")) (concl th) &&
          can (find_term (fun t -> is_const t && fst(dest_const t) = "has_vector_derivative"))
              (concl th))) THEN
        REWRITE_TAC[INTER_IDEMPOT] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
      REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_lacc")) (concl th) &&
        can (find_term ((=) `K2:real^3->bool`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s:real`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REWRITE_TAC[real_div; REAL_MUL_ASSOC]]);;

(* ------------------------------------------------------------------------- *)
(* The barrier at one point.  For a minimizer gamma to (q, tau) with the     *)
(* uniform end data of P2AW_FLOW_END_UNIF, and the bounds of the combined    *)
(* and spatial families (the conclusions of P2AW_CFAM_BOUND and              *)
(* P2AW_SFAM_BOUNDS for the compact set K0 and the velocity bound M), the    *)
(* reduced length satisfies the one-sided first order bound and the second   *)
(* difference bound at (q, tau).                                             *)
(* ------------------------------------------------------------------------- *)

let P2AW_FLOW_PT_BARRIER = prove
 (`!top atlas a b (g:real->A->real^3^3) m p tau (gamma:real->A) U (phi:A->real^3)
    K2 r0 sl sh c Kp Cacc Lup D0 K0 M d1 C1 d2 C2.
     p2a_cbflow (top,atlas) a b g /\ p IN topspace top /\ (U,phi) IN atlas /\
     (!t y. a <= t /\ t <= b /\ y IN topspace top ==> m <= mfd_scalar atlas (g t) y) /\
     p2a_min (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p tau gamma /\
     tau < b - a /\ gamma tau IN U /\
     compact K2 /\ K2 SUBSET IMAGE phi U /\ &0 < r0 /\ cball(phi(gamma tau),r0) SUBSET K2 /\
     &0 < sl /\ sl + D0 <= sqrt tau /\ sqrt tau <= sh /\ &0 < c /\ &0 <= Kp /\ &0 < Cacc /\
     (!r y A. sl <= r /\ r <= sh /\ y IN K2
              ==> c * norm A pow 2 <=
                  A dot (p2a_rlocal (p2a_flow_view (top,atlas) (real_interval[a,b]) g) U b
                           (U,phi) (b - r pow 2) y ** A)) /\
     (!r y. sl <= r /\ r <= sh /\ y IN K2
            ==> abs(p2a_llag (p2a_rlocal (p2a_flow_view (top,atlas) (real_interval[a,b]) g) U b
                                (U,phi)) b r y (vec 0)) <= Kp) /\
     (!r y A. sl <= r /\ r <= sh /\ y IN K2
              ==> norm(p2a_lacc (p2a_rlocal (p2a_flow_view (top,atlas) (real_interval[a,b]) g)
                                   U b (U,phi)) b r y A) <= Cacc * (&1 + norm A pow 2)) /\
     p2a_L_length (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b gamma tau +
       &2 * abs m * sqrt tau * tau <= Lup /\
     &0 < D0 /\ D0 <= &1 /\ &16 * (&4 * (abs Lup + Kp) / c + &1) * D0 < r0 pow 2 /\
     (!s y. sl <= s /\ s <= sh /\ y IN K2 ==> pastecart (lift(b - s pow 2)) y IN K0) /\
     sqrt((&2 / c) * (Lup + Kp * (D0 / &2)) / (D0 / &2) + &1) +
     Cacc * (D0 / &2 + (&2 / c) * (Lup + Kp * (D0 / &2))) <= M /\
     (!(y:real^1->real^3) A s1 sb w k.
        &0 <= s1 /\ s1 + D0 / &2 <= sb /\ sb <= sh /\
        (!s. s1 <= s /\ s <= sb
             ==> pastecart (lift(b - s pow 2)) (y(lift s)) IN K0 /\
                 norm(A(lift s)) <= M /\
                 (y has_vector_derivative A(lift s)) (at (lift s))) /\
        A continuous_on interval[lift s1,lift sb] /\
        abs(k - &1) <= d1 /\ norm w <= d1
        ==> (!s. s1 <= s /\ s <= sb
                 ==> pastecart (lift(b - (s1 + k * (s - s1)) pow 2))
                               (y(lift s) + ((s - s1) / (sb - s1)) % w)
                     IN interval(lift a,lift b) PCROSS IMAGE phi U) /\
            abs(p2a_cL (p2a_rlocal (p2a_flow_view (top,atlas) (real_interval[a,b]) g) U b
                                   (U,phi)) b (p2aw_cfam y s1 sb w k) s1 (s1 + k * (sb - s1)) -
                p2a_cL (p2a_rlocal (p2a_flow_view (top,atlas) (real_interval[a,b]) g) U b
                                   (U,phi)) b y s1 sb) <= C1 * (abs(k - &1) + norm w)) /\
     (!(y:real^1->real^3) A s1 sb w.
        s1 < sb /\
        (!s. s1 <= s /\ s <= sb
             ==> pastecart (lift(b - s pow 2)) (y(lift s)) IN K0 /\
                 norm(A(lift s)) <= M /\
                 (y has_vector_derivative A(lift s)) (at (lift s))) /\
        A continuous_on interval[lift s1,lift sb] /\
        (&1 + inv(sb - s1)) * norm w <= d2
        ==> (!s. s1 <= s /\ s <= sb
                 ==> pastecart (lift(b - s pow 2)) (y(lift s) + ((s - s1) / (sb - s1)) % w)
                     IN interval(lift a,lift b) PCROSS IMAGE phi U) /\
            p2a_cL (p2a_rlocal (p2a_flow_view (top,atlas) (real_interval[a,b]) g) U b (U,phi)) b
                   (p2aw_sfam y s1 sb w) s1 sb +
            p2a_cL (p2a_rlocal (p2a_flow_view (top,atlas) (real_interval[a,b]) g) U b (U,phi)) b
                   (p2aw_sfam y s1 sb (--w)) s1 sb -
            &2 * p2a_cL (p2a_rlocal (p2a_flow_view (top,atlas) (real_interval[a,b]) g) U b
                                    (U,phi)) b y s1 sb
            <= C2 * (sb - s1 + &1) pow 2 / (sb - s1) * norm w pow 2)
     ==> (!w k. &0 < k /\ abs(k - &1) <= d1 /\ norm w <= d1 /\
                (sqrt tau - D0 / &2 + k * (D0 / &2)) pow 2 < b - a
                ==> p2a_Lx (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p
                           ((sqrt tau - D0 / &2 + k * (D0 / &2)) pow 2)
                           (chart_inv (U,phi) (phi(gamma tau) + w)) <=
                    p2a_Lx (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p tau
                           (gamma tau) + C1 * (abs(k - &1) + norm w)) /\
         (!w. (&1 + inv(D0 / &2)) * norm w <= d2
              ==> p2a_Lx (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p tau
                         (chart_inv (U,phi) (phi(gamma tau) + w)) +
                  p2a_Lx (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p tau
                         (chart_inv (U,phi) (phi(gamma tau) - w)) -
                  &2 * p2a_Lx (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p tau
                              (gamma tau)
                  <= C2 * (D0 / &2 + &1) pow 2 / (D0 / &2) * norm w pow 2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                 `g:real->A->real^3^3`; `m:real`; `p:A`; `tau:real`; `gamma:real->A`;
                 `U:A->bool`; `phi:A->real^3`; `K2:real^3->bool`; `r0:real`; `sl:real`;
                 `sh:real`; `c:real`; `Kp:real`; `Cacc:real`; `Lup:real`; `D0:real`]
                P2AW_FLOW_END_UNIF) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `A:real^1->real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `&0 < tau` ASSUME_TAC THENL
   [FIRST_ASSUM(ACCEPT_TAC o MATCH_MP SPDR13_MIN_POS); ALL_TAC] THEN
  SUBGOAL_THEN `sqrt tau pow 2 = tau /\ &0 < sqrt tau` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POW_2; SQRT_POS_LT; REAL_LT_IMP_LE]; ALL_TAC] THEN
  ABBREV_TAC `s1 = sqrt tau - D0 / &2` THEN
  SUBGOAL_THEN `sqrt tau - D0 < s1 /\ s1 < sqrt tau /\ sl < s1 /\ &0 < s1`
  STRIP_ASSUME_TAC THENL [EXPAND_TAC "s1" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `D0 / &2 = sqrt tau - s1` SUBST1_TAC THENL
   [EXPAND_TAC "s1" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt tau - D0` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!s. sqrt tau - D0 <= s /\ s <= sqrt tau ==> (gamma:real->A)(s pow 2) IN U`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "cball")) (concl th) &&
      can (find_term ((=) `U:A->bool`)) (concl th) &&
      not (can (find_term (fun t -> is_const t && fst(dest_const t) = "dot")) (concl th)) &&
      not (can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_llag"))
             (concl th)))) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\v:real^1. (phi:A->real^3)((gamma:real->A)(drop v pow 2))`;
                 `A:real^1->real^3`; `sqrt tau - D0`; `sqrt tau`] P2AW_C1_EXTEND) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    DISCH_THEN(STRIP_ASSUME_TAC o REWRITE_RULE[LIFT_DROP])] THEN
  (* the extended curve satisfies the hypotheses of the family bounds *)
  SUBGOAL_THEN
   `!s. s1 <= s /\ s <= sqrt tau
        ==> pastecart (lift(b - s pow 2))
              (p2aw_rext (\v:real^1. (phi:A->real^3)((gamma:real->A)(drop v pow 2))) A
                         (sqrt tau) (lift s)) IN K0 /\
            norm(p2aw_dext (A:real^1->real^3) (sqrt tau) (lift s)) <= M /\
            (p2aw_rext (\v:real^1. phi(gamma(drop v pow 2))) A (sqrt tau)
             has_vector_derivative p2aw_dext A (sqrt tau) (lift s)) (at (lift s))`
  (LABEL_TAC "YH") THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `p2aw_rext (\v:real^1. (phi:A->real^3)((gamma:real->A)(drop v pow 2)))
                    (A:real^1->real^3) (sqrt tau) (lift s) = phi(gamma(s pow 2)) /\
                  p2aw_dext A (sqrt tau) (lift s) = A(lift s)`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "=")) (concl th) &&
        not (can (find_term (fun t -> is_const t && fst(dest_const t) = "has_vector_derivative"))
               (concl th)) &&
        (can (find_term (fun t -> is_const t && fst(dest_const t) = "p2aw_rext")) (concl th) ||
         can (find_term (fun t -> is_const t && fst(dest_const t) = "p2aw_dext")) (concl th)))) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `K0:real^(1,3)finite_sum->bool`)) (concl th) &&
        not (can (find_term (fun t -> is_const t && fst(dest_const t) = "p2aw_cfam")) (concl th)) &&
        not (can (find_term (fun t -> is_const t && fst(dest_const t) = "p2aw_sfam")) (concl th)))) THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "cball")) (concl th) &&
        can (find_term ((=) `U:A->bool`)) (concl th) &&
        not (can (find_term (fun t -> is_const t && fst(dest_const t) = "dot")) (concl th)) &&
        not (can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_llag"))
               (concl th)))) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM SET_TAC[]];
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `sqrt((&2 / c) * (Lup + Kp * (D0 / &2)) / (D0 / &2) + &1) +
                  Cacc * (D0 / &2 + (&2 / c) * (Lup + Kp * (D0 / &2)))` THEN
      ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "sqrt")) (concl th) &&
        can (find_term ((=) `Cacc:real`)) (concl th) &&
        not (can (find_term ((=) `M:real`)) (concl th)))) THEN
      ASM_REAL_ARITH_TAC;
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "has_vector_derivative"))
            (concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "p2aw_rext")) (concl th))) THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `p2aw_dext (A:real^1->real^3) (sqrt tau) continuous_on
                interval[lift s1,lift(sqrt tau)]` ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN
    REWRITE_TAC[FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP] THEN X_GEN_TAC `s:real` THEN
    STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "continuous")) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "p2aw_dext")) (concl th))) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the length at the point *)
  SUBGOAL_THEN
   `p2a_Lx (p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3)) b p tau
           ((gamma:real->A) tau) =
    p2a_L_length (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b gamma (s1 pow 2) +
    p2a_cL (p2a_rlocal (p2a_flow_view (top,atlas) (real_interval[a,b]) g) U b (U,phi)) b
           (p2aw_rext (\v:real^1. (phi:A->real^3)(gamma(drop v pow 2))) A (sqrt tau))
           s1 (sqrt tau)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3)`;
                   `b:real`; `p:A`; `tau:real`; `gamma:real->A`] P2A_MIN_LX) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MP_TAC(ISPECL [`p2a_rlocal (p2a_flow_view (top,atlas) (real_interval[a,b])
                                  (g:real->A->real^3^3)) U b (U,phi:A->real^3)`; `b:real`;
                   `\v:real^1. (phi:A->real^3)((gamma:real->A)(drop v pow 2))`;
                   `A:real^1->real^3`; `sqrt tau - D0`; `s1:real`; `sqrt tau`] P2AW_REXT_CL) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    MATCH_MP_TAC P2AW_FLOW_CUT THEN
    MAP_EVERY EXISTS_TAC [`p:A`; `sqrt tau - D0`; `A:real^1->real^3`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [(* first order *)
    MAP_EVERY X_GEN_TAC [`w:real^3`; `k:real`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL
     [`p2aw_rext (\v:real^1. (phi:A->real^3)((gamma:real->A)(drop v pow 2))) A (sqrt tau)`;
      `p2aw_dext (A:real^1->real^3) (sqrt tau)`; `s1:real`; `sqrt tau`; `w:real^3`; `k:real`] o
      check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "p2aw_cfam")) (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                   `g:real->A->real^3^3`; `m:real`; `p:A`; `tau:real`; `gamma:real->A`;
                   `U:A->bool`; `phi:A->real^3`; `sqrt tau - D0`; `s1:real`; `A:real^1->real^3`;
                   `w:real^3`; `k:real`] P2AW_FLOW_CMP) THEN
    SUBGOAL_THEN
     `!s. s1 <= s /\ s <= sqrt tau
          ==> p2aw_rext (\v:real^1. (phi:A->real^3)((gamma:real->A)(drop v pow 2))) A
                        (sqrt tau) (lift s) + ((s - s1) / (sqrt tau - s1)) % w IN IMAGE phi U`
    ASSUME_TAC THENL
     [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "PCROSS")) (concl th) &&
        can (find_term ((=) `k:real`)) (concl th))) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[PASTECART_IN_PCROSS]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                   `g:real->A->real^3^3`; `m:real`; `p:A`; `tau:real`; `gamma:real->A`;
                   `U:A->bool`; `phi:A->real^3`; `sqrt tau - D0`; `s1:real`; `A:real^1->real^3`;
                   `w:real^3`; `k:real`] P2AW_FLOW_CMP) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* second differences *)
  X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(&1 + inv(sqrt tau - s1)) * norm(--(w:real^3)) <= d2` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_NEG]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPECL
   [`p2aw_rext (\v:real^1. (phi:A->real^3)((gamma:real->A)(drop v pow 2))) A (sqrt tau)`;
    `p2aw_dext (A:real^1->real^3) (sqrt tau)`; `s1:real`; `sqrt tau`; `--w:real^3`] o
    check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "p2aw_sfam")) (concl th))) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[]; DISCH_THEN(ASSUME_TAC o CONJUNCT1)] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`p2aw_rext (\v:real^1. (phi:A->real^3)((gamma:real->A)(drop v pow 2))) A (sqrt tau)`;
    `p2aw_dext (A:real^1->real^3) (sqrt tau)`; `s1:real`; `sqrt tau`; `w:real^3`] o
    check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "p2aw_sfam")) (concl th))) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN
   `!v:real^3.
      (!s. s1 <= s /\ s <= sqrt tau
           ==> pastecart (lift(b - s pow 2))
                 (p2aw_rext (\v:real^1. (phi:A->real^3)((gamma:real->A)(drop v pow 2))) A
                            (sqrt tau) (lift s) + ((s - s1) / (sqrt tau - s1)) % v)
               IN interval(lift a,lift b) PCROSS IMAGE phi U)
      ==> p2a_Lx (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p tau
                 (chart_inv (U,phi) (phi(gamma tau) + v)) <=
          p2a_L_length (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b gamma (s1 pow 2) +
          p2a_cL (p2a_rlocal (p2a_flow_view (top,atlas) (real_interval[a,b]) g) U b (U,phi)) b
                 (p2aw_sfam (p2aw_rext (\v:real^1. phi(gamma(drop v pow 2))) A (sqrt tau))
                            s1 (sqrt tau) v) s1 (sqrt tau)`
  (LABEL_TAC "CMP1") THENL
   [X_GEN_TAC `v:real^3` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                   `g:real->A->real^3^3`; `m:real`; `p:A`; `tau:real`; `gamma:real->A`;
                   `U:A->bool`; `phi:A->real^3`; `sqrt tau - D0`; `s1:real`; `A:real^1->real^3`;
                   `v:real^3`; `&1`] P2AW_FLOW_CMP) THEN
    REWRITE_TAC[REAL_LT_01; REAL_MUL_LID; REAL_SUB_ADD2; P2AW_CFAM_ONE] THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `s:real`) THEN
    ASM_REWRITE_TAC[PASTECART_IN_PCROSS] THEN SIMP_TAC[];
    ALL_TAC] THEN
  USE_THEN "CMP1" (MP_TAC o SPEC `w:real^3`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  USE_THEN "CMP1" (MP_TAC o SPEC `--w:real^3`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[GSYM VECTOR_SUB] THEN DISCH_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Arithmetic for the barrier on compact sets: square roots are Lipschitz    *)
(* away from 0, the reparametrization factor k for a time change h, and the  *)
(* time range of a compact subset of the chart domain.                       *)
(* ------------------------------------------------------------------------- *)

let P2AW_SQRT_DIFF_LE = prove
 (`!x y t. &0 < t /\ t <= x /\ &0 <= y ==> abs(sqrt y - sqrt x) <= abs(y - x) / sqrt t`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < sqrt t /\ sqrt t <= sqrt x /\ &0 <= sqrt y /\
                sqrt x pow 2 = x /\ sqrt y pow 2 = y` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LT; SQRT_MONO_LE; SQRT_POS_LE; SQRT_POW_2] THEN
    MATCH_MP_TAC SQRT_POW_2 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
  SUBGOAL_THEN `y - x = (sqrt y - sqrt x) * (sqrt y + sqrt x)` SUBST1_TAC THENL
   [UNDISCH_TAC `sqrt x pow 2 = x` THEN UNDISCH_TAC `sqrt y pow 2 = y` THEN
    CONV_TAC REAL_RING;
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ABS_MUL] THEN
  SUBGOAL_THEN `abs(sqrt y + sqrt x) = sqrt y + sqrt x` SUBST1_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN ASM_REAL_ARITH_TAC);;

let P2AW_K_ARITH = prove
 (`!tau h D0 t1.
     &0 < t1 /\ t1 <= tau /\ &0 < D0 /\ &0 <= tau + h
     ==> sqrt tau - D0 / &2 + (&1 + (sqrt(tau + h) - sqrt tau) / (D0 / &2)) * (D0 / &2) =
         sqrt(tau + h) /\
         abs((&1 + (sqrt(tau + h) - sqrt tau) / (D0 / &2)) - &1) <=
         (&2 / (D0 * sqrt t1)) * abs h`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < D0 / &2 /\ &0 < sqrt t1` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LT] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[REAL_ADD_RDISTRIB; REAL_MUL_LID] THEN
    ASM_SIMP_TAC[REAL_DIV_RMUL; REAL_LT_IMP_NZ] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ADD_SUB] THEN
  SUBGOAL_THEN `abs((sqrt(tau + h) - sqrt tau) / (D0 / &2)) =
                abs(sqrt(tau + h) - sqrt tau) / (D0 / &2)` SUBST1_TAC THENL
   [REWRITE_TAC[REAL_ABS_DIV] THEN AP_TERM_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
  SUBGOAL_THEN `(&2 / (D0 * sqrt t1) * abs h) * (D0 / &2) = abs h / sqrt t1` SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < D0 / &2` THEN UNDISCH_TAC `&0 < sqrt t1` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`tau:real`; `tau + h`; `t1:real`] P2AW_SQRT_DIFF_LE) THEN
  ASM_REWRITE_TAC[REAL_ADD_SUB]);;

let P2AW_KK_TAU_BOUNDS = prove
 (`!(c:(A->bool)#(A->real^N)) tmax kk.
     &0 < tmax /\ compact kk /\ kk SUBSET p2bw_cdom c tmax
     ==> ?tau1 tau2. &0 < tau1 /\ tau1 <= tau2 /\ tau2 < tmax /\
                     !z. z IN kk ==> tau1 <= drop(sndcart z) /\ drop(sndcart z) <= tau2`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `kk:real^(N,1)finite_sum->bool = {}` THENL
   [MAP_EVERY EXISTS_TAC [`tmax / &2`; `tmax / &2`] THEN ASM_REWRITE_TAC[NOT_IN_EMPTY] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(lift o (\z:real^(N,1)finite_sum. drop(sndcart z))) continuous_on kk`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `lift o (\z:real^(N,1)finite_sum. drop(sndcart z)) = sndcart` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_DROP]; ALL_TAC] THEN
    MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN REWRITE_TAC[LINEAR_SNDCART];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\z:real^(N,1)finite_sum. drop(sndcart z)`; `kk:real^(N,1)finite_sum->bool`]
                CONTINUOUS_ATTAINS_INF) THEN
  MP_TAC(ISPECL [`\z:real^(N,1)finite_sum. drop(sndcart z)`; `kk:real^(N,1)finite_sum->bool`]
                CONTINUOUS_ATTAINS_SUP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `z2:real^(N,1)finite_sum` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `z1:real^(N,1)finite_sum` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`drop(sndcart(z1:real^(N,1)finite_sum))`;
                        `drop(sndcart(z2:real^(N,1)finite_sum))`] THEN
  SUBGOAL_THEN `(z1:real^(N,1)finite_sum) IN p2bw_cdom (c:(A->bool)#(A->real^N)) tmax /\
                (z2:real^(N,1)finite_sum) IN p2bw_cdom c tmax` MP_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[p2bw_cdom; IN_ELIM_THM] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The barrier on a compact subset kk of the chart domain, uniformly: if     *)
(* every point of kk is reached by a minimizer and the reduced length is     *)
(* bounded above on kk, then near every point of kk the reduced length is    *)
(* bounded by its value plus C (|dx| + |dtau|), and its spatial second       *)
(* differences are bounded by C |dx|^2.                                      *)
(* ------------------------------------------------------------------------- *)

let P2AW_FLOW_KK_BARRIER = prove
 (`!top atlas a b (g:real->A->real^3^3) m p U (phi:A->real^3) kk Lmax.
     p2a_cbflow (top,atlas) a b g /\ p IN topspace top /\ (U,phi) IN atlas /\
     (!t y. a <= t /\ t <= b /\ y IN topspace top ==> m <= mfd_scalar atlas (g t) y) /\
     compact kk /\ kk SUBSET p2bw_cdom (U,phi) (b - a) /\
     (!z. z IN kk
          ==> ?gamma. p2a_min (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p
                              (drop(sndcart z)) gamma /\
                      gamma(drop(sndcart z)) = chart_inv (U,phi) (fstcart z)) /\
     (!z. z IN kk
          ==> p2a_Lx (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p (drop(sndcart z))
                     (chart_inv (U,phi) (fstcart z)) <= Lmax)
     ==> ?d C. &0 < d /\ &0 <= C /\
           !z. z IN kk
               ==> (!w h. norm w <= d /\ abs h <= d
                          ==> pastecart (fstcart z + w) (sndcart z + lift h)
                                IN p2bw_cdom (U,phi) (b - a) /\
                              p2a_Lx (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p
                                     (drop(sndcart z) + h) (chart_inv (U,phi) (fstcart z + w)) <=
                              p2a_Lx (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p
                                     (drop(sndcart z)) (chart_inv (U,phi) (fstcart z)) +
                              C * (norm w + abs h)) /\
                   (!w. norm w <= d
                        ==> p2a_Lx (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p
                                   (drop(sndcart z)) (chart_inv (U,phi) (fstcart z + w)) +
                            p2a_Lx (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p
                                   (drop(sndcart z)) (chart_inv (U,phi) (fstcart z - w)) -
                            &2 * p2a_Lx (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p
                                        (drop(sndcart z)) (chart_inv (U,phi) (fstcart z))
                            <= C * norm w pow 2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2AW_FLOW_FACTS) THEN
  SUBGOAL_THEN `open_in top (U:A->bool) /\ open(IMAGE (phi:A->real^3) U)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[SMOOTH_MANIFOLD_ATLAS_CHART]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `U:A->bool`;
                 `phi:A->real^3`] CHART_INV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `p2a_region (p2a_flow_view (top,atlas) (real_interval[a,b])
                              (g:real->A->real^3^3)) U a b` ASSUME_TAC THENL
   [MATCH_MP_TAC P2AW_CBFLOW_REGION THEN ASM_REWRITE_TAC[REAL_LE_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN `!s. &0 < s /\ s < sqrt(b - a) ==> a < b - s pow 2 /\ b - s pow 2 <= b`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `s pow 2 < sqrt(b - a) pow 2` MP_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[ARITH_EQ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `sqrt(b - a) pow 2 = b - a` SUBST1_TAC THENL
     [MATCH_MP_TAC SQRT_POW_2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPEC `s:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `p2a_lsmooth (IMAGE (phi:A->real^3) U) (&0) (sqrt(b - a))
      (\s. p2a_rlocal (p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3))
                      U b (U,phi) (b - s pow 2))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3)`;
                   `U:A->bool`; `a:real`; `b:real`; `U:A->bool`; `phi:A->real^3`; `b:real`;
                   `&0`; `sqrt(b - a)`] P2A_REGION_SFAMILY) THEN
    ASM_REWRITE_TAC[INTER_IDEMPOT] THEN DISCH_THEN MATCH_MP_TAC THEN
    MATCH_MP_TAC SQRT_POS_LT THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `lrg_lsmooth (IMAGE (phi:A->real^3) U) a b
      (p2a_rlocal (p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3))
                  U b (U,phi))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3)`;
                   `U:A->bool`; `a:real`; `b:real`; `U:A->bool`; `phi:A->real^3`]
                  P2A_REGION_LRICCI) THEN
    ASM_REWRITE_TAC[INTER_IDEMPOT; lrg_lsmooth; p2a_lsmooth] THEN SIMP_TAC[];
    ALL_TAC] THEN
  (* the time range *)
  MP_TAC(ISPECL [`(U:A->bool,phi:A->real^3)`; `b - a`; `kk:real^(3,1)finite_sum->bool`]
                P2AW_KK_TAU_BOUNDS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `tau1:real` (X_CHOOSE_THEN `tau2:real` STRIP_ASSUME_TAC)) THEN
  (* the space range and a thickening *)
  SUBGOAL_THEN `compact(IMAGE fstcart (kk:real^(3,1)finite_sum->bool)) /\
                IMAGE fstcart kk SUBSET IMAGE (phi:A->real^3) U`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_LINEAR_IMAGE THEN ASM_REWRITE_TAC[LINEAR_FSTCART];
      UNDISCH_TAC `kk SUBSET p2bw_cdom (U:A->bool,phi:A->real^3) (b - a)` THEN
      REWRITE_TAC[p2bw_cdom; SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (phi:A->real^3) U`; `IMAGE fstcart (kk:real^(3,1)finite_sum->bool)`]
                P2AW_COMPACT_THICK) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `rr:real` (X_CHOOSE_THEN `K2:real^3->bool` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `!z:real^(3,1)finite_sum. z IN kk ==> cball(fstcart z,rr) SUBSET (K2:real^3->bool)`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:real^(3,1)finite_sum` THEN DISCH_TAC THEN
    REWRITE_TAC[SUBSET; IN_CBALL] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `y:real^3 = fstcart(z:real^(3,1)finite_sum) + (y - fstcart z)` SUBST1_TAC THENL
     [VECTOR_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `K2:real^3->bool`)) (concl th))) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `dist(fstcart(z:real^(3,1)finite_sum),y:real^3) <= rr` THEN
      REWRITE_TAC[dist] THEN MESON_TAC[NORM_SUB]];
    ALL_TAC] THEN
  (* constants *)
  ABBREV_TAC `sl = sqrt tau1 / &2` THEN ABBREV_TAC `sh = sqrt tau2` THEN
  SUBGOAL_THEN `&0 < sl /\ sl < sh /\ sh < sqrt(b - a) /\ sl + sl = sqrt tau1 /\
                &0 < sqrt tau1`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < sqrt tau1 /\ sqrt tau1 <= sqrt tau2 /\ sqrt tau2 < sqrt(b - a)`
    MP_TAC THENL
     [ASM_SIMP_TAC[SQRT_POS_LT; SQRT_MONO_LE; SQRT_MONO_LT] THEN
      MATCH_MP_TAC SQRT_MONO_LT THEN ASM_REAL_ARITH_TAC;
      EXPAND_TAC "sl" THEN EXPAND_TAC "sh" THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (phi:A->real^3) U`; `&0`; `sqrt(b - a)`;
                 `p2a_rlocal (p2a_flow_view (top,atlas) (real_interval[a,b])
                                (g:real->A->real^3^3)) U b (U,phi:A->real^3)`;
                 `b:real`; `K2:real^3->bool`; `sl:real`; `sh:real`] P2A_LSMOOTH_QUAD_BOUNDS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real` (X_CHOOSE_THEN `Cg:real` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`IMAGE (phi:A->real^3) U`; `&0`; `sqrt(b - a)`;
                 `p2a_rlocal (p2a_flow_view (top,atlas) (real_interval[a,b])
                                (g:real->A->real^3^3)) U b (U,phi:A->real^3)`;
                 `b:real`; `K2:real^3->bool`; `sl:real`; `sh:real`; `&0`] P2A_LLAG_BOUND) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `Kb:real`) THEN
  MP_TAC(ISPECL [`IMAGE (phi:A->real^3) U`; `&0`; `sqrt(b - a)`;
                 `p2a_rlocal (p2a_flow_view (top,atlas) (real_interval[a,b])
                                (g:real->A->real^3^3)) U b (U,phi:A->real^3)`;
                 `b:real`; `sl:real`; `sh:real`; `K2:real^3->bool`] P2A_LACC_QUAD_BOUND) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Cacc:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `Kp = abs Kb` THEN
  ABBREV_TAC `Lup = abs Lmax + &2 * abs m * sqrt tau2 * tau2` THEN
  ABBREV_TAC `X0 = &4 * (abs Lup + Kp) / c + &1` THEN
  SUBGOAL_THEN `&0 <= Kp /\ &1 <= X0` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "Kp" THEN EXPAND_TAC "X0" THEN REWRITE_TAC[REAL_ABS_POS] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &1 <= x + &1`) THEN MATCH_MP_TAC REAL_LE_MUL THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `D0 = min (min sl (&1)) (rr pow 2 / (&32 * X0))` THEN
  SUBGOAL_THEN `&0 < D0 /\ D0 <= &1 /\ D0 <= sl /\ &16 * X0 * D0 < rr pow 2`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < rr pow 2 / (&32 * X0)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_SIMP_TAC[REAL_POW_LT] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&16 * X0 * (rr pow 2 / (&32 * X0)) = rr pow 2 / &2` ASSUME_TAC THENL
     [UNDISCH_TAC `&1 <= X0` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    SUBGOAL_THEN `D0 <= rr pow 2 / (&32 * X0)` ASSUME_TAC THENL
     [EXPAND_TAC "D0" THEN REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&16 * X0 * D0 <= &16 * X0 * (rr pow 2 / (&32 * X0))` MP_TAC THENL
     [REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < rr pow 2` MP_TAC THENL [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
    EXPAND_TAC "D0" THEN
    MAP_EVERY UNDISCH_TAC [`&16 * (X0:real) * ((rr:real) pow 2 / (&32 * X0)) = rr pow 2 / &2`;
                           `&0 < (rr:real) pow 2 / (&32 * X0)`; `&0 < (sl:real)`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_THEN `min (min sl (&1)) (rr pow 2 / (&32 * X0)) = (D0:real)` (K ALL_TAC) THEN
  ABBREV_TAC `M = sqrt((&2 / c) * (Lup + Kp * (D0 / &2)) / (D0 / &2) + &1) +
                  Cacc * (D0 / &2 + (&2 / c) * (Lup + Kp * (D0 / &2)))` THEN
  SUBGOAL_THEN `&0 <= Lup` ASSUME_TAC THENL
   [EXPAND_TAC "Lup" THEN MATCH_MP_TAC(REAL_ARITH `&0 <= y ==> &0 <= abs x + &2 * y`) THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_ABS_POS] THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_SIMP_TAC[SQRT_POS_LE; REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &2 / c /\ &0 <= Lup + Kp * (D0 / &2)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_ADD THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= M` ASSUME_TAC THENL
   [EXPAND_TAC "M" THEN MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LE THEN MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 <= x + &1`) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_DIV THEN
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `K0 = interval[lift(b - sh pow 2),lift(b - sl pow 2)] PCROSS (K2:real^3->bool)` THEN
  SUBGOAL_THEN
   `compact (K0:real^(1,3)finite_sum->bool) /\
    K0 SUBSET interval(lift a,lift b) PCROSS IMAGE (phi:A->real^3) U /\
    (!s y. sl <= s /\ s <= sh /\ y IN K2 ==> pastecart (lift(b - s pow 2)) y IN K0)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `sh pow 2 = tau2 /\ &0 < sl pow 2` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [EXPAND_TAC "sh" THEN MATCH_MP_TAC SQRT_POW_2 THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    EXPAND_TAC "K0" THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_PCROSS THEN ASM_REWRITE_TAC[COMPACT_INTERVAL];
      REWRITE_TAC[SUBSET; FORALL_PASTECART; PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP] THEN
      MAP_EVERY X_GEN_TAC [`t:real^1`; `y:real^3`] THEN STRIP_TAC THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
        concl th = `K2 SUBSET IMAGE (phi:A->real^3) U`)) THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP] THEN
      MAP_EVERY X_GEN_TAC [`s:real`; `y:real^3`] THEN STRIP_TAC THEN
      SUBGOAL_THEN `sl pow 2 <= s pow 2 /\ s pow 2 <= sh pow 2` MP_TAC THENL
       [CONJ_TAC THEN MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* the family bounds *)
  MP_TAC(ISPECL [`IMAGE (phi:A->real^3) U`; `a:real`; `b:real`;
                 `p2a_rlocal (p2a_flow_view (top,atlas) (real_interval[a,b])
                                (g:real->A->real^3^3)) U b (U,phi:A->real^3)`;
                 `b:real`; `K0:real^(1,3)finite_sum->bool`; `M:real`; `D0 / &2`; `sh:real`]
                P2AW_CFAM_BOUND) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` (X_CHOOSE_THEN `C1:real` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`IMAGE (phi:A->real^3) U`; `a:real`; `b:real`;
                 `p2a_rlocal (p2a_flow_view (top,atlas) (real_interval[a,b])
                                (g:real->A->real^3^3)) U b (U,phi:A->real^3)`;
                 `b:real`; `K0:real^(1,3)finite_sum->bool`; `M:real`] P2AW_SFAM_BOUNDS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d2:real` (X_CHOOSE_THEN `C2:real` STRIP_ASSUME_TAC)) THEN
  (* hypotheses of the barrier at a point in the required form *)
  SUBGOAL_THEN
   `!(y:real^1->real^3) A s1 sb w.
      s1 < sb /\
      (!s. s1 <= s /\ s <= sb
           ==> pastecart (lift(b - s pow 2)) (y(lift s)) IN K0 /\
               norm(A(lift s)) <= M /\
               (y has_vector_derivative A(lift s)) (at (lift s))) /\
      A continuous_on interval[lift s1,lift sb] /\
      (&1 + inv(sb - s1)) * norm w <= d2
      ==> (!s. s1 <= s /\ s <= sb
               ==> pastecart (lift(b - s pow 2)) (y(lift s) + ((s - s1) / (sb - s1)) % w)
                   IN interval(lift a,lift b) PCROSS IMAGE (phi:A->real^3) U) /\
          p2a_cL (p2a_rlocal (p2a_flow_view (top,atlas) (real_interval[a,b])
                                (g:real->A->real^3^3)) U b (U,phi)) b
                 (p2aw_sfam y s1 sb w) s1 sb +
          p2a_cL (p2a_rlocal (p2a_flow_view (top,atlas) (real_interval[a,b]) g) U b (U,phi)) b
                 (p2aw_sfam y s1 sb (--w)) s1 sb -
          &2 * p2a_cL (p2a_rlocal (p2a_flow_view (top,atlas) (real_interval[a,b]) g) U b
                                  (U,phi)) b y s1 sb
          <= C2 * (sb - s1 + &1) pow 2 / (sb - s1) * norm w pow 2`
  (LABEL_TAC "HSF") THENL
   [MAP_EVERY X_GEN_TAC [`y:real^1->real^3`; `A:real^1->real^3`; `s1:real`; `sb:real`;
                         `w:real^3`] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`y:real^1->real^3`; `A:real^1->real^3`; `s1:real`; `sb:real`;
                                  `w:real^3`] o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "p2aw_sfam")) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!r y. sl <= r /\ r <= sh /\ y IN K2
          ==> abs(p2a_llag (p2a_rlocal (p2a_flow_view (top,atlas) (real_interval[a,b])
                                         (g:real->A->real^3^3)) U b (U,phi:A->real^3))
                           b r y (vec 0)) <= Kp`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "Kp" THEN
    MATCH_MP_TAC(REAL_ARITH `x <= k ==> x <= abs k`) THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `Kb:real`)) (concl th))) THEN
    ASM_REWRITE_TAC[NORM_0; REAL_LE_REFL];
    ALL_TAC] THEN
  UNDISCH_THEN `abs(Kb:real) = Kp` (K ALL_TAC) THEN
  SUBGOAL_THEN
   `!r y A. sl <= r /\ r <= sh /\ y IN K2
            ==> c * norm(A:real^3) pow 2 <=
                A dot (p2a_rlocal (p2a_flow_view (top,atlas) (real_interval[a,b])
                                     (g:real->A->real^3^3)) U b (U,phi:A->real^3)
                         (b - r pow 2) y ** A)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`r:real`; `y:real^3`; `A:real^3`] o
      check (fun th -> is_forall(concl th) && can (find_term ((=) `Cg:real`)) (concl th))) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  (* the radius and the constant *)
  ABBREV_TAC `Q = &2 / (D0 * sqrt tau1)` THEN
  SUBGOAL_THEN `&0 < Q` ASSUME_TAC THENL
   [EXPAND_TAC "Q" THEN MATCH_MP_TAC REAL_LT_DIV THEN CONJ_TAC THENL
     [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `dk = min d1 (inv(&2)) / Q` THEN
  SUBGOAL_THEN `&0 < dk /\ Q * dk = min d1 (inv(&2))` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "dk" THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      UNDISCH_TAC `&0 < Q` THEN CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  UNDISCH_THEN `min d1 (inv(&2)) / Q = (dk:real)` (K ALL_TAC) THEN
  SUBGOAL_THEN `&0 < &1 + inv(D0 / &2)` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 < &1 + x`) THEN
    MATCH_MP_TAC REAL_LE_INV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `d = min (min dk d1) (min (min (tau1 / &2) ((b - a - tau2) / &2))
                                       (min rr (d2 / (&1 + inv(D0 / &2)))))` THEN
  SUBGOAL_THEN `&0 < d /\ d <= dk /\ d <= d1 /\ d <= tau1 / &2 /\ d <= (b - a - tau2) / &2 /\
                d <= rr /\ d <= d2 / (&1 + inv(D0 / &2))`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < d2 / (&1 + inv(D0 / &2))` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    EXPAND_TAC "d" THEN
    MAP_EVERY UNDISCH_TAC [`&0 < (dk:real)`; `&0 < (d1:real)`; `&0 < (rr:real)`;
                           `tau2 < (b:real) - a`; `&0 < (tau1:real)`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `C = max (C1 * (&1 + Q)) (C2 * (D0 / &2 + &1) pow 2 / (D0 / &2))` THEN
  SUBGOAL_THEN `C1 * (&1 + Q) <= C /\ C2 * (D0 / &2 + &1) pow 2 / (D0 / &2) <= C /\ &0 <= C`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "C" THEN REWRITE_TAC[REAL_LE_MAX; REAL_LE_REFL] THEN
    DISJ1_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
    UNDISCH_TAC `&0 < (Q:real)` THEN UNDISCH_TAC `&0 <= (C1:real)` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (fun th -> is_eq(concl th) && is_var(rand(concl th)) &&
    mem (fst(dest_var(rand(concl th)))) ["Kp"; "D0"; "d"; "C"]))) THEN
  MAP_EVERY EXISTS_TAC [`d:real`; `C:real`] THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `z:real^(3,1)finite_sum` THEN DISCH_TAC THEN
  (* the point *)
  FIRST_X_ASSUM(MP_TAC o SPEC `z:real^(3,1)finite_sum` o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_min")) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `gamma:real->A` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `p2a_Lx (p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3))
                  b p (drop(sndcart(z:real^(3,1)finite_sum))) (chart_inv (U,phi) (fstcart z))
                <= Lmax` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `fstcart(z:real^(3,1)finite_sum) IN IMAGE (phi:A->real^3) U /\
                tau1 <= drop(sndcart z) /\ drop(sndcart z) <= tau2 /\
                cball(fstcart z,rr) SUBSET K2`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[] THEN
    FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
      concl th = `IMAGE fstcart (kk:real^(3,1)finite_sum->bool) SUBSET IMAGE (phi:A->real^3) U`)) THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `x = fstcart(z:real^(3,1)finite_sum)` THEN
  ABBREV_TAC `tau = drop(sndcart(z:real^(3,1)finite_sum))` THEN
  SUBGOAL_THEN `(gamma:real->A) tau IN U /\ (phi:A->real^3)(gamma tau) = x`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < tau /\ tau < b - a /\ sqrt tau1 <= sqrt tau /\ sqrt tau <= sh`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    EXPAND_TAC "sh" THEN CONJ_TAC THEN MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `p2a_L_length (p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3)) b
                 (gamma:real->A) tau + &2 * abs m * sqrt tau * tau <= Lup`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3)`;
                   `b:real`; `p:A`; `tau:real`; `gamma:real->A`] P2A_MIN_LX) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN EXPAND_TAC "Lup" THEN
    MATCH_MP_TAC(REAL_ARITH `l <= lm /\ y <= y' ==> l + &2 * y <= abs lm + &2 * y'`) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN
    REPEAT CONJ_TAC THEN TRY(MATCH_MP_TAC SQRT_POS_LE) THEN TRY ASM_REAL_ARITH_TAC THEN
    UNDISCH_TAC `sqrt tau <= sh` THEN EXPAND_TAC "sh" THEN REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                 `g:real->A->real^3^3`; `m:real`; `p:A`; `tau:real`; `gamma:real->A`;
                 `U:A->bool`; `phi:A->real^3`; `K2:real^3->bool`; `rr:real`; `sl:real`;
                 `sh:real`; `c:real`; `Kp:real`; `Cacc:real`; `Lup:real`; `D0:real`;
                 `K0:real^(1,3)finite_sum->bool`; `M:real`; `d1:real`; `C1:real`; `d2:real`;
                 `C2:real`] P2AW_FLOW_PT_BARRIER) THEN
  ASM_REWRITE_TAC[REAL_LE_REFL] THEN ANTS_TAC THENL
   [ASM_REAL_ARITH_TAC;
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "P1") (LABEL_TAC "P2"))] THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (fun th -> is_eq(concl th) && is_var(rand(concl th)) &&
    mem (fst(dest_var(rand(concl th)))) ["X0"; "Lup"; "M"]))) THEN
  CONJ_TAC THENL
   [(* first order *)
    MAP_EVERY X_GEN_TAC [`w:real^3`; `h:real`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `&0 <= tau + h /\ &0 < tau + h /\ tau + h < b - a` STRIP_ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[p2bw_cdom; IN_ELIM_THM; FSTCART_PASTECART; SNDCART_PASTECART; DROP_ADD;
                  LIFT_DROP] THEN
      ASM_REWRITE_TAC[] THEN
      FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
        concl th = `K2 SUBSET IMAGE (phi:A->real^3) U`)) THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `rr:real`)) (concl th) &&
        can (find_term ((=) `K2:real^3->bool`)) (concl th) &&
        not (can (find_term (fun t -> is_const t && fst(dest_const t) = "cball")) (concl th)))) THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th ->
          concl th = `fstcart(z:real^(3,1)finite_sum) = x`)) THEN
        MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
        ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`tau:real`; `h:real`; `D0:real`; `tau1:real`] P2AW_K_ARITH) THEN
    ASM_REWRITE_TAC[] THEN
    ABBREV_TAC `k = &1 + (sqrt(tau + h) - sqrt tau) / (D0 / &2)` THEN STRIP_TAC THEN
    SUBGOAL_THEN `abs(k - &1) <= min d1 (inv(&2))` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `Q * abs h` THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `Q * dk = min d1 (inv(&2))`)) THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    USE_THEN "P1" (MP_TAC o SPECL [`w:real^3`; `k:real`]) THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `sqrt(tau + h) pow 2 = tau + h` SUBST1_TAC THENL
       [MATCH_MP_TAC SQRT_POW_2 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      MAP_EVERY UNDISCH_TAC [`abs(k - &1) <= min d1 (inv(&2))`; `abs(h:real) <= d`;
                             `norm(w:real^3) <= d`; `tau <= (tau2:real)`;
                             `d <= ((b:real) - a - tau2) / &2`; `d <= (d1:real)`;
                             `tau2 < (b:real) - a`] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `sqrt(tau + h) pow 2 = tau + h` SUBST1_TAC THENL
     [MATCH_MP_TAC SQRT_POW_2 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `y <= z ==> l <= l0 + y ==> l <= l0 + z`) THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(C1 * (&1 + Q)) * (norm(w:real^3) + abs h)` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `&0 <= Q * norm(w:real^3) /\ &0 <= Q * abs h` MP_TAC THENL
       [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[NORM_POS_LE; REAL_ABS_POS] THEN
        ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC];
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPEC `w:real^3` NORM_POS_LE) THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* second differences *)
  X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
  USE_THEN "P2" (MP_TAC o SPEC `w:real^3`) THEN ANTS_TAC THENL
   [ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    SUBGOAL_THEN `norm(w:real^3) <= d2 / (&1 + inv(D0 / &2))` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_SIMP_TAC[REAL_LE_RDIV_EQ]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REAL_ARITH `y <= z ==> l <= y ==> l <= z`) THEN
  REWRITE_TAC[REAL_MUL_ASSOC] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2]);;

(* ------------------------------------------------------------------------- *)
(* Bounds of the reduced length on compact subsets of the chart domain       *)
(* (above: pointwise barriers and a finite subcover; below: the scalar lower *)
(* bound), and the quotient rule for L / (2 sqrt tau).                       *)
(* ------------------------------------------------------------------------- *)

(* The text and proof of PDM_COMPACT_LOCAL_BOUND (pc_pde_mnorm), restated  *)
(* here to keep the load closure of this unit low.                          *)

let P2AW_COMPACT_LOCAL_BOUND = prove
 (`!(k:real^N->bool) (P:real->real^N->bool).
        compact k /\ (!C C' y. P C y /\ C <= C' ==> P C' y) /\
        (!y0. y0 IN k ==> ?r C. &0 < r /\ !y. y IN k /\ y IN ball(y0,r) ==> P C y)
        ==> ?C. !y. y IN k ==> P C y`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "mono")
    (MP_TAC o REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM]))) THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real^N->real` (X_CHOOSE_TAC `CC:real^N->real`)) THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [COMPACT_EQ_HEINE_BOREL]) THEN
  DISCH_THEN(MP_TAC o SPEC `IMAGE (\y0:real^N. ball(y0,r y0)) k`) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FORALL_IN_IMAGE; OPEN_BALL; SUBSET; IN_UNIONS; EXISTS_IN_IMAGE] THEN
    X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN EXISTS_TAC `y:real^N` THEN
    ASM_SIMP_TAC[CENTRE_IN_BALL];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `?FF. FINITE FF /\ FF SUBSET k /\ f = IMAGE (\y0:real^N. ball(y0,r y0)) FF`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM FINITE_SUBSET_IMAGE] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`CC:real^N->real`; `FF:real^N->bool`] UPPER_BOUND_FINITE_SET_REAL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `a:real`) THEN
  EXISTS_TAC `a:real` THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
  SUBGOAL_THEN `?y0:real^N. y0 IN FF /\ y IN ball(y0,r y0)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `k SUBSET UNIONS (f:(real^N->bool)->bool)` THEN
    ASM_REWRITE_TAC[SUBSET; IN_UNIONS; EXISTS_IN_IMAGE] THEN
    DISCH_THEN(MP_TAC o SPEC `y:real^N`) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  USE_THEN "mono" MATCH_MP_TAC THEN
  EXISTS_TAC `(CC:real^N->real) y0` THEN
  CONJ_TAC THENL [ALL_TAC; ASM_SIMP_TAC[]] THEN
  SUBGOAL_THEN `(y0:real^N) IN k` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  ASM_MESON_TAC[]);;

let P2AW_CART_STEP = prove
 (`!(z:real^(M,1)finite_sum) y.
     pastecart (fstcart z + (fstcart y - fstcart z))
               (sndcart z + lift(drop(sndcart y) - drop(sndcart z))) = y /\
     drop(sndcart z) + (drop(sndcart y) - drop(sndcart z)) = drop(sndcart y) /\
     norm(fstcart y - fstcart z) <= norm(y - z) /\
     abs(drop(sndcart y) - drop(sndcart z)) <= norm(y - z)`,
  REPEAT GEN_TAC THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[LIFT_SUB; LIFT_DROP; VECTOR_ARITH `x + (y - x):real^N = y`;
                PASTECART_FST_SND];
    REAL_ARITH_TAC;
    REWRITE_TAC[GSYM FSTCART_SUB; NORM_FSTCART];
    REWRITE_TAC[GSYM DROP_SUB; GSYM SNDCART_SUB; GSYM NORM_1; NORM_SNDCART]]);;

let P2AW_FLOW_LX_UBOUND = prove
 (`!top atlas a b (g:real->A->real^3^3) m p U (phi:A->real^3) kk.
     p2a_cbflow (top,atlas) a b g /\ p IN topspace top /\ (U,phi) IN atlas /\
     (!t y. a <= t /\ t <= b /\ y IN topspace top ==> m <= mfd_scalar atlas (g t) y) /\
     compact kk /\ kk SUBSET p2bw_cdom (U,phi) (b - a) /\
     (!z. z IN p2bw_cdom (U,phi) (b - a)
          ==> ?gamma. p2a_min (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p
                              (drop(sndcart z)) gamma /\
                      gamma(drop(sndcart z)) = chart_inv (U,phi) (fstcart z))
     ==> ?Lmax. !z. z IN kk
                    ==> p2a_Lx (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p
                               (drop(sndcart z)) (chart_inv (U,phi) (fstcart z)) <= Lmax`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`kk:real^(3,1)finite_sum->bool`;
                 `\C z:real^(3,1)finite_sum.
                    p2a_Lx (p2a_flow_view (top,atlas) (real_interval[a,b])
                              (g:real->A->real^3^3)) b p
                           (drop(sndcart z)) (chart_inv (U,phi:A->real^3) (fstcart z)) <= C`]
                P2AW_COMPACT_LOCAL_BOUND) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `z0:real^(3,1)finite_sum` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                 `g:real->A->real^3^3`; `m:real`; `p:A`; `U:A->bool`; `phi:A->real^3`;
                 `{z0:real^(3,1)finite_sum}`;
                 `p2a_Lx (p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3))
                         b p (drop(sndcart(z0:real^(3,1)finite_sum)))
                         (chart_inv (U,phi:A->real^3) (fstcart z0))`] P2AW_FLOW_KK_BARRIER) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[COMPACT_SING; IN_SING; FORALL_UNWIND_THM2; SING_SUBSET; REAL_LE_REFL] THEN
    SUBGOAL_THEN `(z0:real^(3,1)finite_sum) IN p2bw_cdom (U:A->bool,phi:A->real^3) (b - a)`
    ASSUME_TAC THENL
     [FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
        concl th = `(kk:real^(3,1)finite_sum->bool) SUBSET p2bw_cdom (U:A->bool,phi:A->real^3) (b - a)`)) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[IN_SING; FORALL_UNWIND_THM2] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (X_CHOOSE_THEN `C:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (LABEL_TAC "B1") (K ALL_TAC)))))) THEN
  MAP_EVERY EXISTS_TAC
   [`d:real`;
    `p2a_Lx (p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3))
            b p (drop(sndcart(z0:real^(3,1)finite_sum)))
            (chart_inv (U,phi:A->real^3) (fstcart z0)) + C * (d + d)`] THEN
  ASM_REWRITE_TAC[IN_BALL] THEN X_GEN_TAC `y:real^(3,1)finite_sum` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`z0:real^(3,1)finite_sum`; `y:real^(3,1)finite_sum`] P2AW_CART_STEP) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `norm(y - z0:real^(3,1)finite_sum) < d` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[NORM_SUB] THEN ASM_REWRITE_TAC[GSYM dist]; ALL_TAC] THEN
  USE_THEN "B1" (MP_TAC o SPECL [`fstcart(y:real^(3,1)finite_sum) - fstcart(z0:real^(3,1)finite_sum)`;
                                 `drop(sndcart(y:real^(3,1)finite_sum)) - drop(sndcart(z0:real^(3,1)finite_sum))`]) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT2) THEN
  ASM_REWRITE_TAC[VECTOR_ARITH `x + (y - x):real^N = y`] THEN
  MATCH_MP_TAC(REAL_ARITH `y <= z ==> l <= l0 + y ==> l <= l0 + z`) THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC);;

let P2AW_FLOW_LX_LBOUND = prove
 (`!top atlas a b (g:real->A->real^3^3) m p tau (gamma:real->A).
     p2a_cbflow (top,atlas) a b g /\
     (!t y. a <= t /\ t <= b /\ y IN topspace top ==> m <= mfd_scalar atlas (g t) y) /\
     p2a_min (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p tau gamma /\ tau < b - a
     ==> --(abs m * sqrt(b - a) * (b - a)) <=
         p2a_Lx (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p tau (gamma tau)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `p2a_adm (p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3))
                  b p tau gamma` ASSUME_TAC THENL [ASM_MESON_TAC[p2a_min]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < tau` ASSUME_TAC THENL [ASM_MESON_TAC[p2a_adm]; ALL_TAC] THEN
  MP_TAC(ISPECL [`p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3)`;
                 `b:real`; `p:A`; `tau:real`; `gamma:real->A`] P2A_MIN_LX) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `--(abs m * sqrt tau * tau)` THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_LE_NEG2] THEN MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN
    ASM_SIMP_TAC[SQRT_POS_LE; SQRT_MONO_LE; REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC P2AW_ADM_LOWER THEN EXISTS_TAC `p:A` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC P2AW_FLOW_SCAL_ALONG THEN EXISTS_TAC `p:A` THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE]]);;

let P2AW_QUOT_LIP = prove
 (`!A1 A2 t1 t2 tau1 B L r.
     &0 < tau1 /\ tau1 <= t1 /\ tau1 <= t2 /\ abs A2 <= B /\
     abs(A1 - A2) <= L * r /\ abs(t1 - t2) <= r
     ==> abs(A1 / (&2 * sqrt t1) - A2 / (&2 * sqrt t2)) <=
         (L / (&2 * sqrt tau1) + B / (&2 * tau1 * sqrt tau1)) * r`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < sqrt tau1 /\ sqrt tau1 <= sqrt t1 /\ sqrt tau1 <= sqrt t2 /\
                sqrt tau1 * sqrt tau1 = tau1` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LT; SQRT_MONO_LE; REAL_LT_IMP_LE; GSYM REAL_POW_2; SQRT_POW_2];
    ALL_TAC] THEN
  ABBREV_TAC `u = sqrt tau1` THEN ABBREV_TAC `s1 = sqrt t1` THEN ABBREV_TAC `s2 = sqrt t2` THEN
  SUBGOAL_THEN `abs(s2 - s1) <= r / u` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`t1:real`; `t2:real`; `tau1:real`] P2AW_SQRT_DIFF_LE) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]] THEN
    MATCH_MP_TAC(REAL_ARITH `y <= z ==> x <= y ==> x <= z`) THEN
    ASM_SIMP_TAC[REAL_LE_DIV2_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < s1 /\ &0 < s2 /\ tau1 <= s1 * s2` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `u * u = tau1`)) THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `A1 / (&2 * s1) - A2 / (&2 * s2) =
                (A1 - A2) * inv(&2 * s1) + (A2 * (s2 - s1)) * inv(&2 * s1 * s2)`
  SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < s1` THEN UNDISCH_TAC `&0 < s2` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  SUBGOAL_THEN `(L / (&2 * u) + B / (&2 * tau1 * u)) * r =
                (L * r) * inv(&2 * u) + (B * (r / u)) * inv(&2 * tau1)`
  SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < u` THEN UNDISCH_TAC `&0 < tau1` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `abs x <= x' /\ abs y <= y' ==> abs(x + y) <= x' + y'`) THEN
  REWRITE_TAC[REAL_ABS_MUL] THEN
  SUBGOAL_THEN `abs(inv(&2 * s1)) = inv(&2 * s1) /\ abs(inv(&2 * s1 * s2)) = inv(&2 * s1 * s2)`
  (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[REAL_ABS_INV] THEN CONJ_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_NUM] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_ABS_POS] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_LE_INV THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_ABS_POS];
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_ABS_POS];
    MATCH_MP_TAC REAL_LE_INV THEN MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC];
    MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC]);;

let P2AW_LIP_FROM_LOCAL = prove
 (`!(f:real^N->real) k d C B.
     &0 < d /\ &0 <= C /\ (!x. x IN k ==> abs(f x) <= B) /\
     (!x y. x IN k /\ y IN k /\ norm(x - y) <= d ==> f x <= f y + C * norm(x - y))
     ==> !x y. x IN k /\ y IN k ==> abs(f x - f y) <= (C + &2 * B / d) * norm(x - y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= B` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `abs((f:real^N->real) x)` THEN
    ASM_SIMP_TAC[REAL_ABS_POS];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= B / d` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &2 * B / d * norm(x - y:real^N) /\ &0 <= C * norm(x - y:real^N)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_SIMP_TAC[NORM_POS_LE; REAL_LE_MUL; REAL_POS];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ADD_RDISTRIB] THEN
  ASM_CASES_TAC `norm(x - y:real^N) <= d` THENL
   [SUBGOAL_THEN `(f:real^N->real) x <= f y + C * norm(x - y) /\
                  f y <= f x + C * norm(x - y)` MP_TAC THENL
     [CONJ_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        ONCE_REWRITE_TAC[NORM_SUB] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        ONCE_REWRITE_TAC[NORM_SUB] THEN ASM_REWRITE_TAC[]];
      ASM_REAL_ARITH_TAC];
    SUBGOAL_THEN `&2 * B <= &2 * B / d * norm(x - y:real^N)` MP_TAC THENL
     [REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
      ASM_SIMP_TAC[GSYM real_div; REAL_LE_RDIV_EQ; REAL_MUL_LID] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `abs((f:real^N->real) x) <= B /\ abs(f y) <= B` MP_TAC THENL
     [ASM_SIMP_TAC[]; ASM_REAL_ARITH_TAC]]);;

let P2AW_SHIFT_SPACE = prove
 (`!(x:real^(M,N)finite_sum) v t.
     x + t % pastecart v (vec 0) = pastecart (fstcart x + t % v) (sndcart x) /\
     x - t % pastecart v (vec 0) = pastecart (fstcart x - t % v) (sndcart x)`,
  REWRITE_TAC[PASTECART_EQ; FSTCART_ADD; SNDCART_ADD; FSTCART_SUB; SNDCART_SUB;
              FSTCART_CMUL; SNDCART_CMUL; FSTCART_PASTECART; SNDCART_PASTECART;
              VECTOR_MUL_RZERO; VECTOR_ADD_RID; VECTOR_SUB_RZERO]);;

(* ------------------------------------------------------------------------- *)
(* The results of this unit for the reduced distance read in a chart, l =    *)
(* p2bw_cfun c (p2a_lx V b p), given a lower bound of the scalar curvature   *)
(* and minimizers to all points of the chart domain: l is locally Lipschitz  *)
(* on the space-time chart domain (MT Prop 7.5(1)) and spatially semiconcave *)
(* in the form used by P2AW_NBP_MATRIX.                                      *)
(* ------------------------------------------------------------------------- *)

let P2AW_LX_LOCLIP_UPHI = prove
 (`!top atlas a b (g:real->A->real^3^3) m p U (phi:A->real^3).
     p2a_cbflow (top,atlas) a b g /\ p IN topspace top /\ (U,phi) IN atlas /\
     (!t y. a <= t /\ t <= b /\ y IN topspace top ==> m <= mfd_scalar atlas (g t) y) /\
     (!z. z IN p2bw_cdom (U,phi) (b - a)
          ==> ?gamma. p2a_min (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p
                              (drop(sndcart z)) gamma /\
                      gamma(drop(sndcart z)) = chart_inv (U,phi) (fstcart z))
     ==> wan_loclip (p2bw_cdom (U,phi) (b - a))
                    (p2bw_cfun (U,phi)
                       (p2a_lx (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[wan_loclip; p2bw_cfun; p2a_lx] THEN
  X_GEN_TAC `kk:real^(3,1)finite_sum->bool` THEN STRIP_TAC THEN
  ABBREV_TAC
   `Lf = \z:real^(3,1)finite_sum.
           p2a_Lx (p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3)) b p
                  (drop(sndcart z)) (chart_inv (U,phi:A->real^3) (fstcart z))` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                 `g:real->A->real^3^3`; `m:real`; `p:A`; `U:A->bool`; `phi:A->real^3`;
                 `kk:real^(3,1)finite_sum->bool`] P2AW_FLOW_LX_UBOUND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `Lmax:real`) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                 `g:real->A->real^3^3`; `m:real`; `p:A`; `U:A->bool`; `phi:A->real^3`;
                 `kk:real^(3,1)finite_sum->bool`; `Lmax:real`] P2AW_FLOW_KK_BARRIER) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `z:real^(3,1)finite_sum` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_min")) (concl th))) THEN
    FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
      concl th = `(kk:real^(3,1)finite_sum->bool) SUBSET p2bw_cdom (U:A->bool,phi:A->real^3) (b - a)`)) THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `d:real` (X_CHOOSE_THEN `C:real` STRIP_ASSUME_TAC))] THEN
  MP_TAC(ISPECL [`(U:A->bool,phi:A->real^3)`; `b - a`; `kk:real^(3,1)finite_sum->bool`]
                P2AW_KK_TAU_BOUNDS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `p2a_cbflow (top,atlas) a b (g:real->A->real^3^3)` THEN
    REWRITE_TAC[p2a_cbflow] THEN STRIP_TAC THEN ASM_REAL_ARITH_TAC;
    DISCH_THEN(X_CHOOSE_THEN `tau1:real` (X_CHOOSE_THEN `tau2:real` STRIP_ASSUME_TAC))] THEN
  (* bounds of Lf on kk *)
  SUBGOAL_THEN `!z:real^(3,1)finite_sum.
                  z IN kk ==> abs((Lf:real^(3,1)finite_sum->real) z) <=
                              abs Lmax + abs m * sqrt(b - a) * (b - a)`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:real^(3,1)finite_sum` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(z:real^(3,1)finite_sum) IN p2bw_cdom (U,phi:A->real^3) (b - a)` MP_TAC THENL
     [FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
        concl th = `(kk:real^(3,1)finite_sum->bool) SUBSET p2bw_cdom (U:A->bool,phi:A->real^3) (b - a)`)) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(fun th -> ASSUME_TAC th THEN MP_TAC th) THEN
    REWRITE_TAC[p2bw_cdom; IN_ELIM_THM] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `z:real^(3,1)finite_sum` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_min")) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `gamma:real->A` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                   `g:real->A->real^3^3`; `m:real`; `p:A`; `drop(sndcart(z:real^(3,1)finite_sum))`;
                   `gamma:real->A`] P2AW_FLOW_LX_LBOUND) THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `z:real^(3,1)finite_sum` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `Lmax:real`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "Lf" THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `&0 <= abs m * sqrt(b - a) * (b - a)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_ABS_POS] THEN MATCH_MP_TAC REAL_LE_MUL THEN
      CONJ_TAC THENL [MATCH_MP_TAC SQRT_POS_LE; ALL_TAC] THEN ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* local one-sided bound *)
  SUBGOAL_THEN
   `!x y:real^(3,1)finite_sum.
      x IN kk /\ y IN kk /\ norm(x - y) <= d
      ==> (Lf:real^(3,1)finite_sum->real) x <= Lf y + (&2 * C) * norm(x - y)`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`x:real^(3,1)finite_sum`; `y:real^(3,1)finite_sum`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`y:real^(3,1)finite_sum`; `x:real^(3,1)finite_sum`] P2AW_CART_STEP) THEN
    STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:real^(3,1)finite_sum` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `C:real`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL [`fstcart(x:real^(3,1)finite_sum) - fstcart(y:real^(3,1)finite_sum)`;
                               `drop(sndcart(x:real^(3,1)finite_sum)) - drop(sndcart(y:real^(3,1)finite_sum))`] o
               CONJUNCT1) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o CONJUNCT2) THEN
    ASM_REWRITE_TAC[VECTOR_ARITH `y + (x - y):real^N = x`] THEN EXPAND_TAC "Lf" THEN
    REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `y <= z ==> l <= l0 + y ==> l <= l0 + z`) THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `C * (norm(x - y:real^(3,1)finite_sum) + norm(x - y:real^(3,1)finite_sum))` THEN
    CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`Lf:real^(3,1)finite_sum->real`; `kk:real^(3,1)finite_sum->bool`; `d:real`;
                 `&2 * C`; `abs Lmax + abs m * sqrt(b - a) * (b - a)`] P2AW_LIP_FROM_LOCAL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  EXISTS_TAC `(&2 * C + &2 * (abs Lmax + abs m * sqrt(b - a) * (b - a)) / d) /
                (&2 * sqrt tau1) +
              (abs Lmax + abs m * sqrt(b - a) * (b - a)) / (&2 * tau1 * sqrt tau1)` THEN
  MAP_EVERY X_GEN_TAC [`x:real^(3,1)finite_sum`; `y:real^(3,1)finite_sum`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`y:real^(3,1)finite_sum`; `x:real^(3,1)finite_sum`] P2AW_CART_STEP) THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`(Lf:real^(3,1)finite_sum->real) x`; `(Lf:real^(3,1)finite_sum->real) y`;
                 `drop(sndcart(x:real^(3,1)finite_sum))`; `drop(sndcart(y:real^(3,1)finite_sum))`;
                 `tau1:real`; `abs Lmax + abs m * sqrt(b - a) * (b - a)`;
                 `&2 * C + &2 * (abs Lmax + abs m * sqrt(b - a) * (b - a)) / d`;
                 `norm(x - y:real^(3,1)finite_sum)`] P2AW_QUOT_LIP) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; EXPAND_TAC "Lf" THEN REWRITE_TAC[]]);;

let P2AW_LX_SEMICONC_UPHI = prove
 (`!top atlas a b (g:real->A->real^3^3) m p U (phi:A->real^3).
     p2a_cbflow (top,atlas) a b g /\ p IN topspace top /\ (U,phi) IN atlas /\
     (!t y. a <= t /\ t <= b /\ y IN topspace top ==> m <= mfd_scalar atlas (g t) y) /\
     (!z. z IN p2bw_cdom (U,phi) (b - a)
          ==> ?gamma. p2a_min (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p
                              (drop(sndcart z)) gamma /\
                      gamma(drop(sndcart z)) = chart_inv (U,phi) (fstcart z))
     ==> !kk. compact kk /\ kk SUBSET p2bw_cdom (U,phi) (b - a)
              ==> ?C d. &0 < d /\
                        !x v t. x IN kk /\ norm v <= &2 /\ abs t < d
                                ==> p2bw_cfun (U,phi)
                                      (p2a_lx (p2a_flow_view (top,atlas) (real_interval[a,b]) g)
                                              b p) (x + t % pastecart v (vec 0)) +
                                    p2bw_cfun (U,phi)
                                      (p2a_lx (p2a_flow_view (top,atlas) (real_interval[a,b]) g)
                                              b p) (x - t % pastecart v (vec 0)) -
                                    &2 * p2bw_cfun (U,phi)
                                           (p2a_lx (p2a_flow_view (top,atlas)
                                                      (real_interval[a,b]) g) b p) x
                                    <= C * t pow 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  X_GEN_TAC `kk:real^(3,1)finite_sum->bool` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                 `g:real->A->real^3^3`; `m:real`; `p:A`; `U:A->bool`; `phi:A->real^3`;
                 `kk:real^(3,1)finite_sum->bool`] P2AW_FLOW_LX_UBOUND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `Lmax:real`) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                 `g:real->A->real^3^3`; `m:real`; `p:A`; `U:A->bool`; `phi:A->real^3`;
                 `kk:real^(3,1)finite_sum->bool`; `Lmax:real`] P2AW_FLOW_KK_BARRIER) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `z:real^(3,1)finite_sum` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_min")) (concl th))) THEN
    FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
      concl th = `(kk:real^(3,1)finite_sum->bool) SUBSET p2bw_cdom (U:A->bool,phi:A->real^3) (b - a)`)) THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `d:real` (X_CHOOSE_THEN `C:real` STRIP_ASSUME_TAC))] THEN
  MP_TAC(ISPECL [`(U:A->bool,phi:A->real^3)`; `b - a`; `kk:real^(3,1)finite_sum->bool`]
                P2AW_KK_TAU_BOUNDS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `p2a_cbflow (top,atlas) a b (g:real->A->real^3^3)` THEN
    REWRITE_TAC[p2a_cbflow] THEN STRIP_TAC THEN ASM_REAL_ARITH_TAC;
    DISCH_THEN(X_CHOOSE_THEN `tau1:real` (X_CHOOSE_THEN `tau2:real` STRIP_ASSUME_TAC))] THEN
  SUBGOAL_THEN `&0 < sqrt tau1` ASSUME_TAC THENL [ASM_SIMP_TAC[SQRT_POS_LT]; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`&2 * C / sqrt tau1`; `d / &2`] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`x:real^(3,1)finite_sum`; `v:real^3`; `t:real`] THEN STRIP_TAC THEN
  REWRITE_TAC[P2AW_SHIFT_SPACE; p2bw_cfun; p2a_lx; FSTCART_PASTECART; SNDCART_PASTECART] THEN
  SUBGOAL_THEN `norm(t % v:real^3) <= d /\ norm(t % v:real^3) pow 2 <= &4 * t pow 2`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[NORM_MUL] THEN
    SUBGOAL_THEN `abs t * norm(v:real^3) <= &2 * abs t` ASSUME_TAC THENL
     [GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_REWRITE_TAC[REAL_ABS_POS];
      ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_POW_MUL] THEN
    SUBGOAL_THEN `abs t pow 2 = t pow 2` SUBST1_TAC THENL
     [REWRITE_TAC[REAL_POW2_ABS]; ALL_TAC] THEN
    GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    REWRITE_TAC[REAL_LE_POW_2] THEN
    SUBGOAL_THEN `&4 = &2 pow 2` SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[NORM_POS_LE];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:real^(3,1)finite_sum` o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `C:real`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `t % v:real^3` o CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `tau1 <= drop(sndcart(x:real^(3,1)finite_sum))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `s = sqrt(drop(sndcart(x:real^(3,1)finite_sum)))` THEN
  SUBGOAL_THEN `sqrt tau1 <= s` ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < s` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `X1 = p2a_Lx (p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3))
                          b p (drop(sndcart(x:real^(3,1)finite_sum)))
                          (chart_inv (U,phi:A->real^3) (fstcart x + t % v))` THEN
  ABBREV_TAC `X2 = p2a_Lx (p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3))
                          b p (drop(sndcart(x:real^(3,1)finite_sum)))
                          (chart_inv (U,phi:A->real^3) (fstcart x - t % v))` THEN
  ABBREV_TAC `X0 = p2a_Lx (p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3))
                          b p (drop(sndcart(x:real^(3,1)finite_sum)))
                          (chart_inv (U,phi:A->real^3) (fstcart x))` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `X1 / (&2 * s) + X2 / (&2 * s) - &2 * X0 / (&2 * s) =
                (X1 + X2 - &2 * X0) * inv(&2 * s)` SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < s` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(C * &4 * t pow 2) * inv(&2 * s)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `C * norm(t % v:real^3) pow 2` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_INV THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(&2 * C / sqrt tau1) * t pow 2 = (C * &4 * t pow 2) * inv(&2 * sqrt tau1)`
  SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < sqrt tau1` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The two results for a general chart c of the atlas.                       *)
(* ------------------------------------------------------------------------- *)

let P2AW_LX_LOCLIP = prove
 (`!top atlas a b (g:real->A->real^3^3) m p (c:(A->bool)#(A->real^3)).
     p2a_cbflow (top,atlas) a b g /\ p IN topspace top /\ c IN atlas /\
     (!t y. a <= t /\ t <= b /\ y IN topspace top ==> m <= mfd_scalar atlas (g t) y) /\
     (!z. z IN p2bw_cdom c (b - a)
          ==> ?gamma. p2a_min (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p
                              (drop(sndcart z)) gamma /\
                      gamma(drop(sndcart z)) = chart_inv c (fstcart z))
     ==> wan_loclip (p2bw_cdom c (b - a))
                    (p2bw_cfun c (p2a_lx (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p))`,
  REWRITE_TAC[FORALL_PAIR_THM; P2AW_LX_LOCLIP_UPHI]);;

let P2AW_LX_SEMICONC = prove
 (`!top atlas a b (g:real->A->real^3^3) m p (c:(A->bool)#(A->real^3)).
     p2a_cbflow (top,atlas) a b g /\ p IN topspace top /\ c IN atlas /\
     (!t y. a <= t /\ t <= b /\ y IN topspace top ==> m <= mfd_scalar atlas (g t) y) /\
     (!z. z IN p2bw_cdom c (b - a)
          ==> ?gamma. p2a_min (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p
                              (drop(sndcart z)) gamma /\
                      gamma(drop(sndcart z)) = chart_inv c (fstcart z))
     ==> !kk. compact kk /\ kk SUBSET p2bw_cdom c (b - a)
              ==> ?C d. &0 < d /\
                        !x v t. x IN kk /\ norm v <= &2 /\ abs t < d
                                ==> p2bw_cfun c
                                      (p2a_lx (p2a_flow_view (top,atlas) (real_interval[a,b]) g)
                                              b p) (x + t % pastecart v (vec 0)) +
                                    p2bw_cfun c
                                      (p2a_lx (p2a_flow_view (top,atlas) (real_interval[a,b]) g)
                                              b p) (x - t % pastecart v (vec 0)) -
                                    &2 * p2bw_cfun c
                                           (p2a_lx (p2a_flow_view (top,atlas)
                                                      (real_interval[a,b]) g) b p) x
                                    <= C * t pow 2`,
  REWRITE_TAC[FORALL_PAIR_THM; P2AW_LX_SEMICONC_UPHI]);;

