(* ========================================================================= *)
(* Unit pc_pde_st: space-time calculus, time first.  A point of space-time  *)
(* is pastecart (lift t) y : real^(1,N)finite_sum; coordinate 1 is time and  *)
(* coordinate 1 + k is the space coordinate k.  Partials of time slices,     *)
(* time derivatives of space slices, open time half-spaces, one-sided limits *)
(* at a time t = b, uniform continuity in time on compact sets of space      *)
(* points.  (Shared by pc_rf_glue and the PDE layer.)                        *)
(* ========================================================================= *)

needs "src/pc_pde_seeley.ml";;

prioritize_real();;
type_invention_error := true;;

let PDE_ST_BASIS_SPACE = prove
 (`!k. 1 <= k /\ k <= dimindex(:N)
       ==> basis(1 + k):real^(1,N)finite_sum = pastecart (vec 0) (basis k)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `k:num` (INST_TYPE [`:1`,`:M`] TEXT_BASIS_HIGH)) THEN
  ASM_REWRITE_TAC[DIMINDEX_1] THEN STRIP_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM PASTECART_FST_SND] THEN ASM_REWRITE_TAC[]);;

let PDE_ST_BASIS_TIME = prove
 (`basis 1:real^(1,N)finite_sum = pastecart (lift(&1)) (vec 0)`,
  MP_TAC(ISPEC `1` (INST_TYPE [`:1`,`:M`] TEXT_BASIS_LOW)) THEN
  REWRITE_TAC[DIMINDEX_1; LE_REFL] THEN STRIP_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM PASTECART_FST_SND] THEN
  ASM_REWRITE_TAC[PDE_BASIS1_REAL1]);;

let PDE_ST_SLICE_PARTIAL = prove
 (`!(f:real^(1,N)finite_sum->real^P) c y k.
        f differentiable (at (pastecart c y)) /\ 1 <= k /\ k <= dimindex(:N)
        ==> partial_derivative k (\y. f(pastecart c y)) y =
            partial_derivative (1 + k) f (pastecart c y)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\y:real^N. (f:real^(1,N)finite_sum->real^P)(pastecart c y)) =
                f o (\y. pastecart c y)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `((\y:real^N. pastecart (c:real^1) y) has_derivative
                 (\h. pastecart (vec 0) h)) (at y)` ASSUME_TAC THENL
   [MATCH_MP_TAC HAS_DERIVATIVE_PASTECART THEN
    REWRITE_TAC[HAS_DERIVATIVE_CONST; HAS_DERIVATIVE_ID];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:num`; `\y:real^N. pastecart (c:real^1) y`;
                 `f:real^(1,N)finite_sum->real^P`; `y:real^N`]
                PARTIAL_DERIVATIVE_CHAIN) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[differentiable]; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[partial_derivative] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
  ASM_SIMP_TAC[PDE_ST_BASIS_SPACE]);;

let PDE_ST_TIME_DERIV = prove
 (`!(f:real^(1,N)finite_sum->real^P) t y.
        f differentiable (at (pastecart (lift t) y))
        ==> ((\r. f(pastecart r y)) has_vector_derivative
             partial_derivative 1 f (pastecart (lift t) y)) (at (lift t))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> ASSUME_TAC(MATCH_MP LINEAR_FRECHET_DERIVATIVE th) THEN
                       ASSUME_TAC(REWRITE_RULE[FRECHET_DERIVATIVE_WORKS] th)) THEN
  REWRITE_TAC[has_vector_derivative; partial_derivative] THEN
  SUBGOAL_THEN `(\r:real^1. (f:real^(1,N)finite_sum->real^P)(pastecart r y)) =
                f o (\r. pastecart r y)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(\h:real^1. drop h % frechet_derivative (f:real^(1,N)finite_sum->real^P)
                           (at (pastecart (lift t) y)) (basis 1)) =
    frechet_derivative f (at (pastecart (lift t) y)) o (\h. pastecart h (vec 0))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; PDE_ST_BASIS_TIME] THEN X_GEN_TAC `h:real^1` THEN
    SUBGOAL_THEN `pastecart (h:real^1) (vec 0:real^N) = drop h % pastecart (lift(&1)) (vec 0)`
    SUBST1_TAC THENL
     [REWRITE_TAC[PASTECART_EQ; FSTCART_PASTECART; SNDCART_PASTECART; FSTCART_CMUL;
                  SNDCART_CMUL; VECTOR_MUL_RZERO; GSYM LIFT_CMUL; REAL_MUL_RID; LIFT_DROP];
      ALL_TAC] THEN
    CONV_TAC SYM_CONV THEN FIRST_ASSUM(MATCH_ACCEPT_TAC o MATCH_MP LINEAR_CMUL);
    ALL_TAC] THEN
  MATCH_MP_TAC DIFF_CHAIN_AT THEN CONJ_TAC THENL
   [MATCH_MP_TAC HAS_DERIVATIVE_PASTECART THEN
    REWRITE_TAC[HAS_DERIVATIVE_CONST; HAS_DERIVATIVE_ID];
    ASM_REWRITE_TAC[]]);;

let PDE_ST_TIME_REAL_DERIV = prove
 (`!(f:real^(1,N)finite_sum->real^1) t y.
        f differentiable (at (pastecart (lift t) y))
        ==> ((\s. drop(f(pastecart (lift s) y))) has_real_derivative
             drop(partial_derivative 1 f (pastecart (lift t) y))) (atreal t)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[HAS_REAL_VECTOR_DERIVATIVE_AT; o_DEF; LIFT_DROP] THEN
  REWRITE_TAC[ETA_AX] THEN ASM_SIMP_TAC[PDE_ST_TIME_DERIV]);;

let PDE_ST_SLICE_OPEN = prove
 (`!(S:real^(1,N)finite_sum->bool) c. open S ==> open {y | pastecart c y IN S}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE_UNIV THEN
  ASM_REWRITE_TAC[] THEN GEN_TAC THEN
  MATCH_MP_TAC CONTINUOUS_PASTECART THEN
  REWRITE_TAC[CONTINUOUS_CONST; CONTINUOUS_AT_ID]);;

let PDE_ST_SLICE_ITERATED = prove
 (`!l (f:real^(1,N)finite_sum->real^P) S c y.
        open S /\ smooth_map_on S f /\ pastecart c y IN S /\
        ALL (\k. 1 <= k /\ k <= dimindex(:N)) l
        ==> iterated_partial l (\y. f(pastecart c y)) y =
            iterated_partial (MAP (\k. 1 + k) l) f (pastecart c y)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[iterated_partial; MAP; ALL] THEN
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `partial_derivative h
                (\y. iterated_partial (MAP (\k. 1 + k) t) (f:real^(1,N)finite_sum->real^P)
                                      (pastecart c y)) y` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC PARTIAL_DERIVATIVE_LOCAL_OPEN THEN
    EXISTS_TAC `{y:real^N | pastecart c y IN (S:real^(1,N)finite_sum->bool)}` THEN
    ASM_SIMP_TAC[PDE_ST_SLICE_OPEN; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `S:real^(1,N)finite_sum->bool` THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC PDE_ST_SLICE_PARTIAL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `S:real^(1,N)finite_sum->bool` THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_ITERATED_PARTIAL]]);;

let PDE_ST_OPEN_TIME_LT = prove
 (`!b. open {z:real^(1,N)finite_sum | drop(fstcart z) < b}`,
  GEN_TAC THEN
  MP_TAC(ISPECL [`fstcart:real^(1,N)finite_sum->real^1`; `{y:real^1 | y$1 < b}`]
         CONTINUOUS_OPEN_PREIMAGE_UNIV) THEN
  REWRITE_TAC[OPEN_HALFSPACE_COMPONENT_LT; IN_ELIM_THM; drop] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  GEN_TAC THEN MATCH_MP_TAC LINEAR_CONTINUOUS_AT THEN REWRITE_TAC[LINEAR_FSTCART]);;

let PDE_ST_OPEN_TIME_GT = prove
 (`!b. open {z:real^(1,N)finite_sum | b < drop(fstcart z)}`,
  GEN_TAC THEN
  MP_TAC(ISPECL [`fstcart:real^(1,N)finite_sum->real^1`; `{y:real^1 | y$1 > b}`]
         CONTINUOUS_OPEN_PREIMAGE_UNIV) THEN
  REWRITE_TAC[OPEN_HALFSPACE_COMPONENT_GT; IN_ELIM_THM; drop; real_gt] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  GEN_TAC THEN MATCH_MP_TAC LINEAR_CONTINUOUS_AT THEN REWRITE_TAC[LINEAR_FSTCART]);;

let PDE_ST_TIME_DIST = prove
 (`!y z:real^(1,N)finite_sum. abs(drop(fstcart y) - drop(fstcart z)) <= norm(y - z)`,
  REPEAT GEN_TAC THEN MP_TAC(ISPEC `y - z:real^(1,N)finite_sum` NORM_FSTCART) THEN
  REWRITE_TAC[FSTCART_SUB; NORM_REAL; GSYM drop; DROP_SUB]);;

let PDE_ST_PASTECART_DIST = prove
 (`!s t (y:real^N).
        norm(pastecart (lift s) y - pastecart (lift t) y:real^(1,N)finite_sum) = abs(s - t)`,
  REWRITE_TAC[PASTECART_SUB; VECTOR_SUB_REFL; NORM_PASTECART_0; GSYM LIFT_SUB; NORM_LIFT]);;

let PDE_ST_RIGHT_EQ = prove
 (`!(f:real^(1,N)finite_sum->real^K) g b c y.
        b < c /\
        f continuous (at (pastecart (lift b) y)) /\
        g continuous (at (pastecart (lift b) y)) /\
        (!s. b < s /\ s < c ==> f(pastecart (lift s) y) = g(pastecart (lift s) y))
        ==> f(pastecart (lift b) y) = g(pastecart (lift b) y)`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `(f:real^(1,N)finite_sum->real^K)(pastecart (lift b) y) =
                 g(pastecart (lift b) y)` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(\z. (f:real^(1,N)finite_sum->real^K) z - g z) continuous
                (at (pastecart (lift b) (y:real^N)))` MP_TAC THENL
   [ASM_SIMP_TAC[CONTINUOUS_SUB]; ALL_TAC] THEN
  REWRITE_TAC[continuous_at] THEN
  DISCH_THEN(MP_TAC o SPEC `norm((f:real^(1,N)finite_sum->real^K)(pastecart (lift b) y) -
                                 g(pastecart (lift b) y))`) THEN
  ASM_REWRITE_TAC[NORM_POS_LT; VECTOR_SUB_EQ] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `pastecart (lift(b + min d (c - b) / &2)) (y:real^N)`) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[dist; PDE_ST_PASTECART_DIST] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(f:real^(1,N)finite_sum->real^K)(pastecart (lift(b + min d (c - b) / &2)) y) =
                g(pastecart (lift(b + min d (c - b) / &2)) y)` SUBST1_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[dist; VECTOR_SUB_REFL; VECTOR_SUB_LZERO; NORM_NEG; REAL_LT_REFL]);;

let PDE_ST_UNIFORM_LEFT = prove
 (`!(f:real^(1,N)finite_sum->real^K) b e c (W:real^N->bool) K.
        &0 < e /\ b < c /\
        f continuous_on (interval(lift(b - e),lift c) PCROSS W) /\
        compact K /\ K SUBSET W
        ==> !eps. &0 < eps
                  ==> ?d. &0 < d /\
                          !t y. b - d < t /\ t <= b /\ y IN K
                                ==> norm(f(pastecart (lift t) y) -
                                         f(pastecart (lift b) y)) < eps`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `eps:real` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`f:real^(1,N)finite_sum->real^K`;
                 `interval[lift(b - e / &2),lift b] PCROSS (K:real^N->bool)`]
                COMPACT_UNIFORMLY_CONTINUOUS) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[COMPACT_PCROSS; COMPACT_INTERVAL] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `interval(lift(b - e),lift c) PCROSS (W:real^N->bool)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PCROSS_MONO THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET_INTERVAL_1; LIFT_DROP] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[uniformly_continuous_on] THEN DISCH_THEN(MP_TAC o SPEC `eps:real`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `min d (e / &2)` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `y:real^N`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`pastecart (lift b) (y:real^N)`;
                                `pastecart (lift t) (y:real^N)`]) THEN
  REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP; dist; PDE_ST_PASTECART_DIST] THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REWRITE_TAC[]]);;

