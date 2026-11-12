(* ========================================================================= *)
(* pc_wan_sob2: W^(1,2) calculus. Removable points (the weak equation across *)
(* a point and W^(1,2) itself, dimension >= 2), local smooth approximation   *)
(* and closure of weak derivatives, the chain rule through C^1 maps with     *)
(* bounded derivative, Stampacchia's theorem (weak derivatives vanish a.e.   *)
(* on the zero set), zero traces of continuous maps on balls, gluing.        *)
(* Statement constants: pc_wan_defs (CHAIN_W12, W120_CONT, GLUE_W12),        *)
(* pc_wan_p4defs (REMOVABLE_POINT), pc_wan_p4defs2 (REMOVABLE_POINT_WEAK).   *)
(* Sources: Evans PDE 2nd ed. 5.2-5.5; Gilbarg-Trudinger Lemma 7.7           *)
(* (Stampacchia).                                                            *)
(* ========================================================================= *)

needs "src/pc_wan_lipx.ml";;
needs "src/pc_wan_p4defs2.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* The point cutoff b_e(x) = smooth_bump e (2 e) (x - a): smooth, values in  *)
(* [0,1], 1 on cball(a,e), 0 outside ball(a,2e), |D b_e| <= B/e, and for     *)
(* N >= 2 the L^2 norms of its partials are bounded uniformly in e <= 1.     *)
(* ------------------------------------------------------------------------- *)

let WAN_SMOOTH_BUMP_SCALE = prove
 (`!e (z:real^N). &0 < e ==> smooth_bump e (&2 * e) z = smooth_bump (&1) (&2) (inv e % z)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[smooth_bump; NORM_MUL; REAL_POW_MUL; REAL_ABS_INV] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < e ==> abs e = e`] THEN AP_TERM_TAC THEN
  UNDISCH_TAC `&0 < e` THEN CONV_TAC REAL_FIELD);;

let WAN_BUMP12_DERIV_BOUND = prove
 (`?B. &0 <= B /\
       !(z:real^N) h.
         abs(drop(frechet_derivative (\y. lift(smooth_bump (&1) (&2) y)) (at z) h))
         <= B * norm h`,
  MP_TAC(ISPECL [`\y:real^N. smooth_bump (&1) (&2) y`; `cball(vec 0:real^N,&2)`]
                WAN_SMOOTH_SUPPORT_BOUNDS) THEN
  REWRITE_TAC[COMPACT_CBALL; IN_CBALL_0] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_BUMP_SMOOTH THEN REAL_ARITH_TAC;
      REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_BUMP_0 THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `B:real` o CONJUNCT2) THEN
  EXISTS_TAC `abs B` THEN REWRITE_TAC[REAL_ABS_POS] THEN
  REPEAT GEN_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `B * norm(h:real^N)` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE] THEN REAL_ARITH_TAC);;

let WAN_NORM_BASIS_LE = prove
 (`!i. norm(basis i:real^N) <= &1`,
  GEN_TAC THEN ASM_CASES_TAC `1 <= i /\ i <= dimindex(:N)` THENL
   [ASM_SIMP_TAC[NORM_BASIS; REAL_LE_REFL];
    SUBGOAL_THEN `basis i:real^N = vec 0` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[BASIS_EQ_0; IN_NUMSEG]; REWRITE_TAC[NORM_0; REAL_POS]]]);;

let WAN_POINT_CUTOFF_DERIV = prove
 (`!(a:real^N) e x.
     &0 < e
     ==> ((\y. lift(smooth_bump e (&2 * e) (y - a))) has_derivative
          (\h. frechet_derivative (\y. lift(smooth_bump (&1) (&2) y)) (at (inv e % (x - a)))
                 (inv e % h))) (at x)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `(\y. lift(smooth_bump e (&2 * e) (y - a:real^N))) =
    (\y. lift(smooth_bump (&1) (&2) y)) o (\y. inv e % (y - a))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM] THEN ASM_SIMP_TAC[WAN_SMOOTH_BUMP_SCALE]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(\h. frechet_derivative (\y. lift(smooth_bump (&1) (&2) y)) (at (inv e % (x - a)))
           (inv e % h)) =
    frechet_derivative (\y. lift(smooth_bump (&1) (&2) y))
      (at ((\y. inv e % (y - a:real^N)) x)) o (\h. inv e % h)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC DIFF_CHAIN_AT THEN CONJ_TAC THENL
   [MATCH_MP_TAC HAS_DERIVATIVE_CMUL THEN
    MP_TAC(ISPECL [`\y:real^N. y`; `\h:real^N. h`; `\y:real^N. a:real^N`;
                   `\h:real^N. vec 0:real^N`; `at (x:real^N)`] HAS_DERIVATIVE_SUB) THEN
    REWRITE_TAC[HAS_DERIVATIVE_ID; HAS_DERIVATIVE_CONST; VECTOR_SUB_RZERO];
    REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `(:real^N)` THEN
    REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN MATCH_MP_TAC SMOOTH_BUMP_SMOOTH THEN
    REAL_ARITH_TAC]);;

let WAN_POINT_CUTOFF_FACTS = prove
 (`!(a:real^N) e.
     &0 < e
     ==> smooth_map_on (:real^N) (\x. lift(smooth_bump e (&2 * e) (x - a))) /\
         (!x. &0 <= smooth_bump e (&2 * e) (x - a) /\ smooth_bump e (&2 * e) (x - a) <= &1) /\
         (!x. norm(x - a) <= e ==> smooth_bump e (&2 * e) (x - a) = &1) /\
         (!x. &2 * e <= norm(x - a) ==> smooth_bump e (&2 * e) (x - a) = &0)`,
  REPEAT STRIP_TAC THENL
   [MP_TAC(ISPECL [`\x:real^N. lift(smooth_bump e (&2 * e) x)`; `--a:real^N`]
                  PDE_SMOOTH_TRANSLATE) THEN
    ASM_SIMP_TAC[SMOOTH_BUMP_SMOOTH; VECTOR_ARITH `x + --c:real^N = x - c`;
                 REAL_ARITH `&0 < e ==> &0 <= e /\ e < &2 * e`];
    REWRITE_TAC[SMOOTH_BUMP_BOUNDS];
    REWRITE_TAC[SMOOTH_BUMP_BOUNDS];
    MATCH_MP_TAC SMOOTH_BUMP_1 THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC SMOOTH_BUMP_0 THEN ASM_REAL_ARITH_TAC]);;

let WAN_POINT_CUTOFF_DBOUND = prove
 (`?B. &0 <= B /\
       !(a:real^N) e x h.
         &0 < e
         ==> abs(drop(frechet_derivative (\y. lift(smooth_bump e (&2 * e) (y - a))) (at x) h))
             <= B / e * norm h`,
  X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC (INST_TYPE [`:N`,`:N`] WAN_BUMP12_DERIV_BOUND) THEN
  EXISTS_TAC `B:real` THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`a:real^N`; `e:real`; `x:real^N`] WAN_POINT_CUTOFF_DERIV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
  REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `B * norm(inv e % h:real^N)` THEN ASM_REWRITE_TAC[NORM_MUL] THEN
  ASM_SIMP_TAC[REAL_ABS_INV; REAL_ARITH `&0 < e ==> abs e = e`; real_div; REAL_MUL_ASSOC;
               REAL_LE_REFL]);;

let WAN_POINT_CUTOFF_TEST = prove
 (`!(a:real^N) e.
     &0 < e ==> wan_test (:real^N) (\y. smooth_bump e (&2 * e) (y - a))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`a:real^N`; `e:real`] WAN_POINT_CUTOFF_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[wan_test] THEN ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `cball(a:real^N,&2 * e)` THEN
  REWRITE_TAC[COMPACT_CBALL; SUBSET_UNIV; IN_CBALL; dist] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ONCE_REWRITE_TAC[NORM_SUB] THEN ASM_REAL_ARITH_TAC);;

let WAN_POINT_CUTOFF_L2 = prove
 (`?C. &0 <= C /\
       !(a:real^N) e i.
         &0 < e /\ e <= &1 /\ 2 <= dimindex(:N)
         ==> (\x. lift(wan_dpart i (\y. smooth_bump e (&2 * e) (y - a)) x pow 2))
               integrable_on (:real^N) /\
             drop(integral (:real^N)
                    (\x. lift(wan_dpart i (\y. smooth_bump e (&2 * e) (y - a)) x pow 2)))
             <= C`,
  X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC (INST_TYPE [`:N`,`:N`] WAN_POINT_CUTOFF_DBOUND) THEN
  EXISTS_TAC `B pow 2 * &4 pow dimindex(:N)` THEN
  SIMP_TAC[REAL_LE_MUL; REAL_POW_LE; REAL_POS; REAL_LE_POW_2] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`a:real^N`; `e:real`] WAN_POINT_CUTOFF_TEST) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `b = \y:real^N. smooth_bump e (&2 * e) (y - a)` THEN
  SUBGOAL_THEN `!x. abs(wan_dpart i (b:real^N->real) x) <= B / e` ASSUME_TAC THENL
   [X_GEN_TAC `x:real^N` THEN EXPAND_TAC "b" THEN REWRITE_TAC[wan_dpart] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `B / e * norm(basis i:real^N)` THEN
    ASM_SIMP_TAC[] THEN GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[WAN_NORM_BASIS_LE] THEN
    MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!x. ~(x IN cball(a:real^N,&2 * e)) ==> wan_dpart i (b:real^N->real) x = &0`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC WAN_TEST_DPART_ZERO THEN
    EXISTS_TAC `cball(a:real^N,&2 * e)` THEN ASM_REWRITE_TAC[COMPACT_CBALL] THEN
    UNDISCH_TAC `wan_test (:real^N) b` THEN REWRITE_TAC[wan_test] THEN
    DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "b" THEN REWRITE_TAC[IN_CBALL; dist] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC SMOOTH_BUMP_0 THEN ONCE_REWRITE_TAC[NORM_SUB] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
   [MATCH_MP_TAC WAN_CONT_SUPPORT_INTEGRABLE THEN EXISTS_TAC `cball(a:real^N,&2 * e)` THEN
    ASM_SIMP_TAC[COMPACT_CBALL; REAL_POW_2; REAL_MUL_LZERO; LIFT_NUM] THEN
    MATCH_MP_TAC WAN_CONT_LIFT_MUL THEN
    ASM_MESON_TAC[WAN_TEST_CONTINUOUS];
    DISCH_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `drop(integral (:real^N)
                 (\x. if x IN cball(a:real^N,&2 * e) then lift((B / e) pow 2) else vec 0))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRAL_DROP_LE THEN ASM_SIMP_TAC[WAN_INDICATOR_CONST_INTEGRABLE; COMPACT_CBALL] THEN
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN COND_CASES_TAC THENL
     [REWRITE_TAC[LIFT_DROP; GSYM REAL_LE_SQUARE_ABS] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `B / e` THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      ASM_SIMP_TAC[LIFT_DROP; DROP_VEC] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[INTEGRAL_RESTRICT_UNIV] THEN
  SIMP_TAC[INTEGRAL_CONST_GEN; MEASURABLE_CBALL; DROP_CMUL; LIFT_DROP] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(&4 * e) pow dimindex(:N) * (B / e) pow 2` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
    MP_TAC(ISPECL [`a:real^N`; `&2 * e`] MEASURE_CBALL_BOUND) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REWRITE_TAC[REAL_ARITH `&2 * &2 * e = &4 * e`]];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_POW_MUL; REAL_POW_DIV] THEN
  SUBGOAL_THEN `e pow dimindex(:N) <= e pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_MONO_INV THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < e pow 2` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(&4 pow dimindex(:N) * e pow 2) * B pow 2 / e pow 2` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_SIMP_TAC[REAL_LE_DIV; REAL_LE_POW_2; REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_POW_LE; REAL_POS];
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN UNDISCH_TAC `&0 < e pow 2` THEN CONV_TAC REAL_FIELD]);;

(* ------------------------------------------------------------------------- *)
(* Products of absolutely integrable functions with bounded continuous ones; *)
(* the radii e_n = d0 / (n + 1); AM-GM; a product of L^2-bounded functions   *)
(* supported in shrinking sets with a fixed L^2 function tends to 0.         *)
(* ------------------------------------------------------------------------- *)

let WAN_ABS_INT_CONT_MUL = prove
 (`!(s:real^N->bool) (c:real^N->real) (w:real^N->real) M.
     lebesgue_measurable s /\ (\x. lift(c x)) continuous_on (:real^N) /\
     (!x. abs(c x) <= M) /\ (\x. lift(w x)) absolutely_integrable_on s
     ==> (\x. lift(c x * w x)) absolutely_integrable_on s`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\x y. lift(drop x * drop y)`; `\x:real^N. lift(c x)`;
                 `\x:real^N. lift(w x)`; `s:real^N->bool`]
                ABSOLUTELY_INTEGRABLE_BOUNDED_MEASURABLE_PRODUCT) THEN
  REWRITE_TAC[BILINEAR_LIFT_MUL; LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
    ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_UNIV];
    REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE; NORM_LIFT] THEN
    EXISTS_TAC `abs M + &1` THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N`) THEN REAL_ARITH_TAC]);;

let WAN_ABS_INT_CONT_DOT = prove
 (`!(s:real^N->bool) (P:real^N->real^K) (A:real^N->real^K) M.
     lebesgue_measurable s /\ P continuous_on (:real^N) /\
     (!x. norm(P x) <= M) /\ A absolutely_integrable_on s
     ==> (\x. lift(A x dot P x)) absolutely_integrable_on s`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[DOT_SYM] THEN
  MP_TAC(ISPECL [`\x y:real^K. lift(x dot y)`; `P:real^N->real^K`;
                 `A:real^N->real^K`; `s:real^N->bool`]
                ABSOLUTELY_INTEGRABLE_BOUNDED_MEASURABLE_PRODUCT) THEN
  REWRITE_TAC[BILINEAR_DOT] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
    ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_UNIV];
    REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE] THEN
    EXISTS_TAC `abs M + &1` THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N`) THEN REAL_ARITH_TAC]);;

let WAN_CONT_SUPPORT_BOUNDED = prove
 (`!(P:real^N->real^K) k.
     P continuous_on (:real^N) /\ compact k /\ (!x. ~(x IN k) ==> P x = vec 0)
     ==> ?M. !x. norm(P x) <= M`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`P:real^N->real^K`; `k:real^N->bool`] COMPACT_CONTINUOUS_IMAGE) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_UNIV]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
  REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `M:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `M:real` THEN X_GEN_TAC `x:real^N` THEN
  ASM_CASES_TAC `(x:real^N) IN k` THEN ASM_SIMP_TAC[NORM_0; REAL_LT_IMP_LE]);;

let WAN_LLOC_DOT_CONT_SUPPORT = prove
 (`!(s:real^N->bool) (A:real^N->real^K) (P:real^N->real^K) k.
     wan_lloc s A /\ P continuous_on (:real^N) /\ compact k /\ k SUBSET s /\
     (!x. ~(x IN k) ==> P x = vec 0)
     ==> (\x. lift(A x dot P x)) absolutely_integrable_on s`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`P:real^N->real^K`; `k:real^N->bool`] WAN_CONT_SUPPORT_BOUNDED) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `M:real`) THEN
  SUBGOAL_THEN `(\x. lift((A:real^N->real^K) x dot P x)) absolutely_integrable_on k`
  MP_TAC THENL
   [MATCH_MP_TAC WAN_ABS_INT_CONT_DOT THEN EXISTS_TAC `M:real` THEN
    ASM_SIMP_TAC[LEBESGUE_MEASURABLE_COMPACT] THEN
    UNDISCH_TAC `wan_lloc s (A:real^N->real^K)` THEN REWRITE_TAC[wan_lloc] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[GSYM ABSOLUTELY_INTEGRABLE_RESTRICT_UNIV] THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `x:real^N` THEN
  ASM_CASES_TAC `(x:real^N) IN k` THENL
   [SUBGOAL_THEN `(x:real^N) IN s` (fun th -> ASM_REWRITE_TAC[th]) THEN ASM SET_TAC[];
    ASM_SIMP_TAC[DOT_RZERO; LIFT_NUM; COND_ID]]);;

let WAN_EN_FACTS = prove
 (`!d0 n. &0 < d0 ==> &0 < d0 * inv(&n + &1) /\ d0 * inv(&n + &1) <= d0`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[REAL_LT_INV_EQ] THEN REAL_ARITH_TAC;
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC REAL_INV_LE_1 THEN REAL_ARITH_TAC]);;

let WAN_CUTOFF_SEQ = prove
 (`!d0 (a:real^N) x.
     &0 < d0 /\ ~(x = a)
     ==> ?N. !n. N <= n ==> &2 * (d0 * inv(&n + &1)) < norm(x - a)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < norm(x - a:real^N)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT; VECTOR_SUB_EQ]; ALL_TAC] THEN
  MP_TAC(SPEC `(&2 * d0) / norm(x - a:real^N)` REAL_ARCH_SIMPLE) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN DISCH_TAC THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(&2 * d0) / norm(x - a:real^N) < &n + &1` MP_TAC THENL
   [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `&N` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `N:num <= n` THEN REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN DISCH_TAC THEN
  REWRITE_TAC[REAL_ARITH `&2 * (d0 * inv(&n + &1)) = (&2 * d0) / (&n + &1)`] THEN
  ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_ARITH `&0 < &n + &1`] THEN ASM_REAL_ARITH_TAC);;

let WAN_AMGM_ABS = prove
 (`!t g h. &0 < t /\ &0 <= h ==> abs g * h <= t * g pow 2 + h pow 2 / t`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `abs g * h = (t * abs g * h) / t` SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < t` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  SUBGOAL_THEN `t * g pow 2 + h pow 2 / t = (t pow 2 * abs g pow 2 + h pow 2) / t`
  SUBST1_TAC THENL
   [REWRITE_TAC[REAL_POW2_ABS] THEN UNDISCH_TAC `&0 < t` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_DIV2_EQ] THEN
  MP_TAC(SPEC `t * abs g - h` REAL_LE_POW_2) THEN
  SUBGOAL_THEN `&0 <= t * abs g * h` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_ABS_POS];
    ALL_TAC] THEN
  REAL_ARITH_TAC);;

let WAN_L2_SHRINKING_PRODUCT = prove
 (`!(g:num->real^N->real) (k:real^N->real) (h:real^N->real) (B:num->real^N->bool) C.
     &0 <= C /\
     (!n. (\x. lift(g n x pow 2)) integrable_on (:real^N) /\
          drop(integral (:real^N) (\x. lift(g n x pow 2))) <= C) /\
     (!n x. ~(x IN B n) ==> g n x = &0) /\
     (!n. (\x. lift(g n x * k x)) integrable_on (:real^N)) /\
     (!x. abs(k x) <= h x) /\
     (!n. (\x. if x IN B n then lift(h x pow 2) else vec 0) integrable_on (:real^N)) /\
     ((\n. integral (:real^N) (\x. if x IN B n then lift(h x pow 2) else vec 0)) --> vec 0)
       sequentially
     ==> ((\n. integral (:real^N) (\x. lift(g n x * k x))) --> vec 0) sequentially`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "lim"))))))) THEN
  REWRITE_TAC[LIM_SEQUENTIALLY; DIST_0] THEN X_GEN_TAC `eps:real` THEN DISCH_TAC THEN
  ABBREV_TAC `t = eps / (&2 * (C + &1))` THEN
  SUBGOAL_THEN `&0 < t` ASSUME_TAC THENL
   [EXPAND_TAC "t" THEN MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `t * C < eps / &2` ASSUME_TAC THENL
   [SUBGOAL_THEN `t * C = eps / &2 - t` SUBST1_TAC THENL
     [EXPAND_TAC "t" THEN MATCH_MP_TAC(REAL_FIELD
       `~(C + &1 = &0) ==> eps / (&2 * (C + &1)) * C = eps / &2 - eps / (&2 * (C + &1))`) THEN
      ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REMOVE_THEN "lim" (MP_TAC o GEN_REWRITE_RULE I [LIM_SEQUENTIALLY]) THEN
  REWRITE_TAC[DIST_0] THEN DISCH_THEN(MP_TAC o SPEC `eps * t / &2`) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN DISCH_TAC THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `!x:real^N. &0 <= h x` ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `abs((k:real^N->real) x)` THEN
    ASM_REWRITE_TAC[REAL_ABS_POS];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `drop(integral (:real^N)
                 (\x. lift(t * (g:num->real^N->real) n x pow 2) +
                      inv t % (if x IN (B:num->real^N->bool) n then lift(h x pow 2) else vec 0)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRAL_NORM_BOUND_INTEGRAL THEN ASM_REWRITE_TAC[IN_UNIV] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC INTEGRABLE_ADD THEN REWRITE_TAC[LIFT_CMUL] THEN CONJ_TAC THEN
      MATCH_MP_TAC INTEGRABLE_CMUL THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    X_GEN_TAC `x:real^N` THEN
    ASM_CASES_TAC `(x:real^N) IN B(n:num)` THEN
    ASM_SIMP_TAC[DROP_ADD; DROP_CMUL; LIFT_DROP; DROP_VEC; NORM_LIFT; REAL_ABS_MUL] THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `abs((g:num->real^N->real) n x) * h x` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_ABS_POS];
        MP_TAC(SPECL [`t:real`; `(g:num->real^N->real) n x`; `(h:real^N->real) x`]
                     WAN_AMGM_ABS) THEN
        ASM_REWRITE_TAC[real_div] THEN REAL_ARITH_TAC];
      REWRITE_TAC[REAL_ABS_0; REAL_MUL_LZERO; REAL_POW_2; REAL_MUL_RZERO; REAL_ADD_LID;
                  REAL_LE_REFL]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\x. lift(t * (g:num->real^N->real) n x pow 2)`;
                 `\x. inv t % (if x IN (B:num->real^N->bool) n then lift((h:real^N->real) x pow 2) else vec 0)`;
                 `(:real^N)`] INTEGRAL_ADD) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [REWRITE_TAC[LIFT_CMUL] THEN CONJ_TAC THEN
    MATCH_MP_TAC INTEGRABLE_CMUL THEN ASM_REWRITE_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[LIFT_CMUL] THEN
  ASM_SIMP_TAC[INTEGRAL_CMUL; DROP_ADD; DROP_CMUL] THEN
  MATCH_MP_TAC(REAL_ARITH `a <= t * C /\ b <= eps / &2 /\ t * C < eps / &2 ==> a + b < eps`) THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `inv t * (eps * t / &2)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC REAL_LT_IMP_LE THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `norm(integral (:real^N)
                  (\x. if x IN B(n:num) then lift((h:real^N->real) x pow 2) else vec 0))` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[NORM_1] THEN REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN UNDISCH_TAC `&0 < t` THEN CONV_TAC REAL_FIELD]);;

let WAN_SMALL_BALL_L2 = prove
 (`!(A:real^N->real^K) a r0 (r:num->real).
     A IN lspace (cball(a,r0)) (&2) /\ (!n. r n <= r0) /\
     (!x. ~(x = a) ==> ?N. !n. N <= n ==> r n < norm(x - a))
     ==> (!n. (\x. if x IN cball(a,r n) then lift(norm(A x) pow 2) else vec 0)
                integrable_on (:real^N)) /\
         ((\n. integral (:real^N)
                 (\x. if x IN cball(a,r n) then lift(norm(A x) pow 2) else vec 0)) --> vec 0)
         sequentially`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!d. d <= r0
        ==> (\x. if x IN cball(a,d) then lift(norm((A:real^N->real^K) x) pow 2) else vec 0)
              integrable_on (:real^N)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[INTEGRABLE_RESTRICT_UNIV] THEN
    MATCH_MP_TAC WAN_LSPACE2_SQNORM_INTEGRABLE THEN
    MATCH_MP_TAC LSPACE_SUBSET THEN EXISTS_TAC `cball(a:real^N,r0)` THEN
    ASM_SIMP_TAC[SUBSET_CBALL; LEBESGUE_MEASURABLE_CLOSED; CLOSED_CBALL];
    ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[]; DISCH_TAC] THEN
  MP_TAC(ISPECL
   [`\n x. if x IN cball(a,(r:num->real) n) then lift(norm((A:real^N->real^K) x) pow 2)
           else vec 0`;
    `\x:real^N. vec 0:real^1`;
    `\x. if x IN cball(a,r0) then lift(norm((A:real^N->real^K) x) pow 2) else vec 0`;
    `(:real^N)`; `{a:real^N}`] DOMINATED_CONVERGENCE_AE) THEN
  REWRITE_TAC[NEGLIGIBLE_SING; INTEGRAL_0] THEN ANTS_TAC THENL
   [ALL_TAC; SIMP_TAC[]] THEN
  ASM_SIMP_TAC[REAL_LE_REFL] THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`n:num`; `x:real^N`] THEN DISCH_TAC THEN
    ASM_CASES_TAC `(x:real^N) IN cball(a,r(n:num))` THEN ASM_REWRITE_TAC[] THENL
     [SUBGOAL_THEN `(x:real^N) IN cball(a,r0)` (fun th -> REWRITE_TAC[th]) THENL
       [ASM_MESON_TAC[SUBSET_CBALL; SUBSET]; ALL_TAC] THEN
      REWRITE_TAC[NORM_LIFT; LIFT_DROP; REAL_ABS_POW; REAL_ABS_NORM; REAL_LE_REFL];
      REWRITE_TAC[NORM_0] THEN COND_CASES_TAC THEN
      REWRITE_TAC[LIFT_DROP; DROP_VEC; REAL_LE_REFL; REAL_LE_POW_2]];
    X_GEN_TAC `x:real^N` THEN REWRITE_TAC[IN_DIFF; IN_UNIV; IN_SING] THEN DISCH_TAC THEN
    MATCH_MP_TAC LIM_EVENTUALLY THEN REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N` o check (is_forall o concl)) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `~((x:real^N) IN cball(a,r(n:num)))` (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[IN_CBALL; dist; REAL_NOT_LE] THEN ONCE_REWRITE_TAC[NORM_SUB] THEN
    ASM_SIMP_TAC[]]);;

let WAN_CUTOFF_CONT = prove
 (`!(a:real^N) e.
     &0 < e
     ==> (\x. lift(smooth_bump e (&2 * e) (x - a))) continuous_on (:real^N) /\
         (\x. lift(&1 - smooth_bump e (&2 * e) (x - a))) continuous_on (:real^N)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`a:real^N`; `e:real`] WAN_POINT_CUTOFF_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN ASM_REWRITE_TAC[];
    DISCH_TAC THEN REWRITE_TAC[LIFT_SUB] THEN MATCH_MP_TAC CONTINUOUS_ON_SUB THEN
    ASM_REWRITE_TAC[CONTINUOUS_ON_CONST]]);;

let WAN_CUTOFF_GOOD_TERM = prove
 (`!(s:real^N->bool) (w:real^N->real) a d0.
     lebesgue_measurable s /\ (\x. lift(w x)) absolutely_integrable_on s /\ &0 < d0
     ==> ((\n. integral s
                 (\x. lift((&1 - smooth_bump (d0 * inv(&n + &1)) (&2 * (d0 * inv(&n + &1)))
                                    (x - a)) * w x)))
          --> integral s (\x. lift(w x))) sequentially`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`\n x. lift((&1 - smooth_bump (d0 * inv(&n + &1)) (&2 * (d0 * inv(&n + &1)))
                       (x - a:real^N)) * (w:real^N->real) x)`;
    `\x. lift((w:real^N->real) x)`; `\x. lift(abs((w:real^N->real) x))`;
    `s:real^N->bool`; `{a:real^N}`] DOMINATED_CONVERGENCE_AE) THEN
  REWRITE_TAC[NEGLIGIBLE_SING] THEN ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `n:num` THEN
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
    MATCH_MP_TAC WAN_ABS_INT_CONT_MUL THEN EXISTS_TAC `&1` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`d0:real`; `n:num`] WAN_EN_FACTS) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN
    MP_TAC(ISPECL [`a:real^N`; `d0 * inv(&n + &1)`] WAN_CUTOFF_CONT) THEN
    MP_TAC(ISPECL [`a:real^N`; `d0 * inv(&n + &1)`] WAN_POINT_CUTOFF_FACTS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `x:real^N` THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N` o check (is_conj o snd o dest_forall o concl)) THEN
    REAL_ARITH_TAC;
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
    MP_TAC(ISPECL [`\x. lift((w:real^N->real) x)`; `s:real^N->bool`]
                  ABSOLUTELY_INTEGRABLE_NORM) THEN
    ASM_REWRITE_TAC[NORM_LIFT];
    MAP_EVERY X_GEN_TAC [`n:num`; `x:real^N`] THEN DISCH_TAC THEN
    REWRITE_TAC[NORM_LIFT; LIFT_DROP; REAL_ABS_MUL] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
    MP_TAC(ISPECL [`d0 * inv(&n + &1)`; `&2 * (d0 * inv(&n + &1))`; `x - a:real^N`]
                  SMOOTH_BUMP_BOUNDS) THEN
    REAL_ARITH_TAC;
    X_GEN_TAC `x:real^N` THEN REWRITE_TAC[IN_DIFF; IN_SING] THEN STRIP_TAC THEN
    MATCH_MP_TAC LIM_EVENTUALLY THEN REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
    MP_TAC(ISPECL [`d0:real`; `a:real^N`; `x:real^N`] WAN_CUTOFF_SEQ) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN
    DISCH_TAC THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`d0:real`; `n:num`] WAN_EN_FACTS) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN
     `smooth_bump (d0 * inv(&n + &1)) (&2 * (d0 * inv(&n + &1))) (x - a:real^N) = &0`
    SUBST1_TAC THENL
     [MATCH_MP_TAC SMOOTH_BUMP_0 THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `n:num` o check (is_forall o concl)) THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_SUB_RZERO; REAL_MUL_LID]]]);;

let WAN_POINT_CUTOFF_DPART = prove
 (`?B. &0 <= B /\
       !(a:real^N) e i.
         &0 < e
         ==> (\x. lift(wan_dpart i (\y. smooth_bump e (&2 * e) (y - a)) x))
               continuous_on (:real^N) /\
             (!x. abs(wan_dpart i (\y. smooth_bump e (&2 * e) (y - a)) x) <= B / e) /\
             (!x. ~(x IN cball(a,&2 * e))
                  ==> wan_dpart i (\y. smooth_bump e (&2 * e) (y - a)) x = &0)`,
  X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC (INST_TYPE [`:N`,`:N`] WAN_POINT_CUTOFF_DBOUND) THEN
  EXISTS_TAC `B:real` THEN ASM_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`a:real^N`; `e:real`] WAN_POINT_CUTOFF_TEST) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`(:real^N)`; `\y:real^N. smooth_bump e (&2 * e) (y - a)`; `i:num`]
                  WAN_TEST_CONTINUOUS) THEN
    ASM_SIMP_TAC[];
    X_GEN_TAC `x:real^N` THEN REWRITE_TAC[wan_dpart] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `B / e * norm(basis i:real^N)` THEN
    ASM_SIMP_TAC[] THEN GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[WAN_NORM_BASIS_LE] THEN
    MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
    REPEAT STRIP_TAC THEN MATCH_MP_TAC WAN_TEST_DPART_ZERO THEN
    EXISTS_TAC `cball(a:real^N,&2 * e)` THEN ASM_REWRITE_TAC[COMPACT_CBALL] THEN
    UNDISCH_TAC `wan_test (:real^N) (\y. smooth_bump e (&2 * e) (y - a))` THEN
    REWRITE_TAC[wan_test] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN_CBALL; dist] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC SMOOTH_BUMP_0 THEN ONCE_REWRITE_TAC[NORM_SUB] THEN ASM_REAL_ARITH_TAC]);;

let WAN_BAD_TERM_ABS = prove
 (`!(s:real^N->bool) (A:real^N->real^K) (Q:real^N->real^K) (g:num->real^N->real)
    a r0 (r:num->real) C M.
     cball(a,r0) SUBSET s /\ A IN lspace (cball(a,r0)) (&2) /\
     Q continuous_on (:real^N) /\ (!x. norm(Q x) <= M) /\ &0 <= C /\
     (!n. (\x. lift(g n x)) continuous_on (:real^N)) /\
     (!n. ?Bn. !x. abs(g n x) <= Bn) /\
     (!n x. ~(x IN cball(a,r n)) ==> g n x = &0) /\
     (!n. (\x. lift(g n x pow 2)) integrable_on (:real^N) /\
          drop(integral (:real^N) (\x. lift(g n x pow 2))) <= C) /\
     (!n. r n <= r0) /\
     (!x. ~(x = a) ==> ?N. !n. N <= n ==> r n < norm(x - a))
     ==> ((\n. integral s (\x. lift(g n x * (A x dot Q x)))) --> vec 0) sequentially`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `AK = \x. if x IN cball(a:real^N,r0) then (A:real^N->real^K) x else vec 0` THEN
  SUBGOAL_THEN `!x. x IN cball(a:real^N,r0) ==> (AK:real^N->real^K) x = A x` ASSUME_TAC THENL
   [EXPAND_TAC "AK" THEN SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!n x. x IN cball(a:real^N,(r:num->real) n) ==> x IN cball(a,r0)` ASSUME_TAC THENL
   [ASM_MESON_TAC[SUBSET_CBALL; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. integral s (\x. lift((g:num->real^N->real) n x * (A x dot (Q:real^N->real^K) x))) =
        integral (:real^N) (\x. lift(g n x * ((AK:real^N->real^K) x dot Q x)))`
  (fun th -> REWRITE_TAC[th]) THENL
   [X_GEN_TAC `n:num` THEN
    MP_TAC(ISPECL [`\x. lift((g:num->real^N->real) n x * (A x dot (Q:real^N->real^K) x))`;
                   `cball(a:real^N,r(n:num))`; `s:real^N->bool`; `(:real^N)`]
                  WAN_INTEGRAL_SUPPORT_SUBSET) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[SUBSET_UNIV] THEN CONJ_TAC THENL
       [ASM SET_TAC[]; ASM_SIMP_TAC[REAL_MUL_LZERO; LIFT_NUM]];
      DISCH_THEN SUBST1_TAC] THEN
    MATCH_MP_TAC INTEGRAL_EQ THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    ASM_CASES_TAC `(x:real^N) IN cball(a,r(n:num))` THENL
     [SUBGOAL_THEN `(x:real^N) IN cball(a,r0)` (fun th -> ASM_SIMP_TAC[th]) THEN
      ASM_MESON_TAC[];
      ASM_SIMP_TAC[REAL_MUL_LZERO]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(AK:real^N->real^K) absolutely_integrable_on (:real^N)` ASSUME_TAC THENL
   [EXPAND_TAC "AK" THEN REWRITE_TAC[ABSOLUTELY_INTEGRABLE_RESTRICT_UNIV] THEN
    REWRITE_TAC[GSYM LSPACE_1] THEN MATCH_MP_TAC LSPACE_MONO THEN
    EXISTS_TAC `&2` THEN ASM_REWRITE_TAC[MEASURABLE_CBALL] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`A:real^N->real^K`; `a:real^N`; `r0:real`; `r:num->real`]
                WAN_SMALL_BALL_L2) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!n x. (if x IN cball(a:real^N,(r:num->real) n) then lift((abs M * norm((AK:real^N->real^K) x)) pow 2)
           else vec 0) =
          abs M pow 2 % (if x IN cball(a,r n) then lift(norm((A:real^N->real^K) x) pow 2)
                         else vec 0)`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN COND_CASES_TAC THENL
     [SUBGOAL_THEN `(x:real^N) IN cball(a,r0)`
       (fun th -> ASM_SIMP_TAC[th; REAL_POW_MUL; LIFT_CMUL]) THEN
      ASM_MESON_TAC[];
      REWRITE_TAC[VECTOR_MUL_RZERO]];
    ALL_TAC] THEN
  MATCH_MP_TAC WAN_L2_SHRINKING_PRODUCT THEN
  MAP_EVERY EXISTS_TAC
   [`\x. abs M * norm((AK:real^N->real^K) x)`; `\n:num. cball(a:real^N,(r:num->real) n)`; `C:real`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `n:num` THEN MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
    FIRST_X_ASSUM(X_CHOOSE_TAC `Bn:real` o SPEC `n:num` o
      check (fun th -> is_exists(snd(dest_forall(concl th))))) THEN
    MATCH_MP_TAC WAN_ABS_INT_CONT_MUL THEN EXISTS_TAC `Bn:real` THEN
    ASM_REWRITE_TAC[LEBESGUE_MEASURABLE_UNIV] THEN
    MATCH_MP_TAC WAN_ABS_INT_CONT_DOT THEN EXISTS_TAC `M:real` THEN
    ASM_REWRITE_TAC[LEBESGUE_MEASURABLE_UNIV];
    X_GEN_TAC `x:real^N` THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `norm((AK:real^N->real^K) x) * norm((Q:real^N->real^K) x)` THEN
    REWRITE_TAC[NORM_CAUCHY_SCHWARZ_ABS] THEN GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N` o
      check (fun th -> can (find_term ((=) `M:real`)) (concl th) && is_forall(concl th))) THEN
    REAL_ARITH_TAC;
    X_GEN_TAC `n:num` THEN MATCH_MP_TAC INTEGRABLE_CMUL THEN ASM_REWRITE_TAC[];
    SUBGOAL_THEN
     `!n. integral (:real^N)
            (\x. abs M pow 2 % (if x IN cball(a,(r:num->real) n)
                                then lift(norm((A:real^N->real^K) x) pow 2) else vec 0)) =
          abs M pow 2 % integral (:real^N)
            (\x. if x IN cball(a,r n) then lift(norm(A x) pow 2) else vec 0)`
    (fun th -> REWRITE_TAC[th]) THENL
     [GEN_TAC THEN MATCH_MP_TAC INTEGRAL_CMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC LIM_NULL_CMUL THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Cutting a vector test map away from a point, and the weak equation across *)
(* a point (WAN_REMOVABLE_POINT_WEAK_STATEMENT).                              *)
(* ------------------------------------------------------------------------- *)

let WAN_VTEST_MUL_CUTOFF = prove
 (`!(s:real^N->bool) (phi:real^N->real^K) (b:real^N->real) a e.
     wan_vtest s phi /\ smooth_map_on (:real^N) (\x. lift(b x)) /\ &0 < e /\
     (!x. x IN ball(a,e) ==> b x = &1)
     ==> wan_vtest (s DIFF {a}) (\x. (&1 - b x) % phi x) /\
         !i x. partial_derivative i (\x. (&1 - b x) % phi x) x =
               (&1 - b x) % partial_derivative i phi x - wan_dpart i b x % phi x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [wan_vtest]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `k:real^N->bool` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `smooth_map_on (:real^N) (\x. lift(&1 - (b:real^N->real) x))` ASSUME_TAC THENL
   [REWRITE_TAC[LIFT_SUB] THEN MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN
    ASM_REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_CONST];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[wan_vtest] THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`(:real^N)`; `\x. lift(&1 - (b:real^N->real) x)`; `phi:real^N->real^K`]
                    SMOOTH_MAP_ON_MUL_DROP_OPEN) THEN
      ASM_REWRITE_TAC[OPEN_UNIV; LIFT_DROP];
      EXISTS_TAC `k DIFF ball(a:real^N,e)` THEN
      ASM_SIMP_TAC[COMPACT_DIFF; OPEN_BALL] THEN CONJ_TAC THENL
       [UNDISCH_TAC `(k:real^N->bool) SUBSET s` THEN
        MP_TAC(ISPECL [`a:real^N`; `e:real`] CENTRE_IN_BALL) THEN ASM_REWRITE_TAC[] THEN
        SET_TAC[];
        X_GEN_TAC `x:real^N` THEN REWRITE_TAC[IN_DIFF; DE_MORGAN_THM] THEN
        STRIP_TAC THEN ASM_SIMP_TAC[VECTOR_MUL_RZERO; REAL_SUB_REFL; VECTOR_MUL_LZERO]]];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`i:num`; `x:real^N`] THEN REWRITE_TAC[partial_derivative] THEN
  SUBGOAL_THEN
   `((\x. (&1 - (b:real^N->real) x) % (phi:real^N->real^K) x) has_derivative
     (\h. (&1 - b x) % frechet_derivative phi (at x) h +
          (--drop(frechet_derivative (\y. lift(b y)) (at x) h)) % phi x)) (at x)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\x. &1 - (b:real^N->real) x`;
                   `\h. --drop(frechet_derivative (\y. lift((b:real^N->real) y)) (at x) h)`;
                   `phi:real^N->real^K`; `frechet_derivative (phi:real^N->real^K) (at x)`;
                   `x:real^N`] HAS_DERIVATIVE_MUL_AT) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
     [SUBGOAL_THEN
       `(lift o (\x. &1 - (b:real^N->real) x)) = (\x. lift(&1) - lift(b x)) /\
        (lift o (\h. --drop(frechet_derivative (\y. lift(b y)) (at x) h))) =
        (\h. vec 0 - frechet_derivative (\y. lift(b y)) (at x) h)`
      (fun th -> REWRITE_TAC[th]) THENL
       [REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_SUB; LIFT_NEG; LIFT_DROP; VECTOR_SUB_LZERO];
        ALL_TAC] THEN
      MATCH_MP_TAC HAS_DERIVATIVE_SUB THEN REWRITE_TAC[HAS_DERIVATIVE_CONST; ETA_AX] THEN
      REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `(:real^N)` THEN
      ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV];
      REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `(:real^N)` THEN
      ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
  REWRITE_TAC[wan_dpart] THEN VECTOR_ARITH_TAC);;

let WAN_L2LOC_IMP_LLOC = prove
 (`!(s:real^N->bool) (u:real^N->real^K). wan_l2loc s u ==> wan_lloc s u`,
  REWRITE_TAC[wan_l2loc; wan_lloc] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM LSPACE_1] THEN MATCH_MP_TAC LSPACE_MONO THEN
  EXISTS_TAC `&2` THEN ASM_SIMP_TAC[MEASURABLE_COMPACT] THEN REAL_ARITH_TAC);;

let WAN_SUM_DROP = prove
 (`!s (X:num->real^1). sum s (\i. drop(X i)) = drop(vsum s X)`,
  REWRITE_TAC[DROP_VSUM; o_DEF]);;

let WAN_RPW_IDENTITY = prove
 (`!(s:real^N->bool) (a:real^N) (A:num->real^N->real^K) (f:real^N->real^K) phi kp e.
     (!i. 1 <= i /\ i <= dimindex(:N) ==> wan_lloc s (A i)) /\ wan_lloc s f /\
     (!phi. wan_vtest (s DIFF {a}) phi
            ==> sum(1..dimindex(:N))
                   (\i. drop(integral s (\x. lift(A i x dot partial_derivative i phi x)))) =
                drop(integral s (\x. lift(f x dot phi x)))) /\
     open s /\ wan_vtest s phi /\ compact kp /\ kp SUBSET s /\
     (!x. ~(x IN kp) ==> phi x = vec 0) /\ &0 < e
     ==> vsum(1..dimindex(:N))
           (\i. integral s (\x. lift((&1 - smooth_bump e (&2 * e) (x - a)) *
                                     (A i x dot partial_derivative i phi x))) -
                integral s (\x. lift(wan_dpart i (\y. smooth_bump e (&2 * e) (y - a)) x *
                                     (A i x dot phi x)))) =
         integral s (\x. lift((&1 - smooth_bump e (&2 * e) (x - a)) * (f x dot phi x)))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (LABEL_TAC "H") STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`a:real^N`; `e:real`] WAN_POINT_CUTOFF_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`a:real^N`; `e:real`] WAN_CUTOFF_CONT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC (INST_TYPE [`:N`,`:N`] WAN_POINT_CUTOFF_DPART) THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `phi:real^N->real^K`;
                 `\y:real^N. smooth_bump e (&2 * e) (y - a)`; `a:real^N`; `e:real`]
                WAN_VTEST_MUL_CUTOFF) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [REWRITE_TAC[IN_BALL; dist] THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ONCE_REWRITE_TAC[NORM_SUB] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o BETA_RULE)) THEN
  REMOVE_THEN "H" (MP_TAC o SPEC
    `\x. (&1 - smooth_bump e (&2 * e) (x - a:real^N)) % (phi:real^N->real^K) x`) THEN
  ASM_REWRITE_TAC[DOT_RSUB; DOT_RMUL; LIFT_SUB] THEN
  SUBGOAL_THEN `(phi:real^N->real^K) continuous_on (:real^N)` ASSUME_TAC THENL
   [UNDISCH_TAC `wan_vtest s (phi:real^N->real^K)` THEN REWRITE_TAC[wan_vtest] THEN
    MESON_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. (\x. partial_derivative i (phi:real^N->real^K) x) continuous_on (:real^N) /\
        (!x. ~(x IN kp) ==> partial_derivative i phi x = vec 0)`
  ASSUME_TAC THENL
   [GEN_TAC THEN UNDISCH_TAC `wan_vtest s (phi:real^N->real^K)` THEN
    REWRITE_TAC[wan_vtest; partial_derivative] THEN STRIP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_FRECHET_DERIVATIVE THEN ASM_REWRITE_TAC[OPEN_UNIV];
      REPEAT STRIP_TAC THEN
      MP_TAC(ISPECL [`phi:real^N->real^K`; `kp:real^N->bool`; `x:real^N`]
                    WAN_FRECHET_ZERO_OUTSIDE) THEN
      ASM_SIMP_TAC[COMPACT_IMP_CLOSED]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= dimindex(:N)
        ==> (\x. lift((&1 - smooth_bump e (&2 * e) (x - a)) *
                      ((A:num->real^N->real^K) i x dot partial_derivative i phi x)))
              absolutely_integrable_on s /\
            (\x. lift(wan_dpart i (\y. smooth_bump e (&2 * e) (y - a)) x *
                      (A i x dot (phi:real^N->real^K) x)))
              absolutely_integrable_on s`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC WAN_ABS_INT_CONT_MUL THENL
     [EXISTS_TAC `&1`; EXISTS_TAC `B / e`] THEN
    ASM_SIMP_TAC[LEBESGUE_MEASURABLE_OPEN] THEN REPEAT CONJ_TAC THEN
    TRY(X_GEN_TAC `x:real^N` THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N` o
          check (is_conj o snd o dest_forall o concl)) THEN REAL_ARITH_TAC) THEN
    MATCH_MP_TAC WAN_LLOC_DOT_CONT_SUPPORT THEN EXISTS_TAC `kp:real^N->bool` THEN
    ASM_SIMP_TAC[ETA_AX];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\x. lift((&1 - smooth_bump e (&2 * e) (x - a)) * ((f:real^N->real^K) x dot phi x)))
      absolutely_integrable_on s`
  ASSUME_TAC THENL
   [MATCH_MP_TAC WAN_ABS_INT_CONT_MUL THEN EXISTS_TAC `&1` THEN
    ASM_SIMP_TAC[LEBESGUE_MEASURABLE_OPEN] THEN CONJ_TAC THENL
     [X_GEN_TAC `x:real^N` THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N` o
        check (is_conj o snd o dest_forall o concl)) THEN REAL_ARITH_TAC;
      MATCH_MP_TAC WAN_LLOC_DOT_CONT_SUPPORT THEN EXISTS_TAC `kp:real^N->bool` THEN
      ASM_SIMP_TAC[ETA_AX]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= dimindex(:N)
        ==> integral s (\x. lift((&1 - smooth_bump e (&2 * e) (x - a)) *
                                 ((A:num->real^N->real^K) i x dot partial_derivative i phi x)) -
                            lift(wan_dpart i (\y. smooth_bump e (&2 * e) (y - a)) x *
                                 (A i x dot (phi:real^N->real^K) x))) =
            integral s (\x. lift((&1 - smooth_bump e (&2 * e) (x - a)) *
                                 (A i x dot partial_derivative i phi x))) -
            integral s (\x. lift(wan_dpart i (\y. smooth_bump e (&2 * e) (y - a)) x *
                                 (A i x dot phi x)))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRAL_SUB THEN
    ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE];
    ALL_TAC] THEN
  REWRITE_TAC[WAN_SUM_DROP; DROP_EQ] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC VSUM_EQ THEN REWRITE_TAC[IN_NUMSEG] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN ASM_SIMP_TAC[]);;

let WAN_VTEST_PARTIAL = prove
 (`!(s:real^N->bool) (phi:real^N->real^K) kp i.
     wan_vtest s phi /\ compact kp /\ (!x. ~(x IN kp) ==> phi x = vec 0)
     ==> phi continuous_on (:real^N) /\
         (\x. partial_derivative i phi x) continuous_on (:real^N) /\
         (!x. ~(x IN kp) ==> partial_derivative i phi x = vec 0)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wan_vtest; partial_derivative] THEN STRIP_TAC THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_FRECHET_DERIVATIVE THEN ASM_REWRITE_TAC[OPEN_UNIV];
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`phi:real^N->real^K`; `kp:real^N->bool`; `x:real^N`]
                  WAN_FRECHET_ZERO_OUTSIDE) THEN
    ASM_SIMP_TAC[COMPACT_IMP_CLOSED]]);;

let WAN_REMOVABLE_POINT_WEAK_CORE = prove
 (`!(s:real^N->bool) (a:real^N) (A:num->real^N->real^K) (f:real^N->real^K) phi.
     open s /\ 2 <= dimindex(:N) /\
     (!i. 1 <= i /\ i <= dimindex(:N) ==> wan_l2loc s (A i)) /\ wan_lloc s f /\
     (!phi. wan_vtest (s DIFF {a}) phi
            ==> sum(1..dimindex(:N))
                   (\i. drop(integral s (\x. lift(A i x dot partial_derivative i phi x)))) =
                drop(integral s (\x. lift(f x dot phi x)))) /\
     wan_vtest s phi
     ==> sum(1..dimindex(:N))
            (\i. drop(integral s (\x. lift(A i x dot partial_derivative i phi x)))) =
         drop(integral s (\x. lift(f x dot phi x)))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (LABEL_TAC "H") ASSUME_TAC))))) THEN
  ASM_CASES_TAC `(a:real^N) IN s` THENL
   [ALL_TAC;
    REMOVE_THEN "H" MATCH_MP_TAC THEN
    SUBGOAL_THEN `s DIFF {a:real^N} = s` (fun th -> ASM_REWRITE_TAC[th]) THEN ASM SET_TAC[]] THEN
  SUBGOAL_THEN `!i. 1 <= i /\ i <= dimindex(:N) ==> wan_lloc s ((A:num->real^N->real^K) i)`
  ASSUME_TAC THENL [ASM_SIMP_TAC[WAN_L2LOC_IMP_LLOC]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `a:real^N` o GEN_REWRITE_RULE I [OPEN_CONTAINS_CBALL] o
    check (fun th -> concl th = `open (s:real^N->bool)`)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `d1:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `d0 = min (d1 / &2) (&1)` THEN
  SUBGOAL_THEN `&0 < d0 /\ d0 <= &1 /\ cball(a:real^N,&2 * d0) SUBSET s` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "d0" THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC;
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `cball(a:real^N,d1)` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_CBALL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [wan_vtest] o
    check (fun th -> concl th = `wan_vtest (s:real^N->bool) (phi:real^N->real^K)`)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `kp:real^N->bool` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN
   `(phi:real^N->real^K) continuous_on (:real^N) /\
    !i. (\x. partial_derivative i phi x) continuous_on (:real^N) /\
        (!x. ~(x IN kp) ==> partial_derivative i phi x = vec 0)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`s:real^N->bool`; `phi:real^N->real^K`; `kp:real^N->bool`]
                  WAN_VTEST_PARTIAL) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`phi:real^N->real^K`; `kp:real^N->bool`] WAN_CONT_SUPPORT_BOUNDED) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `M:real`) THEN
  X_CHOOSE_THEN `C:real` STRIP_ASSUME_TAC (INST_TYPE [`:N`,`:N`] WAN_POINT_CUTOFF_L2) THEN
  X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC (INST_TYPE [`:N`,`:N`] WAN_POINT_CUTOFF_DPART) THEN
  SUBGOAL_THEN
   `!n. vsum(1..dimindex(:N))
          (\i. integral s
                 (\x. lift((&1 - smooth_bump (d0 * inv(&n + &1)) (&2 * (d0 * inv(&n + &1)))
                                   (x - a)) *
                           ((A:num->real^N->real^K) i x dot partial_derivative i phi x))) -
               integral s
                 (\x. lift(wan_dpart i (\y. smooth_bump (d0 * inv(&n + &1))
                                              (&2 * (d0 * inv(&n + &1))) (y - a)) x *
                           (A i x dot (phi:real^N->real^K) x)))) =
        integral s
          (\x. lift((&1 - smooth_bump (d0 * inv(&n + &1)) (&2 * (d0 * inv(&n + &1))) (x - a)) *
                    ((f:real^N->real^K) x dot phi x)))`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC WAN_RPW_IDENTITY THEN EXISTS_TAC `kp:real^N->bool` THEN
    ASM_SIMP_TAC[WAN_EN_FACTS];
    ALL_TAC] THEN
  MATCH_MP_TAC(MESON[DROP_EQ]
   `!v w. v = w /\
          sum(1..dimindex(:N)) (\i. drop(integral s (\x. lift(A i x dot partial_derivative i phi x)))) = drop v /\
          drop(integral s (\x. lift((f:real^N->real^K) x dot phi x))) = drop w
          ==> sum(1..dimindex(:N))
                (\i. drop(integral s (\x. lift((A:num->real^N->real^K) i x dot
                                               partial_derivative i (phi:real^N->real^K) x)))) =
              drop(integral s (\x. lift(f x dot phi x)))`) THEN
  MAP_EVERY EXISTS_TAC
   [`vsum(1..dimindex(:N))
       (\i. integral s (\x. lift((A:num->real^N->real^K) i x dot partial_derivative i phi x)) -
            vec 0)`;
    `integral s (\x. lift((f:real^N->real^K) x dot phi x))`] THEN
  REWRITE_TAC[VECTOR_SUB_RZERO; GSYM WAN_SUM_DROP] THEN
  MATCH_MP_TAC(ISPEC `sequentially` LIM_UNIQUE) THEN
  EXISTS_TAC
   `\n. vsum(1..dimindex(:N))
          (\i. integral s
                 (\x. lift((&1 - smooth_bump (d0 * inv(&n + &1)) (&2 * (d0 * inv(&n + &1)))
                                   (x - a)) *
                           ((A:num->real^N->real^K) i x dot partial_derivative i phi x))) -
               integral s
                 (\x. lift(wan_dpart i (\y. smooth_bump (d0 * inv(&n + &1))
                                              (&2 * (d0 * inv(&n + &1))) (y - a)) x *
                           (A i x dot (phi:real^N->real^K) x))))` THEN
  REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN CONJ_TAC THENL
   [ALL_TAC;
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC WAN_CUTOFF_GOOD_TERM THEN
    ASM_SIMP_TAC[LEBESGUE_MEASURABLE_OPEN] THEN
    MATCH_MP_TAC WAN_LLOC_DOT_CONT_SUPPORT THEN EXISTS_TAC `kp:real^N->bool` THEN
    ASM_SIMP_TAC[ETA_AX]] THEN
  SUBGOAL_THEN
   `!n. &0 < d0 * inv(&n + &1) /\ d0 * inv(&n + &1) <= &1 /\
        &2 * (d0 * inv(&n + &1)) <= &2 * d0`
  ASSUME_TAC THENL
   [GEN_TAC THEN MP_TAC(ISPECL [`d0:real`; `n:num`] WAN_EN_FACTS) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= dimindex(:N)
        ==> (A:num->real^N->real^K) i IN lspace (cball(a,&2 * d0)) (&2)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th ->
      can (find_term ((=) `wan_l2loc:(real^N->bool)->(real^N->real^K)->bool`)) (concl th))) THEN
    ASM_REWRITE_TAC[wan_l2loc] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[COMPACT_CBALL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `vsum(1..dimindex(:N))
      (\i. integral s (\x. lift((A:num->real^N->real^K) i x dot partial_derivative i phi x))) =
    vsum(1..dimindex(:N))
      (\i. integral s (\x. lift(A i x dot partial_derivative i phi x)) - vec 0)`
  SUBST1_TAC THENL [REWRITE_TAC[VECTOR_SUB_RZERO]; ALL_TAC] THEN
  MATCH_MP_TAC LIM_VSUM THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN MATCH_MP_TAC LIM_SUB THEN CONJ_TAC THENL
   [MATCH_MP_TAC WAN_CUTOFF_GOOD_TERM THEN
    ASM_SIMP_TAC[LEBESGUE_MEASURABLE_OPEN] THEN
    MATCH_MP_TAC WAN_LLOC_DOT_CONT_SUPPORT THEN EXISTS_TAC `kp:real^N->bool` THEN
    ASM_SIMP_TAC[ETA_AX];
    ALL_TAC] THEN
  MATCH_MP_TAC WAN_BAD_TERM_ABS THEN
  MAP_EVERY EXISTS_TAC
   [`a:real^N`; `&2 * d0`; `\n. &2 * (d0 * inv(&n + &1))`; `C:real`; `M:real`] THEN
  ASM_SIMP_TAC[ETA_AX] THEN REPEAT CONJ_TAC THEN
  TRY(GEN_TAC THEN EXISTS_TAC `B / (d0 * inv(&n + &1))` THEN ASM_SIMP_TAC[] THEN NO_TAC) THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC WAN_CUTOFF_SEQ THEN ASM_REWRITE_TAC[]);;

let WAN_REMOVABLE_POINT_WEAK = prove
 (`!(n:N->bool) (kk:K->bool). WAN_REMOVABLE_POINT_WEAK_STATEMENT n kk`,
  REWRITE_TAC[WAN_REMOVABLE_POINT_WEAK_STATEMENT] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC WAN_REMOVABLE_POINT_WEAK_CORE THEN EXISTS_TAC `a:real^N` THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Weak partials against vector test maps, components of test maps, L^2 on   *)
(* sets differing by a null set; removable points for W^(1,2).               *)
(* ------------------------------------------------------------------------- *)

let WAN_LSPACE_NEGLIGIBLE_DIFF = prove
 (`!(s:real^N->bool) t (f:real^N->real^K) p.
     negligible(s DIFF t UNION t DIFF s) ==> (f IN lspace s p <=> f IN lspace t p)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[lspace; IN_ELIM_THM] THEN
  SUBGOAL_THEN `negligible((t:real^N->bool) DIFF s UNION s DIFF t)` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[UNION_COMM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`f:real^N->real^K`; `s:real^N->bool`; `t:real^N->bool`]
                MEASURABLE_ON_SPIKE_SET) THEN
  MP_TAC(ISPECL [`f:real^N->real^K`; `t:real^N->bool`; `s:real^N->bool`]
                MEASURABLE_ON_SPIKE_SET) THEN
  MP_TAC(ISPECL [`\x. lift(norm((f:real^N->real^K) x) rpow p)`; `s:real^N->bool`;
                 `t:real^N->bool`] INTEGRABLE_SPIKE_SET_EQ) THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

let WAN_LSPACE2_IMP_LLOC = prove
 (`!(s:real^N->bool) (u:real^N->real^K). u IN lspace s (&2) ==> wan_lloc s u`,
  REWRITE_TAC[wan_lloc] THEN REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM LSPACE_1] THEN
  MATCH_MP_TAC LSPACE_MONO THEN EXISTS_TAC `&2` THEN
  ASM_SIMP_TAC[MEASURABLE_COMPACT] THEN CONJ_TAC THENL
   [MATCH_MP_TAC LSPACE_SUBSET THEN EXISTS_TAC `s:real^N->bool` THEN
    ASM_SIMP_TAC[LEBESGUE_MEASURABLE_COMPACT];
    REAL_ARITH_TAC]);;

let WAN_LSPACE2_IMP_L2LOC = prove
 (`!(s:real^N->bool) (u:real^N->real^K). u IN lspace s (&2) ==> wan_l2loc s u`,
  REWRITE_TAC[wan_l2loc] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC LSPACE_SUBSET THEN EXISTS_TAC `s:real^N->bool` THEN
  ASM_SIMP_TAC[LEBESGUE_MEASURABLE_COMPACT]);;

let WAN_VTEST_COMPONENT = prove
 (`!(s:real^N->bool) (Psi:real^N->real^K) j.
     wan_vtest s Psi /\ 1 <= j /\ j <= dimindex(:K)
     ==> wan_test s (\x. Psi x$j) /\
         !i x. wan_dpart i (\x. Psi x$j) x = partial_derivative i Psi x$j`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wan_vtest; wan_test] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!x. lift((Psi:real^N->real^K) x$j) = lift(basis j dot Psi x)`
  ASSUME_TAC THENL [ASM_SIMP_TAC[DOT_BASIS]; ALL_TAC] THEN
  CONJ_TAC THENL
   [CONJ_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SMOOTH_MAP_ON_DOT_OPEN THEN
      ASM_REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_CONST];
      EXISTS_TAC `k:real^N->bool` THEN ASM_SIMP_TAC[VEC_COMPONENT]];
    REPEAT GEN_TAC THEN REWRITE_TAC[wan_dpart; partial_derivative] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `((\x. lift(basis j dot (Psi:real^N->real^K) x)) has_derivative
       (\t. lift(basis j dot frechet_derivative Psi (at x) t))) (at x)`
    MP_TAC THENL
     [MATCH_MP_TAC HAS_DERIVATIVE_LIFT_DOT THEN REWRITE_TAC[ETA_AX; GSYM FRECHET_DERIVATIVE_WORKS] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `(:real^N)` THEN
      ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV];
      DISCH_THEN(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
      ASM_SIMP_TAC[LIFT_DROP; DOT_BASIS]]]);;

let WAN_VTEST_BASIS = prove
 (`!(s:real^N->bool) phi j.
     wan_test s phi
     ==> wan_vtest s (\x. phi x % basis j:real^K) /\
         !i x. partial_derivative i (\x. phi x % basis j:real^K) x =
               wan_dpart i phi x % basis j`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wan_vtest; wan_test] THEN STRIP_TAC THEN CONJ_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`(:real^N)`; `\x. lift((phi:real^N->real) x)`;
                     `\x:real^N. basis j:real^K`] SMOOTH_MAP_ON_MUL_DROP_OPEN) THEN
      ASM_REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_CONST; LIFT_DROP];
      EXISTS_TAC `k:real^N->bool` THEN ASM_SIMP_TAC[VECTOR_MUL_LZERO]];
    REPEAT GEN_TAC THEN REWRITE_TAC[wan_dpart; partial_derivative] THEN
    SUBGOAL_THEN
     `((\x. drop(lift((phi:real^N->real) x)) % basis j:real^K) has_derivative
       (\t. drop(frechet_derivative (\y. lift(phi y)) (at x) t) % basis j)) (at x)`
    MP_TAC THENL
     [MATCH_MP_TAC HAS_DERIVATIVE_VMUL_DROP THEN REWRITE_TAC[ETA_AX; GSYM FRECHET_DERIVATIVE_WORKS] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `(:real^N)` THEN
      ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV];
      REWRITE_TAC[LIFT_DROP] THEN
      DISCH_THEN(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN REWRITE_TAC[]]]);;

let WAN_INTEGRABLE_SMUL_COMPONENT = prove
 (`!(s:real^N->bool) (c:real^N->real) (u:real^N->real^K) j.
     (\x. c x % u x) integrable_on s /\ 1 <= j /\ j <= dimindex(:K)
     ==> (\x. lift(c x * u x$j)) integrable_on s /\
         integral s (\x. c x % u x)$j = drop(integral s (\x. lift(c x * u x$j)))`,
  REPEAT STRIP_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [INTEGRABLE_COMPONENTWISE]) THEN
    DISCH_THEN(MP_TAC o SPEC `j:num`) THEN ASM_REWRITE_TAC[VECTOR_MUL_COMPONENT];
    ASM_SIMP_TAC[INTEGRAL_COMPONENT; VECTOR_MUL_COMPONENT]]);;

let WAN_WPD_IMP_VTEST = prove
 (`!(s:real^N->bool) i (u:real^N->real^K) v Psi.
     wan_wpd s i u v /\ wan_vtest s Psi
     ==> integral s (\x. lift(u x dot partial_derivative i Psi x)) =
         --(integral s (\x. lift(v x dot Psi x)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `wan_lloc s (u:real^N->real^K) /\ wan_lloc s (v:real^N->real^K)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[wan_wpd]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!j. 1 <= j /\ j <= dimindex(:K)
        ==> (\x. lift(partial_derivative i (Psi:real^N->real^K) x$j * (u:real^N->real^K) x$j))
              integrable_on s /\
            (\x. lift(Psi x$j * (v:real^N->real^K) x$j)) integrable_on s /\
            integral s (\x. lift(partial_derivative i Psi x$j * u x$j)) =
            --(integral s (\x. lift(Psi x$j * v x$j)))`
  ASSUME_TAC THENL
   [X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`s:real^N->bool`; `Psi:real^N->real^K`; `j:num`] WAN_VTEST_COMPONENT) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `(\x. partial_derivative i (Psi:real^N->real^K) x$j % (u:real^N->real^K) x)
        integrable_on s /\
      (\x. Psi x$j % (v:real^N->real^K) x) integrable_on s`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THENL
       [MP_TAC(ISPECL [`s:real^N->bool`; `\x. (Psi:real^N->real^K) x$j`;
                       `u:real^N->real^K`] WAN_TEST_PAIRING) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `i:num` o CONJUNCT2) THEN
        ASM_REWRITE_TAC[];
        MP_TAC(ISPECL [`s:real^N->bool`; `\x. (Psi:real^N->real^K) x$j`;
                       `v:real^N->real^K`] WAN_TEST_PAIRING) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN REWRITE_TAC[]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`s:real^N->bool`; `\x. partial_derivative i (Psi:real^N->real^K) x$j`;
                   `u:real^N->real^K`; `j:num`] WAN_INTEGRABLE_SMUL_COMPONENT) THEN
    MP_TAC(ISPECL [`s:real^N->bool`; `\x. (Psi:real^N->real^K) x$j`;
                   `v:real^N->real^K`; `j:num`] WAN_INTEGRABLE_SMUL_COMPONENT) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "cv")) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "cu")) THEN
    SUBGOAL_THEN
     `integral s (\x. partial_derivative i (Psi:real^N->real^K) x$j % (u:real^N->real^K) x) =
      --(integral s (\x. Psi x$j % (v:real^N->real^K) x))`
    (LABEL_TAC "eq") THENL
     [UNDISCH_TAC `wan_wpd s i (u:real^N->real^K) v` THEN REWRITE_TAC[wan_wpd] THEN
      DISCH_THEN(MP_TAC o SPEC `\x. (Psi:real^N->real^K) x$j` o CONJUNCT2 o CONJUNCT2) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    REMOVE_THEN "eq" (MP_TAC o AP_TERM `\w:real^K. w$j`) THEN
    REWRITE_TAC[VECTOR_NEG_COMPONENT] THEN
    REMOVE_THEN "cu" SUBST1_TAC THEN REMOVE_THEN "cv" SUBST1_TAC THEN
    REWRITE_TAC[GSYM DROP_EQ; DROP_NEG];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[DOT_SYM] THEN REWRITE_TAC[dot; LIFT_SUM; o_DEF] THEN
  MP_TAC(ISPECL [`\j x. lift(partial_derivative i (Psi:real^N->real^K) x$j *
                             (u:real^N->real^K) x$j)`;
                 `s:real^N->bool`; `1..dimindex(:K)`] INTEGRAL_VSUM) THEN
  MP_TAC(ISPECL [`\j x. lift((Psi:real^N->real^K) x$j * (v:real^N->real^K) x$j)`;
                 `s:real^N->bool`; `1..dimindex(:K)`] INTEGRAL_VSUM) THEN
  ASM_SIMP_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  DISCH_THEN SUBST1_TAC THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[GSYM VSUM_NEG] THEN MATCH_MP_TAC VSUM_EQ THEN
  REWRITE_TAC[IN_NUMSEG] THEN ASM_SIMP_TAC[]);;

let WAN_VTEST_IMP_WPD = prove
 (`!(s:real^N->bool) i (u:real^N->real^K) v.
     wan_lloc s u /\ wan_lloc s v /\
     (!Psi. wan_vtest s Psi
            ==> integral s (\x. lift(u x dot partial_derivative i Psi x)) =
                --(integral s (\x. lift(v x dot Psi x))))
     ==> wan_wpd s i u v`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[wan_wpd] THEN
  X_GEN_TAC `phi:real^N->real` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `phi:real^N->real`; `u:real^N->real^K`] WAN_TEST_PAIRING) THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `phi:real^N->real`; `v:real^N->real^K`] WAN_TEST_PAIRING) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(ASSUME_TAC o MATCH_MP ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE o CONJUNCT1) THEN
  DISCH_THEN(ASSUME_TAC o MATCH_MP ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE o SPEC `i:num` o
             CONJUNCT2) THEN
  REWRITE_TAC[CART_EQ] THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  REWRITE_TAC[VECTOR_NEG_COMPONENT] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `\x. wan_dpart i (phi:real^N->real) x`;
                 `u:real^N->real^K`; `j:num`] WAN_INTEGRABLE_SMUL_COMPONENT) THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `phi:real^N->real`; `v:real^N->real^K`; `j:num`]
                WAN_INTEGRABLE_SMUL_COMPONENT) THEN
  ASM_REWRITE_TAC[ETA_AX] THEN STRIP_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `\x. (phi:real^N->real) x % basis j:real^K`) THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `phi:real^N->real`; `j:num`] WAN_VTEST_BASIS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[DOT_RMUL] THEN
  ASM_SIMP_TAC[DOT_BASIS] THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[DROP_NEG]);;

let WAN_SUM_DELTA_DOT = prove
 (`!(s:real^N->bool) (u:real^N->real^K) (Psi:real^N->real^K) i.
     1 <= i /\ i <= dimindex(:N)
     ==> sum(1..dimindex(:N))
           (\m. drop(integral s (\x. lift((if m = i then u x else vec 0) dot
                                          partial_derivative m Psi x)))) =
         drop(integral s (\x. lift(u x dot partial_derivative i Psi x)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!m. drop(integral s (\x. lift((if m = i then (u:real^N->real^K) x else vec 0) dot
                                  partial_derivative m (Psi:real^N->real^K) x))) =
        if m = i then drop(integral s (\x. lift(u x dot partial_derivative i Psi x)))
        else &0`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN ASM_CASES_TAC `m:num = i` THEN
    ASM_REWRITE_TAC[DOT_LZERO; LIFT_NUM; INTEGRAL_0; DROP_VEC];
    REWRITE_TAC[SUM_DELTA; IN_NUMSEG] THEN ASM_REWRITE_TAC[]]);;

let WAN_REMOVABLE_POINT = prove
 (`!(n:N->bool) (kk:K->bool). WAN_REMOVABLE_POINT_STATEMENT n kk`,
  REWRITE_TAC[WAN_REMOVABLE_POINT_STATEMENT] THEN
  MAP_EVERY X_GEN_TAC [`s:real^N->bool`; `a:real^N`; `u:real^N->real^K`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `negligible((s DIFF {a:real^N}) DIFF s UNION s DIFF (s DIFF {a}))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN EXISTS_TAC `{a:real^N}` THEN
    REWRITE_TAC[NEGLIGIBLE_SING] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `open(s DIFF {a:real^N})` ASSUME_TAC THENL
   [MATCH_MP_TAC OPEN_DIFF THEN ASM_REWRITE_TAC[CLOSED_SING]; ALL_TAC] THEN
  SUBGOAL_THEN `!f:real^N->real^K. f IN lspace (s DIFF {a}) (&2) <=> f IN lspace s (&2)`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC WAN_LSPACE_NEGLIGIBLE_DIFF THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!g:real^N->real^1. integral (s DIFF {a}) g = integral s g` ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC INTEGRAL_SPIKE_SET THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(u:real^N->real^K) IN lspace s (&2)` ASSUME_TAC THENL
   [ASM_MESON_TAC[wan_w12]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= dimindex(:N)
        ==> wan_wd (s DIFF {a}) i (u:real^N->real^K) IN lspace s (&2) /\
            wan_wpd s i u (wan_wd (s DIFF {a}) i u)`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`s DIFF {a:real^N}`; `i:num`; `u:real^N->real^K`] WAN_WD_WORKS) THEN
    ASM_REWRITE_TAC[] THEN
    ABBREV_TAC `v = wan_wd (s DIFF {a:real^N}) i (u:real^N->real^K)` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC WAN_VTEST_IMP_WPD THEN ASM_SIMP_TAC[WAN_LSPACE2_IMP_LLOC] THEN
    X_GEN_TAC `Psi:real^N->real^K` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`s:real^N->bool`; `a:real^N`;
                   `\m:num x:real^N. if m = i then (u:real^N->real^K) x else vec 0`;
                   `\x:real^N. --((v:real^N->real^K) x)`; `Psi:real^N->real^K`]
                  WAN_REMOVABLE_POINT_WEAK_CORE) THEN
    ASM_SIMP_TAC[WAN_SUM_DELTA_DOT] THEN ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [X_GEN_TAC `m:num` THEN STRIP_TAC THEN ASM_CASES_TAC `m:num = i` THEN
        ASM_REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC WAN_LSPACE2_IMP_L2LOC THEN
        ASM_REWRITE_TAC[WAN_LSPACE2_ZERO];
        MATCH_MP_TAC WAN_LLOC_NEG THEN ASM_SIMP_TAC[WAN_LSPACE2_IMP_LLOC];
        X_GEN_TAC `phi:real^N->real^K` THEN DISCH_TAC THEN
        MP_TAC(ISPECL [`s DIFF {a:real^N}`; `i:num`; `u:real^N->real^K`;
                       `v:real^N->real^K`; `phi:real^N->real^K`] WAN_WPD_IMP_VTEST) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
        REWRITE_TAC[DOT_LNEG; LIFT_NEG] THEN
        MP_TAC(ISPECL [`\x. lift((v:real^N->real^K) x dot (phi:real^N->real^K) x)`;
                       `s:real^N->bool`] INTEGRAL_NEG) THEN
        REWRITE_TAC[] THEN ANTS_TAC THENL
         [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
          UNDISCH_TAC `wan_vtest (s DIFF {a}) (phi:real^N->real^K)` THEN
          REWRITE_TAC[wan_vtest] THEN STRIP_TAC THEN
          MATCH_MP_TAC WAN_LLOC_DOT_CONT_SUPPORT THEN EXISTS_TAC `k:real^N->bool` THEN
          ASM_SIMP_TAC[WAN_LSPACE2_IMP_LLOC; SMOOTH_MAP_ON_CONTINUOUS_ON] THEN
          ASM SET_TAC[];
          DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[DROP_NEG]]];
      ALL_TAC] THEN
    REWRITE_TAC[DOT_LNEG; LIFT_NEG] THEN
    MP_TAC(ISPECL [`\x. lift((v:real^N->real^K) x dot (Psi:real^N->real^K) x)`;
                   `s:real^N->bool`] INTEGRAL_NEG) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL
     [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
      UNDISCH_TAC `wan_vtest s (Psi:real^N->real^K)` THEN
      REWRITE_TAC[wan_vtest] THEN STRIP_TAC THEN
      MATCH_MP_TAC WAN_LLOC_DOT_CONT_SUPPORT THEN EXISTS_TAC `k:real^N->bool` THEN
      ASM_SIMP_TAC[WAN_LSPACE2_IMP_LLOC; SMOOTH_MAP_ON_CONTINUOUS_ON];
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[GSYM DROP_EQ; DROP_NEG]];
    ALL_TAC] THEN
  ASM_SIMP_TAC[wan_w12] THEN ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* L^2 and measurability helpers; local smooth approximation of W^(1,2)       *)
(* functions on compact subsets (cutoff, zero extension, mollification).      *)
(* ------------------------------------------------------------------------- *)

(* A copy of WAN_LSPACE_ZERO_EXTEND (pc_wan_preg), which this unit does not  *)
(* load.                                                                      *)

let WAN_SOB_LSPACE_ZERO_EXT = prove
 (`!(f:real^M->real^K) k p.
     &0 < p /\ f IN lspace k p /\ (!x. ~(x IN k) ==> f x = vec 0)
     ==> f IN lspace (:real^M) p`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LSPACE_ALT; IN_ELIM_THM] THEN STRIP_TAC THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN `(f:real^M->real^K) = (\x. if x IN k then f x else vec 0)`
    (fun th -> ONCE_REWRITE_TAC[th]) THENL
     [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `x:real^M` THEN
      COND_CASES_TAC THEN ASM_SIMP_TAC[];
      ASM_REWRITE_TAC[MEASURABLE_ON_UNIV]];
    SUBGOAL_THEN
     `(\x. lift(norm((f:real^M->real^K) x) rpow p)) =
      (\x. if x IN k then lift(norm(f x) rpow p) else vec 0)`
    (fun th -> ONCE_REWRITE_TAC[th]) THENL
     [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `x:real^M` THEN
      COND_CASES_TAC THEN ASM_SIMP_TAC[NORM_0; RPOW_ZERO; REAL_LT_IMP_NZ; LIFT_NUM];
      ASM_REWRITE_TAC[ABSOLUTELY_INTEGRABLE_RESTRICT_UNIV]]]);;

let WAN_MEASURABLE_COMPOSE_CONT = prove
 (`!(f:real^M->real^N) (g:real^N->real^P) s.
     lebesgue_measurable s /\ f measurable_on s /\ g continuous_on (:real^N)
     ==> (\x. g(f x)) measurable_on s`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\x. (g:real^N->real^P)(f x)) =
                (\x. (\y. g y - g(vec 0)) ((f:real^M->real^N) x) + g(vec 0))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM] THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC MEASURABLE_ON_ADD THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`f:real^M->real^N`; `\y. (g:real^N->real^P) y - g(vec 0)`;
                   `s:real^M->bool`] MEASURABLE_ON_COMPOSE_CONTINUOUS_0) THEN
    REWRITE_TAC[o_DEF; VECTOR_SUB_REFL] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_SIMP_TAC[CONTINUOUS_ON_SUB; CONTINUOUS_ON_CONST];
    MATCH_MP_TAC MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
    EXISTS_TAC `(:real^M)` THEN ASM_REWRITE_TAC[SUBSET_UNIV; MEASURABLE_ON_CONST]]);;

let WAN_LSPACE_RESTRICT_UNIV = prove
 (`!(f:real^M->real^K) k p.
     &0 < p
     ==> ((\x. if x IN k then f x else vec 0) IN lspace (:real^M) p <=> f IN lspace k p)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[lspace; IN_ELIM_THM; MEASURABLE_ON_UNIV] THEN
  AP_TERM_TAC THEN
  SUBGOAL_THEN
   `(\x. lift(norm(if x IN k then (f:real^M->real^K) x else vec 0) rpow p)) =
    (\x. if x IN k then lift(norm(f x) rpow p) else vec 0)`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `x:real^M` THEN COND_CASES_TAC THEN
    ASM_SIMP_TAC[NORM_0; RPOW_ZERO; REAL_LT_IMP_NZ; LIFT_NUM];
    REWRITE_TAC[INTEGRABLE_RESTRICT_UNIV]]);;

let WAN_L2_L1_BOUND = prove
 (`!(f:real^M->real^K) k t.
     measurable k /\ f IN lspace k (&2) /\ &0 < t
     ==> (\x. lift(norm(f x))) integrable_on k /\
         drop(integral k (\x. lift(norm(f x)))) <=
         t * drop(integral k (\x. lift(norm(f x) pow 2))) + measure k / t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`\x. if x IN k then (f:real^M->real^K) x else vec 0`;
                 `k:real^M->bool`; `t:real`] WAN_L1_SMALL_FROM_L2) THEN
  ASM_SIMP_TAC[WAN_LSPACE_RESTRICT_UNIV; REAL_OF_NUM_LT; ARITH] THEN
  REWRITE_TAC[COND_RAND; COND_RATOR; NORM_0; LIFT_NUM; REAL_POW_ZERO; ARITH_EQ] THEN
  REWRITE_TAC[INTEGRAL_RESTRICT_UNIV; INTEGRABLE_RESTRICT_UNIV]);;

let WAN_L2_TO_L1_CONV = prove
 (`!(f:num->real^M->real^K) k.
     measurable k /\ (!n. f n IN lspace k (&2)) /\
     ((\n. drop(integral k (\x. lift(norm(f n x) pow 2)))) ---> &0) sequentially
     ==> ((\n. drop(integral k (\x. lift(norm(f n x))))) ---> &0) sequentially`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "lim"))) THEN
  REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN X_GEN_TAC `eps:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= measure(k:real^M->bool)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[MEASURE_POS_LE]; ALL_TAC] THEN
  ABBREV_TAC `t = &2 * (measure(k:real^M->bool) + &1) / eps` THEN
  SUBGOAL_THEN `&0 < t /\ measure(k:real^M->bool) / t < eps / &2` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "t" THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
      SUBGOAL_THEN `measure(k:real^M->bool) / (&2 * (measure k + &1) / eps) =
                    (eps / &2) * (measure k / (measure k + &1))` SUBST1_TAC THENL
       [MATCH_MP_TAC(REAL_FIELD `&0 < e /\ &0 < m + &1
          ==> m / (&2 * (m + &1) / e) = (e / &2) * (m / (m + &1))`) THEN
        ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
      MATCH_MP_TAC REAL_LT_LMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_ARITH `&0 <= m ==> &0 < m + &1`] THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  REMOVE_THEN "lim" (MP_TAC o GEN_REWRITE_RULE I [REALLIM_SEQUENTIALLY]) THEN
  DISCH_THEN(MP_TAC o SPEC `eps / (&2 * t)`) THEN ANTS_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN DISCH_TAC THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN ASM_REWRITE_TAC[REAL_SUB_RZERO] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`(f:num->real^M->real^K) n`; `k:real^M->bool`; `t:real`]
                WAN_L2_L1_BOUND) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= drop(integral k (\x. lift(norm((f:num->real^M->real^K) n x))))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRAL_DROP_POS THEN ASM_REWRITE_TAC[LIFT_DROP; NORM_POS_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `t * drop(integral k (\x. lift(norm((f:num->real^M->real^K) n x) pow 2))) < eps / &2`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `t * eps / (&2 * t)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC
       `abs(drop(integral k (\x. lift(norm((f:num->real^M->real^K) n x) pow 2)))) <
        eps / (&2 * t)` THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN UNDISCH_TAC `&0 < t` THEN CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let WAN_TEST_BOUNDS = prove
 (`!(s:real^N->bool) psi i.
     wan_test s psi
     ==> ?k B. compact k /\ k SUBSET s /\ (!x. ~(x IN k) ==> psi x = &0) /\
               (!x. ~(x IN k) ==> wan_dpart i psi x = &0) /\
               (!x. abs(psi x) <= B) /\ (!x. abs(wan_dpart i psi x) <= B)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [wan_test]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `k:real^N->bool` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `psi:real^N->real`; `i:num`] WAN_TEST_CONTINUOUS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!x. ~(x IN k) ==> wan_dpart i (psi:real^N->real) x = &0` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC WAN_TEST_DPART_ZERO THEN
    EXISTS_TAC `k:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?B1. !x. abs((psi:real^N->real) x) <= B1` (X_CHOOSE_TAC `B1:real`) THENL
   [MP_TAC(ISPECL [`\x. lift((psi:real^N->real) x)`; `k:real^N->bool`]
                  WAN_CONT_SUPPORT_BOUNDED) THEN
    ASM_SIMP_TAC[LIFT_NUM; NORM_LIFT];
    ALL_TAC] THEN
  SUBGOAL_THEN `?B2. !x. abs(wan_dpart i (psi:real^N->real) x) <= B2`
  (X_CHOOSE_TAC `B2:real`) THENL
   [MP_TAC(ISPECL [`\x. lift(wan_dpart i (psi:real^N->real) x)`; `k:real^N->bool`]
                  WAN_CONT_SUPPORT_BOUNDED) THEN
    ASM_SIMP_TAC[LIFT_NUM; NORM_LIFT];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`k:real^N->bool`; `max B1 B2`] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THEN X_GEN_TAC `x:real^N` THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N` o check (fun th ->
      can (find_term ((=) `B1:real`)) (concl th))) THEN REAL_ARITH_TAC;
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N` o check (fun th ->
      can (find_term ((=) `B2:real`)) (concl th))) THEN REAL_ARITH_TAC]);;

let WAN_CUTOFF_EXTENSION = prove
 (`!(s:real^N->bool) (u:real^N->real^K) (g:num->real^N->real^K) psi.
     open s /\ wan_l2loc s u /\
     (!i. 1 <= i /\ i <= dimindex(:N) ==> wan_l2loc s (g i) /\ wan_wpd s i u (g i)) /\
     wan_test s psi
     ==> ?kp. compact kp /\ kp SUBSET s /\
              (\x. if x IN s then psi x % u x else vec 0) IN lspace (:real^N) (&2) /\
              (!x. ~(x IN kp) ==> (if x IN s then psi x % u x else vec 0) = vec 0) /\
              !i. 1 <= i /\ i <= dimindex(:N)
                  ==> (\x. if x IN s then wan_dpart i psi x % u x + psi x % g i x
                           else vec 0) IN lspace (:real^N) (&2) /\
                      (!x. ~(x IN kp)
                           ==> (if x IN s then wan_dpart i psi x % u x + psi x % g i x
                                else vec 0) = vec 0) /\
                      wan_wpd (:real^N) i (\x. if x IN s then psi x % u x else vec 0)
                        (\x. if x IN s then wan_dpart i psi x % u x + psi x % g i x
                             else vec 0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [wan_test] o
    check (fun th -> concl th = `wan_test (s:real^N->bool) psi`)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `kp:real^N->bool` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `kp:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!x. ~(x IN kp) ==> !i. wan_dpart i (psi:real^N->real) x = &0` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC WAN_TEST_DPART_ZERO THEN
    EXISTS_TAC `kp:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(u:real^N->real^K) IN lspace kp (&2)` ASSUME_TAC THENL
   [UNDISCH_TAC `wan_l2loc s (u:real^N->real^K)` THEN REWRITE_TAC[wan_l2loc] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `lebesgue_measurable(kp:real^N->bool)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[LEBESGUE_MEASURABLE_COMPACT]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN
     `(\x. if x IN s then (psi:real^N->real) x % (u:real^N->real^K) x else vec 0) =
      (\x. if x IN kp then psi x % u x else vec 0)`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `x:real^N` THEN
      ASM_CASES_TAC `(x:real^N) IN kp` THEN ASM_SIMP_TAC[VECTOR_MUL_LZERO; COND_ID] THEN
      SUBGOAL_THEN `(x:real^N) IN s` (fun th -> REWRITE_TAC[th]) THEN ASM SET_TAC[];
      ALL_TAC] THEN
    ASM_SIMP_TAC[WAN_LSPACE_RESTRICT_UNIV; REAL_OF_NUM_LT; ARITH] THEN
    MP_TAC(ISPECL [`s:real^N->bool`; `psi:real^N->real`; `1`] WAN_TEST_BOUNDS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MATCH_MP_TAC WAN_LSPACE2_BOUNDED_MUL THEN EXISTS_TAC `B:real` THEN
    ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^N)` THEN
    ASM_SIMP_TAC[SUBSET_UNIV; SMOOTH_MAP_ON_CONTINUOUS_ON];
    ASM_SIMP_TAC[VECTOR_MUL_LZERO; COND_ID];
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th ->
      can (find_term ((=) `wan_wpd:(real^N->bool)->num->(real^N->real^K)->(real^N->real^K)->bool`))
          (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `((g:num->real^N->real^K) i) IN lspace kp (&2)` ASSUME_TAC THENL
     [UNDISCH_TAC `wan_l2loc s ((g:num->real^N->real^K) i)` THEN REWRITE_TAC[wan_l2loc] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [SUBGOAL_THEN
       `(\x. if x IN s then wan_dpart i (psi:real^N->real) x % (u:real^N->real^K) x +
                            psi x % (g:num->real^N->real^K) i x else vec 0) =
        (\x. if x IN kp then wan_dpart i psi x % u x + psi x % g i x else vec 0)`
      SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `x:real^N` THEN
        ASM_CASES_TAC `(x:real^N) IN kp` THEN
        ASM_SIMP_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_LID; COND_ID] THEN
        SUBGOAL_THEN `(x:real^N) IN s` (fun th -> REWRITE_TAC[th]) THEN ASM SET_TAC[];
        ALL_TAC] THEN
      ASM_SIMP_TAC[WAN_LSPACE_RESTRICT_UNIV; REAL_OF_NUM_LT; ARITH] THEN
      MP_TAC(ISPECL [`s:real^N->bool`; `psi:real^N->real`; `i:num`] WAN_TEST_BOUNDS) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`s:real^N->bool`; `psi:real^N->real`; `i:num`] WAN_TEST_CONTINUOUS) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      MATCH_MP_TAC LSPACE_ADD THEN REWRITE_TAC[REAL_POS] THEN CONJ_TAC THEN
      MATCH_MP_TAC WAN_LSPACE2_BOUNDED_MUL THEN EXISTS_TAC `B:real` THEN
      ASM_SIMP_TAC[ETA_AX] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^N)` THEN
      ASM_REWRITE_TAC[SUBSET_UNIV];
      ASM_SIMP_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_LID; COND_ID];
      MATCH_MP_TAC WAN_WPD_ZERO_EXTENSION THEN ASM_REWRITE_TAC[ETA_AX]]]);;

let WAN_FAMILY_SEQ_EVENTUALLY = prove
 (`!d2 d. &0 < d2 /\ &0 < d
          ==> ?N. !n. N <= n ==> &0 < d2 / (&n + &2) /\ d2 / (&n + &2) < d`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `d2 / d` REAL_ARCH_SIMPLE) THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `N:num` THEN DISCH_TAC THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `&N <= &n` ASSUME_TAC THENL [ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
    ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_ARITH `&0 < &n + &2`] THEN
    UNDISCH_TAC `d2 / d <= &N` THEN ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
    SUBGOAL_THEN `&0 <= d * &n` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_POS]; ALL_TAC] THEN
    SUBGOAL_THEN `d * &N <= d * &n` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC]);;

let WAN_FAMILY_TO_SEQ = prove
 (`!(f:real->real^K) l d2.
     &0 < d2 /\
     (!eps. &0 < eps ==> ?d. &0 < d /\ !e. &0 < e /\ e < d ==> norm(f e - l) < eps)
     ==> ((\n. f(d2 / (&n + &2))) --> l) sequentially`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LIM_SEQUENTIALLY; dist] THEN
  X_GEN_TAC `eps:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `eps:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`d2:real`; `d:real`] WAN_FAMILY_SEQ_EVENTUALLY) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN ASM_MESON_TAC[]);;

let WAN_FAMILY_TO_SEQ_REAL = prove
 (`!(q:real->real) d2.
     &0 < d2 /\ (!e. &0 < e ==> &0 <= q e) /\
     (!eps. &0 < eps ==> ?d. &0 < d /\ !e. &0 < e /\ e < d ==> q e < eps)
     ==> ((\n. q(d2 / (&n + &2))) ---> &0) sequentially`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
  X_GEN_TAC `eps:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `eps:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`d2:real`; `d:real`] WAN_FAMILY_SEQ_EVENTUALLY) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN
  DISCH_TAC THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `d2 / (&n + &2)` o check (is_forall o concl)) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `d2 / (&n + &2)` o check (fun th ->
    is_forall(concl th) && can (find_term ((=) `(<=):real->real->bool`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let WAN_MOLL_SEQ_L2_ON = prove
 (`!(h:real^N->real^K) (v:real^N->real^K) kp k d2.
     compact kp /\ (!x. ~(x IN kp) ==> h x = vec 0) /\ h IN lspace (:real^N) (&2) /\
     compact k /\ (!x. x IN k ==> h x = v x) /\ &0 < d2
     ==> ((\n. drop(integral k (\x. lift(norm(wan_moll (d2 / (&n + &2)) h x - v x) pow 2))))
          ---> &0) sequentially`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!e. &0 < e
        ==> (\x. lift(norm(wan_moll e (h:real^N->real^K) x - h x) pow 2))
              integrable_on (:real^N)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC WAN_LSPACE2_SQNORM_INTEGRABLE THEN
    MATCH_MP_TAC LSPACE_SUB THEN ASM_SIMP_TAC[WAN_MOLL_L2; REAL_POS; ETA_AX];
    ALL_TAC] THEN
  MATCH_MP_TAC REALLIM_NULL_COMPARISON THEN
  EXISTS_TAC `\n. drop(integral (:real^N)
                    (\x. lift(norm(wan_moll (d2 / (&n + &2)) (h:real^N->real^K) x - h x)
                              pow 2)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC ALWAYS_EVENTUALLY THEN X_GEN_TAC `n:num` THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `&0 < d2 / (&n + &2)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN
     `integral k (\x. lift(norm(wan_moll (d2 / (&n + &2)) (h:real^N->real^K) x - v x) pow 2)) =
      integral k (\x. lift(norm(wan_moll (d2 / (&n + &2)) h x - h x) pow 2))`
    SUBST1_TAC THENL
     [MATCH_MP_TAC INTEGRAL_EQ THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `(\x. lift(norm(wan_moll (d2 / (&n + &2)) (h:real^N->real^K) x - h x) pow 2))
        integrable_on k`
    ASSUME_TAC THENL
     [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
      MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
      EXISTS_TAC `(:real^N)` THEN ASM_SIMP_TAC[LEBESGUE_MEASURABLE_COMPACT; SUBSET_UNIV] THEN
      MATCH_MP_TAC WAN_NONNEG_ABS_INTEGRABLE THEN
      ASM_SIMP_TAC[REAL_LE_POW_2];
      ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= a /\ a <= b ==> abs a <= b`) THEN CONJ_TAC THENL
     [MATCH_MP_TAC INTEGRAL_DROP_POS THEN ASM_REWRITE_TAC[LIFT_DROP; REAL_LE_POW_2];
      MATCH_MP_TAC INTEGRAL_SUBSET_DROP_LE THEN
      ASM_SIMP_TAC[SUBSET_UNIV; LIFT_DROP; REAL_LE_POW_2]];
    MP_TAC(ISPECL [`\e. drop(integral (:real^N)
                         (\x. lift(norm(wan_moll e (h:real^N->real^K) x - h x) pow 2)))`;
                   `d2:real`] WAN_FAMILY_TO_SEQ_REAL) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRAL_DROP_POS THEN
      ASM_SIMP_TAC[LIFT_DROP; REAL_LE_POW_2];
      MATCH_MP_TAC WAN_MOLL_L2_CONV THEN EXISTS_TAC `kp:real^N->bool` THEN
      ASM_REWRITE_TAC[]]]);;

let WAN_MOLL_SEQ_L2_LMEAS = prove
 (`!(h:real^N->real^K) (v:real^N->real^K) kp k d2.
     compact kp /\ (!x. ~(x IN kp) ==> h x = vec 0) /\ h IN lspace (:real^N) (&2) /\
     lebesgue_measurable k /\ (!x. x IN k ==> h x = v x) /\ &0 < d2
     ==> ((\n. drop(integral k (\x. lift(norm(wan_moll (d2 / (&n + &2)) h x - v x) pow 2))))
          ---> &0) sequentially`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!e. &0 < e
        ==> (\x. lift(norm(wan_moll e (h:real^N->real^K) x - h x) pow 2))
              integrable_on (:real^N)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC WAN_LSPACE2_SQNORM_INTEGRABLE THEN
    MATCH_MP_TAC LSPACE_SUB THEN ASM_SIMP_TAC[WAN_MOLL_L2; REAL_POS; ETA_AX];
    ALL_TAC] THEN
  MATCH_MP_TAC REALLIM_NULL_COMPARISON THEN
  EXISTS_TAC `\n. drop(integral (:real^N)
                    (\x. lift(norm(wan_moll (d2 / (&n + &2)) (h:real^N->real^K) x - h x)
                              pow 2)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC ALWAYS_EVENTUALLY THEN X_GEN_TAC `n:num` THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `&0 < d2 / (&n + &2)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN
     `integral k (\x. lift(norm(wan_moll (d2 / (&n + &2)) (h:real^N->real^K) x - v x) pow 2)) =
      integral k (\x. lift(norm(wan_moll (d2 / (&n + &2)) h x - h x) pow 2))`
    SUBST1_TAC THENL
     [MATCH_MP_TAC INTEGRAL_EQ THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `(\x. lift(norm(wan_moll (d2 / (&n + &2)) (h:real^N->real^K) x - h x) pow 2))
        integrable_on k`
    ASSUME_TAC THENL
     [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
      MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
      EXISTS_TAC `(:real^N)` THEN ASM_SIMP_TAC[SUBSET_UNIV] THEN
      MATCH_MP_TAC WAN_NONNEG_ABS_INTEGRABLE THEN
      ASM_SIMP_TAC[REAL_LE_POW_2];
      ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= a /\ a <= b ==> abs a <= b`) THEN CONJ_TAC THENL
     [MATCH_MP_TAC INTEGRAL_DROP_POS THEN ASM_REWRITE_TAC[LIFT_DROP; REAL_LE_POW_2];
      MATCH_MP_TAC INTEGRAL_SUBSET_DROP_LE THEN
      ASM_SIMP_TAC[SUBSET_UNIV; LIFT_DROP; REAL_LE_POW_2]];
    MP_TAC(ISPECL [`\e. drop(integral (:real^N)
                         (\x. lift(norm(wan_moll e (h:real^N->real^K) x - h x) pow 2)))`;
                   `d2:real`] WAN_FAMILY_TO_SEQ_REAL) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRAL_DROP_POS THEN
      ASM_SIMP_TAC[LIFT_DROP; REAL_LE_POW_2];
      MATCH_MP_TAC WAN_MOLL_L2_CONV THEN EXISTS_TAC `kp:real^N->bool` THEN
      ASM_REWRITE_TAC[]]]);;

let WAN_W12_LOCAL_APPROX = prove
 (`!(s:real^N->bool) (u:real^N->real^K) (g:num->real^N->real^K) k.
     open s /\ wan_l2loc s u /\
     (!i. 1 <= i /\ i <= dimindex(:N) ==> wan_l2loc s (g i) /\ wan_wpd s i u (g i)) /\
     compact k /\ k SUBSET s
     ==> ?w:num->real^N->real^K.
           (!n. wan_vtest s (w n)) /\
           ((\n. drop(integral k (\x. lift(norm(w n x - u x) pow 2)))) ---> &0)
             sequentially /\
           (!i. 1 <= i /\ i <= dimindex(:N)
                ==> ((\n. drop(integral k
                                (\x. lift(norm(partial_derivative i (w n) x - g i x) pow 2))))
                     ---> &0) sequentially) /\
           (?t. negligible t /\ !x. x IN k DIFF t ==> ((\n. w n x) --> u x) sequentially)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `k:real^N->bool`] WAN_COMPACT_NBHD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `d1:real` MP_TAC) THEN
  ABBREV_TAC `k1 = {x + y:real^N | x IN k /\ y IN cball(vec 0,d1)}` THEN
  ABBREV_TAC `uu = {x + y:real^N | x IN k /\ y IN ball(vec 0,d1)}` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `k1:real^N->bool`] WAN_SMOOTH_URYSOHN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `psi:real^N->real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!i x. x IN uu ==> wan_dpart i (psi:real^N->real) x = &0` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[wan_dpart] THEN
    MP_TAC(ISPECL [`\y. lift((psi:real^N->real) y)`; `\y:real^N. lift(&1)`;
                   `uu:real^N->bool`; `x:real^N`] LRG_FRECHET_DERIVATIVE_EQ_OPEN) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
      AP_TERM_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[FRECHET_DERIVATIVE_CONST_AT; DROP_VEC]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `u:real^N->real^K`; `g:num->real^N->real^K`;
                 `psi:real^N->real`] WAN_CUTOFF_EXTENSION) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `kp:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `?w0 (G:num->real^N->real^K).
      w0 IN lspace (:real^N) (&2) /\ (!x. ~(x IN kp) ==> w0 x = vec 0) /\
      (!x. x IN k ==> w0 x = (u:real^N->real^K) x) /\
      !i. 1 <= i /\ i <= dimindex(:N)
          ==> G i IN lspace (:real^N) (&2) /\ (!x. ~(x IN kp) ==> G i x = vec 0) /\
              wan_wpd (:real^N) i w0 (G i) /\
              (!x. x IN k ==> G i x = (g:num->real^N->real^K) i x)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXISTS_TAC
     [`\x. if x IN s then (psi:real^N->real) x % (u:real^N->real^K) x else vec 0`;
      `\i x. if x IN s then wan_dpart i (psi:real^N->real) x % (u:real^N->real^K) x +
                            psi x % (g:num->real^N->real^K) i x else vec 0`] THEN
    ASM_SIMP_TAC[ETA_AX] THEN
    SUBGOAL_THEN `!x. x IN k ==> (x:real^N) IN s /\ x IN uu /\ psi x = &1` ASSUME_TAC THENL
     [REPEAT STRIP_TAC THENL [ASM SET_TAC[]; ASM SET_TAC[]; ALL_TAC] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
      ALL_TAC] THEN
    ASM_SIMP_TAC[VECTOR_MUL_LID; VECTOR_MUL_LZERO; VECTOR_ADD_LID];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `kp:real^N->bool`] WAN_COMPACT_NBHD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `d2:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `\n. wan_moll (d2 / (&n + &2)) (w0:real^N->real^K)` THEN
  SUBGOAL_THEN `!n. &0 < d2 / (&n + &2) /\ d2 / (&n + &2) < d2` ASSUME_TAC THENL
   [GEN_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_ARITH `&0 < &n + &2`] THEN
      SUBGOAL_THEN `&0 <= d2 * &n` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_POS]; ALL_TAC] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `wan_lloc (:real^N) (w0:real^N->real^K)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[WAN_L2_LLOC]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `n:num` THEN REWRITE_TAC[wan_vtest] THEN CONJ_TAC THENL
     [MATCH_MP_TAC WAN_MOLL_SMOOTH THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    EXISTS_TAC `{x + y:real^N | x IN kp /\ y IN cball(vec 0,d2)}` THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`d2 / (&n + &2)`; `w0:real^N->real^K`; `kp:real^N->bool`]
                  WAN_MOLL_SUPPORT) THEN
    ASM_SIMP_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    UNDISCH_TAC `~((x:real^N) IN {x + y | x IN kp /\ y IN cball(vec 0,d2)})` THEN
    REWRITE_TAC[IN_ELIM_THM; CONTRAPOS_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `p:real^N` (X_CHOOSE_THEN `q:real^N` STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`p:real^N`; `q:real^N`] THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(q:real^N) IN ball(vec 0,d2 / (&n + &2))` THEN
    REWRITE_TAC[IN_BALL_0; IN_CBALL_0] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `n:num` o check (is_forall o concl)) THEN REAL_ARITH_TAC;
    REWRITE_TAC[] THEN MATCH_MP_TAC WAN_MOLL_SEQ_L2_ON THEN
    EXISTS_TAC `kp:real^N->bool` THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `!n x. partial_derivative i (wan_moll (d2 / (&n + &2)) (w0:real^N->real^K)) x =
            wan_moll (d2 / (&n + &2)) ((G:num->real^N->real^K) i) x`
    (fun th -> REWRITE_TAC[th]) THENL
     [REPEAT GEN_TAC THEN MATCH_MP_TAC WAN_MOLL_WPD THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC WAN_MOLL_SEQ_L2_ON THEN EXISTS_TAC `kp:real^N->bool` THEN
    ASM_SIMP_TAC[];
    MP_TAC(ISPEC `w0:real^N->real^K` WAN_MOLL_AE_CONV) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `t:real^N->bool` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[IN_DIFF] THEN X_GEN_TAC `x:real^N` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(u:real^N->real^K) x = w0 x` SUBST1_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`\e. wan_moll e (w0:real^N->real^K) x`; `(w0:real^N->real^K) x`;
                   `d2:real`] WAN_FAMILY_TO_SEQ) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `eps:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`x:real^N`; `eps:real`] o check (fun th ->
      can (find_term ((=) `t:real^N->bool`)) (concl th) && is_forall(concl th))) THEN
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The chain rule through C^1 maps with bounded derivative (CHAIN_W12).      *)
(* ------------------------------------------------------------------------- *)

let WAN_C1_BOUNDED_FACTS = prove
 (`!(P:real^K->real^L) B.
     continuously_differentiable 1 (:real^K) P /\
     (!y. onorm(frechet_derivative P (at y)) <= B)
     ==> (!y. (P has_derivative frechet_derivative P (at y)) (at y)) /\
         (!y. linear(frechet_derivative P (at y))) /\
         (!h. (\y. frechet_derivative P (at y) h) continuous_on (:real^K)) /\
         (!y h. norm(frechet_derivative P (at y) h) <= B * norm h) /\
         (!y z. norm(P y - P z) <= B * norm(y - z)) /\
         P continuous_on (:real^K)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!y. ((P:real^K->real^L) has_derivative frechet_derivative P (at y)) (at y)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `continuously_differentiable 1 (:real^K) (P:real^K->real^L)` THEN
    REWRITE_TAC[ONE; CONTINUOUSLY_DIFFERENTIABLE_UNIV] THEN
    DISCH_THEN(X_CHOOSE_THEN `f':real^K->real^K->real^L` STRIP_ASSUME_TAC) THEN
    X_GEN_TAC `y:real^K` THEN REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS; differentiable] THEN
    EXISTS_TAC `(f':real^K->real^K->real^L) y` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y. linear(frechet_derivative (P:real^K->real^L) (at y))` ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
    REWRITE_TAC[differentiable] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`0`; `P:real^K->real^L`] CONTINUOUSLY_DIFFERENTIABLE_FRECHET_UNIV) THEN
    ASM_REWRITE_TAC[GSYM ONE] THEN
    DISCH_THEN(MP_TAC o SPEC `h:real^K`) THEN
    REWRITE_TAC[continuously_differentiable];
    REPEAT GEN_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `onorm(frechet_derivative (P:real^K->real^L) (at y)) * norm(h:real^K)` THEN
    ASM_SIMP_TAC[ONORM] THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[NORM_POS_LE];
    MP_TAC(ISPECL [`P:real^K->real^L`; `\y. frechet_derivative (P:real^K->real^L) (at y)`;
                   `(:real^K)`; `B:real`] DIFFERENTIABLE_BOUND) THEN
    ASM_REWRITE_TAC[CONVEX_UNIV; WITHIN_UNIV; IN_UNIV] THEN MESON_TAC[];
    MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_IMP_CONTINUOUS_ON THEN
    EXISTS_TAC `1` THEN ASM_REWRITE_TAC[]]);;

let WAN_DP_MEASURABLE = prove
 (`!(P:real^K->real^L) (a:real^N->real^K) (b:real^N->real^K) k.
     lebesgue_measurable k /\ a measurable_on k /\ b measurable_on k /\
     (!y. linear(frechet_derivative P (at y))) /\
     (!h. (\y. frechet_derivative P (at y) h) continuous_on (:real^K))
     ==> (\x. frechet_derivative P (at (a x)) (b x)) measurable_on k`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `(\x. frechet_derivative (P:real^K->real^L) (at ((a:real^N->real^K) x)) ((b:real^N->real^K) x)) =
    (\x. vsum(1..dimindex(:K)) (\j. b x$j % frechet_derivative P (at (a x)) (basis j)))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `x:real^N` THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM BASIS_EXPANSION] THEN
    ASM_SIMP_TAC[LINEAR_VSUM; FINITE_NUMSEG; o_DEF; LINEAR_CMUL];
    ALL_TAC] THEN
  MATCH_MP_TAC MEASURABLE_ON_VSUM THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  X_GEN_TAC `j:num` THEN STRIP_TAC THEN MATCH_MP_TAC MEASURABLE_ON_MUL THEN CONJ_TAC THENL
   [UNDISCH_TAC `(b:real^N->real^K) measurable_on k` THEN
    GEN_REWRITE_TAC LAND_CONV [MEASURABLE_ON_COMPONENTWISE] THEN
    DISCH_THEN(MP_TAC o SPEC `j:num`) THEN ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`a:real^N->real^K`; `\y. frechet_derivative (P:real^K->real^L) (at y) (basis j)`;
                   `k:real^N->bool`] WAN_MEASURABLE_COMPOSE_CONT) THEN
    ASM_REWRITE_TAC[]]);;

let WAN_CHAIN_LLOC = prove
 (`!(s:real^N->bool) (u:real^N->real^K) (v:real^N->real^K) (P:real^K->real^L) B.
     wan_l2loc s u /\ wan_l2loc s v /\
     continuously_differentiable 1 (:real^K) P /\
     (!y. onorm(frechet_derivative P (at y)) <= B)
     ==> wan_lloc s (\x. P(u x)) /\
         wan_lloc s (\x. frechet_derivative P (at (u x)) (v x))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`P:real^K->real^L`; `B:real`] WAN_C1_BOUNDED_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[wan_lloc] THEN CONJ_TAC THEN X_GEN_TAC `k:real^N->bool` THEN STRIP_TAC THEN
  (SUBGOAL_THEN `(u:real^N->real^K) IN lspace k (&2) /\ (v:real^N->real^K) IN lspace k (&2)`
   STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[wan_l2loc]; ALL_TAC] THEN
   SUBGOAL_THEN `(u:real^N->real^K) absolutely_integrable_on k /\
                 (v:real^N->real^K) absolutely_integrable_on k`
   STRIP_ASSUME_TAC THENL
    [REWRITE_TAC[GSYM LSPACE_1] THEN CONJ_TAC THEN MATCH_MP_TAC LSPACE_MONO THEN
     EXISTS_TAC `&2` THEN ASM_SIMP_TAC[MEASURABLE_COMPACT] THEN REAL_ARITH_TAC;
     ALL_TAC] THEN
   SUBGOAL_THEN `lebesgue_measurable(k:real^N->bool)` ASSUME_TAC THENL
    [ASM_SIMP_TAC[LEBESGUE_MEASURABLE_COMPACT]; ALL_TAC] THEN
   MATCH_MP_TAC MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_ABSOLUTELY_INTEGRABLE) THENL
   [EXISTS_TAC `\x. lift(norm((P:real^K->real^L)(vec 0)) +
                         B * norm((u:real^N->real^K) x))` THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC WAN_MEASURABLE_COMPOSE_CONT THEN
      ASM_SIMP_TAC[INTEGRABLE_IMP_MEASURABLE; ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE];
      REWRITE_TAC[LIFT_ADD; LIFT_CMUL] THEN MATCH_MP_TAC INTEGRABLE_ADD THEN CONJ_TAC THENL
       [ONCE_REWRITE_TAC[GSYM INTEGRABLE_RESTRICT_UNIV] THEN REWRITE_TAC[] THEN
        MATCH_MP_TAC WAN_INDICATOR_CONST_INTEGRABLE THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC INTEGRABLE_CMUL THEN
        MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
        MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_NORM THEN ASM_REWRITE_TAC[]];
      X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN REWRITE_TAC[LIFT_DROP] THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`(u:real^N->real^K) x`; `vec 0:real^K`] o
        check (fun th -> can (find_term ((=) `(P:real^K->real^L) z`)) (concl th))) THEN
      REWRITE_TAC[VECTOR_SUB_RZERO] THEN
      MP_TAC(ISPECL [`(P:real^K->real^L)((u:real^N->real^K) x) - P(vec 0)`;
                     `(P:real^K->real^L)(vec 0)`] NORM_TRIANGLE) THEN
      REWRITE_TAC[VECTOR_SUB_ADD] THEN REAL_ARITH_TAC];
    EXISTS_TAC `\x. lift(B * norm((v:real^N->real^K) x))` THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC WAN_DP_MEASURABLE THEN
      ASM_SIMP_TAC[INTEGRABLE_IMP_MEASURABLE; ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE];
      REWRITE_TAC[LIFT_CMUL] THEN MATCH_MP_TAC INTEGRABLE_CMUL THEN
      MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
      MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_NORM THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN ASM_REWRITE_TAC[LIFT_DROP]]]);;

let WAN_WEIGHTED_L1_LIMIT = prove
 (`!(s:real^N->bool) (c:real^N->real) (H:num->real^N->real^K) H0 k M.
     lebesgue_measurable s /\ compact k /\ k SUBSET s /\ (!x. ~(x IN k) ==> c x = &0) /\
     (!x. abs(c x) <= M) /\ (\x. lift(c x)) continuous_on (:real^N) /\
     (!n. H n absolutely_integrable_on k) /\ H0 absolutely_integrable_on k /\
     ((\n. drop(integral k (\x. lift(norm(H n x - H0 x))))) ---> &0) sequentially
     ==> ((\n. integral s (\x. c x % H n x)) --> integral s (\x. c x % H0 x)) sequentially`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!G:real^N->real^K. integral s (\x. c x % G x) = integral k (\x. c x % G x)`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC WAN_INTEGRAL_SUPPORT_SUBSET THEN
    EXISTS_TAC `k:real^N->bool` THEN ASM_SIMP_TAC[SUBSET_REFL; VECTOR_MUL_LZERO];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\x. lift((c:real^N->real) x)) measurable_on k /\
                bounded(IMAGE (\x. lift((c:real^N->real) x)) k)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
      ASM_SIMP_TAC[LEBESGUE_MEASURABLE_COMPACT] THEN
      ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_UNIV];
      REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE; NORM_LIFT] THEN
      EXISTS_TAC `abs M + &1` THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N` o check (fun th ->
        can (find_term ((=) `M:real`)) (concl th))) THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!G:real^N->real^K. G absolutely_integrable_on k
                       ==> (\x. (c:real^N->real) x % G x) absolutely_integrable_on k`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`\x y:real^K. drop x % y`; `\x:real^N. lift((c:real^N->real) x)`;
                   `G:real^N->real^K`; `k:real^N->bool`]
                  ABSOLUTELY_INTEGRABLE_BOUNDED_MEASURABLE_PRODUCT) THEN
    ASM_REWRITE_TAC[BILINEAR_DROP_MUL; LIFT_DROP; ETA_AX];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[LIM_NULL] THEN MATCH_MP_TAC LIM_NULL_COMPARISON THEN
  EXISTS_TAC `\n. M * drop(integral k (\x. lift(norm((H:num->real^N->real^K) n x - H0 x))))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC ALWAYS_EVENTUALLY THEN X_GEN_TAC `n:num` THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `(\x. (c:real^N->real) x % (H:num->real^N->real^K) n x) absolutely_integrable_on k /\
      (\x. c x % (H0:real^N->real^K) x) absolutely_integrable_on k`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[ETA_AX]; ALL_TAC] THEN
    MP_TAC(ISPECL [`\x. (c:real^N->real) x % (H:num->real^N->real^K) n x`;
                   `\x. (c:real^N->real) x % (H0:real^N->real^K) x`; `k:real^N->bool`]
                  INTEGRAL_SUB) THEN
    ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[GSYM VECTOR_SUB_LDISTRIB] THEN
    MP_TAC(ISPECL [`\x. (c:real^N->real) x % ((H:num->real^N->real^K) n x - H0 x)`;
                   `\x. lift(M * norm((H:num->real^N->real^K) n x - H0 x))`; `k:real^N->bool`]
                  INTEGRAL_NORM_BOUND_INTEGRAL) THEN
    REWRITE_TAC[LIFT_CMUL] THEN ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_SUB THEN
        ASM_REWRITE_TAC[ETA_AX];
        MATCH_MP_TAC INTEGRABLE_CMUL THEN
        MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
        MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_NORM THEN
        MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_SUB THEN ASM_REWRITE_TAC[ETA_AX];
        X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
        REWRITE_TAC[NORM_MUL; DROP_CMUL; LIFT_DROP] THEN
        MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[NORM_POS_LE]];
      ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `b = c ==> a <= b ==> a <= c`) THEN
    MP_TAC(ISPECL [`\x. lift(norm((H:num->real^N->real^K) n x - H0 x))`; `M:real`;
                   `k:real^N->bool`] INTEGRAL_CMUL) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL
     [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
      MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_NORM THEN
      MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_SUB THEN ASM_REWRITE_TAC[ETA_AX];
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[DROP_CMUL]];
    REWRITE_TAC[GSYM LIFT_NUM; GSYM(REWRITE_RULE[o_DEF] TENDSTO_REAL)] THEN
    MATCH_MP_TAC REALLIM_NULL_LMUL THEN ASM_REWRITE_TAC[]]);;

let WAN_COMPOSE_L1_CONV = prove
 (`!(P:real^K->real^L) B (w:num->real^N->real^K) u k.
     compact k /\ (!y z. norm(P y - P z) <= B * norm(y - z)) /\
     (!n. w n IN lspace k (&2)) /\ u IN lspace k (&2) /\
     (!n. (\x. P(w n x)) absolutely_integrable_on k) /\
     (\x. P(u x)) absolutely_integrable_on k /\
     ((\n. drop(integral k (\x. lift(norm(w n x - u x) pow 2)))) ---> &0) sequentially
     ==> ((\n. drop(integral k (\x. lift(norm(P(w n x) - P(u x)))))) ---> &0) sequentially`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\n x. (w:num->real^N->real^K) n x - u x`; `k:real^N->bool`]
                WAN_L2_TO_L1_CONV) THEN
  ASM_SIMP_TAC[MEASURABLE_COMPACT; LSPACE_SUB; REAL_POS; ETA_AX] THEN DISCH_TAC THEN
  MATCH_MP_TAC REALLIM_NULL_COMPARISON THEN
  EXISTS_TAC `\n. B * drop(integral k (\x. lift(norm((w:num->real^N->real^K) n x - u x))))` THEN
  ASM_SIMP_TAC[REALLIM_NULL_LMUL] THEN MATCH_MP_TAC ALWAYS_EVENTUALLY THEN
  X_GEN_TAC `n:num` THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `(\x. lift(norm((P:real^K->real^L)((w:num->real^N->real^K) n x) - P(u x))))
      integrable_on k /\
    (\x. lift(norm((w:num->real^N->real^K) n x - u x))) integrable_on k`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_NORM THEN
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_SUB THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM LSPACE_1] THEN CONJ_TAC THEN MATCH_MP_TAC LSPACE_MONO THEN
    EXISTS_TAC `&2` THEN ASM_SIMP_TAC[MEASURABLE_COMPACT; ETA_AX] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= a /\ a <= b ==> abs a <= b`) THEN CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRAL_DROP_POS THEN ASM_REWRITE_TAC[LIFT_DROP; NORM_POS_LE];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `drop(integral k (\x. lift(B * norm((w:num->real^N->real^K) n x - u x))))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRAL_DROP_LE THEN ASM_REWRITE_TAC[LIFT_CMUL; DROP_CMUL; LIFT_DROP] THEN
    ASM_SIMP_TAC[INTEGRABLE_CMUL];
    REWRITE_TAC[LIFT_CMUL] THEN ASM_SIMP_TAC[INTEGRAL_CMUL; DROP_CMUL; REAL_LE_REFL]]);;

let WAN_LSPACE_MEASURABLE = prove
 (`!(f:real^N->real^K) s p. f IN lspace s p ==> f measurable_on s`,
  SIMP_TAC[lspace; IN_ELIM_THM]);;

let WAN_LSPACE2_NORM_INTEGRABLE = prove
 (`!(f:real^N->real^K) k.
     compact k /\ f IN lspace k (&2)
     ==> f absolutely_integrable_on k /\ (\x. lift(norm(f x))) integrable_on k`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(f:real^N->real^K) absolutely_integrable_on k` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM LSPACE_1] THEN MATCH_MP_TAC LSPACE_MONO THEN
    EXISTS_TAC `&2` THEN ASM_SIMP_TAC[MEASURABLE_COMPACT] THEN REAL_ARITH_TAC;
    ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE; ABSOLUTELY_INTEGRABLE_NORM]]);;

let WAN_DP_L1_CONV = prove
 (`!(P:real^K->real^L) B (w:num->real^N->real^K) u (p:num->real^N->real^K) g k t.
     compact k /\ negligible t /\
     (!y. linear(frechet_derivative P (at y))) /\
     (!h. (\y. frechet_derivative P (at y) h) continuous_on (:real^K)) /\
     (!y h. norm(frechet_derivative P (at y) h) <= B * norm h) /\
     (!n. w n measurable_on k) /\ u measurable_on k /\
     (!n. p n IN lspace k (&2)) /\ g IN lspace k (&2) /\
     (!x. x IN k DIFF t ==> ((\n. w n x) --> u x) sequentially) /\
     ((\n. drop(integral k (\x. lift(norm(p n x - g x) pow 2)))) ---> &0) sequentially
     ==> ((\n. drop(integral k (\x. lift(norm(frechet_derivative P (at (w n x)) (p n x) -
                                              frechet_derivative P (at (u x)) (g x))))))
          ---> &0) sequentially`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `lebesgue_measurable(k:real^N->bool)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[LEBESGUE_MEASURABLE_COMPACT]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(g:real^N->real^K) absolutely_integrable_on k /\
    (\x. lift(norm((g:real^N->real^K) x))) integrable_on k /\
    !n. (\x. lift(norm((p:num->real^N->real^K) n x - g x))) integrable_on k`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[WAN_LSPACE2_NORM_INTEGRABLE] THEN GEN_TAC THEN
    MP_TAC(ISPECL [`\x. (p:num->real^N->real^K) n x - g x`; `k:real^N->bool`]
                  WAN_LSPACE2_NORM_INTEGRABLE) THEN
    ASM_SIMP_TAC[LSPACE_SUB; REAL_POS; ETA_AX];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!a b:real^N->real^K. a measurable_on k /\ b measurable_on k
         ==> (\x. frechet_derivative (P:real^K->real^L) (at (a x)) (b x)) measurable_on k`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC WAN_DP_MEASURABLE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(g:real^N->real^K) measurable_on k /\
                !n. (p:num->real^N->real^K) n measurable_on k`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[WAN_LSPACE_MEASURABLE]; ALL_TAC] THEN
  SUBGOAL_THEN
   `((\n. drop(integral k
              (\x. lift(norm(frechet_derivative (P:real^K->real^L)
                                  (at ((w:num->real^N->real^K) n x)) (g x) -
                              frechet_derivative P (at (u x)) (g x)))))) ---> &0)
    sequentially`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL
     [`\n x. lift(norm(frechet_derivative (P:real^K->real^L)
                          (at ((w:num->real^N->real^K) n x)) ((g:real^N->real^K) x) -
                        frechet_derivative P (at (u x)) (g x)))`;
      `\x:real^N. vec 0:real^1`;
      `\x. lift(&2 * B * norm((g:real^N->real^K) x))`; `k:real^N->bool`; `t:real^N->bool`]
     DOMINATED_CONVERGENCE_AE) THEN
    REWRITE_TAC[INTEGRAL_0] THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [X_GEN_TAC `n:num` THEN
        MATCH_MP_TAC MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_INTEGRABLE THEN
        EXISTS_TAC `\x. lift(&2 * B * norm((g:real^N->real^K) x))` THEN
        REPEAT CONJ_TAC THENL
         [MATCH_MP_TAC MEASURABLE_ON_NORM THEN MATCH_MP_TAC MEASURABLE_ON_SUB THEN
          CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[ETA_AX];
          REWRITE_TAC[LIFT_CMUL] THEN REPEAT(MATCH_MP_TAC INTEGRABLE_CMUL) THEN
          ASM_REWRITE_TAC[];
          X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
          REWRITE_TAC[NORM_LIFT; LIFT_DROP; REAL_ABS_NORM] THEN
          MATCH_MP_TAC(NORM_ARITH
           `norm(a:real^L) <= c /\ norm b <= c ==> norm(a - b) <= &2 * c`) THEN
          ASM_REWRITE_TAC[]];
        REWRITE_TAC[LIFT_CMUL] THEN REPEAT(MATCH_MP_TAC INTEGRABLE_CMUL) THEN
        ASM_REWRITE_TAC[];
        MAP_EVERY X_GEN_TAC [`n:num`; `x:real^N`] THEN DISCH_TAC THEN
        REWRITE_TAC[NORM_LIFT; LIFT_DROP; REAL_ABS_NORM] THEN
        MATCH_MP_TAC(NORM_ARITH
         `norm(a:real^L) <= c /\ norm b <= c ==> norm(a - b) <= &2 * c`) THEN
        ASM_REWRITE_TAC[];
        X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
        REWRITE_TAC[GSYM LIM_NULL_NORM; GSYM LIM_NULL] THEN
        MP_TAC(ISPECL [`\y. frechet_derivative (P:real^K->real^L) (at y) ((g:real^N->real^K) x)`;
                       `sequentially`; `\n. (w:num->real^N->real^K) n x`;
                       `(u:real^N->real^K) x`] LIM_CONTINUOUS_FUNCTION) THEN
        REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[] THEN
        MP_TAC(SPEC `(g:real^N->real^K) x` (ASSUME
          `!h. (\y. frechet_derivative (P:real^K->real^L) (at y) h) continuous_on (:real^K)`)) THEN
        SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_AT; OPEN_UNIV; IN_UNIV]];
      DISCH_THEN(MP_TAC o CONJUNCT2) THEN
      REWRITE_TAC[TENDSTO_REAL; o_DEF; LIFT_DROP; LIFT_NUM]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. (\x. lift(norm(frechet_derivative (P:real^K->real^L)
                         (at ((w:num->real^N->real^K) n x)) ((g:real^N->real^K) x) -
                       frechet_derivative P (at (u x)) (g x)))) integrable_on k`
  ASSUME_TAC THENL
   [X_GEN_TAC `n:num` THEN
    MATCH_MP_TAC MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_INTEGRABLE THEN
    EXISTS_TAC `\x. lift(&2 * B * norm((g:real^N->real^K) x))` THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MEASURABLE_ON_NORM THEN MATCH_MP_TAC MEASURABLE_ON_SUB THEN
      CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[ETA_AX];
      REWRITE_TAC[LIFT_CMUL] THEN REPEAT(MATCH_MP_TAC INTEGRABLE_CMUL) THEN
      ASM_REWRITE_TAC[];
      X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
      REWRITE_TAC[NORM_LIFT; LIFT_DROP; REAL_ABS_NORM] THEN
      MATCH_MP_TAC(NORM_ARITH
       `norm(a:real^L) <= c /\ norm b <= c ==> norm(a - b) <= &2 * c`) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\n x. (p:num->real^N->real^K) n x - g x`; `k:real^N->bool`]
                WAN_L2_TO_L1_CONV) THEN
  ASM_SIMP_TAC[MEASURABLE_COMPACT; LSPACE_SUB; REAL_POS; ETA_AX] THEN DISCH_TAC THEN
  MATCH_MP_TAC REALLIM_NULL_COMPARISON THEN
  EXISTS_TAC
   `\n. B * drop(integral k (\x. lift(norm((p:num->real^N->real^K) n x - g x)))) +
        drop(integral k
          (\x. lift(norm(frechet_derivative (P:real^K->real^L)
                           (at ((w:num->real^N->real^K) n x)) ((g:real^N->real^K) x) -
                         frechet_derivative P (at (u x)) (g x)))))` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    SUBGOAL_THEN `&0 = B * &0 + &0` SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REALLIM_ADD THEN ASM_SIMP_TAC[REALLIM_LMUL]] THEN
  MATCH_MP_TAC ALWAYS_EVENTUALLY THEN X_GEN_TAC `n:num` THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!x. norm(frechet_derivative (P:real^K->real^L) (at ((w:num->real^N->real^K) n x))
               ((p:num->real^N->real^K) n x) -
             frechet_derivative P (at (u x)) ((g:real^N->real^K) x))
        <= B * norm(p n x - g x) +
           norm(frechet_derivative P (at (w n x)) (g x) - frechet_derivative P (at (u x)) (g x))`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^N` THEN
    MP_TAC(ISPECL [`frechet_derivative (P:real^K->real^L) (at ((w:num->real^N->real^K) n x))`;
                   `(p:num->real^N->real^K) n x`; `(g:real^N->real^K) x`] LINEAR_SUB) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC
     `norm(frechet_derivative (P:real^K->real^L) (at ((w:num->real^N->real^K) n x))
             ((p:num->real^N->real^K) n x - g x)) +
      norm(frechet_derivative P (at (w n x)) ((g:real^N->real^K) x) -
           frechet_derivative P (at (u x)) (g x))` THEN
    CONJ_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONV_TAC NORM_ARITH;
      MATCH_MP_TAC(REAL_ARITH `a <= b ==> a + c <= b + c`) THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\x. lift(norm(frechet_derivative (P:real^K->real^L) (at ((w:num->real^N->real^K) n x))
                     ((p:num->real^N->real^K) n x) -
                   frechet_derivative P (at (u x)) ((g:real^N->real^K) x)))) integrable_on k`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_INTEGRABLE THEN
    EXISTS_TAC
     `\x. lift(B * norm((p:num->real^N->real^K) n x - g x) +
               norm(frechet_derivative (P:real^K->real^L) (at ((w:num->real^N->real^K) n x))
                      ((g:real^N->real^K) x) -
                    frechet_derivative P (at (u x)) (g x)))` THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MEASURABLE_ON_NORM THEN MATCH_MP_TAC MEASURABLE_ON_SUB THEN
      CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[ETA_AX];
      REWRITE_TAC[LIFT_ADD; LIFT_CMUL] THEN MATCH_MP_TAC INTEGRABLE_ADD THEN
      ASM_SIMP_TAC[INTEGRABLE_CMUL];
      ASM_REWRITE_TAC[NORM_LIFT; LIFT_DROP; REAL_ABS_NORM]];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= a /\ a <= b ==> abs a <= b`) THEN CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRAL_DROP_POS THEN ASM_REWRITE_TAC[LIFT_DROP; NORM_POS_LE];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `drop(integral k (\x. lift(B * norm((p:num->real^N->real^K) n x - g x) +
               norm(frechet_derivative (P:real^K->real^L) (at ((w:num->real^N->real^K) n x))
                      ((g:real^N->real^K) x) -
                    frechet_derivative P (at (u x)) (g x)))))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRAL_DROP_LE THEN ASM_REWRITE_TAC[LIFT_DROP] THEN
    REWRITE_TAC[LIFT_ADD; LIFT_CMUL] THEN MATCH_MP_TAC INTEGRABLE_ADD THEN
    ASM_SIMP_TAC[INTEGRABLE_CMUL];
    REWRITE_TAC[LIFT_ADD; LIFT_CMUL] THEN
    ASM_SIMP_TAC[INTEGRAL_ADD; INTEGRAL_CMUL; INTEGRABLE_CMUL; DROP_ADD; DROP_CMUL;
                 REAL_LE_REFL]]);;

let WAN_CHAIN_WPD = prove
 (`!(s:real^N->bool) (u:real^N->real^K) (g:num->real^N->real^K) (P:real^K->real^L) B i.
     open s /\ wan_l2loc s u /\
     (!i. 1 <= i /\ i <= dimindex(:N) ==> wan_l2loc s (g i) /\ wan_wpd s i u (g i)) /\
     continuously_differentiable 1 (:real^K) P /\
     (!y. onorm(frechet_derivative P (at y)) <= B) /\
     1 <= i /\ i <= dimindex(:N)
     ==> wan_wpd s i (\x. P(u x)) (\x. frechet_derivative P (at (u x)) (g i x))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`P:real^K->real^L`; `B:real`] WAN_C1_BOUNDED_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `wan_l2loc s ((g:num->real^N->real^K) i) /\ wan_wpd s i (u:real^N->real^K) (g i)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `u:real^N->real^K`; `(g:num->real^N->real^K) i`;
                 `P:real^K->real^L`; `B:real`] WAN_CHAIN_LLOC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[wan_wpd] THEN X_GEN_TAC `phi:real^N->real` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `phi:real^N->real`; `i:num`] WAN_TEST_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `kp:real^N->bool` (X_CHOOSE_THEN `M:real` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `phi:real^N->real`; `i:num`] WAN_TEST_CONTINUOUS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `u:real^N->real^K`; `g:num->real^N->real^K`;
                 `kp:real^N->bool`] WAN_W12_LOCAL_APPROX) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:num->real^N->real^K` (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (MP_TAC o SPEC `i:num`)
   (X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC))))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!n. smooth_map_on (:real^N) ((w:num->real^N->real^K) n) /\
        (w n) continuous_on (:real^N) /\
        (\x. partial_derivative i (w n) x) continuous_on (:real^N) /\
        wan_l2loc s (w n) /\ wan_l2loc s (\x. partial_derivative i (w n) x)`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [wan_vtest] o SPEC `n:num` o
      check (fun th -> can (find_term ((=) `wan_vtest:(real^N->bool)->(real^N->real^K)->bool`))
                           (concl th))) THEN
    MP_TAC(ISPECL [`s:real^N->bool`; `(w:num->real^N->real^K) n`; `k:real^N->bool`; `i:num`]
                  WAN_VTEST_PARTIAL) THEN
    ASM_REWRITE_TAC[wan_vtest] THEN ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    STRIP_TAC THEN ASM_SIMP_TAC[WAN_CONTINUOUS_ON_L2LOC; CONTINUOUS_ON_SUBSET; SUBSET_UNIV] THEN
    CONJ_TAC THEN MATCH_MP_TAC WAN_CONTINUOUS_ON_L2LOC THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^N)` THEN
    ASM_REWRITE_TAC[SUBSET_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. integral s (\x. wan_dpart i (phi:real^N->real) x %
                         (P:real^K->real^L)((w:num->real^N->real^K) n x)) =
        --(integral s (\x. phi x % frechet_derivative P (at (w n x))
                                      (partial_derivative i (w n) x)))`
  ASSUME_TAC THENL
   [X_GEN_TAC `n:num` THEN
    SUBGOAL_THEN
     `wan_wpd s i (\x. (P:real^K->real^L)((w:num->real^N->real^K) n x))
        (\x. frechet_derivative P (at (w n x)) (partial_derivative i (w n) x))`
    MP_TAC THENL
     [SUBGOAL_THEN
       `continuously_differentiable 1 (:real^N)
          (\x. (P:real^K->real^L)((w:num->real^N->real^K) n x))`
      ASSUME_TAC THENL
       [SUBGOAL_THEN `(\x. (P:real^K->real^L)((w:num->real^N->real^K) n x)) = P o w n`
        SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
        MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_COMPOSE_OPEN THEN
        EXISTS_TAC `(:real^K)` THEN ASM_REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV] THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `n:num` o check (fun th ->
          can (find_term ((=) `smooth_map_on:(real^N->bool)->(real^N->real^K)->bool`))
              (concl th))) THEN
        SIMP_TAC[SMOOTH_MAP_ON_OPEN_UNIV];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`s:real^N->bool`;
                     `\x. (P:real^K->real^L)((w:num->real^N->real^K) n x)`; `i:num`]
                    WAN_WPD_C1) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_SUBSET THEN
        EXISTS_TAC `(:real^N)` THEN ASM_REWRITE_TAC[SUBSET_UNIV];
        ALL_TAC] THEN
      MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
      X_GEN_TAC `x:real^N` THEN REWRITE_TAC[partial_derivative] THEN
      SUBGOAL_THEN
       `(((P:real^K->real^L) o (w:num->real^N->real^K) n) has_derivative
         (frechet_derivative P (at (w n x)) o frechet_derivative (w n) (at x))) (at x)`
      MP_TAC THENL
       [MATCH_MP_TAC DIFF_CHAIN_AT THEN ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
        MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `(:real^N)` THEN
        ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV];
        ALL_TAC] THEN
      DISCH_THEN(MP_TAC o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
      REWRITE_TAC[o_DEF; FUN_EQ_THM] THEN DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]);
      ALL_TAC] THEN
    REWRITE_TAC[wan_wpd] THEN
    DISCH_THEN(MP_TAC o SPEC `phi:real^N->real` o CONJUNCT2 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(!n. (w:num->real^N->real^K) n IN lspace kp (&2)) /\ (u:real^N->real^K) IN lspace kp (&2) /\
    (!n. (\x. partial_derivative i (w n) x) IN lspace kp (&2)) /\
    (g:num->real^N->real^K) i IN lspace kp (&2)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[wan_l2loc]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(!n. (w:num->real^N->real^K) n measurable_on kp) /\ (u:real^N->real^K) measurable_on kp /\
    (!n. partial_derivative i (w n) IN lspace kp (&2))`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [GEN_TAC THEN MATCH_MP_TAC WAN_LSPACE_MEASURABLE THEN EXISTS_TAC `&2` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC WAN_LSPACE_MEASURABLE THEN EXISTS_TAC `&2` THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `n:num` THEN
      MP_TAC(SPEC `n:num` (ASSUME
        `!n. (\x. partial_derivative i ((w:num->real^N->real^K) n) x) IN lspace kp (&2)`)) THEN
      REWRITE_TAC[ETA_AX]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. wan_lloc s (\x. (P:real^K->real^L)((w:num->real^N->real^K) n x)) /\
        wan_lloc s (\x. frechet_derivative P (at (w n x)) (partial_derivative i (w n) x))`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`s:real^N->bool`; `(w:num->real^N->real^K) n`;
                   `\x. partial_derivative i ((w:num->real^N->real^K) n) x`;
                   `P:real^K->real^L`; `B:real`] WAN_CHAIN_LLOC) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC(ISPEC `sequentially` LIM_UNIQUE) THEN
  EXISTS_TAC `\n. integral s (\x. wan_dpart i (phi:real^N->real) x %
                                  (P:real^K->real^L)((w:num->real^N->real^K) n x))` THEN
  REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN CONJ_TAC THENL
   [MATCH_MP_TAC WAN_WEIGHTED_L1_LIMIT THEN
    MAP_EVERY EXISTS_TAC [`kp:real^N->bool`; `M:real`] THEN
    ASM_SIMP_TAC[LEBESGUE_MEASURABLE_OPEN] THEN REPEAT CONJ_TAC THENL
     [GEN_TAC THEN ASM_MESON_TAC[wan_lloc];
      ASM_MESON_TAC[wan_lloc];
      MATCH_MP_TAC WAN_COMPOSE_L1_CONV THEN EXISTS_TAC `B:real` THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [GEN_TAC THEN ASM_MESON_TAC[wan_lloc]; ASM_MESON_TAC[wan_lloc]]];
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LIM_NEG THEN
    MATCH_MP_TAC WAN_WEIGHTED_L1_LIMIT THEN
    MAP_EVERY EXISTS_TAC [`kp:real^N->bool`; `M:real`] THEN
    ASM_SIMP_TAC[LEBESGUE_MEASURABLE_OPEN] THEN REPEAT CONJ_TAC THENL
     [GEN_TAC THEN ASM_MESON_TAC[wan_lloc];
      ASM_MESON_TAC[wan_lloc];
      MATCH_MP_TAC WAN_DP_L1_CONV THEN
      MAP_EVERY EXISTS_TAC [`B:real`; `t:real^N->bool`] THEN
      ASM_SIMP_TAC[WAN_LSPACE_MEASURABLE; ETA_AX]]]);;

let WAN_CHAIN_W12 = prove
 (`!(n:N->bool) (kk:K->bool) (ll:L->bool). WAN_CHAIN_W12_STATEMENT n kk ll`,
  REWRITE_TAC[WAN_CHAIN_W12_STATEMENT] THEN
  MAP_EVERY X_GEN_TAC [`s:real^N->bool`; `u:real^N->real^K`; `P:real^K->real^L`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (X_CHOOSE_TAC `B:real`))))) THEN
  MP_TAC(ISPECL [`P:real^K->real^L`; `B:real`] WAN_C1_BOUNDED_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(u:real^N->real^K) IN lspace s (&2)` ASSUME_TAC THENL
   [ASM_MESON_TAC[wan_w12]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= dimindex(:N)
        ==> wan_wd s i (u:real^N->real^K) IN lspace s (&2) /\ wan_wpd s i u (wan_wd s i u)`
  ASSUME_TAC THENL [ASM_SIMP_TAC[WAN_WD_WORKS]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= dimindex(:N)
        ==> wan_wpd s i (\x. (P:real^K->real^L)((u:real^N->real^K) x))
              (\x. frechet_derivative P (at (u x)) (wan_wd s i u x))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`s:real^N->bool`; `u:real^N->real^K`; `\i. wan_wd s i (u:real^N->real^K)`;
                   `P:real^K->real^L`; `B:real`; `i:num`] WAN_CHAIN_WPD) THEN
    ASM_SIMP_TAC[WAN_LSPACE2_IMP_L2LOC; ETA_AX];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[wan_w12] THEN
  SUBGOAL_THEN `lebesgue_measurable(s:real^N->bool) /\ measurable s` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[LEBESGUE_MEASURABLE_OPEN; MEASURABLE_OPEN]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= B` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`vec 0:real^K`; `basis 1:real^K`] o check (fun th ->
      can (find_term ((=) `B:real`)) (concl th) && is_forall(concl th) &&
      can (find_term ((=) `h:real^K`)) (concl th))) THEN
    SIMP_TAC[NORM_BASIS; DIMINDEX_GE_1; LE_REFL] THEN
    MP_TAC(ISPEC `frechet_derivative (P:real^K->real^L) (at (vec 0)) (basis 1)` NORM_POS_LE) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`s:real^N->bool`; `&2`; `\x. (P:real^K->real^L)((u:real^N->real^K) x)`;
                   `\x. lift(norm((P:real^K->real^L)(vec 0))) +
                        lift(B * norm((u:real^N->real^K) x))`] LSPACE_BOUNDED_MEASURABLE) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    REPEAT CONJ_TAC THENL
     [REAL_ARITH_TAC;
      MATCH_MP_TAC WAN_MEASURABLE_COMPOSE_CONT THEN ASM_SIMP_TAC[] THEN
      MATCH_MP_TAC WAN_LSPACE_MEASURABLE THEN EXISTS_TAC `&2` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC LSPACE_ADD THEN ASM_SIMP_TAC[LSPACE_CONST; REAL_POS] THEN
      REWRITE_TAC[LIFT_CMUL] THEN MATCH_MP_TAC LSPACE_CMUL THEN
      MATCH_MP_TAC LSPACE_NORM THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
      REWRITE_TAC[GSYM LIFT_ADD; NORM_LIFT] THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`(u:real^N->real^K) x`; `vec 0:real^K`] o
        check (fun th -> can (find_term ((=) `(P:real^K->real^L) z`)) (concl th))) THEN
      REWRITE_TAC[VECTOR_SUB_RZERO] THEN
      MP_TAC(ISPECL [`(P:real^K->real^L)((u:real^N->real^K) x) - P(vec 0)`;
                     `(P:real^K->real^L)(vec 0)`] NORM_TRIANGLE) THEN
      REWRITE_TAC[VECTOR_SUB_ADD] THEN
      MP_TAC(ISPEC `(u:real^N->real^K) x` NORM_POS_LE) THEN
      MP_TAC(ISPEC `(P:real^K->real^L)(vec 0)` NORM_POS_LE) THEN
      SUBGOAL_THEN `&0 <= B * norm((u:real^N->real^K) x)` MP_TAC THENL
       [ASM_SIMP_TAC[REAL_LE_MUL; NORM_POS_LE]; ALL_TAC] THEN
      REAL_ARITH_TAC];
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    EXISTS_TAC `\x. frechet_derivative (P:real^K->real^L) (at ((u:real^N->real^K) x))
                      (wan_wd s i u x)` THEN
    ASM_SIMP_TAC[] THEN
    MP_TAC(ISPECL [`s:real^N->bool`; `&2`;
                   `\x. frechet_derivative (P:real^K->real^L) (at ((u:real^N->real^K) x))
                          (wan_wd s i u x)`;
                   `\x. B % wan_wd s i (u:real^N->real^K) x`] LSPACE_BOUNDED_MEASURABLE) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    REPEAT CONJ_TAC THENL
     [REAL_ARITH_TAC;
      MATCH_MP_TAC WAN_DP_MEASURABLE THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
      MATCH_MP_TAC WAN_LSPACE_MEASURABLE THEN EXISTS_TAC `&2` THEN
      REWRITE_TAC[ETA_AX] THEN ASM_SIMP_TAC[];
      MATCH_MP_TAC LSPACE_CMUL THEN REWRITE_TAC[ETA_AX] THEN ASM_SIMP_TAC[];
      X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
      ASM_REWRITE_TAC[NORM_MUL] THEN ASM_SIMP_TAC[REAL_ARITH `&0 <= B ==> abs B = B`]]]);;

(* ------------------------------------------------------------------------- *)
(* W^(1,2) algebra: sums and differences, expansion of the Dirichlet         *)
(* integral, test maps are in W^(1,2) and W^(1,2)_0, W^(1,2)_0 is closed     *)
(* under sums, differences and W^(1,2) limits.                               *)
(* ------------------------------------------------------------------------- *)

let WAN_LSPACE2_DOT_INTEGRABLE = prove
 (`!(s:real^N->bool) (f:real^N->real^K) g.
     f IN lspace s (&2) /\ g IN lspace s (&2)
     ==> (\x. lift(f x dot g x)) integrable_on s`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_INTEGRABLE THEN
  EXISTS_TAC `\x. lift(norm((f:real^N->real^K) x) * norm((g:real^N->real^K) x))` THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`\x y:real^K. lift(x dot y)`; `f:real^N->real^K`; `g:real^N->real^K`;
                   `s:real^N->bool`] MEASURABLE_ON_BILINEAR) THEN
    REWRITE_TAC[BILINEAR_DOT] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_MESON_TAC[WAN_LSPACE_MEASURABLE];
    MATCH_MP_TAC LSPACE_INTEGRABLE_PRODUCT THEN
    MAP_EVERY EXISTS_TAC [`&2`; `&2`] THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV;
    REWRITE_TAC[NORM_LIFT; LIFT_DROP; NORM_CAUCHY_SCHWARZ_ABS]]);;

let WAN_W12_ADD_WD = prove
 (`!(s:real^N->bool) (u:real^N->real^K) v.
     wan_w12 s u /\ wan_w12 s v
     ==> wan_w12 s (\x. u x + v x) /\
         !i. 1 <= i /\ i <= dimindex(:N)
             ==> wan_wpd s i (\x. u x + v x) (\x. wan_wd s i u x + wan_wd s i v x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= dimindex(:N)
        ==> wan_wpd s i (\x. (u:real^N->real^K) x + v x) (\x. wan_wd s i u x + wan_wd s i v x)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC WAN_WPD_ADD THEN ASM_SIMP_TAC[WAN_WD_WORKS; ETA_AX];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[wan_w12] THEN CONJ_TAC THENL
   [MATCH_MP_TAC LSPACE_ADD THEN REWRITE_TAC[REAL_POS] THEN ASM_MESON_TAC[wan_w12];
    REPEAT STRIP_TAC THEN
    EXISTS_TAC `\x. wan_wd s i (u:real^N->real^K) x + wan_wd s i v x` THEN
    ASM_SIMP_TAC[] THEN MATCH_MP_TAC LSPACE_ADD THEN
    ASM_SIMP_TAC[REAL_POS; WAN_WD_WORKS; ETA_AX]]);;

let WAN_W12_SUB_WD = prove
 (`!(s:real^N->bool) (u:real^N->real^K) v.
     wan_w12 s u /\ wan_w12 s v
     ==> wan_w12 s (\x. u x - v x) /\
         !i. 1 <= i /\ i <= dimindex(:N)
             ==> wan_wpd s i (\x. u x - v x) (\x. wan_wd s i u x - wan_wd s i v x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= dimindex(:N)
        ==> wan_wpd s i (\x. (u:real^N->real^K) x - v x) (\x. wan_wd s i u x - wan_wd s i v x)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC WAN_WPD_SUB THEN ASM_SIMP_TAC[WAN_WD_WORKS; ETA_AX];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[wan_w12] THEN CONJ_TAC THENL
   [MATCH_MP_TAC LSPACE_SUB THEN REWRITE_TAC[REAL_POS] THEN ASM_MESON_TAC[wan_w12];
    REPEAT STRIP_TAC THEN
    EXISTS_TAC `\x. wan_wd s i (u:real^N->real^K) x - wan_wd s i v x` THEN
    ASM_SIMP_TAC[] THEN MATCH_MP_TAC LSPACE_SUB THEN
    ASM_SIMP_TAC[REAL_POS; WAN_WD_WORKS; ETA_AX]]);;

let WAN_NORM_ADD_SUB_POW2 = prove
 (`!x y:real^N. norm(x + y) pow 2 = norm x pow 2 + norm y pow 2 + &2 * (x dot y) /\
                norm(x - y) pow 2 = norm x pow 2 + norm y pow 2 - &2 * (x dot y)`,
  REWRITE_TAC[NORM_POW_2; DOT_LADD; DOT_RADD; DOT_LSUB; DOT_RSUB; DOT_SYM] THEN
  REAL_ARITH_TAC);;

let WAN_INTEGRAL_SQ_EXPAND = prove
 (`!(s:real^N->bool) (a:real^N->real^K) b.
     a IN lspace s (&2) /\ b IN lspace s (&2)
     ==> drop(integral s (\x. lift(norm(a x + b x) pow 2))) =
         drop(integral s (\x. lift(norm(a x) pow 2))) +
         drop(integral s (\x. lift(norm(b x) pow 2))) +
         &2 * drop(integral s (\x. lift(a x dot b x))) /\
         drop(integral s (\x. lift(norm(a x - b x) pow 2))) =
         drop(integral s (\x. lift(norm(a x) pow 2))) +
         drop(integral s (\x. lift(norm(b x) pow 2))) -
         &2 * drop(integral s (\x. lift(a x dot b x)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `a:real^N->real^K`; `b:real^N->real^K`]
                WAN_LSPACE2_DOT_INTEGRABLE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `(\x. lift(norm((a:real^N->real^K) x) pow 2)) integrable_on s /\
    (\x. lift(norm((b:real^N->real^K) x) pow 2)) integrable_on s`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[WAN_LSPACE2_SQNORM_INTEGRABLE]; ALL_TAC] THEN
  REWRITE_TAC[WAN_NORM_ADD_SUB_POW2; LIFT_ADD; LIFT_SUB; LIFT_CMUL] THEN
  ASM_SIMP_TAC[INTEGRAL_ADD; INTEGRAL_SUB; INTEGRAL_CMUL; INTEGRABLE_ADD; INTEGRABLE_SUB; INTEGRABLE_CMUL;
               DROP_ADD; DROP_SUB; DROP_CMUL]);;

let WAN_DIR_ADD = prove
 (`!(s:real^N->bool) (u:real^N->real^K) v.
     open s /\ wan_w12 s u /\ wan_w12 s v
     ==> wan_w12 s (\x. u x + v x) /\
         wan_dir s (\x. u x + v x) =
         wan_dir s u + wan_dir s v +
         &2 * sum(1..dimindex(:N))
                (\i. drop(integral s (\x. lift(wan_wd s i u x dot wan_wd s i v x))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `u:real^N->real^K`; `v:real^N->real^K`] WAN_W12_ADD_WD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `\x. (u:real^N->real^K) x + v x`;
                 `\i x. wan_wd s i (u:real^N->real^K) x + wan_wd s i v x`] WAN_DIR_EQ) THEN
  ASM_SIMP_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[wan_dir; GSYM SUM_LMUL; GSYM SUM_ADD_NUMSEG] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `wan_wd s i (u:real^N->real^K)`;
                 `wan_wd s i (v:real^N->real^K)`] WAN_INTEGRAL_SQ_EXPAND) THEN
  ASM_SIMP_TAC[WAN_WD_WORKS]);;

let WAN_DIR_SUB = prove
 (`!(s:real^N->bool) (u:real^N->real^K) v.
     open s /\ wan_w12 s u /\ wan_w12 s v
     ==> wan_w12 s (\x. u x - v x) /\
         wan_dir s (\x. u x - v x) =
         wan_dir s u + wan_dir s v -
         &2 * sum(1..dimindex(:N))
                (\i. drop(integral s (\x. lift(wan_wd s i u x dot wan_wd s i v x))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `u:real^N->real^K`; `v:real^N->real^K`] WAN_W12_SUB_WD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `\x. (u:real^N->real^K) x - v x`;
                 `\i x. wan_wd s i (u:real^N->real^K) x - wan_wd s i v x`] WAN_DIR_EQ) THEN
  ASM_SIMP_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[wan_dir; GSYM SUM_LMUL; GSYM SUM_ADD_NUMSEG; GSYM SUM_SUB_NUMSEG] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `wan_wd s i (u:real^N->real^K)`;
                 `wan_wd s i (v:real^N->real^K)`] WAN_INTEGRAL_SQ_EXPAND) THEN
  ASM_SIMP_TAC[WAN_WD_WORKS]);;

let WAN_DIR_ADD_LE = prove
 (`!(s:real^N->bool) (u:real^N->real^K) v.
     open s /\ wan_w12 s u /\ wan_w12 s v
     ==> wan_dir s (\x. u x + v x) <= &2 * wan_dir s u + &2 * wan_dir s v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `u:real^N->real^K`; `v:real^N->real^K`] WAN_DIR_ADD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN
  MATCH_MP_TAC(REAL_ARITH `&2 * a <= u + v ==> u + v + &2 * a <= &2 * u + &2 * v`) THEN
  REWRITE_TAC[wan_dir; GSYM SUM_LMUL; GSYM SUM_ADD_NUMSEG] THEN
  MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `wan_wd s i (u:real^N->real^K)`;
                 `wan_wd s i (v:real^N->real^K)`] WAN_INTEGRAL_SQ_EXPAND) THEN
  ASM_SIMP_TAC[WAN_WD_WORKS] THEN DISCH_THEN(MP_TAC o CONJUNCT2) THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= c ==> c = a + b - &2 * d ==> &2 * d <= a + b`) THEN
  MATCH_MP_TAC INTEGRAL_DROP_POS THEN REWRITE_TAC[LIFT_DROP; REAL_LE_POW_2] THEN
  MATCH_MP_TAC WAN_LSPACE2_SQNORM_INTEGRABLE THEN MATCH_MP_TAC LSPACE_SUB THEN
  ASM_SIMP_TAC[WAN_WD_WORKS; REAL_POS; ETA_AX]);;

let WAN_VTEST_W12 = prove
 (`!(s:real^N->bool) (f:real^N->real^K).
     open s /\ wan_vtest s f
     ==> wan_w12 s f /\
         !i. 1 <= i /\ i <= dimindex(:N)
             ==> wan_wpd s i f (\x. partial_derivative i f x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [wan_vtest]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `k:real^N->bool` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `!i. wan_wpd s i (f:real^N->real^K) (\x. partial_derivative i f x)`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC WAN_WPD_C1 THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_SUBSET THEN EXISTS_TAC `(:real^N)` THEN
    ASM_MESON_TAC[SUBSET_UNIV; SMOOTH_MAP_ON_OPEN_UNIV];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[wan_w12] THEN CONJ_TAC THENL
   [MATCH_MP_TAC WAN_LSPACE2_CONT_SUPPORT THEN EXISTS_TAC `k:real^N->bool` THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON];
    REPEAT STRIP_TAC THEN EXISTS_TAC `\x. partial_derivative i (f:real^N->real^K) x` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC WAN_LSPACE2_CONT_SUPPORT THEN
    EXISTS_TAC `k:real^N->bool` THEN
    MP_TAC(ISPECL [`s:real^N->bool`; `f:real^N->real^K`; `k:real^N->bool`; `i:num`]
                  WAN_VTEST_PARTIAL) THEN
    ASM_SIMP_TAC[]]);;

let WAN_DIR_ZERO = prove
 (`!(s:real^N->bool). open s ==> wan_dir s (\x. vec 0:real^K) = &0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `\x:real^N. vec 0:real^K`; `\i:num x:real^N. vec 0:real^K`]
                WAN_DIR_EQ) THEN
  ASM_REWRITE_TAC[WAN_WPD_ZERO; wan_w12; WAN_LSPACE2_ZERO] THEN
  ANTS_TAC THENL [MESON_TAC[WAN_WPD_ZERO; WAN_LSPACE2_ZERO]; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[NORM_0; REAL_POW_ZERO; ARITH_EQ; LIFT_NUM; INTEGRAL_0; DROP_VEC; SUM_0]);;

let WAN_VTEST_W120 = prove
 (`!(s:real^N->bool) (f:real^N->real^K). open s /\ wan_vtest s f ==> wan_w120 s f`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[wan_w120] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[WAN_VTEST_W12]; ALL_TAC] THEN
  EXISTS_TAC `\n:num. (f:real^N->real^K)` THEN
  ASM_SIMP_TAC[VECTOR_SUB_REFL; WAN_DIR_ZERO] THEN
  REWRITE_TAC[REALLIM_CONST] THEN
  SUBGOAL_THEN `lnorm s (&2) (\x:real^N. vec 0:real^K) = &0` SUBST1_TAC THENL
   [MATCH_MP_TAC LNORM_0 THEN REAL_ARITH_TAC; REWRITE_TAC[REALLIM_CONST]]);;

let WAN_VTEST_ADD = prove
 (`!(s:real^N->bool) (f:real^N->real^K) g.
     wan_vtest s f /\ wan_vtest s g ==> wan_vtest s (\x. f x + g x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wan_vtest] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `k1:real^N->bool` STRIP_ASSUME_TAC))
    (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `k2:real^N->bool` STRIP_ASSUME_TAC))) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN ASM_REWRITE_TAC[OPEN_UNIV];
    EXISTS_TAC `k1 UNION k2:real^N->bool` THEN ASM_SIMP_TAC[COMPACT_UNION] THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_UNION; DE_MORGAN_THM] THEN ASM_SIMP_TAC[VECTOR_ADD_LID]]);;

let WAN_VTEST_NEG = prove
 (`!(s:real^N->bool) (f:real^N->real^K). wan_vtest s f ==> wan_vtest s (\x. --(f x))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wan_vtest] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `k:real^N->bool` STRIP_ASSUME_TAC)) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_NEG_OPEN THEN ASM_REWRITE_TAC[OPEN_UNIV];
    EXISTS_TAC `k:real^N->bool` THEN ASM_SIMP_TAC[VECTOR_NEG_0]]);;

let WAN_W12_IMP_LSPACE = prove
 (`!(s:real^N->bool) (u:real^N->real^K). wan_w12 s u ==> u IN lspace s (&2)`,
  SIMP_TAC[wan_w12]);;

let WAN_W120_APPROX_ADD = prove
 (`!(s:real^N->bool) (u:real^N->real^K) v f g.
     open s /\ wan_w12 s u /\ wan_w12 s v /\
     (!n. wan_vtest s (f n)) /\ (!n. wan_vtest s (g n)) /\
     ((\n. lnorm s (&2) (\x. f n x - u x)) ---> &0) sequentially /\
     ((\n. wan_dir s (\x. f n x - u x)) ---> &0) sequentially /\
     ((\n. lnorm s (&2) (\x. g n x - v x)) ---> &0) sequentially /\
     ((\n. wan_dir s (\x. g n x - v x)) ---> &0) sequentially
     ==> ((\n. lnorm s (&2) (\x. (f n x + g n x) - (u x + v x))) ---> &0) sequentially /\
         ((\n. wan_dir s (\x. (f n x + g n x) - (u x + v x))) ---> &0) sequentially`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!n. wan_w12 s (\x. (f:num->real^N->real^K) n x - u x) /\
        wan_w12 s (\x. (g:num->real^N->real^K) n x - v x)`
  ASSUME_TAC THENL
   [GEN_TAC THEN CONJ_TAC THEN MATCH_MP_TAC WAN_W12_SUB THEN ASM_REWRITE_TAC[ETA_AX] THENL
     [MP_TAC(ISPECL [`s:real^N->bool`; `(f:num->real^N->real^K) n`] WAN_VTEST_W12);
      MP_TAC(ISPECL [`s:real^N->bool`; `(g:num->real^N->real^K) n`] WAN_VTEST_W12)] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. (\x. (f:num->real^N->real^K) n x - u x) IN lspace s (&2) /\
        (\x. (g:num->real^N->real^K) n x - v x) IN lspace s (&2)`
  ASSUME_TAC THENL [ASM_SIMP_TAC[WAN_W12_IMP_LSPACE]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. (\x. ((f:num->real^N->real^K) n x + g n x) - (u x + v x)) =
        (\x. (f n x - u x) + (g n x - v x))`
  (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN REPEAT GEN_TAC THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THEN MATCH_MP_TAC REALLIM_NULL_COMPARISON THENL
   [EXISTS_TAC `\n. lnorm s (&2) (\x. (f:num->real^N->real^K) n x - u x) +
                    lnorm s (&2) (\x. (g:num->real^N->real^K) n x - v x)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC ALWAYS_EVENTUALLY THEN X_GEN_TAC `n:num` THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= a /\ a <= b ==> abs a <= b`) THEN CONJ_TAC THENL
       [MATCH_MP_TAC LNORM_POS_LE THEN MATCH_MP_TAC LSPACE_ADD THEN
        ASM_REWRITE_TAC[REAL_POS];
        MP_TAC(ISPECL [`s:real^N->bool`; `&2`;
                       `\x. (f:num->real^N->real^K) n x - u x`;
                       `\x. (g:num->real^N->real^K) n x - v x`] LNORM_TRIANGLE) THEN
        ASM_REWRITE_TAC[] THEN REWRITE_TAC[REAL_ARITH `&1 <= &2`]];
      SUBGOAL_THEN `&0 = &0 + &0` SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REALLIM_ADD THEN ASM_REWRITE_TAC[]];
    EXISTS_TAC `\n. &2 * wan_dir s (\x. (f:num->real^N->real^K) n x - u x) +
                    &2 * wan_dir s (\x. (g:num->real^N->real^K) n x - v x)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC ALWAYS_EVENTUALLY THEN X_GEN_TAC `n:num` THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= a /\ a <= b ==> abs a <= b`) THEN CONJ_TAC THENL
       [MATCH_MP_TAC WAN_DIR_POS THEN MATCH_MP_TAC WAN_W12_ADD THEN
        ASM_REWRITE_TAC[];
        MATCH_MP_TAC WAN_DIR_ADD_LE THEN ASM_REWRITE_TAC[]];
      SUBGOAL_THEN `&0 = &2 * &0 + &2 * &0` SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REALLIM_ADD THEN CONJ_TAC THEN MATCH_MP_TAC REALLIM_LMUL THEN
      ASM_REWRITE_TAC[]]]);;

let WAN_W120_ADD = prove
 (`!(s:real^N->bool) (u:real^N->real^K) v.
     open s /\ wan_w120 s u /\ wan_w120 s v ==> wan_w120 s (\x. u x + v x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wan_w120] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
    (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `f:num->real^N->real^K` STRIP_ASSUME_TAC))
    (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `g:num->real^N->real^K` STRIP_ASSUME_TAC)))) THEN
  ASM_SIMP_TAC[WAN_W12_ADD] THEN
  EXISTS_TAC `\n x. (f:num->real^N->real^K) n x + g n x` THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC WAN_VTEST_ADD THEN ASM_REWRITE_TAC[ETA_AX];
    MATCH_MP_TAC WAN_W120_APPROX_ADD THEN ASM_REWRITE_TAC[]]);;

let WAN_DIR_NEG = prove
 (`!(s:real^N->bool) (u:real^N->real^K).
     open s /\ wan_w12 s u
     ==> wan_w12 s (\x. --(u x)) /\ wan_dir s (\x. --(u x)) = wan_dir s u`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= dimindex(:N)
        ==> wan_wpd s i (\x. --((u:real^N->real^K) x)) (\x. --(wan_wd s i u x))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC WAN_WPD_NEG THEN ASM_SIMP_TAC[WAN_WD_WORKS; ETA_AX];
    ALL_TAC] THEN
  SUBGOAL_THEN `wan_w12 s (\x. --((u:real^N->real^K) x))` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[wan_w12] THEN CONJ_TAC THENL
     [MATCH_MP_TAC LSPACE_NEG THEN ASM_SIMP_TAC[WAN_W12_IMP_LSPACE; ETA_AX];
      REPEAT STRIP_TAC THEN EXISTS_TAC `\x. --(wan_wd s i (u:real^N->real^K) x)` THEN
      ASM_SIMP_TAC[] THEN MATCH_MP_TAC LSPACE_NEG THEN ASM_SIMP_TAC[WAN_WD_WORKS; ETA_AX]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `\x. --((u:real^N->real^K) x)`;
                 `\i x. --(wan_wd s i (u:real^N->real^K) x)`] WAN_DIR_EQ) THEN
  ASM_SIMP_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[wan_dir; NORM_NEG]);;

let WAN_W120_NEG = prove
 (`!(s:real^N->bool) (u:real^N->real^K).
     open s /\ wan_w120 s u ==> wan_w120 s (\x. --(u x))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wan_w120] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `f:num->real^N->real^K` STRIP_ASSUME_TAC))) THEN
  ASM_SIMP_TAC[WAN_DIR_NEG] THEN
  EXISTS_TAC `\n x. --((f:num->real^N->real^K) n x)` THEN
  ASM_SIMP_TAC[WAN_VTEST_NEG] THEN
  SUBGOAL_THEN
   `!n. (\x. --((f:num->real^N->real^K) n x) - --(u x)) = (\x. --(f n x - u x))`
  (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN REPEAT GEN_TAC THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!n. wan_w12 s (\x. (f:num->real^N->real^K) n x - u x)` ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC WAN_W12_SUB THEN ASM_REWRITE_TAC[ETA_AX] THEN
    MP_TAC(ISPECL [`s:real^N->bool`; `(f:num->real^N->real^K) n`] WAN_VTEST_W12) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[WAN_DIR_NEG; LNORM_NEG] THEN
  GEN_TAC THEN MATCH_MP_TAC WAN_VTEST_NEG THEN ASM_REWRITE_TAC[ETA_AX]);;

let WAN_W120_SUB = prove
 (`!(s:real^N->bool) (u:real^N->real^K) v.
     open s /\ wan_w120 s u /\ wan_w120 s v ==> wan_w120 s (\x. u x - v x)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\x. (u:real^N->real^K) x - v x) = (\x. u x + --(v x))` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC WAN_W120_ADD THEN ASM_SIMP_TAC[WAN_W120_NEG]);;

let WAN_INV_N1_LIM = prove
 (`((\n. inv(&n + &1)) ---> &0) sequentially`,
  MATCH_MP_TAC REALLIM_NULL_COMPARISON THEN EXISTS_TAC `\n. inv(&n)` THEN
  REWRITE_TAC[REALLIM_1_OVER_N; EVENTUALLY_SEQUENTIALLY] THEN
  EXISTS_TAC `1` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `&1 <= &n` ASSUME_TAC THENL [ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_ABS_INV; REAL_ARITH `&1 <= x ==> abs(x + &1) = x + &1`] THEN
  MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC);;

let WAN_W120_LIMIT = prove
 (`!(s:real^N->bool) (u:real^N->real^K) (w:num->real^N->real^K).
     open s /\ wan_w12 s u /\ (!n. wan_w120 s (w n)) /\
     ((\n. lnorm s (&2) (\x. w n x - u x)) ---> &0) sequentially /\
     ((\n. wan_dir s (\x. w n x - u x)) ---> &0) sequentially
     ==> wan_w120 s u`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!n. ?psi. wan_vtest s psi /\
              lnorm s (&2) (\x. psi x - (w:num->real^N->real^K) n x) < inv(&n + &1) /\
              wan_dir s (\x. psi x - w n x) < inv(&n + &1)`
  MP_TAC THENL
   [X_GEN_TAC `m:num` THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `m:num` o check (fun th ->
      can (find_term ((=) `wan_w120:(real^N->bool)->(real^N->real^K)->bool`)) (concl th))) THEN
    REWRITE_TAC[wan_w120] THEN
    DISCH_THEN(X_CHOOSE_THEN `f:num->real^N->real^K` STRIP_ASSUME_TAC o CONJUNCT2) THEN
    SUBGOAL_THEN `&0 < inv(&m + &1)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_INV THEN REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC
     `((\n. lnorm s (&2) (\x. (f:num->real^N->real^K) n x - (w:num->real^N->real^K) m x)) ---> &0) sequentially` THEN
    UNDISCH_TAC
     `((\n. wan_dir s (\x. (f:num->real^N->real^K) n x - (w:num->real^N->real^K) m x)) ---> &0) sequentially` THEN
    REWRITE_TAC[REALLIM_SEQUENTIALLY; REAL_SUB_RZERO] THEN
    DISCH_THEN(MP_TAC o SPEC `inv(&m + &1)`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_TAC `N1:num`) THEN
    DISCH_THEN(MP_TAC o SPEC `inv(&m + &1)`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_TAC `N2:num`) THEN
    EXISTS_TAC `(f:num->real^N->real^K) (MAX N1 N2)` THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THEN MATCH_MP_TAC(REAL_ARITH `abs x < e ==> x < e`) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC;
    REWRITE_TAC[SKOLEM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `psi:num->real^N->real^K` STRIP_ASSUME_TAC)] THEN
  ASM_REWRITE_TAC[wan_w120] THEN EXISTS_TAC `psi:num->real^N->real^K` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!n. wan_w12 s ((w:num->real^N->real^K) n)` ASSUME_TAC THENL
   [ASM_MESON_TAC[wan_w120]; ALL_TAC] THEN
  SUBGOAL_THEN `!n. wan_w12 s ((psi:num->real^N->real^K) n)` ASSUME_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`s:real^N->bool`; `(psi:num->real^N->real^K) n`] WAN_VTEST_W12) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. (\x. (psi:num->real^N->real^K) n x - u x) =
        (\x. (psi n x - (w:num->real^N->real^K) n x) + (w n x - u x))`
  (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN REPEAT GEN_TAC THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. wan_w12 s (\x. (psi:num->real^N->real^K) n x - (w:num->real^N->real^K) n x) /\
        wan_w12 s (\x. w n x - (u:real^N->real^K) x)`
  ASSUME_TAC THENL
   [GEN_TAC THEN CONJ_TAC THEN MATCH_MP_TAC WAN_W12_SUB THEN ASM_REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
  CONJ_TAC THEN MATCH_MP_TAC REALLIM_NULL_COMPARISON THENL
   [EXISTS_TAC `\n. inv(&n + &1) +
                    lnorm s (&2) (\x. (w:num->real^N->real^K) n x - (u:real^N->real^K) x)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC ALWAYS_EVENTUALLY THEN X_GEN_TAC `n:num` THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC(REAL_ARITH `!a b c d. &0 <= a /\ a <= b + c /\ b < d ==> abs a <= d + c`) THEN
      EXISTS_TAC `lnorm s (&2) (\x. (psi:num->real^N->real^K) n x - (w:num->real^N->real^K) n x)` THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC LNORM_POS_LE THEN MATCH_MP_TAC LSPACE_ADD THEN
        ASM_SIMP_TAC[REAL_POS; WAN_W12_IMP_LSPACE];
        MP_TAC(ISPECL [`s:real^N->bool`; `&2`;
                       `\x. (psi:num->real^N->real^K) n x - (w:num->real^N->real^K) n x`;
                       `\x. (w:num->real^N->real^K) n x - (u:real^N->real^K) x`]
                      LNORM_TRIANGLE) THEN
        ASM_SIMP_TAC[WAN_W12_IMP_LSPACE; REAL_ARITH `&1 <= &2`]];
      SUBGOAL_THEN `&0 = &0 + &0` SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REALLIM_ADD THEN ASM_REWRITE_TAC[WAN_INV_N1_LIM]];
    EXISTS_TAC `\n. &2 * inv(&n + &1) +
                    &2 * wan_dir s (\x. (w:num->real^N->real^K) n x - (u:real^N->real^K) x)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC ALWAYS_EVENTUALLY THEN X_GEN_TAC `n:num` THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC(REAL_ARITH
       `!a b c d. &0 <= a /\ a <= &2 * b + &2 * c /\ b < d ==> abs a <= &2 * d + &2 * c`) THEN
      EXISTS_TAC `wan_dir s (\x. (psi:num->real^N->real^K) n x - (w:num->real^N->real^K) n x)` THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC WAN_DIR_POS THEN MATCH_MP_TAC WAN_W12_ADD THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC WAN_DIR_ADD_LE THEN ASM_REWRITE_TAC[]];
      SUBGOAL_THEN `&0 = &2 * &0 + &2 * &0` SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REALLIM_ADD THEN CONJ_TAC THEN MATCH_MP_TAC REALLIM_LMUL THEN
      ASM_REWRITE_TAC[WAN_INV_N1_LIM]]]);;

(* ------------------------------------------------------------------------- *)
(* The truncation maps T_e(y) = (1 - b_e(y)) y, Stampacchia's theorem, W^1,2 *)
(* maps with compact support are in W^1,2_0, and continuous W^1,2 maps that  *)
(* vanish on the sphere are in W^1,2_0 of the ball (W120_CONT).               *)
(* ------------------------------------------------------------------------- *)

(* A copy of WAN_LNORM2_SQ (pc_wan_pstep), which this unit does not load.   *)

let WAN_SOB_LNORM2_SQ = prove
 (`!(f:real^M->real^K) s.
     f IN lspace s (&2)
     ==> lnorm s (&2) f pow 2 = drop(integral s (\x. lift(norm(f x) pow 2)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM RPOW_POW] THEN
  MP_TAC(ISPECL [`s:real^M->bool`; `&2`; `f:real^M->real^K`] LNORM_RPOW) THEN
  ASM_REWRITE_TAC[RPOW_POW] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN SIMP_TAC[]);;

let WAN_LNORM2_NULL = prove
 (`!(f:num->real^M->real^K) s.
     (!n. f n IN lspace s (&2)) /\
     ((\n. drop(integral s (\x. lift(norm(f n x) pow 2)))) ---> &0) sequentially
     ==> ((\n. lnorm s (&2) (f n)) ---> &0) sequentially`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[REALLIM_SEQUENTIALLY; REAL_SUB_RZERO] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e pow 2` o GEN_REWRITE_RULE I [REALLIM_SEQUENTIALLY]) THEN
  ASM_SIMP_TAC[REAL_POW_LT; REAL_SUB_RZERO] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN DISCH_TAC THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= lnorm s (&2) ((f:num->real^M->real^K) n)` ASSUME_TAC THENL
   [MATCH_MP_TAC LNORM_POS_LE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ x < e ==> abs x < e`) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_POW_LT2_REV THEN EXISTS_TAC `2` THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE; WAN_SOB_LNORM2_SQ] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term ((=) `abs:real->real`)) (concl th))) THEN
  REAL_ARITH_TAC);;

let WAN_TRUNC_FACTS = prove
 (`?B. &0 <= B /\
       !e. &0 < e
           ==> continuously_differentiable 1 (:real^K)
                 (\y:real^K. (&1 - smooth_bump e (&2 * e) y) % y) /\
               (!y:real^K. onorm(frechet_derivative
                            (\y:real^K. (&1 - smooth_bump e (&2 * e) y) % y) (at y)) <= B) /\
               (!(y:real^K) h. frechet_derivative (\y:real^K. (&1 - smooth_bump e (&2 * e) y) % y)
                        (at y) h =
                      (&1 - smooth_bump e (&2 * e) y) % h -
                      drop(frechet_derivative (\z. lift(smooth_bump e (&2 * e) z)) (at y) h) % y) /\
               (!y:real^K. norm y <= e ==> (&1 - smooth_bump e (&2 * e) y) % y = vec 0) /\
               (!y:real^K. &2 * e <= norm y ==> (&1 - smooth_bump e (&2 * e) y) % y = y) /\
               (!y:real^K. norm((&1 - smooth_bump e (&2 * e) y) % y) <= norm y) /\
               (!(y:real^K) h. &2 * e < norm(y:real^K)
                      ==> frechet_derivative (\z. lift(smooth_bump e (&2 * e) z)) (at y) h =
                          vec 0)`,
  X_CHOOSE_THEN `B0:real` STRIP_ASSUME_TAC (INST_TYPE [`:K`,`:N`] WAN_POINT_CUTOFF_DBOUND) THEN
  EXISTS_TAC `&1 + &2 * B0` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`vec 0:real^K`; `e:real`] WAN_POINT_CUTOFF_FACTS) THEN
  ASM_REWRITE_TAC[VECTOR_SUB_RZERO] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`vec 0:real^K`; `e:real`] o check (fun th ->
    can (find_term ((=) `B0:real`)) (concl th) && is_forall(concl th))) THEN
  ASM_REWRITE_TAC[VECTOR_SUB_RZERO; ETA_AX] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!y h. ~(y IN cball(vec 0:real^K,&2 * e))
          ==> frechet_derivative (\z. lift(smooth_bump e (&2 * e) z)) (at y) h = vec 0`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`\z:real^K. lift(smooth_bump e (&2 * e) z)`; `cball(vec 0:real^K,&2 * e)`;
                   `y:real^K`] WAN_FRECHET_ZERO_OUTSIDE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[CLOSED_CBALL; IN_CBALL_0; REAL_NOT_LE] THEN
      REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM LIFT_NUM; LIFT_EQ] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on (:real^K) (\y:real^K. (&1 - smooth_bump e (&2 * e) y) % y)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`(:real^K)`; `\y:real^K. lift(&1 - smooth_bump e (&2 * e) y)`;
                   `\y:real^K. y`] SMOOTH_MAP_ON_MUL_DROP_OPEN) THEN
    REWRITE_TAC[LIFT_DROP; OPEN_UNIV; SMOOTH_MAP_ON_ID] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[LIFT_SUB] THEN MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN
    ASM_REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_CONST];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y h. frechet_derivative (\y:real^K. (&1 - smooth_bump e (&2 * e) y) % y) (at y) h =
          (&1 - smooth_bump e (&2 * e) y) % h -
          drop(frechet_derivative (\z. lift(smooth_bump e (&2 * e) z)) (at y) h) % y`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN
    SUBGOAL_THEN
     `((\y:real^K. (&1 - smooth_bump e (&2 * e) y) % y) has_derivative
       (\h. (&1 - smooth_bump e (&2 * e) y) % h +
            (--drop(frechet_derivative (\z. lift(smooth_bump e (&2 * e) z)) (at y) h)) % y))
      (at y)`
    MP_TAC THENL
     [MP_TAC(ISPECL [`\y:real^K. &1 - smooth_bump e (&2 * e) y`;
                     `\h. --drop(frechet_derivative (\z:real^K. lift(smooth_bump e (&2 * e) z))
                                   (at (y:real^K)) h)`;
                     `\y:real^K. y`; `\h:real^K. h`; `y:real^K`] HAS_DERIVATIVE_MUL_AT) THEN
      REWRITE_TAC[HAS_DERIVATIVE_ID] THEN DISCH_THEN MATCH_MP_TAC THEN
      SUBGOAL_THEN
       `(lift o (\y:real^K. &1 - smooth_bump e (&2 * e) y)) =
        (\y. lift(&1) - lift(smooth_bump e (&2 * e) y)) /\
        (lift o (\h. --drop(frechet_derivative (\z:real^K. lift(smooth_bump e (&2 * e) z))
                              (at (y:real^K)) h))) =
        (\h. vec 0 - frechet_derivative (\z. lift(smooth_bump e (&2 * e) z)) (at y) h)`
      (fun th -> REWRITE_TAC[th]) THENL
       [REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_SUB; LIFT_NEG; LIFT_DROP; VECTOR_SUB_LZERO];
        ALL_TAC] THEN
      MATCH_MP_TAC HAS_DERIVATIVE_SUB THEN REWRITE_TAC[HAS_DERIVATIVE_CONST; ETA_AX] THEN
      REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `(:real^K)` THEN
      ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV];
      DISCH_THEN(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
      REWRITE_TAC[] THEN VECTOR_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[SMOOTH_MAP_ON_OPEN_UNIV];
    X_GEN_TAC `y:real^K` THEN
    MP_TAC(ISPECL [`frechet_derivative (\y:real^K. (&1 - smooth_bump e (&2 * e) y) % y) (at y)`]
                  ONORM) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `(:real^K)` THEN
      ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV];
      DISCH_THEN(MATCH_MP_TAC o CONJUNCT2)] THEN
    X_GEN_TAC `h:real^K` THEN ASM_REWRITE_TAC[REAL_ADD_RDISTRIB; REAL_MUL_LID] THEN
    MATCH_MP_TAC(NORM_ARITH
     `norm(a:real^K) <= x /\ norm(b:real^K) <= y ==> norm(a - b) <= x + y`) THEN
    REWRITE_TAC[NORM_MUL] THEN CONJ_TAC THENL
     [GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `y:real^K` o check (fun th ->
        is_forall(concl th) && is_conj(snd(dest_forall(concl th))))) THEN REAL_ARITH_TAC;
      ASM_CASES_TAC `(y:real^K) IN cball(vec 0,&2 * e)` THENL
       [MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `(B0 / e * norm(h:real^K)) * norm(y:real^K)` THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[NORM_POS_LE];
          UNDISCH_TAC `(y:real^K) IN cball(vec 0,&2 * e)` THEN REWRITE_TAC[IN_CBALL_0] THEN
          DISCH_TAC THEN
          SUBGOAL_THEN `(B0 / e * norm(h:real^K)) * norm(y:real^K) <=
                        (B0 / e * norm h) * (&2 * e)` MP_TAC THENL
           [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
            MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[NORM_POS_LE] THEN
            MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
            ALL_TAC] THEN
          SUBGOAL_THEN `(B0 / e * norm(h:real^K)) * (&2 * e) = (&2 * B0) * norm h`
          SUBST1_TAC THENL
           [UNDISCH_TAC `&0 < e` THEN CONV_TAC REAL_FIELD; REAL_ARITH_TAC]];
        ASM_SIMP_TAC[DROP_VEC; REAL_ABS_0; REAL_MUL_LZERO] THEN
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[NORM_POS_LE] THEN
        ASM_REAL_ARITH_TAC]];
    X_GEN_TAC `y:real^K` THEN DISCH_TAC THEN
    SUBGOAL_THEN `smooth_bump e (&2 * e) (y:real^K) = &1` SUBST1_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[REAL_SUB_REFL; VECTOR_MUL_LZERO]];
    X_GEN_TAC `y:real^K` THEN DISCH_TAC THEN
    SUBGOAL_THEN `smooth_bump e (&2 * e) (y:real^K) = &0` SUBST1_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[REAL_SUB_RZERO; VECTOR_MUL_LID]];
    X_GEN_TAC `y:real^K` THEN REWRITE_TAC[NORM_MUL] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:real^K` o check (fun th ->
      is_forall(concl th) && is_conj(snd(dest_forall(concl th))))) THEN REAL_ARITH_TAC;
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[IN_CBALL_0; REAL_NOT_LE]]);;

let WAN_TRUNC_LIMITS = prove
 (`!(y:real^K) h.
     ((\n. (&1 - smooth_bump (inv(&n + &1)) (&2 * inv(&n + &1)) y) % y) --> y) sequentially /\
     ((\n. frechet_derivative
             (\y:real^K. (&1 - smooth_bump (inv(&n + &1)) (&2 * inv(&n + &1)) y) % y) (at y) h)
      --> (if y = vec 0 then vec 0 else h)) sequentially`,
  REPEAT GEN_TAC THEN
  X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC (INST_TYPE [`:K`,`:K`] WAN_TRUNC_FACTS) THEN
  SUBGOAL_THEN `!n. &0 < inv(&n + &1)` ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC REAL_LT_INV THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `y:real^K = vec 0` THEN ASM_REWRITE_TAC[] THENL
   [CONJ_TAC THEN MATCH_MP_TAC LIM_EVENTUALLY THEN MATCH_MP_TAC ALWAYS_EVENTUALLY THEN
    X_GEN_TAC `n:num` THEN REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `inv(&n + &1)` o check (is_forall o concl)) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_SIMP_TAC[NORM_0; REAL_LT_IMP_LE] THEN
    SUBGOAL_THEN `smooth_bump (inv(&n + &1)) (&2 * inv(&n + &1)) (vec 0:real^K) = &1`
    SUBST1_TAC THENL
     [MP_TAC(ISPECL [`vec 0:real^K`; `inv(&n + &1)`] WAN_POINT_CUTOFF_FACTS) THEN
      ASM_SIMP_TAC[VECTOR_SUB_RZERO; NORM_0; REAL_LT_IMP_LE];
      REWRITE_TAC[REAL_SUB_REFL; VECTOR_MUL_LZERO; VECTOR_MUL_RZERO; VECTOR_SUB_RZERO]];
    MP_TAC(ISPECL [`&1`; `vec 0:real^K`; `y:real^K`] WAN_CUTOFF_SEQ) THEN
    ASM_REWRITE_TAC[REAL_LT_01; REAL_MUL_LID; VECTOR_SUB_RZERO] THEN
    DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
    CONJ_TAC THEN MATCH_MP_TAC LIM_EVENTUALLY THEN REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
    EXISTS_TAC `N:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `n:num` o check (fun th ->
      can (find_term ((=) `N:num`)) (concl th))) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `inv(&n + &1)` o check (is_forall o concl)) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    SUBGOAL_THEN `smooth_bump (inv(&n + &1)) (&2 * inv(&n + &1)) (y:real^K) = &0`
    SUBST1_TAC THENL
     [MP_TAC(ISPECL [`vec 0:real^K`; `inv(&n + &1)`] WAN_POINT_CUTOFF_FACTS) THEN
      ASM_SIMP_TAC[VECTOR_SUB_RZERO; REAL_LT_IMP_LE];
      REWRITE_TAC[REAL_SUB_RZERO; VECTOR_MUL_LID; DROP_VEC; VECTOR_MUL_LZERO;
                  VECTOR_SUB_RZERO]]]);;

let WAN_STAMPACCHIA = prove
 (`!(s:real^N->bool) (u:real^N->real^K) i.
     open s /\ wan_w12 s u /\ 1 <= i /\ i <= dimindex(:N)
     ==> wan_wpd s i u (\x. if u x = vec 0 then vec 0 else wan_wd s i u x) /\
         negligible {x | x IN s /\ u x = vec 0 /\ ~(wan_wd s i u x = vec 0)}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC (INST_TYPE [`:K`,`:K`] WAN_TRUNC_FACTS) THEN
  ABBREV_TAC `tr = \n (y:real^K). (&1 - smooth_bump (inv(&n + &1)) (&2 * inv(&n + &1)) y) % y` THEN
  SUBGOAL_THEN `!n. &0 < inv(&n + &1)` ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC REAL_LT_INV THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. continuously_differentiable 1 (:real^K) ((tr:num->real^K->real^K) n) /\
        (!y. onorm(frechet_derivative (tr n) (at y)) <= B) /\
        (!y. norm(tr n y) <= norm y)`
  ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "tr" THEN REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `inv(&n + &1)` o check (is_forall o concl)) THEN
    ASM_SIMP_TAC[ETA_AX];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y:real^K. ((\n. (tr:num->real^K->real^K) n y) --> y) sequentially /\
               !h. ((\n. frechet_derivative (tr n) (at y) h) -->
                    (if y = vec 0 then vec 0 else h)) sequentially`
  ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "tr" THEN REWRITE_TAC[ETA_AX] THEN
    MESON_TAC[WAN_TRUNC_LIMITS];
    ALL_TAC] THEN
  SUBGOAL_THEN `wan_l2loc s (u:real^N->real^K) /\
                !j. 1 <= j /\ j <= dimindex(:N)
                    ==> wan_l2loc s (wan_wd s j u) /\ wan_wpd s j u (wan_wd s j u)`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[WAN_LSPACE2_IMP_L2LOC; WAN_W12_IMP_LSPACE; WAN_WD_WORKS]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. wan_wpd s i (\x. (tr:num->real^K->real^K) n ((u:real^N->real^K) x))
          (\x. frechet_derivative (tr n) (at (u x)) (wan_wd s i u x)) /\
        wan_lloc s (\x. tr n (u x)) /\
        wan_lloc s (\x. frechet_derivative (tr n) (at (u x)) (wan_wd s i u x))`
  ASSUME_TAC THENL
   [GEN_TAC THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`s:real^N->bool`; `u:real^N->real^K`; `\j. wan_wd s j (u:real^N->real^K)`;
                     `(tr:num->real^K->real^K) n`; `B:real`; `i:num`] WAN_CHAIN_WPD) THEN
      ASM_SIMP_TAC[ETA_AX];
      MATCH_MP_TAC WAN_CHAIN_LLOC THEN EXISTS_TAC `B:real` THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `wan_wpd s i (u:real^N->real^K) (\x. if u x = vec 0 then vec 0 else wan_wd s i u x)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `!n y h. norm(frechet_derivative ((tr:num->real^K->real^K) n) (at y) h) <= B * norm h`
    ASSUME_TAC THENL
     [GEN_TAC THEN
      MP_TAC(ISPECL [`(tr:num->real^K->real^K) n`; `B:real`] WAN_C1_BOUNDED_FACTS) THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[wan_wpd] THEN REPEAT CONJ_TAC THENL
     [ASM_SIMP_TAC[WAN_L2LOC_IMP_LLOC];
      REWRITE_TAC[wan_lloc] THEN X_GEN_TAC `k:real^N->bool` THEN STRIP_TAC THEN
      MATCH_MP_TAC MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_ABSOLUTELY_INTEGRABLE THEN
      EXISTS_TAC `\x. lift(norm(wan_wd s i (u:real^N->real^K) x))` THEN
      REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC MEASURABLE_ON_LIMIT THEN
        MAP_EVERY EXISTS_TAC
         [`\n x. frechet_derivative ((tr:num->real^K->real^K) n) (at ((u:real^N->real^K) x))
                   (wan_wd s i u x)`; `{}:real^N->bool`] THEN
        REWRITE_TAC[NEGLIGIBLE_EMPTY; DIFF_EMPTY] THEN CONJ_TAC THENL
         [X_GEN_TAC `n:num` THEN MATCH_MP_TAC INTEGRABLE_IMP_MEASURABLE THEN
          MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
          FIRST_ASSUM(MP_TAC o SPEC `n:num` o check (fun th ->
            is_forall(concl th) &&
            can (find_term ((=) `wan_lloc:(real^N->bool)->(real^N->real^K)->bool`)) (concl th))) THEN
          REWRITE_TAC[wan_lloc] THEN
          DISCH_THEN(MP_TAC o SPEC `k:real^N->bool` o CONJUNCT2 o CONJUNCT2) THEN
          ASM_REWRITE_TAC[];
          X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN ASM_REWRITE_TAC[]];
        MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
        MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_NORM THEN REWRITE_TAC[ETA_AX] THEN
        MP_TAC(ISPECL [`s:real^N->bool`; `wan_wd s i (u:real^N->real^K)`] WAN_L2LOC_IMP_LLOC) THEN
        ASM_SIMP_TAC[] THEN REWRITE_TAC[wan_lloc] THEN
        DISCH_THEN(MP_TAC o SPEC `k:real^N->bool`) THEN ASM_REWRITE_TAC[];
        X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN REWRITE_TAC[LIFT_DROP] THEN
        COND_CASES_TAC THEN REWRITE_TAC[NORM_0; NORM_POS_LE; REAL_LE_REFL]];
      X_GEN_TAC `phi:real^N->real` THEN DISCH_TAC THEN
      SUBGOAL_THEN
       `!n. integral s (\x. wan_dpart i phi x % (tr:num->real^K->real^K) n ((u:real^N->real^K) x)) =
            --(integral s (\x. phi x % frechet_derivative (tr n) (at (u x)) (wan_wd s i u x)))`
      ASSUME_TAC THENL
       [GEN_TAC THEN
        FIRST_ASSUM(MP_TAC o SPEC `n:num` o check (fun th ->
          is_forall(concl th) &&
          can (find_term ((=) `wan_lloc:(real^N->bool)->(real^N->real^K)->bool`)) (concl th))) THEN
        REWRITE_TAC[wan_wpd] THEN
        DISCH_THEN(MP_TAC o SPEC `phi:real^N->real` o CONJUNCT2 o CONJUNCT2 o CONJUNCT1) THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN
       `!n. (\x. wan_dpart i phi x % (tr:num->real^K->real^K) n ((u:real^N->real^K) x))
              integrable_on s /\
            (\x. phi x % frechet_derivative (tr n) (at (u x)) (wan_wd s i u x)) integrable_on s`
      ASSUME_TAC THENL
       [GEN_TAC THEN CONJ_TAC THEN MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THENL
         [MP_TAC(ISPECL [`s:real^N->bool`; `phi:real^N->real`;
                         `\x. (tr:num->real^K->real^K) n ((u:real^N->real^K) x)`]
                        WAN_TEST_PAIRING) THEN
          ASM_SIMP_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `i:num` o CONJUNCT2) THEN
          REWRITE_TAC[];
          MP_TAC(ISPECL [`s:real^N->bool`; `phi:real^N->real`;
                         `\x. frechet_derivative ((tr:num->real^K->real^K) n)
                                 (at ((u:real^N->real^K) x)) (wan_wd s i u x)`]
                        WAN_TEST_PAIRING) THEN
          ASM_SIMP_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN REWRITE_TAC[]];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`s:real^N->bool`; `phi:real^N->real`; `u:real^N->real^K`]
                    WAN_TEST_PAIRING) THEN
      MP_TAC(ISPECL [`s:real^N->bool`; `phi:real^N->real`; `wan_wd s i (u:real^N->real^K)`]
                    WAN_TEST_PAIRING) THEN
      ASM_SIMP_TAC[WAN_L2LOC_IMP_LLOC] THEN
      DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
      DISCH_THEN(ASSUME_TAC o SPEC `i:num` o CONJUNCT2) THEN
      MATCH_MP_TAC(ISPEC `sequentially` LIM_UNIQUE) THEN
      EXISTS_TAC `\n. integral s (\x. wan_dpart i phi x %
                                      (tr:num->real^K->real^K) n ((u:real^N->real^K) x))` THEN
      REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN CONJ_TAC THENL
       [MP_TAC(ISPECL
         [`\n x. wan_dpart i phi x % (tr:num->real^K->real^K) n ((u:real^N->real^K) x)`;
          `\x. wan_dpart i phi x % (u:real^N->real^K) x`;
          `\x. lift(norm(wan_dpart i phi x % (u:real^N->real^K) x))`; `s:real^N->bool`]
         DOMINATED_CONVERGENCE) THEN
        REWRITE_TAC[] THEN ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
        ASM_SIMP_TAC[] THEN REPEAT CONJ_TAC THENL
         [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
          MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_NORM THEN ASM_REWRITE_TAC[];
          REPEAT STRIP_TAC THEN REWRITE_TAC[LIFT_DROP; NORM_MUL] THEN
          MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_ABS_POS];
          REPEAT STRIP_TAC THEN MATCH_MP_TAC LIM_CMUL THEN ASM_REWRITE_TAC[]];
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LIM_NEG THEN
        MP_TAC(ISPECL
         [`\n x. phi x % frechet_derivative ((tr:num->real^K->real^K) n) (at ((u:real^N->real^K) x))
                           (wan_wd s i u x)`;
          `\x. phi x % (if (u:real^N->real^K) x = vec 0 then vec 0 else wan_wd s i u x)`;
          `\x. lift(B * norm(phi x % wan_wd s i (u:real^N->real^K) x))`; `s:real^N->bool`]
         DOMINATED_CONVERGENCE) THEN
        REWRITE_TAC[] THEN ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
        ASM_SIMP_TAC[] THEN REPEAT CONJ_TAC THENL
         [REWRITE_TAC[LIFT_CMUL] THEN MATCH_MP_TAC INTEGRABLE_CMUL THEN
          MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
          MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_NORM THEN ASM_REWRITE_TAC[];
          REPEAT STRIP_TAC THEN REWRITE_TAC[LIFT_DROP; NORM_MUL] THEN
          ONCE_REWRITE_TAC[REAL_ARITH `B * a * b = a * B * b`] THEN
          MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_ABS_POS];
          REPEAT STRIP_TAC THEN MATCH_MP_TAC LIM_CMUL THEN ASM_REWRITE_TAC[]]]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `i:num`; `u:real^N->real^K`;
                 `\x. if (u:real^N->real^K) x = vec 0 then vec 0 else wan_wd s i u x`]
                WAN_WD_UNIQUE) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(MESON[NEGLIGIBLE_SUBSET]
   `!s t:real^N->bool. t SUBSET s ==> negligible s ==> negligible t`) THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `x:real^N` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[]);;

let WAN_W12_COMPACT_SUPPORT_W120 = prove
 (`!(s:real^N->bool) (v:real^N->real^K) c.
     open s /\ wan_w12 s v /\ compact c /\ c SUBSET s /\
     (!x. x IN s /\ ~(x IN c) ==> v x = vec 0)
     ==> wan_w120 s v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `c:real^N->bool`] WAN_COMPACT_NBHD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `d1:real` MP_TAC) THEN
  ABBREV_TAC `c1 = {x + y:real^N | x IN c /\ y IN cball(vec 0,d1)}` THEN
  ABBREV_TAC `uu = {x + y:real^N | x IN c /\ y IN ball(vec 0,d1)}` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `c1:real^N->bool`] WAN_SMOOTH_URYSOHN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `psi:real^N->real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!i x. x IN uu ==> wan_dpart i (psi:real^N->real) x = &0` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[wan_dpart] THEN
    MP_TAC(ISPECL [`\y. lift((psi:real^N->real) y)`; `\y:real^N. lift(&1)`;
                   `uu:real^N->bool`; `x:real^N`] LRG_FRECHET_DERIVATIVE_EQ_OPEN) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
      AP_TERM_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[FRECHET_DERIVATIVE_CONST_AT; DROP_VEC]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `wan_l2loc s (v:real^N->real^K) /\
    !i. 1 <= i /\ i <= dimindex(:N)
        ==> wan_l2loc s (wan_wd s i v) /\ wan_wpd s i v (wan_wd s i v)`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[WAN_LSPACE2_IMP_L2LOC; WAN_W12_IMP_LSPACE; WAN_WD_WORKS]; ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `v:real^N->real^K`; `\i. wan_wd s i (v:real^N->real^K)`;
                 `psi:real^N->real`] WAN_CUTOFF_EXTENSION) THEN
  ASM_SIMP_TAC[ETA_AX] THEN
  DISCH_THEN(X_CHOOSE_THEN `kp:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `?w0 (G:num->real^N->real^K).
      w0 IN lspace (:real^N) (&2) /\ (!x. ~(x IN kp) ==> w0 x = vec 0) /\
      (!x. x IN s ==> w0 x = (v:real^N->real^K) x) /\
      !i. 1 <= i /\ i <= dimindex(:N)
          ==> G i IN lspace (:real^N) (&2) /\ (!x. ~(x IN kp) ==> G i x = vec 0) /\
              wan_wpd (:real^N) i w0 (G i) /\
              negligible {x | x IN s /\ ~(G i x = wan_wd s i v x)}`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXISTS_TAC
     [`\x. if x IN s then (psi:real^N->real) x % (v:real^N->real^K) x else vec 0`;
      `\i x. if x IN s then wan_dpart i (psi:real^N->real) x % (v:real^N->real^K) x +
                            psi x % wan_wd s i v x else vec 0`] THEN
    ASM_SIMP_TAC[ETA_AX] THEN CONJ_TAC THENL
     [X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
      ASM_CASES_TAC `(x:real^N) IN c` THENL
       [SUBGOAL_THEN `(psi:real^N->real) x = &1` (fun th -> REWRITE_TAC[th; VECTOR_MUL_LID]) THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
        ASM_SIMP_TAC[VECTOR_MUL_RZERO]];
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`s:real^N->bool`; `v:real^N->real^K`; `i:num`] WAN_STAMPACCHIA) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT2) THEN
      MATCH_MP_TAC(MESON[NEGLIGIBLE_SUBSET]
       `!s t:real^N->bool. t SUBSET s ==> negligible s ==> negligible t`) THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `x:real^N` THEN
      ASM_CASES_TAC `(x:real^N) IN uu` THENL
       [SUBGOAL_THEN `(psi:real^N->real) x = &1` ASSUME_TAC THENL
         [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]; ALL_TAC] THEN
        STRIP_TAC THEN
        UNDISCH_TAC `~((if x IN s then wan_dpart i psi x % (v:real^N->real^K) x +
                          psi x % wan_wd s i v x else vec 0) = wan_wd s i v x)` THEN
        ASM_SIMP_TAC[VECTOR_MUL_LZERO; VECTOR_MUL_LID; VECTOR_ADD_LID];
        SUBGOAL_THEN `~((x:real^N) IN c)` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
        STRIP_TAC THEN ASM_SIMP_TAC[] THEN
        UNDISCH_TAC `~((if x IN s then wan_dpart i psi x % (v:real^N->real^K) x +
                          psi x % wan_wd s i v x else vec 0) = wan_wd s i v x)` THEN
        ASM_SIMP_TAC[VECTOR_MUL_RZERO; VECTOR_ADD_LID] THEN
        MESON_TAC[VECTOR_MUL_RZERO]]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `kp:real^N->bool`] WAN_COMPACT_NBHD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `d2:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!n. &0 < d2 / (&n + &2) /\ d2 / (&n + &2) < d2` ASSUME_TAC THENL
   [GEN_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_ARITH `&0 < &n + &2`] THEN
      SUBGOAL_THEN `&0 <= d2 * &n` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_POS]; ALL_TAC] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `wan_lloc (:real^N) (w0:real^N->real^K)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[WAN_L2_LLOC]; ALL_TAC] THEN
  SUBGOAL_THEN `!n. wan_vtest s (wan_moll (d2 / (&n + &2)) (w0:real^N->real^K))`
  ASSUME_TAC THENL
   [X_GEN_TAC `n:num` THEN REWRITE_TAC[wan_vtest] THEN CONJ_TAC THENL
     [MATCH_MP_TAC WAN_MOLL_SMOOTH THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    EXISTS_TAC `{x + y:real^N | x IN kp /\ y IN cball(vec 0,d2)}` THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`d2 / (&n + &2)`; `w0:real^N->real^K`; `kp:real^N->bool`]
                  WAN_MOLL_SUPPORT) THEN
    ASM_SIMP_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    UNDISCH_TAC `~((x:real^N) IN {x + y | x IN kp /\ y IN cball(vec 0,d2)})` THEN
    REWRITE_TAC[IN_ELIM_THM; CONTRAPOS_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `p:real^N` (X_CHOOSE_THEN `q:real^N` STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`p:real^N`; `q:real^N`] THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(q:real^N) IN ball(vec 0,d2 / (&n + &2))` THEN
    REWRITE_TAC[IN_BALL_0; IN_CBALL_0] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `n:num` o check (is_forall o concl)) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `lebesgue_measurable(s:real^N->bool)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[LEBESGUE_MEASURABLE_OPEN]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. wan_w12 s (\x. wan_moll (d2 / (&n + &2)) (w0:real^N->real^K) x - v x) /\
        !i. 1 <= i /\ i <= dimindex(:N)
            ==> wan_wpd s i (\x. wan_moll (d2 / (&n + &2)) w0 x - v x)
                  (\x. wan_moll (d2 / (&n + &2)) ((G:num->real^N->real^K) i) x -
                        wan_wd s i v x)`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`s:real^N->bool`; `wan_moll (d2 / (&n + &2)) (w0:real^N->real^K)`]
                  WAN_VTEST_W12) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC WAN_W12_SUB THEN ASM_REWRITE_TAC[ETA_AX];
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      SUBGOAL_THEN
       `!x. wan_moll (d2 / (&n + &2)) ((G:num->real^N->real^K) i) x =
            partial_derivative i (wan_moll (d2 / (&n + &2)) (w0:real^N->real^K)) x`
      (fun th -> REWRITE_TAC[th]) THENL
       [GEN_TAC THEN CONV_TAC SYM_CONV THEN
        MATCH_MP_TAC WAN_MOLL_WPD THEN ASM_SIMP_TAC[];
        MP_TAC(ISPECL [`s:real^N->bool`; `i:num`;
                       `wan_moll (d2 / (&n + &2)) (w0:real^N->real^K)`;
                       `\x. partial_derivative i (wan_moll (d2 / (&n + &2)) (w0:real^N->real^K)) x`;
                       `v:real^N->real^K`; `wan_wd s i (v:real^N->real^K)`] WAN_WPD_SUB) THEN
        ASM_SIMP_TAC[WAN_WD_WORKS]]];
    ALL_TAC] THEN
  REWRITE_TAC[wan_w120] THEN ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `\n. wan_moll (d2 / (&n + &2)) (w0:real^N->real^K)` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`\n x. wan_moll (d2 / (&n + &2)) (w0:real^N->real^K) x - v x`;
                   `s:real^N->bool`] WAN_LNORM2_NULL) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
     [GEN_TAC THEN MATCH_MP_TAC WAN_W12_IMP_LSPACE THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC WAN_MOLL_SEQ_L2_LMEAS THEN EXISTS_TAC `kp:real^N->bool` THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. wan_dir s (\x. wan_moll (d2 / (&n + &2)) (w0:real^N->real^K) x - v x) =
        sum(1..dimindex(:N))
          (\i. drop(integral s
                  (\x. lift(norm(wan_moll (d2 / (&n + &2)) ((G:num->real^N->real^K) i) x -
                                  G i x) pow 2))))`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`s:real^N->bool`;
                   `\x. wan_moll (d2 / (&n + &2)) (w0:real^N->real^K) x - v x`;
                   `\i x. wan_moll (d2 / (&n + &2)) ((G:num->real^N->real^K) i) x -
                          wan_wd s i (v:real^N->real^K) x`] WAN_DIR_EQ) THEN
    ASM_SIMP_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN AP_TERM_TAC THEN MATCH_MP_TAC INTEGRAL_SPIKE THEN
    EXISTS_TAC `{x | x IN s /\ ~((G:num->real^N->real^K) i x = wan_wd s i v x)}` THEN
    ASM_SIMP_TAC[] THEN REWRITE_TAC[IN_DIFF; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 = sum(1..dimindex(:N)) (\i. &0)` SUBST1_TAC THENL
   [REWRITE_TAC[SUM_0]; ALL_TAC] THEN
  MATCH_MP_TAC REALLIM_SUM THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  MATCH_MP_TAC WAN_MOLL_SEQ_L2_LMEAS THEN EXISTS_TAC `kp:real^N->bool` THEN
  ASM_SIMP_TAC[]);;

let WAN_W120_CONT = prove
 (`!(n:N->bool) (kk:K->bool). WAN_W120_CONT_STATEMENT n kk`,
  REWRITE_TAC[WAN_W120_CONT_STATEMENT] THEN
  MAP_EVERY X_GEN_TAC [`a:real^N`; `r:real`; `w:real^N->real^K`] THEN STRIP_TAC THEN
  X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC (INST_TYPE [`:K`,`:K`] WAN_TRUNC_FACTS) THEN
  ABBREV_TAC `tr = \n (y:real^K). (&1 - smooth_bump (inv(&n + &1)) (&2 * inv(&n + &1)) y) % y` THEN
  SUBGOAL_THEN `!n. &0 < inv(&n + &1)` ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC REAL_LT_INV THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. continuously_differentiable 1 (:real^K) ((tr:num->real^K->real^K) n) /\
        (!y. onorm(frechet_derivative (tr n) (at y)) <= B) /\
        (!y. norm(tr n y) <= norm y) /\
        (!y. norm y <= inv(&n + &1) ==> tr n y = vec 0)`
  ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "tr" THEN REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `inv(&n + &1)` o check (is_forall o concl)) THEN
    ASM_SIMP_TAC[ETA_AX];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y:real^K. ((\n. (tr:num->real^K->real^K) n y) --> y) sequentially /\
               !h. ((\n. frechet_derivative (tr n) (at y) h) -->
                    (if y = vec 0 then vec 0 else h)) sequentially`
  ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "tr" THEN REWRITE_TAC[ETA_AX] THEN
    MESON_TAC[WAN_TRUNC_LIMITS];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n y h. norm(frechet_derivative ((tr:num->real^K->real^K) n) (at y) h) <= B * norm h`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`(tr:num->real^K->real^K) n`; `B:real`] WAN_C1_BOUNDED_FACTS) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `open(ball(a:real^N,r)) /\ bounded(ball(a:real^N,r))` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[OPEN_BALL; BOUNDED_BALL]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. wan_w12 (ball(a,r)) (\x. (tr:num->real^K->real^K) n ((w:real^N->real^K) x)) /\
        !i. 1 <= i /\ i <= dimindex(:N)
            ==> wan_wpd (ball(a,r)) i (\x. tr n (w x))
                  (\x. frechet_derivative (tr n) (at (w x)) (wan_wd (ball(a,r)) i w x))`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`(:N)`; `(:K)`; `(:K)`] WAN_CHAIN_W12) THEN
    REWRITE_TAC[WAN_CHAIN_W12_STATEMENT] THEN
    DISCH_THEN(MP_TAC o SPECL [`ball(a:real^N,r)`; `w:real^N->real^K`;
                               `(tr:num->real^K->real^K) n`]) THEN
    ASM_SIMP_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN EXISTS_TAC `B:real` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n i. 1 <= i /\ i <= dimindex(:N)
          ==> (\x. frechet_derivative ((tr:num->real^K->real^K) n) (at ((w:real^N->real^K) x))
                     (wan_wd (ball(a,r)) i w x)) IN lspace (ball(a,r)) (&2)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`(tr:num->real^K->real^K) n`; `B:real`] WAN_C1_BOUNDED_FACTS) THEN
    ASM_SIMP_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`ball(a:real^N,r)`; `&2`;
                   `\x. frechet_derivative ((tr:num->real^K->real^K) n) (at ((w:real^N->real^K) x))
                          (wan_wd (ball(a,r)) i w x)`;
                   `\x. B % wan_wd (ball(a,r)) i (w:real^N->real^K) x`]
                  LSPACE_BOUNDED_MEASURABLE) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
     [REAL_ARITH_TAC;
      MATCH_MP_TAC WAN_DP_MEASURABLE THEN ASM_SIMP_TAC[LEBESGUE_MEASURABLE_OPEN] THEN
      CONJ_TAC THEN MATCH_MP_TAC WAN_LSPACE_MEASURABLE THEN EXISTS_TAC `&2` THEN
      ASM_SIMP_TAC[WAN_W12_IMP_LSPACE; WAN_WD_WORKS; ETA_AX];
      MATCH_MP_TAC LSPACE_CMUL THEN ASM_SIMP_TAC[WAN_WD_WORKS; ETA_AX];
      X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN REWRITE_TAC[NORM_MUL] THEN
      ASM_SIMP_TAC[REAL_ARITH `&0 <= B ==> abs B = B`]];
    ALL_TAC] THEN
  MATCH_MP_TAC WAN_W120_LIMIT THEN
  EXISTS_TAC `\n x. (tr:num->real^K->real^K) n ((w:real^N->real^K) x)` THEN
  ASM_REWRITE_TAC[OPEN_BALL] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `n:num` THEN MATCH_MP_TAC WAN_W12_COMPACT_SUPPORT_W120 THEN
    EXISTS_TAC `{x | x IN cball(a:real^N,r) /\ inv(&n + &1) <= norm((w:real^N->real^K) x)}` THEN
    ASM_SIMP_TAC[OPEN_BALL] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC BOUNDED_CLOSED_IMP_COMPACT THEN CONJ_TAC THENL
       [MATCH_MP_TAC BOUNDED_SUBSET THEN EXISTS_TAC `cball(a:real^N,r)` THEN
        REWRITE_TAC[BOUNDED_CBALL] THEN SET_TAC[];
        MATCH_MP_TAC CLOSED_IN_CLOSED_TRANS THEN EXISTS_TAC `cball(a:real^N,r)` THEN
        REWRITE_TAC[CLOSED_CBALL] THEN
        MP_TAC(ISPECL [`\x. lift(norm((w:real^N->real^K) x))`; `cball(a:real^N,r)`;
                       `{y:real^1 | inv(&n + &1) <= drop y}`]
                      CONTINUOUS_CLOSED_IN_PREIMAGE) THEN
        REWRITE_TAC[IN_ELIM_THM; LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC CONTINUOUS_ON_LIFT_NORM_COMPOSE THEN ASM_REWRITE_TAC[];
          REWRITE_TAC[drop; GSYM real_ge; CLOSED_HALFSPACE_COMPONENT_GE]]];
      REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_BALL; IN_CBALL] THEN
      X_GEN_TAC `x:real^N` THEN STRIP_TAC THEN
      ASM_CASES_TAC `dist(a:real^N,x) = r` THENL
       [UNDISCH_TAC `inv(&n + &1) <= norm((w:real^N->real^K) x)` THEN
        SUBGOAL_THEN `(w:real^N->real^K) x = vec 0` SUBST1_TAC THENL
         [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_SPHERE]; ALL_TAC] THEN
        REWRITE_TAC[NORM_0] THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `n:num` o check (fun th ->
          can (find_term ((=) `inv(&n + &1)`)) (concl th) && is_forall(concl th) &&
          not (can (find_term ((=) `tr:num->real^K->real^K`)) (concl th)))) THEN
        REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC];
      X_GEN_TAC `x:real^N` THEN REWRITE_TAC[IN_ELIM_THM; IN_BALL; IN_CBALL; DE_MORGAN_THM] THEN
      STRIP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `n:num` o check (fun th ->
        can (find_term ((=) `tr:num->real^K->real^K`)) (concl th) && is_forall(concl th) &&
        can (find_term ((=) `onorm:(real^K->real^K)->real`)) (concl th))) THEN
      STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
    REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`\n x. (tr:num->real^K->real^K) n ((w:real^N->real^K) x) - w x`;
                   `\x:real^N. vec 0:real^K`; `\x. &2 % (w:real^N->real^K) x`;
                   `ball(a:real^N,r)`; `&2`; `{}:real^N->bool`]
                  LSPACE_DOMINATED_CONVERGENCE) THEN
    REWRITE_TAC[VECTOR_SUB_RZERO; NEGLIGIBLE_EMPTY; DIFF_EMPTY] THEN ANTS_TAC THENL
     [ALL_TAC; SIMP_TAC[]] THEN
    REPEAT CONJ_TAC THENL
     [REAL_ARITH_TAC;
      GEN_TAC THEN MATCH_MP_TAC LSPACE_SUB THEN REWRITE_TAC[REAL_POS] THEN
      CONJ_TAC THEN MATCH_MP_TAC WAN_W12_IMP_LSPACE THEN ASM_SIMP_TAC[ETA_AX];
      MATCH_MP_TAC LSPACE_CMUL THEN ASM_SIMP_TAC[WAN_W12_IMP_LSPACE; ETA_AX];
      REPEAT STRIP_TAC THEN REWRITE_TAC[NORM_MUL; REAL_ABS_NUM] THEN
      MATCH_MP_TAC(NORM_ARITH
       `norm(a:real^K) <= norm(b:real^K) ==> norm(a - b) <= &2 * norm b`) THEN
      ASM_REWRITE_TAC[];
      REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM LIM_NULL] THEN ASM_REWRITE_TAC[]];
    SUBGOAL_THEN
     `!n. wan_dir (ball(a,r)) (\x. (tr:num->real^K->real^K) n ((w:real^N->real^K) x) - w x) =
          sum(1..dimindex(:N))
            (\i. lnorm (ball(a,r)) (&2)
                   (\x. frechet_derivative (tr n) (at (w x)) (wan_wd (ball(a,r)) i w x) -
                        wan_wd (ball(a,r)) i w x) pow 2)`
    (fun th -> REWRITE_TAC[th]) THENL
     [GEN_TAC THEN
      MP_TAC(ISPECL [`ball(a:real^N,r)`;
                     `\x. (tr:num->real^K->real^K) n ((w:real^N->real^K) x) - w x`;
                     `\i x. frechet_derivative ((tr:num->real^K->real^K) n)
                              (at ((w:real^N->real^K) x)) (wan_wd (ball(a,r)) i w x) -
                            wan_wd (ball(a,r)) i w x`] WAN_DIR_EQ) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
         [MATCH_MP_TAC WAN_W12_SUB THEN ASM_SIMP_TAC[ETA_AX];
          REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN MATCH_MP_TAC WAN_WPD_SUB THEN
          ASM_SIMP_TAC[WAN_WD_WORKS; ETA_AX]];
        DISCH_THEN SUBST1_TAC] THEN
      MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC WAN_SOB_LNORM2_SQ THEN
      MATCH_MP_TAC LSPACE_SUB THEN REWRITE_TAC[REAL_POS] THEN CONJ_TAC THENL
       [ASM_SIMP_TAC[];
        ASM_SIMP_TAC[WAN_WD_WORKS; ETA_AX]];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 = sum(1..dimindex(:N)) (\i. &0 pow 2)` SUBST1_TAC THENL
     [REWRITE_TAC[REAL_POW_ZERO; ARITH_EQ; SUM_0]; ALL_TAC] THEN
    MATCH_MP_TAC REALLIM_SUM THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN MATCH_MP_TAC REALLIM_POW THEN
    MP_TAC(ISPECL [`ball(a:real^N,r)`; `w:real^N->real^K`; `i:num`] WAN_STAMPACCHIA) THEN
    ASM_REWRITE_TAC[OPEN_BALL] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT2) THEN
    MP_TAC(ISPECL
     [`\n x. frechet_derivative ((tr:num->real^K->real^K) n) (at ((w:real^N->real^K) x))
               (wan_wd (ball(a,r)) i w x) - wan_wd (ball(a,r)) i w x`;
      `\x:real^N. vec 0:real^K`;
      `\x. (B + &1) % wan_wd (ball(a,r)) i (w:real^N->real^K) x`;
      `ball(a:real^N,r)`; `&2`;
      `{x | x IN ball(a,r) /\ (w:real^N->real^K) x = vec 0 /\
            ~(wan_wd (ball(a,r)) i w x = vec 0)}`]
     LSPACE_DOMINATED_CONVERGENCE) THEN
    REWRITE_TAC[VECTOR_SUB_RZERO] THEN ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [REAL_ARITH_TAC;
      GEN_TAC THEN MATCH_MP_TAC LSPACE_SUB THEN ASM_SIMP_TAC[REAL_POS; WAN_WD_WORKS; ETA_AX];
      MATCH_MP_TAC LSPACE_CMUL THEN ASM_SIMP_TAC[WAN_WD_WORKS; ETA_AX];
      REPEAT STRIP_TAC THEN REWRITE_TAC[NORM_MUL] THEN
      ASM_SIMP_TAC[REAL_ARITH `&0 <= B ==> abs(B + &1) = B + &1`] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `norm(frechet_derivative ((tr:num->real^K->real^K) n) (at ((w:real^N->real^K) x))
                        (wan_wd (ball(a,r)) i w x)) + norm(wan_wd (ball(a,r)) i w x)` THEN
      CONJ_TAC THENL
       [CONV_TAC NORM_ARITH;
        MATCH_MP_TAC(REAL_ARITH `a <= B * b ==> a + b <= (B + &1) * b`) THEN
        ASM_REWRITE_TAC[]];
      X_GEN_TAC `x:real^N` THEN REWRITE_TAC[IN_DIFF; IN_ELIM_THM] THEN STRIP_TAC THEN
      SUBGOAL_THEN
       `vec 0:real^K =
        (if (w:real^N->real^K) x = vec 0 then vec 0 else wan_wd (ball(a,r)) i w x) -
        wan_wd (ball(a,r)) i w x`
      SUBST1_TAC THENL
       [COND_CASES_TAC THEN REWRITE_TAC[VECTOR_SUB_REFL; VECTOR_SUB_LZERO] THEN
        ASM_MESON_TAC[VECTOR_NEG_0];
        MATCH_MP_TAC LIM_SUB THEN ASM_REWRITE_TAC[LIM_CONST]]]]);;

(* ------------------------------------------------------------------------- *)
(* Restriction of weak partials to open subsets, zero extension of W^1,2_0   *)
(* maps, and gluing (GLUE_W12).                                               *)
(* ------------------------------------------------------------------------- *)

let WAN_WD_SQ_LE_DIR = prove
 (`!(s:real^N->bool) (w:real^N->real^K) i.
     wan_w12 s w /\ 1 <= i /\ i <= dimindex(:N)
     ==> drop(integral s (\x. lift(norm(wan_wd s i w x) pow 2))) <= wan_dir s w`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[wan_dir] THEN
  MP_TAC(ISPECL [`\j. drop(integral s (\x. lift(norm(wan_wd s j (w:real^N->real^K) x) pow 2)))`;
                 `1..dimindex(:N)`; `i:num`] SUM_DELETE) THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= c ==> c = s - a ==> a <= s`) THEN
  MATCH_MP_TAC SUM_POS_LE THEN REWRITE_TAC[IN_DELETE; IN_NUMSEG] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRAL_DROP_POS THEN
  REWRITE_TAC[LIFT_DROP; REAL_LE_POW_2] THEN
  MATCH_MP_TAC WAN_LSPACE2_SQNORM_INTEGRABLE THEN ASM_SIMP_TAC[WAN_WD_WORKS; ETA_AX]);;

let WAN_WD_RESTRICT = prove
 (`!(s:real^N->bool) t (u:real^N->real^K) i.
     open t /\ t SUBSET s /\ wan_w12 s u /\ 1 <= i /\ i <= dimindex(:N)
     ==> wan_w12 t u /\ negligible {x | x IN t /\ ~(wan_wd t i u x = wan_wd s i u x)}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `wan_w12 t (u:real^N->real^K)` ASSUME_TAC THENL
   [REWRITE_TAC[wan_w12] THEN CONJ_TAC THENL
     [MATCH_MP_TAC LSPACE_SUBSET THEN EXISTS_TAC `s:real^N->bool` THEN
      ASM_SIMP_TAC[LEBESGUE_MEASURABLE_OPEN; WAN_W12_IMP_LSPACE];
      X_GEN_TAC `j:num` THEN STRIP_TAC THEN
      EXISTS_TAC `wan_wd s j (u:real^N->real^K)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC LSPACE_SUBSET THEN EXISTS_TAC `s:real^N->bool` THEN
        ASM_SIMP_TAC[LEBESGUE_MEASURABLE_OPEN; WAN_WD_WORKS];
        MATCH_MP_TAC WAN_WPD_SUBSET THEN EXISTS_TAC `s:real^N->bool` THEN
        ASM_SIMP_TAC[WAN_WD_WORKS]]];
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC WAN_WD_UNIQUE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC WAN_WPD_SUBSET THEN EXISTS_TAC `s:real^N->bool` THEN
    ASM_SIMP_TAC[WAN_WD_WORKS; ETA_AX]]);;

let WAN_L2_UNIV_TO_L1_ON = prove
 (`!(H:num->real^N->real^K) H0 k.
     compact k /\ (!n. H n IN lspace (:real^N) (&2)) /\ H0 IN lspace (:real^N) (&2) /\
     ((\n. drop(integral (:real^N) (\x. lift(norm(H n x - H0 x) pow 2)))) ---> &0) sequentially
     ==> ((\n. drop(integral k (\x. lift(norm(H n x - H0 x))))) ---> &0) sequentially`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!n. (\x. (H:num->real^N->real^K) n x - H0 x) IN lspace (:real^N) (&2)`
  ASSUME_TAC THENL [GEN_TAC THEN MATCH_MP_TAC LSPACE_SUB THEN ASM_REWRITE_TAC[REAL_POS; ETA_AX];
                    ALL_TAC] THEN
  MATCH_MP_TAC WAN_L2_TO_L1_CONV THEN ASM_SIMP_TAC[MEASURABLE_COMPACT] THEN CONJ_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC LSPACE_SUBSET THEN EXISTS_TAC `(:real^N)` THEN
    ASM_SIMP_TAC[LEBESGUE_MEASURABLE_COMPACT; SUBSET_UNIV];
    ALL_TAC] THEN
  MATCH_MP_TAC REALLIM_NULL_COMPARISON THEN
  EXISTS_TAC `\n. drop(integral (:real^N)
                    (\x. lift(norm((H:num->real^N->real^K) n x - H0 x) pow 2)))` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC ALWAYS_EVENTUALLY THEN X_GEN_TAC `n:num` THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `(\x. lift(norm((H:num->real^N->real^K) n x - H0 x) pow 2)) integrable_on (:real^N)`
  ASSUME_TAC THENL [ASM_SIMP_TAC[WAN_LSPACE2_SQNORM_INTEGRABLE]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(\x. lift(norm((H:num->real^N->real^K) n x - H0 x) pow 2)) integrable_on k`
  ASSUME_TAC THENL
   [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
    EXISTS_TAC `(:real^N)` THEN ASM_SIMP_TAC[LEBESGUE_MEASURABLE_COMPACT; SUBSET_UNIV] THEN
    MATCH_MP_TAC WAN_NONNEG_ABS_INTEGRABLE THEN ASM_SIMP_TAC[REAL_LE_POW_2];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= a /\ a <= b ==> abs a <= b`) THEN CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRAL_DROP_POS THEN ASM_REWRITE_TAC[LIFT_DROP; REAL_LE_POW_2];
    MATCH_MP_TAC INTEGRAL_SUBSET_DROP_LE THEN
    ASM_REWRITE_TAC[SUBSET_UNIV; LIFT_DROP; REAL_LE_POW_2]]);;

let WAN_ZERO_EXT_WEIGHTED_LIMIT = prove
 (`!(b:real^N->bool) (c:real^N->real) (G:num->real^N->real^K) G0 k M.
     lebesgue_measurable b /\ compact k /\ (!x. ~(x IN k) ==> c x = &0) /\
     (!x. abs(c x) <= M) /\ (\x. lift(c x)) continuous_on (:real^N) /\
     (!n. G n IN lspace b (&2)) /\ G0 IN lspace b (&2) /\
     (!n x. ~(x IN b) ==> G n x = vec 0) /\
     ((\n. drop(integral b (\x. lift(norm(G n x - G0 x) pow 2)))) ---> &0) sequentially
     ==> ((\n. integral (:real^N) (\x. c x % G n x)) -->
          integral (:real^N) (\x. c x % (if x IN b then G0 x else vec 0))) sequentially`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!n. (G:num->real^N->real^K) n IN lspace (:real^N) (&2)` ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC WAN_SOB_LSPACE_ZERO_EXT THEN EXISTS_TAC `b:real^N->bool` THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < &2`];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\x. if x IN b then (G0:real^N->real^K) x else vec 0) IN lspace (:real^N) (&2)`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[WAN_LSPACE_RESTRICT_UNIV; REAL_ARITH `&0 < &2`]; ALL_TAC] THEN
  MATCH_MP_TAC WAN_WEIGHTED_L1_LIMIT THEN
  EXISTS_TAC `k:real^N->bool` THEN EXISTS_TAC `M:real` THEN
  ASM_REWRITE_TAC[LEBESGUE_MEASURABLE_UNIV; SUBSET_UNIV] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `n:num` THEN
    MP_TAC(ISPECL [`(:real^N)`; `(G:num->real^N->real^K) n`] WAN_LSPACE2_IMP_LLOC) THEN
    ASM_REWRITE_TAC[wan_lloc; SUBSET_UNIV] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`(:real^N)`; `\x. if x IN b then (G0:real^N->real^K) x else vec 0`]
                  WAN_LSPACE2_IMP_LLOC) THEN
    ASM_REWRITE_TAC[wan_lloc; SUBSET_UNIV] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC WAN_L2_UNIV_TO_L1_ON THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!n. drop(integral (:real^N)
          (\x. lift(norm((G:num->real^N->real^K) n x -
                         (if x IN b then G0 x else vec 0)) pow 2))) =
        drop(integral b (\x. lift(norm(G n x - G0 x) pow 2)))`
  (fun th -> ASM_REWRITE_TAC[th]) THEN
  X_GEN_TAC `n:num` THEN AP_TERM_TAC THEN
  SUBGOAL_THEN
   `(\x. lift(norm((G:num->real^N->real^K) n x -
                   (if x IN b then G0 x else vec 0)) pow 2)) =
    (\x. if x IN b then lift(norm(G n x - G0 x) pow 2) else vec 0)`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `x:real^N` THEN
    ASM_CASES_TAC `(x:real^N) IN b` THEN
    ASM_SIMP_TAC[VECTOR_SUB_RZERO; NORM_0; REAL_POW_ZERO; ARITH_EQ; LIFT_NUM];
    REWRITE_TAC[INTEGRAL_RESTRICT_UNIV]]);;

let WAN_WD_DIFF_SQ_LE_DIR = prove
 (`!(b:real^N->bool) (f:real^N->real^K) h i.
     open b /\ wan_vtest b f /\ wan_w12 b h /\ 1 <= i /\ i <= dimindex(:N)
     ==> drop(integral b (\x. lift(norm(partial_derivative i f x - wan_wd b i h x) pow 2)))
         <= wan_dir b (\x. f x - h x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`b:real^N->bool`; `f:real^N->real^K`] WAN_VTEST_W12) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `i:num`)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `wan_w12 b (\x. (f:real^N->real^K) x - h x)` ASSUME_TAC THENL
   [MATCH_MP_TAC WAN_W12_SUB THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `wan_wpd b i (\x. (f:real^N->real^K) x - h x)
                (\x. partial_derivative i f x - wan_wd b i h x)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC WAN_WPD_SUB THEN ASM_SIMP_TAC[WAN_WD_WORKS; ETA_AX];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`b:real^N->bool`; `i:num`; `\x. (f:real^N->real^K) x - h x`;
                 `\x. partial_derivative i (f:real^N->real^K) x - wan_wd b i h x`]
                WAN_WD_UNIQUE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `drop(integral b
     (\x. lift(norm(wan_wd b i (\x. (f:real^N->real^K) x - h x) x) pow 2)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_EQ_IMP_LE THEN AP_TERM_TAC THEN MATCH_MP_TAC INTEGRAL_SPIKE THEN
    EXISTS_TAC `{x | x IN b /\
                     ~(wan_wd b i (\x. (f:real^N->real^K) x - h x) x =
                       partial_derivative i f x - wan_wd b i h x)}` THEN
    ASM_REWRITE_TAC[IN_DIFF; IN_ELIM_THM] THEN MESON_TAC[];
    MATCH_MP_TAC WAN_WD_SQ_LE_DIR THEN ASM_REWRITE_TAC[]]);;

let WAN_W120_ZERO_EXT = prove
 (`!(b:real^N->bool) (h:real^N->real^K).
     open b /\ wan_w120 b h
     ==> (\x. if x IN b then h x else vec 0) IN lspace (:real^N) (&2) /\
         !i. 1 <= i /\ i <= dimindex(:N)
             ==> wan_wpd (:real^N) i (\x. if x IN b then h x else vec 0)
                   (\x. if x IN b then wan_wd b i h x else vec 0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [wan_w120]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `f:num->real^N->real^K` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `(h:real^N->real^K) IN lspace b (&2)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[WAN_W12_IMP_LSPACE]; ALL_TAC] THEN
  ASM_SIMP_TAC[WAN_LSPACE_RESTRICT_UNIV; REAL_ARITH `&0 < &2`] THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!n. wan_w12 b ((f:num->real^N->real^K) n) /\
        (f n) IN lspace b (&2) /\
        (\x. partial_derivative i (f n) x) IN lspace b (&2) /\
        (!x. ~(x IN b) ==> f n x = vec 0) /\
        (!x. ~(x IN b) ==> partial_derivative i (f n) x = vec 0) /\
        wan_vtest (:real^N) (f n)`
  ASSUME_TAC THENL
   [X_GEN_TAC `n:num` THEN
    MP_TAC(ISPECL [`b:real^N->bool`; `(f:num->real^N->real^K) n`] WAN_VTEST_W12) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_SIMP_TAC[WAN_W12_IMP_LSPACE] THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [wan_vtest] o SPEC `n:num`) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `kn:real^N->bool` STRIP_ASSUME_TAC)) THEN
    MP_TAC(ISPECL [`b:real^N->bool`; `(f:num->real^N->real^K) n`; `kn:real^N->bool`; `i:num`]
                  WAN_VTEST_PARTIAL) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC WAN_LSPACE2_CONT_SUPPORT THEN EXISTS_TAC `kn:real^N->bool` THEN
      ASM_REWRITE_TAC[];
      ASM SET_TAC[];
      ASM SET_TAC[];
      MATCH_MP_TAC WAN_VTEST_SUBSET THEN EXISTS_TAC `b:real^N->bool` THEN
      ASM_REWRITE_TAC[SUBSET_UNIV]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\x. wan_wd b i (h:real^N->real^K) x) IN lspace b (&2)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[WAN_WD_WORKS; ETA_AX]; ALL_TAC] THEN
  REWRITE_TAC[wan_wpd] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC WAN_LSPACE2_IMP_LLOC THEN
    ASM_SIMP_TAC[WAN_LSPACE_RESTRICT_UNIV; REAL_ARITH `&0 < &2`];
    MATCH_MP_TAC WAN_LSPACE2_IMP_LLOC THEN
    ASM_SIMP_TAC[WAN_LSPACE_RESTRICT_UNIV; REAL_ARITH `&0 < &2`];
    ALL_TAC] THEN
  X_GEN_TAC `phi:real^N->real` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`(:real^N)`; `phi:real^N->real`; `i:num`] WAN_TEST_BOUNDS) THEN
  ASM_REWRITE_TAC[SUBSET_UNIV] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`(:real^N)`; `phi:real^N->real`; `i:num`] WAN_TEST_CONTINUOUS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC(ISPEC `sequentially` LIM_UNIQUE) THEN
  EXISTS_TAC `\n. integral (:real^N) (\x. wan_dpart i phi x % (f:num->real^N->real^K) n x)` THEN
  REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN CONJ_TAC THENL
   [MATCH_MP_TAC WAN_ZERO_EXT_WEIGHTED_LIMIT THEN
    EXISTS_TAC `k:real^N->bool` THEN EXISTS_TAC `B:real` THEN
    ASM_SIMP_TAC[LEBESGUE_MEASURABLE_OPEN] THEN
    SUBGOAL_THEN
     `!n. drop(integral b (\x. lift(norm((f:num->real^N->real^K) n x - h x) pow 2))) =
          lnorm b (&2) (\x. f n x - h x) pow 2`
    (fun th -> REWRITE_TAC[th]) THENL
     [GEN_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC WAN_SOB_LNORM2_SQ THEN
      MATCH_MP_TAC LSPACE_SUB THEN ASM_REWRITE_TAC[REAL_POS; ETA_AX];
      MATCH_MP_TAC REALLIM_NULL_POW THEN ASM_REWRITE_TAC[ARITH_EQ]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. integral (:real^N) (\x. wan_dpart i phi x % (f:num->real^N->real^K) n x) =
        --(integral (:real^N) (\x. phi x % partial_derivative i (f n) x))`
  (fun th -> REWRITE_TAC[th]) THENL
   [X_GEN_TAC `n:num` THEN
    MP_TAC(ISPECL [`(:real^N)`; `(f:num->real^N->real^K) n`] WAN_VTEST_W12) THEN
    ASM_REWRITE_TAC[OPEN_UNIV] THEN
    DISCH_THEN(MP_TAC o SPEC `i:num` o CONJUNCT2) THEN ASM_REWRITE_TAC[wan_wpd] THEN
    DISCH_THEN(MP_TAC o SPEC `phi:real^N->real` o CONJUNCT2 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC LIM_NEG THEN
  MATCH_MP_TAC WAN_ZERO_EXT_WEIGHTED_LIMIT THEN
  EXISTS_TAC `k:real^N->bool` THEN EXISTS_TAC `B:real` THEN
  ASM_SIMP_TAC[LEBESGUE_MEASURABLE_OPEN] THEN
  MATCH_MP_TAC REALLIM_NULL_COMPARISON THEN
  EXISTS_TAC `\n. wan_dir b (\x. (f:num->real^N->real^K) n x - h x)` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC ALWAYS_EVENTUALLY THEN X_GEN_TAC `n:num` THEN
  REWRITE_TAC[] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= a /\ a <= b ==> abs a <= b`) THEN CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRAL_DROP_POS THEN REWRITE_TAC[LIFT_DROP; REAL_LE_POW_2] THEN
    MATCH_MP_TAC WAN_LSPACE2_SQNORM_INTEGRABLE THEN
    MATCH_MP_TAC LSPACE_SUB THEN ASM_REWRITE_TAC[REAL_POS; ETA_AX];
    MATCH_MP_TAC WAN_WD_DIFF_SQ_LE_DIR THEN ASM_REWRITE_TAC[]]);;

let WAN_INTEGRAL_BALL_SPLIT = prove
 (`!(s:real^N->bool) a r (f:real^N->real^K).
     open s /\ cball(a,r) SUBSET s /\ f absolutely_integrable_on s
     ==> integral s f = integral (ball(a,r)) f + integral (s DIFF cball(a,r)) f`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `ball(a:real^N,r) SUBSET s` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`a:real^N`; `r:real`] BALL_SUBSET_CBALL) THEN ASM SET_TAC[]; ALL_TAC] THEN
  TRANS_TAC EQ_TRANS
   `integral (ball(a:real^N,r) UNION (s DIFF cball(a,r))) (f:real^N->real^K)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRAL_SPIKE_SET THEN MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
    EXISTS_TAC `sphere(a:real^N,r)` THEN REWRITE_TAC[NEGLIGIBLE_SPHERE] THEN
    MP_TAC(ISPECL [`a:real^N`; `r:real`] CBALL_DIFF_BALL) THEN
    MP_TAC(ISPECL [`a:real^N`; `r:real`] BALL_SUBSET_CBALL) THEN ASM SET_TAC[];
    MATCH_MP_TAC INTEGRAL_UNION THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
      MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
      EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[LEBESGUE_MEASURABLE_BALL];
      MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
      MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
      EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[SUBSET_DIFF] THEN
      MATCH_MP_TAC LEBESGUE_MEASURABLE_OPEN THEN
      ASM_SIMP_TAC[OPEN_DIFF; CLOSED_CBALL];
      MATCH_MP_TAC(MESON[NEGLIGIBLE_EMPTY] `(t:real^N->bool) = {} ==> negligible t`) THEN
      MP_TAC(ISPECL [`a:real^N`; `r:real`] BALL_SUBSET_CBALL) THEN SET_TAC[]]]);;

let WAN_WD_ADD_RESTRICT = prove
 (`!(s:real^N->bool) t (u:real^N->real^K) v i.
     open t /\ t SUBSET s /\ wan_w12 s u /\ wan_w12 t v /\ wan_w12 t (\x. v x - u x) /\
     1 <= i /\ i <= dimindex(:N)
     ==> negligible {x | x IN t /\
                         ~(wan_wd t i v x = wan_wd s i u x + wan_wd t i (\x. v x - u x) x)}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC WAN_WD_UNIQUE THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`t:real^N->bool`; `i:num`; `u:real^N->real^K`;
                 `wan_wd s i (u:real^N->real^K)`;
                 `\x. (v:real^N->real^K) x - u x`;
                 `wan_wd t i (\x. (v:real^N->real^K) x - u x)`]
                WAN_WPD_ADD) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC WAN_WPD_SUBSET THEN EXISTS_TAC `s:real^N->bool` THEN
      ASM_SIMP_TAC[WAN_WD_WORKS];
      ASM_SIMP_TAC[WAN_WD_WORKS]];
    REWRITE_TAC[VECTOR_ARITH `u + (v - u):real^K = v`; ETA_AX]]);;

let WAN_GLUE_W12 = prove
 (`!(n:N->bool) (kk:K->bool). WAN_GLUE_W12_STATEMENT n kk`,
  REWRITE_TAC[WAN_GLUE_W12_STATEMENT] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `ball(a:real^N,r) SUBSET s` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`a:real^N`; `r:real`] BALL_SUBSET_CBALL) THEN ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `open(s DIFF cball(a:real^N,r))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[OPEN_DIFF; CLOSED_CBALL]; ALL_TAC] THEN
  SUBGOAL_THEN `wan_w12 (ball(a:real^N,r)) (\x. (v:real^N->real^K) x - u x)` ASSUME_TAC THENL
   [ASM_MESON_TAC[wan_w120]; ALL_TAC] THEN
  MP_TAC(ISPECL [`ball(a:real^N,r)`; `\x. (v:real^N->real^K) x - u x`] WAN_W120_ZERO_EXT) THEN
  ASM_REWRITE_TAC[OPEN_BALL] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= dimindex(:N)
        ==> (\x. if x IN ball(a,r)
                 then wan_wd (ball(a,r)) i (\x. (v:real^N->real^K) x - u x) x else vec 0)
              IN lspace s (&2) /\
            wan_wpd s i (\x. if x IN ball(a:real^N,r) then v x - u x else vec 0)
                        (\x. if x IN ball(a,r)
                             then wan_wd (ball(a,r)) i (\x. v x - u x) x else vec 0)`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN STRIP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC LSPACE_SUBSET THEN EXISTS_TAC `(:real^N)` THEN
      ASM_SIMP_TAC[LEBESGUE_MEASURABLE_OPEN; SUBSET_UNIV; WAN_LSPACE_RESTRICT_UNIV;
                   REAL_ARITH `&0 < &2`; WAN_WD_WORKS; ETA_AX];
      MATCH_MP_TAC WAN_WPD_SUBSET THEN EXISTS_TAC `(:real^N)` THEN
      ASM_SIMP_TAC[SUBSET_UNIV]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `wan_w12 s (\x. if x IN ball(a:real^N,r) then (v:real^N->real^K) x - u x else vec 0)`
  ASSUME_TAC THENL
   [REWRITE_TAC[wan_w12] THEN CONJ_TAC THENL
     [MATCH_MP_TAC LSPACE_SUBSET THEN EXISTS_TAC `(:real^N)` THEN
      ASM_SIMP_TAC[LEBESGUE_MEASURABLE_OPEN; SUBSET_UNIV];
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      EXISTS_TAC `\x. if x IN ball(a,r)
                      then wan_wd (ball(a,r)) i (\x. (v:real^N->real^K) x - u x) x
                      else vec 0` THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\x. if x IN ball(a:real^N,r) then (v:real^N->real^K) x else u x) =
    (\x. u x + (if x IN ball(a,r) then v x - u x else vec 0))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN COND_CASES_TAC THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `u:real^N->real^K`;
                 `\x. if x IN ball(a:real^N,r) then (v:real^N->real^K) x - u x else vec 0`]
                WAN_W12_ADD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`s:real^N->bool`;
                 `\x. (u:real^N->real^K) x +
                      (if x IN ball(a:real^N,r) then v x - u x else vec 0)`;
                 `\i x. wan_wd s i (u:real^N->real^K) x +
                        (if x IN ball(a:real^N,r)
                         then wan_wd (ball(a,r)) i (\x. (v:real^N->real^K) x - u x) x
                         else vec 0)`]
                WAN_DIR_EQ) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    MATCH_MP_TAC WAN_WPD_ADD THEN ASM_SIMP_TAC[WAN_WD_WORKS; ETA_AX];
    DISCH_THEN(SUBST1_TAC o REWRITE_RULE[])] THEN
  REWRITE_TAC[wan_dir; GSYM SUM_ADD_NUMSEG] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `(\x. lift(norm(wan_wd s i (u:real^N->real^K) x +
                   (if x IN ball(a:real^N,r)
                    then wan_wd (ball(a,r)) i (\x. (v:real^N->real^K) x - u x) x
                    else vec 0)) pow 2)) absolutely_integrable_on s`
  ASSUME_TAC THENL
   [MATCH_MP_TAC WAN_NONNEG_ABS_INTEGRABLE THEN REWRITE_TAC[REAL_LE_POW_2] THEN
    MATCH_MP_TAC WAN_LSPACE2_SQNORM_INTEGRABLE THEN MATCH_MP_TAC LSPACE_ADD THEN
    ASM_SIMP_TAC[WAN_WD_WORKS; ETA_AX; REAL_POS];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `a:real^N`; `r:real`;
                 `\x. lift(norm(wan_wd s i (u:real^N->real^K) x +
                   (if x IN ball(a:real^N,r)
                    then wan_wd (ball(a,r)) i (\x. (v:real^N->real^K) x - u x) x
                    else vec 0)) pow 2)`]
                WAN_INTEGRAL_BALL_SPLIT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[DROP_ADD] THEN
  BINOP_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC INTEGRAL_SPIKE THENL
   [EXISTS_TAC `{x | x IN ball(a:real^N,r) /\
                     ~(wan_wd (ball(a,r)) i (v:real^N->real^K) x =
                       wan_wd s i u x + wan_wd (ball(a,r)) i (\x. v x - u x) x)}` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC WAN_WD_ADD_RESTRICT THEN ASM_REWRITE_TAC[OPEN_BALL]; ALL_TAC] THEN
    REWRITE_TAC[IN_DIFF; IN_ELIM_THM] THEN X_GEN_TAC `x:real^N` THEN
    ASM_CASES_TAC `(x:real^N) IN ball(a,r)` THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN SUBST1_TAC THEN REFL_TAC;
    EXISTS_TAC `{x | x IN s DIFF cball(a:real^N,r) /\
                     ~(wan_wd (s DIFF cball(a,r)) i (u:real^N->real^K) x = wan_wd s i u x)}` THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`s:real^N->bool`; `s DIFF cball(a:real^N,r)`; `u:real^N->real^K`; `i:num`]
                    WAN_WD_RESTRICT) THEN
      ASM_REWRITE_TAC[SUBSET_DIFF] THEN MESON_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[IN_DIFF; IN_ELIM_THM] THEN X_GEN_TAC `x:real^N` THEN STRIP_TAC THEN
    SUBGOAL_THEN `~((x:real^N) IN ball(a,r))` (fun th -> REWRITE_TAC[th; VECTOR_ADD_RID]) THENL
     [MP_TAC(ISPECL [`a:real^N`; `r:real`] BALL_SUBSET_CBALL) THEN ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `wan_wd (s DIFF cball(a,r)) i (u:real^N->real^K) x = wan_wd s i u x`
    SUBST1_TAC THENL [ASM_MESON_TAC[]; REFL_TAC]]);;

