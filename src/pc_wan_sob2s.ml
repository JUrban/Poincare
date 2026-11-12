(* ========================================================================= *)
(* pc_wan_sob2s: W^(1,2) maps on the 2-sphere and the stereographic chart    *)
(* (WAN_S2_STEREO). The shell minus the positive x3-axis is parametrised by  *)
(* F(y,r) = r stereo2_n_inv(y) on the slab 1/2 < r < 2 (wan_nch, inverse     *)
(* wan_nchi); weak partials are transported by the chain rule                *)
(* (WAN_DIFFEO_WPD of pc_wan_sob2v) in both directions, sliced by Fubini in  *)
(* the 2 + 1 splitting of real^3, and compared by the conformality of        *)
(* stereo2_n_inv (Parseval for the orthogonal columns of DF,                 *)
(* |det DF| = (r lam)^2).  The x3-axis, a set of codimension two, is         *)
(* removable for L^2 weak partials (WAN_REMOVABLE_AXIS3, cutoffs b_e(x1,x2)  *)
(* with uniformly L^2-bounded derivatives).  Statement constant:             *)
(* WAN_S2_STEREO_STATEMENT of pc_wan_p4defs.                                 *)
(* ========================================================================= *)

needs "src/pc_wan_sob2v.ml";;
prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Fubini in the splitting real^3 = real^2 x real^1.                         *)
(* ------------------------------------------------------------------------- *)

let WAN_TWIZZLE3 = prove
 (`!p:real^(2,1)finite_sum.
     ((lambda i. p$i):real^3) = vector[fstcart p$1; fstcart p$2; drop(sndcart p)]`,
  GEN_TAC THEN
  SIMP_TAC[CART_EQ; DIMINDEX_3; FORALL_3; LAMBDA_BETA; VECTOR_3; ARITH] THEN
  SIMP_TAC[fstcart; sndcart; drop; LAMBDA_BETA; DIMINDEX_FINITE_SUM; DIMINDEX_2; DIMINDEX_1;
           ARITH]);;

let WAN_TWIZZLE3_IMAGE = prove
 (`IMAGE (\x:real^(2,1)finite_sum. (lambda i. x$i):real^3) (:real^(2,1)finite_sum) =
   (:real^3)`,
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_UNIV] THEN X_GEN_TAC `z:real^3` THEN
  EXISTS_TAC `(lambda i. (z:real^3)$i):real^(2,1)finite_sum` THEN
  SIMP_TAC[CART_EQ; LAMBDA_BETA; DIMINDEX_3; DIMINDEX_FINITE_SUM; DIMINDEX_2; DIMINDEX_1] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SIMP_TAC[LAMBDA_BETA; DIMINDEX_FINITE_SUM; DIMINDEX_2; DIMINDEX_1; ARITH]);;

let WAN_TWIZZLE3_EQ = prove
 (`!(f:real^3->real^K).
     (f absolutely_integrable_on (:real^3) <=>
      (\p:real^(2,1)finite_sum. f(vector[fstcart p$1; fstcart p$2; drop(sndcart p)]))
      absolutely_integrable_on (:real^(2,1)finite_sum)) /\
     integral (:real^3) f =
     integral (:real^(2,1)finite_sum)
       (\p. f(vector[fstcart p$1; fstcart p$2; drop(sndcart p)]))`,
  GEN_TAC THEN
  MP_TAC(ISPECL [`f:real^3->real^K`; `(:real^(2,1)finite_sum)`; `\n:num. n`]
                ABSOLUTELY_INTEGRABLE_TWIZZLE_EQ) THEN
  MP_TAC(ISPECL [`f:real^3->real^K`; `(:real^(2,1)finite_sum)`; `\n:num. n`]
                INTEGRAL_TWIZZLE_EQ) THEN
  REWRITE_TAC[PERMUTES_ID; DIMINDEX_FINITE_SUM; DIMINDEX_1; DIMINDEX_2; DIMINDEX_3] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[WAN_TWIZZLE3_IMAGE; WAN_TWIZZLE3] THEN
  SIMP_TAC[]);;

let WAN_FUBINI3 = prove
 (`!(f:real^3->real^K).
     f absolutely_integrable_on (:real^3)
     ==> negligible {y:real^2 | ~((\r. f(vector[y$1; y$2; drop r]))
                                  absolutely_integrable_on (:real^1))} /\
         ((\y. integral (:real^1) (\r. f(vector[y$1; y$2; drop r]))) has_integral
          integral (:real^3) f) (:real^2) /\
         negligible {r:real^1 | ~((\y. f(vector[y$1; y$2; drop r]))
                                  absolutely_integrable_on (:real^2))} /\
         ((\r. integral (:real^2) (\y. f(vector[y$1; y$2; drop r]))) has_integral
          integral (:real^3) f) (:real^1)`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPEC `f:real^3->real^K` WAN_TWIZZLE3_EQ) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (fun th -> FIRST_ASSUM(ASSUME_TAC o GEN_REWRITE_RULE I [th]))
    SUBST1_TAC) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP FUBINI_ABSOLUTELY_INTEGRABLE) THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP FUBINI_ABSOLUTELY_INTEGRABLE_ALT) THEN
  REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN SIMP_TAC[]);;

let WAN_VECTOR2_ETA = prove
 (`!y:real^2. vector[y$1; y$2] = y`,
  REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2]);;

let WAN_TWIZZLE3_LINEAR = prove
 (`linear (\x:real^(2,1)finite_sum. (lambda i. x$i):real^3) /\
   (!x y:real^(2,1)finite_sum. ((lambda i. x$i):real^3) = (lambda i. y$i) ==> x = y)`,
  CONJ_TAC THENL
   [REWRITE_TAC[linear] THEN
    SIMP_TAC[CART_EQ; LAMBDA_BETA; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; DIMINDEX_3;
             DIMINDEX_FINITE_SUM; DIMINDEX_2; DIMINDEX_1] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    SIMP_TAC[LAMBDA_BETA; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; DIMINDEX_FINITE_SUM;
             DIMINDEX_2; DIMINDEX_1; ARITH];
    REPEAT GEN_TAC THEN
    SIMP_TAC[CART_EQ; LAMBDA_BETA; DIMINDEX_3; DIMINDEX_FINITE_SUM; DIMINDEX_2;
             DIMINDEX_1] THEN
    CONV_TAC NUM_REDUCE_CONV THEN MESON_TAC[]]);;

let WAN_MEASURABLE3_EQ = prove
 (`!(f:real^3->real^K).
     f measurable_on (:real^3) <=>
     (\p:real^(2,1)finite_sum. f(vector[fstcart p$1; fstcart p$2; drop(sndcart p)]))
     measurable_on (:real^(2,1)finite_sum)`,
  GEN_TAC THEN
  MP_TAC(ISPECL [`(\x:real^(2,1)finite_sum. (lambda i. x$i):real^3)`; `f:real^3->real^K`;
                 `(:real^(2,1)finite_sum)`] MEASURABLE_ON_LINEAR_IMAGE_EQ_GEN) THEN
  REWRITE_TAC[WAN_TWIZZLE3_LINEAR; WAN_TWIZZLE3_IMAGE; DIMINDEX_FINITE_SUM; DIMINDEX_1;
              DIMINDEX_2; DIMINDEX_3] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[o_DEF; WAN_TWIZZLE3] THEN SIMP_TAC[]);;

let WAN_ABS_INT_SCALAR_VEC = prove
 (`!(g:real^M->real) (c:real^K) s.
     (\r. lift(g r)) absolutely_integrable_on s
     ==> (\r. g r % c) absolutely_integrable_on s /\
         integral s (\r. g r % c) = drop(integral s (\r. lift(g r))) % c`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `linear (\t:real^1. drop t % (c:real^K))` ASSUME_TAC THENL
   [REWRITE_TAC[linear; DROP_ADD; DROP_CMUL] THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`\r:real^M. lift(g r)`; `\t:real^1. drop t % (c:real^K)`; `s:real^M->bool`]
                ABSOLUTELY_INTEGRABLE_LINEAR) THEN
  MP_TAC(ISPECL [`\r:real^M. lift(g r)`; `s:real^M->bool`; `\t:real^1. drop t % (c:real^K)`]
                INTEGRAL_LINEAR) THEN
  ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE; o_DEF; LIFT_DROP]);;

let WAN_ABS_INT3_PROD = prove
 (`!(f:real^2->real^K) (g:real^1->real).
     f absolutely_integrable_on (:real^2) /\
     (\r. lift(g r)) absolutely_integrable_on (:real^1)
     ==> (\x:real^3. g(lift(x$3)) % f(vector[x$1; x$2])) absolutely_integrable_on (:real^3) /\
         integral (:real^3) (\x. g(lift(x$3)) % f(vector[x$1; x$2])) =
         drop(integral (:real^1) (\r. lift(g r))) % integral (:real^2) f`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `\x:real^3. g(lift(x$3)) % (f:real^2->real^K)(vector[x$1; x$2])`
               WAN_TWIZZLE3_EQ) THEN
  REWRITE_TAC[VECTOR_3; LIFT_DROP; WAN_VECTOR2_ETA] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  SUBGOAL_THEN
   `!x:real^2. (\r:real^1. g r % (f:real^2->real^K) x) absolutely_integrable_on (:real^1) /\
               integral (:real^1) (\r. g r % f x) = drop(integral (:real^1) (\r. lift(g r))) % f x`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC WAN_ABS_INT_SCALAR_VEC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(\p:real^(2,1)finite_sum. g(sndcart p) % (f:real^2->real^K)(fstcart p))
    absolutely_integrable_on (:real^(2,1)finite_sum)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `(\p:real^(2,1)finite_sum. g(sndcart p) % (f:real^2->real^K)(fstcart p))
      measurable_on (:real^(2,1)finite_sum)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC MEASURABLE_ON_MUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC(INST_TYPE [`:2`,`:M`; `:1`,`:N`] MEASURABLE_ON_COMPOSE_SNDCART) THEN
        MATCH_MP_TAC INTEGRABLE_IMP_MEASURABLE THEN
        ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE; ETA_AX];
        MATCH_MP_TAC(INST_TYPE [`:2`,`:M`; `:1`,`:N`] MEASURABLE_ON_COMPOSE_FSTCART) THEN
        MATCH_MP_TAC INTEGRABLE_IMP_MEASURABLE THEN
        ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE]];
      ALL_TAC] THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP FUBINI_TONELLI_ALT th]) THEN
    REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN
    SUBGOAL_THEN
     `!r:real^1. (\x:real^2. g r % (f:real^2->real^K) x) absolutely_integrable_on (:real^2)`
    ASSUME_TAC THENL
     [GEN_TAC THEN MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_CMUL THEN ASM_REWRITE_TAC[ETA_AX];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN EXISTS_TAC `{}:real^1->bool` THEN
      ASM_REWRITE_TAC[NEGLIGIBLE_EMPTY; SUBSET; IN_ELIM_THM; NOT_IN_EMPTY];
      ALL_TAC] THEN
    REWRITE_TAC[NORM_MUL; LIFT_CMUL] THEN
    SUBGOAL_THEN `(\x:real^2. lift(norm((f:real^2->real^K) x))) integrable_on (:real^2)` ASSUME_TAC THENL
     [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
      MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_NORM THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_SIMP_TAC[INTEGRAL_CMUL] THEN
    MP_TAC(ISPECL [`\r:real^1. abs(g r)`; `integral (:real^2) (\x. lift(norm((f:real^2->real^K) x)))`;
                   `(:real^1)`] WAN_ABS_INT_SCALAR_VEC) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[GSYM NORM_LIFT] THEN MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_NORM THEN
      ASM_REWRITE_TAC[];
      SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT2 o MATCH_MP FUBINI_ABSOLUTELY_INTEGRABLE) THEN
  REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o MATCH_MP INTEGRAL_UNIQUE) THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  ASM_SIMP_TAC[INTEGRAL_CMUL; ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE] THEN
  REWRITE_TAC[DROP_CMUL] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  ASM_SIMP_TAC[GSYM INTEGRAL_CMUL; ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE] THEN
  REWRITE_TAC[DROP_CMUL]);;

(* ------------------------------------------------------------------------- *)
(* Local integrability of maps independent of the third coordinate.         *)
(* ------------------------------------------------------------------------- *)

let WAN_NORM_PROJ3 = prove
 (`!x:real^3. norm(vector[x$1; x$2]:real^2) <= norm x /\ abs(x$3) <= norm x`,
  GEN_TAC THEN CONJ_TAC THENL
   [REWRITE_TAC[NORM_LE; DOT_2; DOT_3; VECTOR_2] THEN
    MP_TAC(SPEC `(x:real^3)$3` REAL_LE_SQUARE) THEN REAL_ARITH_TAC;
    MP_TAC(ISPECL [`x:real^3`; `3`] COMPONENT_LE_NORM) THEN
    REWRITE_TAC[DIMINDEX_3; ARITH]]);;

let WAN_INDICATOR_INTERVAL_ABS_INT = prove
 (`!a b:real^1. (\r. lift(if r IN interval[a,b] then &1 else &0)) absolutely_integrable_on
                (:real^1)`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `(\r:real^1. lift(if r IN interval[a,b] then &1 else &0)) =
                (\r. if r IN interval[a,b] then lift(&1) else vec 0)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[LIFT_NUM];
    ALL_TAC] THEN
  REWRITE_TAC[ABSOLUTELY_INTEGRABLE_RESTRICT_UNIV] THEN
  MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_CONTINUOUS THEN REWRITE_TAC[CONTINUOUS_ON_CONST]);;

let WAN_LLOC_PROJ3 = prove
 (`!(w:real^2->real^K). wan_lloc (:real^2) w ==> wan_lloc (:real^3) (\x. w(vector[x$1; x$2]))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[wan_lloc] THEN X_GEN_TAC `k:real^3->bool` THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
  REWRITE_TAC[BOUNDED_POS] THEN DISCH_THEN(X_CHOOSE_THEN `c:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(w:real^2->real^K) absolutely_integrable_on cball(vec 0,c)` ASSUME_TAC THENL
   [UNDISCH_TAC `wan_lloc (:real^2) (w:real^2->real^K)` THEN REWRITE_TAC[wan_lloc] THEN
    DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[COMPACT_CBALL; SUBSET_UNIV];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\y:real^2. if y IN cball(vec 0,c) then (w:real^2->real^K) y else vec 0`;
                 `\r:real^1. if r IN interval[lift(--c),lift c] then &1 else &0`]
                WAN_ABS_INT3_PROD) THEN
  ASM_REWRITE_TAC[ABSOLUTELY_INTEGRABLE_RESTRICT_UNIV; WAN_INDICATOR_INTERVAL_ABS_INT] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1) THEN DISCH_TAC THEN
  MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_EQ THEN
  EXISTS_TAC `\x:real^3. (if lift(x$3) IN interval[lift(--c),lift c] then &1 else &0) %
                         (if (vector[x$1; x$2]:real^2) IN cball(vec 0,c)
                          then (w:real^2->real^K)(vector[x$1; x$2]) else vec 0)` THEN
  CONJ_TAC THENL
   [X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `norm(x:real^3) <= c` ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    MP_TAC(SPEC `x:real^3` WAN_NORM_PROJ3) THEN STRIP_TAC THEN
    REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP; IN_CBALL_0] THEN
    SUBGOAL_THEN `--c <= (x:real^3)$3 /\ x$3 <= c /\ norm(vector[x$1; x$2]:real^2) <= c`
    (fun th -> REWRITE_TAC[th; VECTOR_MUL_LID]) THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
    EXISTS_TAC `(:real^3)` THEN ASM_SIMP_TAC[SUBSET_UNIV; LEBESGUE_MEASURABLE_COMPACT]]);;

(* ------------------------------------------------------------------------- *)
(* Test functions composed with affine maps; slices and products on slabs.  *)
(* ------------------------------------------------------------------------- *)

let WAN_SMOOTH_AFFINE = prove
 (`!(L:real^M->real^N) c. linear L ==> smooth_map_on (:real^M) (\x. L x + c)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN
  REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_CONST] THEN
  SUBGOAL_THEN `(L:real^M->real^N) = L o (\x. x)` (fun th -> ONCE_REWRITE_TAC[th]) THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_LINEAR_O THEN ASM_REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_ID]);;

let WAN_DPART_AFFINE = prove
 (`!(phi:real^N->real) (L:real^M->real^N) c i x.
     smooth_map_on (:real^N) (\y. lift(phi y)) /\ linear L
     ==> smooth_map_on (:real^M) (\x. lift(phi(L x + c))) /\
         wan_dpart i (\x. phi(L x + c)) x =
         drop(frechet_derivative (\y. lift(phi y)) (at (L x + c)) (L(basis i)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(\x. lift((phi:real^N->real)((L:real^M->real^N) x + c))) =
                (\y. lift(phi y)) o (\x. L x + c)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `(:real^N)` THEN
    ASM_SIMP_TAC[OPEN_UNIV; SUBSET_UNIV; WAN_SMOOTH_AFFINE];
    ALL_TAC] THEN
  REWRITE_TAC[wan_dpart] THEN
  SUBGOAL_THEN `(\x. lift((phi:real^N->real)((L:real^M->real^N) x + c))) =
                (\y. lift(phi y)) o (\x. L x + c)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(((\y. lift((phi:real^N->real) y)) o (\x. (L:real^M->real^N) x + c)) has_derivative
     (frechet_derivative (\y. lift(phi y)) (at (L x + c)) o L)) (at x)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC DIFF_CHAIN_AT THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`L:real^M->real^N`; `L:real^M->real^N`; `\x:real^M. c:real^N`;
                     `\h:real^M. vec 0:real^N`; `at (x:real^M)`] HAS_DERIVATIVE_ADD) THEN
      ASM_SIMP_TAC[HAS_DERIVATIVE_LINEAR; HAS_DERIVATIVE_CONST; VECTOR_ADD_RID; ETA_AX];
      REWRITE_TAC[] THEN
      MATCH_MP_TAC(REWRITE_RULE[RIGHT_IMP_FORALL_THM; IMP_IMP] SMOOTH_MAP_ON_HAS_DERIVATIVE) THEN
      EXISTS_TAC `(:real^N)` THEN ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
  REWRITE_TAC[o_THM]);;

let WAN_TEST_SLICE3 = prove
 (`!(s:real^3->bool) Phi r.
     wan_test s Phi
     ==> wan_test (:real^2) (\y:real^2. Phi(vector[y$1; y$2; r])) /\
         (!i (y:real^2). i = 1 \/ i = 2
                ==> wan_dpart i (\y:real^2. Phi(vector[y$1; y$2; r])) y =
                    wan_dpart i Phi (vector[y$1; y$2; r]))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wan_test] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `k:real^3->bool` STRIP_ASSUME_TAC)) THEN
  ABBREV_TAC `L = \y:real^2. vector[y$1; y$2; &0]:real^3` THEN
  SUBGOAL_THEN `linear (L:real^2->real^3)` ASSUME_TAC THENL
   [EXPAND_TAC "L" THEN REWRITE_TAC[linear] THEN
    SIMP_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3; VECTOR_ADD_COMPONENT;
             VECTOR_MUL_COMPONENT] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^2. vector[y$1; y$2; r]:real^3 = L y + vector[&0; &0; r]`
  (fun th -> REWRITE_TAC[th]) THENL
   [EXPAND_TAC "L" THEN
    SIMP_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3; VECTOR_ADD_COMPONENT] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`Phi:real^3->real`; `L:real^2->real^3`; `vector[&0; &0; r]:real^3`]
                WAN_DPART_AFFINE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN REPEAT CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`1`; `vec 0:real^2`]) THEN SIMP_TAC[];
    EXISTS_TAC `{y:real^2 | (L:real^2->real^3) y + vector[&0; &0; r] IN k}` THEN
    REWRITE_TAC[SUBSET_UNIV; IN_ELIM_THM] THEN CONJ_TAC THENL
     [REWRITE_TAC[COMPACT_EQ_BOUNDED_CLOSED] THEN CONJ_TAC THENL
       [FIRST_ASSUM(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
        REWRITE_TAC[BOUNDED_POS; IN_ELIM_THM] THEN
        DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
        EXISTS_TAC `B + abs r + &1` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        X_GEN_TAC `y:real^2` THEN DISCH_TAC THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `(L:real^2->real^3) y + vector[&0; &0; r]`) THEN
        ASM_REWRITE_TAC[] THEN
        SUBGOAL_THEN `norm(y:real^2) <= norm((L:real^2->real^3) y + vector[&0; &0; r]) + abs r`
        MP_TAC THENL
         [EXPAND_TAC "L" THEN
          SUBGOAL_THEN `vector[(y:real^2)$1; y$2; &0] + vector[&0; &0; r] = vector[y$1; y$2; r]:real^3`
          SUBST1_TAC THENL
           [SIMP_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3; VECTOR_ADD_COMPONENT] THEN
            REAL_ARITH_TAC;
            ALL_TAC] THEN
          MP_TAC(SPEC `vector[(y:real^2)$1; y$2; r]:real^3` WAN_NORM_PROJ3) THEN
          REWRITE_TAC[VECTOR_3; WAN_VECTOR2_ETA] THEN REAL_ARITH_TAC;
          REAL_ARITH_TAC];
        MATCH_MP_TAC CONTINUOUS_CLOSED_PREIMAGE_UNIV THEN
        ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN GEN_TAC THEN
        MATCH_MP_TAC CONTINUOUS_ADD THEN
        ASM_SIMP_TAC[LINEAR_CONTINUOUS_AT; CONTINUOUS_CONST]];
      ASM_SIMP_TAC[]];
    REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[wan_dpart] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN EXPAND_TAC "L" THEN
    SIMP_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3; BASIS_COMPONENT; DIMINDEX_2; ARITH] THEN
    ASM_REWRITE_TAC[ARITH]]);;

let WAN_DPART_MUL = prove
 (`!(f:real^N->real) g i x.
     smooth_map_on (:real^N) (\y. lift(f y)) /\ smooth_map_on (:real^N) (\y. lift(g y))
     ==> smooth_map_on (:real^N) (\y. lift(f y * g y)) /\
         wan_dpart i (\y. f y * g y) x = wan_dpart i f x * g x + f x * wan_dpart i g x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`(:real^N)`; `\y. lift((f:real^N->real) y)`; `\y. lift((g:real^N->real) y)`]
                  SMOOTH_MAP_ON_MUL_LIFT_OPEN) THEN
    ASM_REWRITE_TAC[OPEN_UNIV; LIFT_DROP];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!h:real^N->real. smooth_map_on (:real^N) (\y. lift(h y))
       ==> ((\y. lift(h y)) has_derivative frechet_derivative (\y. lift(h y)) (at x)) (at x)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MATCH_MP_TAC(REWRITE_RULE[RIGHT_IMP_FORALL_THM; IMP_IMP] SMOOTH_MAP_ON_HAS_DERIVATIVE) THEN
    EXISTS_TAC `(:real^N)` THEN ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`f:real^N->real`;
                 `\h. drop(frechet_derivative (\y. lift((f:real^N->real) y)) (at x) h)`;
                 `\y. lift((g:real^N->real) y)`;
                 `frechet_derivative (\y. lift((g:real^N->real) y)) (at x)`;
                 `x:real^N`] HAS_DERIVATIVE_MUL_AT) THEN
  REWRITE_TAC[o_DEF; LIFT_DROP; ETA_AX] THEN ASM_SIMP_TAC[] THEN
  REWRITE_TAC[GSYM LIFT_CMUL] THEN DISCH_TAC THEN
  REWRITE_TAC[wan_dpart] THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
  REWRITE_TAC[DROP_ADD; DROP_CMUL; LIFT_DROP] THEN REAL_ARITH_TAC);;

let WAN_NORM3_SPLIT = prove
 (`!x:real^3. norm x <= norm(vector[x$1; x$2]:real^2) + abs(x$3)`,
  GEN_TAC THEN
  SUBGOAL_THEN `x = vector[(x:real^3)$1; x$2; &0] + vector[&0; &0; x$3]:real^3`
  (fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THENL
   [SIMP_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3; VECTOR_ADD_COMPONENT] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `norm(vector[(x:real^3)$1; x$2; &0]:real^3) + norm(vector[&0; &0; x$3]:real^3)` THEN
  REWRITE_TAC[NORM_TRIANGLE] THEN MATCH_MP_TAC REAL_EQ_IMP_LE THEN BINOP_TAC THENL
   [REWRITE_TAC[vector_norm; DOT_3; DOT_2; VECTOR_2; VECTOR_3] THEN
    AP_TERM_TAC THEN REAL_ARITH_TAC;
    REWRITE_TAC[vector_norm; DOT_3; VECTOR_3] THEN
    REWRITE_TAC[REAL_MUL_LZERO; REAL_ADD_LID; GSYM REAL_POW_2; POW_2_SQRT_ABS]]);;

let WAN_PROJ3_LINEAR = prove
 (`linear (\x:real^3. vector[x$1; x$2]:real^2) /\ linear (\x:real^3. lift(x$3))`,
  REWRITE_TAC[linear] THEN
  SIMP_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2; VECTOR_ADD_COMPONENT;
           VECTOR_MUL_COMPONENT; LIFT_ADD; LIFT_CMUL]);;

let WAN_PROD3_SUPPORT_COMPACT = prove
 (`!(k1:real^2->bool) (k2:real^1->bool).
     compact k1 /\ compact k2
     ==> compact {x:real^3 | (vector[x$1; x$2]:real^2) IN k1 /\ lift(x$3) IN k2}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[COMPACT_EQ_BOUNDED_CLOSED] THEN CONJ_TAC THENL
   [MP_TAC(ISPEC `k1:real^2->bool` COMPACT_IMP_BOUNDED) THEN
    MP_TAC(ISPEC `k2:real^1->bool` COMPACT_IMP_BOUNDED) THEN ASM_REWRITE_TAC[BOUNDED_POS] THEN
    DISCH_THEN(X_CHOOSE_THEN `B2:real` STRIP_ASSUME_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `B1:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `B1 + B2` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `x:real^3` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `norm(vector[(x:real^3)$1; x$2]:real^2) + norm(lift(x$3))` THEN
    REWRITE_TAC[WAN_NORM3_SPLIT; NORM_LIFT] THEN MATCH_MP_TAC REAL_LE_ADD2 THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[GSYM NORM_LIFT] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    REWRITE_TAC[SET_RULE `{x:real^3 | P x /\ Q x} = {x | P x} INTER {x | Q x}`] THEN
    MATCH_MP_TAC CLOSED_INTER THEN CONJ_TAC THEN
    MATCH_MP_TAC CONTINUOUS_CLOSED_PREIMAGE_UNIV THEN
    ASM_SIMP_TAC[COMPACT_IMP_CLOSED; LINEAR_CONTINUOUS_AT; WAN_PROJ3_LINEAR]]);;

let WAN_TEST_PROD3 = prove
 (`!(phi:real^2->real) (psi:real^1->real) a b.
     wan_test (:real^2) phi /\ wan_test {r:real^1 | a < drop r /\ drop r < b} psi
     ==> wan_test {x:real^3 | a < x$3 /\ x$3 < b}
                  (\x:real^3. phi(vector[x$1; x$2]) * psi(lift(x$3))) /\
         (!x:real^3. wan_dpart 1 (\x:real^3. phi(vector[x$1; x$2]) * psi(lift(x$3))) x =
              wan_dpart 1 phi (vector[x$1; x$2]) * psi(lift(x$3))) /\
         (!x:real^3. wan_dpart 2 (\x:real^3. phi(vector[x$1; x$2]) * psi(lift(x$3))) x =
              wan_dpart 2 phi (vector[x$1; x$2]) * psi(lift(x$3))) /\
         (!x:real^3. wan_dpart 3 (\x:real^3. phi(vector[x$1; x$2]) * psi(lift(x$3))) x =
              phi(vector[x$1; x$2]) * wan_dpart 1 psi (lift(x$3)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wan_test] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `k1:real^2->bool` STRIP_ASSUME_TAC))
    (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `k2:real^1->bool` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`phi:real^2->real`; `\x:real^3. vector[x$1; x$2]:real^2`; `vec 0:real^2`]
                WAN_DPART_AFFINE) THEN
  MP_TAC(ISPECL [`psi:real^1->real`; `\x:real^3. lift(x$3)`; `vec 0:real^1`]
                WAN_DPART_AFFINE) THEN
  ASM_REWRITE_TAC[WAN_PROJ3_LINEAR; VECTOR_ADD_RID] THEN
  DISCH_THEN(LABEL_TAC "E1") THEN DISCH_THEN(LABEL_TAC "P1") THEN
  SUBGOAL_THEN
   `smooth_map_on (:real^3) (\x. lift((phi:real^2->real)(vector[x$1; x$2]))) /\
    smooth_map_on (:real^3) (\x. lift((psi:real^1->real)(lift(x$3))))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [USE_THEN "P1" (MP_TAC o SPECL [`1`; `vec 0:real^3`]);
      USE_THEN "E1" (MP_TAC o SPECL [`1`; `vec 0:real^3`])] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\x:real^3. (phi:real^2->real)(vector[x$1; x$2])`;
                 `\x:real^3. (psi:real^1->real)(lift(x$3))`] WAN_DPART_MUL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "M") THEN
  SUBGOAL_THEN
   `(!z. frechet_derivative (\y. lift((phi:real^2->real) y)) (at z) (vec 0) = vec 0) /\
    (!z. frechet_derivative (\y. lift((psi:real^1->real) y)) (at z) (vec 0) = vec 0)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [X_GEN_TAC `z:real^2` THEN
      MP_TAC(ISPEC `frechet_derivative (\y. lift((phi:real^2->real) y)) (at z)` LINEAR_0);
      X_GEN_TAC `z:real^1` THEN
      MP_TAC(ISPEC `frechet_derivative (\y. lift((psi:real^1->real) y)) (at z)` LINEAR_0)] THEN
    DISCH_THEN MATCH_MP_TAC THEN MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THENL
     [EXISTS_TAC `(:real^2)`; EXISTS_TAC `(:real^1)`] THEN
    ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(vector[(basis 1:real^3)$1; (basis 1:real^3)$2]:real^2) = basis 1 /\
    (vector[(basis 2:real^3)$1; (basis 2:real^3)$2]:real^2) = basis 2 /\
    (vector[(basis 3:real^3)$1; (basis 3:real^3)$2]:real^2) = vec 0 /\
    lift((basis 1:real^3)$3) = vec 0 /\ lift((basis 2:real^3)$3) = vec 0 /\
    lift((basis 3:real^3)$3) = basis 1`
  STRIP_ASSUME_TAC THENL
   [SIMP_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2; BASIS_COMPONENT; DIMINDEX_3; ARITH;
             VEC_COMPONENT; DIMINDEX_1; FORALL_1; LIFT_COMPONENT];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [USE_THEN "M" (MP_TAC o SPECL [`1`; `vec 0:real^3`]) THEN SIMP_TAC[];
    EXISTS_TAC `{x:real^3 | (vector[x$1; x$2]:real^2) IN k1 /\ lift(x$3) IN k2}` THEN
    ASM_SIMP_TAC[WAN_PROD3_SUPPORT_COMPACT] THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
      SUBGOAL_THEN `lift((x:real^3)$3) IN {r:real^1 | a < drop r /\ drop r < b}` MP_TAC THENL
       [ASM SET_TAC[]; REWRITE_TAC[IN_ELIM_THM; LIFT_DROP]];
      X_GEN_TAC `x:real^3` THEN REWRITE_TAC[IN_ELIM_THM; DE_MORGAN_THM] THEN
      STRIP_TAC THEN ASM_SIMP_TAC[REAL_MUL_LZERO; REAL_MUL_RZERO]];
    GEN_TAC THEN USE_THEN "M" (fun th -> REWRITE_TAC[th]) THEN
    ASM_REWRITE_TAC[DROP_VEC; REAL_MUL_RZERO; REAL_ADD_RID; wan_dpart];
    GEN_TAC THEN USE_THEN "M" (fun th -> REWRITE_TAC[th]) THEN
    ASM_REWRITE_TAC[DROP_VEC; REAL_MUL_RZERO; REAL_ADD_RID; wan_dpart];
    GEN_TAC THEN USE_THEN "M" (fun th -> REWRITE_TAC[th]) THEN
    ASM_REWRITE_TAC[DROP_VEC; REAL_MUL_LZERO; REAL_ADD_LID; wan_dpart]]);;

(* ------------------------------------------------------------------------- *)
(* Functions of the first two coordinates on subsets of real^3: weak        *)
(* partials of w(x1,x2) in the directions 1, 2 (from those of w) and 3      *)
(* (zero), by Fubini over the slices.                                       *)
(* ------------------------------------------------------------------------- *)

let WAN_WPD_EQ_ON = prove
 (`!(s:real^N->bool) i (u:real^N->real^K) u' v.
     wan_wpd s i u v /\ (!x. x IN s ==> u' x = u x) ==> wan_wpd s i u' v`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wan_wpd; wan_lloc] THEN STRIP_TAC THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `k:real^N->bool` THEN STRIP_TAC THEN
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_EQ THEN EXISTS_TAC `u:real^N->real^K` THEN
    ASM_SIMP_TAC[] THEN ASM_MESON_TAC[SUBSET];
    ASM_REWRITE_TAC[];
    X_GEN_TAC `phi:real^N->real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `phi:real^N->real`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC INTEGRAL_EQ THEN ASM_SIMP_TAC[]]);;

let WAN_TEST_DPART_ABS_INT = prove
 (`!(s:real^N->bool) phi i.
     wan_test s phi
     ==> (\x. lift(phi x)) absolutely_integrable_on s /\
         (\x. lift(wan_dpart i phi x)) absolutely_integrable_on s`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `phi:real^N->real`; `\x:real^N. vec 1:real^1`]
                WAN_TEST_PAIRING) THEN
  ASM_SIMP_TAC[WAN_CONTINUOUS_LLOC; CONTINUOUS_ON_CONST; GSYM LIFT_EQ_CMUL]);;

let WAN_TEST_DPART_INTEGRAL_ZERO = prove
 (`!(s:real^N->bool) phi i.
     open s /\ wan_test s phi ==> integral s (\x. lift(wan_dpart i phi x)) = vec 0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `\x:real^N. vec 1:real^1`; `i:num`] WAN_WPD_C1) THEN
  ASM_SIMP_TAC[CONTINUOUSLY_DIFFERENTIABLE_CONST] THEN
  REWRITE_TAC[wan_wpd] THEN
  DISCH_THEN(MP_TAC o SPEC `phi:real^N->real` o CONJUNCT2 o CONJUNCT2) THEN
  ASM_REWRITE_TAC[partial_derivative; FRECHET_DERIVATIVE_CONST_AT; VECTOR_MUL_RZERO;
                  INTEGRAL_0; VECTOR_NEG_0; GSYM LIFT_EQ_CMUL]);;

let WAN_TEST_VSLICE3 = prove
 (`!(s:real^3->bool) Phi (y:real^2).
     wan_test s Phi
     ==> wan_test (:real^1) (\r. Phi(vector[y$1; y$2; drop r])) /\
         (!r. wan_dpart 1 (\r. Phi(vector[y$1; y$2; drop r])) r =
              wan_dpart 3 Phi (vector[y$1; y$2; drop r]))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wan_test] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `k:real^3->bool` STRIP_ASSUME_TAC)) THEN
  ABBREV_TAC `L = \r:real^1. drop r % basis 3:real^3` THEN
  SUBGOAL_THEN `linear (L:real^1->real^3)` ASSUME_TAC THENL
   [EXPAND_TAC "L" THEN REWRITE_TAC[linear; DROP_ADD; DROP_CMUL] THEN
    REPEAT STRIP_TAC THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!r:real^1. vector[(y:real^2)$1; y$2; drop r]:real^3 = L r + vector[y$1; y$2; &0]`
  (fun th -> REWRITE_TAC[th]) THENL
   [EXPAND_TAC "L" THEN
    SIMP_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3; VECTOR_ADD_COMPONENT;
             VECTOR_MUL_COMPONENT; BASIS_COMPONENT; ARITH] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`Phi:real^3->real`; `L:real^1->real^3`;
                 `vector[(y:real^2)$1; y$2; &0]:real^3`] WAN_DPART_AFFINE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN REPEAT CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`1`; `vec 0:real^1`]) THEN SIMP_TAC[];
    EXISTS_TAC `{r:real^1 | (L:real^1->real^3) r + vector[(y:real^2)$1; y$2; &0] IN k}` THEN
    REWRITE_TAC[SUBSET_UNIV; IN_ELIM_THM] THEN CONJ_TAC THENL
     [REWRITE_TAC[COMPACT_EQ_BOUNDED_CLOSED] THEN CONJ_TAC THENL
       [FIRST_ASSUM(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
        REWRITE_TAC[BOUNDED_POS; IN_ELIM_THM] THEN
        DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
        EXISTS_TAC `B:real` THEN ASM_REWRITE_TAC[] THEN
        X_GEN_TAC `r:real^1` THEN DISCH_TAC THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `(L:real^1->real^3) r + vector[(y:real^2)$1; y$2; &0]`) THEN
        ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC(REAL_ARITH `a <= b ==> b <= B ==> a <= B`) THEN
        EXPAND_TAC "L" THEN
        MP_TAC(SPEC `drop r % basis 3 + vector[(y:real^2)$1; y$2; &0]:real^3`
                    WAN_NORM_PROJ3) THEN
        SIMP_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; VECTOR_3; BASIS_COMPONENT;
                 DIMINDEX_3; ARITH] THEN
        REWRITE_TAC[NORM_1; drop] THEN REAL_ARITH_TAC;
        MATCH_MP_TAC CONTINUOUS_CLOSED_PREIMAGE_UNIV THEN
        ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN GEN_TAC THEN
        MATCH_MP_TAC CONTINUOUS_ADD THEN
        ASM_SIMP_TAC[LINEAR_CONTINUOUS_AT; CONTINUOUS_CONST]];
      ASM_SIMP_TAC[]];
    GEN_TAC THEN ASM_REWRITE_TAC[] THEN REWRITE_TAC[wan_dpart] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN EXPAND_TAC "L" THEN
    SIMP_TAC[drop; BASIS_COMPONENT; DIMINDEX_1; ARITH; VECTOR_MUL_LID]]);;

let WAN_WPD_PROJ3 = prove
 (`!(s:real^3->bool) (w:real^2->real^K) v i.
     wan_wpd (:real^2) i w v /\ (i = 1 \/ i = 2)
     ==> wan_wpd s i (\x. w(vector[x$1; x$2])) (\x. v(vector[x$1; x$2]))`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  REWRITE_TAC[wan_wpd] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "W"))) THEN
  SUBGOAL_THEN `wan_lloc (:real^3) (\x. (w:real^2->real^K)(vector[x$1; x$2])) /\
                wan_lloc (:real^3) (\x. (v:real^2->real^K)(vector[x$1; x$2]))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC WAN_LLOC_PROJ3 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC WAN_LLOC_SUBSET THEN EXISTS_TAC `(:real^3)` THEN
    ASM_REWRITE_TAC[SUBSET_UNIV];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC WAN_LLOC_SUBSET THEN EXISTS_TAC `(:real^3)` THEN
    ASM_REWRITE_TAC[SUBSET_UNIV];
    ALL_TAC] THEN
  X_GEN_TAC `Phi:real^3->real` THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [wan_test]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `k:real^3->bool` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `wan_test (:real^3) Phi` ASSUME_TAC THENL
   [MATCH_MP_TAC WAN_TEST_SUBSET THEN EXISTS_TAC `s:real^3->bool` THEN
    ASM_REWRITE_TAC[SUBSET_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `integral s (\x. wan_dpart i (Phi:real^3->real) x % (w:real^2->real^K)(vector[x$1; x$2])) =
    integral (:real^3) (\x. wan_dpart i Phi x % w(vector[x$1; x$2])) /\
    integral s (\x. Phi x % (v:real^2->real^K)(vector[x$1; x$2])) =
    integral (:real^3) (\x. Phi x % v(vector[x$1; x$2]))`
  (fun th -> REWRITE_TAC[th]) THENL
   [CONJ_TAC THEN MATCH_MP_TAC WAN_INTEGRAL_SUPPORT_SUBSET THEN
    EXISTS_TAC `k:real^3->bool` THEN ASM_REWRITE_TAC[SUBSET_UNIV] THEN
    X_GEN_TAC `x:real^3` THEN DISCH_TAC THENL
     [MP_TAC(ISPECL [`Phi:real^3->real`; `k:real^3->bool`; `i:num`; `x:real^3`]
                    WAN_TEST_DPART_ZERO) THEN
      ASM_SIMP_TAC[VECTOR_MUL_LZERO];
      ASM_SIMP_TAC[VECTOR_MUL_LZERO]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(:real^3)`; `Phi:real^3->real`; `\x:real^3. (w:real^2->real^K)(vector[x$1; x$2])`]
                WAN_TEST_PAIRING) THEN
  MP_TAC(ISPECL [`(:real^3)`; `Phi:real^3->real`; `\x:real^3. (v:real^2->real^K)(vector[x$1; x$2])`]
                WAN_TEST_PAIRING) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o MATCH_MP WAN_FUBINI3 o CONJUNCT1) THEN
  DISCH_THEN(MP_TAC o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
  REWRITE_TAC[VECTOR_3; WAN_VECTOR2_ETA] THEN DISCH_THEN(LABEL_TAC "R") THEN
  DISCH_THEN(MP_TAC o MATCH_MP WAN_FUBINI3 o SPEC `i:num` o CONJUNCT2) THEN
  DISCH_THEN(MP_TAC o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
  REWRITE_TAC[VECTOR_3; WAN_VECTOR2_ETA] THEN DISCH_THEN(LABEL_TAC "L") THEN
  SUBGOAL_THEN
   `!r:real^1.
      integral (:real^2)
        (\y. wan_dpart i (Phi:real^3->real) (vector[y$1; y$2; drop r]) % (w:real^2->real^K) y) =
      --(integral (:real^2) (\y. Phi(vector[y$1; y$2; drop r]) % (v:real^2->real^K) y))`
  (LABEL_TAC "E") THENL
   [X_GEN_TAC `r:real^1` THEN
    MP_TAC(ISPECL [`(:real^3)`; `Phi:real^3->real`; `drop r`] WAN_TEST_SLICE3) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    USE_THEN "W" (MP_TAC o SPEC `\y:real^2. (Phi:real^3->real)(vector[y$1; y$2; drop r])`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC INTEGRAL_EQ THEN X_GEN_TAC `y:real^2` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC(ISPECL
   [`\r:real^1. integral (:real^2)
       (\y. wan_dpart i (Phi:real^3->real) (vector[y$1; y$2; drop r]) % (w:real^2->real^K) y)`;
    `(:real^1)`] HAS_INTEGRAL_UNIQUE) THEN
  CONJ_TAC THENL
   [USE_THEN "L" ACCEPT_TAC;
    USE_THEN "E" (fun th -> REWRITE_TAC[th]) THEN
    MATCH_MP_TAC HAS_INTEGRAL_NEG THEN USE_THEN "R" ACCEPT_TAC]);;

let WAN_WPD_PROJ3_VERT = prove
 (`!(s:real^3->bool) (w:real^2->real^K).
     wan_lloc (:real^2) w ==> wan_wpd s 3 (\x. w(vector[x$1; x$2])) (\x. vec 0)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[wan_wpd; WAN_LLOC_ZERO; VECTOR_MUL_RZERO; INTEGRAL_0; VECTOR_NEG_0] THEN
  SUBGOAL_THEN `wan_lloc (:real^3) (\x. (w:real^2->real^K)(vector[x$1; x$2]))` ASSUME_TAC THENL
   [MATCH_MP_TAC WAN_LLOC_PROJ3 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC WAN_LLOC_SUBSET THEN EXISTS_TAC `(:real^3)` THEN
    ASM_REWRITE_TAC[SUBSET_UNIV];
    ALL_TAC] THEN
  X_GEN_TAC `Phi:real^3->real` THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [wan_test]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `k:real^3->bool` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `wan_test (:real^3) Phi` ASSUME_TAC THENL
   [MATCH_MP_TAC WAN_TEST_SUBSET THEN EXISTS_TAC `s:real^3->bool` THEN
    ASM_REWRITE_TAC[SUBSET_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `integral s (\x. wan_dpart 3 (Phi:real^3->real) x % (w:real^2->real^K)(vector[x$1; x$2])) =
    integral (:real^3) (\x. wan_dpart 3 Phi x % w(vector[x$1; x$2]))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC WAN_INTEGRAL_SUPPORT_SUBSET THEN
    EXISTS_TAC `k:real^3->bool` THEN ASM_REWRITE_TAC[SUBSET_UNIV] THEN
    X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`Phi:real^3->real`; `k:real^3->bool`; `3`; `x:real^3`]
                  WAN_TEST_DPART_ZERO) THEN
    ASM_SIMP_TAC[VECTOR_MUL_LZERO];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(:real^3)`; `Phi:real^3->real`; `\x:real^3. (w:real^2->real^K)(vector[x$1; x$2])`]
                WAN_TEST_PAIRING) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o MATCH_MP WAN_FUBINI3 o SPEC `3` o CONJUNCT2) THEN
  DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2) THEN
  REWRITE_TAC[VECTOR_3; WAN_VECTOR2_ETA] THEN
  SUBGOAL_THEN
   `!y:real^2. integral (:real^1)
                 (\r. wan_dpart 3 (Phi:real^3->real) (vector[y$1; y$2; drop r]) %
                      (w:real^2->real^K) y) =
               vec 0`
  (fun th -> REWRITE_TAC[th]) THENL
   [X_GEN_TAC `y:real^2` THEN
    MP_TAC(ISPECL [`(:real^3)`; `Phi:real^3->real`; `y:real^2`] WAN_TEST_VSLICE3) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `!r. wan_dpart 3 (Phi:real^3->real) (vector[(y:real^2)$1; y$2; drop r]) =
          wan_dpart 1 (\r. Phi(vector[y$1; y$2; drop r])) r`
    (fun th -> REWRITE_TAC[th]) THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL
     [`\r:real^1. wan_dpart 1 (\r. (Phi:real^3->real)(vector[(y:real^2)$1; y$2; drop r])) r`;
      `(w:real^2->real^K) y`; `(:real^1)`] WAN_ABS_INT_SCALAR_VEC) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL
     [MP_TAC(ISPECL [`(:real^1)`; `\r:real^1. (Phi:real^3->real)(vector[(y:real^2)$1; y$2; drop r])`;
                     `1`] WAN_TEST_DPART_ABS_INT) THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN
    MP_TAC(ISPECL [`(:real^1)`; `\r:real^1. (Phi:real^3->real)(vector[(y:real^2)$1; y$2; drop r])`;
                   `1`] WAN_TEST_DPART_INTEGRAL_ZERO) THEN
    ASM_REWRITE_TAC[OPEN_UNIV] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[DROP_VEC; VECTOR_MUL_LZERO];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP INTEGRAL_UNIQUE) THEN REWRITE_TAC[INTEGRAL_0] THEN
  DISCH_THEN(ACCEPT_TAC o SYM));;

(* ------------------------------------------------------------------------- *)
(* Averages over the third coordinate: for H in L^1_loc of a slab and a     *)
(* test psi in the third variable, v(y) = int psi(r) H(y,r) dr is in        *)
(* L^1_loc(R^2) and pairs with planar tests as psi times H does on the      *)
(* slab.  Weak partials of w(x1,x2) on a slab give weak partials of w.      *)
(* ------------------------------------------------------------------------- *)

let WAN_SLICE_FUBINI3 = prove
 (`!(phi:real^2->real) (psi:real^1->real) (H:real^3->real^K).
     (\x:real^3. (phi(vector[x$1; x$2]) * psi(lift(x$3))) % H x)
       absolutely_integrable_on (:real^3)
     ==> (\y. phi y % integral (:real^1) (\r. psi r % H(vector[y$1; y$2; drop r])))
           absolutely_integrable_on (:real^2) /\
         integral (:real^2)
           (\y. phi y % integral (:real^1) (\r. psi r % H(vector[y$1; y$2; drop r]))) =
         integral (:real^3) (\x. (phi(vector[x$1; x$2]) * psi(lift(x$3))) % H x)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP WAN_FUBINI3) THEN
  REWRITE_TAC[VECTOR_3; WAN_VECTOR2_ETA; LIFT_DROP] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC))) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP WAN_FUBINI3 o MATCH_MP ABSOLUTELY_INTEGRABLE_NORM) THEN
  REWRITE_TAC[VECTOR_3; WAN_VECTOR2_ETA; LIFT_DROP] THEN
  DISCH_THEN(ASSUME_TAC o CONJUNCT1 o CONJUNCT2) THEN
  SUBGOAL_THEN
   `!y:real^2.
      (\r. ((phi:real^2->real) y * (psi:real^1->real) r) %
           (H:real^3->real^K)(vector[y$1; y$2; drop r])) absolutely_integrable_on (:real^1)
      ==> integral (:real^1) (\r. (phi y * psi r) % H(vector[y$1; y$2; drop r])) =
          phi y % integral (:real^1) (\r. psi r % H(vector[y$1; y$2; drop r]))`
  (LABEL_TAC "PW") THENL
   [X_GEN_TAC `y:real^2` THEN DISCH_TAC THEN
    ASM_CASES_TAC `(phi:real^2->real) y = &0` THEN
    ASM_REWRITE_TAC[REAL_MUL_LZERO; VECTOR_MUL_LZERO; INTEGRAL_0] THEN
    REWRITE_TAC[GSYM VECTOR_MUL_ASSOC] THEN MATCH_MP_TAC INTEGRAL_CMUL THEN
    SUBGOAL_THEN
     `(\r. (psi:real^1->real) r % (H:real^3->real^K)(vector[(y:real^2)$1; y$2; drop r])) =
      (\r. inv((phi:real^2->real) y) % ((phi y * psi r) % H(vector[y$1; y$2; drop r])))`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; VECTOR_MUL_ASSOC] THEN GEN_TAC THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN UNDISCH_TAC `~((phi:real^2->real) y = &0)` THEN
      CONV_TAC REAL_FIELD;
      MATCH_MP_TAC INTEGRABLE_CMUL THEN
      MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\y. (phi:real^2->real) y %
          integral (:real^1) (\r. (psi:real^1->real) r % (H:real^3->real^K)(vector[y$1; y$2; drop r])))
     has_integral
     integral (:real^3) (\x. (phi(vector[x$1; x$2]) * psi(lift(x$3))) % H x)) (:real^2)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HAS_INTEGRAL_SPIKE THEN
    EXISTS_TAC
     `\y:real^2. integral (:real^1)
        (\r. ((phi:real^2->real) y * (psi:real^1->real) r) %
             (H:real^3->real^K)(vector[y$1; y$2; drop r]))` THEN
    EXISTS_TAC
     `{y:real^2 | ~((\r. ((phi:real^2->real) y * (psi:real^1->real) r) %
                         (H:real^3->real^K)(vector[y$1; y$2; drop r]))
                     absolutely_integrable_on (:real^1))}` THEN
    ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `y:real^2` THEN REWRITE_TAC[IN_DIFF; IN_UNIV; IN_ELIM_THM; NOT_CLAUSES] THEN
    DISCH_TAC THEN CONV_TAC SYM_CONV THEN USE_THEN "PW" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [ALL_TAC; MATCH_MP_TAC INTEGRAL_UNIQUE THEN ASM_REWRITE_TAC[]] THEN
  MATCH_MP_TAC MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_ABSOLUTELY_INTEGRABLE_AE THEN
  EXISTS_TAC
   `\y:real^2. integral (:real^1)
      (\r. lift(norm(((phi:real^2->real) y * (psi:real^1->real) r) %
                     (H:real^3->real^K)(vector[y$1; y$2; drop r]))))` THEN
  EXISTS_TAC
   `{y:real^2 | ~((\r. ((phi:real^2->real) y * (psi:real^1->real) r) %
                       (H:real^3->real^K)(vector[y$1; y$2; drop r]))
                   absolutely_integrable_on (:real^1))}` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_IMP_MEASURABLE THEN
    FIRST_ASSUM(ACCEPT_TAC o MATCH_MP HAS_INTEGRAL_INTEGRABLE);
    FIRST_ASSUM(ACCEPT_TAC o MATCH_MP HAS_INTEGRAL_INTEGRABLE);
    X_GEN_TAC `y:real^2` THEN REWRITE_TAC[IN_DIFF; IN_UNIV; IN_ELIM_THM; NOT_CLAUSES] THEN
    DISCH_TAC THEN USE_THEN "PW" (fun th -> FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP th)) THEN
    MATCH_MP_TAC INTEGRAL_NORM_BOUND_INTEGRAL THEN
    ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE; ABSOLUTELY_INTEGRABLE_NORM;
                 LIFT_DROP; REAL_LE_REFL]]);;

let WAN_SLICE_AVG3 = prove
 (`!(H:real^3->real^K) (psi:real^1->real) a b.
     wan_lloc {x:real^3 | a < x$3 /\ x$3 < b} H /\
     wan_test {r:real^1 | a < drop r /\ drop r < b} psi
     ==> wan_lloc (:real^2)
           (\y. integral (:real^1) (\r. psi r % H(vector[y$1; y$2; drop r]))) /\
         (!phi. wan_test (:real^2) phi
                ==> integral {x:real^3 | a < x$3 /\ x$3 < b}
                      (\x. (phi(vector[x$1; x$2]) * psi(lift(x$3))) % H x) =
                    integral (:real^2)
                      (\y. phi y % integral (:real^1) (\r. psi r % H(vector[y$1; y$2; drop r]))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!phi. wan_test (:real^2) phi
          ==> (\x:real^3. ((phi:real^2->real)(vector[x$1; x$2]) * (psi:real^1->real)(lift(x$3))) %
                          (H:real^3->real^K) x) absolutely_integrable_on (:real^3) /\
              integral {x:real^3 | a < x$3 /\ x$3 < b}
                (\x. (phi(vector[x$1; x$2]) * psi(lift(x$3))) % H x) =
              integral (:real^3) (\x. (phi(vector[x$1; x$2]) * psi(lift(x$3))) % H x)`
  (LABEL_TAC "AI") THENL
   [X_GEN_TAC `phi:real^2->real` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`phi:real^2->real`; `psi:real^1->real`; `a:real`; `b:real`]
                  WAN_TEST_PROD3) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
    FIRST_ASSUM(MP_TAC o REWRITE_RULE[wan_test]) THEN
    DISCH_THEN(X_CHOOSE_THEN `k:real^3->bool` STRIP_ASSUME_TAC o CONJUNCT2) THEN
    MP_TAC(ISPECL [`{x:real^3 | a < x$3 /\ x$3 < b}`;
                   `\x:real^3. (phi:real^2->real)(vector[x$1; x$2]) * (psi:real^1->real)(lift(x$3))`;
                   `H:real^3->real^K`] WAN_TEST_PAIRING) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
    SUBGOAL_THEN
     `!x:real^3. ~(x IN k)
                 ==> ((phi:real^2->real)(vector[x$1; x$2]) * (psi:real^1->real)(lift(x$3))) %
                     (H:real^3->real^K) x = vec 0`
    ASSUME_TAC THENL [REPEAT STRIP_TAC THEN ASM_SIMP_TAC[VECTOR_MUL_LZERO]; ALL_TAC] THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL
       [`\x:real^3. ((phi:real^2->real)(vector[x$1; x$2]) * (psi:real^1->real)(lift(x$3))) %
                    (H:real^3->real^K) x`;
        `k:real^3->bool`; `{x:real^3 | a < x$3 /\ x$3 < b}`; `(:real^3)`]
       WAN_ABS_INTEGRABLE_SUPPORT_SUBSET) THEN
      ASM_REWRITE_TAC[SUBSET_UNIV];
      MATCH_MP_TAC WAN_INTEGRAL_SUPPORT_SUBSET THEN EXISTS_TAC `k:real^3->bool` THEN
      ASM_REWRITE_TAC[SUBSET_UNIV]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [ALL_TAC;
    X_GEN_TAC `phi:real^2->real` THEN DISCH_TAC THEN
    USE_THEN "AI" (MP_TAC o SPEC `phi:real^2->real`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o MATCH_MP WAN_SLICE_FUBINI3) SUBST1_TAC) THEN
    DISCH_THEN(ACCEPT_TAC o SYM o CONJUNCT2)] THEN
  REWRITE_TAC[wan_lloc] THEN X_GEN_TAC `kk:real^2->bool` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`(:real^2)`; `kk:real^2->bool`] WAN_SMOOTH_URYSOHN) THEN
  ASM_REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV] THEN
  DISCH_THEN(X_CHOOSE_THEN `chi:real^2->real` STRIP_ASSUME_TAC) THEN
  USE_THEN "AI" (MP_TAC o SPEC `chi:real^2->real`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1 o MATCH_MP WAN_SLICE_FUBINI3 o CONJUNCT1) THEN
  DISCH_THEN(MP_TAC o SPEC `kk:real^2->bool` o MATCH_MP
    (REWRITE_RULE[IMP_CONJ] ABSOLUTELY_INTEGRABLE_ON_LEBESGUE_MEASURABLE_SUBSET)) THEN
  ASM_SIMP_TAC[SUBSET_UNIV; LEBESGUE_MEASURABLE_COMPACT] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] ABSOLUTELY_INTEGRABLE_EQ) THEN
  ASM_SIMP_TAC[VECTOR_MUL_LID]);;

let WAN_SLAB_PSI = prove
 (`!a b. a < b
         ==> ?psi. wan_test {r:real^1 | a < drop r /\ drop r < b} psi /\
                   integral (:real^1) (\r. lift(psi r)) = lift(&1)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `e = (b - a) / &4` THEN
  SUBGOAL_THEN `&0 < e` ASSUME_TAC THENL [EXPAND_TAC "e" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  EXISTS_TAC `\r:real^1. wan_mke e (lift((a + b) / &2) - r)` THEN CONJ_TAC THENL
   [REWRITE_TAC[wan_test] THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`wan_mke e:real^1->real`; `\r:real^1. --r`; `lift((a + b) / &2)`;
                     `1`; `vec 0:real^1`] WAN_DPART_AFFINE) THEN
      ASM_SIMP_TAC[WAN_MKE_PROPS] THEN ANTS_TAC THENL
       [REWRITE_TAC[linear] THEN REPEAT STRIP_TAC THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o CONJUNCT1) THEN MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
      REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN REWRITE_TAC[] THEN
      AP_TERM_TAC THEN AP_TERM_TAC THEN VECTOR_ARITH_TAC;
      EXISTS_TAC `cball(lift((a + b) / &2),e)` THEN REWRITE_TAC[COMPACT_CBALL] THEN
      CONJ_TAC THENL
       [REWRITE_TAC[SUBSET; IN_CBALL; IN_ELIM_THM; DIST_REAL; GSYM drop; LIFT_DROP] THEN
        X_GEN_TAC `r:real^1` THEN EXPAND_TAC "e" THEN ASM_REAL_ARITH_TAC;
        X_GEN_TAC `r:real^1` THEN REWRITE_TAC[IN_CBALL; REAL_NOT_LE; dist] THEN
        DISCH_TAC THEN MATCH_MP_TAC WAN_MKE_ZERO THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]]];
    MATCH_MP_TAC INTEGRAL_UNIQUE THEN
    MP_TAC(ISPECL [`e:real`; `lift((a + b) / &2)`] WAN_MKE_INTEGRAL_AT) THEN
    ASM_REWRITE_TAC[]]);;

let WAN_SLICE_WPD3 = prove
 (`!(w:real^2->real^K) (H:real^3->real^K) psi a b i.
     wan_wpd {x:real^3 | a < x$3 /\ x$3 < b} i (\x. w(vector[x$1; x$2])) H /\
     (i = 1 \/ i = 2) /\
     wan_test {r:real^1 | a < drop r /\ drop r < b} psi /\
     integral (:real^1) (\r. lift(psi r)) = lift(&1)
     ==> wan_lloc (:real^2) w /\
         wan_wpd (:real^2) i w
           (\y. integral (:real^1) (\r. psi r % H(vector[y$1; y$2; drop r])))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [wan_wpd]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "WS"))) THEN
  SUBGOAL_THEN `wan_test (:real^1) (psi:real^1->real)` ASSUME_TAC THENL
   [MATCH_MP_TAC WAN_TEST_SUBSET THEN
    EXISTS_TAC `{r:real^1 | a < drop r /\ drop r < b}` THEN ASM_REWRITE_TAC[SUBSET_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^2. integral (:real^1) (\r. (psi:real^1->real) r % (w:real^2->real^K) y) = w y`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`psi:real^1->real`; `(w:real^2->real^K) y`; `(:real^1)`]
                  WAN_ABS_INT_SCALAR_VEC) THEN
    ANTS_TAC THENL
     [MP_TAC(ISPECL [`(:real^1)`; `psi:real^1->real`; `0`] WAN_TEST_DPART_ABS_INT) THEN
      ASM_SIMP_TAC[];
      DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN ASM_REWRITE_TAC[LIFT_DROP; VECTOR_MUL_LID]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\x:real^3. (w:real^2->real^K)(vector[x$1; x$2])`; `psi:real^1->real`;
                 `a:real`; `b:real`] WAN_SLICE_AVG3) THEN
  ASM_REWRITE_TAC[VECTOR_3; WAN_VECTOR2_ETA; ETA_AX] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "Aw")) THEN
  MP_TAC(ISPECL [`H:real^3->real^K`; `psi:real^1->real`; `a:real`; `b:real`] WAN_SLICE_AVG3) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "AH")) THEN
  ASM_REWRITE_TAC[wan_wpd] THEN X_GEN_TAC `phi:real^2->real` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`phi:real^2->real`; `psi:real^1->real`; `a:real`; `b:real`] WAN_TEST_PROD3) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "D")) THEN
  SUBGOAL_THEN
   `!x:real^3. wan_dpart i (\x:real^3. (phi:real^2->real)(vector[x$1; x$2]) *
                                       (psi:real^1->real)(lift(x$3))) x =
               wan_dpart i phi (vector[x$1; x$2]) * psi(lift(x$3))`
  ASSUME_TAC THENL
   [UNDISCH_TAC `i = 1 \/ i = 2` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "D" (fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  REMOVE_THEN "WS" (MP_TAC o SPEC
    `\x:real^3. (phi:real^2->real)(vector[x$1; x$2]) * (psi:real^1->real)(lift(x$3))`) THEN
  ASM_REWRITE_TAC[] THEN
  USE_THEN "AH" (MP_TAC o SPEC `phi:real^2->real`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  USE_THEN "Aw" (MP_TAC o SPEC `wan_dpart i (phi:real^2->real)`) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[WAN_TEST_DPART_TEST]; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The derivative of the inverse stereographic projection and its           *)
(* conformality: with D = |y|^2 + 1, the partials S_i of stereo2_n_inv      *)
(* satisfy S_i . S_j = (2 / D)^2 delta_ij and stereo2_n_inv y . S_i = 0.    *)
(* ------------------------------------------------------------------------- *)

let WAN_NORM2_PLUS1_NZ = prove
 (`!y:real^N. ~(norm y pow 2 + &1 = &0) /\ &0 < norm y pow 2 + &1`,
  GEN_TAC THEN MP_TAC(SPEC `norm(y:real^N)` REAL_LE_POW_2) THEN REAL_ARITH_TAC);;

let WAN_STEREO_SCALED = prove
 (`!y:real^2. (norm y pow 2 + &1) % stereo2_n_inv y =
              vector[&2 * y$1; &2 * y$2; norm y pow 2 - &1]`,
  GEN_TAC THEN MP_TAC(ISPEC `y:real^2` WAN_NORM2_PLUS1_NZ) THEN STRIP_TAC THEN
  SIMP_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3; VECTOR_MUL_COMPONENT;
           STEX_STEREO2_N_INV_COMPONENTS] THEN
  REPEAT CONJ_TAC THEN UNDISCH_TAC `~(norm(y:real^2) pow 2 + &1 = &0)` THEN
  CONV_TAC REAL_FIELD);;

let WAN_STEREO_DERIV = prove
 (`!y:real^2.
     (stereo2_n_inv has_derivative
      (\h. inv(norm y pow 2 + &1) %
           (&2 % (vector[h$1; h$2; &0]:real^3) +
            (&2 * (y dot h)) % (basis 3 - stereo2_n_inv y)))) (at y)`,
  GEN_TAC THEN
  ABBREV_TAC `s' = frechet_derivative stereo2_n_inv (at (y:real^2))` THEN
  SUBGOAL_THEN `(stereo2_n_inv has_derivative (s':real^2->real^3)) (at (y:real^2))`
  ASSUME_TAC THENL
   [EXPAND_TAC "s'" THEN REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `(:real^2)` THEN
    REWRITE_TAC[OPEN_UNIV; IN_UNIV; STEX_STEREO2_N_INV_SMOOTH];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((lift o (\z:real^2. norm z pow 2 + &1)) has_derivative
     (lift o (\h. &2 * (y dot h)))) (at y)`
  ASSUME_TAC THENL
   [REWRITE_TAC[o_DEF; LIFT_ADD; LIFT_CMUL] THEN
    SUBGOAL_THEN `(\h:real^2. &2 % lift(y dot h)) = (\h. &2 % lift(y dot h) + vec 0)`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; VECTOR_ADD_RID]; ALL_TAC] THEN
    MATCH_MP_TAC HAS_DERIVATIVE_ADD THEN
    REWRITE_TAC[HAS_DERIVATIVE_CONST; HAS_DERIVATIVE_SQNORM_AT];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\z:real^2. norm z pow 2 + &1`; `\h:real^2. &2 * (y dot h)`;
                 `stereo2_n_inv`; `s':real^2->real^3`; `y:real^2`] HAS_DERIVATIVE_MUL_AT) THEN
  ASM_REWRITE_TAC[WAN_STEREO_SCALED] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `((\z:real^2. vector[&2 * z$1; &2 * z$2; norm z pow 2 - &1]:real^3) has_derivative
     (\h. vector[&2 * h$1; &2 * h$2; &0] + drop(&2 % lift(y dot h)) % basis 3)) (at y)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `(\z:real^2. vector[&2 * z$1; &2 * z$2; norm z pow 2 - &1]:real^3) =
      (\z. vector[&2 * z$1; &2 * z$2; &0] + drop(lift(norm z pow 2) - lift(&1)) % basis 3)`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
      SIMP_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3; VECTOR_ADD_COMPONENT;
               VECTOR_MUL_COMPONENT; BASIS_COMPONENT; ARITH; DROP_SUB; LIFT_DROP] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC HAS_DERIVATIVE_ADD THEN CONJ_TAC THENL
     [MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN REWRITE_TAC[linear] THEN
      SIMP_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3; VECTOR_ADD_COMPONENT;
               VECTOR_MUL_COMPONENT] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC HAS_DERIVATIVE_VMUL_DROP THEN
      SUBGOAL_THEN `(\h:real^2. &2 % lift(y dot h)) = (\h. &2 % lift(y dot h) - vec 0)`
      SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; VECTOR_SUB_RZERO]; ALL_TAC] THEN
      MATCH_MP_TAC HAS_DERIVATIVE_SUB THEN
      REWRITE_TAC[HAS_DERIVATIVE_CONST; HAS_DERIVATIVE_SQNORM_AT]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!h:real^2. (norm y pow 2 + &1) % (s':real^2->real^3) h + (&2 * (y dot h)) % stereo2_n_inv y =
               vector[&2 * h$1; &2 * h$2; &0] + drop(&2 % lift(y dot h)) % basis 3`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM FUN_EQ_THM] THEN MATCH_MP_TAC FRECHET_DERIVATIVE_UNIQUE_AT THEN
    EXISTS_TAC `\z:real^2. vector[&2 * z$1; &2 * z$2; norm z pow 2 - &1]:real^3` THEN
    EXISTS_TAC `y:real^2` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(s':real^2->real^3) =
    (\h. inv(norm y pow 2 + &1) %
         (&2 % (vector[h$1; h$2; &0]:real^3) +
          (&2 * (y dot h)) % (basis 3 - stereo2_n_inv y)))`
  (fun th -> ASM_REWRITE_TAC[GSYM th]) THEN
  REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `h:real^2` THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `h:real^2`) THEN
  MP_TAC(ISPEC `y:real^2` WAN_NORM2_PLUS1_NZ) THEN STRIP_TAC THEN
  REWRITE_TAC[DROP_CMUL; LIFT_DROP] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `(s':real^2->real^3) h =
    inv(norm(y:real^2) pow 2 + &1) % ((norm y pow 2 + &1) % s' h)`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_LINV; VECTOR_MUL_LID]; ALL_TAC] THEN
  AP_TERM_TAC THEN POP_ASSUM MP_TAC THEN
  SIMP_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3; VECTOR_ADD_COMPONENT;
           VECTOR_MUL_COMPONENT; VECTOR_SUB_COMPONENT; BASIS_COMPONENT; ARITH] THEN
  CONV_TAC REAL_RING);;

let WAN_STEREO_PARTIAL = prove
 (`!(y:real^2) h.
     frechet_derivative stereo2_n_inv (at y) h =
     inv(norm y pow 2 + &1) %
     (&2 % (vector[h$1; h$2; &0]:real^3) + (&2 * (y dot h)) % (basis 3 - stereo2_n_inv y))`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPEC `y:real^2` WAN_STEREO_DERIV) THEN
  DISCH_THEN(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN REWRITE_TAC[]);;

let WAN_STEREO_CONFORMAL = prove
 (`!y:real^2.
     frechet_derivative stereo2_n_inv (at y) (basis 1) dot
     frechet_derivative stereo2_n_inv (at y) (basis 1) = (&2 / (norm y pow 2 + &1)) pow 2 /\
     frechet_derivative stereo2_n_inv (at y) (basis 2) dot
     frechet_derivative stereo2_n_inv (at y) (basis 2) = (&2 / (norm y pow 2 + &1)) pow 2 /\
     frechet_derivative stereo2_n_inv (at y) (basis 1) dot
     frechet_derivative stereo2_n_inv (at y) (basis 2) = &0 /\
     stereo2_n_inv y dot frechet_derivative stereo2_n_inv (at y) (basis 1) = &0 /\
     stereo2_n_inv y dot frechet_derivative stereo2_n_inv (at y) (basis 2) = &0 /\
     stereo2_n_inv y dot stereo2_n_inv y = &1`,
  GEN_TAC THEN REWRITE_TAC[WAN_STEREO_PARTIAL] THEN
  MP_TAC(ISPEC `y:real^2` WAN_NORM2_PLUS1_NZ) THEN
  SIMP_TAC[DOT_3; DOT_2; VECTOR_3; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
           VECTOR_SUB_COMPONENT; BASIS_COMPONENT; DIMINDEX_2; DIMINDEX_3; ARITH;
           STEX_STEREO2_N_INV_COMPONENTS; NORM_POW_2] THEN
  DISCH_THEN(fun th -> REPEAT CONJ_TAC THEN MP_TAC th) THEN CONV_TAC REAL_FIELD);;

(* ------------------------------------------------------------------------- *)
(* The north chart of the shell: wan_nch (x1,x2,x3) = x3 sigma(x1,x2) maps   *)
(* the slab 1/2 < x3 < 2 diffeomorphically onto the shell minus the        *)
(* positive x3-axis, with inverse wan_nchi.                                  *)
(* ------------------------------------------------------------------------- *)

let wan_nch = new_definition
 `wan_nch (x:real^3) = x$3 % stereo2_n_inv(vector[x$1; x$2]:real^2)`;;

let wan_nchi = new_definition
 `wan_nchi (z:real^3) =
    vector[z$1 / (norm z - z$3); z$2 / (norm z - z$3); norm z]:real^3`;;

let WAN_OPEN_REAL_LT = prove
 (`!(f:real^N->real) g.
     (!x. (\x. lift(f x)) continuous at x) /\ (!x. (\x. lift(g x)) continuous at x)
     ==> open {x | f x < g x}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\x:real^N. lift(g x - f x)`; `{t:real^1 | t$1 > &0}`]
                CONTINUOUS_OPEN_PREIMAGE_UNIV) THEN
  REWRITE_TAC[OPEN_HALFSPACE_COMPONENT_GT; GSYM drop; LIFT_DROP; real_gt; REAL_SUB_LT;
              IN_ELIM_THM] THEN
  DISCH_THEN MATCH_MP_TAC THEN GEN_TAC THEN REWRITE_TAC[LIFT_SUB] THEN
  MATCH_MP_TAC CONTINUOUS_SUB THEN ASM_REWRITE_TAC[]);;

let WAN_NCH_OPEN = prove
 (`open {x:real^3 | &1 / &2 < x$3 /\ x$3 < &2} /\
   open {z:real^3 | &1 / &2 < norm z /\ norm z < &2 /\ z$3 < norm z}`,
  REWRITE_TAC[SET_RULE `{x:real^3 | P x /\ Q x} = {x | P x} INTER {x | Q x}`] THEN
  CONJ_TAC THEN REPEAT(MATCH_MP_TAC OPEN_INTER THEN CONJ_TAC) THEN
  MATCH_MP_TAC WAN_OPEN_REAL_LT THEN
  REWRITE_TAC[CONTINUOUS_CONST] THEN REPEAT CONJ_TAC THEN GEN_TAC THEN
  TRY(MATCH_MP_TAC CONTINUOUS_LIFT_NORM_COMPOSE) THEN
  TRY(MATCH_MP_TAC CONTINUOUS_LIFT_COMPONENT_COMPOSE) THEN
  REWRITE_TAC[CONTINUOUS_AT_ID]);;

let WAN_NCH_SMOOTH = prove
 (`smooth_map_on (:real^3) wan_nch`,
  SUBGOAL_THEN `wan_nch = (\x:real^3. drop(lift(x$3)) % (stereo2_n_inv o (\x. vector[x$1; x$2])) x)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; wan_nch; LIFT_DROP; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_MUL_DROP_OPEN THEN
  SIMP_TAC[OPEN_UNIV; SMOOTH_MAP_ON_LIFT_COORDINATE] THEN REWRITE_TAC[ETA_AX] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `(:real^2)` THEN
  REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV; STEX_STEREO2_N_INV_SMOOTH] THEN
  MP_TAC(ISPECL [`\x:real^3. vector[x$1; x$2]:real^2`; `vec 0:real^2`] WAN_SMOOTH_AFFINE) THEN
  REWRITE_TAC[WAN_PROJ3_LINEAR; VECTOR_ADD_RID; ETA_AX]);;

let WAN_NCHI_SMOOTH = prove
 (`smooth_map_on {z:real^3 | &1 / &2 < norm z /\ norm z < &2 /\ z$3 < norm z} wan_nchi`,
  ABBREV_TAC `s = {z:real^3 | &1 / &2 < norm z /\ norm z < &2 /\ z$3 < norm z}` THEN
  SUBGOAL_THEN `open (s:real^3->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN REWRITE_TAC[WAN_NCH_OPEN]; ALL_TAC] THEN
  SUBGOAL_THEN `!z:real^3. z IN s ==> ~(z = vec 0) /\ ~(norm z - z$3 = &0)` ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THENL
     [UNDISCH_TAC `&1 / &2 < norm(z:real^3)` THEN ASM_REWRITE_TAC[NORM_0] THEN REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on s (\z:real^3. lift(norm z))` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`s:real^3->bool`; `\z:real^3. z`] SMOOTH_MAP_ON_LIFT_NORM) THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_ID];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on s (\z:real^3. lift(norm z - z$3))` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`s:real^3->bool`; `\z:real^3. lift(norm z)`; `\z:real^3. lift(z$3)`]
                  SMOOTH_MAP_ON_LIFT_SUB) THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_LIFT_COORDINATE; LIFT_DROP];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `wan_nchi`] SMOOTH_MAP_ON_COMPONENTWISE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[DIMINDEX_3] THEN
  REWRITE_TAC[ARITH_RULE `1 <= k /\ k <= 3 <=> k = 1 \/ k = 2 \/ k = 3`] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[wan_nchi; VECTOR_3] THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `\z:real^3. lift(z$k)`; `\z:real^3. lift(norm z - z$3)`]
                SMOOTH_MAP_ON_LIFT_DIV) THEN
  ASM_SIMP_TAC[SMOOTH_MAP_ON_LIFT_COORDINATE; LIFT_DROP; ETA_AX]);;

let WAN_STEREO_THIRD_LT1 = prove
 (`!y:real^2. stereo2_n_inv y$3 < &1 /\ norm(stereo2_n_inv y) = &1`,
  GEN_TAC THEN CONJ_TAC THENL
   [REWRITE_TAC[STEX_STEREO2_N_INV_COMPONENTS] THEN
    MP_TAC(ISPEC `y:real^2` WAN_NORM2_PLUS1_NZ) THEN STRIP_TAC THEN
    ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN REAL_ARITH_TAC;
    MP_TAC(SPEC `y:real^2` STEX_STEREO2_N_INV_IN) THEN
    REWRITE_TAC[IN_DELETE; IN_SPHERE_0] THEN SIMP_TAC[]]);;

let WAN_NCH_NORM = prove
 (`!x:real^3. &0 < x$3
              ==> norm(wan_nch x) = x$3 /\
                  inv(norm(wan_nch x)) % wan_nch x = stereo2_n_inv(vector[x$1; x$2])`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `norm(wan_nch x) = (x:real^3)$3` ASSUME_TAC THENL
   [REWRITE_TAC[wan_nch; NORM_MUL; WAN_STEREO_THIRD_LT1] THEN ASM_REAL_ARITH_TAC;
    ASM_REWRITE_TAC[wan_nch; VECTOR_MUL_ASSOC] THEN
    ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID]]);;

let WAN_NCH_INV = prove
 (`(!x:real^3. &1 / &2 < x$3 /\ x$3 < &2
               ==> wan_nch x IN {z:real^3 | &1 / &2 < norm z /\ norm z < &2 /\ z$3 < norm z} /\
                   wan_nchi(wan_nch x) = x) /\
   (!z:real^3. &1 / &2 < norm z /\ norm z < &2 /\ z$3 < norm z
               ==> wan_nchi z IN {x:real^3 | &1 / &2 < x$3 /\ x$3 < &2} /\
                   wan_nch(wan_nchi z) = z)`,
  CONJ_TAC THENL
   [X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
    MP_TAC(SPEC `x:real^3` WAN_NCH_NORM) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
    MP_TAC(SPEC `vector[(x:real^3)$1; x$2]:real^2` WAN_STEREO_THIRD_LT1) THEN STRIP_TAC THEN
    SUBGOAL_THEN `(wan_nch x)$3 = (x:real^3)$3 * stereo2_n_inv(vector[x$1; x$2])$3`
    ASSUME_TAC THENL
     [REWRITE_TAC[wan_nch; VECTOR_MUL_COMPONENT]; ALL_TAC] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&0 < x /\ x * s < x * &1 ==> x * s < x`) THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(SPEC `vector[(x:real^3)$1; x$2]:real^2` STEX_STEREO2_N_RIGHT) THEN
    REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; STEX_STEREO2_N_COMPONENTS; VECTOR_2] THEN
    STRIP_TAC THEN
    REWRITE_TAC[wan_nchi] THEN ASM_REWRITE_TAC[] THEN
    SIMP_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3] THEN
    REWRITE_TAC[wan_nch; VECTOR_MUL_COMPONENT] THEN
    SUBGOAL_THEN `~(&1 - stereo2_n_inv(vector[(x:real^3)$1; x$2])$3 = &0) /\ ~((x:real^3)$3 = &0)`
    STRIP_ASSUME_TAC THENL [CONJ_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_FIELD `~(x = &0) /\ ~(&1 - s = &0)
                             ==> (x * a) / (x - x * s) = a / (&1 - s)`];
    ALL_TAC] THEN
  X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < norm(z:real^3) /\ ~(norm z - z$3 = &0)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [REWRITE_TAC[IN_ELIM_THM; wan_nchi; VECTOR_3] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `inv(norm z) % (z:real^3) IN sphere(vec 0:real^3,&1) DELETE basis 3`
  ASSUME_TAC THENL
   [REWRITE_TAC[IN_DELETE; IN_SPHERE_0; NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM] THEN
    ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ] THEN
    DISCH_THEN(MP_TAC o AP_TERM `\v:real^3. v$3`) THEN
    SIMP_TAC[VECTOR_MUL_COMPONENT; BASIS_COMPONENT; DIMINDEX_3; ARITH] THEN
    ASM_SIMP_TAC[REAL_FIELD `&0 < n ==> (inv n * a = &1 <=> a = n)`] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(&1 - inv(norm z) * (z:real^3)$3 = &0)` ASSUME_TAC THENL
   [SUBGOAL_THEN `&1 - inv(norm z) * (z:real^3)$3 = (norm z - z$3) / norm z` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < norm(z:real^3)` THEN CONV_TAC REAL_FIELD;
      ASM_SIMP_TAC[REAL_DIV_EQ_0; REAL_LT_IMP_NZ]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `vector[(z:real^3)$1 / (norm z - z$3); z$2 / (norm z - z$3)]:real^2 =
    stereo2_n(inv(norm z) % z)`
  ASSUME_TAC THENL
   [REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; STEX_STEREO2_N_COMPONENTS; VECTOR_2;
                VECTOR_MUL_COMPONENT] THEN
    CONJ_TAC THEN
    MAP_EVERY UNDISCH_TAC [`&0 < norm(z:real^3)`; `~(norm(z:real^3) - z$3 = &0)`;
                           `~(&1 - inv(norm z) * (z:real^3)$3 = &0)`] THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  REWRITE_TAC[wan_nch; wan_nchi; VECTOR_3] THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[STEX_STEREO2_N_LEFT] THEN
  ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_RINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID]);;

let WAN_NCH_IMAGE = prove
 (`IMAGE wan_nch {x:real^3 | &1 / &2 < x$3 /\ x$3 < &2} =
   {z:real^3 | &1 / &2 < norm z /\ norm z < &2 /\ z$3 < norm z}`,
  REWRITE_TAC[EXTENSION; IN_IMAGE] THEN X_GEN_TAC `z:real^3` THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `x:real^3` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(CONJUNCT1 WAN_NCH_INV) THEN DISCH_THEN(MP_TAC o SPEC `x:real^3`) THEN
    UNDISCH_TAC `(x:real^3) IN {x | &1 / &2 < x$3 /\ x$3 < &2}` THEN
    REWRITE_TAC[IN_ELIM_THM] THEN SIMP_TAC[];
    REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN EXISTS_TAC `wan_nchi z` THEN
    MP_TAC(CONJUNCT2 WAN_NCH_INV) THEN DISCH_THEN(MP_TAC o SPEC `z:real^3`) THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN SIMP_TAC[]]);;

let WAN_SHELL_NCH = prove
 (`{z:real^3 | &1 / &2 < norm z /\ norm z < &2 /\ z$3 < norm z} SUBSET wan_shell /\
   negligible(wan_shell DIFF {z:real^3 | &1 / &2 < norm z /\ norm z < &2 /\ z$3 < norm z})`,
  CONJ_TAC THENL [REWRITE_TAC[wan_shell] THEN SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN EXISTS_TAC `{z:real^3 | z$1 = &0}` THEN
  REWRITE_TAC[NEGLIGIBLE_STANDARD_HYPERPLANE] THEN
  REWRITE_TAC[SUBSET; wan_shell; IN_DIFF; IN_ELIM_THM] THEN X_GEN_TAC `z:real^3` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `norm(z:real^3) <= z$3` ASSUME_TAC THENL [ASM_MESON_TAC[REAL_NOT_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `norm(z:real^3) pow 2 <= (z$3) pow 2` MP_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[NORM_POS_LE]; ALL_TAC] THEN
  REWRITE_TAC[NORM_POW_2; DOT_3] THEN
  MP_TAC(SPEC `(z:real^3)$2` REAL_LE_SQUARE) THEN
  MP_TAC(SPEC `(z:real^3)$1` REAL_LE_SQUARE) THEN
  REWRITE_TAC[REAL_POW_2] THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `(z:real^3)$1 * z$1 = &0` MP_TAC THENL
   [ASM_REAL_ARITH_TAC; REWRITE_TAC[REAL_ENTIRE]]);;

let WAN_REXT_NCH = prove
 (`!(u:real^3->real^K) x.
     &0 < x$3 ==> wan_rext u (wan_nch x) = u(stereo2_n_inv(vector[x$1; x$2]))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[wan_rext] THEN ASM_SIMP_TAC[WAN_NCH_NORM]);;

(* ------------------------------------------------------------------------- *)
(* Derivatives of the north chart: the columns of D wan_nch are x3 S_1,     *)
(* x3 S_2 and sigma, pairwise orthogonal with lengths x3 lam, x3 lam, 1     *)
(* (lam = 2 / (|y|^2 + 1)); |det| = (x3 lam)^2; the derivative of the       *)
(* inverse chart is the transpose scaled by the inverse squared lengths.    *)
(* ------------------------------------------------------------------------- *)

let WAN_BASIS3_PROJ = prove
 (`(vector[(basis 1:real^3)$1; (basis 1:real^3)$2]:real^2) = basis 1 /\
   (vector[(basis 2:real^3)$1; (basis 2:real^3)$2]:real^2) = basis 2 /\
   (vector[(basis 3:real^3)$1; (basis 3:real^3)$2]:real^2) = vec 0 /\
   (basis 1:real^3)$3 = &0 /\ (basis 2:real^3)$3 = &0 /\ (basis 3:real^3)$3 = &1`,
  SIMP_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2; BASIS_COMPONENT; DIMINDEX_3; ARITH;
           VEC_COMPONENT]);;

let WAN_COLUMN_MATRIX = prove
 (`!(f:real^M->real^N) j.
     1 <= j /\ j <= dimindex(:M) ==> column j (matrix f) = f(basis j)`,
  SIMP_TAC[column; CART_EQ; LAMBDA_BETA; MATRIX_COMPONENT]);;

let WAN_NCH_DERIV = prove
 (`!x:real^3.
     (wan_nch has_derivative
      (\h. x$3 % frechet_derivative stereo2_n_inv (at (vector[x$1; x$2])) (vector[h$1; h$2]) +
           h$3 % stereo2_n_inv(vector[x$1; x$2]))) (at x)`,
  GEN_TAC THEN
  SUBGOAL_THEN `wan_nch = (\x:real^3. x$3 % stereo2_n_inv(vector[x$1; x$2]))` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; wan_nch]; ALL_TAC] THEN
  MP_TAC(ISPECL [`\x:real^3. x$3`; `\h:real^3. h$3`;
                 `stereo2_n_inv o (\x:real^3. vector[x$1; x$2]:real^2)`;
                 `frechet_derivative stereo2_n_inv (at (vector[(x:real^3)$1; x$2])) o
                  (\h:real^3. vector[h$1; h$2]:real^2)`;
                 `x:real^3`] HAS_DERIVATIVE_MUL_AT) THEN
  REWRITE_TAC[o_THM] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
   [REWRITE_TAC[o_DEF] THEN MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN
    REWRITE_TAC[WAN_PROJ3_LINEAR];
    MATCH_MP_TAC DIFF_CHAIN_AT THEN CONJ_TAC THENL
     [MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN REWRITE_TAC[WAN_PROJ3_LINEAR];
      REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `(:real^2)` THEN
      REWRITE_TAC[OPEN_UNIV; IN_UNIV; STEX_STEREO2_N_INV_SMOOTH]]]);;

let WAN_NCH_COLS = prove
 (`!x:real^3.
     frechet_derivative wan_nch (at x) (basis 1) =
       x$3 % frechet_derivative stereo2_n_inv (at (vector[x$1; x$2])) (basis 1) /\
     frechet_derivative wan_nch (at x) (basis 2) =
       x$3 % frechet_derivative stereo2_n_inv (at (vector[x$1; x$2])) (basis 2) /\
     frechet_derivative wan_nch (at x) (basis 3) = stereo2_n_inv(vector[x$1; x$2])`,
  GEN_TAC THEN
  MP_TAC(SPEC `x:real^3` WAN_NCH_DERIV) THEN
  DISCH_THEN(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
  REWRITE_TAC[WAN_BASIS3_PROJ; VECTOR_MUL_LZERO; VECTOR_ADD_RID; VECTOR_MUL_LID] THEN
  MP_TAC(ISPEC `frechet_derivative stereo2_n_inv (at (vector[(x:real^3)$1; x$2]))` LINEAR_0) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `(:real^2)` THEN
    REWRITE_TAC[OPEN_UNIV; IN_UNIV; STEX_STEREO2_N_INV_SMOOTH];
    SIMP_TAC[VECTOR_MUL_RZERO; VECTOR_ADD_LID]]);;

let WAN_NCH_ORTHO = prove
 (`!x:real^3.
     let a1 = frechet_derivative wan_nch (at x) (basis 1)
     and a2 = frechet_derivative wan_nch (at x) (basis 2)
     and a3 = frechet_derivative wan_nch (at x) (basis 3)
     and n = x$3 * &2 / (norm(vector[x$1; x$2]:real^2) pow 2 + &1) in
     a1 dot a1 = n pow 2 /\ a2 dot a2 = n pow 2 /\ a3 dot a3 = &1 /\
     a1 dot a2 = &0 /\ a2 dot a1 = &0 /\ a1 dot a3 = &0 /\ a3 dot a1 = &0 /\
     a2 dot a3 = &0 /\ a3 dot a2 = &0`,
  GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[WAN_NCH_COLS; DOT_LMUL; DOT_RMUL] THEN
  MP_TAC(SPEC `vector[(x:real^3)$1; x$2]:real^2` WAN_STEREO_CONFORMAL) THEN
  ABBREV_TAC `S1 = frechet_derivative stereo2_n_inv (at (vector[(x:real^3)$1; x$2])) (basis 1)` THEN
  ABBREV_TAC `S2 = frechet_derivative stereo2_n_inv (at (vector[(x:real^3)$1; x$2])) (basis 2)` THEN
  ABBREV_TAC `s = stereo2_n_inv (vector[(x:real^3)$1; x$2])` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `(S2:real^3) dot S1 = &0 /\ (S1:real^3) dot s = &0 /\ (S2:real^3) dot s = &0`
  STRIP_ASSUME_TAC THENL [ONCE_REWRITE_TAC[DOT_SYM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN CONV_TAC REAL_RING);;

let WAN_NCH_DET = prove
 (`!x:real^3. abs(det(jacobian wan_nch (at x))) =
              (x$3 * &2 / (norm(vector[x$1; x$2]:real^2) pow 2 + &1)) pow 2`,
  GEN_TAC THEN
  SUBGOAL_THEN
   `det(jacobian wan_nch (at x)) pow 2 =
    (((x:real^3)$3 * &2 / (norm(vector[x$1; x$2]:real^2) pow 2 + &1)) pow 2) pow 2`
  MP_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [REAL_POW_2] THEN
    GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [GSYM DET_TRANSP] THEN
    REWRITE_TAC[GSYM DET_MUL; MATRIX_MUL_LTRANSP_DOT_COLUMN] THEN
    SIMP_TAC[DET_3; LAMBDA_BETA; DIMINDEX_3; ARITH; jacobian; WAN_COLUMN_MATRIX] THEN
    MP_TAC(SPEC `x:real^3` WAN_NCH_ORTHO) THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RING;
    REWRITE_TAC[GSYM REAL_EQ_SQUARE_ABS; REAL_ABS_POW; REAL_POW2_ABS] THEN SIMP_TAC[]]);;

let WAN_ORTHO3_INVERSE = prove
 (`!(L:real^3->real^3) w j.
     linear L /\ L w = basis j /\ 1 <= j /\ j <= 3 /\
     L(basis 1) dot L(basis 2) = &0 /\ L(basis 1) dot L(basis 3) = &0 /\
     L(basis 2) dot L(basis 3) = &0 /\
     ~(L(basis 1) dot L(basis 1) = &0) /\ ~(L(basis 2) dot L(basis 2) = &0) /\
     ~(L(basis 3) dot L(basis 3) = &0)
     ==> !i. 1 <= i /\ i <= 3 ==> w$i = L(basis i)$j / (L(basis i) dot L(basis i))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(w:real^3)$1 % (L:real^3->real^3)(basis 1) + w$2 % L(basis 2) + w$3 % L(basis 3) =
    basis j`
  (LABEL_TAC "C") THENL
   [UNDISCH_TAC `(L:real^3->real^3) w = basis j` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    SUBGOAL_THEN `(w:real^3) = w$1 % basis 1 + w$2 % basis 2 + w$3 % basis 3`
    (fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [th]) THENL
     [SIMP_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
               BASIS_COMPONENT; ARITH] THEN REAL_ARITH_TAC;
      ASM_SIMP_TAC[LINEAR_ADD; LINEAR_CMUL]];
    ALL_TAC] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(L:real^3->real^3)(basis i)$j = L(basis i) dot basis j` SUBST1_TAC THENL
   [ASM_SIMP_TAC[DOT_BASIS; DIMINDEX_3]; ALL_TAC] THEN
  REMOVE_THEN "C" (SUBST1_TAC o SYM) THEN
  REWRITE_TAC[DOT_RADD; DOT_RMUL] THEN
  SUBGOAL_THEN
   `(L:real^3->real^3)(basis 2) dot L(basis 1) = &0 /\ L(basis 3) dot L(basis 1) = &0 /\
    L(basis 3) dot L(basis 2) = &0`
  STRIP_ASSUME_TAC THENL [ONCE_REWRITE_TAC[DOT_SYM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `1 <= i /\ i <= 3` THEN
  REWRITE_TAC[ARITH_RULE `1 <= i /\ i <= 3 <=> i = 1 \/ i = 2 \/ i = 3`] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[REAL_MUL_RZERO; REAL_ADD_LID; REAL_ADD_RID] THEN
  ASM_SIMP_TAC[REAL_FIELD `~(a = &0) ==> w = (w * a) / a`]);;

let WAN_NCH_FACTS = prove
 (`(!x:real^3. (wan_nch has_derivative frechet_derivative wan_nch (at x)) (at x) /\
               linear(frechet_derivative wan_nch (at x))) /\
   (!z:real^3. z IN {z:real^3 | &1 / &2 < norm z /\ norm z < &2 /\ z$3 < norm z}
               ==> (wan_nchi has_derivative frechet_derivative wan_nchi (at z)) (at z)) /\
   continuously_differentiable 1 (:real^3) wan_nch /\
   continuously_differentiable 1 {x:real^3 | &1 / &2 < x$3 /\ x$3 < &2} wan_nch /\
   continuously_differentiable 1
     {z:real^3 | &1 / &2 < norm z /\ norm z < &2 /\ z$3 < norm z} wan_nchi`,
  REPEAT CONJ_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
     [REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `(:real^3)` THEN
      REWRITE_TAC[OPEN_UNIV; IN_UNIV; WAN_NCH_SMOOTH];
      MESON_TAC[has_derivative]];
    REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `{z:real^3 | &1 / &2 < norm z /\ norm z < &2 /\ z$3 < norm z}` THEN
    ASM_REWRITE_TAC[WAN_NCH_OPEN; WAN_NCHI_SMOOTH];
    MP_TAC WAN_NCH_SMOOTH THEN REWRITE_TAC[smooth_map_on] THEN SIMP_TAC[];
    MP_TAC(ISPECL [`(:real^3)`; `{x:real^3 | &1 / &2 < x$3 /\ x$3 < &2}`; `wan_nch`]
                  SMOOTH_MAP_ON_SUBSET) THEN
    REWRITE_TAC[SUBSET_UNIV; WAN_NCH_SMOOTH; smooth_map_on] THEN SIMP_TAC[];
    MP_TAC WAN_NCHI_SMOOTH THEN REWRITE_TAC[smooth_map_on] THEN SIMP_TAC[]]);;

let WAN_NCHI_COEFF = prove
 (`!z:real^3 i j.
     z IN {z:real^3 | &1 / &2 < norm z /\ norm z < &2 /\ z$3 < norm z} /\
     1 <= i /\ i <= 3 /\ 1 <= j /\ j <= 3
     ==> (frechet_derivative wan_nchi (at z) (basis j))$i =
         (frechet_derivative wan_nch (at (wan_nchi z)) (basis i))$j /
         (frechet_derivative wan_nch (at (wan_nchi z)) (basis i) dot
          frechet_derivative wan_nch (at (wan_nchi z)) (basis i))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `x = wan_nchi z` THEN
  SUBGOAL_THEN `&1 / &2 < (x:real^3)$3 /\ x$3 < &2` STRIP_ASSUME_TAC THENL
   [MP_TAC(CONJUNCT2 WAN_NCH_INV) THEN DISCH_THEN(MP_TAC o SPEC `z:real^3`) THEN
    UNDISCH_TAC `z IN {z:real^3 | &1 / &2 < norm z /\ norm z < &2 /\ z$3 < norm z}` THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPEC `x:real^3` WAN_NCH_ORTHO) THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  STRIP_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_IMP; RIGHT_IMP_FORALL_THM] WAN_ORTHO3_INVERSE) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(((x:real^3)$3 * &2 / (norm(vector[x$1; x$2]:real^2) pow 2 + &1)) pow 2 = &0)`
  ASSUME_TAC THENL
   [REWRITE_TAC[REAL_POW_EQ_0; ARITH] THEN
    MP_TAC(ISPEC `vector[(x:real^3)$1; x$2]:real^2` WAN_NORM2_PLUS1_NZ) THEN
    STRIP_TAC THEN
    MATCH_MP_TAC REAL_LT_IMP_NZ THEN MATCH_MP_TAC REAL_LT_MUL THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[REAL_OF_NUM_EQ; ARITH] THEN
  REWRITE_TAC[ETA_AX; WAN_NCH_FACTS] THEN
  SUBGOAL_THEN
   `(frechet_derivative wan_nch (at x) o frechet_derivative wan_nchi (at z)) =
    (\h:real^3. h)`
  (fun th -> REWRITE_TAC[REWRITE_RULE[FUN_EQ_THM; o_THM] th]) THEN
  MATCH_MP_TAC FRECHET_DERIVATIVE_UNIQUE_AT THEN
  EXISTS_TAC `\h:real^3. h` THEN EXISTS_TAC `z:real^3` THEN
  REWRITE_TAC[HAS_DERIVATIVE_ID] THEN
  MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_AT THEN
  EXISTS_TAC `wan_nch o wan_nchi` THEN
  MP_TAC(CONJUNCT2 WAN_NCH_OPEN) THEN REWRITE_TAC[OPEN_CONTAINS_BALL] THEN
  DISCH_THEN(MP_TAC o SPEC `z:real^3`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN
    SUBGOAL_THEN
     `(w:real^3) IN {z:real^3 | &1 / &2 < norm z /\ norm z < &2 /\ z$3 < norm z}`
    MP_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
      REWRITE_TAC[IN_BALL] THEN ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
    MP_TAC(CONJUNCT2 WAN_NCH_INV) THEN DISCH_THEN(MP_TAC o SPEC `w:real^3`) THEN
    ASM_SIMP_TAC[];
    MATCH_MP_TAC DIFF_CHAIN_AT THEN ASM_SIMP_TAC[WAN_NCH_FACTS]]);;

(* ------------------------------------------------------------------------- *)
(* Parseval identities for an orthogonal (not normalized) triple in real^3, *)
(* and their vector-valued forms used for the Dirichlet integrands.         *)
(* ------------------------------------------------------------------------- *)

let WAN_ORTHO3_COMPLETE = prove
 (`!(a1:real^3) a2 a3 v.
     a1 dot a2 = &0 /\ a1 dot a3 = &0 /\ a2 dot a3 = &0 /\
     ~(a1 dot a1 = &0) /\ ~(a2 dot a2 = &0) /\ ~(a3 dot a3 = &0)
     ==> (a1 dot v) pow 2 / (a1 dot a1) + (a2 dot v) pow 2 / (a2 dot a2) +
         (a3 dot v) pow 2 / (a3 dot a3) = v dot v`,
  REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "H") THEN
  SUBGOAL_THEN
   `(vector[inv(a1 dot a1) % a1; inv(a2 dot a2) % a2; inv(a3 dot a3) % a3]:real^3^3) **
    transp(vector[a1; a2; a3]:real^3^3) = mat 1`
  (LABEL_TAC "QM") THENL
   [SIMP_TAC[CART_EQ; DIMINDEX_3; FORALL_3; matrix_mul; transp; mat; LAMBDA_BETA; ARITH;
             SUM_3; VECTOR_3; VECTOR_MUL_COMPONENT] THEN
    USE_THEN "H" MP_TAC THEN REWRITE_TAC[DOT_3] THEN DISCH_TAC THEN
    REPEAT CONJ_TAC THEN POP_ASSUM MP_TAC THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `transp(vector[a1; a2; a3]:real^3^3) **
    (vector[inv(a1 dot a1) % a1; inv(a2 dot a2) % a2; inv(a3 dot a3) % a3]:real^3^3) =
    mat 1`
  (LABEL_TAC "MQ") THENL
   [ONCE_REWRITE_TAC[MATRIX_LEFT_RIGHT_INVERSE] THEN USE_THEN "QM" ACCEPT_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `(v:real^3) = transp(vector[a1; a2; a3]:real^3^3) **
                 ((vector[inv(a1 dot a1) % a1; inv(a2 dot a2) % a2;
                          inv(a3 dot a3) % a3]:real^3^3) ** v)`
  (fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [th]) THENL
   [USE_THEN "MQ" (fun th -> REWRITE_TAC[MATRIX_VECTOR_MUL_ASSOC; th; MATRIX_VECTOR_MUL_LID]);
    ALL_TAC] THEN
  REWRITE_TAC[DOT_MATRIX_TRANSP_RMUL] THEN GEN_REWRITE_TAC RAND_CONV [DOT_3] THEN
  SIMP_TAC[MATRIX_VECTOR_MUL_COMPONENT; DIMINDEX_3; ARITH; VECTOR_3; DOT_LMUL] THEN
  REWRITE_TAC[real_div] THEN CONV_TAC REAL_RING);;

let WAN_ORTHO3_SUMSQ = prove
 (`!(a1:real^3) a2 a3 t1 t2 t3.
     a1 dot a2 = &0 /\ a1 dot a3 = &0 /\ a2 dot a3 = &0
     ==> (t1 % a1 + t2 % a2 + t3 % a3) dot (t1 % a1 + t2 % a2 + t3 % a3) =
         t1 pow 2 * (a1 dot a1) + t2 pow 2 * (a2 dot a2) + t3 pow 2 * (a3 dot a3)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[DOT_LADD; DOT_RADD; DOT_LMUL; DOT_RMUL] THEN
  ONCE_REWRITE_TAC[DOT_SYM] THEN ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[DOT_SYM] THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let WAN_NORM_POW2_SUM = prove
 (`!x:real^K. norm x pow 2 = sum(1..dimindex(:K)) (\k. x$k pow 2)`,
  REWRITE_TAC[NORM_POW_2; dot; REAL_POW_2]);;

let WAN_PARSEVAL3_VEC = prove
 (`!(A:num->real^3) (V:num->real^K).
     A 1 dot A 2 = &0 /\ A 1 dot A 3 = &0 /\ A 2 dot A 3 = &0 /\
     ~(A 1 dot A 1 = &0) /\ ~(A 2 dot A 2 = &0) /\ ~(A 3 dot A 3 = &0)
     ==> sum(1..3) (\i. norm(vsum(1..3) (\j. A i$j % V j)) pow 2 / (A i dot A i)) =
         sum(1..3) (\j. norm(V j) pow 2)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[WAN_NORM_POW2_SUM; real_div; GSYM SUM_RMUL] THEN
  REWRITE_TAC[SUM_3] THEN REWRITE_TAC[GSYM SUM_ADD_NUMSEG] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
  ASM_SIMP_TAC[VSUM_COMPONENT; VECTOR_MUL_COMPONENT; SUM_3] THEN
  FIRST_ASSUM(MP_TAC o SPEC `vector[(V:num->real^K) 1$k; V 2$k; V 3$k]:real^3` o
    MATCH_MP WAN_ORTHO3_COMPLETE) THEN
  REWRITE_TAC[DOT_3; VECTOR_3; real_div] THEN CONV_TAC REAL_RING);;

let WAN_PARSEVAL3_VEC_INV = prove
 (`!(A:num->real^3) (G:num->real^K).
     A 1 dot A 2 = &0 /\ A 1 dot A 3 = &0 /\ A 2 dot A 3 = &0 /\
     ~(A 1 dot A 1 = &0) /\ ~(A 2 dot A 2 = &0) /\ ~(A 3 dot A 3 = &0)
     ==> sum(1..3) (\j. norm(vsum(1..3) (\i. (A i$j / (A i dot A i)) % G i)) pow 2) =
         sum(1..3) (\i. norm(G i) pow 2 / (A i dot A i))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[WAN_NORM_POW2_SUM; real_div; GSYM SUM_RMUL] THEN
  REWRITE_TAC[SUM_3] THEN REWRITE_TAC[GSYM SUM_ADD_NUMSEG] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
  ASM_SIMP_TAC[VSUM_COMPONENT; VECTOR_MUL_COMPONENT; SUM_3] THEN
  FIRST_ASSUM(MP_TAC o SPECL
   [`(G:num->real^K) 1$k * inv(A 1 dot (A:num->real^3) 1)`;
    `(G:num->real^K) 2$k * inv(A 2 dot (A:num->real^3) 2)`;
    `(G:num->real^K) 3$k * inv(A 3 dot (A:num->real^3) 3)`] o
    MATCH_MP WAN_ORTHO3_SUMSQ o
    (fun th -> CONJ (CONJUNCT1 th) (CONJ (CONJUNCT1(CONJUNCT2 th))
                                         (CONJUNCT1(CONJUNCT2(CONJUNCT2 th)))))) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[DOT_3; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
  REPEAT(POP_ASSUM MP_TAC) THEN REWRITE_TAC[DOT_3] THEN CONV_TAC REAL_FIELD);;

(* ------------------------------------------------------------------------- *)
(* Integration tools for the chart: the Jacobian factor wan_nchj, change of *)
(* variables between the slab and the shell, pointwise Parseval relations   *)
(* for the chain-rule partials, L^1_loc measurability, Dirichlet integrals  *)
(* from L^2 weak partials, and slab integrals of functions of (x1,x2).      *)
(* ------------------------------------------------------------------------- *)

let wan_nchj = new_definition
 `wan_nchj (x:real^3) = (x$3 * &2 / (norm(vector[x$1; x$2]:real^2) pow 2 + &1)) pow 2`;;

let WAN_NCHJ_POS = prove
 (`!x:real^3. &0 < x$3 ==> &0 < wan_nchj x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[wan_nchj] THEN
  MATCH_MP_TAC REAL_POW_LT THEN MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LT_DIV THEN REWRITE_TAC[WAN_NORM2_PLUS1_NZ] THEN REAL_ARITH_TAC);;

let WAN_NCH_DETJ = prove
 (`!x:real^3. abs(det(jacobian wan_nch (at x))) = wan_nchj x`,
  REWRITE_TAC[wan_nchj; WAN_NCH_DET]);;

let WAN_NCH_COV = prove
 (`!(q:real^3->real^K).
     (q absolutely_integrable_on
        {z:real^3 | &1 / &2 < norm z /\ norm z < &2 /\ z$3 < norm z} <=>
      (\x. wan_nchj x % q(wan_nch x)) absolutely_integrable_on
        {x:real^3 | &1 / &2 < x$3 /\ x$3 < &2}) /\
     (q absolutely_integrable_on
        {z:real^3 | &1 / &2 < norm z /\ norm z < &2 /\ z$3 < norm z}
      ==> integral {z:real^3 | &1 / &2 < norm z /\ norm z < &2 /\ z$3 < norm z} q =
          integral {x:real^3 | &1 / &2 < x$3 /\ x$3 < &2} (\x. wan_nchj x % q(wan_nch x)))`,
  GEN_TAC THEN
  MP_TAC(ISPECL [`{x:real^3 | &1 / &2 < x$3 /\ x$3 < &2}`; `wan_nch`; `wan_nchi`;
                 `\x:real^3. (q:real^3->real^K)(wan_nch x)`] WAN_COV_COMPOSE) THEN
  REWRITE_TAC[WAN_NCH_IMAGE; WAN_NCH_DETJ] THEN ANTS_TAC THENL
   [SIMP_TAC[LEBESGUE_MEASURABLE_OPEN; WAN_NCH_OPEN; WAN_NCH_FACTS] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[WAN_NCH_INV];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z:real^3. z IN {z:real^3 | &1 / &2 < norm z /\ norm z < &2 /\ z$3 < norm z}
               ==> (q:real^3->real^K)(wan_nch(wan_nchi z)) = q z`
  ASSUME_TAC THENL [REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[WAN_NCH_INV]; ALL_TAC] THEN
  SUBGOAL_THEN
   `((\z. (q:real^3->real^K)(wan_nch(wan_nchi z))) absolutely_integrable_on
       {z:real^3 | &1 / &2 < norm z /\ norm z < &2 /\ z$3 < norm z} <=>
     q absolutely_integrable_on
       {z:real^3 | &1 / &2 < norm z /\ norm z < &2 /\ z$3 < norm z}) /\
    integral {z:real^3 | &1 / &2 < norm z /\ norm z < &2 /\ z$3 < norm z}
      (\z. q(wan_nch(wan_nchi z))) =
    integral {z:real^3 | &1 / &2 < norm z /\ norm z < &2 /\ z$3 < norm z} q`
  (fun th -> REWRITE_TAC[th]) THEN CONJ_TAC THENL
   [EQ_TAC THEN DISCH_TAC THEN MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_EQ THENL
     [EXISTS_TAC `\z. (q:real^3->real^K)(wan_nch(wan_nchi z))`;
      EXISTS_TAC `q:real^3->real^K`] THEN
    ASM_SIMP_TAC[];
    MATCH_MP_TAC INTEGRAL_EQ THEN ASM_SIMP_TAC[]]);;

let WAN_NCH_ORTHO_HYP = prove
 (`!x:real^3.
     &0 < x$3
     ==> frechet_derivative wan_nch (at x) (basis 1) dot
         frechet_derivative wan_nch (at x) (basis 2) = &0 /\
         frechet_derivative wan_nch (at x) (basis 1) dot
         frechet_derivative wan_nch (at x) (basis 3) = &0 /\
         frechet_derivative wan_nch (at x) (basis 2) dot
         frechet_derivative wan_nch (at x) (basis 3) = &0 /\
         ~(frechet_derivative wan_nch (at x) (basis 1) dot
           frechet_derivative wan_nch (at x) (basis 1) = &0) /\
         ~(frechet_derivative wan_nch (at x) (basis 2) dot
           frechet_derivative wan_nch (at x) (basis 2) = &0) /\
         ~(frechet_derivative wan_nch (at x) (basis 3) dot
           frechet_derivative wan_nch (at x) (basis 3) = &0) /\
         frechet_derivative wan_nch (at x) (basis 1) dot
         frechet_derivative wan_nch (at x) (basis 1) = wan_nchj x /\
         frechet_derivative wan_nch (at x) (basis 2) dot
         frechet_derivative wan_nch (at x) (basis 2) = wan_nchj x /\
         frechet_derivative wan_nch (at x) (basis 3) dot
         frechet_derivative wan_nch (at x) (basis 3) = &1`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPEC `x:real^3` WAN_NCH_ORTHO) THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[GSYM wan_nchj] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPEC `x:real^3` WAN_NCHJ_POS) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let WAN_NCH_PARSEVAL = prove
 (`!(x:real^3) (V:num->real^K).
     &0 < x$3
     ==> norm(vsum(1..3) (\j. frechet_derivative wan_nch (at x) (basis 1)$j % V j)) pow 2 +
         norm(vsum(1..3) (\j. frechet_derivative wan_nch (at x) (basis 2)$j % V j)) pow 2 +
         wan_nchj x *
         norm(vsum(1..3) (\j. frechet_derivative wan_nch (at x) (basis 3)$j % V j)) pow 2 =
         wan_nchj x * sum(1..3) (\j. norm(V j) pow 2)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPEC `x:real^3` WAN_NCH_ORTHO_HYP) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPEC `x:real^3` WAN_NCHJ_POS) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`\i. frechet_derivative wan_nch (at (x:real^3)) (basis i)`;
                 `V:num->real^K`] WAN_PARSEVAL3_VEC) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  ASM_REWRITE_TAC[SUM_3] THEN UNDISCH_TAC `&0 < wan_nchj x` THEN
  CONV_TAC REAL_FIELD);;

let WAN_NCHI_PARSEVAL = prove
 (`!(z:real^3) (G:num->real^K).
     z IN {z:real^3 | &1 / &2 < norm z /\ norm z < &2 /\ z$3 < norm z}
     ==> sum(1..3) (\j. norm(vsum(1..3)
                     (\i. (frechet_derivative wan_nchi (at z) (basis j))$i % G i)) pow 2) =
         (norm(G 1) pow 2 + norm(G 2) pow 2) / wan_nchj(wan_nchi z) + norm(G 3) pow 2`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `&1 / &2 < (wan_nchi z)$3 /\ (wan_nchi z)$3 < &2` STRIP_ASSUME_TAC THENL
   [MP_TAC(CONJUNCT2 WAN_NCH_INV) THEN DISCH_THEN(MP_TAC o SPEC `z:real^3`) THEN
    UNDISCH_TAC `z IN {z:real^3 | &1 / &2 < norm z /\ norm z < &2 /\ z$3 < norm z}` THEN
    REWRITE_TAC[IN_ELIM_THM] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (wan_nchi z)$3` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPEC `wan_nchi z` WAN_NCH_ORTHO_HYP) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!j. 1 <= j /\ j <= 3
        ==> vsum(1..3) (\i. (frechet_derivative wan_nchi (at z) (basis j))$i % (G:num->real^K) i) =
            vsum(1..3) (\i. ((frechet_derivative wan_nch (at (wan_nchi z)) (basis i))$j /
                             (frechet_derivative wan_nch (at (wan_nchi z)) (basis i) dot
                              frechet_derivative wan_nch (at (wan_nchi z)) (basis i))) % G i)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC VSUM_EQ_NUMSEG THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC WAN_NCHI_COEFF THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum(1..3) (\j. norm(vsum(1..3)
                     (\i. (frechet_derivative wan_nchi (at z) (basis j))$i % (G:num->real^K) i)) pow 2) =
    sum(1..3) (\j. norm(vsum(1..3)
                     (\i. ((frechet_derivative wan_nch (at (wan_nchi z)) (basis i))$j /
                           (frechet_derivative wan_nch (at (wan_nchi z)) (basis i) dot
                            frechet_derivative wan_nch (at (wan_nchi z)) (basis i))) % G i)) pow 2)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`\i. frechet_derivative wan_nch (at (wan_nchi z)) (basis i)`;
                 `G:num->real^K`] WAN_PARSEVAL3_VEC_INV) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  ASM_REWRITE_TAC[SUM_3] THEN REAL_ARITH_TAC);;

let WAN_LLOC_MEASURABLE = prove
 (`!(s:real^N->bool) (f:real^N->real^K). open s /\ wan_lloc s f ==> f measurable_on s`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP OPEN_UNION_COMPACT_SUBSETS) THEN
  DISCH_THEN(X_CHOOSE_THEN `c:num->real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `s = UNIONS {(c:num->real^N->bool) n | n IN (:num)}` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC MEASURABLE_ON_COUNTABLE_UNIONS THEN CONJ_TAC THENL
   [REWRITE_TAC[SIMPLE_IMAGE] THEN MATCH_MP_TAC COUNTABLE_IMAGE THEN
    REWRITE_TAC[NUM_COUNTABLE];
    REWRITE_TAC[FORALL_IN_GSPEC; IN_UNIV] THEN X_GEN_TAC `n:num` THEN
    UNDISCH_TAC `wan_lloc s (f:real^N->real^K)` THEN REWRITE_TAC[wan_lloc] THEN
    DISCH_THEN(MP_TAC o SPEC `(c:num->real^N->bool) n`) THEN
    ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_MEASURABLE]]);;

let WAN_WD_SELECT = prove
 (`!(s:real^N->bool) i (u:real^N->real^K) v.
     v IN lspace s (&2) /\ wan_wpd s i u v
     ==> wan_wd s i u IN lspace s (&2) /\ wan_wpd s i u (wan_wd s i u)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`\w:real^N->real^K. w IN lspace s (&2) /\ wan_wpd s i u w`;
                 `v:real^N->real^K`] SELECT_AX) THEN
  ASM_REWRITE_TAC[GSYM wan_wd]);;

let WAN_DIR_EQ_L2 = prove
 (`!(s:real^N->bool) (u:real^N->real^K) v.
     open s /\
     (!i. 1 <= i /\ i <= dimindex(:N) ==> v i IN lspace s (&2) /\ wan_wpd s i u (v i))
     ==> wan_dir s u =
         sum(1..dimindex(:N)) (\i. drop(integral s (\x. lift(norm(v i x) pow 2))))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[wan_dir] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  REWRITE_TAC[] THEN AP_TERM_TAC THEN MATCH_MP_TAC INTEGRAL_SPIKE THEN
  EXISTS_TAC `{x | x IN s /\ ~(wan_wd s i (u:real^N->real^K) x = v i x)}` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC WAN_WPD_UNIQUE THEN MAP_EVERY EXISTS_TAC [`i:num`; `u:real^N->real^K`] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`s:real^N->bool`; `i:num`; `u:real^N->real^K`;
                   `(v:num->real^N->real^K) i`] WAN_WD_SELECT) THEN
    ASM_SIMP_TAC[ETA_AX];
    REWRITE_TAC[IN_DIFF; IN_ELIM_THM] THEN MESON_TAC[]]);;

let WAN_INTERVAL1_INDICATOR = prove
 (`!a b (c:real^K).
     a < b
     ==> ((\r:real^1. if a < drop r /\ drop r < b then c else vec 0) has_integral
          ((b - a) % c)) (:real^1)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\r:real^1. if a < drop r /\ drop r < b then (c:real^K) else vec 0) =
                (\r. if r IN interval(lift a,lift b) then c else vec 0)` SUBST1_TAC THENL
   [REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP]; ALL_TAC] THEN
  REWRITE_TAC[HAS_INTEGRAL_RESTRICT_UNIV; HAS_INTEGRAL_OPEN_INTERVAL] THEN
  SUBGOAL_THEN `b - a = content(interval[lift a,lift b])` SUBST1_TAC THENL
   [ASM_SIMP_TAC[CONTENT_1; LIFT_DROP; REAL_LT_IMP_LE]; REWRITE_TAC[HAS_INTEGRAL_CONST]]);;

let WAN_INTERVAL1_INDICATOR_ABS = prove
 (`!a b. a < b
         ==> (\r:real^1. lift(if a < drop r /\ drop r < b then &1 else &0))
               absolutely_integrable_on (:real^1) /\
             integral (:real^1) (\r. lift(if a < drop r /\ drop r < b then &1 else &0)) =
             lift(b - a)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `(\r:real^1. lift(if a < drop r /\ drop r < b then &1 else &0)) =
                (\r. if a < drop r /\ drop r < b then lift(&1) else vec 0)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[LIFT_NUM];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`a:real`; `b:real`; `lift(&1)`] WAN_INTERVAL1_INDICATOR) THEN
  ASM_REWRITE_TAC[GSYM LIFT_CMUL; REAL_MUL_RID] THEN DISCH_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC NONNEGATIVE_ABSOLUTELY_INTEGRABLE THEN CONJ_TAC THENL
     [REWRITE_TAC[DIMINDEX_1; ARITH_RULE `1 <= i /\ i <= 1 <=> i = 1`] THEN
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN
      REWRITE_TAC[GSYM drop; LIFT_DROP; DROP_VEC] THEN REAL_ARITH_TAC;
      ASM_MESON_TAC[integrable_on]];
    MATCH_MP_TAC INTEGRAL_UNIQUE THEN ASM_REWRITE_TAC[]]);;

let WAN_PROJ3_SQ = prove
 (`!(f:real^2->real^K) a b.
     a < b /\ f measurable_on (:real^2) /\
     (\x:real^3. lift(norm(f(vector[x$1; x$2])) pow 2)) integrable_on
       {x:real^3 | a < x$3 /\ x$3 < b}
     ==> f IN lspace (:real^2) (&2) /\
         integral {x:real^3 | a < x$3 /\ x$3 < b}
           (\x. lift(norm(f(vector[x$1; x$2])) pow 2)) =
         (b - a) % integral (:real^2) (\y. lift(norm(f y) pow 2))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `Q = \x:real^3. if x IN {x:real^3 | a < x$3 /\ x$3 < b}
                             then lift(norm((f:real^2->real^K)(vector[x$1; x$2])) pow 2)
                             else vec 0` THEN
  SUBGOAL_THEN `(Q:real^3->real^1) absolutely_integrable_on (:real^3)` ASSUME_TAC THENL
   [EXPAND_TAC "Q" THEN REWRITE_TAC[ABSOLUTELY_INTEGRABLE_RESTRICT_UNIV] THEN
    MATCH_MP_TAC NONNEGATIVE_ABSOLUTELY_INTEGRABLE THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[DIMINDEX_1; ARITH_RULE `1 <= i /\ i <= 1 <=> i = 1`] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[GSYM drop; LIFT_DROP; REAL_LE_POW_2];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT1 o CONJUNCT2 o MATCH_MP WAN_FUBINI3) THEN
  SUBGOAL_THEN
   `!y:real^2. integral (:real^1) (\r. (Q:real^3->real^1)(vector[y$1; y$2; drop r])) =
               (b - a) % lift(norm((f:real^2->real^K) y) pow 2)`
  (fun th -> REWRITE_TAC[th]) THENL
   [X_GEN_TAC `y:real^2` THEN MATCH_MP_TAC INTEGRAL_UNIQUE THEN
    EXPAND_TAC "Q" THEN REWRITE_TAC[IN_ELIM_THM; VECTOR_3; WAN_VECTOR2_ETA] THEN
    MATCH_MP_TAC WAN_INTERVAL1_INDICATOR THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `(\y. lift(norm((f:real^2->real^K) y) pow 2)) integrable_on (:real^2)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `(\y. lift(norm((f:real^2->real^K) y) pow 2)) =
                  (\y. inv(b - a) % ((b - a) % lift(norm(f y) pow 2)))` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; VECTOR_MUL_ASSOC] THEN GEN_TAC THEN
      SUBGOAL_THEN `inv(b - a) * (b - a) = &1` (fun th -> REWRITE_TAC[th; VECTOR_MUL_LID]) THEN
      MATCH_MP_TAC REAL_MUL_LINV THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC INTEGRABLE_CMUL THEN ASM_MESON_TAC[integrable_on]];
    ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[lspace; IN_ELIM_THM; RPOW_POW]; ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM INTEGRAL_RESTRICT_UNIV] THEN
  SUBGOAL_THEN
   `(\x:real^3. if x IN {x:real^3 | a < x$3 /\ x$3 < b}
                then lift(norm((f:real^2->real^K)(vector[x$1; x$2])) pow 2) else vec 0) = Q`
  SUBST1_TAC THENL [EXPAND_TAC "Q" THEN REFL_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM INTEGRAL_CMUL] THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC INTEGRAL_UNIQUE THEN ASM_REWRITE_TAC[]);;

let WAN_PROJ3_SQ_CONV = prove
 (`!(f:real^2->real^K) a b.
     a < b /\ f IN lspace (:real^2) (&2)
     ==> (\x:real^3. lift(norm(f(vector[x$1; x$2])) pow 2)) absolutely_integrable_on
           {x:real^3 | a < x$3 /\ x$3 < b} /\
         integral {x:real^3 | a < x$3 /\ x$3 < b}
           (\x. lift(norm(f(vector[x$1; x$2])) pow 2)) =
         (b - a) % integral (:real^2) (\y. lift(norm(f y) pow 2))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`\y:real^2. lift(norm((f:real^2->real^K) y) pow 2)`;
                 `\r:real^1. if a < drop r /\ drop r < b then &1 else &0`]
                WAN_ABS_INT3_PROD) THEN
  MP_TAC(SPECL [`a:real`; `b:real`] WAN_INTERVAL1_INDICATOR_ABS) THEN
  ASM_REWRITE_TAC[LIFT_DROP] THEN STRIP_TAC THEN ANTS_TAC THENL
   [CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[]] THEN
    MATCH_MP_TAC NONNEGATIVE_ABSOLUTELY_INTEGRABLE THEN CONJ_TAC THENL
     [REWRITE_TAC[DIMINDEX_1; ARITH_RULE `1 <= i /\ i <= 1 <=> i = 1`] THEN
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[GSYM drop; LIFT_DROP; REAL_LE_POW_2];
      UNDISCH_TAC `(f:real^2->real^K) IN lspace (:real^2) (&2)` THEN
      SIMP_TAC[lspace; IN_ELIM_THM; RPOW_POW]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\x:real^3. (if a < x$3 /\ x$3 < b then &1 else &0) %
                lift(norm((f:real^2->real^K)(vector[x$1; x$2])) pow 2)) =
    (\x. if x IN {x:real^3 | a < x$3 /\ x$3 < b}
         then lift(norm(f(vector[x$1; x$2])) pow 2) else vec 0)`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; IN_ELIM_THM; LIFT_DROP] THEN GEN_TAC THEN
    COND_CASES_TAC THEN REWRITE_TAC[VECTOR_MUL_LID; VECTOR_MUL_LZERO];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[ABSOLUTELY_INTEGRABLE_RESTRICT_UNIV; INTEGRAL_RESTRICT_UNIV; LIFT_DROP] THEN
  SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Direction (A) of S2_STEREO, first part: the chain rule through the north *)
(* chart, the slice lemma, and the identification of the transported weak   *)
(* partials with the planar ones (a.e. on the slab).                        *)
(* ------------------------------------------------------------------------- *)

let WAN_NCH_DIFFEO_HYP = prove
 (`open {z:real^3 | &1 / &2 < norm z /\ norm z < &2 /\ z$3 < norm z} /\
   open {x:real^3 | &1 / &2 < x$3 /\ x$3 < &2} /\
   continuously_differentiable 1 {x:real^3 | &1 / &2 < x$3 /\ x$3 < &2} wan_nch /\
   continuously_differentiable 1
     {z:real^3 | &1 / &2 < norm z /\ norm z < &2 /\ z$3 < norm z} wan_nchi /\
   (!x. x IN {x:real^3 | &1 / &2 < x$3 /\ x$3 < &2}
        ==> wan_nch x IN {z:real^3 | &1 / &2 < norm z /\ norm z < &2 /\ z$3 < norm z} /\
            wan_nchi(wan_nch x) = x) /\
   (!z. z IN {z:real^3 | &1 / &2 < norm z /\ norm z < &2 /\ z$3 < norm z}
        ==> wan_nchi z IN {x:real^3 | &1 / &2 < x$3 /\ x$3 < &2} /\
            wan_nch(wan_nchi z) = z)`,
  REWRITE_TAC[WAN_NCH_OPEN; WAN_NCH_FACTS] THEN
  MP_TAC WAN_NCH_INV THEN REWRITE_TAC[IN_ELIM_THM] THEN SIMP_TAC[]);;

let WAN_S2_SHELL_FACTS = prove
 (`!(u:real^3->real^K).
     wan_s2_w12 u
     ==> wan_rext u IN lspace wan_shell (&2) /\
         wan_l2loc {z:real^3 | &1 / &2 < norm z /\ norm z < &2 /\ z$3 < norm z} (wan_rext u) /\
         (!j. 1 <= j /\ j <= 3
              ==> wan_wd wan_shell j (wan_rext u) IN lspace wan_shell (&2) /\
                  wan_wpd wan_shell j (wan_rext u) (wan_wd wan_shell j (wan_rext u)) /\
                  wan_l2loc {z:real^3 | &1 / &2 < norm z /\ norm z < &2 /\ z$3 < norm z}
                    (wan_wd wan_shell j (wan_rext u)) /\
                  wan_wpd {z:real^3 | &1 / &2 < norm z /\ norm z < &2 /\ z$3 < norm z} j
                    (wan_rext u) (wan_wd wan_shell j (wan_rext u)))`,
  GEN_TAC THEN REWRITE_TAC[wan_s2_w12] THEN DISCH_TAC THEN
  SUBGOAL_THEN `wan_rext (u:real^3->real^K) IN lspace wan_shell (&2)` ASSUME_TAC THENL
   [ASM_MESON_TAC[wan_w12]; ASM_REWRITE_TAC[]] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC WAN_L2LOC_SUBSET THEN EXISTS_TAC `wan_shell` THEN
    ASM_SIMP_TAC[WAN_LSPACE2_IMP_L2LOC; WAN_SHELL_NCH];
    ALL_TAC] THEN
  X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`wan_shell`; `j:num`; `wan_rext (u:real^3->real^K)`] WAN_WD_WORKS) THEN
  ASM_REWRITE_TAC[DIMINDEX_3] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC WAN_L2LOC_SUBSET THEN EXISTS_TAC `wan_shell` THEN
    ASM_SIMP_TAC[WAN_LSPACE2_IMP_L2LOC; WAN_SHELL_NCH];
    MATCH_MP_TAC WAN_WPD_SUBSET THEN EXISTS_TAC `wan_shell` THEN
    ASM_REWRITE_TAC[WAN_SHELL_NCH]]);;

let WAN_S2_A_CHAIN = prove
 (`!(u:real^3->real^K) i.
     wan_s2_w12 u /\ 1 <= i /\ i <= 3
     ==> wan_wpd {x:real^3 | &1 / &2 < x$3 /\ x$3 < &2} i
           (\x. u(stereo2_n_inv(vector[x$1; x$2])))
           (\x. vsum(1..3) (\j. frechet_derivative wan_nch (at x) (basis i)$j %
                                wan_wd wan_shell j (wan_rext u) (wan_nch x)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP WAN_S2_SHELL_FACTS) THEN
  MATCH_MP_TAC WAN_WPD_EQ_ON THEN
  EXISTS_TAC `\x:real^3. wan_rext (u:real^3->real^K) (wan_nch x)` THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`{z:real^3 | &1 / &2 < norm z /\ norm z < &2 /\ z$3 < norm z}`;
                   `{x:real^3 | &1 / &2 < x$3 /\ x$3 < &2}`; `wan_nch`; `wan_nchi`;
                   `wan_rext (u:real^3->real^K)`;
                   `\j. wan_wd wan_shell j (wan_rext (u:real^3->real^K))`; `i:num`]
                  WAN_DIFFEO_WPD) THEN
    REWRITE_TAC[DIMINDEX_3; WAN_NCH_DIFFEO_HYP] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_SIMP_TAC[];
    REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC WAN_REXT_NCH THEN ASM_REAL_ARITH_TAC]);;

let WAN_S2_A_SLICE_I = prove
 (`!(u:real^3->real^K) psi i.
     wan_s2_w12 u /\
     wan_test {r:real^1 | &1 / &2 < drop r /\ drop r < &2} psi /\
     integral (:real^1) (\r. lift(psi r)) = lift(&1) /\ (i = 1 \/ i = 2)
     ==> wan_lloc (:real^2) (\y. u(stereo2_n_inv y)) /\
         wan_wpd (:real^2) i (\y. u(stereo2_n_inv y))
           (\y. integral (:real^1)
                 (\r. psi r %
                      vsum(1..3) (\j. frechet_derivative wan_nch (at (vector[y$1; y$2; drop r]))
                                        (basis i)$j %
                                      wan_wd wan_shell j (wan_rext u)
                                        (wan_nch (vector[y$1; y$2; drop r]))))) /\
         negligible
          {x:real^3 | x IN {x:real^3 | &1 / &2 < x$3 /\ x$3 < &2} /\
                      ~(vsum(1..3) (\j. frechet_derivative wan_nch (at x) (basis i)$j %
                                        wan_wd wan_shell j (wan_rext u) (wan_nch x)) =
                        integral (:real^1)
                         (\r. psi r %
                              vsum(1..3) (\j. frechet_derivative wan_nch
                                                (at (vector[x$1; x$2; drop r])) (basis i)$j %
                                              wan_wd wan_shell j (wan_rext u)
                                                (wan_nch (vector[x$1; x$2; drop r])))))}`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`u:real^3->real^K`; `i:num`] WAN_S2_A_CHAIN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(ISPECL
   [`\y:real^2. (u:real^3->real^K)(stereo2_n_inv y)`;
    `\x:real^3. vsum(1..3) (\j. frechet_derivative wan_nch (at x) (basis i)$j %
                                wan_wd wan_shell j (wan_rext (u:real^3->real^K)) (wan_nch x))`;
    `psi:real^1->real`; `&1 / &2`; `&2`; `i:num`] WAN_SLICE_WPD3) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL
   [`{x:real^3 | &1 / &2 < x$3 /\ x$3 < &2}`; `i:num`;
    `\x:real^3. (u:real^3->real^K)(stereo2_n_inv(vector[x$1; x$2]))`;
    `\x:real^3. vsum(1..3) (\j. frechet_derivative wan_nch (at x) (basis i)$j %
                                wan_wd wan_shell j (wan_rext (u:real^3->real^K)) (wan_nch x))`;
    `\x:real^3. integral (:real^1)
       (\r. (psi:real^1->real) r %
            vsum(1..3) (\j. frechet_derivative wan_nch (at (vector[x$1; x$2; drop r]))
                              (basis i)$j %
                            wan_wd wan_shell j (wan_rext (u:real^3->real^K))
                              (wan_nch (vector[x$1; x$2; drop r]))))`] WAN_WPD_UNIQUE) THEN
  REWRITE_TAC[CONJUNCT1 WAN_NCH_OPEN] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL
   [`{x:real^3 | &1 / &2 < x$3 /\ x$3 < &2}`; `\y:real^2. (u:real^3->real^K)(stereo2_n_inv y)`;
    `\y:real^2. integral (:real^1)
       (\r. (psi:real^1->real) r %
            vsum(1..3) (\j. frechet_derivative wan_nch (at (vector[y$1; y$2; drop r]))
                              (basis i)$j %
                            wan_wd wan_shell j (wan_rext (u:real^3->real^K))
                              (wan_nch (vector[y$1; y$2; drop r]))))`;
    `i:num`] WAN_WPD_PROJ3) THEN
  ASM_REWRITE_TAC[VECTOR_2]);;

let WAN_S2_A_VERT = prove
 (`!(u:real^3->real^K).
     wan_s2_w12 u /\ wan_lloc (:real^2) (\y. u(stereo2_n_inv y))
     ==> negligible
          {x:real^3 | x IN {x:real^3 | &1 / &2 < x$3 /\ x$3 < &2} /\
                      ~(vsum(1..3) (\j. frechet_derivative wan_nch (at x) (basis 3)$j %
                                        wan_wd wan_shell j (wan_rext u) (wan_nch x)) =
                        vec 0)}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`{x:real^3 | &1 / &2 < x$3 /\ x$3 < &2}`; `3`;
    `\x:real^3. (u:real^3->real^K)(stereo2_n_inv(vector[x$1; x$2]))`;
    `\x:real^3. vsum(1..3) (\j. frechet_derivative wan_nch (at x) (basis 3)$j %
                                wan_wd wan_shell j (wan_rext (u:real^3->real^K)) (wan_nch x))`;
    `\x:real^3. vec 0:real^K`] WAN_WPD_UNIQUE) THEN
  REWRITE_TAC[CONJUNCT1 WAN_NCH_OPEN] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC WAN_S2_A_CHAIN THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
    MP_TAC(ISPECL [`{x:real^3 | &1 / &2 < x$3 /\ x$3 < &2}`;
                   `\y:real^2. (u:real^3->real^K)(stereo2_n_inv y)`] WAN_WPD_PROJ3_VERT) THEN
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Direction (A) of S2_STEREO, second part: the Dirichlet integral of the   *)
(* radial extension pulled back to the slab, and its identification with    *)
(* 3/2 times the planar Dirichlet integral.                                  *)
(* ------------------------------------------------------------------------- *)

let wan_s2h = new_definition
 `wan_s2h (u:real^3->real^K) i (x:real^3) =
    vsum(1..3) (\j. frechet_derivative wan_nch (at x) (basis i)$j %
                    wan_wd wan_shell j (wan_rext u) (wan_nch x))`;;

let WAN_S2_A_SQ_INT = prove
 (`!(u:real^3->real^K).
     wan_s2_w12 u
     ==> (\z. lift(sum(1..3) (\j. norm(wan_wd wan_shell j (wan_rext u) z) pow 2)))
           absolutely_integrable_on
           {z:real^3 | &1 / &2 < norm z /\ norm z < &2 /\ z$3 < norm z} /\
         wan_dir wan_shell (wan_rext u) =
         drop(integral {z:real^3 | &1 / &2 < norm z /\ norm z < &2 /\ z$3 < norm z}
                (\z. lift(sum(1..3) (\j. norm(wan_wd wan_shell j (wan_rext u) z) pow 2))))`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP WAN_S2_SHELL_FACTS) THEN
  SUBGOAL_THEN
   `!j. 1 <= j /\ j <= 3
        ==> (\z. lift(norm(wan_wd wan_shell j (wan_rext (u:real^3->real^K)) z) pow 2))
              absolutely_integrable_on
              {z:real^3 | &1 / &2 < norm z /\ norm z < &2 /\ z$3 < norm z} /\
            integral wan_shell (\z. lift(norm(wan_wd wan_shell j (wan_rext u) z) pow 2)) =
            integral {z:real^3 | &1 / &2 < norm z /\ norm z < &2 /\ z$3 < norm z}
              (\z. lift(norm(wan_wd wan_shell j (wan_rext u) z) pow 2))`
  ASSUME_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `wan_wd wan_shell j (wan_rext (u:real^3->real^K)) IN lspace wan_shell (&2)`
    ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN CONJ_TAC THENL
     [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
      EXISTS_TAC `wan_shell` THEN REWRITE_TAC[WAN_SHELL_NCH] THEN
      SIMP_TAC[LEBESGUE_MEASURABLE_OPEN; WAN_NCH_OPEN] THEN
      MATCH_MP_TAC NONNEGATIVE_ABSOLUTELY_INTEGRABLE THEN CONJ_TAC THENL
       [REWRITE_TAC[DIMINDEX_1; ARITH_RULE `1 <= i /\ i <= 1 <=> i = 1`] THEN
        REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[GSYM drop; LIFT_DROP; REAL_LE_POW_2];
        MATCH_MP_TAC WAN_LSPACE2_SQNORM_INTEGRABLE THEN ASM_REWRITE_TAC[ETA_AX]];
      MATCH_MP_TAC INTEGRAL_SPIKE_SET THEN
      MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
      EXISTS_TAC `wan_shell DIFF {z:real^3 | &1 / &2 < norm z /\ norm z < &2 /\ z$3 < norm z}` THEN
      REWRITE_TAC[WAN_SHELL_NCH] THEN MP_TAC WAN_SHELL_NCH THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!j. 1 <= j /\ j <= 3
        ==> (\z. lift(norm(wan_wd wan_shell j (wan_rext (u:real^3->real^K)) z) pow 2))
              integrable_on
              {z:real^3 | &1 / &2 < norm z /\ norm z < &2 /\ z$3 < norm z}`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE]; ALL_TAC] THEN
  REWRITE_TAC[SUM_3; LIFT_ADD] THEN CONJ_TAC THENL
   [REPEAT(MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_ADD THEN CONJ_TAC) THEN
    FIRST_X_ASSUM(K ALL_TAC) THEN ASM_SIMP_TAC[ARITH];
    ALL_TAC] THEN
  REWRITE_TAC[wan_dir; DIMINDEX_3; SUM_3] THEN
  ASM_SIMP_TAC[ARITH; INTEGRAL_ADD; INTEGRABLE_ADD; DROP_ADD] THEN REAL_ARITH_TAC);;

let WAN_S2_A_PULL = prove
 (`!(u:real^3->real^K).
     wan_s2_w12 u
     ==> (\x. lift(norm(wan_s2h u 1 x) pow 2 + norm(wan_s2h u 2 x) pow 2 +
                   wan_nchj x * norm(wan_s2h u 3 x) pow 2))
           absolutely_integrable_on {x:real^3 | &1 / &2 < x$3 /\ x$3 < &2} /\
         wan_dir wan_shell (wan_rext u) =
         drop(integral {x:real^3 | &1 / &2 < x$3 /\ x$3 < &2}
                (\x. lift(norm(wan_s2h u 1 x) pow 2 + norm(wan_s2h u 2 x) pow 2 +
                          wan_nchj x * norm(wan_s2h u 3 x) pow 2)))`,
  GEN_TAC THEN DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP WAN_S2_A_SQ_INT) THEN
  MP_TAC(ISPEC `\z:real^3. lift(sum(1..3)
                  (\j. norm(wan_wd wan_shell j (wan_rext (u:real^3->real^K)) z) pow 2))`
               WAN_NCH_COV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!x:real^3. x IN {x:real^3 | &1 / &2 < x$3 /\ x$3 < &2}
               ==> wan_nchj x %
                   lift(sum(1..3) (\j. norm(wan_wd wan_shell j (wan_rext (u:real^3->real^K))
                                            (wan_nch x)) pow 2)) =
                   lift(norm(wan_s2h u 1 x) pow 2 + norm(wan_s2h u 2 x) pow 2 +
                        wan_nchj x * norm(wan_s2h u 3 x) pow 2)`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^3` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
    REWRITE_TAC[GSYM LIFT_CMUL; LIFT_EQ; wan_s2h] THEN
    CONV_TAC SYM_CONV THEN
    MP_TAC(ISPECL [`x:real^3`;
                   `\j. wan_wd wan_shell j (wan_rext (u:real^3->real^K)) (wan_nch x)`]
                  WAN_NCH_PARSEVAL) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_EQ THEN
    EXISTS_TAC
     `\x:real^3. wan_nchj x %
                 lift(sum(1..3) (\j. norm(wan_wd wan_shell j (wan_rext (u:real^3->real^K))
                                          (wan_nch x)) pow 2))` THEN
    ASM_SIMP_TAC[];
    ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN MATCH_MP_TAC INTEGRAL_EQ THEN ASM_SIMP_TAC[]]);;

let WAN_PROJ3_SQ_MEAS = prove
 (`!(f:real^2->real^K) s.
     wan_lloc (:real^2) f /\ lebesgue_measurable s
     ==> (\x:real^3. lift(norm(f(vector[x$1; x$2])) pow 2)) measurable_on s /\
         f measurable_on (:real^2)`,
  REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC MEASURABLE_ON_LIFT_POW THEN REWRITE_TAC[ARITH] THEN
    MATCH_MP_TAC MEASURABLE_ON_NORM THEN
    MATCH_MP_TAC MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
    EXISTS_TAC `(:real^3)` THEN ASM_REWRITE_TAC[SUBSET_UNIV] THEN
    MATCH_MP_TAC WAN_LLOC_MEASURABLE THEN REWRITE_TAC[OPEN_UNIV] THEN
    MATCH_MP_TAC WAN_LLOC_PROJ3 THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC WAN_LLOC_MEASURABLE THEN ASM_REWRITE_TAC[OPEN_UNIV]]);;

let WAN_S2_A_ENERGY = prove
 (`!(u:real^3->real^K) (v:num->real^2->real^K).
     wan_s2_w12 u /\
     (!i. i = 1 \/ i = 2
          ==> wan_lloc (:real^2) (v i) /\
              negligible {x:real^3 | x IN {x:real^3 | &1 / &2 < x$3 /\ x$3 < &2} /\
                                     ~(wan_s2h u i x = v i (vector[x$1; x$2]))}) /\
     negligible {x:real^3 | x IN {x:real^3 | &1 / &2 < x$3 /\ x$3 < &2} /\
                            ~(wan_s2h u 3 x = vec 0)}
     ==> v 1 IN lspace (:real^2) (&2) /\ v 2 IN lspace (:real^2) (&2) /\
         wan_dir wan_shell (wan_rext u) =
         &3 / &2 * (drop(integral (:real^2) (\y. lift(norm(v 1 y) pow 2))) +
                    drop(integral (:real^2) (\y. lift(norm(v 2 y) pow 2))))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "V") ASSUME_TAC)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP WAN_S2_A_PULL) THEN
  USE_THEN "V" (MP_TAC o SPEC `1`) THEN USE_THEN "V" (MP_TAC o SPEC `2`) THEN
  REWRITE_TAC[ARITH] THEN STRIP_TAC THEN STRIP_TAC THEN
  ABBREV_TAC
   `N = {x:real^3 | x IN {x:real^3 | &1 / &2 < x$3 /\ x$3 < &2} /\
                    ~(wan_s2h (u:real^3->real^K) 1 x = v 1 (vector[x$1; x$2]))} UNION
        {x:real^3 | x IN {x:real^3 | &1 / &2 < x$3 /\ x$3 < &2} /\
                    ~(wan_s2h u 2 x = (v:num->real^2->real^K) 2 (vector[x$1; x$2]))} UNION
        {x:real^3 | x IN {x:real^3 | &1 / &2 < x$3 /\ x$3 < &2} /\ ~(wan_s2h u 3 x = vec 0)}` THEN
  SUBGOAL_THEN `negligible(N:real^3->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "N" THEN REPEAT(MATCH_MP_TAC NEGLIGIBLE_UNION THEN CONJ_TAC) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x:real^3. x IN {x:real^3 | &1 / &2 < x$3 /\ x$3 < &2} DIFF N
               ==> lift(norm(wan_s2h (u:real^3->real^K) 1 x) pow 2 +
                        norm(wan_s2h u 2 x) pow 2 + wan_nchj x * norm(wan_s2h u 3 x) pow 2) =
                   lift(norm((v:num->real^2->real^K) 1 (vector[x$1; x$2])) pow 2 +
                        norm(v 2 (vector[x$1; x$2])) pow 2)`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^3` THEN EXPAND_TAC "N" THEN
    REWRITE_TAC[IN_DIFF; IN_UNION; IN_ELIM_THM; DE_MORGAN_THM] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[NORM_0] THEN REWRITE_TAC[REAL_POW_ZERO; ARITH; REAL_MUL_RZERO;
                                             REAL_ADD_RID] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\x:real^3. lift(norm((v:num->real^2->real^K) 1 (vector[x$1; x$2])) pow 2 +
                     norm(v 2 (vector[x$1; x$2])) pow 2))
      absolutely_integrable_on {x:real^3 | &1 / &2 < x$3 /\ x$3 < &2} /\
    integral {x:real^3 | &1 / &2 < x$3 /\ x$3 < &2}
      (\x. lift(norm(v 1 (vector[x$1; x$2])) pow 2 + norm(v 2 (vector[x$1; x$2])) pow 2)) =
    integral {x:real^3 | &1 / &2 < x$3 /\ x$3 < &2}
      (\x. lift(norm(wan_s2h (u:real^3->real^K) 1 x) pow 2 + norm(wan_s2h u 2 x) pow 2 +
                wan_nchj x * norm(wan_s2h u 3 x) pow 2))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] ABSOLUTELY_INTEGRABLE_SPIKE) THEN
      EXISTS_TAC
       `\x:real^3. lift(norm(wan_s2h (u:real^3->real^K) 1 x) pow 2 + norm(wan_s2h u 2 x) pow 2 +
                        wan_nchj x * norm(wan_s2h u 3 x) pow 2)` THEN
      EXISTS_TAC `N:real^3->bool` THEN ASM_SIMP_TAC[];
      MATCH_MP_TAC INTEGRAL_SPIKE THEN EXISTS_TAC `N:real^3->bool` THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. i = 1 \/ i = 2
        ==> (\x:real^3. lift(norm((v:num->real^2->real^K) i (vector[x$1; x$2])) pow 2))
              integrable_on {x:real^3 | &1 / &2 < x$3 /\ x$3 < &2}`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
    MATCH_MP_TAC MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_ABSOLUTELY_INTEGRABLE THEN
    EXISTS_TAC
     `\x:real^3. lift(norm((v:num->real^2->real^K) 1 (vector[x$1; x$2])) pow 2 +
                      norm(v 2 (vector[x$1; x$2])) pow 2)` THEN
    ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE] THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`(v:num->real^2->real^K) i`; `{x:real^3 | &1 / &2 < x$3 /\ x$3 < &2}`]
                    WAN_PROJ3_SQ_MEAS) THEN
      SIMP_TAC[LEBESGUE_MEASURABLE_OPEN; WAN_NCH_OPEN] THEN ANTS_TAC THENL
       [USE_THEN "V" (MP_TAC o SPEC `i:num`) THEN ASM_SIMP_TAC[]; SIMP_TAC[]];
      X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
      REWRITE_TAC[NORM_LIFT; LIFT_DROP; REAL_ABS_POW; REAL_ABS_NORM] THEN
      MP_TAC(SPEC `norm((v:num->real^2->real^K) 1 (vector[(x:real^3)$1; x$2]))` REAL_LE_POW_2) THEN
      MP_TAC(SPEC `norm((v:num->real^2->real^K) 2 (vector[(x:real^3)$1; x$2]))` REAL_LE_POW_2) THEN
      FIRST_X_ASSUM(DISJ_CASES_THEN SUBST1_TAC) THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(v:num->real^2->real^K) 1`; `&1 / &2`; `&2`] WAN_PROJ3_SQ) THEN
  MP_TAC(ISPECL [`(v:num->real^2->real^K) 2`; `&1 / &2`; `&2`] WAN_PROJ3_SQ) THEN
  MP_TAC(ISPECL [`(v:num->real^2->real^K) 1`; `(:real^3)`] WAN_PROJ3_SQ_MEAS) THEN
  MP_TAC(ISPECL [`(v:num->real^2->real^K) 2`; `(:real^3)`] WAN_PROJ3_SQ_MEAS) THEN
  ASM_SIMP_TAC[LEBESGUE_MEASURABLE_UNIV; ARITH; REAL_ARITH `&1 / &2 < &2`] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `integral {x:real^3 | &1 / &2 < x$3 /\ x$3 < &2}
      (\x. lift(norm((v:num->real^2->real^K) 1 (vector[x$1; x$2])) pow 2 +
                norm(v 2 (vector[x$1; x$2])) pow 2)) =
    integral {x:real^3 | &1 / &2 < x$3 /\ x$3 < &2}
      (\x. lift(norm(v 1 (vector[x$1; x$2])) pow 2)) +
    integral {x:real^3 | &1 / &2 < x$3 /\ x$3 < &2}
      (\x. lift(norm(v 2 (vector[x$1; x$2])) pow 2))`
  MP_TAC THENL
   [REWRITE_TAC[LIFT_ADD] THEN MATCH_MP_TAC INTEGRAL_ADD THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o AP_TERM `drop`) THEN
  REWRITE_TAC[DROP_ADD; DROP_CMUL; REAL_ARITH `&2 - &1 / &2 = &3 / &2`] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC);;

let WAN_S2_STEREO_A = prove
 (`!(u:real^3->real^K).
     wan_s2_w12 u
     ==> wan_lloc (:real^2) (\y. u(stereo2_n_inv y)) /\
         (!i. 1 <= i /\ i <= 2
              ==> ?v. v IN lspace (:real^2) (&2) /\
                      wan_wpd (:real^2) i (\y. u(stereo2_n_inv y)) v) /\
         wan_dir (:real^2) (\y. u(stereo2_n_inv y)) = wan_s2_dir u`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL [`&1 / &2`; `&2`] WAN_SLAB_PSI) THEN
  REWRITE_TAC[REAL_ARITH `&1 / &2 < &2`] THEN
  DISCH_THEN(X_CHOOSE_THEN `psi:real^1->real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC
   `v = \i (y:real^2). integral (:real^1)
          (\r. (psi:real^1->real) r %
               wan_s2h (u:real^3->real^K) i (vector[y$1; y$2; drop r]))` THEN
  SUBGOAL_THEN
   `wan_lloc (:real^2) (\y. (u:real^3->real^K)(stereo2_n_inv y)) /\
    !i. i = 1 \/ i = 2
        ==> wan_wpd (:real^2) i (\y. u(stereo2_n_inv y)) ((v:num->real^2->real^K) i) /\
            wan_lloc (:real^2) (v i) /\
            negligible {x:real^3 | x IN {x:real^3 | &1 / &2 < x$3 /\ x$3 < &2} /\
                                   ~(wan_s2h u i x = v i (vector[x$1; x$2]))}`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`u:real^3->real^K`; `psi:real^1->real`; `1`] WAN_S2_A_SLICE_I) THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[];
      ALL_TAC] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`u:real^3->real^K`; `psi:real^1->real`; `i:num`] WAN_S2_A_SLICE_I) THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM wan_s2h] THEN
    EXPAND_TAC "v" THEN REWRITE_TAC[VECTOR_2] THEN
    REWRITE_TAC[wan_wpd] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `u:real^3->real^K` WAN_S2_A_VERT) THEN
  ASM_REWRITE_TAC[GSYM wan_s2h] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`u:real^3->real^K`; `v:num->real^2->real^K`] WAN_S2_A_ENERGY) THEN
  ASM_SIMP_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[ARITH_RULE `1 <= i /\ i <= 2 <=> i = 1 \/ i = 2`] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    EXISTS_TAC `(v:num->real^2->real^K) i` THEN
    FIRST_X_ASSUM(DISJ_CASES_THEN SUBST_ALL_TAC) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(:real^2)`; `\y. (u:real^3->real^K)(stereo2_n_inv y)`;
                 `v:num->real^2->real^K`] WAN_DIR_EQ_L2) THEN
  REWRITE_TAC[OPEN_UNIV; DIMINDEX_2] THEN ANTS_TAC THENL
   [REWRITE_TAC[ARITH_RULE `1 <= i /\ i <= 2 <=> i = 1 \/ i = 2`] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(DISJ_CASES_THEN SUBST_ALL_TAC) THEN ASM_SIMP_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  ASM_REWRITE_TAC[wan_s2_dir; SUM_2] THEN
  REWRITE_TAC[REAL_ARITH `&2 / &3 * &3 / &2 * z = z`]);;

(* ------------------------------------------------------------------------- *)
(* Removability of the x3-axis for weak partials of L^2_loc maps on open    *)
(* subsets of real^3 (a codimension-two set): the cutoffs                    *)
(* wan_acut e z = b_e(z1,z2), with b_e the planar point cutoff, have        *)
(* derivatives bounded in L^2 on bounded sets uniformly in e, and supports  *)
(* shrinking to the axis.                                                    *)
(* ------------------------------------------------------------------------- *)

let wan_acut = new_definition
 `wan_acut (e:real) (z:real^3) =
    smooth_bump e (&2 * e) ((vector[z$1; z$2]:real^2) - vec 0)`;;

let WAN_ACUT_FACTS = prove
 (`!e. &0 < e
       ==> smooth_map_on (:real^3) (\z. lift(wan_acut e z)) /\
           (!z. &0 <= wan_acut e z /\ wan_acut e z <= &1) /\
           (!z. norm(vector[z$1; z$2]:real^2) <= e ==> wan_acut e z = &1) /\
           (!z. &2 * e <= norm(vector[z$1; z$2]:real^2) ==> wan_acut e z = &0) /\
           (!i z. wan_dpart i (\z. wan_acut e z) z =
                  drop(frechet_derivative (\y. lift(smooth_bump e (&2 * e) (y - vec 0)))
                         (at (vector[z$1; z$2])) (vector[(basis i:real^3)$1; (basis i:real^3)$2])))`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`vec 0:real^2`; `e:real`] WAN_POINT_CUTOFF_FACTS) THEN
  ASM_REWRITE_TAC[VECTOR_SUB_RZERO] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`\y:real^2. smooth_bump e (&2 * e) (y - vec 0)`;
                 `\z:real^3. vector[z$1; z$2]:real^2`; `vec 0:real^2`] WAN_DPART_AFFINE) THEN
  ASM_REWRITE_TAC[VECTOR_SUB_RZERO; VECTOR_ADD_RID; WAN_PROJ3_LINEAR] THEN
  REWRITE_TAC[GSYM wan_acut] THEN
  SUBGOAL_THEN `(\x:real^3. smooth_bump e (&2 * e) (vector[x$1; x$2]:real^2)) =
                (\z. wan_acut e z)` (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[FUN_EQ_THM; wan_acut; VECTOR_SUB_RZERO]; ALL_TAC] THEN
  DISCH_TAC THEN REPEAT CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`1`; `vec 0:real^3`]) THEN
    REWRITE_TAC[wan_acut; VECTOR_SUB_RZERO] THEN SIMP_TAC[];
    ASM_REWRITE_TAC[wan_acut; VECTOR_SUB_RZERO];
    ASM_SIMP_TAC[wan_acut; VECTOR_SUB_RZERO];
    ASM_SIMP_TAC[wan_acut; VECTOR_SUB_RZERO];
    ASM_SIMP_TAC[]]);;

let WAN_ACUT_DPART_CASES = prove
 (`!e i z.
     &0 < e
     ==> wan_dpart i (\z. wan_acut e z) z =
         (if i = 1 then wan_dpart 1 (\y. smooth_bump e (&2 * e) (y - vec 0)) (vector[z$1; z$2])
          else if i = 2
          then wan_dpart 2 (\y. smooth_bump e (&2 * e) (y - vec 0)) (vector[z$1; z$2])
          else &0)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[WAN_ACUT_FACTS] THEN
  COND_CASES_TAC THENL [ASM_REWRITE_TAC[WAN_BASIS3_PROJ; wan_dpart]; ALL_TAC] THEN
  COND_CASES_TAC THENL [ASM_REWRITE_TAC[WAN_BASIS3_PROJ; wan_dpart]; ALL_TAC] THEN
  SUBGOAL_THEN `vector[(basis i:real^3)$1; (basis i:real^3)$2]:real^2 = vec 0` SUBST1_TAC THENL
   [SIMP_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2; BASIS_COMPONENT; DIMINDEX_3; ARITH;
             VEC_COMPONENT] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `frechet_derivative (\y. lift(smooth_bump e (&2 * e) (y - vec 0:real^2)))
                  (at (vector[(z:real^3)$1; z$2]))` LINEAR_0) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `(:real^2)` THEN
    REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN
    MP_TAC(ISPECL [`vec 0:real^2`; `e:real`] WAN_POINT_CUTOFF_FACTS) THEN ASM_SIMP_TAC[];
    SIMP_TAC[DROP_VEC]]);;

let WAN_ACUT_DPART = prove
 (`?B. &0 <= B /\
       !e i. &0 < e
             ==> (\z. lift(wan_dpart i (\z. wan_acut e z) z)) continuous_on (:real^3) /\
                 (!z. abs(wan_dpart i (\z. wan_acut e z) z) <= B / e) /\
                 (!z. ~((vector[z$1; z$2]:real^2) IN cball(vec 0,&2 * e))
                      ==> wan_dpart i (\z. wan_acut e z) z = &0) /\
                 (!z. (wan_dpart i (\z. wan_acut e z) z) pow 2 <=
                      (wan_dpart 1 (\y. smooth_bump e (&2 * e) (y - vec 0))
                         (vector[z$1; z$2])) pow 2 +
                      (wan_dpart 2 (\y. smooth_bump e (&2 * e) (y - vec 0))
                         (vector[z$1; z$2])) pow 2)`,
  X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC (INST_TYPE [`:2`,`:N`] WAN_POINT_CUTOFF_DPART) THEN
  EXISTS_TAC `B:real` THEN ASM_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_X_ASSUM(fun th -> MP_TAC(ISPECL [`vec 0:real^2`; `e:real`; `1`] th) THEN
                          MP_TAC(ISPECL [`vec 0:real^2`; `e:real`; `2`] th)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "C2") (CONJUNCTS_THEN2 (LABEL_TAC "B2") (LABEL_TAC "S2"))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "C1") (CONJUNCTS_THEN2 (LABEL_TAC "B1") (LABEL_TAC "S1"))) THEN
  ASM_SIMP_TAC[WAN_ACUT_DPART_CASES] THEN
  SUBGOAL_THEN `&0 <= B / e` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!k. k = 1 \/ k = 2
        ==> (\z. lift(wan_dpart k (\y. smooth_bump e (&2 * e) (y - vec 0:real^2))
                       (vector[(z:real^3)$1; z$2]))) continuous_on (:real^3)`
  ASSUME_TAC THENL
   [X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `(\z. lift(wan_dpart k (\y. smooth_bump e (&2 * e) (y - vec 0:real^2))
                 (vector[(z:real^3)$1; z$2]))) =
      (\y. lift(wan_dpart k (\y. smooth_bump e (&2 * e) (y - vec 0)) y)) o
      (\z:real^3. vector[z$1; z$2]:real^2)`
    SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN REWRITE_TAC[WAN_PROJ3_LINEAR];
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
      REWRITE_TAC[SUBSET_UNIV] THEN
      FIRST_X_ASSUM(DISJ_CASES_THEN SUBST1_TAC) THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(SPEC `1` (ASSUME
   `!k. k = 1 \/ k = 2
        ==> (\z. lift(wan_dpart k (\y. smooth_bump e (&2 * e) (y - vec 0:real^2))
                       (vector[(z:real^3)$1; z$2]))) continuous_on (:real^3)`)) THEN
  MP_TAC(SPEC `2` (ASSUME
   `!k. k = 1 \/ k = 2
        ==> (\z. lift(wan_dpart k (\y. smooth_bump e (&2 * e) (y - vec 0:real^2))
                       (vector[(z:real^3)$1; z$2]))) continuous_on (:real^3)`)) THEN
  REWRITE_TAC[ARITH] THEN REPEAT DISCH_TAC THEN
  ASM_CASES_TAC `i = 1` THEN ASM_REWRITE_TAC[] THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN GEN_TAC THEN
    ASM_SIMP_TAC[] THEN
    MP_TAC(SPEC `wan_dpart 2 (\y. smooth_bump e (&2 * e) (y - vec 0:real^2))
                   (vector[(z:real^3)$1; z$2])` REAL_LE_POW_2) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `i = 2` THEN ASM_REWRITE_TAC[] THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN GEN_TAC THEN
    ASM_SIMP_TAC[] THEN
    MP_TAC(SPEC `wan_dpart 1 (\y. smooth_bump e (&2 * e) (y - vec 0:real^2))
                   (vector[(z:real^3)$1; z$2])` REAL_LE_POW_2) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[LIFT_NUM; CONTINUOUS_ON_CONST; REAL_ABS_0] THEN ASM_REWRITE_TAC[] THEN
  GEN_TAC THEN
  MP_TAC(SPEC `wan_dpart 1 (\y. smooth_bump e (&2 * e) (y - vec 0:real^2))
                 (vector[(z:real^3)$1; z$2])` REAL_LE_POW_2) THEN
  MP_TAC(SPEC `wan_dpart 2 (\y. smooth_bump e (&2 * e) (y - vec 0:real^2))
                 (vector[(z:real^3)$1; z$2])` REAL_LE_POW_2) THEN
  REWRITE_TAC[REAL_POW_ZERO; ARITH] THEN REAL_ARITH_TAC);;

let WAN_INTERVAL1_SYM_INTEGRAL = prove
 (`!H. &0 <= H
       ==> integral (:real^1) (\r. lift(if r IN interval[--lift H,lift H] then &1 else &0)) =
           lift(&2 * H)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\r:real^1. lift(if r IN interval[--lift H,lift H] then &1 else &0)) =
                (\r. if r IN interval[--lift H,lift H] then lift(&1) else vec 0)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[LIFT_NUM];
    ALL_TAC] THEN
  REWRITE_TAC[INTEGRAL_RESTRICT_UNIV; INTEGRAL_CONST] THEN
  SUBGOAL_THEN `content(interval[--lift H,lift H]) = &2 * H` SUBST1_TAC THENL
   [ASM_SIMP_TAC[CONTENT_1; DROP_NEG; LIFT_DROP; REAL_ARITH `&0 <= H ==> --H <= H`] THEN
    REAL_ARITH_TAC;
    REWRITE_TAC[GSYM LIFT_CMUL; REAL_MUL_RID]]);;

let WAN_ACUT_L2 = prove
 (`?C. &0 <= C /\
       !e i H (chi:real^3->real) K.
         &0 < e /\ e <= &1 /\ &0 <= H /\
         (\z. lift(chi z)) continuous_on (:real^3) /\ (!z. abs(chi z) <= &1) /\
         compact K /\ (!z. ~(z IN K) ==> chi z = &0) /\ (!z. z IN K ==> abs(z$3) <= H)
         ==> (\z. lift((wan_dpart i (\z. wan_acut e z) z * chi z) pow 2))
               integrable_on (:real^3) /\
             drop(integral (:real^3)
                    (\z. lift((wan_dpart i (\z. wan_acut e z) z * chi z) pow 2)))
             <= H * C`,
  X_CHOOSE_THEN `C0:real` STRIP_ASSUME_TAC (INST_TYPE [`:2`,`:N`] WAN_POINT_CUTOFF_L2) THEN
  X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC WAN_ACUT_DPART THEN
  EXISTS_TAC `&4 * C0` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`e:real`; `i:num`]) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(fun th -> MP_TAC(ISPECL [`vec 0:real^2`; `e:real`; `1`] th) THEN
                          MP_TAC(ISPECL [`vec 0:real^2`; `e:real`; `2`] th)) THEN
  ASM_REWRITE_TAC[DIMINDEX_2; LE_REFL] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "I2") (LABEL_TAC "L2")) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "I1") (LABEL_TAC "L1")) THEN
  MP_TAC(ISPECL
   [`\y:real^2. lift(wan_dpart 1 (\y. smooth_bump e (&2 * e) (y - vec 0:real^2)) y pow 2 +
                     wan_dpart 2 (\y. smooth_bump e (&2 * e) (y - vec 0:real^2)) y pow 2)`;
    `\r:real^1. if r IN interval[--lift H,lift H] then &1 else &0`] WAN_ABS_INT3_PROD) THEN
  REWRITE_TAC[WAN_INDICATOR_INTERVAL_ABS_INT] THEN ANTS_TAC THENL
   [REWRITE_TAC[LIFT_ADD] THEN MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_ADD THEN
    CONJ_TAC THEN MATCH_MP_TAC NONNEGATIVE_ABSOLUTELY_INTEGRABLE THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[DIMINDEX_1; ARITH_RULE `1 <= i /\ i <= 1 <=> i = 1`] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[GSYM drop; LIFT_DROP; REAL_LE_POW_2];
    ALL_TAC] THEN
  ASM_SIMP_TAC[WAN_INTERVAL1_SYM_INTEGRAL; LIFT_DROP] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(\z. lift((wan_dpart i (\z. wan_acut e z) z * (chi:real^3->real) z) pow 2))
      integrable_on (:real^3)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC WAN_CONT_SUPPORT_INTEGRABLE THEN EXISTS_TAC `K:real^3->bool` THEN
    ASM_SIMP_TAC[REAL_MUL_RZERO; REAL_POW_ZERO; ARITH; LIFT_NUM] THEN
    MATCH_MP_TAC CONTINUOUS_ON_LIFT_POW THEN REWRITE_TAC[LIFT_CMUL] THEN
    MATCH_MP_TAC CONTINUOUS_ON_MUL THEN ASM_REWRITE_TAC[o_DEF];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `drop(integral (:real^3)
      (\x:real^3. (if lift(x$3) IN interval[--lift H,lift H] then &1 else &0) %
                  lift(wan_dpart 1 (\y. smooth_bump e (&2 * e) (y - vec 0:real^2))
                                 (vector[x$1; x$2]) pow 2 +
                       wan_dpart 2 (\y. smooth_bump e (&2 * e) (y - vec 0:real^2))
                                 (vector[x$1; x$2]) pow 2)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRAL_DROP_LE THEN
    ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE; IN_UNIV] THEN
    X_GEN_TAC `z:real^3` THEN REWRITE_TAC[LIFT_DROP; DROP_CMUL] THEN
    ASM_CASES_TAC `(z:real^3) IN K` THENL
     [SUBGOAL_THEN `lift((z:real^3)$3) IN interval[--lift H,lift H]` (fun th -> REWRITE_TAC[th]) THENL
       [REWRITE_TAC[IN_INTERVAL_1; DROP_NEG; LIFT_DROP] THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `z:real^3` o check (is_forall o concl) o
          check (fun th -> can (find_term ((=) `H:real`)) (concl th))) THEN
        ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      REWRITE_TAC[REAL_MUL_LID; REAL_POW_MUL] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `wan_dpart i (\z. wan_acut e z) z pow 2` THEN CONJ_TAC THENL
       [GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
        ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN
        GEN_REWRITE_TAC RAND_CONV [GSYM(REAL_RAT_REDUCE_CONV `&1 pow 2`)] THEN
        MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[REAL_ABS_POS];
        ASM_REWRITE_TAC[]];
      ASM_SIMP_TAC[REAL_MUL_RZERO; REAL_POW_ZERO; ARITH] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
       [COND_CASES_TAC THEN REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_ADD THEN REWRITE_TAC[REAL_LE_POW_2]]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[DROP_CMUL; LIFT_DROP] THEN
  REWRITE_TAC[LIFT_ADD] THEN
  ASM_SIMP_TAC[INTEGRAL_ADD; DROP_ADD] THEN
  USE_THEN "L1" MP_TAC THEN USE_THEN "L2" MP_TAC THEN
  REPEAT DISCH_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&2 * H) * (C0 + C0)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_ADD2 THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[REAL_ARITH `(&2 * H) * (C0 + C0) = H * &4 * C0`; REAL_LE_REFL]]);;

let WAN_AXIS_NEGLIGIBLE = prove
 (`negligible {z:real^3 | z$1 = &0 /\ z$2 = &0} /\
   closed {z:real^3 | z$1 = &0 /\ z$2 = &0}`,
  CONJ_TAC THENL
   [MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN EXISTS_TAC `{z:real^3 | z$1 = &0}` THEN
    REWRITE_TAC[NEGLIGIBLE_STANDARD_HYPERPLANE] THEN SET_TAC[];
    REWRITE_TAC[SET_RULE `{z:real^3 | P z /\ Q z} = {z | P z} INTER {z | Q z}`] THEN
    MATCH_MP_TAC CLOSED_INTER THEN REWRITE_TAC[CLOSED_STANDARD_HYPERPLANE]]);;

let WAN_AXIS_EVENTUALLY = prove
 (`!z:real^3. ~(z$1 = &0 /\ z$2 = &0)
              ==> ?N. !n. N <= n
                          ==> &2 * inv(&n + &1) < norm(vector[z$1; z$2]:real^2) /\
                              (!i. wan_acut (inv(&n + &1)) z = &0 /\
                                   wan_dpart i (\z. wan_acut (inv(&n + &1)) z) z = &0)`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`&1`; `vec 0:real^2`; `vector[(z:real^3)$1; z$2]:real^2`] WAN_CUTOFF_SEQ) THEN
  REWRITE_TAC[REAL_LT_01; REAL_MUL_LID; VECTOR_SUB_RZERO] THEN ANTS_TAC THENL
   [REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2; VEC_COMPONENT] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN DISCH_TAC THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[] THEN GEN_TAC THEN
  SUBGOAL_THEN `&0 < inv(&n + &1)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_LT_INV_EQ] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [MP_TAC(SPEC `inv(&n + &1)` WAN_ACUT_FACTS) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC WAN_ACUT_DPART THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`inv(&n + &1)`; `i:num`]) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[IN_CBALL_0] THEN ASM_REAL_ARITH_TAC]);;

let WAN_AXIS_TUBE_L2 = prove
 (`!(u:real^3->real^K) k.
     compact k /\ u IN lspace k (&2)
     ==> (!n. (\z. if z IN k /\ norm(vector[z$1; z$2]:real^2) <= &2 * inv(&n + &1)
                   then lift(norm(u z) pow 2) else vec 0) integrable_on (:real^3)) /\
         ((\n. integral (:real^3)
                 (\z. if z IN k /\ norm(vector[z$1; z$2]:real^2) <= &2 * inv(&n + &1)
                      then lift(norm(u z) pow 2) else vec 0)) --> vec 0) sequentially`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(\z. lift(norm((u:real^3->real^K) z) pow 2)) absolutely_integrable_on k`
  ASSUME_TAC THENL
   [MATCH_MP_TAC NONNEGATIVE_ABSOLUTELY_INTEGRABLE THEN
    ASM_SIMP_TAC[WAN_LSPACE2_SQNORM_INTEGRABLE] THEN
    REWRITE_TAC[DIMINDEX_1; ARITH_RULE `1 <= i /\ i <= 1 <=> i = 1`] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[GSYM drop; LIFT_DROP; REAL_LE_POW_2];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. (\z. if z IN k /\ norm(vector[z$1; z$2]:real^2) <= &2 * inv(&n + &1)
             then lift(norm((u:real^3->real^K) z) pow 2) else vec 0)
          absolutely_integrable_on (:real^3)`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    SUBGOAL_THEN
     `(\z. if z IN k /\ norm(vector[z$1; z$2]:real^2) <= &2 * inv(&n + &1)
           then lift(norm((u:real^3->real^K) z) pow 2) else vec 0) =
      (\z. if z IN k INTER {z:real^3 | norm(vector[z$1; z$2]:real^2) <= &2 * inv(&n + &1)}
           then lift(norm(u z) pow 2) else vec 0)`
    SUBST1_TAC THENL [REWRITE_TAC[IN_INTER; IN_ELIM_THM]; ALL_TAC] THEN
    REWRITE_TAC[ABSOLUTELY_INTEGRABLE_RESTRICT_UNIV] THEN
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
    EXISTS_TAC `k:real^3->bool` THEN ASM_REWRITE_TAC[INTER_SUBSET] THEN
    MATCH_MP_TAC LEBESGUE_MEASURABLE_CLOSED THEN MATCH_MP_TAC CLOSED_INTER THEN
    ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN
    REWRITE_TAC[GSYM IN_CBALL_0] THEN
    MATCH_MP_TAC CONTINUOUS_CLOSED_PREIMAGE_UNIV THEN
    SIMP_TAC[CLOSED_CBALL; LINEAR_CONTINUOUS_AT; WAN_PROJ3_LINEAR];
    ALL_TAC] THEN
  ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE] THEN
  MP_TAC(ISPECL
   [`\n z. if z IN k /\ norm(vector[z$1; z$2]:real^2) <= &2 * inv(&n + &1)
           then lift(norm((u:real^3->real^K) z) pow 2) else vec 0`;
    `\z:real^3. vec 0:real^1`;
    `\z. if z IN k then lift(norm((u:real^3->real^K) z) pow 2) else vec 0`;
    `(:real^3)`; `{z:real^3 | z$1 = &0 /\ z$2 = &0}`] DOMINATED_CONVERGENCE_AE) THEN
  REWRITE_TAC[WAN_AXIS_NEGLIGIBLE; INTEGRAL_0] THEN ANTS_TAC THENL
   [ALL_TAC; SIMP_TAC[]] THEN
  ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[INTEGRABLE_RESTRICT_UNIV] THEN
    ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE];
    MAP_EVERY X_GEN_TAC [`n:num`; `z:real^3`] THEN DISCH_TAC THEN
    REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
    REWRITE_TAC[NORM_LIFT; LIFT_DROP; DROP_VEC; NORM_0; REAL_ABS_POW; REAL_ABS_NORM;
                REAL_LE_REFL; REAL_LE_POW_2] THEN
    ASM_MESON_TAC[];
    X_GEN_TAC `z:real^3` THEN REWRITE_TAC[IN_DIFF; IN_UNIV; IN_ELIM_THM] THEN DISCH_TAC THEN
    MATCH_MP_TAC LIM_EVENTUALLY THEN REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
    MP_TAC(SPEC `z:real^3` WAN_AXIS_EVENTUALLY) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN DISCH_TAC THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

let WAN_ACUT_CONT = prove
 (`!e. &0 < e
       ==> (\z. lift(wan_acut e z)) continuous_on (:real^3) /\
           (\z. lift(&1 - wan_acut e z)) continuous_on (:real^3) /\
           (!z. abs(&1 - wan_acut e z) <= &1)`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPEC `e:real` WAN_ACUT_FACTS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) /\ r ==> p /\ q /\ r`) THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN ASM_REWRITE_TAC[];
    DISCH_TAC THEN REWRITE_TAC[LIFT_SUB] THEN MATCH_MP_TAC CONTINUOUS_ON_SUB THEN
    ASM_REWRITE_TAC[CONTINUOUS_ON_CONST];
    GEN_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `z:real^3` o
      check (fun th -> is_conj(snd(dest_forall(concl th))))) THEN REAL_ARITH_TAC]);;

let WAN_AXIS_GOOD = prove
 (`!(s:real^3->bool) (h:real^3->real^K).
     lebesgue_measurable s /\ h absolutely_integrable_on s
     ==> ((\n. integral s (\z. (&1 - wan_acut (inv(&n + &1)) z) % h z)) --> integral s h)
         sequentially`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`\n z. (&1 - wan_acut (inv(&n + &1)) z) % (h:real^3->real^K) z`;
    `h:real^3->real^K`; `\z. lift(norm((h:real^3->real^K) z))`;
    `s:real^3->bool`; `{z:real^3 | z$1 = &0 /\ z$2 = &0}`] DOMINATED_CONVERGENCE_AE) THEN
  REWRITE_TAC[WAN_AXIS_NEGLIGIBLE] THEN ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `n:num` THEN MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
    SUBGOAL_THEN `&0 < inv(&n + &1)` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_LT_INV_EQ] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPEC `inv(&n + &1)` WAN_ACUT_CONT) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`\x y:real^K. drop x % y`;
                   `\z. lift(&1 - wan_acut (inv(&n + &1)) z)`;
                   `h:real^3->real^K`; `s:real^3->bool`]
                  ABSOLUTELY_INTEGRABLE_BOUNDED_MEASURABLE_PRODUCT) THEN
    REWRITE_TAC[BILINEAR_DROP_MUL; LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `(:real^3)` THEN ASM_REWRITE_TAC[SUBSET_UNIV];
      REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE] THEN EXISTS_TAC `&1` THEN
      ASM_REWRITE_TAC[REAL_LT_01; NORM_LIFT]];
    ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE; ABSOLUTELY_INTEGRABLE_NORM];
    MAP_EVERY X_GEN_TAC [`n:num`; `z:real^3`] THEN DISCH_TAC THEN
    REWRITE_TAC[LIFT_DROP; NORM_MUL] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
    SUBGOAL_THEN `&0 < inv(&n + &1)` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_LT_INV_EQ] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPEC `inv(&n + &1)` WAN_ACUT_CONT) THEN ASM_SIMP_TAC[];
    X_GEN_TAC `z:real^3` THEN REWRITE_TAC[IN_DIFF; IN_ELIM_THM] THEN STRIP_TAC THEN
    MATCH_MP_TAC LIM_EVENTUALLY THEN REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
    MP_TAC(SPEC `z:real^3` WAN_AXIS_EVENTUALLY) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN DISCH_TAC THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN ASM_REWRITE_TAC[] THEN
    SIMP_TAC[REAL_SUB_RZERO; VECTOR_MUL_LID]]);;

let WAN_AXIS_BAD_COMP = prove
 (`!(u:real^3->real^K) (phi:real^3->real) (chi:real^3->real) k K M H i j.
     compact k /\ compact K /\ k SUBSET K /\ &0 <= H /\ &0 <= M /\
     (\z. lift(chi z)) continuous_on (:real^3) /\ (!z. abs(chi z) <= &1) /\
     (!z. ~(z IN K) ==> chi z = &0) /\ (!z. z IN k ==> chi z = &1) /\
     (!z. z IN K ==> abs(z$3) <= H) /\
     u IN lspace k (&2) /\ (!z. abs(phi z) <= M) /\ (!z. ~(z IN k) ==> phi z = &0) /\
     (\z. lift(phi z * u z$j)) absolutely_integrable_on (:real^3)
     ==> ((\n. integral (:real^3)
                 (\z. lift(wan_dpart i (\z. wan_acut (inv(&n + &1)) z) z *
                           (phi z * u z$j))))
          --> vec 0) sequentially`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  X_CHOOSE_THEN `C1:real` STRIP_ASSUME_TAC WAN_ACUT_L2 THEN
  X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC WAN_ACUT_DPART THEN
  SUBGOAL_THEN `!n. &0 < inv(&n + &1) /\ inv(&n + &1) <= &1` ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[REAL_LT_INV_EQ] THEN CONJ_TAC THENL
     [REAL_ARITH_TAC; MATCH_MP_TAC REAL_INV_LE_1 THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n z. wan_dpart i (\z. wan_acut (inv(&n + &1)) z) z *
          ((phi:real^3->real) z * (u:real^3->real^K) z$j) =
          (wan_dpart i (\z. wan_acut (inv(&n + &1)) z) z * chi z) * (phi z * u z$j)`
  (fun th -> REWRITE_TAC[th]) THENL
   [REPEAT GEN_TAC THEN ASM_CASES_TAC `(z:real^3) IN k` THEN
    ASM_SIMP_TAC[REAL_MUL_RID; REAL_MUL_LZERO; REAL_MUL_RZERO];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`u:real^3->real^K`; `k:real^3->bool`] WAN_AXIS_TUBE_L2) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!n. (\x. if x IN {z:real^3 | z IN K /\ norm(vector[z$1; z$2]:real^2) <= &2 * inv(&n + &1)}
             then lift((if x IN k then M * norm((u:real^3->real^K) x) else &0) pow 2)
             else vec 0) =
        (\x. (M pow 2) %
             (if x IN k /\ norm(vector[x$1; x$2]:real^2) <= &2 * inv(&n + &1)
              then lift(norm(u x) pow 2) else vec 0))`
  (LABEL_TAC "EQ") THENL
   [GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM; IN_ELIM_THM] THEN X_GEN_TAC `x:real^3` THEN
    ASM_CASES_TAC `(x:real^3) IN k` THEN ASM_REWRITE_TAC[] THENL
     [SUBGOAL_THEN `(x:real^3) IN K` (fun th -> REWRITE_TAC[th]) THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      COND_CASES_TAC THEN REWRITE_TAC[VECTOR_MUL_RZERO; REAL_POW_MUL; LIFT_CMUL];
      COND_CASES_TAC THEN REWRITE_TAC[VECTOR_MUL_RZERO; REAL_POW_ZERO; ARITH; LIFT_NUM]];
    ALL_TAC] THEN
  MATCH_MP_TAC WAN_L2_SHRINKING_PRODUCT THEN
  MAP_EVERY EXISTS_TAC
   [`\z:real^3. if z IN k then M * norm((u:real^3->real^K) z) else &0`;
    `\n. {z:real^3 | z IN K /\ norm(vector[z$1; z$2]:real^2) <= &2 * inv(&n + &1)}`;
    `H * C1`] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `n:num` THEN REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_MESON_TAC[];
    MAP_EVERY X_GEN_TAC [`n:num`; `z:real^3`] THEN REWRITE_TAC[IN_ELIM_THM; DE_MORGAN_THM] THEN
    STRIP_TAC THENL
     [ASM_SIMP_TAC[REAL_MUL_RZERO];
      FIRST_X_ASSUM(MP_TAC o SPECL [`inv(&n + &1)`; `i:num`] o
        check (fun th -> can (find_term ((=) `B:real`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      SUBGOAL_THEN `wan_dpart i (\z. wan_acut (inv(&n + &1)) z) z = &0`
        (fun th -> REWRITE_TAC[th; REAL_MUL_LZERO]) THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_CBALL_0] THEN ASM_REAL_ARITH_TAC];
    X_GEN_TAC `n:num` THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
    MATCH_MP_TAC WAN_ABS_INT_CONT_MUL THEN EXISTS_TAC `B / inv(&n + &1)` THEN
    ASM_REWRITE_TAC[LEBESGUE_MEASURABLE_UNIV] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`inv(&n + &1)`; `i:num`] o
      check (fun th -> can (find_term ((=) `B:real`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN CONJ_TAC THENL
     [REWRITE_TAC[LIFT_CMUL] THEN MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
      ASM_REWRITE_TAC[o_DEF];
      X_GEN_TAC `z:real^3` THEN REWRITE_TAC[REAL_ABS_MUL] THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_ABS_POS]];
    X_GEN_TAC `z:real^3` THEN REWRITE_TAC[] THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC[REAL_MUL_LZERO; REAL_ABS_0;
                                                               REAL_LE_REFL] THEN
    REWRITE_TAC[REAL_ABS_MUL] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
    ASM_REWRITE_TAC[REAL_ABS_POS; COMPONENT_LE_NORM];
    USE_THEN "EQ" (fun th -> REWRITE_TAC[th]) THEN GEN_TAC THEN
    MATCH_MP_TAC INTEGRABLE_CMUL THEN ASM_REWRITE_TAC[];
    USE_THEN "EQ" (fun th -> REWRITE_TAC[th]) THEN ASM_SIMP_TAC[INTEGRAL_CMUL] THEN
    MATCH_MP_TAC LIM_NULL_CMUL THEN ASM_REWRITE_TAC[]]);;

let WAN_ACUT_DPART_BOUNDED = prove
 (`!n i. ?Bn. !z. abs(wan_dpart i (\z. wan_acut (inv(&n + &1)) z) z) <= Bn`,
  REPEAT GEN_TAC THEN
  X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC WAN_ACUT_DPART THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`inv(&n + &1)`; `i:num`]) THEN
  REWRITE_TAC[REAL_LT_INV_EQ; REAL_ARITH `&0 < &n + &1`] THEN
  MESON_TAC[]);;

let WAN_AXIS_BAD = prove
 (`!(s:real^3->bool) (u:real^3->real^K) (phi:real^3->real) i.
     open s /\ wan_l2loc s u /\ wan_test s phi
     ==> ((\n. integral s (\z. wan_dpart i (\z. wan_acut (inv(&n + &1)) z) z %
                               (phi z % u z))) --> vec 0) sequentially`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o REWRITE_RULE[wan_test]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `k:real^3->bool` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `(u:real^3->real^K) IN lspace k (&2)` ASSUME_TAC THENL
   [ASM_MESON_TAC[wan_l2loc]; ALL_TAC] THEN
  MP_TAC(ISPECL [`(:real^3)`; `k:real^3->bool`] WAN_SMOOTH_URYSOHN) THEN
  ASM_REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV] THEN
  DISCH_THEN(X_CHOOSE_THEN `chi:real^3->real`
    (CONJUNCTS_THEN2 (LABEL_TAC "CT") (CONJUNCTS_THEN2 (LABEL_TAC "CB") (LABEL_TAC "C1")))) THEN
  USE_THEN "CT" (MP_TAC o REWRITE_RULE[wan_test]) THEN
  DISCH_THEN(X_CHOOSE_THEN `K:real^3->bool`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "CK"))) o CONJUNCT2) THEN
  SUBGOAL_THEN `(\z. lift((chi:real^3->real) z)) continuous_on (:real^3)` ASSUME_TAC THENL
   [USE_THEN "CT" (MP_TAC o CONJUNCT1 o SPEC `0` o MATCH_MP WAN_TEST_CONTINUOUS) THEN
    REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `k SUBSET (K:real^3->bool)` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET] THEN X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    USE_THEN "C1" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(z:real^3) IN k`))) THEN
    USE_THEN "CK" (fun th -> MP_TAC(MATCH_MP th (ASSUME `~((z:real^3) IN K)`))) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `?H. &0 <= H /\ !z:real^3. z IN K ==> abs(z$3) <= H` STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED o
      check (fun th -> concl th = `compact (K:real^3->bool)`)) THEN
    REWRITE_TAC[BOUNDED_POS] THEN DISCH_THEN(X_CHOOSE_THEN `R:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `R:real` THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `norm(z:real^3)` THEN ASM_SIMP_TAC[COMPONENT_LE_NORM];
    ALL_TAC] THEN
  SUBGOAL_THEN `?M. &0 <= M /\ !z:real^3. abs((phi:real^3->real) z) <= M` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\z:real^3. lift((phi:real^3->real) z)`; `k:real^3->bool`]
                  WAN_CONT_SUPPORT_BOUNDED) THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON; LIFT_NUM; NORM_LIFT] THEN
    DISCH_THEN(X_CHOOSE_TAC `M:real`) THEN EXISTS_TAC `M:real` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `abs((phi:real^3->real) (vec 0))` THEN
    ASM_REWRITE_TAC[REAL_ABS_POS];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\z. (phi:real^3->real) z % (u:real^3->real^K) z) absolutely_integrable_on s`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`s:real^3->bool`; `phi:real^3->real`; `u:real^3->real^K`]
                  WAN_TEST_PAIRING) THEN
    ASM_SIMP_TAC[WAN_L2LOC_IMP_LLOC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\z. (phi:real^3->real) z % (u:real^3->real^K) z)
                  absolutely_integrable_on (:real^3)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\z. (phi:real^3->real) z % (u:real^3->real^K) z`; `k:real^3->bool`;
                   `s:real^3->bool`; `(:real^3)`] WAN_ABS_INTEGRABLE_SUPPORT_SUBSET) THEN
    ASM_SIMP_TAC[SUBSET_UNIV; VECTOR_MUL_LZERO];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. (\z. wan_dpart i (\z. wan_acut (inv(&n + &1)) z) z %
             ((phi:real^3->real) z % (u:real^3->real^K) z)) absolutely_integrable_on s`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`n:num`; `i:num`] WAN_ACUT_DPART_BOUNDED) THEN
    DISCH_THEN(X_CHOOSE_TAC `Bn:real`) THEN
    X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC WAN_ACUT_DPART THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`inv(&n + &1)`; `i:num`]) THEN
    REWRITE_TAC[REAL_LT_INV_EQ; REAL_ARITH `&0 < &n + &1`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`\x y:real^K. drop x % y`;
                   `\z. lift(wan_dpart i (\z. wan_acut (inv(&n + &1)) z) z)`;
                   `\z. (phi:real^3->real) z % (u:real^3->real^K) z`; `s:real^3->bool`]
                  ABSOLUTELY_INTEGRABLE_BOUNDED_MEASURABLE_PRODUCT) THEN
    REWRITE_TAC[BILINEAR_DROP_MUL; LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
      ASM_SIMP_TAC[LEBESGUE_MEASURABLE_OPEN] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `(:real^3)` THEN ASM_REWRITE_TAC[SUBSET_UNIV];
      REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE; NORM_LIFT] THEN
      EXISTS_TAC `abs Bn + &1` THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      GEN_TAC THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `x:real^3` o
        check (fun th -> can (find_term ((=) `Bn:real`)) (concl th))) THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[LIM_COMPONENTWISE_LIFT] THEN
  X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  REWRITE_TAC[VEC_COMPONENT; LIFT_NUM] THEN
  SUBGOAL_THEN
   `!n. lift((integral s (\z. wan_dpart i (\z. wan_acut (inv(&n + &1)) z) z %
                               ((phi:real^3->real) z % (u:real^3->real^K) z)))$j) =
        integral (:real^3)
          (\z. lift(wan_dpart i (\z. wan_acut (inv(&n + &1)) z) z * (phi z * u z$j)))`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN
    ASM_SIMP_TAC[INTEGRAL_COMPONENT; ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE; LIFT_DROP;
                 VECTOR_MUL_COMPONENT] THEN
    MATCH_MP_TAC WAN_INTEGRAL_SUPPORT_SUBSET THEN EXISTS_TAC `k:real^3->bool` THEN
    ASM_SIMP_TAC[SUBSET_UNIV; REAL_MUL_LZERO; REAL_MUL_RZERO; LIFT_NUM];
    ALL_TAC] THEN
  MATCH_MP_TAC WAN_AXIS_BAD_COMP THEN
  MAP_EVERY EXISTS_TAC [`chi:real^3->real`; `k:real^3->bool`; `K:real^3->bool`;
                        `M:real`; `H:real`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [GEN_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `z:real^3` o
      check (fun th -> can (find_term ((=) `chi:real^3->real`)) (concl th) &&
                       is_forall(concl th) && is_conj(snd(dest_forall(concl th))))) THEN
    REAL_ARITH_TAC;
    MP_TAC(ISPECL [`\z. (phi:real^3->real) z % (u:real^3->real^K) z`; `(:real^3)`]
                  ABSOLUTELY_INTEGRABLE_COMPONENTWISE) THEN
    ASM_REWRITE_TAC[VECTOR_MUL_COMPONENT] THEN DISCH_THEN(MP_TAC o SPEC `j:num`) THEN
    ASM_REWRITE_TAC[]]);;

let WAN_DPART_ONE_SUB = prove
 (`!(c:real^N->real) i x.
     smooth_map_on (:real^N) (\y. lift(c y))
     ==> wan_dpart i (\y. &1 - c y) x = --(wan_dpart i c x)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[wan_dpart; LIFT_SUB] THEN
  SUBGOAL_THEN
   `((\y. lift(&1) - lift((c:real^N->real) y)) has_derivative
     (\h. vec 0 - frechet_derivative (\y. lift(c y)) (at x) h)) (at x)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HAS_DERIVATIVE_SUB THEN REWRITE_TAC[HAS_DERIVATIVE_CONST] THEN
    REWRITE_TAC[ETA_AX; GSYM FRECHET_DERIVATIVE_WORKS] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `(:real^N)` THEN
    ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV];
    FIRST_X_ASSUM(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
    REWRITE_TAC[DROP_SUB; DROP_VEC] THEN REAL_ARITH_TAC]);;

let WAN_ABS_INT_CONT_SMUL = prove
 (`!(s:real^N->bool) (c:real^N->real) (h:real^N->real^K) B.
     lebesgue_measurable s /\ (\x. lift(c x)) continuous_on (:real^N) /\
     (!x. abs(c x) <= B) /\ h absolutely_integrable_on s
     ==> (\x. c x % h x) absolutely_integrable_on s`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\x y:real^K. drop x % y`; `\x:real^N. lift(c x)`;
                 `h:real^N->real^K`; `s:real^N->bool`]
                ABSOLUTELY_INTEGRABLE_BOUNDED_MEASURABLE_PRODUCT) THEN
  REWRITE_TAC[BILINEAR_DROP_MUL; LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `(:real^N)` THEN ASM_REWRITE_TAC[SUBSET_UNIV];
    REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE; NORM_LIFT] THEN
    EXISTS_TAC `abs B + &1` THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `B:real` THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]);;

let WAN_ACUT_TEST = prove
 (`!(s:real^3->bool) phi n.
     wan_test s phi
     ==> wan_test (s DIFF {z:real^3 | z$1 = &0 /\ z$2 = &0})
                  (\z. (&1 - wan_acut (inv(&n + &1)) z) * phi z) /\
         (!i z. wan_dpart i (\z. (&1 - wan_acut (inv(&n + &1)) z) * phi z) z =
                --(wan_dpart i (\z. wan_acut (inv(&n + &1)) z) z) * phi z +
                (&1 - wan_acut (inv(&n + &1)) z) * wan_dpart i phi z)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wan_test] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `k:real^3->bool` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `&0 < inv(&n + &1)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_LT_INV_EQ] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPEC `inv(&n + &1)` WAN_ACUT_FACTS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `smooth_map_on (:real^3) (\z. lift(&1 - wan_acut (inv(&n + &1)) z))`
  ASSUME_TAC THENL
   [REWRITE_TAC[LIFT_SUB] THEN MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN
    ASM_REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_CONST];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\z. &1 - wan_acut (inv(&n + &1)) z`; `phi:real^3->real`]
                WAN_DPART_MUL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN REPEAT CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`1`; `vec 0:real^3`]) THEN SIMP_TAC[];
    EXISTS_TAC `k DIFF {z:real^3 | norm(vector[z$1; z$2]:real^2) < inv(&n + &1)}` THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_DIFF THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[GSYM IN_BALL_0] THEN MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE_UNIV THEN
      SIMP_TAC[OPEN_BALL; LINEAR_CONTINUOUS_AT; WAN_PROJ3_LINEAR];
      REWRITE_TAC[SUBSET; IN_DIFF; IN_ELIM_THM; REAL_NOT_LT] THEN
      X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN CONJ_TAC THENL
       [ASM SET_TAC[];
        DISCH_TAC THEN UNDISCH_TAC `inv(&n + &1) <= norm(vector[(z:real^3)$1; z$2]:real^2)` THEN
        ASM_REWRITE_TAC[] THEN
        SUBGOAL_THEN `vector[&0; &0]:real^2 = vec 0` SUBST1_TAC THENL
         [SIMP_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2; VEC_COMPONENT]; ALL_TAC] THEN
        REWRITE_TAC[NORM_0] THEN ASM_REAL_ARITH_TAC];
      X_GEN_TAC `z:real^3` THEN REWRITE_TAC[IN_DIFF; IN_ELIM_THM; DE_MORGAN_THM] THEN
      STRIP_TAC THEN ASM_SIMP_TAC[REAL_MUL_RZERO] THEN
      SUBGOAL_THEN `wan_acut (inv(&n + &1)) z = &1` SUBST1_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]];
    REPEAT GEN_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`\z. wan_acut (inv(&n + &1)) z`; `i:num`; `z:real^3`] WAN_DPART_ONE_SUB) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REFL_TAC]);;

let WAN_REMOVABLE_AXIS3 = prove
 (`!(s:real^3->bool) i (u:real^3->real^K) v.
     open s /\ wan_l2loc s u /\ wan_lloc s v /\
     wan_wpd (s DIFF {z:real^3 | z$1 = &0 /\ z$2 = &0}) i u v
     ==> wan_wpd s i u v`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC))) THEN
  REWRITE_TAC[wan_wpd] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC) (LABEL_TAC "W"))) THEN
  ASM_SIMP_TAC[WAN_L2LOC_IMP_LLOC] THEN
  X_GEN_TAC `phi:real^3->real` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!f:real^3->real^K.
      integral (s DIFF {z:real^3 | z$1 = &0 /\ z$2 = &0}) f = integral s f`
  (LABEL_TAC "SP") THENL
   [GEN_TAC THEN MATCH_MP_TAC INTEGRAL_SPIKE_SET THEN MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
    EXISTS_TAC `{z:real^3 | z$1 = &0 /\ z$2 = &0}` THEN
    REWRITE_TAC[WAN_AXIS_NEGLIGIBLE] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `wan_lloc s (u:real^3->real^K)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[WAN_L2LOC_IMP_LLOC]; ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `phi:real^3->real`; `u:real^3->real^K`] WAN_TEST_PAIRING) THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `phi:real^3->real`; `v:real^3->real^K`] WAN_TEST_PAIRING) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o SPEC `i:num`)) THEN
  SUBGOAL_THEN `lebesgue_measurable (s:real^3->bool)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[LEBESGUE_MEASURABLE_OPEN]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. integral s (\z. (&1 - wan_acut (inv(&n + &1)) z) %
                        (wan_dpart i phi z % (u:real^3->real^K) z)) -
        integral s (\z. wan_dpart i (\z. wan_acut (inv(&n + &1)) z) z % (phi z % u z)) =
        --(integral s (\z. (&1 - wan_acut (inv(&n + &1)) z) % (phi z % (v:real^3->real^K) z)))`
  ASSUME_TAC THENL
   [X_GEN_TAC `n:num` THEN
    SUBGOAL_THEN `&0 < inv(&n + &1)` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_LT_INV_EQ] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPEC `inv(&n + &1)` WAN_ACUT_CONT) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`n:num`; `i:num`] WAN_ACUT_DPART_BOUNDED) THEN
    DISCH_THEN(X_CHOOSE_TAC `Bn:real`) THEN
    X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC WAN_ACUT_DPART THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`inv(&n + &1)`; `i:num`]) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN
    MP_TAC(ISPECL [`s:real^3->bool`; `phi:real^3->real`; `n:num`] WAN_ACUT_TEST) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "D")) THEN
    USE_THEN "W" (MP_TAC o SPEC `\z. (&1 - wan_acut (inv(&n + &1)) z) * (phi:real^3->real) z`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    USE_THEN "SP" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "D" (fun th -> REWRITE_TAC[th]) THEN
    SUBGOAL_THEN
     `(\x. (--(wan_dpart i (\z. wan_acut (inv(&n + &1)) z) x) * phi x +
            (&1 - wan_acut (inv(&n + &1)) x) * wan_dpart i phi x) % (u:real^3->real^K) x) =
      (\x. (&1 - wan_acut (inv(&n + &1)) x) % (wan_dpart i phi x % u x) -
           wan_dpart i (\z. wan_acut (inv(&n + &1)) z) x % (phi x % u x))`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN
     `(\x. ((&1 - wan_acut (inv(&n + &1)) x) * (phi:real^3->real) x) % (v:real^3->real^K) x) =
      (\x. (&1 - wan_acut (inv(&n + &1)) x) % (phi x % v x))`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; VECTOR_MUL_ASSOC]; ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC INTEGRAL_SUB THEN CONJ_TAC THEN
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
    MATCH_MP_TAC WAN_ABS_INT_CONT_SMUL THENL
     [EXISTS_TAC `&1`; EXISTS_TAC `Bn:real`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `\z. wan_dpart i phi z % (u:real^3->real^K) z`]
                WAN_AXIS_GOOD) THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `\z. (phi:real^3->real) z % (v:real^3->real^K) z`]
                WAN_AXIS_GOOD) THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `u:real^3->real^K`; `phi:real^3->real`; `i:num`]
                WAN_AXIS_BAD) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  MATCH_MP_TAC(ISPEC `sequentially` LIM_UNIQUE) THEN
  EXISTS_TAC
   `\n. integral s (\z. (&1 - wan_acut (inv(&n + &1)) z) %
                        (wan_dpart i phi z % (u:real^3->real^K) z)) -
        integral s (\z. wan_dpart i (\z. wan_acut (inv(&n + &1)) z) z % (phi z % u z))` THEN
  REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN CONJ_TAC THENL
   [GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) [GSYM VECTOR_SUB_RZERO] THEN
    MATCH_MP_TAC LIM_SUB THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LIM_NEG THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Direction (B) of S2_STEREO: planar weak partials of u o sigma give weak  *)
(* partials of the radial extension on the shell minus the positive axis    *)
(* (chain rule through the inverse chart), square integrable by the         *)
(* Parseval relation and the change of variables; the axis is removable.    *)
(* ------------------------------------------------------------------------- *)

let WAN_L2LOC_EQ_ON = prove
 (`!(s:real^N->bool) (f:real^N->real^K) g.
     wan_l2loc s f /\ (!x. x IN s ==> g x = f x) ==> wan_l2loc s g`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wan_l2loc] THEN STRIP_TAC THEN
  X_GEN_TAC `k:real^N->bool` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `k:real^N->bool`) THEN
  ASM_REWRITE_TAC[lspace; IN_ELIM_THM] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!x. x IN k ==> (f:real^N->real^K) x = g x` ASSUME_TAC THENL
   [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC MEASURABLE_ON_EQ THEN EXISTS_TAC `f:real^N->real^K` THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC INTEGRABLE_EQ THEN
    EXISTS_TAC `\x. lift(norm((f:real^N->real^K) x) rpow &2)` THEN ASM_SIMP_TAC[]]);;

let WAN_S2_B_SLAB = prove
 (`!(w:real^2->real^K) (v:num->real^2->real^K).
     wan_lloc (:real^2) w /\
     (!i. 1 <= i /\ i <= 2 ==> v i IN lspace (:real^2) (&2) /\ wan_wpd (:real^2) i w (v i))
     ==> !i. 1 <= i /\ i <= 3
             ==> wan_wpd {x:real^3 | &1 / &2 < x$3 /\ x$3 < &2} i (\x. w(vector[x$1; x$2]))
                   (\x. if i = 3 then vec 0 else v i (vector[x$1; x$2])) /\
                 wan_l2loc {x:real^3 | &1 / &2 < x$3 /\ x$3 < &2}
                   (\x. if i = 3 then vec 0 else v i (vector[x$1; x$2]))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `i:num` THEN
  REWRITE_TAC[ARITH_RULE `1 <= i /\ i <= 3 <=> i = 3 \/ (1 <= i /\ i <= 2)`] THEN
  STRIP_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC WAN_WPD_PROJ3_VERT THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[wan_l2loc] THEN SIMP_TAC[LSPACE_0; REAL_OF_NUM_EQ; ARITH]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(i = 3)` (fun th -> REWRITE_TAC[th]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC WAN_WPD_PROJ3 THEN ASM_REWRITE_TAC[ETA_AX] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[wan_l2loc] THEN X_GEN_TAC `k:real^3->bool` THEN STRIP_TAC THEN
  REWRITE_TAC[lspace; IN_ELIM_THM; RPOW_POW] THEN CONJ_TAC THENL
   [MP_TAC(ISPEC `(v:num->real^2->real^K) i` WAN_LLOC_PROJ3) THEN
    ASM_SIMP_TAC[WAN_LSPACE2_IMP_LLOC] THEN REWRITE_TAC[wan_lloc] THEN
    DISCH_THEN(MP_TAC o SPEC `k:real^3->bool`) THEN ASM_REWRITE_TAC[SUBSET_UNIV] THEN
    SIMP_TAC[ABSOLUTELY_INTEGRABLE_MEASURABLE];
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
    EXISTS_TAC `{x:real^3 | &1 / &2 < x$3 /\ x$3 < &2}` THEN
    ASM_SIMP_TAC[LEBESGUE_MEASURABLE_COMPACT] THEN
    MP_TAC(ISPECL [`(v:num->real^2->real^K) i`; `&1 / &2`; `&2`] WAN_PROJ3_SQ_CONV) THEN
    ASM_SIMP_TAC[REAL_ARITH `&1 / &2 < &2`]]);;

let WAN_S2_B_L2LOC = prove
 (`!(u:real^3->real^K).
     wan_rext u IN lspace wan_shell (&2)
     ==> wan_l2loc {x:real^3 | &1 / &2 < x$3 /\ x$3 < &2}
           (\x. u(stereo2_n_inv(vector[x$1; x$2])))`,
  GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC WAN_L2LOC_EQ_ON THEN
  EXISTS_TAC `\x:real^3. wan_rext (u:real^3->real^K) (wan_nch x)` THEN CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC WAN_REXT_NCH THEN ASM_REAL_ARITH_TAC] THEN
  REWRITE_TAC[wan_l2loc] THEN X_GEN_TAC `k:real^3->bool` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`{z:real^3 | &1 / &2 < norm z /\ norm z < &2 /\ z$3 < norm z}`;
                 `{x:real^3 | &1 / &2 < x$3 /\ x$3 < &2}`; `wan_nch`; `wan_nchi`;
                 `k:real^3->bool`] WAN_DIFFEO_LOCAL_L1) THEN
  ASM_REWRITE_TAC[WAN_NCH_DIFFEO_HYP] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `C:real` (ASSUME_TAC o CONJUNCT2)))) THEN
  SUBGOAL_THEN `wan_rext (u:real^3->real^K) IN lspace (IMAGE wan_nch k) (&2)` ASSUME_TAC THENL
   [MATCH_MP_TAC LSPACE_SUBSET THEN EXISTS_TAC `wan_shell` THEN
    ASM_SIMP_TAC[LEBESGUE_MEASURABLE_COMPACT] THEN
    MP_TAC WAN_SHELL_NCH THEN ASM SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[lspace; IN_ELIM_THM; RPOW_POW] THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `wan_rext (u:real^3->real^K)`) THEN ANTS_TAC THENL
     [MP_TAC(ISPECL [`IMAGE wan_nch k`; `wan_rext (u:real^3->real^K)`]
                     WAN_LSPACE2_IMP_LLOC) THEN
      ASM_REWRITE_TAC[wan_lloc] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[SUBSET_REFL];
      SIMP_TAC[ABSOLUTELY_INTEGRABLE_MEASURABLE]];
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
    MP_TAC(ISPECL [`{z:real^3 | &1 / &2 < norm z /\ norm z < &2 /\ z$3 < norm z}`;
                   `{x:real^3 | &1 / &2 < x$3 /\ x$3 < &2}`; `wan_nch`; `wan_nchi`;
                   `k:real^3->bool`] (INST_TYPE [`:1`,`:K`] WAN_DIFFEO_LOCAL_L1)) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[WAN_NCH_DIFFEO_HYP]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `C1:real` (MP_TAC o
      SPEC `\z:real^3. lift(norm(wan_rext (u:real^3->real^K) z) pow 2)` o CONJUNCT2) o
      CONJUNCT2 o CONJUNCT2) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
    MATCH_MP_TAC NONNEGATIVE_ABSOLUTELY_INTEGRABLE THEN CONJ_TAC THENL
     [REWRITE_TAC[DIMINDEX_1; ARITH_RULE `1 <= i /\ i <= 1 <=> i = 1`] THEN
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[GSYM drop; LIFT_DROP; REAL_LE_POW_2];
      MATCH_MP_TAC WAN_LSPACE2_SQNORM_INTEGRABLE THEN ASM_REWRITE_TAC[ETA_AX]]]);;

let WAN_S2_B_CHAIN = prove
 (`!(u:real^3->real^K) (v:num->real^2->real^K).
     wan_rext u IN lspace wan_shell (&2) /\
     wan_lloc (:real^2) (\y. u(stereo2_n_inv y)) /\
     (!i. 1 <= i /\ i <= 2
          ==> v i IN lspace (:real^2) (&2) /\
              wan_wpd (:real^2) i (\y. u(stereo2_n_inv y)) (v i))
     ==> !j. 1 <= j /\ j <= 3
             ==> wan_wpd {z:real^3 | &1 / &2 < norm z /\ norm z < &2 /\ z$3 < norm z} j
                   (wan_rext u)
                   (\z. vsum(1..3) (\i. frechet_derivative wan_nchi (at z) (basis j)$i %
                                        (if i = 3 then vec 0
                                         else v i (vector[wan_nchi z$1; wan_nchi z$2]))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`\y:real^2. (u:real^3->real^K)(stereo2_n_inv y)`; `v:num->real^2->real^K`]
                WAN_S2_B_SLAB) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC WAN_WPD_EQ_ON THEN
  EXISTS_TAC `\z:real^3. (u:real^3->real^K)(stereo2_n_inv(vector[wan_nchi z$1; wan_nchi z$2]))` THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`{x:real^3 | &1 / &2 < x$3 /\ x$3 < &2}`;
                   `{z:real^3 | &1 / &2 < norm z /\ norm z < &2 /\ z$3 < norm z}`;
                   `wan_nchi`; `wan_nch`;
                   `\x:real^3. (u:real^3->real^K)(stereo2_n_inv(vector[x$1; x$2]))`;
                   `\i x:real^3. if i = 3 then vec 0:real^K
                                 else (v:num->real^2->real^K) i (vector[x$1; x$2])`;
                   `j:num`] WAN_DIFFEO_WPD) THEN
    REWRITE_TAC[DIMINDEX_3; WAN_NCH_DIFFEO_HYP] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_SIMP_TAC[WAN_S2_B_L2LOC];
    REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
    MP_TAC(CONJUNCT2 WAN_NCH_INV) THEN DISCH_THEN(MP_TAC o SPEC `z:real^3`) THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`u:real^3->real^K`; `wan_nchi z`] WAN_REXT_NCH) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[]]);;

let WAN_S2_B_L2 = prove
 (`!(u:real^3->real^K) (v:num->real^2->real^K).
     wan_rext u IN lspace wan_shell (&2) /\
     wan_lloc (:real^2) (\y. u(stereo2_n_inv y)) /\
     (!i. 1 <= i /\ i <= 2
          ==> v i IN lspace (:real^2) (&2) /\
              wan_wpd (:real^2) i (\y. u(stereo2_n_inv y)) (v i))
     ==> !j. 1 <= j /\ j <= 3
             ==> (\z. vsum(1..3) (\i. frechet_derivative wan_nchi (at z) (basis j)$i %
                                      (if i = 3 then vec 0
                                       else v i (vector[wan_nchi z$1; wan_nchi z$2]))))
                 IN lspace {z:real^3 | &1 / &2 < norm z /\ norm z < &2 /\ z$3 < norm z} (&2)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> LABEL_TAC "CH" (MATCH_MP WAN_S2_B_CHAIN th) THEN STRIP_ASSUME_TAC th) THEN
  ABBREV_TAC
   `V = \j z. vsum(1..3) (\i. frechet_derivative wan_nchi (at z) (basis j)$i %
                              (if i = 3 then vec 0:real^K
                               else (v:num->real^2->real^K) i
                                      (vector[wan_nchi z$1; wan_nchi z$2])))` THEN
  SUBGOAL_THEN
   `!j z. vsum(1..3) (\i. frechet_derivative wan_nchi (at z) (basis j)$i %
                          (if i = 3 then vec 0:real^K
                           else (v:num->real^2->real^K) i (vector[wan_nchi z$1; wan_nchi z$2]))) =
          (V:num->real^3->real^K) j z`
  (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th] THEN LABEL_TAC "VD" th) THENL
   [EXPAND_TAC "V" THEN REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!j. 1 <= j /\ j <= 3
        ==> (\z. (V:num->real^3->real^K) j z) measurable_on
            {z:real^3 | &1 / &2 < norm z /\ norm z < &2 /\ z$3 < norm z}`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC WAN_LLOC_MEASURABLE THEN
    REWRITE_TAC[WAN_NCH_OPEN] THEN
    REMOVE_THEN "CH" (MP_TAC o SPEC `j:num`) THEN ASM_SIMP_TAC[wan_wpd];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\z. lift(sum(1..3) (\j. norm((V:num->real^3->real^K) j z) pow 2)))
      absolutely_integrable_on {z:real^3 | &1 / &2 < norm z /\ norm z < &2 /\ z$3 < norm z}`
  ASSUME_TAC THENL
   [REWRITE_TAC[WAN_NCH_COV] THEN MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_EQ THEN
    EXISTS_TAC
     `\x:real^3. lift(norm((v:num->real^2->real^K) 1 (vector[x$1; x$2])) pow 2) +
                 lift(norm(v 2 (vector[x$1; x$2])) pow 2)` THEN
    CONJ_TAC THENL
     [X_GEN_TAC `x:real^3` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
      MP_TAC(CONJUNCT1 WAN_NCH_INV) THEN DISCH_THEN(MP_TAC o SPEC `x:real^3`) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`wan_nch x`;
                     `\i. if i = 3 then vec 0:real^K
                          else (v:num->real^2->real^K) i
                                 (vector[wan_nchi(wan_nch x)$1; wan_nchi(wan_nch x)$2])`]
                    WAN_NCHI_PARSEVAL) THEN
      REWRITE_TAC[] THEN USE_THEN "VD" (fun th -> REWRITE_TAC[th]) THEN
      ASM_REWRITE_TAC[ARITH] THEN
      DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[NORM_0; REAL_POW_ZERO; ARITH; REAL_ADD_RID; GSYM LIFT_ADD; GSYM LIFT_CMUL;
                  LIFT_EQ] THEN
      MP_TAC(SPEC `x:real^3` WAN_NCHJ_POS) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      CONV_TAC REAL_FIELD;
      MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_ADD THEN CONJ_TAC THENL
       [MP_TAC(ISPECL [`(v:num->real^2->real^K) 1`; `&1 / &2`; `&2`] WAN_PROJ3_SQ_CONV);
        MP_TAC(ISPECL [`(v:num->real^2->real^K) 2`; `&1 / &2`; `&2`] WAN_PROJ3_SQ_CONV)] THEN
      ASM_SIMP_TAC[REAL_ARITH `&1 / &2 < &2`; ARITH]];
    ALL_TAC] THEN
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  REWRITE_TAC[lspace; IN_ELIM_THM; RPOW_POW] THEN ASM_SIMP_TAC[] THEN
  MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
  MATCH_MP_TAC MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_ABSOLUTELY_INTEGRABLE THEN
  EXISTS_TAC `\z. lift(sum(1..3) (\j. norm((V:num->real^3->real^K) j z) pow 2))` THEN
  ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE] THEN CONJ_TAC THENL
   [MATCH_MP_TAC MEASURABLE_ON_LIFT_POW THEN REWRITE_TAC[ARITH] THEN
    MATCH_MP_TAC MEASURABLE_ON_NORM THEN ASM_SIMP_TAC[];
    X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    REWRITE_TAC[NORM_LIFT; LIFT_DROP; REAL_ABS_POW; REAL_ABS_NORM; SUM_3] THEN
    MP_TAC(SPEC `norm((V:num->real^3->real^K) 1 z)` REAL_LE_POW_2) THEN
    MP_TAC(SPEC `norm((V:num->real^3->real^K) 2 z)` REAL_LE_POW_2) THEN
    MP_TAC(SPEC `norm((V:num->real^3->real^K) 3 z)` REAL_LE_POW_2) THEN
    UNDISCH_TAC `1 <= j /\ j <= 3` THEN
    REWRITE_TAC[ARITH_RULE `1 <= j /\ j <= 3 <=> j = 1 \/ j = 2 \/ j = 3`] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]);;

let WAN_SHELL_OPEN_AXIS = prove
 (`open wan_shell /\
   wan_shell DIFF {z:real^3 | z$1 = &0 /\ z$2 = &0} SUBSET
   {z:real^3 | &1 / &2 < norm z /\ norm z < &2 /\ z$3 < norm z} /\
   negligible(wan_shell DIFF {z:real^3 | &1 / &2 < norm z /\ norm z < &2 /\ z$3 < norm z}
              UNION
              {z:real^3 | &1 / &2 < norm z /\ norm z < &2 /\ z$3 < norm z} DIFF wan_shell)`,
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[wan_shell; SET_RULE `{z:real^3 | P z /\ Q z} = {z | P z} INTER {z | Q z}`] THEN
    MATCH_MP_TAC OPEN_INTER THEN CONJ_TAC THEN MATCH_MP_TAC WAN_OPEN_REAL_LT THEN
    REWRITE_TAC[CONTINUOUS_CONST] THEN GEN_TAC THEN
    MATCH_MP_TAC CONTINUOUS_LIFT_NORM_COMPOSE THEN REWRITE_TAC[CONTINUOUS_AT_ID];
    REWRITE_TAC[SUBSET; wan_shell; IN_DIFF; IN_ELIM_THM] THEN X_GEN_TAC `z:real^3` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    SUBGOAL_THEN `norm(z:real^3) pow 2 <= (z$3) pow 2` MP_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[NORM_POS_LE]; ALL_TAC] THEN
    REWRITE_TAC[NORM_POW_2; DOT_3] THEN
    MP_TAC(SPEC `(z:real^3)$2` REAL_LE_SQUARE) THEN
    MP_TAC(SPEC `(z:real^3)$1` REAL_LE_SQUARE) THEN
    REWRITE_TAC[REAL_POW_2] THEN REPEAT DISCH_TAC THEN
    SUBGOAL_THEN `(z:real^3)$1 * z$1 = &0 /\ z$2 * z$2 = &0` MP_TAC THENL
     [CONJ_TAC THEN ASM_REAL_ARITH_TAC; REWRITE_TAC[REAL_ENTIRE] THEN ASM_MESON_TAC[]];
    MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
    EXISTS_TAC `wan_shell DIFF {z:real^3 | &1 / &2 < norm z /\ norm z < &2 /\ z$3 < norm z}` THEN
    REWRITE_TAC[WAN_SHELL_NCH] THEN MP_TAC WAN_SHELL_NCH THEN SET_TAC[]]);;

let WAN_S2_STEREO_B = prove
 (`!(u:real^3->real^K).
     wan_rext u IN lspace wan_shell (&2) /\
     wan_lloc (:real^2) (\y. u(stereo2_n_inv y)) /\
     (!i. 1 <= i /\ i <= 2
          ==> ?v. v IN lspace (:real^2) (&2) /\
                  wan_wpd (:real^2) i (\y. u(stereo2_n_inv y)) v)
     ==> wan_s2_w12 u`,
  GEN_TAC THEN REWRITE_TAC[RIGHT_IMP_EXISTS_THM; SKOLEM_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_TAC `v:num->real^2->real^K`))) THEN
  MP_TAC(ISPECL [`u:real^3->real^K`; `v:num->real^2->real^K`] WAN_S2_B_CHAIN) THEN
  MP_TAC(ISPECL [`u:real^3->real^K`; `v:num->real^2->real^K`] WAN_S2_B_L2) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[wan_s2_w12; wan_w12; DIMINDEX_3] THEN
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  EXISTS_TAC
   `\z. vsum(1..3) (\i. frechet_derivative wan_nchi (at z) (basis j)$i %
                        (if i = 3 then vec 0:real^K
                         else (v:num->real^2->real^K) i (vector[wan_nchi z$1; wan_nchi z$2])))` THEN
  SUBGOAL_THEN
   `(\z. vsum(1..3) (\i. frechet_derivative wan_nchi (at z) (basis j)$i %
                         (if i = 3 then vec 0:real^K
                          else (v:num->real^2->real^K) i (vector[wan_nchi z$1; wan_nchi z$2]))))
      IN lspace wan_shell (&2)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL
     [`wan_shell`; `{z:real^3 | &1 / &2 < norm z /\ norm z < &2 /\ z$3 < norm z}`;
      `\z. vsum(1..3) (\i. frechet_derivative wan_nchi (at z) (basis j)$i %
                           (if i = 3 then vec 0:real^K
                            else (v:num->real^2->real^K) i
                                   (vector[wan_nchi z$1; wan_nchi z$2])))`;
      `&2`] WAN_LSPACE_NEGLIGIBLE_DIFF) THEN
    REWRITE_TAC[WAN_SHELL_OPEN_AXIS] THEN DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC[];
    ASM_REWRITE_TAC[]] THEN
  MATCH_MP_TAC WAN_REMOVABLE_AXIS3 THEN
  ASM_SIMP_TAC[WAN_SHELL_OPEN_AXIS; WAN_LSPACE2_IMP_L2LOC; WAN_LSPACE2_IMP_LLOC] THEN
  MATCH_MP_TAC WAN_WPD_SUBSET THEN
  EXISTS_TAC `{z:real^3 | &1 / &2 < norm z /\ norm z < &2 /\ z$3 < norm z}` THEN
  ASM_SIMP_TAC[WAN_SHELL_OPEN_AXIS]);;

(* ------------------------------------------------------------------------- *)
(* The main theorem: WAN_S2_STEREO_STATEMENT (pc_wan_p4defs).                *)
(* ------------------------------------------------------------------------- *)

let WAN_S2_STEREO = prove
 (`!(kk:K->bool). WAN_S2_STEREO_STATEMENT kk`,
  GEN_TAC THEN REWRITE_TAC[WAN_S2_STEREO_STATEMENT] THEN CONJ_TAC THEN
  X_GEN_TAC `u:real^3->real^K` THEN DISCH_TAC THENL
   [MATCH_MP_TAC WAN_S2_STEREO_A THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC WAN_S2_STEREO_B THEN ASM_REWRITE_TAC[]]);;

