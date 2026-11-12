(* ========================================================================= *)
(* pc_wan_weak: calculus of weak partial derivatives on open subsets of      *)
(* real^N.                                                                   *)
(*   - test-function pairings, linearity, restriction to open subsets;       *)
(*   - the fundamental lemma (Lebesgue density) and a.e. uniqueness of       *)
(*     weak partials; the chosen weak partials and the Dirichlet integral;   *)
(*   - locally Lipschitz functions (WAN_LIP_IBP, WAN_LIP_W12);               *)
(*   - C^1 maps (WAN_W12_C1);                                                *)
(*   - smooth extension by zero, products with smooth functions              *)
(*     (WAN_MUL_W12).                                                        *)
(* ========================================================================= *)

needs "src/pc_wan_defs.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Integrals of functions vanishing off a compact set k: the domain of       *)
(* integration may be any set between k and s.                                *)
(* ------------------------------------------------------------------------- *)

let WAN_INTEGRAL_SUPPORT_SUBSET = prove
 (`!(g:real^N->real^K) k t s.
     k SUBSET t /\ t SUBSET s /\ (!x. ~(x IN k) ==> g x = vec 0)
     ==> integral t g = integral s g`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM INTEGRAL_RESTRICT_UNIV] THEN
  AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `x:real^N` THEN
  ASM_CASES_TAC `(x:real^N) IN k` THENL [ASM SET_TAC[]; ASM_SIMP_TAC[COND_ID]]);;

let WAN_ABS_INTEGRABLE_SUPPORT_SUBSET = prove
 (`!(g:real^N->real^K) k t s.
     k SUBSET t /\ t SUBSET s /\ (!x. ~(x IN k) ==> g x = vec 0)
     ==> (g absolutely_integrable_on t <=> g absolutely_integrable_on s)`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM ABSOLUTELY_INTEGRABLE_RESTRICT_UNIV] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `x:real^N` THEN
  ASM_CASES_TAC `(x:real^N) IN k` THENL [ASM SET_TAC[]; ASM_SIMP_TAC[COND_ID]]);;

(* ------------------------------------------------------------------------- *)
(* Test functions: monotonicity in the set, support, and the pairings with  *)
(* locally integrable maps.                                                   *)
(* ------------------------------------------------------------------------- *)

let WAN_TEST_SUBSET = prove
 (`!(s:real^N->bool) t phi. wan_test t phi /\ t SUBSET s ==> wan_test s phi`,
  REWRITE_TAC[wan_test] THEN MESON_TAC[SUBSET_TRANS]);;

let WAN_LLOC_SUBSET = prove
 (`!(s:real^N->bool) t (u:real^N->real^K). wan_lloc s u /\ t SUBSET s ==> wan_lloc t u`,
  REWRITE_TAC[wan_lloc] THEN MESON_TAC[SUBSET_TRANS]);;

let WAN_L2LOC_SUBSET = prove
 (`!(s:real^N->bool) t (u:real^N->real^K). wan_l2loc s u /\ t SUBSET s ==> wan_l2loc t u`,
  REWRITE_TAC[wan_l2loc] THEN MESON_TAC[SUBSET_TRANS]);;

let WAN_TEST_DPART_ZERO = prove
 (`!(phi:real^N->real) k i x.
     smooth_map_on (:real^N) (\y. lift(phi y)) /\ compact k /\
     (!y. ~(y IN k) ==> phi y = &0) /\ ~(x IN k)
     ==> wan_dpart i phi x = &0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[wan_dpart] THEN
  MP_TAC(ISPECL [`phi:real^N->real`; `k:real^N->bool`; `basis i:real^N`; `x:real^N`]
                WAN_TEST_DERIV_ZERO) THEN
  ASM_SIMP_TAC[DROP_VEC]);;

let WAN_TEST_CONTINUOUS = prove
 (`!(s:real^N->bool) phi i.
     wan_test s phi
     ==> (\x. lift(phi x)) continuous_on (:real^N) /\
         (\x. lift(wan_dpart i phi x)) continuous_on (:real^N)`,
  REWRITE_TAC[wan_test] THEN REPEAT STRIP_TAC THENL
   [ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON]; ALL_TAC] THEN
  REWRITE_TAC[wan_dpart; LIFT_DROP] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_FRECHET_DERIVATIVE THEN ASM_REWRITE_TAC[OPEN_UNIV]);;

let WAN_CONT_LLOC_PAIRING = prove
 (`!(s:real^N->bool) (g:real^N->real) (u:real^N->real^K) k.
     (\x. lift(g x)) continuous_on (:real^N) /\ compact k /\ k SUBSET s /\
     (!x. ~(x IN k) ==> g x = &0) /\ wan_lloc s u
     ==> (\x. g x % u x) absolutely_integrable_on s`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\x:real^N. g x % (u:real^N->real^K) x`; `k:real^N->bool`;
                 `k:real^N->bool`; `s:real^N->bool`] WAN_ABS_INTEGRABLE_SUPPORT_SUBSET) THEN
  ASM_SIMP_TAC[SUBSET_REFL; VECTOR_MUL_LZERO] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MP_TAC(ISPECL [`\a:real^1 b:real^K. drop a % b`; `\x:real^N. lift(g x)`;
                 `u:real^N->real^K`; `k:real^N->bool`]
                ABSOLUTELY_INTEGRABLE_BOUNDED_MEASURABLE_PRODUCT) THEN
  REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[BILINEAR_DROP_MUL] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
    ASM_SIMP_TAC[LEBESGUE_MEASURABLE_COMPACT] THEN
    ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_UNIV];
    MATCH_MP_TAC COMPACT_IMP_BOUNDED THEN MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
    ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_UNIV];
    ASM_MESON_TAC[wan_lloc; SUBSET_REFL]]);;

let WAN_TEST_PAIRING = prove
 (`!(s:real^N->bool) phi (u:real^N->real^K).
     wan_test s phi /\ wan_lloc s u
     ==> (\x. phi x % u x) absolutely_integrable_on s /\
         !i. (\x. wan_dpart i phi x % u x) absolutely_integrable_on s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ASSUME `wan_test (s:real^N->bool) phi`) THEN REWRITE_TAC[wan_test] THEN
  STRIP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC WAN_CONT_LLOC_PAIRING THEN EXISTS_TAC `k:real^N->bool` THEN
    MP_TAC(ISPECL [`s:real^N->bool`; `phi:real^N->real`; `1`] WAN_TEST_CONTINUOUS) THEN
    ASM_SIMP_TAC[];
    GEN_TAC THEN MATCH_MP_TAC WAN_CONT_LLOC_PAIRING THEN EXISTS_TAC `k:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`s:real^N->bool`; `phi:real^N->real`; `i:num`] WAN_TEST_CONTINUOUS) THEN
      ASM_SIMP_TAC[];
      X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN MATCH_MP_TAC WAN_TEST_DPART_ZERO THEN
      EXISTS_TAC `k:real^N->bool` THEN ASM_REWRITE_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* Linearity of local integrability and of weak partials.                    *)
(* ------------------------------------------------------------------------- *)

let WAN_LLOC_ADD = prove
 (`!(s:real^N->bool) (u:real^N->real^K) v.
     wan_lloc s u /\ wan_lloc s v ==> wan_lloc s (\x. u x + v x)`,
  SIMP_TAC[wan_lloc; ABSOLUTELY_INTEGRABLE_ADD]);;

let WAN_LLOC_CMUL = prove
 (`!(s:real^N->bool) (u:real^N->real^K) c. wan_lloc s u ==> wan_lloc s (\x. c % u x)`,
  SIMP_TAC[wan_lloc; ABSOLUTELY_INTEGRABLE_CMUL]);;

let WAN_LLOC_NEG = prove
 (`!(s:real^N->bool) (u:real^N->real^K). wan_lloc s u ==> wan_lloc s (\x. --(u x))`,
  SIMP_TAC[wan_lloc; ABSOLUTELY_INTEGRABLE_NEG]);;

let WAN_LLOC_SUB = prove
 (`!(s:real^N->bool) (u:real^N->real^K) v.
     wan_lloc s u /\ wan_lloc s v ==> wan_lloc s (\x. u x - v x)`,
  SIMP_TAC[wan_lloc; ABSOLUTELY_INTEGRABLE_SUB]);;

let WAN_LLOC_ZERO = prove
 (`!s:real^N->bool. wan_lloc s (\x. vec 0:real^K)`,
  REWRITE_TAC[wan_lloc; ABSOLUTELY_INTEGRABLE_0]);;

let WAN_WPD_ZERO = prove
 (`!(s:real^N->bool) i. wan_wpd s i (\x. vec 0:real^K) (\x. vec 0)`,
  REWRITE_TAC[wan_wpd; WAN_LLOC_ZERO; VECTOR_MUL_RZERO; INTEGRAL_0; VECTOR_NEG_0]);;

let WAN_WPD_ADD = prove
 (`!(s:real^N->bool) i (u:real^N->real^K) v u' v'.
     wan_wpd s i u v /\ wan_wpd s i u' v'
     ==> wan_wpd s i (\x. u x + u' x) (\x. v x + v' x)`,
  REWRITE_TAC[wan_wpd] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[WAN_LLOC_ADD] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `phi:real^N->real`; `u:real^N->real^K`] WAN_TEST_PAIRING) THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `phi:real^N->real`; `u':real^N->real^K`] WAN_TEST_PAIRING) THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `phi:real^N->real`; `v:real^N->real^K`] WAN_TEST_PAIRING) THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `phi:real^N->real`; `v':real^N->real^K`] WAN_TEST_PAIRING) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[VECTOR_ADD_LDISTRIB; INTEGRAL_ADD; ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE] THEN
  VECTOR_ARITH_TAC);;

let WAN_WPD_CMUL = prove
 (`!(s:real^N->bool) i (u:real^N->real^K) v c.
     wan_wpd s i u v ==> wan_wpd s i (\x. c % u x) (\x. c % v x)`,
  REWRITE_TAC[wan_wpd] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[WAN_LLOC_CMUL] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `phi:real^N->real`; `u:real^N->real^K`] WAN_TEST_PAIRING) THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `phi:real^N->real`; `v:real^N->real^K`] WAN_TEST_PAIRING) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[GSYM VECTOR_MUL_ASSOC] THEN
  ASM_SIMP_TAC[INTEGRAL_CMUL; ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE] THEN
  VECTOR_ARITH_TAC);;

let WAN_WPD_NEG = prove
 (`!(s:real^N->bool) i (u:real^N->real^K) v.
     wan_wpd s i u v ==> wan_wpd s i (\x. --(u x)) (\x. --(v x))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `--(&1)` o MATCH_MP WAN_WPD_CMUL) THEN
  REWRITE_TAC[VECTOR_MUL_LNEG; VECTOR_MUL_LID]);;

let WAN_WPD_SUB = prove
 (`!(s:real^N->bool) i (u:real^N->real^K) v u' v'.
     wan_wpd s i u v /\ wan_wpd s i u' v'
     ==> wan_wpd s i (\x. u x - u' x) (\x. v x - v' x)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[VECTOR_SUB] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `i:num`; `u:real^N->real^K`; `v:real^N->real^K`;
                 `\x. --((u':real^N->real^K) x)`; `\x. --((v':real^N->real^K) x)`]
                WAN_WPD_ADD) THEN
  ASM_SIMP_TAC[WAN_WPD_NEG]);;

let WAN_WPD_SUBSET = prove
 (`!(s:real^N->bool) t i (u:real^N->real^K) v.
     wan_wpd s i u v /\ t SUBSET s ==> wan_wpd t i u v`,
  REWRITE_TAC[wan_wpd] THEN REPEAT STRIP_TAC THENL
   [ASM_MESON_TAC[WAN_LLOC_SUBSET];
    ASM_MESON_TAC[WAN_LLOC_SUBSET];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `phi:real^N->real`) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[WAN_TEST_SUBSET]; ALL_TAC] THEN
  MP_TAC(ASSUME `wan_test (t:real^N->bool) phi`) THEN REWRITE_TAC[wan_test] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`\x. wan_dpart i (phi:real^N->real) x % (u:real^N->real^K) x`;
                 `k:real^N->bool`; `t:real^N->bool`; `s:real^N->bool`]
                WAN_INTEGRAL_SUPPORT_SUBSET) THEN
  MP_TAC(ISPECL [`\x. (phi:real^N->real) x % (v:real^N->real^K) x`;
                 `k:real^N->bool`; `t:real^N->bool`; `s:real^N->bool`]
                WAN_INTEGRAL_SUPPORT_SUBSET) THEN
  ASM_SIMP_TAC[VECTOR_MUL_LZERO] THEN
  SUBGOAL_THEN `!x:real^N. ~(x IN k) ==> wan_dpart i phi x = &0` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC WAN_TEST_DPART_ZERO THEN
    EXISTS_TAC `k:real^N->bool` THEN ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[VECTOR_MUL_LZERO]]);;

(* ------------------------------------------------------------------------- *)
(* W^(1,2): closure under linear combinations and restriction.               *)
(* ------------------------------------------------------------------------- *)

let WAN_W12_ADD = prove
 (`!(s:real^N->bool) (f:real^N->real^K) g.
     wan_w12 s f /\ wan_w12 s g ==> wan_w12 s (\x. f x + g x)`,
  REWRITE_TAC[wan_w12] THEN REPEAT STRIP_TAC THENL [ASM_SIMP_TAC[LSPACE_ADD; REAL_POS]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `v2:real^N->real^K` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `v1:real^N->real^K` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `\x. (v1:real^N->real^K) x + v2 x` THEN
  ASM_SIMP_TAC[LSPACE_ADD; REAL_POS; WAN_WPD_ADD]);;

let WAN_W12_CMUL = prove
 (`!(s:real^N->bool) (f:real^N->real^K) c. wan_w12 s f ==> wan_w12 s (\x. c % f x)`,
  REWRITE_TAC[wan_w12] THEN REPEAT STRIP_TAC THENL [ASM_SIMP_TAC[LSPACE_CMUL]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `v1:real^N->real^K` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `\x. c % (v1:real^N->real^K) x` THEN
  ASM_SIMP_TAC[LSPACE_CMUL; WAN_WPD_CMUL]);;

let WAN_W12_NEG = prove
 (`!(s:real^N->bool) (u:real^N->real^K). wan_w12 s u ==> wan_w12 s (\x. --(u x))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `--(&1)` o MATCH_MP WAN_W12_CMUL) THEN
  REWRITE_TAC[VECTOR_MUL_LNEG; VECTOR_MUL_LID]);;

let WAN_W12_SUB = prove
 (`!(s:real^N->bool) (u:real^N->real^K) v.
     wan_w12 s u /\ wan_w12 s v ==> wan_w12 s (\x. u x - v x)`,
  SIMP_TAC[VECTOR_SUB; WAN_W12_ADD; WAN_W12_NEG]);;

let WAN_W12_SUBSET = prove
 (`!(s:real^N->bool) t (f:real^N->real^K).
     wan_w12 s f /\ open t /\ t SUBSET s ==> wan_w12 t f`,
  REWRITE_TAC[wan_w12] THEN REPEAT STRIP_TAC THENL
   [ASM_MESON_TAC[LSPACE_SUBSET; LEBESGUE_MEASURABLE_OPEN]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `v1:real^N->real^K` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `v1:real^N->real^K` THEN
  ASM_MESON_TAC[LSPACE_SUBSET; LEBESGUE_MEASURABLE_OPEN; WAN_WPD_SUBSET]);;

(* ========================================================================= *)
(* The fundamental lemma of the calculus of                                  *)
(* variations for locally integrable maps (bumps converging to the          *)
(* indicator of a ball, dominated convergence, Lebesgue density), a.e.      *)
(* uniqueness of weak partials, the chosen weak partials and the Dirichlet  *)
(* integral.                                                                 *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Bumps approximating the indicator of an open ball from inside.            *)
(* ------------------------------------------------------------------------- *)

let WAN_BALL_BUMP_TEST = prove
 (`!(s:real^N->bool) c e n.
     &0 < e /\ cball(c,e) SUBSET s
     ==> wan_test s (\x. smooth_bump (e * (&1 - inv(&n + &2))) e (x - c))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= e * (&1 - inv(&n + &2)) /\ e * (&1 - inv(&n + &2)) < e`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < inv(&n + &2) /\ inv(&n + &2) <= inv(&2)` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL [MATCH_MP_TAC REAL_LT_INV THEN REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_INV2 THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_ARITH `e * (&1 - x) < e <=> &0 < e * x`] THEN
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[wan_test] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`\x:real^N. lift(smooth_bump (e * (&1 - inv(&n + &2))) e x)`; `--c:real^N`]
                  PDE_SMOOTH_TRANSLATE) THEN
    ASM_SIMP_TAC[SMOOTH_BUMP_SMOOTH; VECTOR_ARITH `x + --c:real^N = x - c`];
    EXISTS_TAC `cball(c:real^N,e)` THEN ASM_REWRITE_TAC[COMPACT_CBALL] THEN
    X_GEN_TAC `x:real^N` THEN REWRITE_TAC[IN_CBALL; dist] THEN DISCH_TAC THEN
    MATCH_MP_TAC SMOOTH_BUMP_0 THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`c:real^N`; `x:real^N`] NORM_SUB) THEN ASM_REAL_ARITH_TAC]);;

let WAN_BALL_BUMP_LIMIT = prove
 (`!(c:real^N) e x.
     &0 < e /\ x IN cball(c,e)
     ==> ((\n. lift(smooth_bump (e * (&1 - inv(&n + &2))) e (x - c))) -->
          (if x IN ball(c,e) then lift(&1) else vec 0)) sequentially`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_CBALL; IN_BALL; dist] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!n. &0 <= e * (&1 - inv(&n + &2)) /\ e * (&1 - inv(&n + &2)) < e`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    SUBGOAL_THEN `&0 < inv(&n + &2) /\ inv(&n + &2) <= inv(&2)` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL [MATCH_MP_TAC REAL_LT_INV THEN REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_INV2 THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_ARITH `e * (&1 - x) < e <=> &0 < e * x`] THEN
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:real^N`; `x:real^N`] NORM_SUB) THEN DISCH_TAC THEN
  COND_CASES_TAC THENL
   [MATCH_MP_TAC LIM_EVENTUALLY THEN REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
    SUBGOAL_THEN `?m. ~(m = 0) /\ &0 < inv(&m) /\ inv(&m) < (e - norm(x - c:real^N)) / e`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_ARCH_INV] THEN MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    EXISTS_TAC `m:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    AP_TERM_TAC THEN MATCH_MP_TAC SMOOTH_BUMP_1 THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `inv(&n + &2) <= inv(&m)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_INV2 THEN
      ASM_SIMP_TAC[REAL_OF_NUM_LT; LE_1; REAL_OF_NUM_LE; REAL_OF_NUM_ADD] THEN
      ASM_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `e * inv(&n + &2) < e - norm(x - c:real^N)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `e * inv(&m)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
        UNDISCH_TAC `inv(&m) < (e - norm(x - c:real^N)) / e` THEN
        ASM_SIMP_TAC[REAL_LT_RDIV_EQ] THEN REAL_ARITH_TAC];
      REAL_ARITH_TAC];
    MATCH_MP_TAC LIM_EVENTUALLY THEN REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
    EXISTS_TAC `0` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    REWRITE_TAC[GSYM LIFT_NUM] THEN AP_TERM_TAC THEN
    MATCH_MP_TAC SMOOTH_BUMP_0 THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

let WAN_INTEGRAL_LIMIT_TESTS = prove
 (`!(s:real^N->bool) (w:real^N->real^K) c e (ph:num->real^N->real).
     wan_lloc s w /\
     (!phi. wan_test s phi ==> integral s (\x. phi x % w x) = vec 0) /\
     &0 < e /\ cball(c,e) SUBSET s /\
     (!n. wan_test s (ph n)) /\ (!n x. &0 <= ph n x /\ ph n x <= &1) /\
     (!n x. ~(x IN cball(c,e)) ==> ph n x = &0) /\
     (!x. x IN cball(c,e)
          ==> ((\n. lift(ph n x)) --> (if x IN ball(c,e) then lift(&1) else vec 0))
              sequentially)
     ==> integral (ball(c,e)) w = vec 0`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(w:real^N->real^K) absolutely_integrable_on cball(c,e)` ASSUME_TAC THENL
   [ASM_MESON_TAC[wan_lloc; COMPACT_CBALL]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. integral (cball(c,e)) (\x. (ph:num->real^N->real) n x % (w:real^N->real^K) x) = vec 0`
  ASSUME_TAC THENL
   [X_GEN_TAC `n:num` THEN
    MP_TAC(MP (SPEC `(ph:num->real^N->real) n`
      (ASSUME `!phi. wan_test s phi
                     ==> integral s (\x. phi x % (w:real^N->real^K) x) = vec 0`))
      (SPEC `n:num` (ASSUME `!n. wan_test (s:real^N->bool) ((ph:num->real^N->real) n)`))) THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC WAN_INTEGRAL_SUPPORT_SUBSET THEN
    EXISTS_TAC `cball(c:real^N,e)` THEN ASM_SIMP_TAC[SUBSET_REFL; VECTOR_MUL_LZERO];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\n x. (ph:num->real^N->real) n x % (w:real^N->real^K) x`;
    `\x:real^N. if x IN ball(c,e) then (w:real^N->real^K) x else vec 0`;
    `\x:real^N. lift(norm((w:real^N->real^K) x))`;
    `cball(c:real^N,e)`] DOMINATED_CONVERGENCE) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [GEN_TAC THEN MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
      MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
      EXISTS_TAC `s:real^N->bool` THEN ASM_SIMP_TAC[LEBESGUE_MEASURABLE_COMPACT; COMPACT_CBALL] THEN
      MP_TAC(ISPECL [`s:real^N->bool`; `(ph:num->real^N->real) k`; `w:real^N->real^K`]
                    WAN_TEST_PAIRING) THEN
      ASM_SIMP_TAC[];
      MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
      MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_NORM THEN ASM_REWRITE_TAC[];
      MAP_EVERY X_GEN_TAC [`n:num`; `x:real^N`] THEN DISCH_TAC THEN
      REWRITE_TAC[NORM_MUL; LIFT_DROP] THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
      MP_TAC(SPECL [`n:num`; `x:real^N`]
        (ASSUME `!n x. &0 <= (ph:num->real^N->real) n x /\ ph n x <= &1`)) THEN
      REAL_ARITH_TAC;
      X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
      MP_TAC(MP (SPEC `x:real^N`
        (ASSUME `!x. x IN cball(c,e)
                     ==> ((\n. lift((ph:num->real^N->real) n x)) -->
                          (if x IN ball(c,e) then lift(&1) else vec 0)) sequentially`))
        (ASSUME `(x:real^N) IN cball(c,e)`)) THEN
      DISCH_TAC THEN
      MP_TAC(ISPECL [`sequentially`; `\n. (ph:num->real^N->real) n x`;
                     `if x IN ball(c:real^N,e) then &1 else &0`;
                     `(w:real^N->real^K) x`] LIM_VMUL) THEN
      ANTS_TAC THENL
       [REWRITE_TAC[o_DEF] THEN POP_ASSUM MP_TAC THEN
        COND_CASES_TAC THEN REWRITE_TAC[LIFT_NUM];
        COND_CASES_TAC THEN REWRITE_TAC[VECTOR_MUL_LID; VECTOR_MUL_LZERO]]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[LIM_CONST_EQ; TRIVIAL_LIMIT_SEQUENTIALLY] THEN
  DISCH_THEN(MP_TAC o CONJUNCT2) THEN
  REWRITE_TAC[INTEGRAL_RESTRICT_INTER] THEN
  SUBGOAL_THEN `ball(c:real^N,e) INTER cball(c,e) = ball(c,e)` SUBST1_TAC THENL
   [MP_TAC(ISPECL [`c:real^N`; `e:real`] BALL_SUBSET_CBALL) THEN SET_TAC[];
    MESON_TAC[]]);;

let WAN_BUMP_RADII = prove
 (`!e n. &0 < e ==> &0 <= e * (&1 - inv(&n + &2)) /\ e * (&1 - inv(&n + &2)) < e`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < inv(&n + &2) /\ inv(&n + &2) <= inv(&2)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [MATCH_MP_TAC REAL_LT_INV THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[REAL_ARITH `e * (&1 - x) < e <=> &0 < e * x`] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC]);;

let WAN_BALL_INTEGRAL_ZERO = prove
 (`!(s:real^N->bool) (w:real^N->real^K) c e.
     wan_lloc s w /\
     (!phi. wan_test s phi ==> integral s (\x. phi x % w x) = vec 0) /\
     &0 < e /\ cball(c,e) SUBSET s
     ==> integral (ball(c,e)) w = vec 0`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC WAN_INTEGRAL_LIMIT_TESTS THEN
  MAP_EVERY EXISTS_TAC
   [`s:real^N->bool`;
    `\n x:real^N. smooth_bump (e * (&1 - inv(&n + &2))) e (x - c)`] THEN
  ASM_SIMP_TAC[WAN_BALL_BUMP_TEST; WAN_BALL_BUMP_LIMIT; SMOOTH_BUMP_BOUNDS] THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `x:real^N`] THEN REWRITE_TAC[IN_CBALL; dist] THEN
  DISCH_TAC THEN MATCH_MP_TAC SMOOTH_BUMP_0 THEN
  MP_TAC(ISPECL [`c:real^N`; `x:real^N`] NORM_SUB) THEN
  MP_TAC(SPECL [`e:real`; `n:num`] WAN_BUMP_RADII) THEN ASM_REAL_ARITH_TAC);;

let WAN_LIMPT_POSITIVE_REALS = prove
 (`~(trivial_limit (at (vec 0:real^1) within {t | &0 < drop t}))`,
  REWRITE_TAC[TRIVIAL_LIMIT_WITHIN; LIMPT_APPROACHABLE; IN_ELIM_THM] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN EXISTS_TAC `lift(e / &2)` THEN
  REWRITE_TAC[LIFT_DROP; GSYM LIFT_NUM; LIFT_EQ; DIST_LIFT; DROP_VEC] THEN
  ASM_REAL_ARITH_TAC);;

let WAN_FUNDAMENTAL_LEMMA = prove
 (`!(s:real^N->bool) (w:real^N->real^K).
     open s /\ wan_lloc s w /\
     (!phi. wan_test s phi ==> integral s (\x. phi x % w x) = vec 0)
     ==> negligible {x | x IN s /\ ~(w x = vec 0)}`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[LOCALLY_NEGLIGIBLE_ALT] THEN
  X_GEN_TAC `x0:real^N` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`] OPEN_CONTAINS_CBALL) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `x0:real^N`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `{x | x IN s /\ ~((w:real^N->real^K) x = vec 0)} INTER ball(x0,e / &2)` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_IN_OPEN_INTER THEN REWRITE_TAC[OPEN_BALL];
    ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM; CENTRE_IN_BALL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(w:real^N->real^K) absolutely_integrable_on cball(x0,e)` ASSUME_TAC THENL
   [ASM_MESON_TAC[wan_lloc; COMPACT_CBALL]; ALL_TAC] THEN
  MP_TAC(ISPECL [`w:real^N->real^K`; `ball(x0:real^N,e / &2)`]
                LEBESGUE_DENSITY_THEOREM_INTEGRAL_BALL) THEN
  ANTS_TAC THENL
   [MAP_EVERY X_GEN_TAC [`p:real^N`; `q:real^N`] THEN
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
    EXISTS_TAC `cball(x0:real^N,e)` THEN ASM_REWRITE_TAC[] THEN
    SIMP_TAC[LEBESGUE_MEASURABLE_INTER; LEBESGUE_MEASURABLE_BALL;
             LEBESGUE_MEASURABLE_INTERVAL] THEN
    MATCH_MP_TAC(SET_RULE `(s:real^N->bool) SUBSET u ==> s INTER t SUBSET u`) THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `ball(x0:real^N,e)` THEN
    REWRITE_TAC[BALL_SUBSET_CBALL] THEN MATCH_MP_TAC SUBSET_BALL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN EXISTS_TAC `k:real^N->bool` THEN
  ASM_REWRITE_TAC[SUBSET; IN_INTER; IN_ELIM_THM] THEN
  X_GEN_TAC `x:real^N` THEN STRIP_TAC THEN
  ASM_CASES_TAC `(x:real^N) IN k` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `((\t. vec 0) --> (w:real^N->real^K) x) (at (vec 0) within {t | &0 < drop t})`
  MP_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT]
      LIM_TRANSFORM_EVENTUALLY)) THEN
    REWRITE_TAC[EVENTUALLY_WITHIN; IN_ELIM_THM] THEN
    EXISTS_TAC `e / &2 - norm(x - x0:real^N)` THEN CONJ_TAC THENL
     [UNDISCH_TAC `(x:real^N) IN ball(x0,e / &2)` THEN
      REWRITE_TAC[IN_BALL; dist] THEN
      MP_TAC(ISPECL [`x0:real^N`; `x:real^N`] NORM_SUB) THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    X_GEN_TAC `t:real^1` THEN REWRITE_TAC[DIST_0; NORM_REAL; GSYM drop] THEN STRIP_TAC THEN
    SUBGOAL_THEN `ball(x0:real^N,e / &2) INTER ball(x,drop t) = ball(x,drop t) /\
                  cball(x:real^N,drop t) SUBSET s`
    STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN `cball(x:real^N,drop t) SUBSET ball(x0,e / &2)` MP_TAC THENL
       [REWRITE_TAC[SUBSET; IN_CBALL; IN_BALL; dist] THEN X_GEN_TAC `y:real^N` THEN
        MP_TAC(ISPECL [`x0:real^N`; `x:real^N`] NORM_SUB) THEN
        MP_TAC(NORM_ARITH `norm(x0 - y:real^N) <= norm(x0 - x) + norm(x - y)`) THEN
        ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      MP_TAC(ISPECL [`x:real^N`; `drop t`] BALL_SUBSET_CBALL) THEN
      SUBGOAL_THEN `ball(x0:real^N,e / &2) SUBSET cball(x0,e)` MP_TAC THENL
       [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `ball(x0:real^N,e)` THEN
        REWRITE_TAC[BALL_SUBSET_CBALL] THEN MATCH_MP_TAC SUBSET_BALL THEN ASM_REAL_ARITH_TAC;
        UNDISCH_TAC `cball(x0:real^N,e) SUBSET s` THEN SET_TAC[]];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`s:real^N->bool`; `w:real^N->real^K`; `x:real^N`; `drop t`]
                  WAN_BALL_INTEGRAL_ZERO) THEN
    ASM_SIMP_TAC[VECTOR_MUL_RZERO] THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[LIM_CONST_EQ; WAN_LIMPT_POSITIVE_REALS] THEN ASM_MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Uniqueness of weak partials up to null sets; the chosen weak partials;    *)
(* the Dirichlet integral does not depend on the choice.                      *)
(* ------------------------------------------------------------------------- *)

let WAN_WPD_UNIQUE = prove
 (`!(s:real^N->bool) i (u:real^N->real^K) v1 v2.
     open s /\ wan_wpd s i u v1 /\ wan_wpd s i u v2
     ==> negligible {x | x IN s /\ ~(v1 x = v2 x)}`,
  REWRITE_TAC[wan_wpd] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `\x. (v1:real^N->real^K) x - v2 x`] WAN_FUNDAMENTAL_LEMMA) THEN
  REWRITE_TAC[VECTOR_SUB_EQ] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_SIMP_TAC[WAN_LLOC_SUB] THEN
  X_GEN_TAC `phi:real^N->real` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `phi:real^N->real`; `v1:real^N->real^K`] WAN_TEST_PAIRING) THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `phi:real^N->real`; `v2:real^N->real^K`] WAN_TEST_PAIRING) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[VECTOR_SUB_LDISTRIB; INTEGRAL_SUB; ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE] THEN
  MP_TAC(MP (SPEC `phi:real^N->real`
    (ASSUME `!phi. wan_test s phi
                   ==> integral s (\x. wan_dpart i phi x % (u:real^N->real^K) x) =
                       --integral s (\x. phi x % v1 x)`))
    (ASSUME `wan_test (s:real^N->bool) phi`)) THEN
  MP_TAC(MP (SPEC `phi:real^N->real`
    (ASSUME `!phi. wan_test s phi
                   ==> integral s (\x. wan_dpart i phi x % (u:real^N->real^K) x) =
                       --integral s (\x. phi x % v2 x)`))
    (ASSUME `wan_test (s:real^N->bool) phi`)) THEN
  VECTOR_ARITH_TAC);;

let WAN_WD_WORKS = prove
 (`!(s:real^N->bool) i (u:real^N->real^K).
     wan_w12 s u /\ 1 <= i /\ i <= dimindex(:N)
     ==> wan_wd s i u IN lspace s (&2) /\ wan_wpd s i u (wan_wd s i u)`,
  REWRITE_TAC[wan_w12; wan_wd] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SELECT_RULE) THEN SIMP_TAC[]);;

let WAN_WD_UNIQUE = prove
 (`!(s:real^N->bool) i (u:real^N->real^K) v.
     open s /\ wan_w12 s u /\ 1 <= i /\ i <= dimindex(:N) /\ wan_wpd s i u v
     ==> negligible {x | x IN s /\ ~(wan_wd s i u x = v x)}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC WAN_WPD_UNIQUE THEN
  MAP_EVERY EXISTS_TAC [`i:num`; `u:real^N->real^K`] THEN
  ASM_SIMP_TAC[WAN_WD_WORKS; ETA_AX]);;

let WAN_DIR_EQ = prove
 (`!(s:real^N->bool) (u:real^N->real^K) v.
     open s /\ wan_w12 s u /\
     (!i. 1 <= i /\ i <= dimindex(:N) ==> wan_wpd s i u (v i))
     ==> wan_dir s u =
         sum(1..dimindex(:N)) (\i. drop(integral s (\x. lift(norm(v i x) pow 2))))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[wan_dir] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  REWRITE_TAC[] THEN AP_TERM_TAC THEN MATCH_MP_TAC INTEGRAL_SPIKE THEN
  EXISTS_TAC `{x | x IN s /\ ~(wan_wd s i (u:real^N->real^K) x = v i x)}` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC WAN_WD_UNIQUE THEN ASM_SIMP_TAC[ETA_AX];
    REWRITE_TAC[IN_DIFF; IN_ELIM_THM] THEN MESON_TAC[]]);;

let WAN_LSPACE2_SQNORM_INTEGRABLE = prove
 (`!(s:real^N->bool) (f:real^N->real^K).
     f IN lspace s (&2) ==> (\x. lift(norm(f x) pow 2)) integrable_on s`,
  REWRITE_TAC[lspace; IN_ELIM_THM; RPOW_POW] THEN SIMP_TAC[]);;

let WAN_DIR_POS = prove
 (`!(s:real^N->bool) (u:real^N->real^K). wan_w12 s u ==> &0 <= wan_dir s u`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[wan_dir] THEN
  MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  REWRITE_TAC[] THEN MATCH_MP_TAC INTEGRAL_DROP_POS THEN
  REWRITE_TAC[LIFT_DROP; REAL_LE_POW_2] THEN
  MATCH_MP_TAC WAN_LSPACE2_SQNORM_INTEGRABLE THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `i:num`; `u:real^N->real^K`] WAN_WD_WORKS) THEN
  ASM_SIMP_TAC[ETA_AX]);;

(* ========================================================================= *)
(* Smooth compactly supported functions are                                  *)
(* bounded and Lipschitz; difference quotients along a sequence; the        *)
(* integration by parts formula for globally Lipschitz functions            *)
(* (difference quotients, translation invariance, dominated convergence and *)
(* Rademacher's theorem).                                                    *)
(* ========================================================================= *)

let WAN_SMOOTH_SUPPORT_BOUNDS = prove
 (`!(phi:real^N->real) k.
     smooth_map_on (:real^N) (\x. lift(phi x)) /\ compact k /\
     (!x. ~(x IN k) ==> phi x = &0)
     ==> (?B. !x. abs(phi x) <= B) /\
         (?B. !x h. abs(drop(frechet_derivative (\y. lift(phi y)) (at x) h)) <= B * norm h)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`\x:real^N. lift(phi x)`; `k:real^N->bool`] COMPACT_CONTINUOUS_IMAGE) THEN
    ANTS_TAC THENL
     [ASM_MESON_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON; CONTINUOUS_ON_SUBSET; SUBSET_UNIV];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
    REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE; NORM_LIFT] THEN
    DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN EXISTS_TAC `B:real` THEN
    X_GEN_TAC `x:real^N` THEN ASM_CASES_TAC `(x:real^N) IN k` THEN ASM_SIMP_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `g = \x:real^N. lift(sum(1..dimindex(:N))
                  (\i. abs(drop(frechet_derivative (\y. lift(phi y)) (at x) (basis i)))))` THEN
  SUBGOAL_THEN `(g:real^N->real^1) continuous_on (:real^N)` ASSUME_TAC THENL
   [EXPAND_TAC "g" THEN REWRITE_TAC[LIFT_SUM; o_DEF] THEN
    MATCH_MP_TAC CONTINUOUS_ON_VSUM THEN REWRITE_TAC[FINITE_NUMSEG] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_ON_LIFT_ABS THEN REWRITE_TAC[LIFT_DROP; ETA_AX] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_FRECHET_DERIVATIVE THEN ASM_REWRITE_TAC[OPEN_UNIV];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`g:real^N->real^1`; `k:real^N->bool`] COMPACT_CONTINUOUS_IMAGE) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_UNIV]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
  REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN EXISTS_TAC `B:real` THEN
  MAP_EVERY X_GEN_TAC [`x:real^N`; `h:real^N`] THEN
  ASM_CASES_TAC `(x:real^N) IN k` THENL
   [ALL_TAC;
    MP_TAC(ISPECL [`phi:real^N->real`; `k:real^N->bool`; `h:real^N`; `x:real^N`]
                  WAN_TEST_DERIV_ZERO) THEN
    ASM_SIMP_TAC[DROP_VEC; REAL_ABS_NUM] THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[NORM_POS_LE] THEN ASM_REAL_ARITH_TAC] THEN
  SUBGOAL_THEN `linear(frechet_derivative (\y. lift((phi:real^N->real) y)) (at x))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `(:real^N)` THEN
    ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV];
    ALL_TAC] THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV o RAND_CONV) [GSYM BASIS_EXPANSION] THEN
  ASM_SIMP_TAC[LINEAR_VSUM; FINITE_NUMSEG; o_DEF; LINEAR_CMUL; DROP_VSUM; DROP_CMUL] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(1..dimindex(:N))
     (\i. norm(h:real^N) * abs(drop(frechet_derivative (\y. lift((phi:real^N->real) y)) (at x) (basis i))))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_ABS_LE THEN REWRITE_TAC[FINITE_NUMSEG] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN REWRITE_TAC[REAL_ABS_MUL] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_ABS_POS; COMPONENT_LE_NORM];
    REWRITE_TAC[SUM_LMUL] THEN GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "g" THEN REWRITE_TAC[NORM_LIFT] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= a ==> abs a <= B ==> a <= B`) THEN
    MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN REWRITE_TAC[REAL_ABS_POS]]);;


let WAN_SMOOTH_SUPPORT_LIPSCHITZ = prove
 (`!(phi:real^N->real) k.
     smooth_map_on (:real^N) (\x. lift(phi x)) /\ compact k /\
     (!x. ~(x IN k) ==> phi x = &0)
     ==> ?B. !x y. abs(phi x - phi y) <= B * norm(x - y)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`phi:real^N->real`; `k:real^N->bool`] WAN_SMOOTH_SUPPORT_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `B:real` o CONJUNCT2) THEN EXISTS_TAC `B:real` THEN
  MP_TAC(ISPECL [`\x:real^N. lift(phi x)`;
                 `\x:real^N. frechet_derivative (\y. lift((phi:real^N->real) y)) (at x)`;
                 `(:real^N)`; `B:real`] DIFFERENTIABLE_BOUND) THEN
  REWRITE_TAC[CONVEX_UNIV; IN_UNIV; GSYM LIFT_SUB; NORM_LIFT] THEN
  DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
   [X_GEN_TAC `x:real^N` THEN REWRITE_TAC[WITHIN_UNIV] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_IMP; RIGHT_IMP_FORALL_THM] SMOOTH_MAP_ON_HAS_DERIVATIVE) THEN
    EXISTS_TAC `(:real^N)` THEN ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV];
    X_GEN_TAC `x:real^N` THEN
    SUBGOAL_THEN `linear(frechet_derivative (\y. lift((phi:real^N->real) y)) (at x))`
    ASSUME_TAC THENL
     [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `(:real^N)` THEN
      ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV];
      ALL_TAC] THEN
    FIRST_ASSUM(fun th -> MATCH_MP_TAC(CONJUNCT2(MATCH_MP ONORM th))) THEN
    X_GEN_TAC `h:real^N` THEN ONCE_REWRITE_TAC[GSYM NORM_LIFT] THEN
    REWRITE_TAC[LIFT_DROP] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`x:real^N`; `h:real^N`]) THEN
    REWRITE_TAC[GSYM NORM_LIFT; LIFT_DROP]]);;

let WAN_DIFF_QUOT_LIMIT = prove
 (`!(f:real^M->real^K) f' x v.
     (f has_derivative f') (at x)
     ==> ((\n. (&n + &1) % (f(x + inv(&n + &1) % v) - f x)) --> f' v) sequentially`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `((\t:real^1. f(x + drop t % v):real^K) has_vector_derivative (f':real^M->real^K) v)
    (at (vec 0))`
  MP_TAC THENL
   [MP_TAC(ISPECL [`\t:real^1. (x:real^M) + drop t % v`; `f:real^M->real^K`;
                   `v:real^M`; `f':real^M->real^K`; `vec 0:real^1`]
                  WAN_HVD_FRECHET_COMPOSE) THEN
    REWRITE_TAC[WAN_NT_LINE_VECTOR_DERIVATIVE; DROP_VEC; VECTOR_MUL_LZERO;
                VECTOR_ADD_RID; o_DEF] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[HAS_VECTOR_DERIVATIVE_AT_1D; LIM_AT_SEQUENTIALLY] THEN
  DISCH_THEN(MP_TAC o SPEC `\n. lift(inv(&n + &1))`) THEN
  REWRITE_TAC[o_DEF; SEQ_HARMONIC_OFFSET; GSYM LIFT_NUM; LIFT_EQ] THEN
  ANTS_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC REAL_LT_IMP_NZ THEN MATCH_MP_TAC REAL_LT_INV THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[LIFT_NUM; VECTOR_SUB_RZERO; LIFT_DROP; DROP_VEC; VECTOR_MUL_LZERO;
              VECTOR_ADD_RID; REAL_INV_INV]);;


let WAN_LIP_CONTINUOUS = prove
 (`!(u:real^M->real) L s.
     (!x y. x IN s /\ y IN s ==> abs(u x - u y) <= L * norm(x - y))
     ==> (\x. lift(u x)) continuous_on s`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LIPSCHITZ_IMP_CONTINUOUS_ON THEN
  EXISTS_TAC `L:real` THEN ASM_REWRITE_TAC[GSYM LIFT_SUB; NORM_LIFT]);;

let WAN_CONT_TRANSLATE = prove
 (`!(f:real^M->real^K) c. f continuous_on (:real^M) ==> (\x. f(x + c)) continuous_on (:real^M)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\x. (f:real^M->real^K)(x + c)) = f o (\x. x + c)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
  ASM_SIMP_TAC[CONTINUOUS_ON_ADD; CONTINUOUS_ON_ID; CONTINUOUS_ON_CONST] THEN
  ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_UNIV]);;

let WAN_CONT_LIFT_MUL = prove
 (`!(f:real^M->real) g s.
     (\x. lift(f x)) continuous_on s /\ (\x. lift(g x)) continuous_on s
     ==> (\x. lift(f x * g x)) continuous_on s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LIFT_CMUL] THEN
  MATCH_MP_TAC CONTINUOUS_ON_MUL THEN ASM_REWRITE_TAC[o_DEF]);;

let WAN_CONT_SUPPORT_INTEGRABLE = prove
 (`!(f:real^M->real^K) k.
     f continuous_on (:real^M) /\ compact k /\ (!x. ~(x IN k) ==> f x = vec 0)
     ==> f integrable_on (:real^M)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC WAN_NT_INTEGRABLE_COMPACT_SUPPORT THEN
  EXISTS_TAC `k:real^M->bool` THEN ASM_SIMP_TAC[OPEN_UNIV; SUBSET_UNIV]);;

let WAN_TRANSLATE_PRODUCT_INTEGRAL = prove
 (`!(u:real^M->real) (phi:real^M->real) c.
     integral (:real^M) (\x. lift(u x * phi(x + c))) =
     integral (:real^M) (\x. lift(u(x - c) * phi x))`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`\y:real^M. lift((u:real^M->real)(y - c) * (phi:real^M->real) y)`;
                 `(:real^M)`; `c:real^M`] INTEGRAL_TRANSLATION) THEN
  REWRITE_TAC[TRANSLATION_UNIV; VECTOR_ARITH `(c + x) - c:real^M = x`] THEN
  REWRITE_TAC[VECTOR_ADD_SYM]);;


let WAN_INDICATOR_CONST_INTEGRABLE = prove
 (`!(k:real^M->bool) (c:real^K).
     compact k ==> (\x. if x IN k then c else vec 0) integrable_on (:real^M)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[INTEGRABLE_RESTRICT_UNIV] THEN
  ASM_SIMP_TAC[INTEGRABLE_ON_CONST; MEASURABLE_COMPACT]);;

let WAN_SEGMENT_SUPPORT = prove
 (`!(phi:real^M->real) k v h.
     (!x. ~(x IN k) ==> phi x = &0) /\ &0 <= h /\ h <= &1
     ==> !x. ~(x IN {x + y | x IN k /\ y IN segment[vec 0,--v]})
             ==> phi(x + h % v) = &0 /\ phi x = &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `x:real^M` THEN
  REWRITE_TAC[IN_ELIM_THM; NOT_EXISTS_THM; DE_MORGAN_THM] THEN DISCH_TAC THEN
  CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN DISCH_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`x + h % v:real^M`; `--(h % v):real^M`]) THEN
    ASM_REWRITE_TAC[VECTOR_ARITH `x = (x + h % v) + --(h % v):real^M`] THEN
    REWRITE_TAC[IN_SEGMENT] THEN EXISTS_TAC `h:real` THEN ASM_REWRITE_TAC[] THEN
    VECTOR_ARITH_TAC;
    FIRST_X_ASSUM(MP_TAC o SPECL [`x:real^M`; `vec 0:real^M`]) THEN
    ASM_REWRITE_TAC[ENDS_IN_SEGMENT; VECTOR_ADD_RID]]);;


let WAN_INV_N1_BOUNDS = prove
 (`!n. &0 <= inv(&n + &1) /\ inv(&n + &1) <= &1 /\ (&n + &1) * inv(&n + &1) = &1`,
  GEN_TAC THEN SUBGOAL_THEN `&0 < &n + &1` ASSUME_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE; REAL_MUL_RINV; REAL_LT_IMP_NZ] THEN
  MATCH_MP_TAC REAL_INV_LE_1 THEN REAL_ARITH_TAC);;

let WAN_LIP_IBP_IDENTITY = prove
 (`!(u:real^M->real) (phi:real^M->real) k v n.
     (\x. lift(u x)) continuous_on (:real^M) /\ (\x. lift(phi x)) continuous_on (:real^M) /\
     compact k /\ (!x. ~(x IN k) ==> phi x = &0)
     ==> integral (:real^M)
           (\x. lift(u x * ((&n + &1) * (phi(x + inv(&n + &1) % v) - phi x)))) =
         integral (:real^M)
           (\x. lift(((&n + &1) * (u(x + inv(&n + &1) % --v) - u x)) * phi x))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `n:num` WAN_INV_N1_BOUNDS) THEN
  ABBREV_TAC `h = inv(&n + &1)` THEN STRIP_TAC THEN
  SUBGOAL_THEN `compact {x + y:real^M | x IN k /\ y IN segment[vec 0,--v]}` ASSUME_TAC THENL
   [MATCH_MP_TAC COMPACT_SUMS THEN ASM_REWRITE_TAC[COMPACT_SEGMENT]; ALL_TAC] THEN
  MP_TAC(ISPECL [`phi:real^M->real`; `k:real^M->bool`; `v:real^M`; `h:real`]
                WAN_SEGMENT_SUPPORT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `(\x. lift((u:real^M->real) x * phi(x + h % v))) integrable_on (:real^M) /\
    (\x. lift(u(x - h % v) * (phi:real^M->real) x)) integrable_on (:real^M) /\
    (\x. lift((u:real^M->real) x * phi x)) integrable_on (:real^M)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC WAN_CONT_SUPPORT_INTEGRABLE THEN
      EXISTS_TAC `{x + y:real^M | x IN k /\ y IN segment[vec 0,--v]}` THEN
      ASM_SIMP_TAC[REAL_MUL_RZERO; LIFT_NUM] THEN
      MATCH_MP_TAC WAN_CONT_LIFT_MUL THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`\x:real^M. lift((phi:real^M->real) x)`; `h % v:real^M`]
                    WAN_CONT_TRANSLATE) THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC WAN_CONT_SUPPORT_INTEGRABLE THEN EXISTS_TAC `k:real^M->bool` THEN
      ASM_SIMP_TAC[REAL_MUL_RZERO; LIFT_NUM] THEN
      MATCH_MP_TAC WAN_CONT_LIFT_MUL THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`\x:real^M. lift((u:real^M->real) x)`; `--(h % v):real^M`]
                    WAN_CONT_TRANSLATE) THEN
      ASM_REWRITE_TAC[VECTOR_ARITH `x + --(h % v):real^M = x - h % v`];
      MATCH_MP_TAC WAN_CONT_SUPPORT_INTEGRABLE THEN EXISTS_TAC `k:real^M->bool` THEN
      ASM_SIMP_TAC[REAL_MUL_RZERO; LIFT_NUM] THEN
      MATCH_MP_TAC WAN_CONT_LIFT_MUL THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\x. lift((u:real^M->real) x * ((&n + &1) * (phi(x + h % v) - phi x)))) =
    (\x. (&n + &1) % (lift(u x * phi(x + h % v)) - lift(u x * phi x))) /\
    (\x. lift(((&n + &1) * (u(x + h % --v) - u x)) * (phi:real^M->real) x)) =
    (\x. (&n + &1) % (lift(u(x - h % v) * phi x) - lift(u x * phi x)))`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [REWRITE_TAC[FUN_EQ_THM; VECTOR_ARITH `x + h % --v:real^M = x - h % v`] THEN
    REWRITE_TAC[GSYM LIFT_SUB; GSYM LIFT_CMUL; LIFT_EQ] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[INTEGRAL_CMUL; INTEGRABLE_SUB; INTEGRAL_SUB] THEN
  REWRITE_TAC[WAN_TRANSLATE_PRODUCT_INTEGRAL]);;


let WAN_DQ_BOUND = prove
 (`!(f:real^M->real) C x v n.
     (!x y. abs(f x - f y) <= C * norm(x - y))
     ==> abs((&n + &1) * (f(x + inv(&n + &1) % v) - f x)) <= C * norm v`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `n:num` WAN_INV_N1_BOUNDS) THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`x + inv(&n + &1) % v:real^M`; `x:real^M`]) THEN
  REWRITE_TAC[VECTOR_ARITH `(x + h % v) - x:real^M = h % v`; NORM_MUL; REAL_ABS_MUL] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`; REAL_ARITH `&0 <= &n + &1`] THEN
  DISCH_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(&n + &1) * C * inv(&n + &1) * norm(v:real^M)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN
    UNDISCH_TAC `(&n + &1) * inv(&n + &1) = &1` THEN CONV_TAC REAL_RING]);;


let WAN_LIP_IBP_LHS = prove
 (`!(u:real^M->real) (phi:real^M->real) k v.
     (\x. lift(u x)) continuous_on (:real^M) /\ smooth_map_on (:real^M) (\x. lift(phi x)) /\
     compact k /\ (!x. ~(x IN k) ==> phi x = &0)
     ==> ((\n. integral (:real^M)
                 (\x. lift(u x * ((&n + &1) * (phi(x + inv(&n + &1) % v) - phi x))))) -->
          integral (:real^M)
            (\x. lift(u x * drop(frechet_derivative (\y. lift(phi y)) (at x) v))))
         sequentially`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `kp = {x + y:real^M | x IN k /\ y IN segment[vec 0,--v]}` THEN
  SUBGOAL_THEN `compact(kp:real^M->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "kp" THEN MATCH_MP_TAC COMPACT_SUMS THEN ASM_REWRITE_TAC[COMPACT_SEGMENT];
    ALL_TAC] THEN
  SUBGOAL_THEN `?U. !x. x IN kp ==> abs((u:real^M->real) x) <= U` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\x:real^M. lift((u:real^M->real) x)`; `kp:real^M->bool`]
                  COMPACT_CONTINUOUS_IMAGE) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_UNIV]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
    REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE; NORM_LIFT] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`phi:real^M->real`; `k:real^M->bool`] WAN_SMOOTH_SUPPORT_LIPSCHITZ) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `C:real`) THEN
  SUBGOAL_THEN `(\x. lift((phi:real^M->real) x)) continuous_on (:real^M)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON]; ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\n x. lift((u:real^M->real) x * ((&n + &1) * (phi(x + inv(&n + &1) % v) - phi x)))`;
    `\x. lift((u:real^M->real) x * drop(frechet_derivative (\y. lift(phi y)) (at x) v))`;
    `\x:real^M. if x IN kp then lift(U * C * norm(v:real^M)) else vec 0`;
    `(:real^M)`] DOMINATED_CONVERGENCE) THEN
  REWRITE_TAC[IN_UNIV] THEN ANTS_TAC THENL
   [ALL_TAC; SIMP_TAC[]] THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `n:num` THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC WAN_CONT_SUPPORT_INTEGRABLE THEN EXISTS_TAC `kp:real^M->bool` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC WAN_CONT_LIFT_MUL THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[LIFT_CMUL; LIFT_SUB] THEN MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUB THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`\x:real^M. lift((phi:real^M->real) x)`; `inv(&n + &1) % v:real^M`]
                    WAN_CONT_TRANSLATE) THEN
      ASM_REWRITE_TAC[];
      X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`phi:real^M->real`; `k:real^M->bool`; `v:real^M`; `inv(&n + &1)`]
                    WAN_SEGMENT_SUPPORT) THEN
      ASM_REWRITE_TAC[WAN_INV_N1_BOUNDS] THEN DISCH_THEN(MP_TAC o SPEC `x:real^M`) THEN
      EXPAND_TAC "kp" THEN ASM_REWRITE_TAC[] THEN
      SIMP_TAC[REAL_SUB_REFL; REAL_MUL_RZERO; LIFT_NUM]];
    ASM_SIMP_TAC[WAN_INDICATOR_CONST_INTEGRABLE];
    MAP_EVERY X_GEN_TAC [`n:num`; `x:real^M`] THEN REWRITE_TAC[] THEN
    COND_CASES_TAC THENL
     [REWRITE_TAC[NORM_LIFT; LIFT_DROP; REAL_ABS_MUL] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_ABS_POS] THEN
      CONJ_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[GSYM REAL_ABS_MUL; REAL_ABS_POS] THEN MATCH_MP_TAC WAN_DQ_BOUND THEN
      ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`phi:real^M->real`; `k:real^M->bool`; `v:real^M`; `inv(&n + &1)`]
                    WAN_SEGMENT_SUPPORT) THEN
      ASM_REWRITE_TAC[WAN_INV_N1_BOUNDS] THEN DISCH_THEN(MP_TAC o SPEC `x:real^M`) THEN
      EXPAND_TAC "kp" THEN ASM_REWRITE_TAC[] THEN
      SIMP_TAC[REAL_SUB_REFL; REAL_MUL_RZERO; LIFT_NUM; NORM_0; DROP_VEC; REAL_LE_REFL]];
    X_GEN_TAC `x:real^M` THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `lift((u:real^M->real) x *
           drop(frechet_derivative (\y. lift((phi:real^M->real) y)) (at x) v)) =
      u x % frechet_derivative (\y. lift(phi y)) (at x) v`
    SUBST1_TAC THENL [REWRITE_TAC[LIFT_CMUL; LIFT_DROP]; ALL_TAC] THEN
    SUBGOAL_THEN
     `(\n. lift((u:real^M->real) x *
                ((&n + &1) * ((phi:real^M->real)(x + inv(&n + &1) % v) - phi x)))) =
      (\n. u x % ((&n + &1) % (lift(phi(x + inv(&n + &1) % v)) - lift(phi x))))`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; LIFT_CMUL; LIFT_SUB]; ALL_TAC] THEN
    MATCH_MP_TAC LIM_CMUL THEN
    MP_TAC(ISPECL [`\y:real^M. lift((phi:real^M->real) y)`;
                   `frechet_derivative (\y:real^M. lift((phi:real^M->real) y)) (at x)`;
                   `x:real^M`; `v:real^M`] WAN_DIFF_QUOT_LIMIT) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_IMP; RIGHT_IMP_FORALL_THM] SMOOTH_MAP_ON_HAS_DERIVATIVE) THEN
    EXISTS_TAC `(:real^M)` THEN ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV]]);;


let WAN_LIP_IBP_RHS = prove
 (`!(u:real^M->real) L (phi:real^M->real) k v.
     (!x y. abs(u x - u y) <= L * norm(x - y)) /\
     smooth_map_on (:real^M) (\x. lift(phi x)) /\
     compact k /\ (!x. ~(x IN k) ==> phi x = &0)
     ==> (\x. lift(drop(frechet_derivative (\y. lift(u y)) (at x) v) * phi x))
           absolutely_integrable_on (:real^M) /\
         ((\n. integral (:real^M)
                 (\x. lift(((&n + &1) * (u(x + inv(&n + &1) % --v) - u x)) * phi x))) -->
          --(integral (:real^M)
               (\x. lift(drop(frechet_derivative (\y. lift(u y)) (at x) v) * phi x))))
         sequentially`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(\x. lift((u:real^M->real) x)) continuous_on (:real^M)` ASSUME_TAC THENL
   [MATCH_MP_TAC WAN_LIP_CONTINUOUS THEN EXISTS_TAC `L:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\x. lift((phi:real^M->real) x)) continuous_on (:real^M)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON]; ALL_TAC] THEN
  MP_TAC(ISPECL [`phi:real^M->real`; `k:real^M->bool`] WAN_SMOOTH_SUPPORT_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `P:real` o CONJUNCT1) THEN
  ABBREV_TAC `t = {x:real^M | ~((\y. lift((u:real^M->real) y)) differentiable at x)}` THEN
  SUBGOAL_THEN `negligible(t:real^M->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "t" THEN MATCH_MP_TAC RADEMACHER_UNIV THEN EXISTS_TAC `L:real` THEN
    ASM_REWRITE_TAC[GSYM LIFT_SUB; NORM_LIFT];
    ALL_TAC] THEN
  ABBREV_TAC
   `g = \x:real^M. lift(--(drop(frechet_derivative (\y. lift((u:real^M->real) y)) (at x) v)) *
                         (phi:real^M->real) x)` THEN
  SUBGOAL_THEN
   `!n x. norm(lift(((&n + &1) * ((u:real^M->real)(x + inv(&n + &1) % --v) - u x)) *
                    (phi:real^M->real) x))
          <= drop(if x IN k then lift((L * norm(v:real^M)) * P) else vec 0)`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`n:num`; `x:real^M`] THEN COND_CASES_TAC THENL
     [REWRITE_TAC[NORM_LIFT; LIFT_DROP; REAL_ABS_MUL] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_ABS_POS] THEN
      REWRITE_TAC[GSYM REAL_ABS_MUL; REAL_ABS_POS] THEN CONJ_TAC THENL
       [MP_TAC(ISPECL [`u:real^M->real`; `L:real`; `x:real^M`; `--v:real^M`; `n:num`]
                      WAN_DQ_BOUND) THEN
        ASM_REWRITE_TAC[NORM_NEG];
        ASM_REWRITE_TAC[]];
      ASM_SIMP_TAC[REAL_MUL_RZERO; LIFT_NUM; NORM_0; DROP_VEC; REAL_LE_REFL]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. ~(x IN t)
        ==> ((\n. lift(((&n + &1) * ((u:real^M->real)(x + inv(&n + &1) % --v) - u x)) *
                        (phi:real^M->real) x)) --> (g:real^M->real^1) x) sequentially`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^M` THEN EXPAND_TAC "t" THEN REWRITE_TAC[IN_ELIM_THM; NOT_CLAUSES] THEN
    DISCH_TAC THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP LINEAR_FRECHET_DERIVATIVE) THEN
    MP_TAC(REWRITE_RULE[FRECHET_DERIVATIVE_WORKS]
      (ASSUME `(\y. lift((u:real^M->real) y)) differentiable at x`)) THEN
    DISCH_THEN(MP_TAC o SPEC `--v:real^M` o MATCH_MP WAN_DIFF_QUOT_LIMIT) THEN
    DISCH_THEN(MP_TAC o SPEC `(phi:real^M->real) x` o MATCH_MP LIM_CMUL) THEN
    EXPAND_TAC "g" THEN
    MATCH_MP_TAC(MESON[] `!f g:num->real^1 l m:real^1.
                    f = g /\ l = m ==> (f --> l) sequentially ==> (g --> m) sequentially`) THEN
    CONJ_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; GSYM LIFT_SUB; GSYM LIFT_CMUL; LIFT_EQ] THEN REAL_ARITH_TAC;
      ASM_SIMP_TAC[LINEAR_NEG] THEN
      REWRITE_TAC[GSYM DROP_EQ; DROP_CMUL; DROP_NEG; LIFT_DROP] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\n x. lift(((&n + &1) * ((u:real^M->real)(x + inv(&n + &1) % --v) - u x)) *
                (phi:real^M->real) x)`;
    `g:real^M->real^1`;
    `\x:real^M. if x IN k then lift((L * norm(v:real^M)) * P) else vec 0`;
    `(:real^M)`; `t:real^M->bool`] DOMINATED_CONVERGENCE_AE) THEN
  REWRITE_TAC[IN_UNIV; IN_DIFF] THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[WAN_INDICATOR_CONST_INTEGRABLE] THEN X_GEN_TAC `n:num` THEN
    MATCH_MP_TAC WAN_CONT_SUPPORT_INTEGRABLE THEN EXISTS_TAC `k:real^M->bool` THEN
    ASM_SIMP_TAC[REAL_MUL_RZERO; LIFT_NUM] THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN MATCH_MP_TAC WAN_CONT_LIFT_MUL THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[LIFT_CMUL; LIFT_SUB] THEN
    MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN MATCH_MP_TAC CONTINUOUS_ON_SUB THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`\x:real^M. lift((u:real^M->real) x)`; `inv(&n + &1) % --v:real^M`]
                  WAN_CONT_TRANSLATE) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `(\x. lift(drop(frechet_derivative (\y. lift((u:real^M->real) y)) (at x) v) *
              (phi:real^M->real) x)) = (\x. --((g:real^M->real^1) x))`
  ASSUME_TAC THENL
   [EXPAND_TAC "g" THEN REWRITE_TAC[FUN_EQ_THM; GSYM LIFT_NEG; LIFT_EQ] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[INTEGRAL_NEG; VECTOR_NEG_NEG] THEN
  MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_NEG THEN
  MATCH_MP_TAC MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_ABSOLUTELY_INTEGRABLE_AE THEN
  MAP_EVERY EXISTS_TAC
   [`\x:real^M. if x IN k then lift((L * norm(v:real^M)) * P) else vec 0`; `t:real^M->bool`] THEN
  ASM_SIMP_TAC[INTEGRABLE_IMP_MEASURABLE; WAN_INDICATOR_CONST_INTEGRABLE; IN_UNIV; IN_DIFF] THEN
  X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
  MATCH_MP_TAC(ISPEC `sequentially` LIM_NORM_UBOUND) THEN
  EXISTS_TAC `\n. lift(((&n + &1) * ((u:real^M->real)(x + inv(&n + &1) % --v) - u x)) *
                       (phi:real^M->real) x)` THEN
  ASM_SIMP_TAC[TRIVIAL_LIMIT_SEQUENTIALLY; EVENTUALLY_TRUE]);;


let WAN_LIP_IBP_UNIV = prove
 (`!(u:real^M->real) L (phi:real^M->real) k v.
     (!x y. abs(u x - u y) <= L * norm(x - y)) /\
     smooth_map_on (:real^M) (\x. lift(phi x)) /\
     compact k /\ (!x. ~(x IN k) ==> phi x = &0)
     ==> (\x. lift(drop(frechet_derivative (\y. lift(u y)) (at x) v) * phi x))
           absolutely_integrable_on (:real^M) /\
         integral (:real^M) (\x. lift(u x * drop(frechet_derivative (\y. lift(phi y)) (at x) v))) =
         --(integral (:real^M)
              (\x. lift(drop(frechet_derivative (\y. lift(u y)) (at x) v) * phi x)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`u:real^M->real`; `L:real`; `phi:real^M->real`; `k:real^M->bool`; `v:real^M`]
                WAN_LIP_IBP_RHS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(\x. lift((u:real^M->real) x)) continuous_on (:real^M)` ASSUME_TAC THENL
   [MATCH_MP_TAC WAN_LIP_CONTINUOUS THEN EXISTS_TAC `L:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`u:real^M->real`; `phi:real^M->real`; `k:real^M->bool`; `v:real^M`]
                WAN_LIP_IBP_LHS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC(ISPEC `sequentially` LIM_UNIQUE) THEN
  EXISTS_TAC `\n. integral (:real^M)
                    (\x. lift((u:real^M->real) x *
                              ((&n + &1) * ((phi:real^M->real)(x + inv(&n + &1) % v) - phi x))))` THEN
  ASM_REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN
  MP_TAC(ISPECL [`u:real^M->real`; `phi:real^M->real`; `k:real^M->bool`; `v:real^M`]
                WAN_LIP_IBP_IDENTITY) THEN
  ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON]);;


(* ------------------------------------------------------------------------- *)
(* Compact sets have compact neighbourhoods inside open supersets, with an   *)
(* open set in between.                                                       *)
(* ------------------------------------------------------------------------- *)

let WAN_COMPACT_NBHD = prove
 (`!(s:real^N->bool) k.
     open s /\ compact k /\ k SUBSET s
     ==> ?d. &0 < d /\
             compact {x + y | x IN k /\ y IN cball(vec 0,d)} /\
             {x + y | x IN k /\ y IN cball(vec 0,d)} SUBSET s /\
             open {x + y | x IN k /\ y IN ball(vec 0,d)} /\
             k SUBSET {x + y | x IN k /\ y IN ball(vec 0,d)} /\
             {x + y | x IN k /\ y IN ball(vec 0,d)} SUBSET
             {x + y | x IN k /\ y IN cball(vec 0,d)}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:real^N->bool`; `(:real^N) DIFF s`] SEPARATE_COMPACT_CLOSED) THEN
  ASM_SIMP_TAC[GSYM OPEN_CLOSED] THEN ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `d / &2` THEN ASM_REWRITE_TAC[REAL_HALF] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC COMPACT_SUMS THEN ASM_REWRITE_TAC[COMPACT_CBALL];
    REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_CBALL_0] THEN X_GEN_TAC `z:real^N` THEN
    DISCH_THEN(X_CHOOSE_THEN `x:real^N` (X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`x:real^N`; `x + y:real^N`]) THEN
    ASM_REWRITE_TAC[IN_DIFF; IN_UNIV; dist; VECTOR_ARITH `x - (x + y):real^N = --y`;
                    NORM_NEG] THEN
    ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC OPEN_SUMS THEN REWRITE_TAC[OPEN_BALL];
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    MAP_EVERY EXISTS_TAC [`x:real^N`; `vec 0:real^N`] THEN
    ASM_REWRITE_TAC[CENTRE_IN_BALL; VECTOR_ADD_RID; REAL_HALF];
    MP_TAC(ISPECL [`vec 0:real^N`; `d / &2`] BALL_SUBSET_CBALL) THEN SET_TAC[]]);;

let WAN_LIP_IBP = prove
 (`!m:M->bool. WAN_LIP_IBP_STATEMENT m`,
  GEN_TAC THEN REWRITE_TAC[WAN_LIP_IBP_STATEMENT] THEN
  MAP_EVERY X_GEN_TAC [`s:real^M->bool`; `u:real^M->real`; `phi:real^M->real`; `v:real^M`] THEN
  REWRITE_TAC[wan_test] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^M->bool`; `k:real^M->bool`] WAN_COMPACT_NBHD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `kk = {x + y:real^M | x IN k /\ y IN cball(vec 0,d)}` THEN
  ABBREV_TAC `uu = {x + y:real^M | x IN k /\ y IN ball(vec 0,d)}` THEN
  FIRST_ASSUM(MP_TAC o SPEC `kk:real^M->bool` o REWRITE_RULE[wan_loclip]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `L:real`) THEN
  MP_TAC(ISPECL [`\x:real^M. lift((u:real^M->real) x)`; `kk:real^M->bool`; `max L (&0)`]
                KIRSZBRAUN) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[REAL_ARITH `&0 <= max L (&0)`; GSYM LIFT_SUB; NORM_LIFT] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `L * norm(x - y:real^M)` THEN ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^M->real^1` STRIP_ASSUME_TAC) THEN
  RULE_ASSUM_TAC BETA_RULE THEN
  MP_TAC(ISPECL [`\x:real^M. drop((g:real^M->real^1) x)`; `max L (&0)`; `phi:real^M->real`;
                 `k:real^M->bool`; `v:real^M`] WAN_LIP_IBP_UNIV) THEN
  REWRITE_TAC[LIFT_DROP; ETA_AX] THEN ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[GSYM DROP_SUB; GSYM NORM_1] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\x. lift((u:real^M->real) x * drop(frechet_derivative (\y. lift((phi:real^M->real) y)) (at x) v))) =
    (\x. lift(drop((g:real^M->real^1) x) * drop(frechet_derivative (\y. lift(phi y)) (at x) v))) /\
    (\x. lift(drop(frechet_derivative (\y. lift((u:real^M->real) y)) (at x) v) * (phi:real^M->real) x)) =
    (\x. lift(drop(frechet_derivative (g:real^M->real^1) (at x) v) * phi x))`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN CONJ_TAC THEN X_GEN_TAC `x:real^M` THEN
    ASM_CASES_TAC `(x:real^M) IN k` THENL
     [SUBGOAL_THEN `(x:real^M) IN kk` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `x:real^M` o check (is_forall o concl)) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[LIFT_DROP];
      ALL_TAC;
      AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN
      MATCH_MP_TAC LRG_FRECHET_DERIVATIVE_EQ_OPEN THEN EXISTS_TAC `uu:real^M->bool` THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      X_GEN_TAC `z:real^M` THEN DISCH_TAC THEN CONV_TAC SYM_CONV THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
      ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_MUL_LZERO; REAL_MUL_RZERO] THEN
    MP_TAC(ISPECL [`phi:real^M->real`; `k:real^M->bool`; `v:real^M`; `x:real^M`]
                  WAN_TEST_DERIV_ZERO) THEN
    ASM_SIMP_TAC[DROP_VEC; REAL_MUL_RZERO];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!f:real^M->real^1. (!x. ~(x IN k) ==> f x = vec 0)
                       ==> (f absolutely_integrable_on s <=> f absolutely_integrable_on (:real^M)) /\
                           integral s f = integral (:real^M) f`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THENL
     [MATCH_MP_TAC WAN_ABS_INTEGRABLE_SUPPORT_SUBSET THEN EXISTS_TAC `k:real^M->bool` THEN
      ASM_REWRITE_TAC[SUBSET_UNIV];
      MATCH_MP_TAC WAN_INTEGRAL_SUPPORT_SUBSET THEN EXISTS_TAC `k:real^M->bool` THEN
      ASM_REWRITE_TAC[SUBSET_UNIV]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(!x. ~(x IN k) ==> lift(drop(frechet_derivative (g:real^M->real^1) (at x) v) *
                            (phi:real^M->real) x) = vec 0) /\
    (!x. ~(x IN k) ==> lift(drop(g x) *
                            drop(frechet_derivative (\y. lift(phi y)) (at x) v)) = vec 0)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN X_GEN_TAC `x:real^M` THEN DISCH_TAC THENL
     [ASM_SIMP_TAC[REAL_MUL_RZERO; LIFT_NUM];
      MP_TAC(ISPECL [`phi:real^M->real`; `k:real^M->bool`; `v:real^M`; `x:real^M`]
                    WAN_TEST_DERIV_ZERO) THEN
      ASM_SIMP_TAC[DROP_VEC; REAL_MUL_RZERO; LIFT_NUM]];
    ALL_TAC] THEN
  ASM_SIMP_TAC[]);;


(* ------------------------------------------------------------------------- *)
(* A smooth Urysohn function: a test function on s equal to 1 on a compact  *)
(* subset k (finite sum of bumps, then the smooth step).                     *)
(* ------------------------------------------------------------------------- *)

let WAN_SMOOTH_URYSOHN = prove
 (`!(s:real^N->bool) k.
     open s /\ compact k /\ k SUBSET s
     ==> ?psi. wan_test s psi /\ (!x. &0 <= psi x /\ psi x <= &1) /\
               (!x. x IN k ==> psi x = &1)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `k:real^N->bool`] WAN_COMPACT_NBHD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPEC `d / &2` (MATCH_MP COMPACT_IMP_TOTALLY_BOUNDED
    (ASSUME `compact(k:real^N->bool)`))) THEN
  ASM_REWRITE_TAC[REAL_HALF] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real^N->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `\y:real^N. smooth_step(sum c (\x. smooth_bump (d / &2) d (y - x)))` THEN
  REWRITE_TAC[SMOOTH_STEP_BOUNDS; wan_test] THEN REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN
     `(\y:real^N. lift(smooth_step(sum c (\x. smooth_bump (d / &2) d (y - x))))) =
      (lift o smooth_step o drop) o (\y. lift(sum c (\x. drop(lift(smooth_bump (d / &2) d (y - x))))))`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_DROP]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `(:real^1)` THEN
    REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV; SMOOTH_STEP_SMOOTH] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_LIFT_SUM THEN ASM_REWRITE_TAC[OPEN_UNIV] THEN
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`\y:real^N. lift(smooth_bump (d / &2) d y)`; `--x:real^N`]
                  PDE_SMOOTH_TRANSLATE) THEN
    ASM_SIMP_TAC[SMOOTH_BUMP_SMOOTH; VECTOR_ARITH `y + --x:real^N = y - x`;
                 REAL_ARITH `&0 < d ==> &0 <= d / &2 /\ d / &2 < d`];
    EXISTS_TAC `{x + y:real^N | x IN k /\ y IN cball(vec 0,d)}` THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    MATCH_MP_TAC SMOOTH_STEP_0 THEN MATCH_MP_TAC REAL_EQ_IMP_LE THEN
    MATCH_MP_TAC SUM_EQ_0 THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC SMOOTH_BUMP_0 THEN
    REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
    REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    UNDISCH_TAC `~((y:real^N) IN {x + y | x IN k /\ y IN cball(vec 0,d)})` THEN
    REWRITE_TAC[IN_ELIM_THM] THEN
    MAP_EVERY EXISTS_TAC [`x:real^N`; `y - x:real^N`] THEN
    REWRITE_TAC[IN_CBALL_0; VECTOR_ARITH `x + y - x:real^N = y`] THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ASM_REAL_ARITH_TAC];
    X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN MATCH_MP_TAC SMOOTH_STEP_1 THEN
    SUBGOAL_THEN `?x:real^N. x IN c /\ y IN ball(x,d / &2)` STRIP_ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `smooth_bump (d / &2) d (y - x:real^N)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_EQ_IMP_LE THEN CONV_TAC SYM_CONV THEN
      MATCH_MP_TAC SMOOTH_BUMP_1 THEN
      UNDISCH_TAC `(y:real^N) IN ball(x,d / &2)` THEN
      REWRITE_TAC[IN_BALL; dist] THEN MP_TAC(ISPECL [`x:real^N`; `y:real^N`] NORM_SUB) THEN
      ASM_REAL_ARITH_TAC;
      MP_TAC(ISPECL [`{x:real^N}`; `c:real^N->bool`;
                     `\x:real^N. smooth_bump (d / &2) d (y - x)`] SUM_SUBSET_SIMPLE) THEN
      ASM_REWRITE_TAC[SUM_SING; SING_SUBSET; SMOOTH_BUMP_BOUNDS]]]);;


(* ------------------------------------------------------------------------- *)
(* Continuity and local integrability of locally Lipschitz functions; the   *)
(* a.e. derivative is locally bounded; WAN_LIP_W12.                          *)
(* ------------------------------------------------------------------------- *)

let WAN_LOCLIP_CONTINUOUS_ON = prove
 (`!(s:real^M->bool) u. open s /\ wan_loclip s u ==> (\x. lift(u x)) continuous_on s`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_AT] THEN
  X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:real^M` o GEN_REWRITE_RULE I [OPEN_CONTAINS_CBALL]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `cball(x:real^M,r)` o REWRITE_RULE[wan_loclip]) THEN
  ASM_REWRITE_TAC[COMPACT_CBALL] THEN DISCH_THEN(X_CHOOSE_TAC `L:real`) THEN
  SUBGOAL_THEN `(\x. lift((u:real^M->real) x)) continuous_on ball(x,r)` MP_TAC THENL
   [MATCH_MP_TAC WAN_LIP_CONTINUOUS THEN EXISTS_TAC `L:real` THEN
    ASM_MESON_TAC[BALL_SUBSET_CBALL; SUBSET];
    SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_AT; OPEN_BALL] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[CENTRE_IN_BALL]]);;

let WAN_CONTINUOUS_ON_LLOC = prove
 (`!(s:real^N->bool) (f:real^N->real^K). f continuous_on s ==> wan_lloc s f`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[wan_lloc] THEN X_GEN_TAC `k:real^N->bool` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `(f:real^N->real^K) continuous_on k` ASSUME_TAC THENL
   [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`f:real^N->real^K`; `k:real^N->bool`] COMPACT_CONTINUOUS_IMAGE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
  REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_ABSOLUTELY_INTEGRABLE THEN
  EXISTS_TAC `\x:real^N. lift B` THEN
  ASM_SIMP_TAC[LIFT_DROP; INTEGRABLE_ON_CONST; MEASURABLE_COMPACT] THEN
  MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
  ASM_SIMP_TAC[LEBESGUE_MEASURABLE_COMPACT]);;

let WAN_CONTINUOUS_ON_L2LOC = prove
 (`!(s:real^N->bool) (f:real^N->real^K). f continuous_on s ==> wan_l2loc s f`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[wan_l2loc] THEN X_GEN_TAC `k:real^N->bool` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `(f:real^N->real^K) continuous_on k` ASSUME_TAC THENL
   [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`f:real^N->real^K`; `k:real^N->bool`] COMPACT_CONTINUOUS_IMAGE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
  REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[lspace; IN_ELIM_THM; RPOW_POW] THEN
  SUBGOAL_THEN `(f:real^N->real^K) measurable_on k` ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
    ASM_SIMP_TAC[LEBESGUE_MEASURABLE_COMPACT];
    ASM_REWRITE_TAC[]] THEN
  MATCH_MP_TAC MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_INTEGRABLE THEN
  EXISTS_TAC `\x:real^N. lift(B pow 2)` THEN
  ASM_SIMP_TAC[LIFT_DROP; INTEGRABLE_ON_CONST; MEASURABLE_COMPACT] THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
    ASM_SIMP_TAC[LEBESGUE_MEASURABLE_COMPACT] THEN
    MATCH_MP_TAC CONTINUOUS_ON_LIFT_POW THEN
    MATCH_MP_TAC CONTINUOUS_ON_LIFT_NORM_COMPOSE THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN REWRITE_TAC[NORM_LIFT] THEN
    REWRITE_TAC[REAL_ABS_POW; REAL_ABS_NORM] THEN MATCH_MP_TAC REAL_POW_LE2 THEN
    ASM_SIMP_TAC[NORM_POS_LE]]);;


let WAN_LIP_DERIV_BOUND = prove
 (`!(u:real^M->real) L x r h.
     &0 < r /\
     (!y z. y IN ball(x,r) /\ z IN ball(x,r) ==> abs(u y - u z) <= L * norm(y - z)) /\
     (\y. lift(u y)) differentiable at x
     ==> abs(drop(frechet_derivative (\y. lift(u y)) (at x) h)) <= L * norm h`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP WAN_DIFF_QUOT_LIMIT o REWRITE_RULE[FRECHET_DERIVATIVE_WORKS]) THEN
  DISCH_THEN(ASSUME_TAC o BETA_RULE o SPEC `h:real^M`) THEN
  REWRITE_TAC[GSYM NORM_1] THEN MATCH_MP_TAC(ISPEC `sequentially` LIM_NORM_UBOUND) THEN
  EXISTS_TAC `\n. (&n + &1) % (lift((u:real^M->real)(x + inv(&n + &1) % h)) - lift(u x))` THEN
  ASM_REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY; EVENTUALLY_SEQUENTIALLY] THEN
  SUBGOAL_THEN `?N. !n. N <= n ==> inv(&n + &1) * norm(h:real^M) < r` STRIP_ASSUME_TAC THENL
   [MP_TAC(SPEC `&1` SEQ_HARMONIC_OFFSET) THEN
    REWRITE_TAC[LIM_SEQUENTIALLY; DIST_0; NORM_LIFT] THEN
    DISCH_THEN(MP_TAC o SPEC `r / (norm(h:real^M) + &1)`) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPEC `h:real^M` NORM_POS_LE) THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN
    MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `n:num` THEN
    MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[] THEN
    MP_TAC(SPEC `n:num` WAN_INV_N1_BOUNDS) THEN STRIP_TAC THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`] THEN
    MP_TAC(ISPEC `h:real^M` NORM_POS_LE) THEN
    SIMP_TAC[REAL_LT_RDIV_EQ; REAL_ARITH `&0 <= x ==> &0 < x + &1`] THEN
    UNDISCH_TAC `&0 <= inv(&n + &1)` THEN
    MAP_EVERY SPEC_TAC [(`inv(&n + &1)`,`a:real`); (`norm(h:real^M)`,`b:real`)] THEN
    REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `a * (b + &1)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `N:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPEC `n:num` WAN_INV_N1_BOUNDS) THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`x + inv(&n + &1) % h:real^M`; `x:real^M`]) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[IN_BALL; dist; VECTOR_ARITH `x - (x + h):real^M = --h`; NORM_NEG;
                VECTOR_SUB_REFL; NORM_0; NORM_MUL] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`];
    ALL_TAC] THEN
  REWRITE_TAC[VECTOR_ARITH `(x + h) - x:real^M = h`; NORM_MUL; GSYM LIFT_SUB;
              GSYM LIFT_CMUL; NORM_LIFT; REAL_ABS_MUL] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`; REAL_ARITH `&0 <= &n + &1`] THEN
  DISCH_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(&n + &1) * L * inv(&n + &1) * norm(h:real^M)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN
    UNDISCH_TAC `(&n + &1) * inv(&n + &1) = &1` THEN CONV_TAC REAL_RING]);;


let WAN_LIP_WPD = prove
 (`!(s:real^M->bool) (u:real^M->real) i.
     open s /\ wan_loclip s u
     ==> wan_wpd s i (\x. lift(u x)) (\x. lift(wan_dpart i u x))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[wan_wpd] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC WAN_CONTINUOUS_ON_LLOC THEN ASM_SIMP_TAC[WAN_LOCLIP_CONTINUOUS_ON];
    REWRITE_TAC[wan_lloc] THEN X_GEN_TAC `k:real^M->bool` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`s:real^M->bool`; `k:real^M->bool`] WAN_SMOOTH_URYSOHN) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `psi:real^M->real` STRIP_ASSUME_TAC) THEN
    MP_TAC(SPEC `(:M)` WAN_LIP_IBP) THEN REWRITE_TAC[WAN_LIP_IBP_STATEMENT] THEN
    DISCH_THEN(MP_TAC o SPECL [`s:real^M->bool`; `u:real^M->real`; `psi:real^M->real`;
                               `basis i:real^M`]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN DISCH_TAC THEN
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_EQ THEN
    EXISTS_TAC `\x. lift(drop(frechet_derivative (\y. lift((u:real^M->real) y)) (at x)
                                (basis i)) * psi x)` THEN
    ASM_SIMP_TAC[wan_dpart; REAL_MUL_RID] THEN
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
    EXISTS_TAC `s:real^M->bool` THEN ASM_SIMP_TAC[LEBESGUE_MEASURABLE_COMPACT];
    X_GEN_TAC `phi:real^M->real` THEN DISCH_TAC THEN
    MP_TAC(SPEC `(:M)` WAN_LIP_IBP) THEN REWRITE_TAC[WAN_LIP_IBP_STATEMENT] THEN
    DISCH_THEN(MP_TAC o SPECL [`s:real^M->bool`; `u:real^M->real`; `phi:real^M->real`;
                               `basis i:real^M`]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT2) THEN
    REWRITE_TAC[wan_dpart; GSYM LIFT_CMUL] THEN
    REWRITE_TAC[REAL_MUL_SYM] THEN SIMP_TAC[]]);;

let WAN_LIP_W12 = prove
 (`!m:M->bool. WAN_LIP_W12_STATEMENT m`,
  GEN_TAC THEN REWRITE_TAC[WAN_LIP_W12_STATEMENT] THEN
  MAP_EVERY X_GEN_TAC [`s:real^M->bool`; `u:real^M->real`] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[WAN_LIP_WPD] THEN
  REWRITE_TAC[num_CONV `1`; wan_hk] THEN CONJ_TAC THENL
   [MATCH_MP_TAC WAN_CONTINUOUS_ON_L2LOC THEN ASM_SIMP_TAC[WAN_LOCLIP_CONTINUOUS_ON];
    ALL_TAC] THEN
  X_GEN_TAC `i:num` THEN REWRITE_TAC[GSYM ONE] THEN STRIP_TAC THEN
  EXISTS_TAC `\x. lift(wan_dpart i (u:real^M->real) x)` THEN
  ASM_SIMP_TAC[WAN_LIP_WPD] THEN REWRITE_TAC[wan_l2loc] THEN
  X_GEN_TAC `k:real^M->bool` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^M->bool`; `k:real^M->bool`] WAN_COMPACT_NBHD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `kk = {x + y:real^M | x IN k /\ y IN cball(vec 0,d)}` THEN
  ABBREV_TAC `uu = {x + y:real^M | x IN k /\ y IN ball(vec 0,d)}` THEN
  FIRST_ASSUM(MP_TAC o SPEC `kk:real^M->bool` o REWRITE_RULE[wan_loclip]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `L:real`) THEN
  SUBGOAL_THEN `negligible {x | x IN uu /\ ~((\y. lift((u:real^M->real) y)) differentiable at x)}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC RADEMACHER_OPEN THEN ASM_REWRITE_TAC[] THEN EXISTS_TAC `L:real` THEN
    REWRITE_TAC[GSYM LIFT_SUB; NORM_LIFT] THEN ASM_MESON_TAC[SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\x. lift(wan_dpart i (u:real^M->real) x)) absolutely_integrable_on k`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`s:real^M->bool`; `u:real^M->real`; `i:num`] WAN_LIP_WPD) THEN
    ASM_REWRITE_TAC[wan_wpd; wan_lloc] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[lspace; IN_ELIM_THM; RPOW_POW] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[ABSOLUTELY_INTEGRABLE_MEASURABLE]; ALL_TAC] THEN
  MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
  MATCH_MP_TAC MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_ABSOLUTELY_INTEGRABLE_AE THEN
  MAP_EVERY EXISTS_TAC
   [`\x:real^M. lift(L pow 2)`;
    `{x | x IN uu /\ ~((\y. lift((u:real^M->real) y)) differentiable at x)}`] THEN
  ASM_SIMP_TAC[INTEGRABLE_ON_CONST; MEASURABLE_COMPACT; LIFT_DROP] THEN CONJ_TAC THENL
   [MATCH_MP_TAC MEASURABLE_ON_LIFT_POW THEN ASM_SIMP_TAC[LEBESGUE_MEASURABLE_COMPACT] THEN
    MATCH_MP_TAC MEASURABLE_ON_NORM THEN ASM_MESON_TAC[ABSOLUTELY_INTEGRABLE_MEASURABLE];
    ALL_TAC] THEN
  X_GEN_TAC `x:real^M` THEN REWRITE_TAC[IN_DIFF; IN_ELIM_THM] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(x:real^M) IN uu` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(\y. lift((u:real^M->real) y)) differentiable at x` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[NORM_LIFT; REAL_ABS_POW; REAL_ABS_NORM] THEN
  MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[REAL_ABS_POS; wan_dpart] THEN
  MP_TAC(ISPECL [`u:real^M->real`; `L:real`; `x:real^M`; `d:real`; `basis i:real^M`]
                WAN_LIP_DERIV_BOUND) THEN
  ASM_SIMP_TAC[NORM_BASIS; REAL_MUL_RID] THEN DISCH_THEN MATCH_MP_TAC THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  SUBGOAL_THEN `ball(x:real^M,d) SUBSET kk` MP_TAC THENL
   [UNDISCH_TAC `(x:real^M) IN k` THEN EXPAND_TAC "kk" THEN
    REWRITE_TAC[SUBSET; IN_BALL; IN_ELIM_THM; IN_CBALL_0; dist] THEN
    DISCH_TAC THEN X_GEN_TAC `w:real^M` THEN DISCH_TAC THEN
    MAP_EVERY EXISTS_TAC [`x:real^M`; `w - x:real^M`] THEN
    ASM_REWRITE_TAC[VECTOR_ARITH `x + w - x:real^M = w`] THEN
    MP_TAC(ISPECL [`x:real^M`; `w:real^M`] NORM_SUB) THEN
    UNDISCH_TAC `norm(x - w:real^M) < d` THEN REAL_ARITH_TAC;
    ASM SET_TAC[]]);;

(* ========================================================================= *)
(* C^1 maps.  The classical partial derivatives of a C^1 map on              *)
(* an open set are weak partial derivatives; with L^2 bounds this gives the  *)
(* W^(1,2) membership and the Dirichlet integral (WAN_W12_C1_STATEMENT).     *)
(* ========================================================================= *)

let WAN_WPD_C1 = prove
 (`!(s:real^N->bool) (u:real^N->real^K) i.
     open s /\ continuously_differentiable 1 s u
     ==> wan_wpd s i u (\x. partial_derivative i u x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CONTINUOUSLY_DIFFERENTIABLE_1] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `D:real^N->real^N->real^K` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN
   `!x. x IN s ==> ((u:real^N->real^K) has_derivative (D:real^N->real^N->real^K) x) (at x)`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[HAS_DERIVATIVE_WITHIN_OPEN]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN s ==> partial_derivative i (u:real^N->real^K) x =
                   (D:real^N->real^N->real^K) x (basis i)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[partial_derivative] THEN
    ASM_MESON_TAC[FRECHET_DERIVATIVE_AT];
    ALL_TAC] THEN
  SUBGOAL_THEN `(u:real^N->real^K) continuous_on s` ASSUME_TAC THENL
   [MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_ON THEN
    REWRITE_TAC[differentiable_on; differentiable] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\x. partial_derivative i (u:real^N->real^K) x) continuous_on s`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_EQ THEN
    EXISTS_TAC `\x. (D:real^N->real^N->real^K) x (basis i)` THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[wan_wpd] THEN ASM_SIMP_TAC[WAN_CONTINUOUS_ON_LLOC] THEN
  X_GEN_TAC `phi:real^N->real` THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o REWRITE_RULE[wan_test]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `k:real^N->bool` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL
   [`\x. (phi:real^N->real) x % (u:real^N->real^K) x`;
    `\x h. (phi:real^N->real) x % (D:real^N->real^N->real^K) x h +
           drop(frechet_derivative (\y. lift(phi y)) (at x) h) % (u:real^N->real^K) x`;
    `s:real^N->bool`; `k:real^N->bool`; `i:num`] WAN_NT_INTEGRAL_PARTIAL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`phi:real^N->real`;
                     `\h. drop(frechet_derivative (\y. lift((phi:real^N->real) y)) (at x) h)`;
                     `u:real^N->real^K`; `(D:real^N->real^N->real^K) x`; `x:real^N`]
                    HAS_DERIVATIVE_MUL_AT) THEN
      ANTS_TAC THENL
       [REWRITE_TAC[o_DEF; LIFT_DROP; ETA_AX] THEN CONJ_TAC THENL
         [MATCH_MP_TAC(REWRITE_RULE[RIGHT_IMP_FORALL_THM; IMP_IMP]
                         SMOOTH_MAP_ON_HAS_DERIVATIVE) THEN
          EXISTS_TAC `(:real^N)` THEN ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV];
          ASM_SIMP_TAC[]];
        REWRITE_TAC[]];
      MATCH_MP_TAC CONTINUOUS_ON_ADD THEN CONJ_TAC THEN
      MATCH_MP_TAC CONTINUOUS_ON_MUL THEN ASM_REWRITE_TAC[o_DEF; LIFT_DROP] THEN
      MP_TAC(ISPECL [`s:real^N->bool`; `phi:real^N->real`; `i:num`]
                    WAN_TEST_CONTINUOUS) THEN
      ASM_REWRITE_TAC[wan_dpart; LIFT_DROP] THEN
      MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_UNIV];
      ASM_SIMP_TAC[VECTOR_MUL_LZERO]];
    DISCH_THEN(ASSUME_TAC o BETA_RULE)] THEN
  SUBGOAL_THEN
   `((\x. (phi:real^N->real) x % partial_derivative i (u:real^N->real^K) x +
          wan_dpart i phi x % u x) has_integral vec 0) s`
  MP_TAC THENL
   [MATCH_MP_TAC HAS_INTEGRAL_EQ THEN
    EXISTS_TAC
     `\x. (phi:real^N->real) x % (D:real^N->real^N->real^K) x (basis i) +
          drop(frechet_derivative (\y. lift(phi y)) (at x) (basis i)) %
          (u:real^N->real^K) x` THEN
    ASM_SIMP_TAC[wan_dpart];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\x. (phi:real^N->real) x % partial_derivative i (u:real^N->real^K) x)
      integrable_on s /\
    (\x. wan_dpart i phi x % (u:real^N->real^K) x) integrable_on s`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THENL
     [MP_TAC(ISPECL [`s:real^N->bool`; `phi:real^N->real`;
                     `\x. partial_derivative i (u:real^N->real^K) x`] WAN_TEST_PAIRING) THEN
      ANTS_TAC THENL [ASM_SIMP_TAC[WAN_CONTINUOUS_ON_LLOC]; ALL_TAC] THEN
      DISCH_THEN(ACCEPT_TAC o CONJUNCT1 o BETA_RULE);
      MP_TAC(ISPECL [`s:real^N->bool`; `phi:real^N->real`; `u:real^N->real^K`]
                    WAN_TEST_PAIRING) THEN
      ANTS_TAC THENL [ASM_SIMP_TAC[WAN_CONTINUOUS_ON_LLOC]; ALL_TAC] THEN
      DISCH_THEN(ACCEPT_TAC o SPEC `i:num` o CONJUNCT2)];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP INTEGRAL_UNIQUE) THEN
  ASM_SIMP_TAC[INTEGRAL_ADD] THEN VECTOR_ARITH_TAC);;

let WAN_W12_C1 = prove
 (`!(n:N->bool) (kk:K->bool). WAN_W12_C1_STATEMENT n kk`,
  REWRITE_TAC[WAN_W12_C1_STATEMENT] THEN
  MAP_EVERY X_GEN_TAC [`s:real^N->bool`; `u:real^N->real^K`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `!i. wan_wpd s i (u:real^N->real^K) (\x. partial_derivative i u x)`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[WAN_WPD_C1]; ALL_TAC] THEN
  SUBGOAL_THEN `wan_w12 s (u:real^N->real^K)` ASSUME_TAC THENL
   [REWRITE_TAC[wan_w12] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `u:real^N->real^K`;
                 `\i x. partial_derivative i (u:real^N->real^K) x`] WAN_DIR_EQ) THEN
  ASM_SIMP_TAC[]);;

(* ========================================================================= *)
(* Smooth multipliers.  Products with a function smooth on the               *)
(* open set, bounded with bounded first partials (WAN_MUL_W12_STATEMENT).    *)
(* ========================================================================= *)

let WAN_LLOC_CONT_MUL = prove
 (`!(s:real^N->bool) (g:real^N->real) (u:real^N->real^K).
     (\x. lift(g x)) continuous_on s /\ wan_lloc s u
     ==> wan_lloc s (\x. g x % u x)`,
  REWRITE_TAC[wan_lloc] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\c:real^1 v:real^K. drop c % v`; `\x. lift((g:real^N->real) x)`;
                 `u:real^N->real^K`; `k:real^N->bool`]
                ABSOLUTELY_INTEGRABLE_BOUNDED_MEASURABLE_PRODUCT) THEN
  REWRITE_TAC[BILINEAR_DROP_MUL; LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_SIMP_TAC[] THEN
  SUBGOAL_THEN `(\x. lift((g:real^N->real) x)) continuous_on k` ASSUME_TAC THENL
   [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET]; ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
    ASM_SIMP_TAC[LEBESGUE_MEASURABLE_COMPACT];
    MATCH_MP_TAC COMPACT_IMP_BOUNDED THEN
    MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[]]);;

let WAN_LSPACE2_BOUNDED_MUL = prove
 (`!(s:real^N->bool) (g:real^N->real) (u:real^N->real^K) B.
     lebesgue_measurable s /\ (\x. lift(g x)) continuous_on s /\
     (!x. x IN s ==> abs(g x) <= B) /\ u IN lspace s (&2)
     ==> (\x. g x % u x) IN lspace s (&2)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(ISPECL [`s:real^N->bool`; `&2`;
                       `\x. (g:real^N->real) x % (u:real^N->real^K) x`;
                       `\x. abs B % (u:real^N->real^K) x`] LSPACE_BOUNDED_MEASURABLE) THEN
  ASM_SIMP_TAC[LSPACE_CMUL; REAL_OF_NUM_LT; ARITH] THEN CONJ_TAC THENL
   [MATCH_MP_TAC MEASURABLE_ON_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
      ASM_REWRITE_TAC[];
      UNDISCH_TAC `(u:real^N->real^K) IN lspace s (&2)` THEN
      SIMP_TAC[lspace; IN_ELIM_THM]];
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    REWRITE_TAC[NORM_MUL; REAL_ABS_ABS] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
    MATCH_MP_TAC(REAL_ARITH `a <= b ==> a <= abs b`) THEN ASM_SIMP_TAC[]]);;

let WAN_TEST_MUL_SMOOTH = prove
 (`!(s:real^N->bool) phi g.
     open s /\ wan_test s phi /\ smooth_map_on s (\x. lift(g x))
     ==> wan_test s (\x. if x IN s then phi x * g x else &0) /\
         !i x. x IN s
               ==> wan_dpart i (\x. if x IN s then phi x * g x else &0) x =
                   wan_dpart i phi x * g x + phi x * wan_dpart i g x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wan_test] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!x. x IN s
        ==> ((\y. lift((phi:real^N->real) y * g y)) has_derivative
             (\h. phi x % frechet_derivative (\y. lift(g y)) (at x) h +
                  drop(frechet_derivative (\y. lift(phi y)) (at x) h) % lift(g x)))
            (at x)`
  (LABEL_TAC "dmul") THENL
   [X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`phi:real^N->real`;
                   `\h. drop(frechet_derivative (\y. lift((phi:real^N->real) y)) (at x) h)`;
                   `\y. lift((g:real^N->real) y)`;
                   `frechet_derivative (\y. lift((g:real^N->real) y)) (at x)`;
                   `x:real^N`] HAS_DERIVATIVE_MUL_AT) THEN
    REWRITE_TAC[o_DEF; LIFT_DROP; ETA_AX; LIFT_CMUL] THEN
    DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THEN
    MATCH_MP_TAC(REWRITE_RULE[RIGHT_IMP_FORALL_THM; IMP_IMP]
                   SMOOTH_MAP_ON_HAS_DERIVATIVE) THENL
     [EXISTS_TAC `(:real^N)`; EXISTS_TAC `s:real^N->bool`] THEN
    ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on (:real^N)
      (\x. lift(if x IN s then (phi:real^N->real) x * g x else &0))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN
    X_GEN_TAC `x:real^N` THEN ASM_CASES_TAC `(x:real^N) IN s` THENL
     [EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
      EXISTS_TAC `\y. lift(drop(lift((phi:real^N->real) y)) * drop(lift(g y)))` THEN
      CONJ_TAC THENL
       [SIMP_TAC[LIFT_DROP];
        MATCH_MP_TAC SMOOTH_MAP_ON_LIFT_MUL THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^N)` THEN
        ASM_REWRITE_TAC[SUBSET_UNIV]];
      EXISTS_TAC `(:real^N) DIFF k` THEN REPEAT CONJ_TAC THENL
       [ASM_SIMP_TAC[GSYM closed; COMPACT_IMP_CLOSED];
        ASM SET_TAC[];
        MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN EXISTS_TAC `\y:real^N. vec 0:real^1` THEN
        REWRITE_TAC[SMOOTH_MAP_ON_CONST; IN_DIFF; IN_UNIV] THEN
        X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
        COND_CASES_TAC THEN ASM_SIMP_TAC[REAL_MUL_LZERO; LIFT_NUM]]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [ASM_REWRITE_TAC[] THEN EXISTS_TAC `k:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN COND_CASES_TAC THEN
    ASM_SIMP_TAC[REAL_MUL_LZERO];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`i:num`; `x:real^N`] THEN DISCH_TAC THEN
  REWRITE_TAC[wan_dpart] THEN
  SUBGOAL_THEN
   `frechet_derivative (\y. lift(if y IN s then (phi:real^N->real) y * g y else &0))
                       (at x) =
    frechet_derivative (\y. lift(phi y * g y)) (at x)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC LRG_FRECHET_DERIVATIVE_EQ_OPEN THEN EXISTS_TAC `s:real^N->bool` THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  USE_THEN "dmul" (fun th -> MP_TAC(MP (SPEC `x:real^N` th)
                                    (ASSUME `(x:real^N) IN s`))) THEN
  DISCH_THEN(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
  REWRITE_TAC[DROP_ADD; DROP_CMUL; LIFT_DROP] THEN REAL_ARITH_TAC);;

let WAN_WPD_MUL_SMOOTH = prove
 (`!(s:real^N->bool) i (u:real^N->real^K) v g.
     open s /\ wan_wpd s i u v /\ smooth_map_on s (\x. lift(g x))
     ==> wan_wpd s i (\x. g x % u x) (\x. wan_dpart i g x % u x + g x % v x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(\x. lift((g:real^N->real) x)) continuous_on s /\
                (\x. lift(wan_dpart i g x)) continuous_on s`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
    ASM_REWRITE_TAC[wan_dpart; LIFT_DROP] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_FRECHET_DERIVATIVE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `wan_wpd s i (u:real^N->real^K) v` THEN REWRITE_TAC[wan_wpd] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ibp"))) THEN
  SUBGOAL_THEN
   `wan_lloc s (\x. (g:real^N->real) x % (u:real^N->real^K) x) /\
    wan_lloc s (\x. wan_dpart i g x % (u:real^N->real^K) x) /\
    wan_lloc s (\x. (g:real^N->real) x % (v:real^N->real^K) x)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC WAN_LLOC_CONT_MUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`s:real^N->bool`; `\x. wan_dpart i g x % (u:real^N->real^K) x`;
                   `\x. (g:real^N->real) x % (v:real^N->real^K) x`] WAN_LLOC_ADD) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `phi:real^N->real` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `phi:real^N->real`; `g:real^N->real`]
                WAN_TEST_MUL_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `psi = \x. if x IN s then (phi:real^N->real) x * g x else &0` THEN
  STRIP_TAC THEN
  USE_THEN "ibp" (fun th -> MP_TAC(MP (SPEC `psi:real^N->real` th)
                                    (ASSUME `wan_test s (psi:real^N->real)`))) THEN
  SUBGOAL_THEN
   `(\x. wan_dpart i phi x % ((g:real^N->real) x % (u:real^N->real^K) x))
      integrable_on s /\
    (\x. (phi:real^N->real) x % (wan_dpart i g x % (u:real^N->real^K) x))
      integrable_on s /\
    (\x. (phi:real^N->real) x % ((g:real^N->real) x % (v:real^N->real^K) x))
      integrable_on s`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THENL
     [MP_TAC(ISPECL [`s:real^N->bool`; `phi:real^N->real`;
                     `\x. (g:real^N->real) x % (u:real^N->real^K) x`] WAN_TEST_PAIRING) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `i:num` o CONJUNCT2) THEN
      REWRITE_TAC[];
      MP_TAC(ISPECL [`s:real^N->bool`; `phi:real^N->real`;
                     `\x. wan_dpart i g x % (u:real^N->real^K) x`] WAN_TEST_PAIRING) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN REWRITE_TAC[];
      MP_TAC(ISPECL [`s:real^N->bool`; `phi:real^N->real`;
                     `\x. (g:real^N->real) x % (v:real^N->real^K) x`] WAN_TEST_PAIRING) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `integral s (\x. wan_dpart i psi x % (u:real^N->real^K) x) =
    integral s (\x. wan_dpart i phi x % ((g:real^N->real) x % u x)) +
    integral s (\x. phi x % (wan_dpart i g x % u x))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC
     `integral s (\x. wan_dpart i phi x % ((g:real^N->real) x % (u:real^N->real^K) x) +
                      phi x % (wan_dpart i g x % u x))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC INTEGRAL_EQ THEN
      X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN ASM_SIMP_TAC[] THEN VECTOR_ARITH_TAC;
      MATCH_MP_TAC INTEGRAL_ADD THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `integral s (\x. psi x % (v:real^N->real^K) x) =
    integral s (\x. phi x % ((g:real^N->real) x % v x))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC INTEGRAL_EQ THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    EXPAND_TAC "psi" THEN ASM_REWRITE_TAC[VECTOR_MUL_ASSOC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `integral s (\x. (phi:real^N->real) x %
                    (wan_dpart i g x % (u:real^N->real^K) x + g x % v x)) =
    integral s (\x. phi x % (wan_dpart i g x % u x)) +
    integral s (\x. phi x % (g x % v x))`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[GSYM INTEGRAL_ADD; VECTOR_ADD_LDISTRIB];
    ALL_TAC] THEN
  VECTOR_ARITH_TAC);;

let WAN_MUL_W12 = prove
 (`!(n:N->bool) (kk:K->bool). WAN_MUL_W12_STATEMENT n kk`,
  REWRITE_TAC[WAN_MUL_W12_STATEMENT] THEN
  MAP_EVERY X_GEN_TAC [`s:real^N->bool`; `u:real^N->real^K`; `g:real^N->real`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
      (X_CHOOSE_TAC `B:real`) (X_CHOOSE_TAC `B1:real`))))) THEN
  SUBGOAL_THEN `(\x. lift((g:real^N->real) x)) continuous_on s /\
                !i. (\x. lift(wan_dpart i g x)) continuous_on s`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ALL_TAC; GEN_TAC] THEN MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
    ASM_REWRITE_TAC[wan_dpart; LIFT_DROP] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_FRECHET_DERIVATIVE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= dimindex(:N)
        ==> wan_wpd s i (\x. (g:real^N->real) x % (u:real^N->real^K) x)
              (\x. wan_dpart i g x % u x + g x % wan_wd s i u x)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC WAN_WPD_MUL_SMOOTH THEN
    REWRITE_TAC[ETA_AX] THEN ASM_SIMP_TAC[WAN_WD_WORKS];
    ALL_TAC] THEN
  SUBGOAL_THEN `(u:real^N->real^K) IN lspace s (&2)` ASSUME_TAC THENL
   [MP_TAC(ASSUME `wan_w12 s (u:real^N->real^K)`) THEN REWRITE_TAC[wan_w12] THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[wan_w12] THEN CONJ_TAC THENL
   [MATCH_MP_TAC WAN_LSPACE2_BOUNDED_MUL THEN EXISTS_TAC `B:real` THEN
    ASM_SIMP_TAC[LEBESGUE_MEASURABLE_OPEN];
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    EXISTS_TAC `\x. wan_dpart i g x % (u:real^N->real^K) x + g x % wan_wd s i u x` THEN
    ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC LSPACE_ADD THEN REWRITE_TAC[REAL_POS] THEN CONJ_TAC THEN
    MATCH_MP_TAC WAN_LSPACE2_BOUNDED_MUL THENL
     [EXISTS_TAC `B1:real`; EXISTS_TAC `B:real`] THEN
    REWRITE_TAC[ETA_AX] THEN ASM_SIMP_TAC[LEBESGUE_MEASURABLE_OPEN; WAN_WD_WORKS]]);;

