(* ========================================================================= *)
(* pc_smt_pole: S7, pole normalization of diffeomorphisms of S^2            *)
(* (SMT_SPHERE_POLE_STATEMENT).                                              *)
(*                                                                           *)
(* The planar cut-off.  A smooth k with k 0 = 0 and Dk(0) = I                *)
(* agrees near 0 with the time-1 map of a compactly supported isotopy        *)
(*   G t y = y + smooth_step t % beta(y/s) % (k y - y),                      *)
(* a diffeo_isotopy by S4a (SMT_PERTURB_ID): k - id is Lipschitz with a      *)
(* small constant near 0 (DIFFERENTIABLE_BOUND) and the bump beta is         *)
(* Lipschitz (compactly supported smooth maps are Lipschitz).                *)
(* ========================================================================= *)

needs "src/pc_smt_rn.ml";;
needs "src/pc_smt_germ.ml";;

prioritize_real();;
type_invention_error := true;;

(* A C^1 map with zero derivative at a is Lipschitz near a, with any given   *)
(* positive constant.                                                        *)

let SMT_C1_SMALL_LIPSCHITZ = prove
 (`!(v:real^M->real^N) W a e.
        open W /\ a IN W /\ smooth_map_on W v /\
        (v has_derivative (\y. vec 0)) (at a) /\ &0 < e
        ==> ?d. &0 < d /\ cball(a,d) SUBSET W /\
                !x y. x IN cball(a,d) /\ y IN cball(a,d)
                      ==> norm(v x - v y) <= e * norm(x - y)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`W:real^M->bool`; `v:real^M->real^N`]
    SMOOTH_MAP_ON_HAS_DERIVATIVE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `frechet_derivative (v:real^M->real^N) (at a) = (\y. vec 0)`
  ASSUME_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC
   `phi = \x. sum(1..dimindex(:M))
                 (\i. norm(frechet_derivative (v:real^M->real^N) (at x) (basis i)))` THEN
  SUBGOAL_THEN `(\x. lift((phi:real^M->real) x)) continuous_on W` ASSUME_TAC THENL
   [EXPAND_TAC "phi" THEN REWRITE_TAC[LIFT_SUM; o_DEF] THEN
    MATCH_MP_TAC CONTINUOUS_ON_VSUM THEN
    REWRITE_TAC[FINITE_NUMSEG] THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_ON_LIFT_NORM_COMPOSE THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_FRECHET_DERIVATIVE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(phi:real^M->real) a = &0` ASSUME_TAC THENL
   [EXPAND_TAC "phi" THEN ASM_REWRITE_TAC[NORM_0; SUM_0]; ALL_TAC] THEN
  SUBGOAL_THEN `(\x. lift((phi:real^M->real) x)) continuous at a` MP_TAC THENL
   [ASM_MESON_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_AT]; ALL_TAC] THEN
  REWRITE_TAC[continuous_at; DIST_LIFT] THEN
  DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[REAL_SUB_RZERO] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(MP_TAC o SPEC `a:real^M` o GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `min d1 r / &2` THEN
  SUBGOAL_THEN
   `!x:real^M. x IN cball(a,min d1 r / &2) ==> x IN W /\ dist(x,a) < d1`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^M` THEN REWRITE_TAC[IN_CBALL] THEN DISCH_TAC THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `ball(a:real^M,r) SUBSET W` THEN
      REWRITE_TAC[SUBSET; IN_BALL] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REAL_ARITH_TAC;
      ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`v:real^M->real^N`;
                 `\x. frechet_derivative (v:real^M->real^N) (at x)`;
                 `cball(a:real^M,min d1 r / &2)`; `e:real`]
    DIFFERENTIABLE_BOUND) THEN
  REWRITE_TAC[CONVEX_CBALL] THEN DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[AND_FORALL_THM] THEN X_GEN_TAC `x:real^M` THEN
  REWRITE_TAC[TAUT `(p ==> q) /\ (p ==> r) <=> p ==> q /\ r`] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `(x:real^M) IN W /\ dist(x,a) < d1` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC HAS_DERIVATIVE_AT_WITHIN THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `linear(frechet_derivative (v:real^M->real^N) (at x))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `W:real^M->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(phi:real^M->real) x` THEN
  CONJ_TAC THENL
   [MP_TAC(ISPEC `frechet_derivative (v:real^M->real^N) (at x)` ONORM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN
    X_GEN_TAC `h:real^M` THEN
    MP_TAC(ISPEC `frechet_derivative (v:real^M->real^N) (at x)`
      ODE_LINEAR_BOUND_BASIS) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `h:real^M`) THEN
    EXPAND_TAC "phi" THEN REWRITE_TAC[];
    MATCH_MP_TAC(REAL_ARITH `abs p < e ==> p <= e`) THEN ASM_SIMP_TAC[]]);;

(* A smooth map vanishing outside a compact set is globally Lipschitz.      *)

let SMT_SMOOTH_COMPACT_LIPSCHITZ = prove
 (`!(f:real^M->real^N) K.
        smooth_map_on (:real^M) f /\ compact K /\
        (!x. ~(x IN K) ==> f x = vec 0)
        ==> ?L. &0 < L /\ !x y. norm(f x - f y) <= L * norm(x - y)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`(:real^M)`; `f:real^M->real^N`] SMOOTH_MAP_ON_HAS_DERIVATIVE) THEN
  ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN DISCH_TAC THEN
  ABBREV_TAC
   `phi = \x. sum(1..dimindex(:M))
                 (\i. norm(frechet_derivative (f:real^M->real^N) (at x) (basis i)))` THEN
  MP_TAC(ISPECL [`\x. lift((phi:real^M->real) x)`; `(:real^M)`; `K:real^M->bool`]
    ODE_COMPACT_BOUND) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[SUBSET_UNIV] THEN EXPAND_TAC "phi" THEN
    REWRITE_TAC[LIFT_SUM; o_DEF] THEN MATCH_MP_TAC CONTINUOUS_ON_VSUM THEN
    REWRITE_TAC[FINITE_NUMSEG] THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_ON_LIFT_NORM_COMPOSE THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_FRECHET_DERIVATIVE THEN
    ASM_REWRITE_TAC[OPEN_UNIV];
    ALL_TAC] THEN
  REWRITE_TAC[NORM_LIFT] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!x:real^M. ~(x IN K)
               ==> frechet_derivative (f:real^M->real^N) (at x) = (\h. vec 0)`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
    SUBGOAL_THEN `open((:real^M) DIFF K)` MP_TAC THENL
     [REWRITE_TAC[GSYM closed] THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED];
      ALL_TAC] THEN
    REWRITE_TAC[OPEN_CONTAINS_BALL] THEN
    DISCH_THEN(MP_TAC o SPEC `x:real^M`) THEN
    ASM_REWRITE_TAC[IN_DIFF; IN_UNIV] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_AT THEN
    MAP_EVERY EXISTS_TAC [`\x:real^M. vec 0:real^N`; `d:real`] THEN
    ASM_REWRITE_TAC[HAS_DERIVATIVE_CONST] THEN
    X_GEN_TAC `y:real^M` THEN DISCH_TAC THEN CONV_TAC SYM_CONV THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `ball(x:real^M,d) SUBSET (:real^M) DIFF K` THEN
    REWRITE_TAC[SUBSET; IN_BALL; IN_DIFF; IN_UNIV] THEN
    DISCH_THEN MATCH_MP_TAC THEN ONCE_REWRITE_TAC[DIST_SYM] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `B:real` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`f:real^M->real^N`;
                 `\x. frechet_derivative (f:real^M->real^N) (at x)`;
                 `(:real^M)`; `B:real`] DIFFERENTIABLE_BOUND) THEN
  REWRITE_TAC[CONVEX_UNIV; IN_UNIV; WITHIN_UNIV] THEN
  ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:real^M` THEN
  ASM_CASES_TAC `(x:real^M) IN K` THENL
   [SUBGOAL_THEN `linear(frechet_derivative (f:real^M->real^N) (at x))`
    ASSUME_TAC THENL
     [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
      EXISTS_TAC `(:real^M)` THEN ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(phi:real^M->real) x` THEN
    CONJ_TAC THENL
     [MP_TAC(ISPEC `frechet_derivative (f:real^M->real^N) (at x)` ONORM) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN
      X_GEN_TAC `h:real^M` THEN
      MP_TAC(ISPEC `frechet_derivative (f:real^M->real^N) (at x)`
        ODE_LINEAR_BOUND_BASIS) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `h:real^M`) THEN
      EXPAND_TAC "phi" THEN REWRITE_TAC[];
      MATCH_MP_TAC(REAL_ARITH `abs p <= b ==> p <= b`) THEN ASM_SIMP_TAC[]];
    ASM_SIMP_TAC[ONORM_CONST; NORM_0] THEN ASM_REAL_ARITH_TAC]);;

let SMT_BUMP_LIPSCHITZ = prove
 (`?L. &0 < L /\
       !x y:real^N. abs(smooth_bump (&1 / &2) (&1) x - smooth_bump (&1 / &2) (&1) y)
                    <= L * norm(x - y)`,
  MP_TAC(ISPECL [`\x:real^N. lift(smooth_bump (&1 / &2) (&1) x)`;
                 `cball(vec 0:real^N,&1)`] SMT_SMOOTH_COMPACT_LIPSCHITZ) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[COMPACT_CBALL; IN_CBALL_0; REAL_NOT_LE] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_BUMP_SMOOTH THEN REAL_ARITH_TAC;
      REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM LIFT_NUM; LIFT_EQ] THEN
      MATCH_MP_TAC SMOOTH_BUMP_0 THEN ASM_REAL_ARITH_TAC];
    REWRITE_TAC[GSYM LIFT_SUB; NORM_LIFT]]);;

(* The cut-off of a map that is c-Lipschitz on cball(0,s) and vanishes at 0  *)
(* by a bump that is (L/s)-Lipschitz and vanishes off ball(0,s).            *)

let SMT_CUTOFF_LIPSCHITZ = prove
 (`!(v:real^N->real^N) beta s c L.
        &0 < s /\ &0 <= c /\ &0 <= L /\ v(vec 0) = vec 0 /\
        (!x y. abs(beta x - beta y) <= L / s * norm(x - y)) /\
        (!x. &0 <= beta x /\ beta x <= &1) /\
        (!x. s <= norm x ==> beta x = &0) /\
        (!x y. x IN cball(vec 0,s) /\ y IN cball(vec 0,s)
               ==> norm(v x - v y) <= c * norm(x - y))
        ==> !x y. norm(beta x % v x - beta y % v y)
                  <= (L + &1) * c * norm(x - y)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (LABEL_TAC "blip") (CONJUNCTS_THEN2 (LABEL_TAC "b01")
   (CONJUNCTS_THEN2 (LABEL_TAC "b0") (LABEL_TAC "vlip")))))))) THEN
  SUBGOAL_THEN `&0 <= s` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!x:real^N. x IN cball(vec 0,s) ==> norm((v:real^N->real^N) x) <= c * s`
  (LABEL_TAC "vsmall") THENL
   [X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    USE_THEN "vlip" (MP_TAC o SPECL [`x:real^N`; `vec 0:real^N`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[CENTRE_IN_CBALL]; ALL_TAC] THEN
    ASM_REWRITE_TAC[VECTOR_SUB_RZERO] THEN
    MATCH_MP_TAC(REAL_ARITH `b <= c ==> a <= b ==> a <= c`) THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(x:real^N) IN cball(vec 0,s)` THEN REWRITE_TAC[IN_CBALL_0];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x y:real^N. x IN cball(vec 0,s)
                 ==> abs((beta:real^N->real) x - beta y) *
                     norm((v:real^N->real^N) x)
                     <= L * c * norm(x - y)`
  (LABEL_TAC "key") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(L / s * norm(x - y:real^N)) * (c * s)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_SIMP_TAC[REAL_ABS_POS; NORM_POS_LE];
      MATCH_MP_TAC(REAL_ARITH `a = b ==> a <= b`) THEN
      UNDISCH_TAC `&0 < s` THEN CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`] THEN
  SUBGOAL_THEN `&0 <= c * norm(x - y:real^N)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_MUL; NORM_POS_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `(L + &1) * c * norm(x - y:real^N) =
                L * c * norm(x - y) + c * norm(x - y)` SUBST1_TAC THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `(x:real^N) IN cball(vec 0,s)` THEN
  ASM_CASES_TAC `(y:real^N) IN cball(vec 0,s)` THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `abs((beta:real^N->real) x - beta y) * norm((v:real^N->real^N) x) +
                abs(beta y) * norm(v x - v y)` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[GSYM NORM_MUL] THEN
      MATCH_MP_TAC(NORM_ARITH
       `!u p q:real^N. u = p + q ==> norm u <= norm p + norm q`) THEN
      VECTOR_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
       [USE_THEN "key" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC(REAL_ARITH `&0 <= a /\ a * n <= &1 * m ==> a * n <= m`) THEN
        REWRITE_TAC[REAL_ABS_POS] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
        REWRITE_TAC[REAL_ABS_POS; NORM_POS_LE] THEN CONJ_TAC THENL
         [USE_THEN "b01" (MP_TAC o SPEC `y:real^N`) THEN REAL_ARITH_TAC;
          USE_THEN "vlip" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]]];
    SUBGOAL_THEN `(beta:real^N->real) y = &0` ASSUME_TAC THENL
     [USE_THEN "b0" MATCH_MP_TAC THEN
      UNDISCH_TAC `~((y:real^N) IN cball(vec 0,s))` THEN
      REWRITE_TAC[IN_CBALL_0] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `a <= b /\ &0 <= c ==> a <= b + c`) THEN
    ASM_REWRITE_TAC[] THEN
    USE_THEN "key" (MP_TAC o SPECL [`x:real^N`; `y:real^N`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `a <= b ==> b <= c ==> a <= c`) THEN
    REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_SUB_RZERO; NORM_MUL; REAL_SUB_RZERO;
                REAL_LE_REFL];
    SUBGOAL_THEN `(beta:real^N->real) x = &0` ASSUME_TAC THENL
     [USE_THEN "b0" MATCH_MP_TAC THEN
      UNDISCH_TAC `~((x:real^N) IN cball(vec 0,s))` THEN
      REWRITE_TAC[IN_CBALL_0] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `a <= b /\ &0 <= c ==> a <= b + c`) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `norm(x - y:real^N) = norm(y - x)` SUBST1_TAC THENL
     [REWRITE_TAC[NORM_SUB]; ALL_TAC] THEN
    USE_THEN "key" (MP_TAC o SPECL [`y:real^N`; `x:real^N`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `a <= b ==> b <= c ==> a <= c`) THEN
    REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_SUB_LZERO; NORM_NEG; NORM_MUL;
                REAL_SUB_RZERO; REAL_LE_REFL];
    SUBGOAL_THEN `(beta:real^N->real) x = &0 /\ beta y = &0`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN USE_THEN "b0" MATCH_MP_TAC THENL
       [UNDISCH_TAC `~((x:real^N) IN cball(vec 0,s))`;
        UNDISCH_TAC `~((y:real^N) IN cball(vec 0,s))`] THEN
      REWRITE_TAC[IN_CBALL_0] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_SUB_REFL; NORM_0] THEN
    MATCH_MP_TAC REAL_LE_ADD THEN ASM_SIMP_TAC[REAL_LE_MUL; NORM_POS_LE]]);;

(* ------------------------------------------------------------------------- *)
(* The cut-off isotopy (SMT_GERM_CUTOFF).                                    *)
(* ------------------------------------------------------------------------- *)

let SMT_NORM_INV_SCALE = prove
 (`!s (x:real^N). &0 < s ==> norm(inv s % x) = norm x / s`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[NORM_MUL; REAL_ABS_INV; REAL_ARITH `&0 < s ==> abs s = s`] THEN
  REWRITE_TAC[real_div] THEN REAL_ARITH_TAC);;

let SMT_GERM_CUTOFF = prove
 (`!(k:real^N->real^N) W.
        open W /\ vec 0 IN W /\ smooth_map_on W k /\ k(vec 0) = vec 0 /\
        (k has_derivative (\y. y)) (at (vec 0))
        ==> ?G G' s. &0 < s /\ cball(vec 0,s) SUBSET W /\ diffeo_isotopy G G' /\
                     (!t y. t <= &0 ==> G t y = y) /\
                     (!t y. &1 <= t ==> G t y = G (&1) y) /\
                     (!t y. s <= norm y ==> G t y = y) /\
                     (!y. norm y <= s / &2 ==> G (&1) y = k y)`,
  REPEAT STRIP_TAC THEN
  X_CHOOSE_THEN `L:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "blip"))
    (INST_TYPE [`:N`,`:N`] SMT_BUMP_LIPSCHITZ) THEN
  ABBREV_TAC `v = \y:real^N. (k:real^N->real^N) y - y` THEN
  SUBGOAL_THEN `!y:real^N. (v:real^N->real^N) y = k y - y` (LABEL_TAC "vdef")
  THENL [EXPAND_TAC "v" THEN REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on W (v:real^N->real^N)` ASSUME_TAC THENL
   [EXPAND_TAC "v" THEN MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN
    ASM_REWRITE_TAC[SMOOTH_MAP_ON_ID];
    ALL_TAC] THEN
  SUBGOAL_THEN `((v:real^N->real^N) has_derivative (\y. vec 0)) (at (vec 0))`
  ASSUME_TAC THENL
   [EXPAND_TAC "v" THEN
    MP_TAC(ISPECL [`k:real^N->real^N`; `\y:real^N. y`; `\y:real^N. y`;
                   `\y:real^N. y`; `at(vec 0:real^N)`] HAS_DERIVATIVE_SUB) THEN
    ASM_REWRITE_TAC[HAS_DERIVATIVE_ID; VECTOR_SUB_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `(v:real^N->real^N)(vec 0) = vec 0` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[VECTOR_SUB_REFL]; ALL_TAC] THEN
  MP_TAC(ISPECL [`v:real^N->real^N`; `W:real^N->bool`; `vec 0:real^N`;
                 `inv(&2 * (L + &1))`] SMT_C1_SMALL_LIPSCHITZ) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_LT_INV_EQ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "vlip")))) THEN
  (* properties of the scaled bump *)
  SUBGOAL_THEN
   `!x y:real^N. abs(smooth_bump (&1 / &2) (&1) (inv s % x) -
                     smooth_bump (&1 / &2) (&1) (inv s % y)) <= L / s * norm(x - y)`
  (LABEL_TAC "B1") THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `L * norm(inv s % x - inv s % y:real^N)` THEN CONJ_TAC THENL
     [USE_THEN "blip" (fun th -> REWRITE_TAC[th]);
      REWRITE_TAC[GSYM VECTOR_SUB_LDISTRIB] THEN
      ASM_SIMP_TAC[SMT_NORM_INV_SCALE] THEN
      MATCH_MP_TAC(REAL_ARITH `a = b ==> a <= b`) THEN
      REWRITE_TAC[real_div] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x:real^N. s <= norm x ==> smooth_bump (&1 / &2) (&1) (inv s % x) = &0`
  (LABEL_TAC "B3") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_BUMP_0 THEN
    ASM_SIMP_TAC[SMT_NORM_INV_SCALE; REAL_LE_RDIV_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x:real^N. norm x <= s / &2 ==> smooth_bump (&1 / &2) (&1) (inv s % x) = &1`
  (LABEL_TAC "B4") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_BUMP_1 THEN
    ASM_SIMP_TAC[SMT_NORM_INV_SCALE; REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the cut-off map is smooth and 1/2-Lipschitz *)
  SUBGOAL_THEN
   `smooth_map_on (:real^N) (\y. lift(smooth_bump (&1 / &2) (&1) (inv s % y)))`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `(\y:real^N. lift(smooth_bump (&1 / &2) (&1) (inv s % y))) =
      (\x. lift(smooth_bump (&1 / &2) (&1) x)) o (\y. inv s % y)`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `(:real^N)` THEN
    REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV] THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`(:real^N)`; `\x:real^N. x`; `\y:real^N. inv s % y`]
        SMOOTH_MAP_ON_LINEAR_O) THEN
      REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_ID; LINEAR_SCALING; o_DEF];
      MATCH_MP_TAC SMOOTH_BUMP_SMOOTH THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on (:real^N)
      (\y. smooth_bump (&1 / &2) (&1) (inv s % y) % (v:real^N->real^N) y)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN
    X_GEN_TAC `x:real^N` THEN ASM_CASES_TAC `(x:real^N) IN W` THENL
     [EXISTS_TAC `W:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`W:real^N->bool`;
                     `\y:real^N. lift(smooth_bump (&1 / &2) (&1) (inv s % y))`;
                     `v:real^N->real^N`] SMOOTH_MAP_ON_MUL_DROP_OPEN) THEN
      ASM_REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^N)` THEN
      ASM_REWRITE_TAC[SUBSET_UNIV];
      EXISTS_TAC `{y:real^N | s < norm y}` THEN REPEAT CONJ_TAC THENL
       [SUBGOAL_THEN `{y:real^N | s < norm y} = (:real^N) DIFF cball(vec 0,s)`
        SUBST1_TAC THENL
         [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_DIFF; IN_UNIV; IN_CBALL_0] THEN
          REAL_ARITH_TAC;
          REWRITE_TAC[GSYM closed; CLOSED_CBALL]];
        REWRITE_TAC[IN_ELIM_THM; GSYM REAL_NOT_LE; GSYM IN_CBALL_0] THEN
        ASM SET_TAC[];
        MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
        EXISTS_TAC `\y:real^N. vec 0:real^N` THEN
        REWRITE_TAC[SMOOTH_MAP_ON_CONST; IN_ELIM_THM] THEN
        X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
        SUBGOAL_THEN `smooth_bump (&1 / &2) (&1) (inv s % y:real^N) = &0`
        SUBST1_TAC THENL
         [USE_THEN "B3" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
          REWRITE_TAC[VECTOR_MUL_LZERO]]]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`v:real^N->real^N`;
                 `\y:real^N. smooth_bump (&1 / &2) (&1) (inv s % y)`;
                 `s:real`; `inv(&2 * (L + &1))`; `L:real`] SMT_CUTOFF_LIPSCHITZ) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[SMOOTH_BUMP_BOUNDS; REAL_LE_INV_EQ] THEN
    ASM_REAL_ARITH_TAC;
    DISCH_THEN(LABEL_TAC "wlip")] THEN
  (* S4a *)
  MP_TAC(ISPEC `(:N)` SMT_PERTURB_ID) THEN REWRITE_TAC[SMT_PERTURB_ID_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPECL
   [`\t:real. \y:real^N. smooth_step t %
        smooth_bump (&1 / &2) (&1) (inv s % y) % (v:real^N->real^N) y`;
    `&1 / &2`]) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REWRITE_TAC[smooth_family; UNIV_PCROSS_UNIV] THEN
      MP_TAC(ISPECL
       [`(:real^(1,N)finite_sum)`;
        `\z:real^(1,N)finite_sum. lift(smooth_step(drop(fstcart z)))`;
        `\z:real^(1,N)finite_sum. smooth_bump (&1 / &2) (&1) (inv s % sndcart z) %
                                  (v:real^N->real^N) (sndcart z)`]
        SMOOTH_MAP_ON_MUL_DROP_OPEN) THEN
      REWRITE_TAC[OPEN_UNIV; LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN
      CONJ_TAC THENL
       [SUBGOAL_THEN
         `(\z:real^(1,N)finite_sum. lift(smooth_step(drop(fstcart z)))) =
          (lift o smooth_step o drop) o fstcart`
        SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
        MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `(:real^1)` THEN
        REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV; SMOOTH_STEP_SMOOTH] THEN
        MP_TAC(ISPECL [`(:real^(1,N)finite_sum)`; `\x:real^(1,N)finite_sum. x`;
                       `fstcart:real^(1,N)finite_sum->real^1`]
          SMOOTH_MAP_ON_LINEAR_O) THEN
        REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_ID; LINEAR_FSTCART; o_DEF; ETA_AX];
        SUBGOAL_THEN
         `(\z:real^(1,N)finite_sum. smooth_bump (&1 / &2) (&1) (inv s % sndcart z) %
                                    (v:real^N->real^N) (sndcart z)) =
          (\y. smooth_bump (&1 / &2) (&1) (inv s % y) % v y) o sndcart`
        SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
        MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `(:real^N)` THEN
        ASM_REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV] THEN
        MP_TAC(ISPECL [`(:real^(1,N)finite_sum)`; `\x:real^(1,N)finite_sum. x`;
                       `sndcart:real^(1,N)finite_sum->real^N`]
          SMOOTH_MAP_ON_LINEAR_O) THEN
        REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_ID; LINEAR_SNDCART; o_DEF; ETA_AX]];
      REAL_ARITH_TAC;
      REAL_ARITH_TAC;
      MAP_EVERY X_GEN_TAC [`t:real`; `x:real^N`; `y:real^N`] THEN
      REWRITE_TAC[GSYM VECTOR_SUB_LDISTRIB; NORM_MUL] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `&1 * ((L + &1) * inv(&2 * (L + &1)) * norm(x - y:real^N))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_ABS_POS; NORM_POS_LE] THEN
        CONJ_TAC THENL
         [MP_TAC(SPEC `t:real` SMOOTH_STEP_BOUNDS) THEN REAL_ARITH_TAC;
          USE_THEN "wlip" (fun th -> REWRITE_TAC[th])];
        MATCH_MP_TAC(REAL_ARITH `a = b ==> a <= b`) THEN
        UNDISCH_TAC `&0 < L` THEN CONV_TAC REAL_FIELD]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `G':real->real^N->real^N`) THEN
  MAP_EVERY EXISTS_TAC
   [`\t (y:real^N). y + smooth_step t %
        smooth_bump (&1 / &2) (&1) (inv s % y) % (v:real^N->real^N) y`;
    `G':real->real^N->real^N`; `s:real`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [SIMP_TAC[SMOOTH_STEP_0; VECTOR_MUL_LZERO; VECTOR_ADD_RID];
    SIMP_TAC[SMOOTH_STEP_1; REAL_LE_REFL];
    REPEAT STRIP_TAC THEN USE_THEN "B3" (fun th -> ASM_SIMP_TAC[th]) THEN
    REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_MUL_RZERO; VECTOR_ADD_RID];
    REPEAT STRIP_TAC THEN USE_THEN "B4" (fun th -> ASM_SIMP_TAC[th]) THEN
    SIMP_TAC[SMOOTH_STEP_1; REAL_LE_REFL; VECTOR_MUL_LID] THEN
    USE_THEN "vdef" (fun th -> REWRITE_TAC[th]) THEN VECTOR_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Compositions of sphere isotopies and sphere diffeomorphisms.              *)
(* Maps defined near the sphere are composed after normalizing x to x/|x|,   *)
(* so the composites are smooth on R^N minus 0.                              *)
(* ------------------------------------------------------------------------- *)

let SMT_FAMILY_COMPOSE_MAPS = prove
 (`!u v w (J:real->real^N->real^N) (a:real^M->real^N) (b:real^N->real^P).
        open u /\ open v /\ open w /\ smooth_family u J /\
        smooth_map_on v a /\ smooth_map_on w b /\
        (!x. x IN v ==> a x IN u) /\ (!t x. x IN v ==> J t (a x) IN w)
        ==> smooth_family v (\t x. b(J t (a x)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[smooth_family] THEN
  SUBGOAL_THEN
   `(\z:real^(1,M)finite_sum. (b:real^N->real^P)
        ((J:real->real^N->real^N) (drop(fstcart z))
                                  ((a:real^M->real^N)(sndcart z)))) =
    b o (\z. J (drop(fstcart z)) (sndcart z)) o
        (\z:real^(1,M)finite_sum. pastecart (fstcart z) (a(sndcart z)))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; FSTCART_PASTECART; SNDCART_PASTECART];
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `w:real^N->bool` THEN
  ASM_SIMP_TAC[OPEN_PCROSS; OPEN_UNIV] THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_PASTECART; PASTECART_IN_PCROSS;
                IN_UNIV; o_THM; FSTCART_PASTECART; SNDCART_PASTECART] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
  EXISTS_TAC `(:real^1) PCROSS (u:real^N->bool)` THEN
  ASM_SIMP_TAC[OPEN_PCROSS; OPEN_UNIV] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_PASTECART; PASTECART_IN_PCROSS;
                IN_UNIV; FSTCART_PASTECART; SNDCART_PASTECART] THEN
    ASM_SIMP_TAC[];
    MATCH_MP_TAC SMOOTH_MAP_ON_PASTECART_OPEN THEN
    ASM_SIMP_TAC[OPEN_PCROSS; OPEN_UNIV] THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`(:real^1) PCROSS (v:real^M->bool)`;
                     `\z:real^(1,M)finite_sum. z`;
                     `fstcart:real^(1,M)finite_sum->real^1`]
        SMOOTH_MAP_ON_LINEAR_O) THEN
      ASM_SIMP_TAC[OPEN_PCROSS; OPEN_UNIV; SMOOTH_MAP_ON_ID; LINEAR_FSTCART;
                   o_DEF; ETA_AX];
      SUBGOAL_THEN
       `(\z:real^(1,M)finite_sum. (a:real^M->real^N)(sndcart z)) = a o sndcart`
      SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
      EXISTS_TAC `v:real^M->bool` THEN
      ASM_SIMP_TAC[OPEN_PCROSS; OPEN_UNIV] THEN CONJ_TAC THENL
       [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_PASTECART;
                    PASTECART_IN_PCROSS; SNDCART_PASTECART] THEN
        SIMP_TAC[];
        MP_TAC(ISPECL [`(:real^1) PCROSS (v:real^M->bool)`;
                       `\z:real^(1,M)finite_sum. z`;
                       `sndcart:real^(1,M)finite_sum->real^M`]
          SMOOTH_MAP_ON_LINEAR_O) THEN
        ASM_SIMP_TAC[OPEN_PCROSS; OPEN_UNIV; SMOOTH_MAP_ON_ID; LINEAR_SNDCART;
                     o_DEF; ETA_AX]]];
    UNDISCH_TAC `smooth_family u (J:real->real^N->real^N)` THEN
    REWRITE_TAC[smooth_family]]);;

let SMT_SPHERE_ISOTOPY_SYM = prove
 (`!(J:real->real^N->real^N) J'.
        sphere_isotopy J J' ==> sphere_isotopy J' J`,
  REWRITE_TAC[sphere_isotopy] THEN MESON_TAC[]);;

let SMT_SPHERE_SUBSET_NONZERO = prove
 (`sphere(vec 0:real^N,&1) SUBSET {x | ~(x = vec 0)}`,
  REWRITE_TAC[SUBSET; IN_SPHERE_0; IN_ELIM_THM] THEN GEN_TAC THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM NORM_EQ_0; th]) THEN REAL_ARITH_TAC);;

(* Composing a sphere isotopy with a sphere diffeomorphism on the left.      *)

let SMT_SPHERE_ISOTOPY_LCOMPOSE = prove
 (`!(J:real->real^N->real^N) J' f g.
        sphere_isotopy J J' /\ sphere_diffeo f g
        ==> sphere_isotopy (\t x. f(J t (inv(norm x) % x)))
                           (\t x. J' t (g(inv(norm x) % x)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[sphere_isotopy; sphere_diffeo; smooth_near] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (CONJUNCTS_THEN2 (X_CHOOSE_THEN `u:real^N->bool` STRIP_ASSUME_TAC)
                     (LABEL_TAC "s"))
    (CONJUNCTS_THEN2 (X_CHOOSE_THEN `uf:real^N->bool` STRIP_ASSUME_TAC)
      (CONJUNCTS_THEN2 (X_CHOOSE_THEN `ug:real^N->bool` STRIP_ASSUME_TAC)
                       (LABEL_TAC "fg")))) THEN
  CONJ_TAC THENL
   [EXISTS_TAC `{x:real^N | ~(x = vec 0)}` THEN
    REWRITE_TAC[OPEN_NONZERO; SMT_SPHERE_SUBSET_NONZERO] THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`u:real^N->bool`; `{x:real^N | ~(x = vec 0)}`;
                     `uf:real^N->bool`; `J:real->real^N->real^N`;
                     `\x:real^N. inv(norm x) % x`; `f:real^N->real^N`]
        SMT_FAMILY_COMPOSE_MAPS) THEN
      ASM_REWRITE_TAC[OPEN_NONZERO; SMOOTH_MAP_ON_NORMALIZE; IN_ELIM_THM] THEN
      DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THEN REPEAT STRIP_TAC THENL
       [UNDISCH_TAC `sphere(vec 0:real^N,&1) SUBSET u` THEN
        REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
        ASM_SIMP_TAC[SMT_NORMALIZE_SPHERE];
        UNDISCH_TAC `sphere(vec 0:real^N,&1) SUBSET uf` THEN
        REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
        USE_THEN "s" (fun th -> ASM_SIMP_TAC[th; SMT_NORMALIZE_SPHERE])];
      MP_TAC(ISPECL [`u:real^N->bool`; `{x:real^N | ~(x = vec 0)}`;
                     `(:real^N)`; `J':real->real^N->real^N`;
                     `\x:real^N. (g:real^N->real^N)(inv(norm x) % x)`;
                     `\x:real^N. x`] SMT_FAMILY_COMPOSE_MAPS) THEN
      ASM_REWRITE_TAC[OPEN_NONZERO; OPEN_UNIV; SMOOTH_MAP_ON_ID; IN_UNIV;
                      IN_ELIM_THM] THEN
      DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
       [SUBGOAL_THEN
         `(\x:real^N. (g:real^N->real^N)(inv(norm x) % x)) =
          g o (\x. inv(norm x) % x)` SUBST1_TAC THENL
         [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
        MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
        EXISTS_TAC `ug:real^N->bool` THEN
        ASM_REWRITE_TAC[OPEN_NONZERO; SMOOTH_MAP_ON_NORMALIZE] THEN
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
        REPEAT STRIP_TAC THEN
        UNDISCH_TAC `sphere(vec 0:real^N,&1) SUBSET ug` THEN
        REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
        ASM_SIMP_TAC[SMT_NORMALIZE_SPHERE];
        REPEAT STRIP_TAC THEN
        UNDISCH_TAC `sphere(vec 0:real^N,&1) SUBSET u` THEN
        REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
        USE_THEN "fg" (fun th -> ASM_SIMP_TAC[th; SMT_NORMALIZE_SPHERE])]];
    REPEAT GEN_TAC THEN DISCH_TAC THEN
    ASM_SIMP_TAC[SMT_NORMALIZE_SPHERE_ID] THEN
    SUBGOAL_THEN `(J:real->real^N->real^N) t x IN sphere(vec 0,&1) /\
                  (g:real^N->real^N) x IN sphere(vec 0,&1)`
    STRIP_ASSUME_TAC THENL
     [USE_THEN "s" (fun th -> ASM_SIMP_TAC[th]) THEN
      USE_THEN "fg" (fun th -> ASM_SIMP_TAC[th]);
      ALL_TAC] THEN
    SUBGOAL_THEN `(f:real^N->real^N) (J (t:real) (x:real^N)) IN sphere(vec 0,&1) /\
                  (J':real->real^N->real^N) t (g x) IN sphere(vec 0,&1)`
    STRIP_ASSUME_TAC THENL
     [USE_THEN "s" (fun th -> ASM_SIMP_TAC[th]) THEN
      USE_THEN "fg" (fun th -> ASM_SIMP_TAC[th]);
      ALL_TAC] THEN
    ASM_SIMP_TAC[SMT_NORMALIZE_SPHERE_ID] THEN
    USE_THEN "fg" (fun th -> ASM_SIMP_TAC[th]) THEN
    USE_THEN "s" (fun th -> ASM_SIMP_TAC[th])]);;

(* Conjugating a sphere isotopy by an orthogonal map.                       *)

let SMT_SPHERE_ISOTOPY_ORTHO_CONJ = prove
 (`!(J:real->real^N->real^N) J' Q Q'.
        sphere_isotopy J J' /\ orthogonal_transformation Q /\
        orthogonal_transformation Q' /\ (!x. Q'(Q x) = x) /\ (!x. Q(Q' x) = x)
        ==> sphere_isotopy (\t x. Q(J t (Q' x))) (\t x. Q(J' t (Q' x)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[sphere_isotopy] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (CONJUNCTS_THEN2 (X_CHOOSE_THEN `u:real^N->bool` STRIP_ASSUME_TAC)
                     (LABEL_TAC "s"))
    STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(!v:real^N. norm((Q:real^N->real^N) v) = norm v) /\
                (!v:real^N. norm((Q':real^N->real^N) v) = norm v) /\
                linear (Q:real^N->real^N) /\ linear (Q':real^N->real^N)`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[ORTHOGONAL_TRANSFORMATION; ORTHOGONAL_TRANSFORMATION_LINEAR];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^N. x IN sphere(vec 0,&1)
                           ==> (Q:real^N->real^N) x IN sphere(vec 0,&1) /\
                               (Q':real^N->real^N) x IN sphere(vec 0,&1)`
  ASSUME_TAC THENL [ASM_REWRITE_TAC[IN_SPHERE_0] THEN SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `open {x:real^N | (Q':real^N->real^N) x IN u}` ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE_UNIV THEN
    ASM_SIMP_TAC[LINEAR_CONTINUOUS_AT];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [EXISTS_TAC `{x:real^N | (Q':real^N->real^N) x IN u}` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
      UNDISCH_TAC `sphere(vec 0:real^N,&1) SUBSET u` THEN
      REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `smooth_map_on (:real^N) (Q:real^N->real^N) /\
                  smooth_map_on (:real^N) (Q':real^N->real^N)`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MP_TAC(ISPECL [`(:real^N)`; `\x:real^N. x`; `Q:real^N->real^N`]
          SMOOTH_MAP_ON_LINEAR_O);
        MP_TAC(ISPECL [`(:real^N)`; `\x:real^N. x`; `Q':real^N->real^N`]
          SMOOTH_MAP_ON_LINEAR_O)] THEN
      ASM_REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_ID; o_DEF; ETA_AX];
      ALL_TAC] THEN
    CONJ_TAC THEN MATCH_MP_TAC SMT_FAMILY_COMPOSE_MAPS THEN
    MAP_EVERY EXISTS_TAC [`u:real^N->bool`; `(:real^N)`] THEN
    ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV; IN_ELIM_THM] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^N)` THEN
    ASM_REWRITE_TAC[SUBSET_UNIV];
    REPEAT GEN_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `(Q':real^N->real^N) x IN sphere(vec 0,&1)` ASSUME_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    USE_THEN "s" (fun th -> ASM_SIMP_TAC[th])]);;

(* Composition of sphere diffeomorphisms; slices of sphere isotopies;        *)
(* orthogonal maps.                                                          *)

let SMT_SPHERE_DIFFEO_COMPOSE = prove
 (`!f g f' g':real^N->real^N.
        sphere_diffeo f g /\ sphere_diffeo f' g'
        ==> sphere_diffeo (\x. f(f' x)) (\x. g'(g x))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[sphere_diffeo] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "fg")))
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "fg'")))) THEN
  SUBGOAL_THEN
   `!(a:real^N->real^N) (b:real^N->real^N).
        smooth_near (sphere(vec 0,&1)) a /\ smooth_near (sphere(vec 0,&1)) b /\
        (!x. x IN sphere(vec 0,&1) ==> b x IN sphere(vec 0,&1))
        ==> smooth_near (sphere(vec 0,&1)) (\x. a(b x))`
  (fun th -> CONJ_TAC THENL
     [MATCH_MP_TAC th THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "fg'" (fun th -> SIMP_TAC[th]);
      CONJ_TAC THENL
       [MATCH_MP_TAC th THEN ASM_REWRITE_TAC[] THEN
        USE_THEN "fg" (fun th -> SIMP_TAC[th]);
        ALL_TAC]]) THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[smooth_near] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `ua:real^N->bool` STRIP_ASSUME_TAC)
      (CONJUNCTS_THEN2 (X_CHOOSE_THEN `ub:real^N->bool` STRIP_ASSUME_TAC)
                       ASSUME_TAC)) THEN
    EXISTS_TAC `{x:real^N | x IN ub /\ (b:real^N->real^N) x IN ua}` THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN
      ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON];
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM SET_TAC[];
      SUBGOAL_THEN `(\x:real^N. (a:real^N->real^N)((b:real^N->real^N) x)) = a o b`
      SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
      EXISTS_TAC `ua:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `open {x:real^N | x IN ub /\ (b:real^N->real^N) x IN ua}`
      ASSUME_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN
        ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN SIMP_TAC[];
        MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `ub:real^N->bool` THEN
        ASM_REWRITE_TAC[] THEN SET_TAC[]]];
    REPEAT GEN_TAC THEN DISCH_TAC THEN
    USE_THEN "fg'" (fun th -> ASM_SIMP_TAC[th]) THEN
    USE_THEN "fg" (fun th -> ASM_SIMP_TAC[th])]);;

let SMT_SPHERE_ISOTOPY_SLICE = prove
 (`!(J:real->real^N->real^N) J' t.
        sphere_isotopy J J' ==> sphere_diffeo (J t) (J' t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[sphere_isotopy; sphere_diffeo; smooth_near] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `u:real^N->bool` STRIP_ASSUME_TAC) ASSUME_TAC) THEN
  ASM_SIMP_TAC[] THEN CONJ_TAC THEN EXISTS_TAC `u:real^N->bool` THEN
  ASM_SIMP_TAC[SMT_FAMILY_SLICE]);;

let SMT_SPHERE_DIFFEO_ORTHO = prove
 (`!Q Q':real^N->real^N.
        orthogonal_transformation Q /\ orthogonal_transformation Q' /\
        (!x. Q'(Q x) = x) /\ (!x. Q(Q' x) = x)
        ==> sphere_diffeo Q Q'`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[sphere_diffeo; smooth_near] THEN
  ASM_REWRITE_TAC[IN_SPHERE_0] THEN
  SUBGOAL_THEN `(!v:real^N. norm((Q:real^N->real^N) v) = norm v) /\
                (!v:real^N. norm((Q':real^N->real^N) v) = norm v) /\
                linear (Q:real^N->real^N) /\ linear (Q':real^N->real^N)`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[ORTHOGONAL_TRANSFORMATION; ORTHOGONAL_TRANSFORMATION_LINEAR];
    ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN CONJ_TAC THEN EXISTS_TAC `(:real^N)` THEN
  REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV] THENL
   [MP_TAC(ISPECL [`(:real^N)`; `\x:real^N. x`; `Q:real^N->real^N`]
      SMOOTH_MAP_ON_LINEAR_O);
    MP_TAC(ISPECL [`(:real^N)`; `\x:real^N. x`; `Q':real^N->real^N`]
      SMOOTH_MAP_ON_LINEAR_O)] THEN
  ASM_REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_ID; o_DEF; ETA_AX]);;

(* ------------------------------------------------------------------------- *)
(* The chart at the north pole.  stereo2_s (projection from the              *)
(* south pole) sends basis 3 to 0.  smt_vflip (x3 -> -x3) conjugates the     *)
(* transport S8 at the north pole to the south pole; smt_vext U extends an   *)
(* orthogonal 2x2 matrix U to R^3 fixing the vertical axis, and stereo2_s    *)
(* intertwines it with U.  The chart germ of a sphere diffeomorphism fixing  *)
(* basis 3 is smooth near 0 with invertible derivative.                      *)
(* ------------------------------------------------------------------------- *)

let smt_vflip = new_definition
 `smt_vflip (x:real^3) = vector[x$1; x$2; --(x$3)]:real^3`;;

let smt_vext = new_definition
 `smt_vext (U:real^2^2) (x:real^3) =
    vector[(U ** (vector[x$1; x$2]:real^2))$1;
           (U ** (vector[x$1; x$2]:real^2))$2; x$3]:real^3`;;

let SMT_VECTOR2_ETA = prove
 (`!x:real^2. vector[x$1; x$2] = x`,
  SIMP_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2]);;

let SMT_VFLIP_ORTHO = prove
 (`orthogonal_transformation smt_vflip /\ !x. smt_vflip(smt_vflip x) = x`,
  REWRITE_TAC[ORTHOGONAL_TRANSFORMATION; linear; NORM_EQ; DOT_3; smt_vflip;
              VECTOR_3] THEN
  SIMP_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3; VECTOR_ADD_COMPONENT;
           VECTOR_MUL_COMPONENT] THEN
  REAL_ARITH_TAC);;

let SMT_VFLIP_STEREO = prove
 (`(!x. stereo2_n(smt_vflip x) = stereo2_s x) /\
   (!y. smt_vflip(stereo2_n_inv y) = stereo2_s_inv y) /\
   smt_vflip(basis 3) = --basis 3 /\ smt_vflip(--basis 3) = basis 3`,
  REPEAT CONJ_TAC THENL
   [GEN_TAC THEN
    SIMP_TAC[CART_EQ; DIMINDEX_2; FORALL_2; STEX_STEREO2_N_COMPONENTS;
             STEX_STEREO2_S_COMPONENTS; smt_vflip; VECTOR_3] THEN
    REWRITE_TAC[REAL_SUB_RNEG];
    GEN_TAC THEN
    SIMP_TAC[CART_EQ; DIMINDEX_3; FORALL_3; smt_vflip; VECTOR_3;
             STEX_STEREO2_N_INV_COMPONENTS; STEX_STEREO2_S_INV_COMPONENTS] THEN
    REWRITE_TAC[real_div] THEN REAL_ARITH_TAC;
    SIMP_TAC[CART_EQ; DIMINDEX_3; FORALL_3; smt_vflip; VECTOR_3;
             VECTOR_NEG_COMPONENT; BASIS_COMPONENT; ARITH] THEN
    REAL_ARITH_TAC;
    SIMP_TAC[CART_EQ; DIMINDEX_3; FORALL_3; smt_vflip; VECTOR_3;
             VECTOR_NEG_COMPONENT; BASIS_COMPONENT; ARITH] THEN
    REAL_ARITH_TAC]);;

(* S8 at the south pole: transport of compactly supported planar isotopies  *)
(* by stereo2_s, fixing --basis 3.                                           *)

let SMT_STEREO_TRANSPORT_S = prove
 (`!H K:real->real^2->real^2 R.
        diffeo_isotopy H K /\ (!t x. R <= norm x ==> H t x = x)
        ==> ?J J'. sphere_isotopy J J' /\
                   (!t x. x IN sphere(vec 0,&1) /\ ~(x = --basis 3)
                          ==> J t x = stereo2_s_inv (H t (stereo2_s x))) /\
                   (!t. J t (--basis 3) = --basis 3)`,
  REPEAT STRIP_TAC THEN
  MP_TAC SMT_STEREO_TRANSPORT THEN REWRITE_TAC[SMT_STEREO_TRANSPORT_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPECL [`H:real->real^2->real^2`; `K:real->real^2->real^2`;
                             `R:real`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `J8:real->real^3->real^3`
    (X_CHOOSE_THEN `J8':real->real^3->real^3` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC
   [`\t x. smt_vflip((J8:real->real^3->real^3) t (smt_vflip x))`;
    `\t x. smt_vflip((J8':real->real^3->real^3) t (smt_vflip x))`] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SMT_SPHERE_ISOTOPY_ORTHO_CONJ THEN
    ASM_REWRITE_TAC[SMT_VFLIP_ORTHO];
    MAP_EVERY X_GEN_TAC [`t:real`; `x:real^3`] THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN
    SUBGOAL_THEN `smt_vflip x IN sphere(vec 0,&1) /\ ~(smt_vflip x = basis 3)`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [UNDISCH_TAC `(x:real^3) IN sphere(vec 0,&1)` THEN
        REWRITE_TAC[IN_SPHERE_0] THEN
        MESON_TAC[SMT_VFLIP_ORTHO; ORTHOGONAL_TRANSFORMATION];
        DISCH_THEN(MP_TAC o AP_TERM `smt_vflip`) THEN
        ASM_REWRITE_TAC[SMT_VFLIP_ORTHO; SMT_VFLIP_STEREO]];
      ASM_SIMP_TAC[SMT_VFLIP_STEREO]];
    GEN_TAC THEN ASM_REWRITE_TAC[SMT_VFLIP_STEREO]]);;

(* The vertical extension of an orthogonal 2x2 matrix.                      *)

let SMT_VEXT_COMPONENTS = prove
 (`!(U:real^2^2) x.
        (smt_vext U x)$1 = (U ** (vector[x$1; x$2]:real^2))$1 /\
        (smt_vext U x)$2 = (U ** (vector[x$1; x$2]:real^2))$2 /\
        (smt_vext U x)$3 = x$3`,
  REWRITE_TAC[smt_vext; VECTOR_3]);;

let SMT_MATVEC2_COMPONENTS = prove
 (`!(U:real^2^2) w.
        (U ** w)$1 = U$1$1 * w$1 + U$1$2 * w$2 /\
        (U ** w)$2 = U$2$1 * w$1 + U$2$2 * w$2`,
  SIMP_TAC[matrix_vector_mul; LAMBDA_BETA; DIMINDEX_2; ARITH; SUM_2]);;

let SMT_VEXT_ORTHO = prove
 (`!U:real^2^2.
        orthogonal_matrix U
        ==> orthogonal_transformation (smt_vext U) /\
            (!x. smt_vext (transp U) (smt_vext U x) = x) /\
            (!x. smt_vext U (smt_vext (transp U) x) = x)`,
  GEN_TAC THEN DISCH_TAC THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[ORTHOGONAL_TRANSFORMATION] THEN CONJ_TAC THENL
     [REWRITE_TAC[linear] THEN
      SIMP_TAC[CART_EQ; DIMINDEX_3; FORALL_3; SMT_VEXT_COMPONENTS;
               VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
               SMT_MATVEC2_COMPONENTS; VECTOR_2] THEN
      REAL_ARITH_TAC;
      X_GEN_TAC `x:real^3` THEN REWRITE_TAC[NORM_EQ; DOT_3; SMT_VEXT_COMPONENTS] THEN
      MP_TAC(ISPECL [`U:real^2^2`; `vector[(x:real^3)$1; x$2]:real^2`]
        ORTHOGONAL_MATRIX_NORM) THEN
      ASM_REWRITE_TAC[NORM_EQ; DOT_2; VECTOR_2] THEN REAL_ARITH_TAC];
    GEN_TAC THEN
    ASM_SIMP_TAC[CART_EQ; DIMINDEX_3; FORALL_3; SMT_VEXT_COMPONENTS;
                 SMT_VECTOR2_ETA; MATRIX_VECTOR_MUL_ASSOC;
                 ORTHOGONAL_MATRIX_TRANSP_LMUL; MATRIX_VECTOR_MUL_LID; VECTOR_2];
    GEN_TAC THEN
    ASM_SIMP_TAC[CART_EQ; DIMINDEX_3; FORALL_3; SMT_VEXT_COMPONENTS;
                 SMT_VECTOR2_ETA; MATRIX_VECTOR_MUL_ASSOC;
                 ORTHOGONAL_MATRIX_TRANSP_RMUL; MATRIX_VECTOR_MUL_LID; VECTOR_2]]);;

let SMT_STEREO2_S_ALT = prove
 (`!z:real^3. stereo2_s z = inv(&1 + z$3) % (vector[z$1; z$2]:real^2)`,
  SIMP_TAC[CART_EQ; DIMINDEX_2; FORALL_2; STEX_STEREO2_S_COMPONENTS;
           VECTOR_MUL_COMPONENT; VECTOR_2] THEN
  REWRITE_TAC[real_div] THEN REAL_ARITH_TAC);;

let SMT_VEXT_STEREO = prove
 (`!(U:real^2^2) z. stereo2_s(smt_vext U z) = U ** stereo2_s z`,
  REWRITE_TAC[SMT_STEREO2_S_ALT; SMT_VEXT_COMPONENTS; SMT_VECTOR2_ETA;
              MATRIX_VECTOR_MUL_RMUL]);;

(* Points of the north chart.                                                *)

let SMT_STEREO2_S_POLES = prove
 (`stereo2_s_inv(vec 0) = basis 3 /\ stereo2_s(basis 3) = vec 0 /\
   (basis 3:real^3)$3 = &1 /\ (--basis 3:real^3)$3 = -- &1`,
  SIMP_TAC[CART_EQ; DIMINDEX_3; DIMINDEX_2; FORALL_3; FORALL_2;
           STEX_STEREO2_S_INV_COMPONENTS; STEX_STEREO2_S_COMPONENTS;
           BASIS_COMPONENT; VEC_COMPONENT; VECTOR_NEG_COMPONENT; NORM_0;
           DIMINDEX_3; ARITH] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV);;

let SMT_SPHERE_NOT_SOUTH = prove
 (`!x:real^3. x IN sphere(vec 0,&1) /\ x$3 > -- &1
              ==> x IN sphere(vec 0,&1) DELETE --(basis 3)`,
  GEN_TAC THEN REWRITE_TAC[IN_DELETE] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST_ALL_TAC THEN
  UNDISCH_TAC `(--basis 3:real^3)$3 > -- &1` THEN
  REWRITE_TAC[SMT_STEREO2_S_POLES] THEN REAL_ARITH_TAC);;

(* A smooth map with a smooth local left inverse has invertible derivative.  *)

let SMT_LOCAL_INVERSE_DERIVATIVE = prove
 (`!(k:real^N->real^N) k' W W' a.
        open W /\ open W' /\ a IN W /\ smooth_map_on W k /\ smooth_map_on W' k' /\
        (!y. y IN W ==> k y IN W' /\ k'(k y) = y)
        ==> invertible(matrix(frechet_derivative k (at a)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `(k has_derivative frechet_derivative (k:real^N->real^N) (at a)) (at a) /\
    (k' has_derivative frechet_derivative (k':real^N->real^N) (at (k a)))
      (at (k a))`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[SMOOTH_MAP_ON_HAS_DERIVATIVE]; ALL_TAC] THEN
  SUBGOAL_THEN
   `((k':real^N->real^N) o (k:real^N->real^N) has_derivative
     frechet_derivative k' (at (k a)) o frechet_derivative k (at a)) (at a)`
  ASSUME_TAC THENL [MATCH_MP_TAC DIFF_CHAIN_AT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `((k':real^N->real^N) o (k:real^N->real^N) has_derivative (\h. h))
                (at a)` ASSUME_TAC THENL
   [MP_TAC(ISPEC `W:real^N->bool` OPEN_CONTAINS_BALL) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `a:real^N`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_AT THEN
    MAP_EVERY EXISTS_TAC [`\y:real^N. y`; `d:real`] THEN
    ASM_REWRITE_TAC[HAS_DERIVATIVE_ID; o_THM] THEN
    X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN CONV_TAC SYM_CONV THEN
    SUBGOAL_THEN `(y:real^N) IN W` ASSUME_TAC THENL
     [UNDISCH_TAC `ball(a:real^N,d) SUBSET W` THEN
      REWRITE_TAC[SUBSET; IN_BALL] THEN DISCH_THEN MATCH_MP_TAC THEN
      ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `frechet_derivative (k':real^N->real^N) (at (k a)) o
    frechet_derivative (k:real^N->real^N) (at a) = (\h. h)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC FRECHET_DERIVATIVE_UNIQUE_AT THEN
    MAP_EVERY EXISTS_TAC [`(k':real^N->real^N) o (k:real^N->real^N)`; `a:real^N`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `linear(frechet_derivative (k:real^N->real^N) (at a)) /\
    linear(frechet_derivative (k':real^N->real^N) (at (k a)))`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[has_derivative]; ALL_TAC] THEN
  REWRITE_TAC[INVERTIBLE_LEFT_INVERSE] THEN
  EXISTS_TAC `matrix(frechet_derivative (k':real^N->real^N)
                  (at ((k:real^N->real^N) (a:real^N))))` THEN
  ASM_SIMP_TAC[GSYM MATRIX_COMPOSE; MATRIX_ID]);;

(* The north chart of a map of the sphere.                                   *)

let SMT_SCHART_SMOOTH = prove
 (`!f:real^3->real^3.
        smooth_near (sphere(vec 0,&1)) f /\
        (!x. x IN sphere(vec 0,&1) ==> f x IN sphere(vec 0,&1))
        ==> open {y:real^2 | (f(stereo2_s_inv y))$3 > -- &1} /\
            smooth_map_on {y:real^2 | (f(stereo2_s_inv y))$3 > -- &1}
                          (\y. stereo2_s(f(stereo2_s_inv y))) /\
            (!y. (f(stereo2_s_inv y))$3 > -- &1
                 ==> f(stereo2_s_inv y) IN sphere(vec 0,&1) DELETE --(basis 3))`,
  GEN_TAC THEN REWRITE_TAC[smooth_near] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `u:real^3->bool` STRIP_ASSUME_TAC)
                             ASSUME_TAC) THEN
  SUBGOAL_THEN `smooth_map_on (:real^2) (\y. (f:real^3->real^3)(stereo2_s_inv y))`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `(\y. (f:real^3->real^3)(stereo2_s_inv y)) = f o stereo2_s_inv`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `u:real^3->bool` THEN
    ASM_REWRITE_TAC[OPEN_UNIV; STEX_STEREO2_S_INV_SMOOTH] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_UNIV] THEN X_GEN_TAC `y:real^2` THEN
    UNDISCH_TAC `sphere(vec 0:real^3,&1) SUBSET u` THEN REWRITE_TAC[SUBSET] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    MP_TAC(SPEC `y:real^2` STEX_STEREO2_S_INV_IN) THEN SIMP_TAC[IN_DELETE];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`\y. (f:real^3->real^3)(stereo2_s_inv y)`;
                   `{x:real^3 | x$3 > -- &1}`] CONTINUOUS_OPEN_PREIMAGE_UNIV) THEN
    REWRITE_TAC[IN_ELIM_THM; OPEN_HALFSPACE_COMPONENT_GT] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    MP_TAC(ISPECL [`\y. (f:real^3->real^3)(stereo2_s_inv y)`; `(:real^2)`]
      CONTINUOUS_ON_EQ_CONTINUOUS_AT) THEN
    REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON];
    SUBGOAL_THEN `(\y. stereo2_s((f:real^3->real^3)(stereo2_s_inv y))) =
                  stereo2_s o (\y. f(stereo2_s_inv y))` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
    EXISTS_TAC `{x:real^3 | x$3 > -- &1}` THEN
    REWRITE_TAC[OPEN_HALFSPACE_COMPONENT_GT; STEX_STEREO2_S_SMOOTH] THEN
    REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL [`\y. (f:real^3->real^3)(stereo2_s_inv y)`;
                     `{x:real^3 | x$3 > -- &1}`] CONTINUOUS_OPEN_PREIMAGE_UNIV) THEN
      REWRITE_TAC[IN_ELIM_THM; OPEN_HALFSPACE_COMPONENT_GT] THEN
      DISCH_THEN MATCH_MP_TAC THEN
      MP_TAC(ISPECL [`\y. (f:real^3->real^3)(stereo2_s_inv y)`; `(:real^2)`]
        CONTINUOUS_ON_EQ_CONTINUOUS_AT) THEN
      REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN
      DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN
      ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN SIMP_TAC[];
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
      ASM_REWRITE_TAC[SUBSET_UNIV]];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC SMT_SPHERE_NOT_SOUTH THEN
    ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    MP_TAC(SPEC `y:real^2` STEX_STEREO2_S_INV_IN) THEN SIMP_TAC[IN_DELETE]]);;

let SMT_SCHART_GERM = prove
 (`!f g:real^3->real^3.
        sphere_diffeo f g /\ f(basis 3) = basis 3
        ==> ?W. open W /\ vec 0 IN W /\
                smooth_map_on W (\y. stereo2_s(f(stereo2_s_inv y))) /\
                (!y. y IN W
                     ==> f(stereo2_s_inv y) IN sphere(vec 0,&1) DELETE --(basis 3)) /\
                stereo2_s(f(stereo2_s_inv(vec 0))) = vec 0 /\
                invertible(matrix(frechet_derivative
                  (\y. stereo2_s(f(stereo2_s_inv y))) (at (vec 0))))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[sphere_diffeo] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "fg")))
   ASSUME_TAC) THEN
  MP_TAC(SPEC `f:real^3->real^3` SMT_SCHART_SMOOTH) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN USE_THEN "fg" (fun th -> SIMP_TAC[th]);
                  STRIP_TAC] THEN
  MP_TAC(SPEC `g:real^3->real^3` SMT_SCHART_SMOOTH) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN USE_THEN "fg" (fun th -> SIMP_TAC[th]);
                  STRIP_TAC] THEN
  EXISTS_TAC `{y:real^2 | ((f:real^3->real^3)(stereo2_s_inv y))$3 > -- &1}` THEN
  ASM_REWRITE_TAC[IN_ELIM_THM; SMT_STEREO2_S_POLES] THEN
  CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC SMT_LOCAL_INVERSE_DERIVATIVE THEN
  MAP_EVERY EXISTS_TAC
   [`\y. stereo2_s((g:real^3->real^3)(stereo2_s_inv y))`;
    `{y:real^2 | ((f:real^3->real^3)(stereo2_s_inv y))$3 > -- &1}`;
    `{y:real^2 | ((g:real^3->real^3)(stereo2_s_inv y))$3 > -- &1}`] THEN
  ASM_REWRITE_TAC[IN_ELIM_THM; SMT_STEREO2_S_POLES] THEN
  CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `y:real^2` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `stereo2_s_inv(stereo2_s((f:real^3->real^3)(stereo2_s_inv y))) =
    f(stereo2_s_inv y)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC STEX_STEREO2_S_LEFT THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(g:real^3->real^3)(f(stereo2_s_inv y)) = stereo2_s_inv y`
  SUBST1_TAC THENL
   [MP_TAC(SPEC `y:real^2` STEX_STEREO2_S_INV_IN) THEN REWRITE_TAC[IN_DELETE] THEN
    USE_THEN "fg" (fun th -> SIMP_TAC[th]);
    ALL_TAC] THEN
  REWRITE_TAC[STEX_STEREO2_S_RIGHT] THEN
  MP_TAC(SPEC `y:real^2` STEX_STEREO2_S_INV_IN) THEN
  MP_TAC STEX_STEREO2_S_DOMAIN THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
  MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The linear step.  For a sphere diffeomorphism f2 fixing                   *)
(* basis 3 with north chart germ k, Dk(0) = U P (right polar decomposition). *)
(* The germ isotopy of S4b' for P^-1, transported by stereo2_s, composed on  *)
(* the left with smt_vext (transp U) o f2, ends at f4 whose chart germ       *)
(* k4 = U^T o k o P^-1 has derivative I at 0.                                *)
(* ------------------------------------------------------------------------- *)

let SMT_SPHERE_ISOTOPY_INITIAL = prove
 (`!(J:real->real^3->real^3) (H:real->real^2->real^2).
        (!t x. x IN sphere(vec 0,&1) /\ ~(x = --basis 3)
               ==> J t x = stereo2_s_inv (H t (stereo2_s x))) /\
        (!t. J t (--basis 3) = --basis 3) /\
        (!x. H (&0) x = x)
        ==> !x. x IN sphere(vec 0,&1) ==> J (&0) x = x`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `x:real^3 = --basis 3` THEN
  ASM_SIMP_TAC[] THEN MATCH_MP_TAC STEX_STEREO2_S_LEFT THEN
  ASM_REWRITE_TAC[IN_DELETE]);;

let SMT_VEXT_SPHERE_DIFFEO = prove
 (`!U:real^2^2.
        orthogonal_matrix U
        ==> sphere_diffeo (smt_vext (transp U)) (smt_vext U) /\
            sphere_diffeo (smt_vext U) (smt_vext (transp U))`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `orthogonal_matrix(transp(U:real^2^2))` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[ORTHOGONAL_MATRIX_TRANSP]; ALL_TAC] THEN
  MP_TAC(SPEC `U:real^2^2` SMT_VEXT_ORTHO) THEN
  MP_TAC(SPEC `transp(U:real^2^2)` SMT_VEXT_ORTHO) THEN
  ASM_REWRITE_TAC[TRANSP_TRANSP] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC SMT_SPHERE_DIFFEO_ORTHO THEN ASM_REWRITE_TAC[]);;

let SMT_POLE_LINEAR_STEP = prove
 (`!f2 g2:real^3->real^3.
        sphere_diffeo f2 g2 /\ f2(basis 3) = basis 3
        ==> ?U I1 I1' f4 g4 W4 k4.
              orthogonal_matrix (U:real^2^2) /\
              sphere_isotopy I1 I1' /\
              (!x. x IN sphere(vec 0,&1)
                   ==> I1 (&0) x = smt_vext (transp U) (f2 x) /\
                       I1 (&1) x = f4 x) /\
              sphere_diffeo f4 g4 /\
              open W4 /\ vec 0 IN W4 /\ smooth_map_on W4 k4 /\
              k4(vec 0) = vec 0 /\ (k4 has_derivative (\y. y)) (at (vec 0)) /\
              (!x. x IN sphere(vec 0,&1) /\ ~(x = --basis 3) /\
                   stereo2_s x IN W4
                   ==> f4 x IN sphere(vec 0,&1) DELETE --(basis 3) /\
                       stereo2_s(f4 x) = k4(stereo2_s x))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f2:real^3->real^3`; `g2:real^3->real^3`] SMT_SCHART_GERM) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `W:real^2->bool` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `k = \y:real^2. stereo2_s((f2:real^3->real^3)(stereo2_s_inv y))` THEN
  ABBREV_TAC `D = frechet_derivative (k:real^2->real^2) (at (vec 0))` THEN
  MP_TAC(ISPEC `matrix(D:real^2->real^2)` RIGHT_POLAR_DECOMPOSITION_INVERTIBLE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `U:real^2^2` (X_CHOOSE_THEN `P:real^2^2`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `invertible(P:real^2^2)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[POSITIVE_DEFINITE_IMP_INVERTIBLE]; ALL_TAC] THEN
  (* the germ isotopy for P^-1 *)
  MP_TAC(ISPEC `(:2)` SMT_POSDEF_GERM) THEN REWRITE_TAC[SMT_POSDEF_GERM_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPEC `\y:real^2. matrix_inv(P:real^2^2) ** y`) THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_LINEAR; MATRIX_OF_MATRIX_VECTOR_MUL] THEN
  ASM_REWRITE_TAC[POSITIVE_DEFINITE_INV] THEN
  DISCH_THEN(X_CHOOSE_THEN `H:real->real^2->real^2` (X_CHOOSE_THEN
    `K:real->real^2->real^2` (X_CHOOSE_THEN `e:real` (CONJUNCTS_THEN2
    ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "H0")
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "H1")
    (X_CHOOSE_TAC `R0:real`))))))))) THEN
  MP_TAC(ISPECL [`H:real->real^2->real^2`; `K:real->real^2->real^2`; `R0:real`]
    SMT_STEREO_TRANSPORT_S) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `J:real->real^3->real^3` (X_CHOOSE_THEN
    `J':real->real^3->real^3` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "Jdef") (LABEL_TAC "JS"))))) THEN
  (* f3 = U^T o f2 *)
  MP_TAC(SPEC `U:real^2^2` SMT_VEXT_SPHERE_DIFFEO) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`smt_vext (transp U)`; `smt_vext U`; `f2:real^3->real^3`;
                 `g2:real^3->real^3`] SMT_SPHERE_DIFFEO_COMPOSE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`J:real->real^3->real^3`; `J':real->real^3->real^3`;
                 `\x. smt_vext (transp U) ((f2:real^3->real^3) x)`;
                 `\x. (g2:real^3->real^3)(smt_vext U x)`]
    SMT_SPHERE_ISOTOPY_LCOMPOSE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MAP_EVERY EXISTS_TAC
   [`U:real^2^2`;
    `\t x. smt_vext (transp U) ((f2:real^3->real^3)
             ((J:real->real^3->real^3) t (inv(norm x) % x)))`;
    `\t x. (J':real->real^3->real^3) t
             ((g2:real^3->real^3)(smt_vext U (inv(norm x) % x)))`;
    `\x. smt_vext (transp U) ((f2:real^3->real^3)((J:real->real^3->real^3) (&1) x))`;
    `\x. (J':real->real^3->real^3) (&1) ((g2:real^3->real^3)(smt_vext U x))`;
    `{y:real^2 | y IN ball(vec 0,e) /\ matrix_inv(P:real^2^2) ** y IN W}`;
    `\y:real^2. transp(U:real^2^2) ** (k:real^2->real^2)(matrix_inv P ** y)`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [(* endpoints of I1 *)
    X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN ASM_SIMP_TAC[SMT_NORMALIZE_SPHERE_ID] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN
    MP_TAC(ISPECL [`J:real->real^3->real^3`;
                   `H:real->real^2->real^2`] SMT_SPHERE_ISOTOPY_INITIAL) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN GEN_TAC THEN USE_THEN "H0" MATCH_MP_TAC THEN
      REAL_ARITH_TAC;
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    (* sphere_diffeo f4 g4 *)
    MP_TAC(ISPECL [`\x. smt_vext (transp U) ((f2:real^3->real^3) x)`;
                   `\x. (g2:real^3->real^3)(smt_vext U x)`;
                   `(J:real->real^3->real^3) (&1)`;
                   `(J':real->real^3->real^3) (&1)`] SMT_SPHERE_DIFFEO_COMPOSE) THEN
    ASM_SIMP_TAC[SMT_SPHERE_ISOTOPY_SLICE];
    (* W4 open *)
    MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN
    ASM_REWRITE_TAC[OPEN_BALL] THEN
    MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN REWRITE_TAC[MATRIX_VECTOR_MUL_LINEAR];
    (* 0 in W4 *)
    ASM_REWRITE_TAC[IN_ELIM_THM; CENTRE_IN_BALL; MATRIX_VECTOR_MUL_RZERO];
    (* k4 smooth *)
    SUBGOAL_THEN
     `(\y:real^2. transp(U:real^2^2) ** (k:real^2->real^2)(matrix_inv P ** y)) =
      (\y. transp U ** y) o (k o (\y. matrix_inv P ** y))` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    SUBGOAL_THEN
     `open {y:real^2 | y IN ball(vec 0,e) /\ matrix_inv(P:real^2^2) ** y IN W}`
    ASSUME_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN
      ASM_REWRITE_TAC[OPEN_BALL] THEN
      MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN REWRITE_TAC[MATRIX_VECTOR_MUL_LINEAR];
      ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_LINEAR_O THEN
    ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_LINEAR] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `W:real^2->bool` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN SIMP_TAC[];
      MP_TAC(ISPECL [`{y:real^2 | y IN ball(vec 0,e) /\
                                  matrix_inv(P:real^2^2) ** y IN W}`;
                     `\x:real^2. x`; `\y:real^2. matrix_inv(P:real^2^2) ** y`]
        SMOOTH_MAP_ON_LINEAR_O) THEN
      ASM_REWRITE_TAC[SMOOTH_MAP_ON_ID; MATRIX_VECTOR_MUL_LINEAR; o_DEF]];
    (* k4 0 = 0 *)
    REWRITE_TAC[MATRIX_VECTOR_MUL_RZERO] THEN EXPAND_TAC "k" THEN
    ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_RZERO];
    (* Dk4(0) = I *)
    SUBGOAL_THEN `((k:real^2->real^2) has_derivative D) (at (vec 0))` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`W:real^2->bool`; `k:real^2->real^2`]
        SMOOTH_MAP_ON_HAS_DERIVATIVE) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o SPEC `vec 0:real^2`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      EXPAND_TAC "D" THEN REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `linear(D:real^2->real^2)` ASSUME_TAC THENL
     [ASM_MESON_TAC[has_derivative]; ALL_TAC] THEN
    SUBGOAL_THEN
     `((\y:real^2. transp(U:real^2^2) ** y) o ((k:real^2->real^2) o
         (\y. matrix_inv(P:real^2^2) ** y)) has_derivative
       (\y:real^2. transp U ** y) o ((D:real^2->real^2) o (\y. matrix_inv P ** y)))
      (at (vec 0))`
    MP_TAC THENL
     [MATCH_MP_TAC DIFF_CHAIN_AT THEN
      SIMP_TAC[HAS_DERIVATIVE_LINEAR; MATRIX_VECTOR_MUL_LINEAR] THEN
      MATCH_MP_TAC DIFF_CHAIN_AT THEN
      SIMP_TAC[HAS_DERIVATIVE_LINEAR; MATRIX_VECTOR_MUL_LINEAR] THEN
      ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_RZERO];
      ALL_TAC] THEN
    MATCH_MP_TAC(MESON[]
     `(f:real^2->real^2) = f' /\ (d:real^2->real^2) = d'
      ==> (f has_derivative d) (net:(real^2)net)
          ==> (f' has_derivative d') net`) THEN
    CONJ_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    REWRITE_TAC[FUN_EQ_THM; o_THM] THEN X_GEN_TAC `h:real^2` THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[GSYM(MATCH_MP MATRIX_WORKS th)]) THEN
    UNDISCH_TAC `(U:real^2^2) ** (P:real^2^2) = matrix(D:real^2->real^2)` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[MATRIX_VECTOR_MUL_ASSOC; MATRIX_MUL_ASSOC] THEN
    ASM_SIMP_TAC[ORTHOGONAL_MATRIX_TRANSP_LMUL; MATRIX_MUL_LID; MATRIX_INV;
                 MATRIX_VECTOR_MUL_LID];
    (* the chart relation for f4 *)
    X_GEN_TAC `x:real^3` THEN REWRITE_TAC[IN_ELIM_THM; IN_BALL_0] THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `(J:real->real^3->real^3) (&1) x =
      stereo2_s_inv(matrix_inv(P:real^2^2) ** stereo2_s x)`
    SUBST1_TAC THENL
     [USE_THEN "Jdef" (fun th -> ASM_SIMP_TAC[th]) THEN AP_TERM_TAC THEN
      USE_THEN "H1" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ABBREV_TAC `z = (f2:real^3->real^3)
                      (stereo2_s_inv(matrix_inv(P:real^2^2) ** stereo2_s x))` THEN
    SUBGOAL_THEN `(z:real^3) IN sphere(vec 0,&1) DELETE --(basis 3)` ASSUME_TAC THENL
     [EXPAND_TAC "z" THEN FIRST_X_ASSUM(MATCH_MP_TAC o check
       (fun th -> can (find_term ((=) `--(basis 3):real^3`)) (concl th) &&
                  is_forall (concl th))) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SMT_SPHERE_NOT_SOUTH THEN CONJ_TAC THENL
       [UNDISCH_TAC `sphere_diffeo (smt_vext (transp U)) (smt_vext U)` THEN
        REWRITE_TAC[sphere_diffeo] THEN
        DISCH_THEN(MP_TAC o SPEC `z:real^3` o CONJUNCT2 o CONJUNCT2) THEN
        UNDISCH_TAC `(z:real^3) IN sphere(vec 0,&1) DELETE --(basis 3)` THEN
        SIMP_TAC[IN_DELETE];
        REWRITE_TAC[SMT_VEXT_COMPONENTS] THEN
        UNDISCH_TAC `(z:real^3) IN sphere(vec 0,&1) DELETE --(basis 3)` THEN
        MP_TAC STEX_STEREO2_S_DOMAIN THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
        MESON_TAC[]];
      REWRITE_TAC[SMT_VEXT_STEREO] THEN AP_TERM_TAC THEN
      EXPAND_TAC "k" THEN ASM_REWRITE_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* The cut-off step.  The chart germ k4 (Dk4(0) = I) agrees                  *)
(* near 0 with the time-1 map of a compactly supported planar isotopy G      *)
(* (SMT_GERM_CUTOFF); its transport Gh by stereo2_s agrees with f4 near the  *)
(* north pole, so f5 = f4 o Gh'(1) is the identity near the north pole.      *)
(* ------------------------------------------------------------------------- *)

let SMT_NORTH_CHART_SMALL = prove
 (`!s. &0 < s
       ==> ?d. &0 < d /\
               !z:real^3. z IN sphere(vec 0,&1) /\ norm(z - basis 3) < d
                          ==> ~(z = --basis 3) /\ norm(stereo2_s z) < s`,
  REPEAT STRIP_TAC THEN EXISTS_TAC `min (&1 / &2) (s pow 2 / &2)` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[REAL_LT_MIN] THEN CONJ_TAC THENL
     [REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_DIV THEN REWRITE_TAC[REAL_OF_NUM_LT; ARITH] THEN
      ASM_SIMP_TAC[REAL_POW_LT]];
    ALL_TAC] THEN
  X_GEN_TAC `z:real^3` THEN REWRITE_TAC[IN_SPHERE_0] THEN STRIP_TAC THEN
  SUBGOAL_THEN `abs((z:real^3)$3 - &1) < min (&1 / &2) (s pow 2 / &2) /\
                (z:real^3)$3 <= &1`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LET_TRANS THEN
      EXISTS_TAC `norm(z - basis 3:real^3)` THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`z - basis 3:real^3`; `3`] COMPONENT_LE_NORM) THEN
      REWRITE_TAC[VECTOR_SUB_COMPONENT; SMT_STEREO2_S_POLES];
      MP_TAC(ISPECL [`z:real^3`; `3`] COMPONENT_LE_NORM) THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(z:real^3 = --basis 3)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `abs((--basis 3:real^3)$3 - &1) < min (&1 / &2) (s pow 2 / &2)` THEN
    REWRITE_TAC[SMT_STEREO2_S_POLES] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPEC `z:real^3` STEX_STEREO2_S_NORM2) THEN
  ASM_REWRITE_TAC[IN_DELETE; IN_SPHERE_0] THEN STRIP_TAC THEN
  MATCH_MP_TAC REAL_POW_LT2_REV THEN EXISTS_TAC `2` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&1 <= &1 + (z:real^3)$3` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `&1 - (z:real^3)$3` THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `&1 <= a ==> &0 < a`] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LTE_TRANS THEN
    EXISTS_TAC `min (&1 / &2) (s pow 2 / &2)` THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 < b /\ m <= b / &2 ==> m <= b`) THEN
    ASM_SIMP_TAC[REAL_POW_LT] THEN REAL_ARITH_TAC]);;

let SMT_POLE_CUTOFF_STEP = prove
 (`!(f4:real^3->real^3) g4 W4 (k4:real^2->real^2).
        sphere_diffeo f4 g4 /\ open W4 /\ vec 0 IN W4 /\ smooth_map_on W4 k4 /\
        k4(vec 0) = vec 0 /\ (k4 has_derivative (\y. y)) (at (vec 0)) /\
        (!x. x IN sphere(vec 0,&1) /\ ~(x = --basis 3) /\ stereo2_s x IN W4
             ==> f4 x IN sphere(vec 0,&1) DELETE --(basis 3) /\
                 stereo2_s(f4 x) = k4(stereo2_s x))
        ==> ?I2 I2' f5 g5 e5.
              sphere_isotopy I2 I2' /\
              (!x. x IN sphere(vec 0,&1)
                   ==> I2 (&0) x = f4 x /\ I2 (&1) x = f5 x) /\
              sphere_diffeo f5 g5 /\ &0 < e5 /\
              (!x. x IN sphere(vec 0,&1) /\ norm(x - basis 3) < e5
                   ==> f5 x = x)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (LABEL_TAC "chart"))))))) THEN
  MP_TAC(ISPECL [`k4:real^2->real^2`; `W4:real^2->bool`] SMT_GERM_CUTOFF) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `G:real->real^2->real^2` (X_CHOOSE_THEN
    `G':real->real^2->real^2` (X_CHOOSE_THEN `s:real` (CONJUNCTS_THEN2
    ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "G0") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "Gfar") (LABEL_TAC "G1")))))))))) THEN
  MP_TAC(ISPECL [`G:real->real^2->real^2`; `G':real->real^2->real^2`; `s:real`]
    SMT_STEREO_TRANSPORT_S) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `Gh:real->real^3->real^3` (X_CHOOSE_THEN
    `Gh':real->real^3->real^3` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "Ghdef") (LABEL_TAC "GhS"))))) THEN
  SUBGOAL_THEN `sphere_isotopy (Gh':real->real^3->real^3) Gh` ASSUME_TAC THENL
   [ASM_SIMP_TAC[SMT_SPHERE_ISOTOPY_SYM]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [sphere_isotopy] o check
    (fun th -> concl th = `sphere_isotopy (Gh:real->real^3->real^3) Gh'`)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `u:real^3->bool` STRIP_ASSUME_TAC)
                             (LABEL_TAC "Ghs")) THEN
  MP_TAC(ISPECL [`Gh':real->real^3->real^3`; `Gh:real->real^3->real^3`;
                 `f4:real^3->real^3`; `g4:real^3->real^3`]
    SMT_SPHERE_ISOTOPY_LCOMPOSE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  (* the agreement of f4 and Gh 1 near the north pole *)
  SUBGOAL_THEN
   `!z. z IN sphere(vec 0,&1) /\ ~(z = --basis 3) /\ norm(stereo2_s z) <= s / &2
        ==> (f4:real^3->real^3) z = (Gh:real->real^3->real^3) (&1) z`
  (LABEL_TAC "agree") THENL
   [REPEAT STRIP_TAC THEN
    USE_THEN "Ghdef" (fun th -> ASM_SIMP_TAC[th]) THEN
    USE_THEN "G1" (fun th -> ASM_SIMP_TAC[th]) THEN
    USE_THEN "chart" (MP_TAC o SPEC `z:real^3`) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `cball(vec 0:real^2,s) SUBSET W4` THEN
      REWRITE_TAC[SUBSET; IN_CBALL_0] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM)) THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC STEX_STEREO2_S_LEFT THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* Gh 1 and Gh' 1 fix the north pole *)
  SUBGOAL_THEN `(basis 3:real^3) IN sphere(vec 0,&1) /\ ~(basis 3 = --basis 3:real^3)`
  STRIP_ASSUME_TAC THENL
   [SIMP_TAC[IN_SPHERE_0; NORM_BASIS; DIMINDEX_3; ARITH] THEN
    DISCH_THEN(MP_TAC o AP_TERM `\x:real^3. x$3`) THEN
    REWRITE_TAC[SMT_STEREO2_S_POLES] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(Gh:real->real^3->real^3) (&1) (basis 3) = basis 3`
  ASSUME_TAC THENL
   [USE_THEN "Ghdef" (fun th -> ASM_SIMP_TAC[th]) THEN
    REWRITE_TAC[SMT_STEREO2_S_POLES] THEN
    SUBGOAL_THEN `(G:real->real^2->real^2) (&1) (vec 0) = (k4:real^2->real^2)(vec 0)` SUBST1_TAC THENL
     [USE_THEN "G1" MATCH_MP_TAC THEN REWRITE_TAC[NORM_0] THEN ASM_REAL_ARITH_TAC;
      ASM_REWRITE_TAC[SMT_STEREO2_S_POLES]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(Gh':real->real^3->real^3) (&1) (basis 3) = basis 3`
  ASSUME_TAC THENL
   [FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [SYM th]) THEN
    USE_THEN "Ghs" (fun th -> ASM_SIMP_TAC[th]);
    ALL_TAC] THEN
  (* continuity of Gh' 1 at the north pole *)
  SUBGOAL_THEN `(Gh':real->real^3->real^3) (&1) continuous at (basis 3)`
  MP_TAC THENL
   [SUBGOAL_THEN `smooth_map_on u ((Gh':real->real^3->real^3) (&1))` MP_TAC THENL
     [MATCH_MP_TAC SMT_FAMILY_SLICE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o MATCH_MP SMOOTH_MAP_ON_CONTINUOUS_ON) THEN
    ASM_SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_AT] THEN DISCH_THEN MATCH_MP_TAC THEN
    UNDISCH_TAC `sphere(vec 0:real^3,&1) SUBSET u` THEN REWRITE_TAC[SUBSET] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPEC `s / &2` SMT_NORTH_CHART_SMALL) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "small"))) THEN
  REWRITE_TAC[continuous_at] THEN DISCH_THEN(MP_TAC o SPEC `d:real`) THEN
  ASM_REWRITE_TAC[dist] THEN
  DISCH_THEN(X_CHOOSE_THEN `e5:real` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC
   [`\t x. (f4:real^3->real^3) ((Gh':real->real^3->real^3) t (inv(norm x) % x))`;
    `\t x. (Gh:real->real^3->real^3) t ((g4:real^3->real^3)(inv(norm x) % x))`;
    `\x. (f4:real^3->real^3) ((Gh':real->real^3->real^3) (&1) x)`;
    `\x. (Gh:real->real^3->real^3) (&1) ((g4:real^3->real^3) x)`;
    `e5:real`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN ASM_SIMP_TAC[SMT_NORMALIZE_SPHERE_ID] THEN
    AP_TERM_TAC THEN
    MP_TAC(ISPECL [`Gh:real->real^3->real^3`; `G:real->real^2->real^2`]
      SMT_SPHERE_ISOTOPY_INITIAL) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN GEN_TAC THEN USE_THEN "G0" MATCH_MP_TAC THEN
      REAL_ARITH_TAC;
      DISCH_THEN(MP_TAC o SPEC `x:real^3`) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [SYM th]) THEN
      USE_THEN "Ghs" (fun th -> ASM_SIMP_TAC[th])];
    MP_TAC(ISPECL [`f4:real^3->real^3`; `g4:real^3->real^3`;
                   `(Gh':real->real^3->real^3) (&1)`;
                   `(Gh:real->real^3->real^3) (&1)`] SMT_SPHERE_DIFFEO_COMPOSE) THEN
    ASM_SIMP_TAC[SMT_SPHERE_ISOTOPY_SLICE];
    X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(Gh':real->real^3->real^3) (&1) x IN sphere(vec 0,&1)`
    ASSUME_TAC THENL [USE_THEN "Ghs" (fun th -> ASM_SIMP_TAC[th]); ALL_TAC] THEN
    USE_THEN "small" (MP_TAC o SPEC `(Gh':real->real^3->real^3) (&1) x`) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM(MP_TAC o SPEC `x:real^3`) THEN
      ASM_REWRITE_TAC[];
      STRIP_TAC] THEN
    USE_THEN "agree" (MP_TAC o SPEC `(Gh':real->real^3->real^3) (&1) x`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN USE_THEN "Ghs" (fun th -> ASM_SIMP_TAC[th])]);;

(* ------------------------------------------------------------------------- *)
(* S7.  An orthogonal R moves f(basis 3) to basis 3; the linear              *)
(* step and the cut-off step give isotopies smt_vext(U^T) o R o f ~ f4 ~ f5  *)
(* with f5 = I near basis 3; they are concatenated and composed with the     *)
(* orthogonal map Q = R^-1 o smt_vext U.                                     *)
(* ------------------------------------------------------------------------- *)

let SMT_SPHERE_POLE = prove
 (`SMT_SPHERE_POLE_STATEMENT`,
  REWRITE_TAC[SMT_SPHERE_POLE_STATEMENT] THEN
  MAP_EVERY X_GEN_TAC [`f:real^3->real^3`; `g:real^3->real^3`] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(basis 3:real^3) IN sphere(vec 0,&1)` ASSUME_TAC THENL
   [SIMP_TAC[IN_SPHERE_0; NORM_BASIS; DIMINDEX_3; ARITH]; ALL_TAC] THEN
  SUBGOAL_THEN `(f:real^3->real^3)(basis 3) IN sphere(vec 0,&1)` ASSUME_TAC THENL
   [UNDISCH_TAC `sphere_diffeo (f:real^3->real^3) g` THEN
    REWRITE_TAC[sphere_diffeo] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(f:real^3->real^3)(basis 3)`; `basis 3:real^3`]
    ORTHOGONAL_TRANSFORMATION_EXISTS_1) THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `(f:real^3->real^3)(basis 3) IN sphere(vec 0,&1)` THEN
    UNDISCH_TAC `(basis 3:real^3) IN sphere(vec 0,&1)` THEN
    SIMP_TAC[IN_SPHERE_0];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `R:real^3->real^3` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `R':real^3->real^3` STRIP_ASSUME_TAC o
    MATCH_MP ORTHOGONAL_TRANSFORMATION_INVERSE) THEN
  SUBGOAL_THEN
   `sphere_diffeo (\x. (R:real^3->real^3)((f:real^3->real^3) x))
                  (\x. (g:real^3->real^3)((R':real^3->real^3) x))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SMT_SPHERE_DIFFEO_COMPOSE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SMT_SPHERE_DIFFEO_ORTHO THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\x. (R:real^3->real^3)((f:real^3->real^3) x)`;
                 `\x. (g:real^3->real^3)((R':real^3->real^3) x)`]
    SMT_POLE_LINEAR_STEP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `U:real^2^2` (X_CHOOSE_THEN `I1:real->real^3->real^3`
    (X_CHOOSE_THEN `I1':real->real^3->real^3` (X_CHOOSE_THEN `f4:real^3->real^3`
    (X_CHOOSE_THEN `g4:real^3->real^3` (X_CHOOSE_THEN `W4:real^2->bool`
    (X_CHOOSE_THEN `k4:real^2->real^2` STRIP_ASSUME_TAC))))))) THEN
  MP_TAC(ISPECL [`f4:real^3->real^3`; `g4:real^3->real^3`; `W4:real^2->bool`;
                 `k4:real^2->real^2`] SMT_POLE_CUTOFF_STEP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `I2:real->real^3->real^3` (X_CHOOSE_THEN
    `I2':real->real^3->real^3` (X_CHOOSE_THEN `f5:real^3->real^3`
    (X_CHOOSE_THEN `g5:real^3->real^3` (X_CHOOSE_THEN `e5:real`
    STRIP_ASSUME_TAC))))) THEN
  MP_TAC(ISPECL [`I1:real->real^3->real^3`; `I1':real->real^3->real^3`;
                 `I2:real->real^3->real^3`; `I2':real->real^3->real^3`;
                 `\x. smt_vext (transp U) ((R:real^3->real^3)((f:real^3->real^3) x))`;
                 `f4:real^3->real^3`; `f5:real^3->real^3`]
    SMT_SPHERE_ISOTOPY_CONCAT) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `II:real->real^3->real^3` (X_CHOOSE_THEN
    `II':real->real^3->real^3` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `orthogonal_transformation
                  (\x. (R':real^3->real^3)(smt_vext U x))` ASSUME_TAC THENL
   [SUBGOAL_THEN `(\x. (R':real^3->real^3)(smt_vext U x)) = R' o smt_vext U`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC ORTHOGONAL_TRANSFORMATION_COMPOSE THEN
    ASM_SIMP_TAC[SMT_VEXT_ORTHO];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`II:real->real^3->real^3`; `II':real->real^3->real^3`;
                 `\x. (R':real^3->real^3)(smt_vext U x)`]
    SMT_SPHERE_ISOTOPY_ORTHO) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `K':real->real^3->real^3`) THEN
  MAP_EVERY EXISTS_TAC
   [`\t x. (R':real^3->real^3)(smt_vext U ((II:real->real^3->real^3) t x))`;
    `K':real->real^3->real^3`; `\x. (R':real^3->real^3)(smt_vext U x)`;
    `f5:real^3->real^3`; `g5:real^3->real^3`; `e5:real`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[SMT_VEXT_ORTHO]);;

(* With S7, the Smale chain rests on S3 (planar isotopies) alone.          *)

let SMT_SMALE_FROM_PLANAR = prove
 (`SMT_PLANAR_ISOTOPY_STATEMENT ==> SMT_SMALE_RADIAL_STATEMENT`,
  MESON_TAC[SMT_SMALE_FROM_POLE_PLANAR; SMT_SPHERE_POLE]);;

