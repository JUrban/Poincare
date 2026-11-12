(* ========================================================================= *)
(* Unit pc_rfa_slcut: the cutoff function for the local Shi estimates        *)
(* (CLN Lemmas 6.17 and 6.20): the radial bump psi(w) = phi(|w|) in          *)
(* exponential coordinates, its gradient and Laplacian bounds at the initial *)
(* time from the Hessian comparison, and at later times through the          *)
(* evolution of the Christoffel symbols.                                     *)
(* ========================================================================= *)

needs "src/pc_rfa_slbar.ml";;
needs "src/pc_rfa_r1.ml";;
needs "src/pc_cmp_pull.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* Derivatives of smooth real functions, the radial profile                  *)
(* phi and the bump psi = phi o norm.                                        *)
(* ========================================================================= *)

let RFA_SMOOTH_REAL_DERIV = prove
 (`!g. smooth_map_on (:real^1) (lift o g o drop)
       ==> smooth_map_on (:real^1) (lift o real_derivative g o drop) /\
           !x. (g has_real_derivative real_derivative g x) (atreal x)`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `!x. (g has_real_derivative real_derivative g x) (atreal x)` ASSUME_TAC THENL
   [X_GEN_TAC `x:real` THEN
    SUBGOAL_THEN `(lift o g o drop) differentiable (at (lift x))` MP_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `(:real^1)` THEN
      ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV];
      ALL_TAC] THEN
    REWRITE_TAC[differentiable] THEN
    DISCH_THEN(X_CHOOSE_THEN `f':real^1->real^1` ASSUME_TAC) THEN
    SUBGOAL_THEN `linear(f':real^1->real^1)` MP_TAC THENL
     [ASM_MESON_TAC[has_derivative]; ALL_TAC] THEN
    REWRITE_TAC[LINEAR_1] THEN DISCH_THEN(X_CHOOSE_THEN `c:real` SUBST_ALL_TAC) THEN
    SUBGOAL_THEN `(g has_real_derivative c) (atreal x)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[HAS_REAL_FRECHET_DERIVATIVE_AT]; ALL_TAC] THEN
    FIRST_ASSUM(SUBST1_TAC o MATCH_MP HAS_REAL_DERIVATIVE_DERIVATIVE) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `lift o real_derivative g o drop =
    (\y. frechet_derivative (lift o g o drop) (at y) (lift(&1)))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM] THEN X_GEN_TAC `y:real^1` THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `drop y`) THEN
    REWRITE_TAC[HAS_REAL_FRECHET_DERIVATIVE_AT; LIFT_DROP] THEN
    DISCH_THEN(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
    REWRITE_TAC[GSYM LIFT_CMUL; REAL_MUL_RID];
    MATCH_MP_TAC SMOOTH_MAP_ON_FRECHET_DERIVATIVE THEN ASM_REWRITE_TAC[OPEN_UNIV]]);;

(* The radial profile of the bump smooth_bump a b = prof a b o norm of       *)
(* ns_cutoff (from the Navier_Stokes development).                           *)

let rfa_prof = new_definition
 `rfa_prof a b (s:real) = smooth_step((b pow 2 - s pow 2) / (b pow 2 - a pow 2))`;;

let RFA_PROF_BUMP = prove
 (`!a b (w:real^N). smooth_bump a b w = rfa_prof a b (norm w)`,
  REWRITE_TAC[smooth_bump; rfa_prof]);;

let RFA_PROF_SMOOTH = prove
 (`!a b. smooth_map_on (:real^1) (lift o rfa_prof a b o drop)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[o_DEF; rfa_prof] THEN
  MP_TAC(ISPECL [`(:real^1)`;
                 `\x:real^1. lift((b pow 2 - drop x pow 2) / (b pow 2 - a pow 2))`]
         SMOOTH_MAP_ON_SMOOTH_STEP_COMPOSE) THEN
  REWRITE_TAC[LIFT_DROP; OPEN_UNIV] THEN DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[real_div] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  MP_TAC(ISPECL [`(:real^1)`; `inv(b pow 2 - a pow 2)`;
                 `\x:real^1. lift(b pow 2 - drop x pow 2)`] SMOOTH_MAP_ON_LIFT_CMUL) THEN
  REWRITE_TAC[LIFT_DROP; OPEN_UNIV] THEN DISCH_THEN MATCH_MP_TAC THEN
  MP_TAC(ISPECL [`(:real^1)`; `\x:real^1. lift(b pow 2)`;
                 `\x:real^1. lift(drop x pow 2)`] SMOOTH_MAP_ON_LIFT_SUB) THEN
  REWRITE_TAC[LIFT_DROP; OPEN_UNIV; SMOOTH_MAP_ON_CONST] THEN DISCH_THEN MATCH_MP_TAC THEN
  MP_TAC(ISPECL [`(:real^1)`; `\x:real^1. x`; `2`] SMOOTH_MAP_ON_LIFT_POW) THEN
  REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_ID]);;

let RFA_PROF_VALUES = prove
 (`!a b s. &0 <= a /\ a < b
           ==> &0 <= rfa_prof a b s /\ rfa_prof a b s <= &1 /\
               (abs s <= a ==> rfa_prof a b s = &1) /\
               (b <= abs s ==> rfa_prof a b s = &0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[rfa_prof; SMOOTH_STEP_BOUNDS] THEN
  SUBGOAL_THEN `&0 < b pow 2 - a pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC CUTOFF_BUMP_DENOM_POS THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THEN DISCH_TAC THENL
   [MATCH_MP_TAC SMOOTH_STEP_1 THEN ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_MUL_LID] THEN
    SUBGOAL_THEN `s pow 2 <= a pow 2` MP_TAC THENL
     [GEN_REWRITE_TAC LAND_CONV [GSYM REAL_POW2_ABS] THEN MATCH_MP_TAC REAL_POW_LE2 THEN
      ASM_REWRITE_TAC[REAL_ABS_POS];
      REAL_ARITH_TAC];
    MATCH_MP_TAC SMOOTH_STEP_0 THEN ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_MUL_LZERO] THEN
    SUBGOAL_THEN `b pow 2 <= s pow 2` MP_TAC THENL
     [GEN_REWRITE_TAC RAND_CONV [GSYM REAL_POW2_ABS] THEN MATCH_MP_TAC REAL_POW_LE2 THEN
      ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC]]);;

let RFA_PROF_DERIVS = prove
 (`!a b. (!x. (rfa_prof a b has_real_derivative real_derivative (rfa_prof a b) x)
              (atreal x)) /\
         (!x. (real_derivative (rfa_prof a b) has_real_derivative
               real_derivative (real_derivative (rfa_prof a b)) x) (atreal x)) /\
         smooth_map_on (:real^1) (lift o real_derivative (rfa_prof a b) o drop) /\
         smooth_map_on (:real^1)
           (lift o real_derivative (real_derivative (rfa_prof a b)) o drop)`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPEC `rfa_prof a b` RFA_SMOOTH_REAL_DERIV) THEN
  REWRITE_TAC[RFA_PROF_SMOOTH] THEN STRIP_TAC THEN
  MP_TAC(SPEC `real_derivative (rfa_prof a b)` RFA_SMOOTH_REAL_DERIV) THEN
  ASM_REWRITE_TAC[] THEN SIMP_TAC[]);;

let RFA_CONT_BOUNDED_INTERVAL = prove
 (`!f R. (lift o f o drop) continuous_on (:real^1)
         ==> ?C. !s. abs s <= R ==> abs(f s) <= C`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`lift o f o drop`; `interval[lift(--R),lift R]`]
         COMPACT_CONTINUOUS_IMAGE) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[COMPACT_INTERVAL] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^1)` THEN
    ASM_REWRITE_TAC[SUBSET_UNIV];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
  REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE; o_THM; NORM_LIFT] THEN
  DISCH_THEN(X_CHOOSE_THEN `C:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `C:real` THEN X_GEN_TAC `s:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `lift s`) THEN
  REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP] THEN ANTS_TAC THENL
   [ASM_REAL_ARITH_TAC; SIMP_TAC[]]);;

let RFA_PROF_DBOUNDS = prove
 (`!a b R. ?C1 C2. &0 <= C1 /\ &0 <= C2 /\
                   !s. abs s <= R
                       ==> abs(real_derivative (rfa_prof a b) s) <= C1 /\
                           abs(real_derivative (real_derivative (rfa_prof a b)) s) <= C2`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`a:real`; `b:real`] RFA_PROF_DERIVS) THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`real_derivative (rfa_prof a b)`; `R:real`] RFA_CONT_BOUNDED_INTERVAL) THEN
  ANTS_TAC THENL [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `C1:real`) THEN
  MP_TAC(ISPECL [`real_derivative (real_derivative (rfa_prof a b))`; `R:real`]
         RFA_CONT_BOUNDED_INTERVAL) THEN
  ANTS_TAC THENL [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `C2:real`) THEN
  MAP_EVERY EXISTS_TAC [`abs C1`; `abs C2`] THEN REWRITE_TAC[REAL_ABS_POS] THEN
  ASM_MESON_TAC[REAL_ARITH `x <= c ==> x <= abs c`]);;

(* ========================================================================= *)
(* The Hessian cmp_lhess in coordinates, its change under a                  *)
(* change of the metric, and llap, lgrad2 in an orthonormal frame.           *)
(* ========================================================================= *)

let RFA_LHESS_D = prove
 (`!(G:real^N->real^N^N) f y a b.
     cmp_lhess G f y a b = rfa_d2 f y b a - rfa_d1 f y (christoffel G y b a)`,
  REWRITE_TAC[cmp_lhess; LRG_LNABLA_EQ; rfa_d1; rfa_d2; SUM_SING_NUMSEG] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[LIFT_DROP; ETA_AX]);;

let RFA_D1_LINEAR = prove
 (`!U (f:real^N->real) y.
     open U /\ smooth_map_on U (\z. lift(f z)) /\ y IN U
     ==> (!u v. rfa_d1 f y (u - v) = rfa_d1 f y u - rfa_d1 f y v) /\
         (!c u. rfa_d1 f y (c % u) = c * rfa_d1 f y u) /\
         (!u. rfa_d1 f y u = sum(1..dimindex(:N)) (\i. u$i * rfa_d1 f y (basis i)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `linear(frechet_derivative (\z. lift((f:real^N->real) z)) (at y))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[rfa_d1] THEN REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[LINEAR_SUB; DROP_SUB];
    ASM_SIMP_TAC[LINEAR_CMUL; DROP_CMUL];
    GEN_TAC THEN FIRST_ASSUM(MP_TAC o SPEC `u:real^N` o MATCH_MP LRG_LINEAR_DROP_EXPAND) THEN
    DISCH_THEN(ACCEPT_TAC o SYM)]);;

let RFA_LLAP_FRAME = prove
 (`!U (G:real^N->real^N^N) f y (S:real^N^N).
     metric_field U G /\ smooth_map_on U (\z. lift(f z)) /\ y IN U /\
     matrix_inv(G y) = transp S ** S
     ==> llap G f y =
         sum(1..dimindex(:N)) (\r. cmp_lhess G f y (transp S ** basis r) (transp S ** basis r))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `f:real^N->real`; `y:real^N`]
         LRG_LLAP_LNABLA) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  ABBREV_TAC
   `Tq = lnabla 1 (G:real^N->real^N^N)
          (\z u. drop(frechet_derivative (\w. lift((f:real^N->real) w)) (at z) (u 1)))` THEN
  SUBGOAL_THEN `ltensor_field (0 + 2) U (Tq:real^N->(num->real^N)->real)` ASSUME_TAC THENL
   [EXPAND_TAC "Tq" THEN REWRITE_TAC[ARITH_RULE `0 + 2 = 1 + 1`] THEN
    MP_TAC(ISPECL [`1`; `U:real^N->bool`; `G:real^N->real^N^N`;
                   `\z u. drop(frechet_derivative (\w. lift((f:real^N->real) w)) (at z)
                                                   (u 1))`] LNABLA_TENSOR_FIELD) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`U:real^N->bool`; `f:real^N->real`] LRG_DF_TENSOR_FIELD) THEN
      ASM_SIMP_TAC[];
      SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!v1 v2 (w:num->real^N).
      (Tq:real^N->(num->real^N)->real) y
        (\m. if m = 1 then v1 else if m = 2 then v2 else w m) =
      Tq y (\m. if m = 1 then v1 else v2)`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN
    UNDISCH_TAC `ltensor_field (0 + 2) U (Tq:real^N->(num->real^N)->real)` THEN
    REWRITE_TAC[ltensor_field] THEN DISCH_THEN(MP_TAC o SPEC `y:real^N`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN
    X_GEN_TAC `m:num` THEN STRIP_TAC THEN
    ASM_CASES_TAC `m = 1` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `m = 2` SUBST1_TAC THENL [ASM_ARITH_TAC; REWRITE_TAC[]] THEN
    CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  REWRITE_TAC[cmp_lhess] THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`0`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `Tq:real^N->(num->real^N)->real`; `y:real^N`; `S:real^N^N`;
                 `\m:num. vec 0:real^N`] RFA_CONTR_FRAME) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  GEN_REWRITE_TAC LAND_CONV [SUM_SWAP_NUMSEG] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `b:num` THEN STRIP_TAC THEN BETA_TAC THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM TRANSP_COMPONENT] THEN
  REWRITE_TAC[MATRIX_TRANSP_MUL; TRANSP_TRANSP]);;

let RFA_LGRAD2_FRAME = prove
 (`!U (G:real^N->real^N^N) f y (S:real^N^N).
     open U /\ smooth_map_on U (\z. lift(f z)) /\ y IN U /\
     matrix_inv(G y) = transp S ** S
     ==> lgrad2 G f y = sum(1..dimindex(:N)) (\r. rfa_d1 f y (transp S ** basis r) pow 2)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `f:real^N->real`; `y:real^N`] RFA_D1_LINEAR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "lin" o CONJUNCT2 o CONJUNCT2) THEN
  REWRITE_TAC[RFA_LGRAD2_D1; rfa_lginner] THEN
  REWRITE_TAC[ASSUME `matrix_inv((G:real^N->real^N^N) y) = transp(S:real^N^N) ** S`] THEN
  REWRITE_TAC[BETA_RULE(ISPECL [`S:real^N^N`; `\a. rfa_d1 (f:real^N->real) y (basis a)`]
                                RFA_QUAD_FRAME)] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `p:num` THEN STRIP_TAC THEN BETA_TAC THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  USE_THEN "lin" (fun th -> GEN_REWRITE_TAC RAND_CONV [th]) THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN BETA_TAC THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC LRG_TRANSP_BASIS_COMPONENT THEN ASM_REWRITE_TAC[]);;

let RFA_LHESS_SHIFT = prove
 (`!U (G1:real^N->real^N^N) G2 f y u v.
     open U /\ smooth_map_on U (\z. lift(f z)) /\ y IN U
     ==> cmp_lhess G2 f y u v =
         cmp_lhess G1 f y u v - rfa_d1 f y (christoffel G2 y v u - christoffel G1 y v u)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `f:real^N->real`; `y:real^N`] RFA_D1_LINEAR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT1 th]) THEN
  REWRITE_TAC[RFA_LHESS_D] THEN REAL_ARITH_TAC);;

(* ========================================================================= *)
(* First and second derivatives of the radial bump                           *)
(* psi(w) = prof(|w|) away from the origin, and its flatness near it.        *)
(* ========================================================================= *)

let RFA_NORM_D1 = prove
 (`!(z:real^N) h. ~(z = vec 0) ==> rfa_d1 (\w. norm w) z h = (z dot h) / norm z`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rfa_d1] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[SYM(MATCH_MP FRECHET_DERIVATIVE_AT
                                           (MATCH_MP CMPP_NORM_DERIV th))]) THEN
  REWRITE_TAC[LIFT_DROP]);;

let RFA_NORM_SMOOTH = prove
 (`smooth_map_on {w:real^N | ~(w = vec 0)} (\w. lift(norm w)) /\
   open {w:real^N | ~(w = vec 0)}`,
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`{w:real^N | ~(w = vec 0)}`; `\w:real^N. w`] SMOOTH_MAP_ON_LIFT_NORM) THEN
    REWRITE_TAC[SMOOTH_MAP_ON_ID; IN_ELIM_THM] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[SET_RULE `{w:real^N | ~(w = vec 0)} = (:real^N) DIFF {vec 0}`] THEN
    MATCH_MP_TAC OPEN_DIFF THEN REWRITE_TAC[OPEN_UNIV; CLOSED_SING];
    REWRITE_TAC[SET_RULE `{w:real^N | ~(w = vec 0)} = (:real^N) DIFF {vec 0}`] THEN
    MATCH_MP_TAC OPEN_DIFF THEN REWRITE_TAC[OPEN_UNIV; CLOSED_SING]]);;

let RFA_BUMP_D1 = prove
 (`!a b (z:real^N) h.
     ~(z = vec 0)
     ==> rfa_d1 (\w. rfa_prof a b (norm w)) z h =
         real_derivative (rfa_prof a b) (norm z) * (z dot h) / norm z`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\w:real^N. norm w`; `rfa_prof a b`;
                 `real_derivative (rfa_prof a b) (norm(z:real^N))`; `z:real^N`; `h:real^N`]
         RFA_D1_COMPOSE_AT) THEN
  REWRITE_TAC[RFA_PROF_DERIVS] THEN ANTS_TAC THENL
   [REWRITE_TAC[differentiable] THEN ASM_MESON_TAC[CMPP_NORM_DERIV]; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC[RFA_NORM_D1]);;

let RFA_BUMP_LHESS = prove
 (`!a b (G:real^N->real^N^N) z u.
     ~(z = vec 0)
     ==> cmp_lhess G (\w. rfa_prof a b (norm w)) z u u =
         real_derivative (real_derivative (rfa_prof a b)) (norm z) *
         ((z dot u) / norm z) pow 2 +
         real_derivative (rfa_prof a b) (norm z) * cmp_lhess G (\w. norm w) z u u`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[RFA_LHESS_D] THEN
  MP_TAC(ISPECL [`{w:real^N | ~(w = vec 0)}`; `(:real)`; `\w:real^N. norm w`;
                 `rfa_prof a b`; `real_derivative (rfa_prof a b)`;
                 `real_derivative (real_derivative (rfa_prof a b))`; `z:real^N`;
                 `u:real^N`; `u:real^N`] RFA_D2_COMPOSE) THEN
  ASM_REWRITE_TAC[RFA_NORM_SMOOTH; IN_ELIM_THM; IN_UNIV; RFA_PROF_DERIVS] THEN
  DISCH_THEN SUBST1_TAC THEN
  ASM_SIMP_TAC[RFA_BUMP_D1; RFA_NORM_D1; REAL_POW_2] THEN REAL_ARITH_TAC);;

let RFA_BUMP_FLAT = prove
 (`!a b (G:real^N->real^N^N) z.
     &0 < a /\ a < b /\ norm z < a
     ==> (!h. rfa_d1 (\w. rfa_prof a b (norm w)) z h = &0) /\
         (!u v. cmp_lhess G (\w. rfa_prof a b (norm w)) z u v = &0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!w:real^N. w IN ball(vec 0,a) ==> rfa_prof a b (norm w) = (\w:real^N. &1) w`
  ASSUME_TAC THENL
   [REWRITE_TAC[IN_BALL_0] THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
    MP_TAC(SPECL [`a:real`; `b:real`; `norm(w:real^N)`] RFA_PROF_VALUES) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SIMP_TAC[REAL_ABS_NORM] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT1 o CONJUNCT2 o
                                            CONJUNCT2) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(z:real^N) IN ball(vec 0,a)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[IN_BALL_0]; ALL_TAC] THEN
  SUBGOAL_THEN `!y h. y IN ball(vec 0:real^N,a)
                      ==> rfa_d1 (\w. rfa_prof a b (norm w)) y h = &0`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `rfa_d1 (\w:real^N. &1) y h` THEN CONJ_TAC THENL
     [MATCH_MP_TAC RFA_D1_LOCAL THEN EXISTS_TAC `ball(vec 0:real^N,a)` THEN
      ASM_REWRITE_TAC[OPEN_BALL];
      REWRITE_TAC[RFA_D1_CONST]];
    ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN REPEAT GEN_TAC THEN REWRITE_TAC[RFA_LHESS_D; RFA_D2_AS_D1] THEN
  ASM_SIMP_TAC[REAL_SUB_RZERO] THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `rfa_d1 (\w:real^N. &0) z v` THEN CONJ_TAC THENL
   [MATCH_MP_TAC RFA_D1_LOCAL THEN EXISTS_TAC `ball(vec 0:real^N,a)` THEN
    ASM_SIMP_TAC[OPEN_BALL];
    REWRITE_TAC[RFA_D1_CONST]]);;

(* ========================================================================= *)
(* Gradient and Laplacian bounds of the radial bump for a                    *)
(* metric G2 comparable to a reference metric G1 with the Gauss lemma and   *)
(* the Hessian comparison of |w| (CLN Lemma 6.17 in exponential coordinates, *)
(* plus the change of the Christoffel symbols, CLN Lemma 6.20).              *)
(* ========================================================================= *)

let RFA_GAUSS_CS = prove
 (`!U (G:real^N->real^N^N) y v.
     metric_field U G /\ y IN U /\ G y ** y = y
     ==> (y dot v) pow 2 <= (y dot y) * (v dot (G y ** v))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `y:real^N`; `v:real^N`]
         LRG_METRIC_CS) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(y:real^N) dot ((G:real^N->real^N^N) y ** v) = y dot v` SUBST1_TAC THENL
   [SUBGOAL_THEN `transp((G:real^N->real^N^N) y) = G y` ASSUME_TAC THENL
     [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
    REWRITE_TAC[GSYM DOT_MATRIX_TRANSP_LMUL] THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[]]);;

let RFA_BUMP_D1_ABS = prove
 (`!a b (z:real^N) w C1.
     &0 < a /\ a < b /\ abs(real_derivative (rfa_prof a b) (norm z)) <= C1
     ==> abs(rfa_d1 (\w. rfa_prof a b (norm w)) z w) <= C1 * norm w`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `z:real^N = vec 0` THENL
   [MP_TAC(ISPECL [`a:real`; `b:real`; `\w:real^N. mat 1:real^N^N`; `z:real^N`]
           RFA_BUMP_FLAT) THEN
    ASM_REWRITE_TAC[NORM_0] THEN DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT1 th]) THEN
    REWRITE_TAC[REAL_ABS_0] THEN MATCH_MP_TAC REAL_LE_MUL THEN
    REWRITE_TAC[NORM_POS_LE] THEN ASM_MESON_TAC[REAL_ABS_POS; REAL_LE_TRANS];
    ALL_TAC] THEN
  ASM_SIMP_TAC[RFA_BUMP_D1] THEN
  SUBGOAL_THEN `&0 < norm(z:real^N)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  REWRITE_TAC[REAL_ABS_MUL; real_div; REAL_ABS_INV; REAL_ABS_NORM] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_ABS_POS] THEN
  CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_MUL THEN SIMP_TAC[REAL_ABS_POS; REAL_LE_INV_EQ;
                                                          NORM_POS_LE]; ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM real_div; REAL_LE_LDIV_EQ] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[NORM_CAUCHY_SCHWARZ_ABS]);;

let RFA_BUMP_SMOOTH_ON = prove
 (`!a b U. &0 < a /\ a < b
           ==> smooth_map_on U (\w. lift(rfa_prof a b (norm(w:real^N))))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
  EXISTS_TAC `(:real^N)` THEN REWRITE_TAC[SUBSET_UNIV; GSYM RFA_PROF_BUMP] THEN
  MATCH_MP_TAC SMOOTH_BUMP_SMOOTH THEN ASM_REAL_ARITH_TAC);;

let RFA_CUT_GRAD_TERM = prove
 (`!a b U (G1:real^N->real^N^N) z v C1.
     metric_field U G1 /\ z IN U /\ &0 < a /\ a < b /\ G1 z ** z = z /\
     abs(real_derivative (rfa_prof a b) (norm z)) <= C1
     ==> rfa_d1 (\w. rfa_prof a b (norm w)) z v pow 2 <= C1 pow 2 * (v dot (G1 z ** v))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= C1` ASSUME_TAC THENL
   [ASM_MESON_TAC[REAL_ABS_POS; REAL_LE_TRANS]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= v dot ((G1:real^N->real^N^N) z ** v)` ASSUME_TAC THENL
   [MATCH_MP_TAC LRG_METRIC_NONNEG THEN EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `z:real^N = vec 0` THENL
   [MP_TAC(ISPECL [`a:real`; `b:real`; `G1:real^N->real^N^N`; `z:real^N`] RFA_BUMP_FLAT) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[NORM_0]; ALL_TAC] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT1 th]) THEN
    CONV_TAC(LAND_CONV REAL_RAT_REDUCE_CONV) THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < norm(z:real^N) pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  ASM_SIMP_TAC[RFA_BUMP_D1] THEN
  REWRITE_TAC[REAL_POW_MUL; REAL_POW_DIV] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_LE_POW_2] THEN REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[GSYM REAL_LE_SQUARE_ABS] THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_LE_POW_2] THEN ASM_REAL_ARITH_TAC;
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G1:real^N->real^N^N`; `z:real^N`; `v:real^N`]
           RFA_GAUSS_CS) THEN
    ASM_REWRITE_TAC[GSYM NORM_POW_2] THEN REAL_ARITH_TAC]);;

let RFA_CUT_GRAD = prove
 (`!a b U (G1:real^N->real^N^N) G2 z C1 E.
     open U /\ metric_field U G1 /\ metric_field U G2 /\ z IN U /\ &0 < a /\ a < b /\
     G1 z ** z = z /\ abs(real_derivative (rfa_prof a b) (norm z)) <= C1 /\ &0 <= E /\
     (!v. v dot (G1 z ** v) <= E * (v dot (G2 z ** v)))
     ==> lgrad2 G2 (\w. rfa_prof a b (norm w)) z <= C1 pow 2 * E * &(dimindex(:N))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G2:real^N->real^N^N`; `z:real^N`]
         LRG_METRIC_INV_FACTOR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `S:real^N^N` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G2:real^N->real^N^N`;
                 `\w. rfa_prof a b (norm(w:real^N))`; `z:real^N`; `S:real^N^N`]
         RFA_LGRAD2_FRAME) THEN
  ASM_SIMP_TAC[RFA_BUMP_SMOOTH_ON] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(1..dimindex(:N)) (\r. C1 pow 2 * E)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `r:num` THEN STRIP_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `C1 pow 2 * ((transp(S:real^N^N) ** basis r) dot ((G1:real^N->real^N^N) z **
                                                      (transp S ** basis r)))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC RFA_CUT_GRAD_TERM THEN EXISTS_TAC `U:real^N->bool` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `E * ((transp(S:real^N^N) ** basis r) dot ((G2:real^N->real^N^N) z **
                                               (transp S ** basis r)))` THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G2:real^N->real^N^N`; `z:real^N`; `S:real^N^N`]
           RFA_FRAME_ORTHO) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPECL [`r:num`; `r:num`]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC;
    REWRITE_TAC[SUM_CONST_NUMSEG; ARITH_RULE `(n + 1) - 1 = n`] THEN REAL_ARITH_TAC]);;

let RFA_CUT_LAP_TERM = prove
 (`!a b U (G1:real^N->real^N^N) G2 z v K rho C1 C2.
     open U /\ metric_field U G1 /\ z IN U /\ &0 < a /\ a < b /\ &0 <= K /\
     a <= norm z /\ norm z < rho /\ G1 z ** z = z /\
     (!v. abs(cmp_lhess G1 (\w. norm w) z v v) <=
          (inv(norm z) + K * norm z) * (v dot (G1 z ** v))) /\
     abs(real_derivative (rfa_prof a b) (norm z)) <= C1 /\
     abs(real_derivative (real_derivative (rfa_prof a b)) (norm z)) <= C2
     ==> abs(cmp_lhess G2 (\w. rfa_prof a b (norm w)) z v v) <=
         (C2 + C1 * (inv a + K * rho)) * (v dot (G1 z ** v)) +
         C1 * norm(christoffel G2 z v v - christoffel G1 z v v)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(z:real^N = vec 0) /\ &0 < norm(z:real^N)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [DISCH_TAC THEN UNDISCH_TAC `a <= norm(z:real^N)` THEN
                    ASM_REWRITE_TAC[NORM_0] THEN ASM_REAL_ARITH_TAC;
                    ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= C1 /\ &0 <= C2` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[REAL_ABS_POS; REAL_LE_TRANS]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= v dot ((G1:real^N->real^N^N) z ** v)` ASSUME_TAC THENL
   [MATCH_MP_TAC LRG_METRIC_NONNEG THEN EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G1:real^N->real^N^N`; `G2:real^N->real^N^N`;
                 `\w. rfa_prof a b (norm(w:real^N))`; `z:real^N`; `v:real^N`; `v:real^N`]
         RFA_LHESS_SHIFT) THEN
  ASM_SIMP_TAC[RFA_BUMP_SMOOTH_ON] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_SIMP_TAC[RFA_BUMP_LHESS] THEN
  ABBREV_TAC `w = christoffel (G2:real^N->real^N^N) z v v - christoffel G1 z v v` THEN
  MP_TAC(ISPECL [`a:real`; `b:real`; `z:real^N`; `w:real^N`; `C1:real`] RFA_BUMP_D1_ABS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `((z dot v) / norm(z:real^N)) pow 2 <= v dot ((G1:real^N->real^N^N) z ** v)`
  ASSUME_TAC THENL
   [REWRITE_TAC[REAL_POW_DIV] THEN
    SUBGOAL_THEN `&0 < norm(z:real^N) pow 2` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G1:real^N->real^N^N`; `z:real^N`; `v:real^N`]
           RFA_GAUSS_CS) THEN
    ASM_REWRITE_TAC[GSYM NORM_POW_2] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `inv(norm(z:real^N)) + K * norm z <= inv a + K * rho` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `abs(real_derivative (real_derivative (rfa_prof a b)) (norm(z:real^N)) *
        ((z dot v) / norm z) pow 2) <= C2 * (v dot ((G1:real^N->real^N^N) z ** v))`
  ASSUME_TAC THENL
   [REWRITE_TAC[REAL_ABS_MUL] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
    ASM_REWRITE_TAC[REAL_ABS_POS] THEN
    REWRITE_TAC[REAL_ABS_POW] THEN ASM_REWRITE_TAC[REAL_POW2_ABS];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `abs(real_derivative (rfa_prof a b) (norm(z:real^N)) *
        cmp_lhess (G1:real^N->real^N^N) (\w. norm w) z v v) <=
    C1 * (inv a + K * rho) * (v dot (G1 z ** v))`
  ASSUME_TAC THENL
   [REWRITE_TAC[REAL_ABS_MUL] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
    ASM_REWRITE_TAC[REAL_ABS_POS] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(inv(norm(z:real^N)) + K * norm z) * (v dot ((G1:real^N->real^N^N) z ** v))` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY UNDISCH_TAC
   [`abs(real_derivative (rfa_prof a b) (norm(z:real^N)) *
         cmp_lhess (G1:real^N->real^N^N) (\w. norm w) z v v) <=
     C1 * (inv a + K * rho) * (v dot (G1 z ** v))`;
    `abs(real_derivative (real_derivative (rfa_prof a b)) (norm(z:real^N)) *
         ((z dot v) / norm z) pow 2) <= C2 * (v dot ((G1:real^N->real^N^N) z ** v))`;
    `abs(rfa_d1 (\w. rfa_prof a b (norm w)) (z:real^N) w) <= C1 * norm w`] THEN
  REAL_ARITH_TAC);;

let RFA_NEG_MUL_ABS = prove
 (`!p x. &0 <= p /\ p <= &1 ==> --(p * x) <= abs x`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `abs(p * x)` THEN
  REWRITE_TAC[REAL_ARITH `--y <= abs y`; REAL_ABS_MUL] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 <= p ==> abs p = p`] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[REAL_ABS_POS]);;

let RFA_NEG_MUL_LE = prove
 (`!p x y. &0 <= p /\ abs x <= y ==> --(p * x) <= p * y`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `abs(p * x)` THEN
  REWRITE_TAC[REAL_ARITH `--y <= abs y`; REAL_ABS_MUL] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 <= p ==> abs p = p`] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]);;

let RFA_CUT_LAP = prove
 (`!a b U (G1:real^N->real^N^N) G2 z K rho C1 C2 E L Dg.
     open U /\ metric_field U G1 /\ metric_field U G2 /\ z IN U /\ &0 < a /\ a < b /\
     &0 <= K /\ norm z < rho /\ G1 z ** z = z /\
     (~(z = vec 0) ==> !v. abs(cmp_lhess G1 (\w. norm w) z v v) <=
                            (inv(norm z) + K * norm z) * (v dot (G1 z ** v))) /\
     abs(real_derivative (rfa_prof a b) (norm z)) <= C1 /\
     abs(real_derivative (real_derivative (rfa_prof a b)) (norm z)) <= C2 /\
     &0 <= E /\ (!v. v dot (G1 z ** v) <= E * (v dot (G2 z ** v))) /\
     &0 <= L /\ (!v. norm v pow 2 <= L * (v dot (G2 z ** v))) /\
     &0 <= Dg /\
     (!v. rfa_prof a b (norm z) * norm(christoffel G2 z v v - christoffel G1 z v v) <=
          Dg * norm v pow 2)
     ==> --(rfa_prof a b (norm z) * llap G2 (\w. rfa_prof a b (norm w)) z) <=
         ((C2 + C1 * (inv a + K * rho)) * E + C1 * Dg * L) * &(dimindex(:N))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= C1 /\ &0 <= C2 /\ &0 <= inv a + K * rho` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[REAL_ABS_POS; REAL_LE_TRANS];
      ASM_MESON_TAC[REAL_ABS_POS; REAL_LE_TRANS];
      MATCH_MP_TAC REAL_LE_ADD THEN ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPEC `z:real^N` NORM_POS_LE) THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= ((C2 + C1 * (inv a + K * rho)) * E + C1 * Dg * L) *
                       &(dimindex(:N))` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_ADD THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G2:real^N->real^N^N`; `z:real^N`]
         LRG_METRIC_INV_FACTOR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `S:real^N^N` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G2:real^N->real^N^N`;
                 `\w. rfa_prof a b (norm(w:real^N))`; `z:real^N`; `S:real^N^N`]
         RFA_LLAP_FRAME) THEN
  ASM_SIMP_TAC[RFA_BUMP_SMOOTH_ON] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_CASES_TAC `norm(z:real^N) < a` THENL
   [MP_TAC(ISPECL [`a:real`; `b:real`; `G2:real^N->real^N^N`; `z:real^N`] RFA_BUMP_FLAT) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT2 th]) THEN
    ASM_REWRITE_TAC[SUM_0; REAL_MUL_RZERO; REAL_NEG_0];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(z:real^N = vec 0)` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `~(norm(z:real^N) < a)` THEN
    ASM_REWRITE_TAC[NORM_0];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= rfa_prof a b (norm(z:real^N)) /\ rfa_prof a b (norm z) <= &1`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(SPECL [`a:real`; `b:real`; `norm(z:real^N)`] RFA_PROF_VALUES) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!r. 1 <= r /\ r <= dimindex(:N)
        ==> rfa_prof a b (norm(z:real^N)) *
            abs(cmp_lhess (G2:real^N->real^N^N) (\w. rfa_prof a b (norm w)) z
                          (transp(S:real^N^N) ** basis r) (transp S ** basis r)) <=
            (C2 + C1 * (inv a + K * rho)) * E + C1 * Dg * L`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G2:real^N->real^N^N`; `z:real^N`; `S:real^N^N`]
           RFA_FRAME_ORTHO) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPECL [`r:num`; `r:num`]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    ABBREV_TAC `vr = transp(S:real^N^N) ** basis r` THEN
    MP_TAC(ISPECL [`a:real`; `b:real`; `U:real^N->bool`; `G1:real^N->real^N^N`;
                   `G2:real^N->real^N^N`; `z:real^N`; `vr:real^N`; `K:real`; `rho:real`;
                   `C1:real`; `C2:real`] RFA_CUT_LAP_TERM) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
    SUBGOAL_THEN `&0 <= vr dot ((G1:real^N->real^N^N) z ** vr)` ASSUME_TAC THENL
     [MATCH_MP_TAC LRG_METRIC_NONNEG THEN EXISTS_TAC `U:real^N->bool` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= C2 + C1 * (inv a + K * rho)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_ADD THEN ASM_SIMP_TAC[REAL_LE_MUL]; ALL_TAC] THEN
    SUBGOAL_THEN `(C2 + C1 * (inv a + K * rho)) * (vr dot ((G1:real^N->real^N^N) z ** vr)) <=
                  (C2 + C1 * (inv a + K * rho)) * E` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `E * (vr dot ((G2:real^N->real^N^N) z ** vr))` THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `C1 * Dg * norm(vr:real^N) pow 2 <= C1 * Dg * L` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `L * (vr dot ((G2:real^N->real^N^N) z ** vr))` THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `C1 * (rfa_prof a b (norm(z:real^N)) *
            norm(christoffel (G2:real^N->real^N^N) z vr vr - christoffel G1 z vr vr)) <=
      C1 * Dg * norm(vr:real^N) pow 2`
    ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `rfa_prof a b (norm(z:real^N)) *
      ((C2 + C1 * (inv a + K * rho)) * (vr dot ((G1:real^N->real^N^N) z ** vr))) <=
      (C2 + C1 * (inv a + K * rho)) * (vr dot (G1 z ** vr))`
    ASSUME_TAC THENL
     [GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC
     `rfa_prof a b (norm(z:real^N)) *
      ((C2 + C1 * (inv a + K * rho)) * (vr dot ((G1:real^N->real^N^N) z ** vr)) +
       C1 * norm(christoffel (G2:real^N->real^N^N) z vr vr - christoffel G1 z vr vr))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MAP_EVERY UNDISCH_TAC
     [`rfa_prof a b (norm(z:real^N)) *
       ((C2 + C1 * (inv a + K * rho)) * (vr dot ((G1:real^N->real^N^N) z ** vr))) <=
       (C2 + C1 * (inv a + K * rho)) * (vr dot (G1 z ** vr))`;
      `C1 * (rfa_prof a b (norm(z:real^N)) *
             norm(christoffel (G2:real^N->real^N^N) z vr vr - christoffel G1 z vr vr)) <=
       C1 * Dg * norm(vr:real^N) pow 2`;
      `C1 * Dg * norm(vr:real^N) pow 2 <= C1 * Dg * L`;
      `(C2 + C1 * (inv a + K * rho)) * (vr dot ((G1:real^N->real^N^N) z ** vr)) <=
       (C2 + C1 * (inv a + K * rho)) * E`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(1..dimindex(:N))
               (\r. rfa_prof a b (norm(z:real^N)) *
                    abs(cmp_lhess (G2:real^N->real^N^N) (\w. rfa_prof a b (norm w)) z
                         (transp(S:real^N^N) ** basis r) (transp S ** basis r)))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[SUM_LMUL] THEN
    MATCH_MP_TAC RFA_NEG_MUL_LE THEN ASM_REWRITE_TAC[SUM_ABS_NUMSEG];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(1..dimindex(:N))
               (\r. (C2 + C1 * (inv a + K * rho)) * E + C1 * Dg * L)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE_NUMSEG THEN ASM_SIMP_TAC[];
    REWRITE_TAC[SUM_CONST_NUMSEG; ARITH_RULE `(n + 1) - 1 = n`] THEN REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* Along a local Ricci flow at a point: the derivative of a                  *)
(* quadratic form, the two-sided metric equivalence under bounded Ricci      *)
(* curvature, and the Ricci bound from the norm of Rm.                       *)
(* ========================================================================= *)

let RFA_LQFORM_DERIV = prove
 (`!U a b (G:real->real^N->real^N^N) t y v.
     lricci_flow U a b G /\ a < t /\ t < b /\ y IN U
     ==> ((\s. v dot (G s y ** v)) has_real_derivative --(&2) * lricci (G t) y v v)
         (atreal t)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `metric_field U ((G:real->real^N->real^N^N) t)` ASSUME_TAC THENL
   [ASM_MESON_TAC[lricci_flow]; ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `(G:real->real^N->real^N^N) t`; `y:real^N`;
                 `v:real^N`; `v:real^N`] LRG_LRICCI_DOT_FORM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[RFA_QFORM_EXPAND] THEN
  REWRITE_TAC[GSYM SUM_LMUL] THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUM THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN BETA_TAC THEN
  REWRITE_TAC[GSYM SUM_LMUL] THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUM THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  X_GEN_TAC `j:num` THEN STRIP_TAC THEN BETA_TAC THEN
  ASM_SIMP_TAC[LAMBDA_BETA] THEN
  SUBGOAL_THEN
   `((\s. (G:real->real^N->real^N^N) s y$i$j) has_real_derivative
     --(&2) * lricci (G t) y (basis i) (basis j)) (atreal t)`
  MP_TAC THENL
   [UNDISCH_TAC `lricci_flow U a b (G:real->real^N->real^N^N)` THEN
    REWRITE_TAC[lricci_flow] THEN STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `(v:real^N)$j` o MATCH_MP HAS_REAL_DERIVATIVE_RMUL_ATREAL) THEN
  DISCH_THEN(MP_TAC o SPEC `(v:real^N)$i` o MATCH_MP HAS_REAL_DERIVATIVE_LMUL_ATREAL) THEN
  REWRITE_TAC[] THEN
  MATCH_MP_TAC(MESON[]
   `(x:real) = y ==> (f has_real_derivative x) net ==> (f has_real_derivative y) net`) THEN
  REAL_ARITH_TAC);;

let RFA_LMETRIC_EQUIV = prove
 (`!U a b (G:real->real^N->real^N^N) y sigma t Kr.
     lricci_flow U a b G /\ a < sigma /\ sigma <= t /\ t < b /\ y IN U /\ &0 <= Kr /\
     (!s v. sigma <= s /\ s <= t ==> abs(lricci (G s) y v v) <= Kr * (v dot (G s y ** v)))
     ==> !v. exp(--(&2 * Kr * (t - sigma))) * (v dot (G sigma y ** v)) <=
             v dot (G t y ** v) /\
             v dot (G t y ** v) <= exp(&2 * Kr * (t - sigma)) * (v dot (G sigma y ** v))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `v:real^N` THEN
  ASM_CASES_TAC `t:real = sigma` THENL
   [ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_MUL_RZERO; REAL_NEG_0; REAL_EXP_0; REAL_MUL_LID;
                    REAL_LE_REFL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\s. v dot ((G:real->real^N->real^N^N) s y ** v)`;
                 `\s. --(&2) * lricci ((G:real->real^N->real^N^N) s) y v v`;
                 `&2 * Kr`; `sigma:real`; `t:real`] RFA_GRONWALL_2SIDED) THEN
  REWRITE_TAC[REAL_MUL_ASSOC] THEN DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
    X_GEN_TAC `s:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
    MATCH_MP_TAC REAL_CONTINUOUS_ATREAL_WITHINREAL THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_IMP_CONTINUOUS_ATREAL THEN
    EXISTS_TAC `--(&2) * lricci ((G:real->real^N->real^N^N) s) y v v` THEN
    MATCH_MP_TAC RFA_LQFORM_DERIV THEN
    MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `a:real`; `b:real`] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    REPEAT STRIP_TAC THEN MATCH_MP_TAC RFA_LQFORM_DERIV THEN
    MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `a:real`; `b:real`] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_NEG; REAL_ABS_NUM] THEN
    REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    CONV_TAC(LAND_CONV REAL_RAT_REDUCE_CONV) THEN REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC]);;

let RFA_LRIC_BOUND = prove
 (`!U (G:real^N->real^N^N) y D v.
     metric_field U G /\ y IN U /\ &0 <= D /\ lrm_deriv_norm2 0 G y <= D
     ==> abs(lricci G y v v) <= (&(dimindex(:N)) * sqrt D) * (v dot (G y ** v))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`] LRG_FRAME) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `M:real^N^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!u. abs(lrm4 (G:real^N->real^N^N) y u) <=
        sqrt D * norm((M:real^N^N) ** u 1) * norm(M ** u 2) * norm(M ** u 3) *
        norm(M ** u 4)`
  ASSUME_TAC THENL
   [X_GEN_TAC `u:num->real^N` THEN
    MP_TAC(ISPECL [`4`; `U:real^N->bool`; `G:real^N->real^N^N`;
                   `lrm4 (G:real^N->real^N^N)`; `y:real^N`; `M:real^N^N`; `u:num->real^N`;
                   `D:real`] LRG_FRAME_BOUND_DELTA) THEN
    ASM_SIMP_TAC[PRODUCT_4; LRM4_TENSOR_FIELD] THEN DISCH_THEN MATCH_MP_TAC THEN
    UNDISCH_TAC `lrm_deriv_norm2 0 (G:real^N->real^N^N) y <= D` THEN
    REWRITE_TAC[lrm_deriv_norm2; lnabla_iter; ADD_CLAUSES];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `M:real^N^N`;
                 `sqrt D`] LRG_RICCI0_BOUND) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[SQRT_POS_LE]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`v:real^N`; `v:real^N`]) THEN
  SUBGOAL_THEN `(v:real^N) dot ((G:real^N->real^N^N) y ** v) =
                norm((M:real^N^N) ** v) * norm(M ** v)`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM REAL_POW_2; GSYM DOT_SQUARE_NORM] THEN
    ASM_REWRITE_TAC[GSYM MATRIX_VECTOR_MUL_ASSOC; DOT_MATRIX_TRANSP_RMUL];
    REAL_ARITH_TAC]);;

let RFA_NRIC_NORM_LE = prove
 (`!U (G:real^N->real^N^N) y.
     metric_field U G /\ y IN U
     ==> ltnorm2 3 G (lnabla 2 G (lric2 G)) y <=
         &(dimindex(:N)) * lrm_deriv_norm2 1 G y`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`]
         RFA_NABLA_RIC_CONTR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `ltnorm2 3 (G:real^N->real^N^N) (lnabla 2 G (lric2 G)) y =
    ltnorm2 3 G (ltcontr G (ltperm (swap(2,3)) (lnabla 4 G (lrm4 G)))) y`
  SUBST1_TAC THENL
   [REWRITE_TAC[RFA_LTNORM2_LTINNER] THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `ltinner 3 (G:real^N->real^N^N) (lnabla 2 G (lric2 G))
                  (ltcontr G (ltperm (swap(2,3)) (lnabla 4 G (lrm4 G)))) y` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC RFA_LTINNER_RLOCAL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `ltinner 3 (G:real^N->real^N^N)
                  (ltcontr G (ltperm (swap(2,3)) (lnabla 4 G (lrm4 G))))
                  (lnabla 2 G (lric2 G)) y` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC RFA_LTINNER_SYM THEN EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC RFA_LTINNER_RLOCAL THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `swap(2,3) permutes 1..4 + 1` ASSUME_TAC THENL
   [MATCH_MP_TAC PERMUTES_SWAP THEN REWRITE_TAC[IN_NUMSEG] THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `ltensor_field (4 + 1) U (lnabla 4 (G:real^N->real^N^N) (lrm4 G)) /\
    (!u. smooth_map_on U (\x. lift(lnabla 4 G (lrm4 G) x u)))`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC LNABLA_TENSOR_FIELD THEN ASM_SIMP_TAC[LRM4_TENSOR_FIELD]; ALL_TAC] THEN
  MP_TAC(ISPECL [`3`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `ltperm (swap(2,3)) (lnabla 4 (G:real^N->real^N^N) (lrm4 G))`;
                 `y:real^N`] RFA_LTNORM2_LTCONTR) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[ARITH_RULE `3 + 2 = 4 + 1`] THEN
    MATCH_MP_TAC RFA_LTPERM_FIELD THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`4 + 1`; `swap(2,3)`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `lnabla 4 (G:real^N->real^N^N) (lrm4 G)`; `y:real^N`]
         RFA_LTNORM2_LTPERM) THEN
  ASM_REWRITE_TAC[ARITH_RULE `3 + 2 = 4 + 1`] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[lrm_deriv_norm2; RFA_LNABLA_ITER_1; ARITH_RULE `4 + 1 = 4 + 1`]);;

(* The time derivative of the Christoffel symbols is bounded by |nabla Rm|. *)

let RFA_FRAME_NORM_BOUND = prove
 (`!(Gm:real^N^N) (M:real^N^N) Lam.
     Gm = transp M ** M /\ &0 <= Lam /\
     (!x. x dot (Gm ** x) <= Lam * norm x pow 2)
     ==> !x. norm(M ** x) <= sqrt Lam * norm x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `x:real^N` THEN
  MATCH_MP_TAC REAL_POW_LE2_REV THEN EXISTS_TAC `2` THEN
  REWRITE_TAC[ARITH_EQ] THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[SQRT_POS_LE; NORM_POS_LE];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_POW_MUL] THEN ASM_SIMP_TAC[SQRT_POW_2] THEN
  SUBGOAL_THEN `norm((M:real^N^N) ** x) pow 2 = x dot ((Gm:real^N^N) ** x)`
  SUBST1_TAC THENL
   [ASM_REWRITE_TAC[NORM_POW_2; GSYM MATRIX_VECTOR_MUL_ASSOC;
                    DOT_MATRIX_TRANSP_RMUL];
    ASM_REWRITE_TAC[]]);;

let RFA_PROD3_FRAME_LE = prove
 (`!(M:real^N^N) s Lam p q r.
     &0 <= s /\ &0 <= Lam /\
     norm(M ** p) <= sqrt Lam * norm p /\ norm(M ** q) <= sqrt Lam * norm q /\
     norm(M ** r) <= sqrt Lam * norm r
     ==> s * norm(M ** p) * norm(M ** q) * norm(M ** r) <=
         s * (Lam * sqrt Lam) * norm p * norm q * norm r`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `s * (Lam * sqrt Lam) * norm(p:real^N) * norm(q:real^N) * norm(r:real^N) =
    s * (sqrt Lam * norm p) * (sqrt Lam * norm q) * (sqrt Lam * norm r)`
  SUBST1_TAC THENL
   [FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o LAND_CONV o
      LAND_CONV) [GSYM(MATCH_MP SQRT_POW_2 th)]) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[NORM_POS_LE] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[NORM_POS_LE]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[NORM_POS_LE]);;

let RFA_METRIC_COMPONENT_INV = prove
 (`!(Gm:real^N^N) w L C.
     &0 <= L /\ (!x. norm x pow 2 <= L * (x dot (Gm ** x))) /\
     (!k. 1 <= k /\ k <= dimindex(:N) ==> abs((Gm ** w)$k) <= C)
     ==> norm w <= L * &(dimindex(:N)) * C`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `norm((Gm:real^N^N) ** w) <= &(dimindex(:N)) * C` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum(1..dimindex(:N)) (\i. abs(((Gm:real^N^N) ** w)$i))` THEN
    REWRITE_TAC[NORM_LE_L1] THEN
    MP_TAC(ISPECL [`1..dimindex(:N)`; `\i. abs(((Gm:real^N^N) ** w)$i)`; `C:real`]
           SUM_BOUND) THEN
    REWRITE_TAC[FINITE_NUMSEG; CARD_NUMSEG_1; IN_NUMSEG] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= C` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `abs(((Gm:real^N^N) ** w)$1)` THEN
    REWRITE_TAC[REAL_ABS_POS] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[LE_REFL; DIMINDEX_GE_1];
    ALL_TAC] THEN
  ASM_CASES_TAC `w:real^N = vec 0` THENL
   [ASM_REWRITE_TAC[NORM_0] THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_REWRITE_TAC[REAL_POS];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < norm(w:real^N)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `norm(w:real^N) * norm w <= norm w * (L * norm((Gm:real^N^N) ** w))`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `L * ((w:real^N) dot ((Gm:real^N^N) ** w))` THEN CONJ_TAC THENL
     [REWRITE_TAC[GSYM REAL_POW_2] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `L * (norm(w:real^N) * norm((Gm:real^N^N) ** w))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[NORM_CAUCHY_SCHWARZ];
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_LMUL_EQ] THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `L * norm((Gm:real^N^N) ** w)` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]);;

let RFA_DGAMMA_BOUND = prove
 (`!U a b (G:real->real^N->real^N^N) t y u v L Lam.
     lricci_flow U a b G /\ a < t /\ t < b /\ y IN U /\ &0 <= L /\ &0 <= Lam /\
     (!x. norm x pow 2 <= L * (x dot (G t y ** x))) /\
     (!x. x dot (G t y ** x) <= Lam * norm x pow 2)
     ==> norm(ldgamma G t y u v) <=
         &3 * &(dimindex(:N)) * L * (Lam * sqrt Lam) *
         sqrt(&(dimindex(:N)) * lrm_deriv_norm2 1 (G t) y) * norm u * norm v`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `metric_field U ((G:real->real^N->real^N^N) t)` ASSUME_TAC THENL
   [ASM_MESON_TAC[lricci_flow]; ALL_TAC] THEN
  ABBREV_TAC `R = &(dimindex(:N)) * lrm_deriv_norm2 1 ((G:real->real^N->real^N^N) t) y` THEN
  SUBGOAL_THEN `&0 <= R` ASSUME_TAC THENL
   [EXPAND_TAC "R" THEN MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC RFA_RMD_POS THEN EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `a:real`; `b:real`; `G:real->real^N->real^N^N`;
                 `t:real`; `y:real^N`; `u:real^N`; `v:real^N`] LCHRISTOFFEL_EVOLUTION) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^N` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "Gw"))) THEN
  SUBGOAL_THEN `ldgamma (G:real->real^N->real^N^N) t y u v = w` SUBST1_TAC THENL
   [MATCH_MP_TAC VECTOR_DERIVATIVE_UNIQUE_AT THEN
    EXISTS_TAC `\s. christoffel ((G:real->real^N->real^N^N) (drop s)) y u v` THEN
    EXISTS_TAC `lift t` THEN ASM_REWRITE_TAC[ldgamma] THEN
    MATCH_MP_TAC LRG_FLOW_GAMMA_VDERIV THEN
    MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `a:real`; `b:real`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `(G:real->real^N->real^N^N) t`; `y:real^N`] LRG_FRAME) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `M:real^N^N` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "GM"))) THEN
  SUBGOAL_THEN `!x:real^N. norm((M:real^N^N) ** x) <= sqrt Lam * norm x` (LABEL_TAC "Mb") THENL
   [MATCH_MP_TAC RFA_FRAME_NORM_BOUND THEN
    EXISTS_TAC `(G:real->real^N->real^N^N) t y` THEN
    REPEAT CONJ_TAC THEN FIRST_ASSUM MATCH_ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ltensor_field 3 U (lnabla 2 ((G:real->real^N->real^N^N) t) (lric2 (G t)))`
  ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `3 = 2 + 1`] THEN
    MP_TAC(ISPECL [`2`; `U:real^N->bool`; `(G:real->real^N->real^N^N) t`;
                   `lric2 ((G:real->real^N->real^N^N) t)`] LNABLA_TENSOR_FIELD) THEN
    ASM_SIMP_TAC[LRG_LRIC2_FIELD];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!p q r. abs(lnabla 2 ((G:real->real^N->real^N^N) t) (lric2 (G t)) y
                  (\m. if m = 1 then p else if m = 2 then q else r)) <=
            sqrt R * norm((M:real^N^N) ** p) * norm(M ** q) * norm(M ** r)`
  (LABEL_TAC "N3") THENL
   [REPEAT GEN_TAC THEN
    MP_TAC(ISPECL [`3`; `U:real^N->bool`; `(G:real->real^N->real^N^N) t`;
                   `lnabla 2 ((G:real->real^N->real^N^N) t) (lric2 (G t))`; `y:real^N`;
                   `M:real^N^N`; `\m:num. if m = 1 then p else if m = 2 then q else r:real^N`;
                   `R:real`] LRG_FRAME_BOUND_DELTA) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN EXPAND_TAC "R" THEN
      MATCH_MP_TAC RFA_NRIC_NORM_LE THEN EXISTS_TAC `U:real^N->bool` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[PRODUCT_3] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN
    DISCH_THEN ACCEPT_TAC;
    ALL_TAC] THEN
  REMOVE_THEN "GM" (K ALL_TAC) THEN
  SUBGOAL_THEN
   `!p q r. abs(lnabla 2 ((G:real->real^N->real^N^N) t) (lric2 (G t)) y
                  (\m. if m = 1 then p else if m = 2 then q else r)) <=
            sqrt R * (Lam * sqrt Lam) * norm p * norm q * norm r`
  (LABEL_TAC "T3") THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sqrt R * norm((M:real^N^N) ** p) * norm(M ** q) * norm(M ** r)` THEN
    CONJ_TAC THENL [USE_THEN "N3" (fun th -> REWRITE_TAC[th]); ALL_TAC] THEN
    MATCH_MP_TAC RFA_PROD3_FRAME_LE THEN ASM_SIMP_TAC[SQRT_POS_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!k. 1 <= k /\ k <= dimindex(:N)
        ==> abs(((G:real->real^N->real^N^N) t y ** w)$k) <=
            &3 * (sqrt R * (Lam * sqrt Lam) * norm(u:real^N) * norm(v:real^N))`
  ASSUME_TAC THENL
   [X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    USE_THEN "Gw" (fun th -> REWRITE_TAC[MATCH_MP th
      (ASSUME `1 <= k /\ k <= dimindex(:N)`)]) THEN
    SUBGOAL_THEN `norm(basis k:real^N) = &1` ASSUME_TAC THENL
     [ASM_SIMP_TAC[NORM_BASIS]; ALL_TAC] THEN
    USE_THEN "T3" (MP_TAC o SPECL [`v:real^N`; `basis k:real^N`; `u:real^N`]) THEN
    USE_THEN "T3" (MP_TAC o SPECL [`u:real^N`; `basis k:real^N`; `v:real^N`]) THEN
    USE_THEN "T3" (MP_TAC o SPECL [`u:real^N`; `v:real^N`; `basis k:real^N`]) THEN
    REWRITE_TAC[ASSUME `norm(basis k:real^N) = &1`; REAL_MUL_LID; REAL_MUL_RID] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(G:real->real^N->real^N^N) t y`; `w:real^N`; `L:real`;
                 `&3 * (sqrt R * (Lam * sqrt Lam) * norm(u:real^N) * norm(v:real^N))`]
         RFA_METRIC_COMPONENT_INV) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM MATCH_ACCEPT_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `a = b ==> x <= a ==> x <= b`) THEN REAL_ARITH_TAC);;

(* ========================================================================= *)
(* Change of the Christoffel symbols along a local Ricci flow                *)
(* at a point, from a bound on abs(nabla Rm) of the form                    *)
(* A / sqrt(s - s0) + B (comparison with 2 A sqrt(s - s0) + B (s - s0)).   *)
(* ========================================================================= *)

let RFA_LIFT_DOT_VDERIV = prove
 (`!(f:real^1->real^N) f' (e:real^N) x.
     (f has_vector_derivative f') (at x)
     ==> ((\z. lift(e dot f z)) has_vector_derivative lift(e dot f')) (at x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[has_vector_derivative] THEN
  DISCH_THEN(MP_TAC o INST [`e:real^N`,`v:real^N`] o
             MATCH_MP HAS_DERIVATIVE_LIFT_DOT) THEN
  REWRITE_TAC[DOT_RMUL; LIFT_CMUL]);;

let RFA_VEC_DERIV_COMPARE = prove
 (`!(f:real^1->real^N) (f':real->real^N) (g:real->real) g' s0 t.
     s0 < t /\
     f continuous_on interval[lift s0,lift t] /\
     g real_continuous_on real_interval[s0,t] /\
     (!s. s0 < s /\ s < t ==> (f has_vector_derivative f' s) (at (lift s))) /\
     (!s. s0 < s /\ s < t ==> (g has_real_derivative g' s) (atreal s)) /\
     (!s. s0 < s /\ s < t ==> norm(f' s) <= g' s)
     ==> norm(f(lift t) - f(lift s0)) <= g t - g s0`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(g:real->real) s0 <= g t` ASSUME_TAC THENL
   [MATCH_MP_TAC RFA_MVT_MONO THEN EXISTS_TAC `g':real->real` THEN
    ASM_SIMP_TAC[] THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `norm((f':real->real^N) s)` THEN
    ASM_SIMP_TAC[NORM_POS_LE];
    ALL_TAC] THEN
  ABBREV_TAC `e:real^N = (f:real^1->real^N)(lift t) - f(lift s0)` THEN
  MP_TAC(ISPECL [`\s. norm(e:real^N) * (g:real->real) s - e dot (f:real^1->real^N)(lift s)`;
                 `\s. norm(e:real^N) * (g':real->real) s - e dot (f':real->real^N) s`;
                 `s0:real`; `t:real`] RFA_MVT_MONO) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_CONTINUOUS_ON_SUB THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_CONTINUOUS_ON_LMUL THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[REAL_CONTINUOUS_ON; IMAGE_LIFT_REAL_INTERVAL] THEN
        REWRITE_TAC[o_DEF; LIFT_DROP] THEN
        MATCH_MP_TAC CONTINUOUS_ON_LIFT_DOT2 THEN
        ASM_REWRITE_TAC[CONTINUOUS_ON_CONST; ETA_AX]];
      X_GEN_TAC `s:real` THEN STRIP_TAC THEN BETA_TAC THEN
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUB THEN CONJ_TAC THENL
       [MATCH_MP_TAC HAS_REAL_DERIVATIVE_LMUL_ATREAL THEN ASM_SIMP_TAC[];
        REWRITE_TAC[HAS_REAL_VECTOR_DERIVATIVE_AT; o_DEF; LIFT_DROP] THEN
        MATCH_MP_TAC RFA_LIFT_DOT_VDERIV THEN ASM_SIMP_TAC[]];
      X_GEN_TAC `s:real` THEN STRIP_TAC THEN BETA_TAC THEN
      REWRITE_TAC[REAL_SUB_LE] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `norm(e:real^N) * norm((f':real->real^N) s)` THEN
      REWRITE_TAC[NORM_CAUCHY_SCHWARZ] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_SIMP_TAC[NORM_POS_LE]];
    ALL_TAC] THEN
  BETA_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `(e:real^N) dot e <= norm e * ((g:real->real) t - g s0)` MP_TAC THENL
   [FIRST_X_ASSUM MP_TAC THEN MATCH_MP_TAC(REAL_ARITH
     `ed = et - es ==> ne * gs - es <= ne * gt - et ==> ed <= ne * (gt - gs)`) THEN
    REWRITE_TAC[GSYM DOT_RSUB] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM NORM_POW_2] THEN
  ASM_CASES_TAC `e:real^N = vec 0` THENL
   [ASM_REWRITE_TAC[NORM_0] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < norm(e:real^N)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  REWRITE_TAC[REAL_POW_2] THEN ASM_SIMP_TAC[REAL_LE_LMUL_EQ]);;

let RFA_SQRT_GROWTH = prove
 (`!A B s0 t1.
     (\s. &2 * A * sqrt(s - s0) + B * (s - s0)) real_continuous_on
       real_interval[s0,t1] /\
     (!s. s0 < s
          ==> ((\s. &2 * A * sqrt(s - s0) + B * (s - s0)) has_real_derivative
               A * inv(sqrt(s - s0)) + B) (atreal s))`,
  REPEAT GEN_TAC THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
    X_GEN_TAC `x:real` THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_CONTINUOUS_ATREAL_WITHINREAL THEN
    MATCH_MP_TAC REAL_CONTINUOUS_ADD THEN CONJ_TAC THEN
    REPEAT(MATCH_MP_TAC REAL_CONTINUOUS_LMUL) THEN
    TRY(MATCH_MP_TAC REAL_CONTINUOUS_ATREAL_SQRT_COMPOSE) THEN
    MATCH_MP_TAC REAL_CONTINUOUS_SUB THEN
    REWRITE_TAC[REAL_CONTINUOUS_CONST; REAL_CONTINUOUS_AT_ID];
    X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    MP_TAC(DISCH_ALL(REAL_DIFF_CONV
      `((\s. &2 * A * sqrt(s - s0) + B * (s - s0)) has_real_derivative k)
       (atreal s)`)) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[REAL_INV_MUL] THEN REAL_ARITH_TAC]);;

let RFA_GAMMA_VDERIV = prove
 (`!U a b (G:real->real^N->real^N^N) t y u v.
     lricci_flow U a b G /\ a < t /\ t < b /\ y IN U
     ==> ((\s. christoffel (G (drop s)) y u v) has_vector_derivative
          ldgamma G t y u v) (at (lift t))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ldgamma] THEN
  MATCH_MP_TAC LRG_FLOW_GAMMA_VDERIV THEN
  MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `a:real`; `b:real`] THEN
  ASM_REWRITE_TAC[]);;

let RFA_GAMMA_CONT = prove
 (`!U a b (G:real->real^N->real^N^N) s0 t1 y u v.
     lricci_flow U a b G /\ a < s0 /\ t1 < b /\ y IN U
     ==> (\s. christoffel (G (drop s)) y u v) continuous_on
         interval[lift s0,lift t1]`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN
  REWRITE_TAC[FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP] THEN
  X_GEN_TAC `s:real` THEN STRIP_TAC THEN
  MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN
  REWRITE_TAC[differentiable] THEN
  EXISTS_TAC `\h. drop h % ldgamma (G:real->real^N->real^N^N) s y u v` THEN
  REWRITE_TAC[GSYM has_vector_derivative] THEN
  MATCH_MP_TAC RFA_GAMMA_VDERIV THEN
  MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `a:real`; `b:real`] THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let RFA_GAMMA_CHANGE = prove
 (`!U a b (G:real->real^N->real^N^N) s0 t1 y v Lm A B.
     lricci_flow U a b G /\ a < s0 /\ s0 < t1 /\ t1 < b /\ y IN U /\
     &0 <= Lm /\
     (!s x. s0 < s /\ s < t1
            ==> norm x pow 2 <= Lm * (x dot (G s y ** x)) /\
                x dot (G s y ** x) <= Lm * norm x pow 2) /\
     (!s. s0 < s /\ s < t1
          ==> sqrt(&(dimindex(:N)) * lrm_deriv_norm2 1 (G s) y) <=
              A * inv(sqrt(s - s0)) + B)
     ==> norm(christoffel (G t1) y v v - christoffel (G s0) y v v) <=
         ((&3 * &(dimindex(:N)) * Lm * (Lm * sqrt Lm)) * norm v pow 2) *
         (&2 * A * sqrt(t1 - s0) + B * (t1 - s0))`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `Cg = (&3 * &(dimindex(:N)) * Lm * (Lm * sqrt Lm)) * norm(v:real^N) pow 2` THEN
  SUBGOAL_THEN `&0 <= Cg` ASSUME_TAC THENL
   [EXPAND_TAC "Cg" THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_SIMP_TAC[REAL_POS; SQRT_POS_LE; REAL_LE_POW_2];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`A:real`; `B:real`; `s0:real`; `t1:real`] RFA_SQRT_GROWTH) THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`\s. christoffel ((G:real->real^N->real^N^N) (drop s)) y v v`;
                 `\s. ldgamma (G:real->real^N->real^N^N) s y v v`;
                 `\s. Cg * (&2 * A * sqrt(s - s0) + B * (s - s0))`;
                 `\s. Cg * (A * inv(sqrt(s - s0)) + B)`; `s0:real`; `t1:real`]
         RFA_VEC_DERIV_COMPARE) THEN
  BETA_TAC THEN REWRITE_TAC[LIFT_DROP] THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      MATCH_MP_TAC RFA_GAMMA_CONT THEN
      MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `a:real`; `b:real`] THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_CONTINUOUS_ON_LMUL THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `s:real` THEN STRIP_TAC THEN
      MATCH_MP_TAC RFA_GAMMA_VDERIV THEN
      MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `a:real`; `b:real`] THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      X_GEN_TAC `s:real` THEN STRIP_TAC THEN
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_LMUL_ATREAL THEN ASM_SIMP_TAC[];
      X_GEN_TAC `s:real` THEN STRIP_TAC THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `&3 * &(dimindex(:N)) * Lm * (Lm * sqrt Lm) *
                  sqrt(&(dimindex(:N)) *
                       lrm_deriv_norm2 1 ((G:real->real^N->real^N^N) s) y) *
                  norm(v:real^N) * norm v` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC RFA_DGAMMA_BOUND THEN
        MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `a:real`; `b:real`] THEN
        ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN
       `&3 * &(dimindex(:N)) * Lm * (Lm * sqrt Lm) *
        sqrt(&(dimindex(:N)) * lrm_deriv_norm2 1 ((G:real->real^N->real^N^N) s) y) *
        norm(v:real^N) * norm v =
        Cg * sqrt(&(dimindex(:N)) * lrm_deriv_norm2 1 (G s) y)`
      SUBST1_TAC THENL
       [EXPAND_TAC "Cg" THEN REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[]]];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_SUB_REFL; SQRT_0; REAL_MUL_RZERO; REAL_ADD_RID;
              REAL_SUB_RZERO]);;

