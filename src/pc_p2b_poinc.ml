(* ========================================================================= *)
(* pc_p2b_poinc (Part 2B, for SPLIT_ROUND): the Poincare lemma on open       *)
(* convex subsets of real^N.  Main theorem:                                  *)
(*   P2BPC_POINCARE_CONVEX: a smooth covector field w on an open convex C   *)
(*   whose Jacobian is symmetric has a smooth primitive h : real^N->real^1  *)
(*   with derivative v |-> lift(w x dot v) at every x of C.                 *)
(* Proof: h(x) = integral over [0,1] of lift(w(p + t (x - p)) dot (x - p)); *)
(* differentiation under the integral sign (NS_PARAM_INTEGRAL_SMOOTH of     *)
(* pc_pde_torus), the symmetric Jacobian turns the x-derivative of the      *)
(* integrand into the t-derivative of t w_i(p + t (x - p)), and the         *)
(* fundamental theorem of calculus.                                          *)
(* Two charts (coordinate form): P2BPC_TWO_CHART_PRIMITIVE, compatible       *)
(* closed fields on two convex sets with a connected overlap have primitives *)
(* that agree through the transition map (for the exactness of g(X,.) on     *)
(* S^2 x I).                                                                 *)
(* Pullbacks: p2bpc_pull tau w (components w(tau y) . Dtau(y) e_j) is smooth *)
(* and closed when w is (P2BPC_PULL_SMOOTH, P2BPC_PULL_CLOSED; the second    *)
(* derivatives of tau commute by SCHWARZ_C2), with                           *)
(* p2bpc_pull tau w y . v = w(tau y) . Dtau(y) v (P2BPC_PULL_DOT).           *)
(* Shells: P2BPC_SHELL_EXACT, a closed smooth covector field on a spherical  *)
(* shell annulus r1 r2 of real^3 (0 < r1 < r2) has a smooth primitive (the   *)
(* case S^2 x I): slab charts radius exp(z$3) times inverse stereographic    *)
(* projection, the punctured slab connected, the transition inversion of the *)
(* first two coordinates, gluing through the explicit inverses off the       *)
(* closed positive and negative z-rays.                                      *)
(* ========================================================================= *)

needs "src/pc_pde_torus.ml";;

prioritize_real();;
type_invention_error := true;;

(* P2BPC.P1 The segment map of the Poincare lemma: membership, smoothness, *)
(* the open parameter domain and the smooth integrand.                     *)

let P2BPC_SEG_IN = prove
 (`!C (p:real^N) x t.
     convex C /\ p IN C /\ x IN C /\ t IN interval[vec 0,vec 1]
     ==> p + drop t % (x - p) IN C`,
  REWRITE_TAC[IN_INTERVAL_1; DROP_VEC] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `p + drop t % (x - p) = (&1 - drop t) % p + drop t % (x:real^N)`
  SUBST1_TAC THENL [VECTOR_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC IN_CONVEX_SET THEN ASM_REWRITE_TAC[]);;

let P2BPC_SMOOTH_LINEAR = prove
 (`!s (g:real^M->real^N). open s /\ linear g ==> smooth_map_on s g`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^M->bool`; `\x:real^M. x`; `g:real^M->real^N`]
                SMOOTH_MAP_ON_LINEAR_O) THEN
  ASM_REWRITE_TAC[SMOOTH_MAP_ON_ID; o_DEF; ETA_AX]);;

let P2BPC_PHI_SMOOTH = prove
 (`!(p:real^N) s.
     open s ==> smooth_map_on s (\z:real^(N,1)finite_sum. p + drop(sndcart z) % (fstcart z - p))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN
  ASM_REWRITE_TAC[SMOOTH_MAP_ON_CONST] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_MUL_DROP_OPEN THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`s:real^(N,1)finite_sum->bool`;
                   `sndcart:real^(N,1)finite_sum->real^1`] P2BPC_SMOOTH_LINEAR) THEN
    ASM_REWRITE_TAC[LINEAR_SNDCART; ETA_AX];
    MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN ASM_REWRITE_TAC[SMOOTH_MAP_ON_CONST] THEN
    MP_TAC(ISPECL [`s:real^(N,1)finite_sum->bool`;
                   `fstcart:real^(N,1)finite_sum->real^N`] P2BPC_SMOOTH_LINEAR) THEN
    ASM_REWRITE_TAC[LINEAR_FSTCART; ETA_AX]]);;

let P2BPC_W_OPEN = prove
 (`!C (p:real^N).
     open C
     ==> open {z:real^(N,1)finite_sum | p + drop(sndcart z) % (fstcart z - p) IN C}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE_UNIV THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`p:real^N`; `(:real^(N,1)finite_sum)`] P2BPC_PHI_SMOOTH) THEN
  REWRITE_TAC[OPEN_UNIV] THEN
  DISCH_THEN(MP_TAC o MATCH_MP SMOOTH_MAP_ON_CONTINUOUS_ON) THEN
  SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_AT; OPEN_UNIV; IN_UNIV]);;

let P2BPC_G_SMOOTH = prove
 (`!C (p:real^N) (w:real^N->real^N).
     open C /\ smooth_map_on C w
     ==> smooth_map_on {z:real^(N,1)finite_sum | p + drop(sndcart z) % (fstcart z - p) IN C}
           (\z. lift(w(p + drop(sndcart z) % (fstcart z - p)) dot (fstcart z - p)))`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `W = {z:real^(N,1)finite_sum | p + drop(sndcart z) % (fstcart z - p) IN C}` THEN
  SUBGOAL_THEN `open (W:real^(N,1)finite_sum->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "W" THEN MATCH_MP_TAC P2BPC_W_OPEN THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`W:real^(N,1)finite_sum->bool`;
                 `\z:real^(N,1)finite_sum. (w:real^N->real^N)(p + drop(sndcart z) % (fstcart z - p))`;
                 `\z:real^(N,1)finite_sum. fstcart z - (p:real^N)`]
                SMOOTH_MAP_ON_DOT_OPEN) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`W:real^(N,1)finite_sum->bool`; `C:real^N->bool`;
                   `\z:real^(N,1)finite_sum. p + drop(sndcart z) % (fstcart z - (p:real^N))`;
                   `w:real^N->real^N`] SMOOTH_MAP_ON_COMPOSE_OPEN) THEN
    REWRITE_TAC[o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [EXPAND_TAC "W" THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM];
      MATCH_MP_TAC P2BPC_PHI_SMOOTH THEN ASM_REWRITE_TAC[]];
    MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN ASM_REWRITE_TAC[SMOOTH_MAP_ON_CONST] THEN
    MP_TAC(ISPECL [`W:real^(N,1)finite_sum->bool`;
                   `fstcart:real^(N,1)finite_sum->real^N`] P2BPC_SMOOTH_LINEAR) THEN
    ASM_REWRITE_TAC[LINEAR_FSTCART; ETA_AX]]);;

(* P2BPC.P2 The x-derivative of the integrand and the t-derivative of the  *)
(* primitive candidate t w(p + t (x - p)).                                  *)

let P2BPC_HAS_DERIVATIVE_EQ_DERIV = prove
 (`!(f:real^M->real^N) f' f'' net.
     f' = f'' ==> (f has_derivative f') net ==> (f has_derivative f'') net`,
  MESON_TAC[]);;

let P2BPC_AFFINE_DERIV = prove
 (`!(p:real^N) s x0.
     ((\x. p + s % (x - p)) has_derivative (\v. s % v)) (at x0)`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `(\v:real^N. s % v) = (\v. vec 0 + s % (v - vec 0))` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC HAS_DERIVATIVE_ADD THEN REWRITE_TAC[HAS_DERIVATIVE_CONST] THEN
  MATCH_MP_TAC HAS_DERIVATIVE_CMUL THEN MATCH_MP_TAC HAS_DERIVATIVE_SUB THEN
  REWRITE_TAC[HAS_DERIVATIVE_ID; HAS_DERIVATIVE_CONST]);;

let P2BPC_INTEGRAND_DERIV = prove
 (`!(w:real^N->real^N) p x0 s.
     w differentiable at (p + s % (x0 - p))
     ==> ((\x. lift(w(p + s % (x - p)) dot (x - p))) has_derivative
          (\v. lift(w(p + s % (x0 - p)) dot v +
                    s * (frechet_derivative w (at (p + s % (x0 - p))) v dot (x0 - p)))))
         (at x0)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `y0:real^N = p + s % (x0 - p)` THEN
  ABBREV_TAC `D = frechet_derivative (w:real^N->real^N) (at y0)` THEN
  SUBGOAL_THEN `linear (D:real^N->real^N)` ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `((\x. (w:real^N->real^N)(p + s % (x - p))) has_derivative (\v. D(s % v))) (at x0)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\x:real^N. p + s % (x - p)`; `w:real^N->real^N`;
                   `\v:real^N. s % v`; `D:real^N->real^N`; `x0:real^N`] DIFF_CHAIN_AT) THEN
    REWRITE_TAC[P2BPC_AFFINE_DERIV; o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "D" THEN
    ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS];
    ALL_TAC] THEN
  SUBGOAL_THEN `((\x:real^N. x - p) has_derivative (\v. v - vec 0)) (at x0)` ASSUME_TAC THENL
   [MATCH_MP_TAC HAS_DERIVATIVE_SUB THEN REWRITE_TAC[HAS_DERIVATIVE_ID; HAS_DERIVATIVE_CONST];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\u v:real^N. lift(u dot v)`; `\x. (w:real^N->real^N)(p + s % (x - p))`;
                 `\x:real^N. x - p`; `\v. (D:real^N->real^N)(s % v)`; `\v:real^N. v - vec 0`;
                 `x0:real^N`] HAS_DERIVATIVE_BILINEAR_AT) THEN
  ASM_REWRITE_TAC[BILINEAR_DOT] THEN
  MATCH_MP_TAC P2BPC_HAS_DERIVATIVE_EQ_DERIV THEN
  REWRITE_TAC[FUN_EQ_THM; VECTOR_SUB_RZERO] THEN X_GEN_TAC `v:real^N` THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LINEAR_CMUL th]) THEN
  REWRITE_TAC[LIFT_ADD; DOT_LMUL; LIFT_CMUL]);;

(* The scalar t w_i(p + t (x - p)) on [0,1]. *)

let P2BPC_FTC_DERIV = prove
 (`!(w:real^N->real^N) p x i t0.
     w differentiable at (p + drop t0 % (x - p))
     ==> ((\t. lift(drop t * (w(p + drop t % (x - p)))$i)) has_vector_derivative
          lift((w(p + drop t0 % (x - p)))$i +
               drop t0 * (frechet_derivative w (at (p + drop t0 % (x - p))) (x - p))$i))
         (at t0)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `y0:real^N = p + drop t0 % (x - p)` THEN
  ABBREV_TAC `D = frechet_derivative (w:real^N->real^N) (at y0)` THEN
  SUBGOAL_THEN `linear (D:real^N->real^N)` ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `((\t:real^1. (p:real^N) + drop t % (x - p)) has_derivative
                 (\h. drop h % (x - p))) (at t0)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `(\h:real^1. drop h % (x - p:real^N)) = (\h. vec 0 + drop h % (x - p))`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; VECTOR_ADD_LID]; ALL_TAC] THEN
    MATCH_MP_TAC HAS_DERIVATIVE_ADD THEN REWRITE_TAC[HAS_DERIVATIVE_CONST] THEN
    MATCH_MP_TAC HAS_DERIVATIVE_VMUL_DROP THEN REWRITE_TAC[HAS_DERIVATIVE_ID];
    ALL_TAC] THEN
  SUBGOAL_THEN `((\t:real^1. (w:real^N->real^N)(p + drop t % (x - p))) has_derivative
                 (\h. D(drop h % (x - p)))) (at t0)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\t:real^1. p + drop t % (x - p:real^N)`; `w:real^N->real^N`;
                   `\h:real^1. drop h % (x - p:real^N)`; `D:real^N->real^N`; `t0:real^1`]
                  DIFF_CHAIN_AT) THEN
    ASM_REWRITE_TAC[o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN
    EXPAND_TAC "D" THEN ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS];
    ALL_TAC] THEN
  SUBGOAL_THEN `((\t:real^1. lift((w:real^N->real^N)(p + drop t % (x - p))$i)) has_derivative
                 (\h. lift(((D:real^N->real^N)(drop h % (x - p)))$i))) (at t0)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\t:real^1. (w:real^N->real^N)(p + drop t % (x - p))`;
                   `\y:real^N. lift(y$i)`;
                   `\h:real^1. (D:real^N->real^N)(drop h % (x - p))`;
                   `\y:real^N. lift(y$i)`; `t0:real^1`] DIFF_CHAIN_AT) THEN
    ASM_REWRITE_TAC[o_DEF; HAS_DERIVATIVE_LIFT_COMPONENT];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`drop`; `drop`;
                 `\t:real^1. lift((w:real^N->real^N)(p + drop t % (x - p))$i)`;
                 `\h:real^1. lift(((D:real^N->real^N)(drop h % (x - p)))$i)`; `t0:real^1`]
                HAS_DERIVATIVE_MUL_AT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(lift o drop) = (\x:real^1. x)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_DROP]; REWRITE_TAC[HAS_DERIVATIVE_ID]];
    ALL_TAC] THEN
  REWRITE_TAC[has_vector_derivative; GSYM LIFT_CMUL] THEN
  MATCH_MP_TAC P2BPC_HAS_DERIVATIVE_EQ_DERIV THEN
  REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `h:real^1` THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LINEAR_CMUL th]) THEN
  ASM_REWRITE_TAC[VECTOR_MUL_COMPONENT; LIFT_ADD; LIFT_CMUL] THEN VECTOR_ARITH_TAC);;

(* P2BPC.P3 Symmetric Jacobians and the partial derivatives of the         *)
(* candidate primitive h(x) = int_0^1 w(p + t (x - p)) . (x - p) dt.        *)

let P2BPC_SYMM_DOT = prove
 (`!(D:real^N->real^N) v i.
     linear D /\
     (!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
            ==> (D(basis i))$j = (D(basis j))$i) /\
     1 <= i /\ i <= dimindex(:N)
     ==> D(basis i) dot v = (D v)$i`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(D:real^N->real^N) v =
                vsum(1..dimindex(:N)) (\j. (v:real^N)$j % D(basis j))` SUBST1_TAC THENL
   [GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM BASIS_EXPANSION] THEN
    ASM_SIMP_TAC[LINEAR_VSUM; FINITE_NUMSEG; o_DEF] THEN
    MATCH_MP_TAC VSUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LINEAR_CMUL th]);
    ALL_TAC] THEN
  REWRITE_TAC[dot; VSUM_COMPONENT; VECTOR_MUL_COMPONENT] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN `((D:real^N->real^N)(basis j))$i = (D(basis i))$j` SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    REAL_ARITH_TAC]);;

(* The x-partial derivative of the integrand at a parameter t in [0,1].     *)

let P2BPC_PARTIAL_INTEGRAND = prove
 (`!C (w:real^N->real^N) p x t i.
     open C /\ convex C /\ smooth_map_on C w /\
     (!y i j. y IN C /\ 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
              ==> (partial_derivative i w y)$j = (partial_derivative j w y)$i) /\
     p IN C /\ x IN C /\ t IN interval[vec 0,vec 1] /\ 1 <= i /\ i <= dimindex(:N)
     ==> partial_derivative i
           (\x. lift(w(p + drop t % (x - p)) dot (x - p))) x =
         lift((w(p + drop t % (x - p)))$i +
              drop t * (frechet_derivative w (at (p + drop t % (x - p))) (x - p))$i)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `y:real^N = p + drop t % (x - p)` THEN
  SUBGOAL_THEN `(y:real^N) IN C` ASSUME_TAC THENL
   [EXPAND_TAC "y" THEN MATCH_MP_TAC P2BPC_SEG_IN THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(w:real^N->real^N) differentiable at y` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `C:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`w:real^N->real^N`; `p:real^N`; `x:real^N`; `drop t`]
                P2BPC_INTEGRAND_DERIV) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[partial_derivative;
                                   GSYM(MATCH_MP FRECHET_DERIVATIVE_AT th)]) THEN
  ASM_SIMP_TAC[DOT_BASIS] THEN
  MP_TAC(ISPECL [`frechet_derivative (w:real^N->real^N) (at y)`; `x - p:real^N`; `i:num`]
                P2BPC_SYMM_DOT) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[LINEAR_FRECHET_DERIVATIVE] THEN
    MAP_EVERY X_GEN_TAC [`k:num`; `j:num`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`y:real^N`; `k:num`; `j:num`]) THEN
    ASM_REWRITE_TAC[partial_derivative];
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[]]);;

(* P2BPC.P4 The fundamental theorem of calculus for t w_i(p + t (x - p))    *)
(* and the Poincare lemma on open convex sets: a smooth covector field with *)
(* symmetric Jacobian has a smooth primitive.                                *)

let P2BPC_FTC_VALUE = prove
 (`!C (w:real^N->real^N) p x i.
     open C /\ convex C /\ smooth_map_on C w /\ p IN C /\ x IN C
     ==> ((\t. lift((w(p + drop t % (x - p)))$i +
                    drop t * (frechet_derivative w (at (p + drop t % (x - p))) (x - p))$i))
          has_integral lift((w x)$i)) (interval[vec 0,vec 1])`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\t:real^1. lift(drop t * ((w:real^N->real^N)(p + drop t % (x - p)))$i)`;
                 `\t:real^1. lift(((w:real^N->real^N)(p + drop t % (x - p)))$i +
                    drop t * (frechet_derivative (w:real^N->real^N)
                                (at (p + drop t % (x - p))) (x - p))$i)`;
                 `vec 0:real^1`; `vec 1:real^1`] FUNDAMENTAL_THEOREM_OF_CALCULUS) THEN
  REWRITE_TAC[DROP_VEC; REAL_POS] THEN ANTS_TAC THENL
   [X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN
    MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_AT_WITHIN THEN
    MATCH_MP_TAC P2BPC_FTC_DERIV THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `C:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P2BPC_SEG_IN THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_LID; VECTOR_MUL_LID; LIFT_NUM; VECTOR_SUB_RZERO;
                VECTOR_ARITH `p + x - p:real^N = x`]]);;

let P2BPC_POINCARE_CONVEX = prove
 (`!C (w:real^N->real^N).
     open C /\ convex C /\ smooth_map_on C w /\
     (!y i j. y IN C /\ 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
              ==> (partial_derivative i w y)$j = (partial_derivative j w y)$i)
     ==> ?h:real^N->real^1.
            smooth_map_on C h /\
            !x. x IN C ==> (h has_derivative (\v. lift(w x dot v))) (at x)`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `C:real^N->bool = {}` THENL
   [EXISTS_TAC `\x:real^N. vec 0:real^1` THEN
    ASM_REWRITE_TAC[SMOOTH_MAP_ON_CONST; NOT_IN_EMPTY];
    ALL_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `p:real^N` o REWRITE_RULE[GSYM MEMBER_NOT_EMPTY]) THEN
  ABBREV_TAC `W = {z:real^(N,1)finite_sum | p + drop(sndcart z) % (fstcart z - p) IN C}` THEN
  ABBREV_TAC `G = \z:real^(N,1)finite_sum.
                    lift((w:real^N->real^N)(p + drop(sndcart z) % (fstcart z - p)) dot
                         (fstcart z - p))` THEN
  MP_TAC(ISPECL [`C:real^N->bool`; `W:real^(N,1)finite_sum->bool`; `vec 0:real^1`;
                 `vec 1:real^1`; `G:real^(N,1)finite_sum->real^1`] NS_PARAM_INTEGRAL_SMOOTH) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [EXPAND_TAC "W" THEN MATCH_MP_TAC P2BPC_W_OPEN THEN ASM_REWRITE_TAC[];
      EXPAND_TAC "W" THEN EXPAND_TAC "G" THEN MATCH_MP_TAC P2BPC_G_SMOOTH THEN
      ASM_REWRITE_TAC[];
      MAP_EVERY X_GEN_TAC [`x:real^N`; `t:real^1`] THEN STRIP_TAC THEN EXPAND_TAC "W" THEN
      REWRITE_TAC[IN_ELIM_THM; FSTCART_PASTECART; SNDCART_PASTECART] THEN
      MATCH_MP_TAC P2BPC_SEG_IN THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `h = \x:real^N. integral (interval[vec 0:real^1,vec 1])
                                (\t. (G:real^(N,1)finite_sum->real^1)(pastecart x t))` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "pd")) THEN
  EXISTS_TAC `h:real^N->real^1` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(h:real^N->real^1) differentiable at x` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `C:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `frechet_derivative (h:real^N->real^1) (at x) = (\v. lift(w x dot v))`
  (fun th -> ASM_MESON_TAC[th; FRECHET_DERIVATIVE_WORKS]) THEN
  MATCH_MP_TAC LINEAR_EQ_STDBASIS THEN
  ASM_SIMP_TAC[LINEAR_FRECHET_DERIVATIVE; LINEAR_LIFT_DOT] THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  ASM_SIMP_TAC[DOT_BASIS; GSYM partial_derivative] THEN
  REMOVE_THEN "pd" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `(x:real^N) IN C`)]) THEN
  TRANS_TAC EQ_TRANS
   `integral (interval[vec 0:real^1,vec 1])
      (\t. lift(((w:real^N->real^N)(p + drop t % (x - p)))$i +
                drop t * (frechet_derivative w (at (p + drop t % (x - p))) (x - p))$i))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRAL_EQ THEN X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN
    EXPAND_TAC "G" THEN BETA_TAC THEN
    REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN
    MATCH_MP_TAC P2BPC_PARTIAL_INTEGRAND THEN EXISTS_TAC `C:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC INTEGRAL_UNIQUE THEN MATCH_MP_TAC P2BPC_FTC_VALUE THEN
    EXISTS_TAC `C:real^N->bool` THEN ASM_REWRITE_TAC[]]);;

(* P2BPC.P5 Two convex charts (coordinate form): closed                     *)
(* covector fields w1 on O1 and w2 on O2, compatible under a smooth          *)
(* transition tau from a connected open O12 in O1 into O2, have primitives   *)
(* h1, h2 with h1 = h2 o tau on O12 (the primitives of P2BPC_POINCARE_CONVEX *)
(* differ by a constant on the connected overlap).                           *)

let P2BPC_TWO_CHART_PRIMITIVE = prove
 (`!O1 O2 O12 (tau:real^N->real^N) (w1:real^N->real^N) (w2:real^N->real^N).
     open O1 /\ convex O1 /\ open O2 /\ convex O2 /\
     open O12 /\ connected O12 /\ O12 SUBSET O1 /\
     (!y. y IN O12 ==> tau y IN O2) /\ smooth_map_on O12 tau /\
     smooth_map_on O1 w1 /\ smooth_map_on O2 w2 /\
     (!y i j. y IN O1 /\ 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
              ==> (partial_derivative i w1 y)$j = (partial_derivative j w1 y)$i) /\
     (!y i j. y IN O2 /\ 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
              ==> (partial_derivative i w2 y)$j = (partial_derivative j w2 y)$i) /\
     (!y v. y IN O12 ==> w1 y dot v = w2 (tau y) dot (frechet_derivative tau (at y) v))
     ==> ?h1 h2:real^N->real^1.
            smooth_map_on O1 h1 /\ smooth_map_on O2 h2 /\
            (!y. y IN O1 ==> (h1 has_derivative (\v. lift(w1 y dot v))) (at y)) /\
            (!z. z IN O2 ==> (h2 has_derivative (\v. lift(w2 z dot v))) (at z)) /\
            (!y. y IN O12 ==> h1 y = h2 (tau y))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`O1:real^N->bool`; `w1:real^N->real^N`] P2BPC_POINCARE_CONVEX) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `h1:real^N->real^1` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`O2:real^N->bool`; `w2:real^N->real^N`] P2BPC_POINCARE_CONVEX) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `k2:real^N->real^1` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`\y:real^N. (h1:real^N->real^1) y - (k2:real^N->real^1)(tau y)`;
                 `O12:real^N->bool`] HAS_DERIVATIVE_ZERO_CONNECTED_CONSTANT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(y:real^N) IN O1 /\ (tau:real^N->real^N) y IN O2` STRIP_ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `((tau:real^N->real^N) has_derivative frechet_derivative tau (at y)) (at y)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC(REWRITE_RULE[RIGHT_IMP_FORALL_THM; IMP_IMP] SMOOTH_MAP_ON_HAS_DERIVATIVE) THEN
      EXISTS_TAC `O12:real^N->bool` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `((\y. (k2:real^N->real^1)((tau:real^N->real^N) y)) has_derivative
                   (\v. lift(w2 (tau y) dot frechet_derivative tau (at y) v))) (at y)`
    ASSUME_TAC THENL
     [MP_TAC(ISPECL [`tau:real^N->real^N`; `k2:real^N->real^1`;
                     `frechet_derivative (tau:real^N->real^N) (at y)`;
                     `\v. lift((w2:real^N->real^N) ((tau:real^N->real^N) (y:real^N)) dot v)`;
                     `y:real^N`]
                    DIFF_CHAIN_AT) THEN
      ASM_SIMP_TAC[o_DEF];
      ALL_TAC] THEN
    SUBGOAL_THEN `(\h:real^N. vec 0:real^1) =
                  (\v. lift(w1 y dot v) - lift(w2 ((tau:real^N->real^N) y) dot
                                              frechet_derivative tau (at y) v))`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `v:real^N` THEN
      ASM_SIMP_TAC[VECTOR_SUB_REFL];
      ALL_TAC] THEN
    MATCH_MP_TAC HAS_DERIVATIVE_SUB THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `c:real^1`) THEN
  MAP_EVERY EXISTS_TAC [`h1:real^N->real^1`; `\z:real^N. (k2:real^N->real^1) z + c`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN ASM_REWRITE_TAC[SMOOTH_MAP_ON_CONST; ETA_AX];
    X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(\v. lift((w2:real^N->real^N) z dot v)) = (\v. lift(w2 z dot v) + vec 0)`
    SUBST1_TAC THENL [REWRITE_TAC[VECTOR_ADD_RID; ETA_AX]; ALL_TAC] THEN
    MATCH_MP_TAC HAS_DERIVATIVE_ADD THEN ASM_SIMP_TAC[HAS_DERIVATIVE_CONST; ETA_AX];
    X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:real^N`) THEN ASM_REWRITE_TAC[] THEN
    VECTOR_ARITH_TAC]);;

(* P2BPC.P6 Pullback of a closed covector field by a smooth map tau: the    *)
(* field p2bpc_pull tau w with components w(tau y) . D tau(y) e_j is smooth  *)
(* and closed, and p2bpc_pull tau w y . v = w(tau y) . D tau(y) v.           *)

let p2bpc_pull = new_definition
 `p2bpc_pull (tau:real^N->real^N) (w:real^N->real^N) (y:real^N) =
    (lambda j. w(tau y) dot frechet_derivative tau (at y) (basis j)):real^N`;;

let P2BPC_SYMM_BILIN = prove
 (`!(D:real^N->real^N) a b.
     linear D /\
     (!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
            ==> (D(basis i))$j = (D(basis j))$i)
     ==> D a dot b = D b dot a`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(D:real^N->real^N) a =
                vsum(1..dimindex(:N)) (\i. (a:real^N)$i % D(basis i))` SUBST1_TAC THENL
   [GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM BASIS_EXPANSION] THEN
    ASM_SIMP_TAC[LINEAR_VSUM; FINITE_NUMSEG; o_DEF; LINEAR_CMUL];
    ALL_TAC] THEN
  SIMP_TAC[DOT_LSUM; FINITE_NUMSEG; DOT_LMUL] THEN
  GEN_REWRITE_TAC RAND_CONV [dot] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`D:real^N->real^N`; `b:real^N`; `i:num`] P2BPC_SYMM_DOT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC);;

let P2BPC_PULL_DOT = prove
 (`!(tau:real^N->real^N) (w:real^N->real^N) y v.
     tau differentiable at y
     ==> p2bpc_pull tau w y dot v = w(tau y) dot frechet_derivative tau (at y) v`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `linear(frechet_derivative (tau:real^N->real^N) (at y))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[LINEAR_FRECHET_DERIVATIVE]; ALL_TAC] THEN
  SUBGOAL_THEN `frechet_derivative (tau:real^N->real^N) (at y) v =
                vsum(1..dimindex(:N)) (\j. (v:real^N)$j % frechet_derivative tau (at y) (basis j))`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM BASIS_EXPANSION] THEN
    ASM_SIMP_TAC[LINEAR_VSUM; FINITE_NUMSEG; o_DEF; LINEAR_CMUL];
    ALL_TAC] THEN
  SIMP_TAC[DOT_RSUM; FINITE_NUMSEG; DOT_RMUL] THEN
  REWRITE_TAC[p2bpc_pull] THEN GEN_REWRITE_TAC LAND_CONV [dot] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN SIMP_TAC[LAMBDA_BETA] THEN REAL_ARITH_TAC);;

let P2BPC_PULL_SMOOTH = prove
 (`!O O' (tau:real^N->real^N) (w:real^N->real^N).
     open O /\ open O' /\ IMAGE tau O SUBSET O' /\ smooth_map_on O tau /\ smooth_map_on O' w
     ==> smooth_map_on O (p2bpc_pull tau w)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `p2bpc_pull (tau:real^N->real^N) (w:real^N->real^N) =
                (\y. (lambda k. drop((\k y. lift(w(tau y) dot
                                     frechet_derivative tau (at y) (basis k))) k y)):real^N)`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; p2bpc_pull; LIFT_DROP]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_LAMBDA THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `k:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_DOT_OPEN THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`O:real^N->bool`; `O':real^N->bool`; `tau:real^N->real^N`;
                   `w:real^N->real^N`] SMOOTH_MAP_ON_COMPOSE_OPEN) THEN
    ASM_REWRITE_TAC[o_DEF];
    MATCH_MP_TAC SMOOTH_MAP_ON_FRECHET_DERIVATIVE THEN ASM_REWRITE_TAC[]]);;

(* The derivative of the k-th component of the pullback.                     *)

let P2BPC_PULL_COMPONENT_DERIV = prove
 (`!O O' (tau:real^N->real^N) (w:real^N->real^N) y k.
     open O /\ open O' /\ IMAGE tau O SUBSET O' /\ smooth_map_on O tau /\
     smooth_map_on O' w /\ y IN O /\ 1 <= k /\ k <= dimindex(:N)
     ==> ((\z. lift(p2bpc_pull tau w z $ k)) has_derivative
          (\d. lift(w(tau y) dot
                    frechet_derivative (\z. frechet_derivative tau (at z) (basis k)) (at y) d) +
               lift(frechet_derivative w (at (tau y)) (frechet_derivative tau (at y) d) dot
                    frechet_derivative tau (at y) (basis k)))) (at y)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(tau:real^N->real^N) y IN O'` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(\z. lift(p2bpc_pull (tau:real^N->real^N) (w:real^N->real^N) z $ k)) =
                (\z. lift(w(tau z) dot frechet_derivative tau (at z) (basis k)))`
  SUBST1_TAC THENL [ASM_SIMP_TAC[FUN_EQ_THM; p2bpc_pull; LAMBDA_BETA]; ALL_TAC] THEN
  MP_TAC(ISPECL [`\u v:real^N. lift(u dot v)`;
                 `\z. (w:real^N->real^N)((tau:real^N->real^N) z)`;
                 `\z. frechet_derivative (tau:real^N->real^N) (at z) (basis k)`;
                 `\d. frechet_derivative (w:real^N->real^N) (at ((tau:real^N->real^N) (y:real^N)))
                        (frechet_derivative tau (at y) d)`;
                 `frechet_derivative (\z. frechet_derivative (tau:real^N->real^N) (at z) (basis k))
                                     (at (y:real^N))`;
                 `y:real^N`] HAS_DERIVATIVE_BILINEAR_AT) THEN
  REWRITE_TAC[BILINEAR_DOT] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`tau:real^N->real^N`; `w:real^N->real^N`;
                     `frechet_derivative (tau:real^N->real^N) (at y)`;
                     `frechet_derivative (w:real^N->real^N) (at ((tau:real^N->real^N) (y:real^N)))`;
                     `y:real^N`] DIFF_CHAIN_AT) THEN
      REWRITE_TAC[o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THEN
      MATCH_MP_TAC(REWRITE_RULE[RIGHT_IMP_FORALL_THM; IMP_IMP] SMOOTH_MAP_ON_HAS_DERIVATIVE) THEN
      ASM_MESON_TAC[];
      MP_TAC(ISPECL [`O:real^N->bool`;
                     `\z. frechet_derivative (tau:real^N->real^N) (at z) (basis k)`]
                    SMOOTH_MAP_ON_HAS_DERIVATIVE) THEN
      ASM_SIMP_TAC[SMOOTH_MAP_ON_FRECHET_DERIVATIVE]];
    REWRITE_TAC[]]);;

let P2BPC_PULL_CLOSED = prove
 (`!O O' (tau:real^N->real^N) (w:real^N->real^N).
     open O /\ open O' /\ IMAGE tau O SUBSET O' /\ smooth_map_on O tau /\
     smooth_map_on O' w /\
     (!y i j. y IN O' /\ 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
              ==> (partial_derivative i w y)$j = (partial_derivative j w y)$i)
     ==> !y i j. y IN O /\ 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
                 ==> (partial_derivative i (p2bpc_pull tau w) y)$j =
                     (partial_derivative j (p2bpc_pull tau w) y)$i`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`y:real^N`; `i:num`; `j:num`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(tau:real^N->real^N) y IN O'` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `P = p2bpc_pull (tau:real^N->real^N) (w:real^N->real^N)` THEN
  SUBGOAL_THEN `((P:real^N->real^N) has_derivative frechet_derivative P (at y)) (at y)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC(REWRITE_RULE[RIGHT_IMP_FORALL_THM; IMP_IMP] SMOOTH_MAP_ON_HAS_DERIVATIVE) THEN
    EXISTS_TAC `O:real^N->bool` THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "P" THEN
    MATCH_MP_TAC P2BPC_PULL_SMOOTH THEN EXISTS_TAC `O':real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the k-th component of D P(y) d by uniqueness of the derivative *)
  SUBGOAL_THEN
   `!k (d:real^N). 1 <= k /\ k <= dimindex(:N)
          ==> (frechet_derivative (P:real^N->real^N) (at y) d)$k =
              (w:real^N->real^N)((tau:real^N->real^N) y) dot
              frechet_derivative (\z. frechet_derivative tau (at z) (basis k)) (at y) d +
              frechet_derivative w (at (tau y)) (frechet_derivative tau (at y) d) dot
              frechet_derivative tau (at y) (basis k)`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`k:num`; `d:real^N`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`O:real^N->bool`; `O':real^N->bool`; `tau:real^N->real^N`;
                   `w:real^N->real^N`; `y:real^N`; `k:num`] P2BPC_PULL_COMPONENT_DERIV) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`P:real^N->real^N`; `frechet_derivative (P:real^N->real^N) (at y)`;
                   `y:real^N`] HAS_DERIVATIVE_COMPONENTWISE_AT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `k:num`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN
    MP_TAC(ISPECL [`\z. lift((P:real^N->real^N) z $ k)`;
                   `\d. lift(frechet_derivative (P:real^N->real^N) (at y) d $ k)`;
                   `\d. lift((w:real^N->real^N)(tau y) dot
                        frechet_derivative (\z. frechet_derivative (tau:real^N->real^N) (at z)
                                                  (basis k)) (at y) d) +
                        lift(frechet_derivative w (at (tau y)) (frechet_derivative tau (at y) d) dot
                             frechet_derivative tau (at y) (basis k))`;
                   `y:real^N`] FRECHET_DERIVATIVE_UNIQUE_AT) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o C AP_THM `d:real^N`) THEN
    REWRITE_TAC[GSYM LIFT_ADD; LIFT_EQ];
    ALL_TAC] THEN
  REWRITE_TAC[partial_derivative] THEN ASM_SIMP_TAC[] THEN
  (* Schwarz for tau and the symmetric Jacobian of w at tau y *)
  SUBGOAL_THEN
   `frechet_derivative (\z. frechet_derivative (tau:real^N->real^N) (at z) (basis j)) (at y)
                       (basis i) =
    frechet_derivative (\z. frechet_derivative tau (at z) (basis i)) (at y) (basis j)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC SCHWARZ_C2 THEN EXISTS_TAC `O:real^N->bool` THEN
    ASM_REWRITE_TAC[IN_NUMSEG] THEN
    UNDISCH_TAC `smooth_map_on O (tau:real^N->real^N)` THEN SIMP_TAC[smooth_map_on];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`frechet_derivative (w:real^N->real^N) (at (tau(y:real^N)))`;
                 `frechet_derivative (tau:real^N->real^N) (at y) (basis i)`;
                 `frechet_derivative (tau:real^N->real^N) (at y) (basis j)`]
                P2BPC_SYMM_BILIN) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `O':real^N->bool` THEN
      ASM_REWRITE_TAC[];
      MAP_EVERY X_GEN_TAC [`a:num`; `b:num`] THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`(tau:real^N->real^N) y`; `a:num`; `b:num`]) THEN
      ASM_REWRITE_TAC[partial_derivative]];
    DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC]);;

(* P2BPC.P8A Spherical shells of real^3 (the case S^2 x I): the slab        *)
(* charts p2bpc_ann_n, p2bpc_ann_s (radius exp(z$3), direction by inverse   *)
(* stereographic projection), their explicit inverses away from the closed *)
(* positive and negative z-rays, and the transition (inversion of the first *)
(* two coordinates) on the overlap.                                         *)

let p2bpc_pr2 = new_definition
 `p2bpc_pr2 (z:real^3) = (lambda i. z$i):real^2`;;

let p2bpc_ann_n = new_definition
 `p2bpc_ann_n (z:real^3) = exp(z$3) % stereo2_n_inv(p2bpc_pr2 z)`;;

let p2bpc_ann_s = new_definition
 `p2bpc_ann_s (z:real^3) = exp(z$3) % stereo2_s_inv(p2bpc_pr2 z)`;;

let p2bpc_ann_n_inv = new_definition
 `p2bpc_ann_n_inv (y:real^3) =
    (lambda i. if i = 3 then log(norm y) else y$i / (norm y - y$3)):real^3`;;

let p2bpc_ann_s_inv = new_definition
 `p2bpc_ann_s_inv (y:real^3) =
    (lambda i. if i = 3 then log(norm y) else y$i / (norm y + y$3)):real^3`;;

let p2bpc_ann_tau = new_definition
 `p2bpc_ann_tau (z:real^3) =
    (lambda i. if i = 3 then z$3 else z$i / (z$1 pow 2 + z$2 pow 2)):real^3`;;

let P2BPC_PR2_COMPONENTS = prove
 (`!z:real^3. p2bpc_pr2 z$1 = z$1 /\ p2bpc_pr2 z$2 = z$2 /\
              norm(p2bpc_pr2 z) pow 2 = z$1 pow 2 + z$2 pow 2`,
  GEN_TAC THEN
  SUBGOAL_THEN `p2bpc_pr2 (z:real^3)$1 = z$1 /\ p2bpc_pr2 z$2 = z$2` STRIP_ASSUME_TAC THENL
   [SIMP_TAC[p2bpc_pr2; LAMBDA_BETA; DIMINDEX_2; ARITH]; ALL_TAC] THEN
  ASM_REWRITE_TAC[NORM_POW_2; DOT_2] THEN REAL_ARITH_TAC);;

let P2BPC_ANN_N_COMPONENTS = prove
 (`!z:real^3.
     p2bpc_ann_n z$1 = exp(z$3) * (&2 * z$1 / ((z$1 pow 2 + z$2 pow 2) + &1)) /\
     p2bpc_ann_n z$2 = exp(z$3) * (&2 * z$2 / ((z$1 pow 2 + z$2 pow 2) + &1)) /\
     p2bpc_ann_n z$3 = exp(z$3) * (((z$1 pow 2 + z$2 pow 2) - &1) /
                                   ((z$1 pow 2 + z$2 pow 2) + &1))`,
  REWRITE_TAC[p2bpc_ann_n; VECTOR_MUL_COMPONENT; STEX_STEREO2_N_INV_COMPONENTS;
              P2BPC_PR2_COMPONENTS]);;

let P2BPC_ANN_S_COMPONENTS = prove
 (`!z:real^3.
     p2bpc_ann_s z$1 = exp(z$3) * (&2 * z$1 / ((z$1 pow 2 + z$2 pow 2) + &1)) /\
     p2bpc_ann_s z$2 = exp(z$3) * (&2 * z$2 / ((z$1 pow 2 + z$2 pow 2) + &1)) /\
     p2bpc_ann_s z$3 = exp(z$3) * ((&1 - (z$1 pow 2 + z$2 pow 2)) /
                                   ((z$1 pow 2 + z$2 pow 2) + &1))`,
  REWRITE_TAC[p2bpc_ann_s; VECTOR_MUL_COMPONENT; STEX_STEREO2_S_INV_COMPONENTS;
              P2BPC_PR2_COMPONENTS]);;

let P2BPC_ANN_N_NORM = prove
 (`!z:real^3. norm(p2bpc_ann_n z) = exp(z$3)`,
  GEN_TAC THEN REWRITE_TAC[p2bpc_ann_n; NORM_MUL] THEN
  MP_TAC(ISPEC `p2bpc_pr2 (z:real^3)` STEX_STEREO2_N_INV_IN) THEN
  REWRITE_TAC[IN_DELETE; IN_SPHERE_0] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[REAL_MUL_RID; REAL_ABS_EXP]);;

let P2BPC_ANN_S_NORM = prove
 (`!z:real^3. norm(p2bpc_ann_s z) = exp(z$3)`,
  GEN_TAC THEN REWRITE_TAC[p2bpc_ann_s; NORM_MUL] THEN
  MP_TAC(ISPEC `p2bpc_pr2 (z:real^3)` STEX_STEREO2_S_INV_IN) THEN
  REWRITE_TAC[IN_DELETE; IN_SPHERE_0] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[REAL_MUL_RID; REAL_ABS_EXP]);;

(* P2BPC.P8B Inverses of the shell charts and the transition identity.     *)

let P2BPC_ANN_N_LEFT = prove
 (`!z:real^3. p2bpc_ann_n_inv (p2bpc_ann_n z) = z`,
  GEN_TAC THEN REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3] THEN
  SIMP_TAC[p2bpc_ann_n_inv; LAMBDA_BETA; DIMINDEX_3; ARITH] THEN
  REWRITE_TAC[P2BPC_ANN_N_NORM; LOG_EXP; P2BPC_ANN_N_COMPONENTS] THEN
  MP_TAC(SPEC `(z:real^3)$3` REAL_EXP_POS_LT) THEN
  MP_TAC(SPEC `(z:real^3)$1 pow 2 + z$2 pow 2` (REAL_ARITH
    `!q. &0 <= q ==> ~(q + &1 = &0)`)) THEN
  ANTS_TAC THENL [MATCH_MP_TAC REAL_LE_ADD THEN REWRITE_TAC[REAL_LE_POW_2]; ALL_TAC] THEN
  SPEC_TAC(`(z:real^3)$1 pow 2 + z$2 pow 2`,`q:real`) THEN
  SPEC_TAC(`exp((z:real^3)$3)`,`e:real`) THEN
  REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `~(e = &0)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THEN REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC REAL_FIELD);;

let P2BPC_ANN_S_LEFT = prove
 (`!z:real^3. p2bpc_ann_s_inv (p2bpc_ann_s z) = z`,
  GEN_TAC THEN REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3] THEN
  SIMP_TAC[p2bpc_ann_s_inv; LAMBDA_BETA; DIMINDEX_3; ARITH] THEN
  REWRITE_TAC[P2BPC_ANN_S_NORM; LOG_EXP; P2BPC_ANN_S_COMPONENTS] THEN
  MP_TAC(SPEC `(z:real^3)$3` REAL_EXP_POS_LT) THEN
  MP_TAC(SPEC `(z:real^3)$1 pow 2 + z$2 pow 2` (REAL_ARITH
    `!q. &0 <= q ==> ~(q + &1 = &0)`)) THEN
  ANTS_TAC THENL [MATCH_MP_TAC REAL_LE_ADD THEN REWRITE_TAC[REAL_LE_POW_2]; ALL_TAC] THEN
  SPEC_TAC(`(z:real^3)$1 pow 2 + z$2 pow 2`,`q:real`) THEN
  SPEC_TAC(`exp((z:real^3)$3)`,`e:real`) THEN
  REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `~(e = &0)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THEN REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC REAL_FIELD);;

(* P2BPC.P8C Right inverses away from the closed z-rays, and the transition *)
(* p2bpc_ann_s o p2bpc_ann_tau = p2bpc_ann_n where z$1, z$2 are not both 0. *)

let P2BPC_ANN_N_RIGHT = prove
 (`!y:real^3. ~(norm y = y$3) ==> p2bpc_ann_n (p2bpc_ann_n_inv y) = y`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < norm(y:real^3) - y$3` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`y:real^3`; `3`] COMPONENT_LE_NORM) THEN
    REWRITE_TAC[DIMINDEX_3; ARITH] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < norm(y:real^3)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`y:real^3`; `3`] COMPONENT_LE_NORM) THEN
    REWRITE_TAC[DIMINDEX_3; ARITH] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `norm(y:real^3) pow 2 = y$1 pow 2 + y$2 pow 2 + y$3 pow 2` ASSUME_TAC THENL
   [REWRITE_TAC[NORM_POW_2; DOT_3] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `p2bpc_ann_n_inv (y:real^3)$1 = y$1 / (norm y - y$3) /\
                p2bpc_ann_n_inv y$2 = y$2 / (norm y - y$3) /\
                p2bpc_ann_n_inv y$3 = log(norm y)` STRIP_ASSUME_TAC THENL
   [SIMP_TAC[p2bpc_ann_n_inv; LAMBDA_BETA; DIMINDEX_3; ARITH]; ALL_TAC] THEN
  REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; P2BPC_ANN_N_COMPONENTS] THEN
  ASM_SIMP_TAC[EXP_LOG] THEN
  ABBREV_TAC `n = norm(y:real^3)` THEN ABBREV_TAC `d = n - (y:real^3)$3` THEN
  SUBGOAL_THEN `~((y$1 / d) pow 2 + ((y:real^3)$2 / d) pow 2 + &1 = &0)` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 <= a /\ &0 <= b ==> ~(a + b + &1 = &0)`) THEN
    REWRITE_TAC[REAL_LE_POW_2];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(d = &0) /\ ~(n = &0)` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_ADD_ASSOC] THEN
  REPEAT CONJ_TAC THEN REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC REAL_FIELD);;

let P2BPC_ANN_S_RIGHT = prove
 (`!y:real^3. ~(norm y = --(y$3)) ==> p2bpc_ann_s (p2bpc_ann_s_inv y) = y`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < norm(y:real^3) + y$3` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`y:real^3`; `3`] COMPONENT_LE_NORM) THEN
    REWRITE_TAC[DIMINDEX_3; ARITH] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < norm(y:real^3)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`y:real^3`; `3`] COMPONENT_LE_NORM) THEN
    REWRITE_TAC[DIMINDEX_3; ARITH] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `norm(y:real^3) pow 2 = y$1 pow 2 + y$2 pow 2 + y$3 pow 2` ASSUME_TAC THENL
   [REWRITE_TAC[NORM_POW_2; DOT_3] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `p2bpc_ann_s_inv (y:real^3)$1 = y$1 / (norm y + y$3) /\
                p2bpc_ann_s_inv y$2 = y$2 / (norm y + y$3) /\
                p2bpc_ann_s_inv y$3 = log(norm y)` STRIP_ASSUME_TAC THENL
   [SIMP_TAC[p2bpc_ann_s_inv; LAMBDA_BETA; DIMINDEX_3; ARITH]; ALL_TAC] THEN
  REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; P2BPC_ANN_S_COMPONENTS] THEN
  ASM_SIMP_TAC[EXP_LOG] THEN
  ABBREV_TAC `n = norm(y:real^3)` THEN ABBREV_TAC `d = n + (y:real^3)$3` THEN
  SUBGOAL_THEN `~((y$1 / d) pow 2 + ((y:real^3)$2 / d) pow 2 + &1 = &0)` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 <= a /\ &0 <= b ==> ~(a + b + &1 = &0)`) THEN
    REWRITE_TAC[REAL_LE_POW_2];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(d = &0) /\ ~(n = &0)` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_ADD_ASSOC] THEN
  REPEAT CONJ_TAC THEN REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC REAL_FIELD);;

let P2BPC_ANN_TAU = prove
 (`!z:real^3. ~(z$1 pow 2 + z$2 pow 2 = &0)
              ==> p2bpc_ann_s (p2bpc_ann_tau z) = p2bpc_ann_n z`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `p2bpc_ann_tau (z:real^3)$1 = z$1 / (z$1 pow 2 + z$2 pow 2) /\
                p2bpc_ann_tau z$2 = z$2 / (z$1 pow 2 + z$2 pow 2) /\
                p2bpc_ann_tau z$3 = z$3` STRIP_ASSUME_TAC THENL
   [SIMP_TAC[p2bpc_ann_tau; LAMBDA_BETA; DIMINDEX_3; ARITH]; ALL_TAC] THEN
  REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; P2BPC_ANN_N_COMPONENTS;
              P2BPC_ANN_S_COMPONENTS] THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `q = (z:real^3)$1 pow 2 + z$2 pow 2` THEN
  SUBGOAL_THEN `~(((z:real^3)$1 / q) pow 2 + (z$2 / q) pow 2 + &1 = &0) /\ ~(q + &1 = &0)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&0 <= a /\ &0 <= b ==> ~(a + b + &1 = &0)`) THEN
      REWRITE_TAC[REAL_LE_POW_2];
      EXPAND_TAC "q" THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= a /\ &0 <= b ==> ~((a + b) + &1 = &0)`) THEN
      REWRITE_TAC[REAL_LE_POW_2]];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_ADD_ASSOC] THEN
  REPEAT CONJ_TAC THEN REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC REAL_FIELD);;

(* P2BPC.P8D Smoothness of the shell charts, their inverses off the closed *)
(* z-rays and the transition off the z-axis; openness of these sets.      *)

let P2BPC_PR2_LINEAR = prove
 (`linear p2bpc_pr2`,
  REWRITE_TAC[linear; CART_EQ; DIMINDEX_2; FORALL_2; P2BPC_PR2_COMPONENTS;
              VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT]);;

let P2BPC_ANN_N_SMOOTH = prove
 (`!s. open s ==> smooth_map_on s p2bpc_ann_n`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `p2bpc_ann_n = (\z:real^3. drop(lift(exp(drop(lift(z$3))))) %
                                         (stereo2_n_inv o p2bpc_pr2) z)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; p2bpc_ann_n; o_THM; LIFT_DROP]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_MUL_DROP_OPEN THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_LIFT_EXP THEN ASM_SIMP_TAC[SMOOTH_MAP_ON_LIFT_COORDINATE];
    REWRITE_TAC[ETA_AX] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `(:real^2)` THEN
    ASM_REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV; STEX_STEREO2_N_INV_SMOOTH] THEN
    MATCH_MP_TAC P2BPC_SMOOTH_LINEAR THEN ASM_REWRITE_TAC[P2BPC_PR2_LINEAR]]);;

let P2BPC_ANN_S_SMOOTH = prove
 (`!s. open s ==> smooth_map_on s p2bpc_ann_s`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `p2bpc_ann_s = (\z:real^3. drop(lift(exp(drop(lift(z$3))))) %
                                         (stereo2_s_inv o p2bpc_pr2) z)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; p2bpc_ann_s; o_THM; LIFT_DROP]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_MUL_DROP_OPEN THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_LIFT_EXP THEN ASM_SIMP_TAC[SMOOTH_MAP_ON_LIFT_COORDINATE];
    REWRITE_TAC[ETA_AX] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `(:real^2)` THEN
    ASM_REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV; STEX_STEREO2_S_INV_SMOOTH] THEN
    MATCH_MP_TAC P2BPC_SMOOTH_LINEAR THEN ASM_REWRITE_TAC[P2BPC_PR2_LINEAR]]);;

let P2BPC_OPEN_NEQ = prove
 (`!f:real^N->real^1 c. (!x. f continuous at x) ==> open {x | ~(f x = c)}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `{x:real^N | ~(f x = c)} = {x | f x IN (:real^1) DIFF {c}}` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_DIFF; IN_UNIV; IN_SING]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE_UNIV THEN
  ASM_SIMP_TAC[OPEN_DIFF; OPEN_UNIV; CLOSED_SING]);;

let P2BPC_OFF_RAY_OPEN = prove
 (`open {y:real^3 | ~(norm y = y$3)} /\ open {y:real^3 | ~(norm y = --(y$3))} /\
   open {z:real^3 | ~(z$1 pow 2 + z$2 pow 2 = &0)}`,
  REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`\y:real^3. lift(norm y) - lift(y$3)`; `vec 0:real^1`] P2BPC_OPEN_NEQ) THEN
    REWRITE_TAC[VECTOR_SUB_EQ; LIFT_EQ] THEN DISCH_THEN MATCH_MP_TAC THEN GEN_TAC THEN
    MATCH_MP_TAC CONTINUOUS_SUB THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_LIFT_NORM_COMPOSE THEN REWRITE_TAC[CONTINUOUS_AT_ID];
      SIMP_TAC[CONTINUOUS_AT_LIFT_COMPONENT; DIMINDEX_3; ARITH]];
    MP_TAC(ISPECL [`\y:real^3. lift(norm y) + lift(y$3)`; `vec 0:real^1`] P2BPC_OPEN_NEQ) THEN
    REWRITE_TAC[VECTOR_ARITH `a + b:real^N = vec 0 <=> a = --b`; GSYM LIFT_NEG; LIFT_EQ] THEN
    DISCH_THEN MATCH_MP_TAC THEN GEN_TAC THEN
    MATCH_MP_TAC CONTINUOUS_ADD THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_LIFT_NORM_COMPOSE THEN REWRITE_TAC[CONTINUOUS_AT_ID];
      SIMP_TAC[CONTINUOUS_AT_LIFT_COMPONENT; DIMINDEX_3; ARITH]];
    MP_TAC(ISPECL [`\z:real^3. lift(z$1 pow 2 + z$2 pow 2)`; `vec 0:real^1`]
                  P2BPC_OPEN_NEQ) THEN
    REWRITE_TAC[GSYM LIFT_NUM; LIFT_EQ] THEN DISCH_THEN MATCH_MP_TAC THEN GEN_TAC THEN
    REWRITE_TAC[LIFT_ADD] THEN MATCH_MP_TAC CONTINUOUS_ADD THEN CONJ_TAC THEN
    MATCH_MP_TAC CONTINUOUS_LIFT_POW THEN
    SIMP_TAC[CONTINUOUS_AT_LIFT_COMPONENT; DIMINDEX_3; ARITH]]);;

let P2BPC_ANN_N_INV_SMOOTH = prove
 (`smooth_map_on {y:real^3 | ~(norm y = y$3)} p2bpc_ann_n_inv`,
  SUBGOAL_THEN
   `p2bpc_ann_n_inv =
    (\y:real^3. (lambda k. drop((\k y. lift(if k = 3 then log(norm y)
                                          else y$k / (norm y - y$3))) k y)):real^3)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; p2bpc_ann_n_inv; LIFT_DROP]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_LAMBDA THEN REWRITE_TAC[P2BPC_OFF_RAY_OPEN] THEN
  X_GEN_TAC `k:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `!y:real^3. y IN {y | ~(norm y = y$3)} ==> ~(y = vec 0) /\ &0 < norm y /\
                                                          ~(norm y - y$3 = &0)`
  ASSUME_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM] THEN GEN_TAC THEN DISCH_TAC THEN
    ASM_CASES_TAC `y:real^3 = vec 0` THENL
     [UNDISCH_TAC `~(norm(y:real^3) = y$3)` THEN ASM_REWRITE_TAC[NORM_0; VEC_COMPONENT];
      ASM_REWRITE_TAC[NORM_POS_LT] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_CASES_TAC `k = 3` THEN ASM_REWRITE_TAC[] THENL
   [SUBGOAL_THEN `(\y:real^3. lift(log(norm y))) =
                  (\y. lift(log(drop((\y. lift(norm y)) y))))` SUBST1_TAC THENL
     [REWRITE_TAC[LIFT_DROP]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_LIFT_LOG THEN REWRITE_TAC[P2BPC_OFF_RAY_OPEN; LIFT_DROP] THEN
    CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_LIFT_NORM THEN
    REWRITE_TAC[P2BPC_OFF_RAY_OPEN; SMOOTH_MAP_ON_ID] THEN ASM_MESON_TAC[];
    SUBGOAL_THEN `(\y:real^3. lift(y$k / (norm y - y$3))) =
                  (\y. lift(drop((\y. lift(y$k)) y) /
                            drop((\y. lift(drop(lift(norm y)) - drop(lift(y$3)))) y)))`
    SUBST1_TAC THENL [REWRITE_TAC[LIFT_DROP]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_LIFT_DIV THEN REWRITE_TAC[P2BPC_OFF_RAY_OPEN] THEN
    REPEAT CONJ_TAC THENL
     [SIMP_TAC[SMOOTH_MAP_ON_LIFT_COORDINATE; P2BPC_OFF_RAY_OPEN];
      MATCH_MP_TAC SMOOTH_MAP_ON_LIFT_SUB THEN
      SIMP_TAC[SMOOTH_MAP_ON_LIFT_COORDINATE; P2BPC_OFF_RAY_OPEN] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_LIFT_NORM THEN
      REWRITE_TAC[P2BPC_OFF_RAY_OPEN; SMOOTH_MAP_ON_ID] THEN ASM_MESON_TAC[];
      REWRITE_TAC[LIFT_DROP] THEN ASM_MESON_TAC[]]]);;

(* P2BPC.P8E The south inverse and the transition are smooth off the       *)
(* closed negative z-ray and the z-axis.                                    *)

let P2BPC_ANN_S_INV_SMOOTH = prove
 (`smooth_map_on {y:real^3 | ~(norm y = --(y$3))} p2bpc_ann_s_inv`,
  SUBGOAL_THEN
   `p2bpc_ann_s_inv =
    (\y:real^3. (lambda k. drop((\k y. lift(if k = 3 then log(norm y)
                                          else y$k / (norm y + y$3))) k y)):real^3)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; p2bpc_ann_s_inv; LIFT_DROP]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_LAMBDA THEN REWRITE_TAC[P2BPC_OFF_RAY_OPEN] THEN
  X_GEN_TAC `k:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `!y:real^3. y IN {y | ~(norm y = --(y$3))} ==> ~(y = vec 0) /\ &0 < norm y /\
                                                          ~(norm y + y$3 = &0)`
  ASSUME_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM] THEN GEN_TAC THEN DISCH_TAC THEN
    ASM_CASES_TAC `y:real^3 = vec 0` THENL
     [UNDISCH_TAC `~(norm(y:real^3) = --(y$3))` THEN ASM_REWRITE_TAC[NORM_0; VEC_COMPONENT; REAL_NEG_0];
      ASM_REWRITE_TAC[NORM_POS_LT] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_CASES_TAC `k = 3` THEN ASM_REWRITE_TAC[] THENL
   [SUBGOAL_THEN `(\y:real^3. lift(log(norm y))) =
                  (\y. lift(log(drop((\y. lift(norm y)) y))))` SUBST1_TAC THENL
     [REWRITE_TAC[LIFT_DROP]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_LIFT_LOG THEN REWRITE_TAC[P2BPC_OFF_RAY_OPEN; LIFT_DROP] THEN
    CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_LIFT_NORM THEN
    REWRITE_TAC[P2BPC_OFF_RAY_OPEN; SMOOTH_MAP_ON_ID] THEN ASM_MESON_TAC[];
    SUBGOAL_THEN `(\y:real^3. lift(y$k / (norm y + y$3))) =
                  (\y. lift(drop((\y. lift(y$k)) y) /
                            drop((\y. lift(drop(lift(norm y)) + drop(lift(y$3)))) y)))`
    SUBST1_TAC THENL [REWRITE_TAC[LIFT_DROP]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_LIFT_DIV THEN REWRITE_TAC[P2BPC_OFF_RAY_OPEN] THEN
    REPEAT CONJ_TAC THENL
     [SIMP_TAC[SMOOTH_MAP_ON_LIFT_COORDINATE; P2BPC_OFF_RAY_OPEN];
      MATCH_MP_TAC SMOOTH_MAP_ON_LIFT_ADD THEN
      SIMP_TAC[SMOOTH_MAP_ON_LIFT_COORDINATE; P2BPC_OFF_RAY_OPEN] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_LIFT_NORM THEN
      REWRITE_TAC[P2BPC_OFF_RAY_OPEN; SMOOTH_MAP_ON_ID] THEN ASM_MESON_TAC[];
      REWRITE_TAC[LIFT_DROP] THEN ASM_MESON_TAC[]]]);;

let P2BPC_ANN_TAU_SMOOTH = prove
 (`smooth_map_on {z:real^3 | ~(z$1 pow 2 + z$2 pow 2 = &0)} p2bpc_ann_tau`,
  SUBGOAL_THEN
   `p2bpc_ann_tau =
    (\z:real^3. (lambda k. drop((\k z. lift(if k = 3 then z$3
                                          else z$k / (z$1 pow 2 + z$2 pow 2))) k z)):real^3)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; p2bpc_ann_tau; LIFT_DROP]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_LAMBDA THEN REWRITE_TAC[P2BPC_OFF_RAY_OPEN] THEN
  X_GEN_TAC `k:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  ASM_CASES_TAC `k = 3` THEN ASM_REWRITE_TAC[] THENL
   [SIMP_TAC[SMOOTH_MAP_ON_LIFT_COORDINATE; P2BPC_OFF_RAY_OPEN];
    SUBGOAL_THEN
     `(\z:real^3. lift(z$k / (z$1 pow 2 + z$2 pow 2))) =
      (\z. lift(drop((\z. lift(z$k)) z) /
                drop((\z. lift(drop(lift(drop(lift(z$1)) pow 2)) +
                               drop(lift(drop(lift(z$2)) pow 2)))) z)))`
    SUBST1_TAC THENL [REWRITE_TAC[LIFT_DROP]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_LIFT_DIV THEN REWRITE_TAC[P2BPC_OFF_RAY_OPEN] THEN
    REPEAT CONJ_TAC THENL
     [SIMP_TAC[SMOOTH_MAP_ON_LIFT_COORDINATE; P2BPC_OFF_RAY_OPEN];
      MATCH_MP_TAC SMOOTH_MAP_ON_LIFT_ADD THEN REWRITE_TAC[P2BPC_OFF_RAY_OPEN] THEN
      CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_LIFT_POW THEN
      SIMP_TAC[SMOOTH_MAP_ON_LIFT_COORDINATE; P2BPC_OFF_RAY_OPEN];
      REWRITE_TAC[LIFT_DROP; IN_ELIM_THM]]]);;

(* P2BPC.P8F Helpers for the shell theorem: the annulus is open, the slab   *)
(* minus the z-axis is connected, the inverse charts invert the derivative  *)
(* of the charts, and the transition carries the derivative of the south    *)
(* chart to that of the north chart.                                        *)

let P2BPC_ANNULUS_OPEN = prove
 (`!r1 r2. open (annulus r1 r2:real^N->bool)`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `annulus r1 r2:real^N->bool = ((:real^N) DIFF cball(vec 0,r1)) INTER ball(vec 0,r2)`
  SUBST1_TAC THENL
   [REWRITE_TAC[annulus; EXTENSION; IN_ELIM_THM; IN_INTER; IN_DIFF; IN_UNIV; IN_CBALL_0;
                IN_BALL_0] THEN REAL_ARITH_TAC;
    MATCH_MP_TAC OPEN_INTER THEN SIMP_TAC[OPEN_DIFF; OPEN_UNIV; CLOSED_CBALL; OPEN_BALL]]);;

let P2BPC_SLAB_HALF_CONNECTED = prove
 (`!a b k c. connected {z:real^3 | a < z$3 /\ z$3 < b /\ c * z$k > &0}`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC CONVEX_CONNECTED THEN
  SUBGOAL_THEN `{z:real^3 | a < z$3 /\ z$3 < b /\ c * z$k > &0} =
                {z | z$3 > a} INTER {z | z$3 < b} INTER {z | (c % z)$k > &0}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INTER; VECTOR_MUL_COMPONENT] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT(MATCH_MP_TAC CONVEX_INTER THEN CONJ_TAC) THEN
  REWRITE_TAC[CONVEX_HALFSPACE_COMPONENT_GT; CONVEX_HALFSPACE_COMPONENT_LT] THEN
  SUBGOAL_THEN `{z:real^3 | (c % z)$k > &0} = {z | c * z$k > &0}` SUBST1_TAC THENL
   [REWRITE_TAC[VECTOR_MUL_COMPONENT]; ALL_TAC] THEN
  ASM_CASES_TAC `c = &0` THEN
  ASM_REWRITE_TAC[REAL_MUL_LZERO; real_gt; REAL_LT_REFL; EMPTY_GSPEC; CONVEX_EMPTY] THEN
  ASM_CASES_TAC `&0 < c` THENL
   [SUBGOAL_THEN `{z:real^3 | &0 < c * z$k} = {z | z$k > &0}` SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; real_gt] THEN GEN_TAC THEN
      ASM_SIMP_TAC[REAL_LT_MUL_EQ];
      REWRITE_TAC[CONVEX_HALFSPACE_COMPONENT_GT]];
    SUBGOAL_THEN `{z:real^3 | &0 < c * z$k} = {z | z$k < &0}` SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN GEN_TAC THEN
      SUBGOAL_THEN `c < &0` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ONCE_REWRITE_TAC[REAL_ARITH `&0 < c * x <=> &0 < --c * --x`] THEN
      SUBGOAL_THEN `&0 < --c` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LT_MUL_EQ] THEN REAL_ARITH_TAC;
      REWRITE_TAC[CONVEX_HALFSPACE_COMPONENT_LT]]]);;

let P2BPC_SLAB_PUNCT_CONNECTED = prove
 (`!a b. connected {z:real^3 | a < z$3 /\ z$3 < b /\ ~(z$1 pow 2 + z$2 pow 2 = &0)}`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `a < b` THENL
   [ALL_TAC;
    SUBGOAL_THEN `{z:real^3 | a < z$3 /\ z$3 < b /\ ~(z$1 pow 2 + z$2 pow 2 = &0)} = {}`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[CONNECTED_EMPTY]]] THEN
  ABBREV_TAC `m = (a + b) / &2` THEN
  SUBGOAL_THEN `a < m /\ m < b` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "m" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `{z:real^3 | a < z$3 /\ z$3 < b /\ ~(z$1 pow 2 + z$2 pow 2 = &0)} =
    (({z | a < z$3 /\ z$3 < b /\ &1 * z$1 > &0} UNION
      {z | a < z$3 /\ z$3 < b /\ &1 * z$2 > &0}) UNION
     {z | a < z$3 /\ z$3 < b /\ -- &1 * z$1 > &0}) UNION
    {z | a < z$3 /\ z$3 < b /\ -- &1 * z$2 > &0}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_UNION; REAL_SOS_EQ_0] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC CONNECTED_UNION THEN REWRITE_TAC[P2BPC_SLAB_HALF_CONNECTED] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CONNECTED_UNION THEN REWRITE_TAC[P2BPC_SLAB_HALF_CONNECTED] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CONNECTED_UNION THEN REWRITE_TAC[P2BPC_SLAB_HALF_CONNECTED] THEN
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_UNION; IN_ELIM_THM] THEN
      EXISTS_TAC `vector[&1; &1; m]:real^3` THEN ASM_REWRITE_TAC[VECTOR_3] THEN
      REAL_ARITH_TAC;
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_UNION; IN_ELIM_THM] THEN
      EXISTS_TAC `vector[-- &1; &1; m]:real^3` THEN ASM_REWRITE_TAC[VECTOR_3] THEN
      REAL_ARITH_TAC];
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_UNION; IN_ELIM_THM] THEN
    EXISTS_TAC `vector[&1; -- &1; m]:real^3` THEN ASM_REWRITE_TAC[VECTOR_3] THEN
    REAL_ARITH_TAC]);;

let P2BPC_ANN_N_INV_DERIV = prove
 (`!y v. ~(norm y = y$3)
         ==> frechet_derivative p2bpc_ann_n (at (p2bpc_ann_n_inv y))
               (frechet_derivative p2bpc_ann_n_inv (at y) v) = v`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(p2bpc_ann_n_inv has_derivative frechet_derivative p2bpc_ann_n_inv (at y)) (at y)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC(REWRITE_RULE[RIGHT_IMP_FORALL_THM; IMP_IMP] SMOOTH_MAP_ON_HAS_DERIVATIVE) THEN
    EXISTS_TAC `{y:real^3 | ~(norm y = y$3)}` THEN
    ASM_REWRITE_TAC[P2BPC_OFF_RAY_OPEN; P2BPC_ANN_N_INV_SMOOTH; IN_ELIM_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN `(p2bpc_ann_n has_derivative frechet_derivative p2bpc_ann_n (at (p2bpc_ann_n_inv y)))
                (at (p2bpc_ann_n_inv y))` ASSUME_TAC THENL
   [MATCH_MP_TAC(REWRITE_RULE[RIGHT_IMP_FORALL_THM; IMP_IMP] SMOOTH_MAP_ON_HAS_DERIVATIVE) THEN
    EXISTS_TAC `(:real^3)` THEN SIMP_TAC[OPEN_UNIV; P2BPC_ANN_N_SMOOTH; IN_UNIV];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`p2bpc_ann_n_inv`; `p2bpc_ann_n`;
                 `frechet_derivative p2bpc_ann_n_inv (at y)`;
                 `frechet_derivative p2bpc_ann_n (at (p2bpc_ann_n_inv y))`; `y:real^3`]
                DIFF_CHAIN_AT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `((\x:real^3. x) has_derivative
                 (frechet_derivative p2bpc_ann_n (at (p2bpc_ann_n_inv y)) o
                  frechet_derivative p2bpc_ann_n_inv (at y))) (at y)` ASSUME_TAC THENL
   [MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_WITHIN_OPEN THEN
    MAP_EVERY EXISTS_TAC [`p2bpc_ann_n o p2bpc_ann_n_inv`; `{y:real^3 | ~(norm y = y$3)}`] THEN
    ASM_SIMP_TAC[P2BPC_OFF_RAY_OPEN; IN_ELIM_THM; o_THM; P2BPC_ANN_N_RIGHT];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\x:real^3. x`; `\h:real^3. h`;
                 `frechet_derivative p2bpc_ann_n (at (p2bpc_ann_n_inv y)) o
                  frechet_derivative p2bpc_ann_n_inv (at y)`; `y:real^3`]
                FRECHET_DERIVATIVE_UNIQUE_AT) THEN
  ASM_REWRITE_TAC[HAS_DERIVATIVE_ID] THEN
  DISCH_THEN(MP_TAC o C AP_THM `v:real^3`) THEN REWRITE_TAC[o_THM] THEN
  MESON_TAC[]);;

let P2BPC_ANN_S_INV_DERIV = prove
 (`!y v. ~(norm y = --(y$3))
         ==> frechet_derivative p2bpc_ann_s (at (p2bpc_ann_s_inv y))
               (frechet_derivative p2bpc_ann_s_inv (at y) v) = v`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(p2bpc_ann_s_inv has_derivative frechet_derivative p2bpc_ann_s_inv (at y)) (at y)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC(REWRITE_RULE[RIGHT_IMP_FORALL_THM; IMP_IMP] SMOOTH_MAP_ON_HAS_DERIVATIVE) THEN
    EXISTS_TAC `{y:real^3 | ~(norm y = --(y$3))}` THEN
    ASM_REWRITE_TAC[P2BPC_OFF_RAY_OPEN; P2BPC_ANN_S_INV_SMOOTH; IN_ELIM_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN `(p2bpc_ann_s has_derivative frechet_derivative p2bpc_ann_s (at (p2bpc_ann_s_inv y)))
                (at (p2bpc_ann_s_inv y))` ASSUME_TAC THENL
   [MATCH_MP_TAC(REWRITE_RULE[RIGHT_IMP_FORALL_THM; IMP_IMP] SMOOTH_MAP_ON_HAS_DERIVATIVE) THEN
    EXISTS_TAC `(:real^3)` THEN SIMP_TAC[OPEN_UNIV; P2BPC_ANN_S_SMOOTH; IN_UNIV];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`p2bpc_ann_s_inv`; `p2bpc_ann_s`;
                 `frechet_derivative p2bpc_ann_s_inv (at y)`;
                 `frechet_derivative p2bpc_ann_s (at (p2bpc_ann_s_inv y))`; `y:real^3`]
                DIFF_CHAIN_AT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `((\x:real^3. x) has_derivative
                 (frechet_derivative p2bpc_ann_s (at (p2bpc_ann_s_inv y)) o
                  frechet_derivative p2bpc_ann_s_inv (at y))) (at y)` ASSUME_TAC THENL
   [MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_WITHIN_OPEN THEN
    MAP_EVERY EXISTS_TAC [`p2bpc_ann_s o p2bpc_ann_s_inv`; `{y:real^3 | ~(norm y = --(y$3))}`] THEN
    ASM_SIMP_TAC[P2BPC_OFF_RAY_OPEN; IN_ELIM_THM; o_THM; P2BPC_ANN_S_RIGHT];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\x:real^3. x`; `\h:real^3. h`;
                 `frechet_derivative p2bpc_ann_s (at (p2bpc_ann_s_inv y)) o
                  frechet_derivative p2bpc_ann_s_inv (at y)`; `y:real^3`]
                FRECHET_DERIVATIVE_UNIQUE_AT) THEN
  ASM_REWRITE_TAC[HAS_DERIVATIVE_ID] THEN
  DISCH_THEN(MP_TAC o C AP_THM `v:real^3`) THEN REWRITE_TAC[o_THM] THEN
  MESON_TAC[]);;

let P2BPC_ANN_TAU_DERIV = prove
 (`!z v. ~(z$1 pow 2 + z$2 pow 2 = &0)
         ==> frechet_derivative p2bpc_ann_s (at (p2bpc_ann_tau z))
               (frechet_derivative p2bpc_ann_tau (at z) v) =
             frechet_derivative p2bpc_ann_n (at z) v`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(p2bpc_ann_tau has_derivative frechet_derivative p2bpc_ann_tau (at z)) (at z)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC(REWRITE_RULE[RIGHT_IMP_FORALL_THM; IMP_IMP] SMOOTH_MAP_ON_HAS_DERIVATIVE) THEN
    EXISTS_TAC `{z:real^3 | ~(z$1 pow 2 + z$2 pow 2 = &0)}` THEN
    ASM_REWRITE_TAC[P2BPC_OFF_RAY_OPEN; P2BPC_ANN_TAU_SMOOTH; IN_ELIM_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN `!u. (p2bpc_ann_s has_derivative frechet_derivative p2bpc_ann_s (at u)) (at u) /\
                    (p2bpc_ann_n has_derivative frechet_derivative p2bpc_ann_n (at u)) (at u)`
  ASSUME_TAC THENL
   [GEN_TAC THEN CONJ_TAC THEN
    MATCH_MP_TAC(REWRITE_RULE[RIGHT_IMP_FORALL_THM; IMP_IMP] SMOOTH_MAP_ON_HAS_DERIVATIVE) THEN
    EXISTS_TAC `(:real^3)` THEN
    SIMP_TAC[OPEN_UNIV; P2BPC_ANN_S_SMOOTH; P2BPC_ANN_N_SMOOTH; IN_UNIV];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`p2bpc_ann_tau`; `p2bpc_ann_s`;
                 `frechet_derivative p2bpc_ann_tau (at z)`;
                 `frechet_derivative p2bpc_ann_s (at (p2bpc_ann_tau z))`; `z:real^3`]
                DIFF_CHAIN_AT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(p2bpc_ann_n has_derivative
                 (frechet_derivative p2bpc_ann_s (at (p2bpc_ann_tau z)) o
                  frechet_derivative p2bpc_ann_tau (at z))) (at z)` ASSUME_TAC THENL
   [MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_WITHIN_OPEN THEN
    MAP_EVERY EXISTS_TAC [`p2bpc_ann_s o p2bpc_ann_tau`;
                          `{z:real^3 | ~(z$1 pow 2 + z$2 pow 2 = &0)}`] THEN
    ASM_SIMP_TAC[P2BPC_OFF_RAY_OPEN; IN_ELIM_THM; o_THM; P2BPC_ANN_TAU];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`p2bpc_ann_n`; `frechet_derivative p2bpc_ann_n (at z)`;
                 `frechet_derivative p2bpc_ann_s (at (p2bpc_ann_tau z)) o
                  frechet_derivative p2bpc_ann_tau (at z)`; `z:real^3`]
                FRECHET_DERIVATIVE_UNIQUE_AT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o C AP_THM `v:real^3`) THEN REWRITE_TAC[o_THM] THEN
  MESON_TAC[]);;

(* P2BPC.P8G Closed covector fields on a spherical shell of real^3 are      *)
(* exact: the pullbacks by the two slab charts are closed on the convex    *)
(* slab, compatible through the transition on the connected overlap, so     *)
(* P2BPC_TWO_CHART_PRIMITIVE gives primitives that glue through the inverse *)
(* charts.                                                                  *)

let P2BPC_SHELL_EXACT = prove
 (`!r1 r2 (w:real^3->real^3).
     &0 < r1 /\ r1 < r2 /\ smooth_map_on (annulus r1 r2) w /\
     (!y i j. y IN annulus r1 r2 /\ 1 <= i /\ i <= dimindex(:3) /\
              1 <= j /\ j <= dimindex(:3)
              ==> (partial_derivative i w y)$j = (partial_derivative j w y)$i)
     ==> ?h:real^3->real^1.
            smooth_map_on (annulus r1 r2) h /\
            !y. y IN annulus r1 r2 ==> (h has_derivative (\v. lift(w y dot v))) (at y)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < r2` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `A = annulus r1 r2:real^3->bool` THEN
  SUBGOAL_THEN `open (A:real^3->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "A" THEN REWRITE_TAC[P2BPC_ANNULUS_OPEN]; ALL_TAC] THEN
  ABBREV_TAC `O = {z:real^3 | log r1 < z$3 /\ z$3 < log r2}` THEN
  SUBGOAL_THEN `open (O:real^3->bool) /\ convex O` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "O" THEN
    SUBGOAL_THEN `{z:real^3 | log r1 < z$3 /\ z$3 < log r2} =
                  {z | z$3 > log r1} INTER {z | z$3 < log r2}` SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM; real_gt]; ALL_TAC] THEN
    SIMP_TAC[OPEN_INTER; CONVEX_INTER; OPEN_HALFSPACE_COMPONENT_GT;
             OPEN_HALFSPACE_COMPONENT_LT; CONVEX_HALFSPACE_COMPONENT_GT;
             CONVEX_HALFSPACE_COMPONENT_LT];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z:real^3. z IN O ==> p2bpc_ann_n z IN A /\ p2bpc_ann_s z IN A`
  ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "O" THEN EXPAND_TAC "A" THEN
    REWRITE_TAC[IN_ELIM_THM; annulus; P2BPC_ANN_N_NORM; P2BPC_ANN_S_NORM] THEN STRIP_TAC THEN
    MP_TAC(SPECL [`log r1`; `(z:real^3)$3`] REAL_EXP_MONO_LT) THEN
    MP_TAC(SPECL [`(z:real^3)$3`; `log r2`] REAL_EXP_MONO_LT) THEN
    ASM_SIMP_TAC[EXP_LOG];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^3. y IN A ==> p2bpc_ann_n_inv y IN O /\ p2bpc_ann_s_inv y IN O`
  ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "O" THEN EXPAND_TAC "A" THEN REWRITE_TAC[IN_ELIM_THM; annulus] THEN
    SIMP_TAC[p2bpc_ann_n_inv; p2bpc_ann_s_inv; LAMBDA_BETA; DIMINDEX_3; ARITH] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `&0 < norm(y:real^3)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[LOG_MONO_LT];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE p2bpc_ann_n O SUBSET (A:real^3->bool) /\
                IMAGE p2bpc_ann_s O SUBSET A` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `wN = p2bpc_pull p2bpc_ann_n (w:real^3->real^3)` THEN
  ABBREV_TAC `wS = p2bpc_pull p2bpc_ann_s (w:real^3->real^3)` THEN
  SUBGOAL_THEN `smooth_map_on O (wN:real^3->real^3) /\ smooth_map_on O (wS:real^3->real^3)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["wN"; "wS"] THEN CONJ_TAC THEN
    MATCH_MP_TAC P2BPC_PULL_SMOOTH THEN EXISTS_TAC `A:real^3->bool` THEN
    ASM_SIMP_TAC[P2BPC_ANN_N_SMOOTH; P2BPC_ANN_S_SMOOTH];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(!y i j. y IN O /\ 1 <= i /\ i <= dimindex(:3) /\ 1 <= j /\ j <= dimindex(:3)
             ==> (partial_derivative i (wN:real^3->real^3) y)$j =
                 (partial_derivative j wN y)$i) /\
    (!y i j. y IN O /\ 1 <= i /\ i <= dimindex(:3) /\ 1 <= j /\ j <= dimindex(:3)
             ==> (partial_derivative i (wS:real^3->real^3) y)$j =
                 (partial_derivative j wS y)$i)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["wN"; "wS"] THEN CONJ_TAC THEN
    MATCH_MP_TAC P2BPC_PULL_CLOSED THEN EXISTS_TAC `A:real^3->bool` THEN
    ASM_SIMP_TAC[P2BPC_ANN_N_SMOOTH; P2BPC_ANN_S_SMOOTH];
    ALL_TAC] THEN
  ABBREV_TAC
   `O12 = {z:real^3 | log r1 < z$3 /\ z$3 < log r2 /\ ~(z$1 pow 2 + z$2 pow 2 = &0)}` THEN
  SUBGOAL_THEN `O12 SUBSET (O:real^3->bool) /\
                O12 SUBSET {z:real^3 | ~(z$1 pow 2 + z$2 pow 2 = &0)}`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["O12"; "O"] THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `open (O12:real^3->bool) /\ connected O12` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [SUBGOAL_THEN `O12 = (O:real^3->bool) INTER {z:real^3 | ~(z$1 pow 2 + z$2 pow 2 = &0)}`
      SUBST1_TAC THENL [MAP_EVERY EXPAND_TAC ["O12"; "O"] THEN SET_TAC[]; ALL_TAC] THEN
      ASM_SIMP_TAC[OPEN_INTER; P2BPC_OFF_RAY_OPEN];
      EXPAND_TAC "O12" THEN REWRITE_TAC[P2BPC_SLAB_PUNCT_CONNECTED]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z:real^3. z IN O12 ==> p2bpc_ann_tau z IN O` ASSUME_TAC THENL
   [GEN_TAC THEN MAP_EVERY EXPAND_TAC ["O12"; "O"] THEN REWRITE_TAC[IN_ELIM_THM] THEN
    SIMP_TAC[p2bpc_ann_tau; LAMBDA_BETA; DIMINDEX_3; ARITH];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on O12 p2bpc_ann_tau` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
    EXISTS_TAC `{z:real^3 | ~(z$1 pow 2 + z$2 pow 2 = &0)}` THEN
    ASM_REWRITE_TAC[P2BPC_ANN_TAU_SMOOTH];
    ALL_TAC] THEN
  SUBGOAL_THEN `(!u:real^3. p2bpc_ann_n differentiable at u) /\
                (!u:real^3. p2bpc_ann_s differentiable at u)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN GEN_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `(:real^3)` THEN
    SIMP_TAC[OPEN_UNIV; IN_UNIV; P2BPC_ANN_N_SMOOTH; P2BPC_ANN_S_SMOOTH];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z v. z IN O12
          ==> (wN:real^3->real^3) z dot v =
              (wS:real^3->real^3) (p2bpc_ann_tau z) dot
              frechet_derivative p2bpc_ann_tau (at z) v`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MAP_EVERY EXPAND_TAC ["wN"; "wS"] THEN
    ASM_SIMP_TAC[P2BPC_PULL_DOT] THEN
    SUBGOAL_THEN `~((z:real^3)$1 pow 2 + z$2 pow 2 = &0)` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[P2BPC_ANN_TAU; P2BPC_ANN_TAU_DERIV];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`O:real^3->bool`; `O:real^3->bool`; `O12:real^3->bool`; `p2bpc_ann_tau`;
                 `wN:real^3->real^3`; `wS:real^3->real^3`] P2BPC_TWO_CHART_PRIMITIVE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `h1:real^3->real^1` (X_CHOOSE_THEN `h2:real^3->real^1`
    STRIP_ASSUME_TAC)) THEN
  ABBREV_TAC `AN = (A:real^3->bool) INTER {y:real^3 | ~(norm y = y$3)}` THEN
  ABBREV_TAC `AS = (A:real^3->bool) INTER {y:real^3 | ~(norm y = --(y$3))}` THEN
  SUBGOAL_THEN `open (AN:real^3->bool) /\ open (AS:real^3->bool)` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["AN"; "AS"] THEN ASM_SIMP_TAC[OPEN_INTER; P2BPC_OFF_RAY_OPEN];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^3. y IN AN ==> y IN A /\ ~(norm y = y$3)` ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "AN" THEN REWRITE_TAC[IN_INTER; IN_ELIM_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^3. y IN AS ==> y IN A /\ ~(norm y = --(y$3))` ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "AS" THEN REWRITE_TAC[IN_INTER; IN_ELIM_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^3. y IN A ==> y IN AN \/ y IN AS` ASSUME_TAC THENL
   [GEN_TAC THEN MAP_EVERY EXPAND_TAC ["AN"; "AS"] THEN REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN
    DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `r1 < norm(y:real^3)` MP_TAC THENL
     [UNDISCH_TAC `(y:real^3) IN A` THEN EXPAND_TAC "A" THEN
      REWRITE_TAC[annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `h = \y:real^3. if norm y = y$3 then (h2:real^3->real^1)(p2bpc_ann_s_inv y)
                             else (h1:real^3->real^1)(p2bpc_ann_n_inv y)` THEN
  SUBGOAL_THEN `!y:real^3. y IN AN ==> (h:real^3->real^1) y = h1(p2bpc_ann_n_inv y)`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN EXPAND_TAC "h" THEN REWRITE_TAC[] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^3. y IN AS ==> (h:real^3->real^1) y = h2(p2bpc_ann_s_inv y)`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN EXPAND_TAC "h" THEN REWRITE_TAC[] THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `(y:real^3) IN A /\ ~(norm y = --(y$3))` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    ABBREV_TAC `z = p2bpc_ann_n_inv (y:real^3)` THEN
    SUBGOAL_THEN `p2bpc_ann_n z = (y:real^3)` ASSUME_TAC THENL
     [EXPAND_TAC "z" THEN MATCH_MP_TAC P2BPC_ANN_N_RIGHT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(z:real^3) IN O` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `~((z:real^3)$1 pow 2 + z$2 pow 2 = &0)` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_SOS_EQ_0] THEN STRIP_TAC THEN
      UNDISCH_TAC `~(norm(y:real^3) = --(y$3))` THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o
        check (fun th -> concl th = `p2bpc_ann_n z = (y:real^3)`)) THEN
      REWRITE_TAC[P2BPC_ANN_N_NORM; P2BPC_ANN_N_COMPONENTS] THEN ASM_REWRITE_TAC[] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(z:real^3) IN O12` ASSUME_TAC THENL
     [UNDISCH_TAC `(z:real^3) IN O` THEN MAP_EVERY EXPAND_TAC ["O"; "O12"] THEN
      REWRITE_TAC[IN_ELIM_THM] THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `p2bpc_ann_s_inv (y:real^3) = p2bpc_ann_tau z` SUBST1_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM o
        check (fun th -> concl th = `p2bpc_ann_n z = (y:real^3)`)) THEN
      ASM_SIMP_TAC[GSYM P2BPC_ANN_TAU; P2BPC_ANN_S_LEFT];
      ALL_TAC] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y:real^3. y IN AN ==> ((h:real^3->real^1) has_derivative (\v. lift(w y dot v))) (at y)`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(y:real^3) IN A /\ ~(norm y = y$3)` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_WITHIN_OPEN THEN
    MAP_EVERY EXISTS_TAC [`(h1:real^3->real^1) o p2bpc_ann_n_inv`; `AN:real^3->bool`] THEN
    ASM_SIMP_TAC[o_THM] THEN
    SUBGOAL_THEN `(p2bpc_ann_n_inv has_derivative frechet_derivative p2bpc_ann_n_inv (at y))
                  (at y)` ASSUME_TAC THENL
     [MATCH_MP_TAC(REWRITE_RULE[RIGHT_IMP_FORALL_THM; IMP_IMP] SMOOTH_MAP_ON_HAS_DERIVATIVE) THEN
      EXISTS_TAC `{y:real^3 | ~(norm y = y$3)}` THEN
      ASM_REWRITE_TAC[P2BPC_OFF_RAY_OPEN; P2BPC_ANN_N_INV_SMOOTH; IN_ELIM_THM];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`p2bpc_ann_n_inv`; `h1:real^3->real^1`;
                   `frechet_derivative p2bpc_ann_n_inv (at y)`;
                   `\v. lift((wN:real^3->real^3)(p2bpc_ann_n_inv y) dot v)`; `y:real^3`]
                  DIFF_CHAIN_AT) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC P2BPC_HAS_DERIVATIVE_EQ_DERIV THEN
    REWRITE_TAC[FUN_EQ_THM; o_THM] THEN X_GEN_TAC `v:real^3` THEN
    EXPAND_TAC "wN" THEN ASM_SIMP_TAC[P2BPC_PULL_DOT; P2BPC_ANN_N_RIGHT; P2BPC_ANN_N_INV_DERIV];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y:real^3. y IN AS ==> ((h:real^3->real^1) has_derivative (\v. lift(w y dot v))) (at y)`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(y:real^3) IN A /\ ~(norm y = --(y$3))` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_WITHIN_OPEN THEN
    MAP_EVERY EXISTS_TAC [`(h2:real^3->real^1) o p2bpc_ann_s_inv`; `AS:real^3->bool`] THEN
    ASM_SIMP_TAC[o_THM] THEN
    SUBGOAL_THEN `(p2bpc_ann_s_inv has_derivative frechet_derivative p2bpc_ann_s_inv (at y))
                  (at y)` ASSUME_TAC THENL
     [MATCH_MP_TAC(REWRITE_RULE[RIGHT_IMP_FORALL_THM; IMP_IMP] SMOOTH_MAP_ON_HAS_DERIVATIVE) THEN
      EXISTS_TAC `{y:real^3 | ~(norm y = --(y$3))}` THEN
      ASM_REWRITE_TAC[P2BPC_OFF_RAY_OPEN; P2BPC_ANN_S_INV_SMOOTH; IN_ELIM_THM];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`p2bpc_ann_s_inv`; `h2:real^3->real^1`;
                   `frechet_derivative p2bpc_ann_s_inv (at y)`;
                   `\v. lift((wS:real^3->real^3)(p2bpc_ann_s_inv y) dot v)`; `y:real^3`]
                  DIFF_CHAIN_AT) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC P2BPC_HAS_DERIVATIVE_EQ_DERIV THEN
    REWRITE_TAC[FUN_EQ_THM; o_THM] THEN X_GEN_TAC `v:real^3` THEN
    EXPAND_TAC "wS" THEN ASM_SIMP_TAC[P2BPC_PULL_DOT; P2BPC_ANN_S_RIGHT; P2BPC_ANN_S_INV_DERIV];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on AN (h:real^3->real^1) /\ smooth_map_on AS h` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN EXISTS_TAC `(h1:real^3->real^1) o p2bpc_ann_n_inv` THEN
      ASM_SIMP_TAC[o_THM] THEN MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
      EXISTS_TAC `O:real^3->bool` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM_MESON_TAC[];
        MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
        EXISTS_TAC `{y:real^3 | ~(norm y = y$3)}` THEN
        REWRITE_TAC[P2BPC_ANN_N_INV_SMOOTH] THEN EXPAND_TAC "AN" THEN SET_TAC[]];
      MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN EXISTS_TAC `(h2:real^3->real^1) o p2bpc_ann_s_inv` THEN
      ASM_SIMP_TAC[o_THM] THEN MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
      EXISTS_TAC `O:real^3->bool` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM_MESON_TAC[];
        MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
        EXISTS_TAC `{y:real^3 | ~(norm y = --(y$3))}` THEN
        REWRITE_TAC[P2BPC_ANN_S_INV_SMOOTH] THEN EXPAND_TAC "AS" THEN SET_TAC[]]];
    ALL_TAC] THEN
  EXISTS_TAC `h:real^3->real^1` THEN CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(y:real^3) IN AN \/ y IN AS` MP_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    STRIP_TAC THENL
     [EXISTS_TAC `AN:real^3->bool` THEN ASM_REWRITE_TAC[];
      EXISTS_TAC `AS:real^3->bool` THEN ASM_REWRITE_TAC[]];
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(y:real^3) IN AN \/ y IN AS` MP_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    STRIP_TAC THEN ASM_SIMP_TAC[]]);;

