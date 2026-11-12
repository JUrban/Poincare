(* ========================================================================= *)
(* pc_wan_lap2d: the Dirichlet problem on discs, WAN_DIRICHLET_DISC, by the  *)
(* Poisson integral wanl_dsol of pc_wan_lap2a.                               *)
(*   - a quadratic barrier, interior sup bounds for derivatives of           *)
(*     harmonic functions, bounded gradients for smooth boundary data;       *)
(*   - W^(1,2) of smooth maps with bounded gradient, orthogonality of        *)
(*     harmonic W^(1,2) maps to W^(1,2)_0, the smooth-data case;             *)
(*   - mollified cutoffs of g: smooth approximations near closed discs;      *)
(*   - the energy of the Poisson integral of g is finite; minimality;        *)
(*     WAN_DIRICHLET_DISC.                                                   *)
(* ========================================================================= *)

needs "src/pc_wan_lap2b.ml";;
needs "src/pc_wan_lap2c.ml";;
needs "src/pc_wan_sob2.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* Barrier and interior derivative bounds; bounded gradients                *)
(* of Poisson integrals of smooth data.                                     *)
(* ========================================================================= *)

let WANL_DPART_COMPONENT = prove
 (`!(H:real^N->real^K) x i j.
        H differentiable (at x) /\ 1 <= j /\ j <= dimindex(:K)
        ==> wan_dpart i (\y. H y$j) x = partial_derivative i H x$j`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[wan_dpart; partial_derivative] THEN
  SUBGOAL_THEN `(\y. lift((H:real^N->real^K) y$j)) = (\y. lift(basis j dot H y))`
  SUBST1_TAC THENL [ASM_SIMP_TAC[FUN_EQ_THM; DOT_BASIS]; ALL_TAC] THEN
  SUBGOAL_THEN
   `((\y. lift(basis j dot (H:real^N->real^K) y)) has_derivative
     (\t. lift(basis j dot frechet_derivative H (at x) t))) (at x)`
  MP_TAC THENL
   [MATCH_MP_TAC HAS_DERIVATIVE_LIFT_DOT THEN
    REWRITE_TAC[ETA_AX; GSYM FRECHET_DERIVATIVE_WORKS] THEN ASM_REWRITE_TAC[];
    DISCH_THEN(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
    ASM_SIMP_TAC[LIFT_DROP; DOT_BASIS]]);;

(* The quadratic c |x - a|^2 + d (pattern of RFA_SQDIST_DERIV in           *)
(* pc_rfa_spread.ml): derivative, smoothness, flat Laplacian 2 N c.         *)

let WANL_DD_QUAD_DERIV = prove
 (`!(a:real^N) c d z.
        ((\w. lift(c * norm(w - a) pow 2 + d)) has_derivative
         (\h. lift(&2 * c * ((z - a) dot h)))) (at z)`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN
   `(\w. lift(c * norm(w - a:real^N) pow 2 + d)) =
    (\w. c % ((\x. lift(norm x pow 2)) o (\w. w - a)) w + lift d) /\
    (\h. lift(&2 * c * ((z - a:real^N) dot h))) =
    (\h. c % ((\x. &2 % lift((z - a) dot x)) o (\h. h)) h + vec 0)`
  (fun th -> ONCE_REWRITE_TAC[th]) THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_ADD; LIFT_CMUL] THEN
    REPEAT STRIP_TAC THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC HAS_DERIVATIVE_ADD THEN REWRITE_TAC[HAS_DERIVATIVE_CONST] THEN
  MATCH_MP_TAC HAS_DERIVATIVE_CMUL THEN REWRITE_TAC[ETA_AX] THEN
  MATCH_MP_TAC DIFF_CHAIN_AT THEN REWRITE_TAC[HAS_DERIVATIVE_SQNORM_AT] THEN
  SUBGOAL_THEN `(\h:real^N. h) = (\h. h - vec 0)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; VECTOR_SUB_RZERO]; ALL_TAC] THEN
  MATCH_MP_TAC HAS_DERIVATIVE_SUB THEN
  REWRITE_TAC[HAS_DERIVATIVE_ID; HAS_DERIVATIVE_CONST]);;

let WANL_DD_QUAD_SMOOTH = prove
 (`!(s:real^N->bool) a c d.
        open s ==> smooth_map_on s (\x. lift(c * norm(x - a) pow 2 + d))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LIFT_ADD; LIFT_CMUL] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN ASM_REWRITE_TAC[SMOOTH_MAP_ON_CONST] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_CMUL_OPEN THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `\w:real^N. w - a`] SMOOTH_MAP_ON_NORM_POW2_OPEN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN
  ASM_REWRITE_TAC[SMOOTH_MAP_ON_ID; SMOOTH_MAP_ON_CONST]);;

let WANL_DD_LLAP_QUAD = prove
 (`!(a:real^N) c d y.
        llap (\z:real^N. mat 1) (\x. c * norm(x - a) pow 2 + d) y =
        &2 * &(dimindex(:N)) * c`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`(:real^N)`; `\x:real^N. c * norm(x - a) pow 2 + d`; `y:real^N`]
         LLAP_FLAT) THEN
  REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN
  ANTS_TAC THENL [MATCH_MP_TAC WANL_DD_QUAD_SMOOTH THEN REWRITE_TAC[OPEN_UNIV]; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= dimindex(:N)
        ==> drop(frechet_derivative
                  (\z. frechet_derivative (\w. lift(c * norm(w - a:real^N) pow 2 + d))
                         (at z) (basis i))
                  (at y) (basis i)) = &2 * c`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
     `(\z. frechet_derivative (\w. lift(c * norm(w - a:real^N) pow 2 + d)) (at z) (basis i)) =
      (\z. (&2 * c) % lift(basis i dot (z - a)))`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `z:real^N` THEN
      MP_TAC(ISPECL [`a:real^N`; `c:real`; `d:real`; `z:real^N`] WANL_DD_QUAD_DERIV) THEN
      DISCH_THEN(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
      REWRITE_TAC[LIFT_CMUL; VECTOR_MUL_ASSOC; REAL_MUL_ASSOC] THEN
      AP_TERM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[DOT_SYM];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `((\z. (&2 * c) % lift(basis i dot (z - a:real^N))) has_derivative
       (\h. (&2 * c) % lift(basis i dot h))) (at y)`
    MP_TAC THENL
     [MATCH_MP_TAC HAS_DERIVATIVE_CMUL THEN
      MATCH_MP_TAC HAS_DERIVATIVE_LIFT_DOT THEN
      SUBGOAL_THEN `(\h:real^N. h) = (\h. h - vec 0)` SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; VECTOR_SUB_RZERO]; ALL_TAC] THEN
      MATCH_MP_TAC HAS_DERIVATIVE_SUB THEN
      REWRITE_TAC[HAS_DERIVATIVE_ID; HAS_DERIVATIVE_CONST];
      DISCH_THEN(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
      ASM_SIMP_TAC[DROP_CMUL; LIFT_DROP; DOT_BASIS; BASIS_COMPONENT; REAL_MUL_RID]];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `sum(1..dimindex(:N)) (\i. &2 * c)` THEN
  CONJ_TAC THENL [MATCH_MP_TAC SUM_EQ_NUMSEG THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[SUM_CONST_NUMSEG; ADD_SUB] THEN CONV_TAC REAL_RING);;

(* The flat Laplacian of a smooth function is continuous.                   *)

let WANL_DD_LLAP_CONT = prove
 (`!(U:real^N->bool) f.
        open U /\ smooth_map_on U (\x. lift(f x))
        ==> (\x. lift(llap (\z:real^N. mat 1) f x)) continuous_on U`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC CONTINUOUS_ON_EQ THEN
  EXISTS_TAC `\x. vsum(1..dimindex(:N))
                    (\i. partial_derivative i (partial_derivative i (\z. lift((f:real^N->real) z))) x)` THEN
  CONJ_TAC THENL
   [X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `f:real^N->real`; `x:real^N`] WANL_LLAP_PARTIAL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[WAN_SUM_DROP; LIFT_DROP];
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_VSUM_OPEN THEN ASM_REWRITE_TAC[FINITE_NUMSEG] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[ETA_AX] THEN
  REPEAT(MATCH_MP_TAC SMOOTH_MAP_ON_PARTIAL_DERIVATIVE THEN ASM_REWRITE_TAC[]));;

(* The barrier: |w| <= M/(2N) (rho^2 - |x-a|^2) for w = 0 on the sphere and  *)
(* |Laplacian w| <= M, by the maximum principle WANL_MAXP_SUB.              *)

let WANL_DD_BARRIER_SIDE = prove
 (`!(a:real^N) rho (w:real^N->real) M s.
        &0 < rho /\ abs s <= &1 /\ (\x. lift(w x)) continuous_on cball(a,rho) /\
        smooth_map_on (ball(a,rho)) (\x. lift(w x)) /\
        (!x. x IN ball(a,rho) ==> abs(llap (\y:real^N. mat 1) w x) <= M) /\
        (!x. x IN sphere(a,rho) ==> w x = &0)
        ==> !x. x IN cball(a,rho)
                ==> s * w x <=
                    M / (&2 * &(dimindex(:N))) * (rho pow 2 - norm(x - a) pow 2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `c = M / (&2 * &(dimindex(:N)))` THEN
  SUBGOAL_THEN `&2 * &(dimindex(:N)) * c = M` ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN
    MATCH_MP_TAC(REAL_FIELD `&0 < n ==> &2 * n * M / (&2 * n) = M`) THEN
    REWRITE_TAC[REAL_OF_NUM_LT; DIMINDEX_GE_1; ARITH_RULE `0 < n <=> 1 <= n`];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`a:real^N`; `rho:real`;
                 `\x:real^N. s * w x + &1 * (c * norm(x - a) pow 2 + --(c * rho pow 2))`;
                 `&0`] WANL_MAXP_SUB) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[LIFT_ADD; LIFT_CMUL] THEN MATCH_MP_TAC CONTINUOUS_ON_ADD THEN
      CONJ_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^N)` THEN
      REWRITE_TAC[SUBSET_UNIV; GSYM LIFT_CMUL; GSYM LIFT_ADD] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
      MATCH_MP_TAC WANL_DD_QUAD_SMOOTH THEN REWRITE_TAC[OPEN_UNIV];
      REWRITE_TAC[LIFT_ADD; LIFT_CMUL] THEN MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN
      REWRITE_TAC[OPEN_BALL] THEN CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_CMUL_OPEN THEN
      ASM_REWRITE_TAC[OPEN_BALL; GSYM LIFT_CMUL; GSYM LIFT_ADD] THEN
      MATCH_MP_TAC WANL_DD_QUAD_SMOOTH THEN REWRITE_TAC[OPEN_BALL];
      X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
      MP_TAC(BETA_RULE(ISPECL [`ball(a:real^N,rho)`; `w:real^N->real`;
                     `\x:real^N. c * norm(x - a) pow 2 + --(c * rho pow 2)`;
                     `s:real`; `&1`; `x:real^N`] WANL_LLAP_LINEAR)) THEN
      ASM_REWRITE_TAC[OPEN_BALL] THEN ANTS_TAC THENL
       [MATCH_MP_TAC WANL_DD_QUAD_SMOOTH THEN REWRITE_TAC[OPEN_BALL]; ALL_TAC] THEN
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[WANL_DD_LLAP_QUAD] THEN
      MP_TAC(C MATCH_MP (ASSUME `(x:real^N) IN ball(a,rho)`)
               (ASSUME `!x. x IN ball(a:real^N,rho)
                            ==> abs(llap (\y:real^N. mat 1) w x) <= M`)) THEN
      ABBREV_TAC `L = llap (\z:real^N. mat 1) w x` THEN DISCH_TAC THEN
      SUBGOAL_THEN `abs(s * L) <= M` MP_TAC THENL
       [REWRITE_TAC[REAL_ABS_MUL] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `&1 * M` THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_ABS_POS]; REAL_ARITH_TAC];
        ASM_REAL_ARITH_TAC];
      X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
      SUBGOAL_THEN `norm(y - a:real^N) = rho` SUBST1_TAC THENL
       [UNDISCH_TAC `(y:real^N) IN sphere(a,rho)` THEN REWRITE_TAC[IN_SPHERE; dist] THEN
        CONV_TAC NORM_ARITH;
        ALL_TAC] THEN
      ASM_SIMP_TAC[] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `x:real^N` THEN
  MATCH_MP_TAC(TAUT `(q ==> r) ==> (p ==> q) ==> (p ==> r)`) THEN
  REAL_ARITH_TAC);;

let WANL_DD_BARRIER = prove
 (`!(a:real^N) rho (w:real^N->real) M.
        &0 < rho /\ (\x. lift(w x)) continuous_on cball(a,rho) /\
        smooth_map_on (ball(a,rho)) (\x. lift(w x)) /\
        (!x. x IN ball(a,rho) ==> abs(llap (\y:real^N. mat 1) w x) <= M) /\
        (!x. x IN sphere(a,rho) ==> w x = &0)
        ==> !x. x IN cball(a,rho)
                ==> abs(w x) <=
                    M / (&2 * &(dimindex(:N))) * (rho pow 2 - norm(x - a) pow 2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`a:real^N`; `rho:real`; `w:real^N->real`; `M:real`; `&1`]
         WANL_DD_BARRIER_SIDE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
                  DISCH_THEN(MP_TAC o SPEC `x:real^N`)] THEN
  MP_TAC(ISPECL [`a:real^N`; `rho:real`; `w:real^N->real`; `M:real`; `--(&1)`]
         WANL_DD_BARRIER_SIDE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
                  DISCH_THEN(MP_TAC o SPEC `x:real^N`)] THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* Interior sup bound: |D_i v(y)| <= C M / d for harmonic v with            *)
(* |v - c| <= M on B(y,2d), from the L^2 bound WANL_DPART_BOUND_UNIFORM.     *)

let WANL_DD_SUP_ARITH = prove
 (`!D K om Tn M d P Q.
        &0 < d /\ &0 <= K /\ &0 <= om /\ &0 <= Tn /\ &0 <= M /\ P * Q = &1 /\
        D pow 2 <= K * (P * inv d pow 2) * (M pow 2 * (om * (Tn * Q)))
        ==> abs D <= sqrt(K * om * Tn) * M / d`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `K * (P * inv d pow 2) * (M pow 2 * (om * (Tn * Q))) = (K * om * Tn) * (M / d) pow 2`
  (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [REWRITE_TAC[real_div; REAL_POW_MUL] THEN UNDISCH_TAC `P * Q = &1` THEN
    SPEC_TAC(`inv d pow 2`,`R:real`) THEN CONV_TAC REAL_RING;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= K * om * Tn /\ &0 <= M / d` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM POW_2_SQRT_ABS] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt((K * om * Tn) * (M / d) pow 2)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REWRITE_TAC[REAL_LE_POW_2];
    ASM_SIMP_TAC[SQRT_MUL; REAL_LE_POW_2; POW_2_SQRT] THEN
    REWRITE_TAC[real_div; REAL_MUL_ASSOC; REAL_LE_REFL]]);;

let WANL_DD_DPART_SUP = prove
 (`?C. &0 < C /\
       !(U:real^N->bool) (v:real^N->real) y d c M i.
          open U /\ smooth_map_on U (\x. lift(v x)) /\
          (!x. x IN U ==> llap (\z:real^N. mat 1) v x = &0) /\
          &0 < d /\ cball(y,&2 * d) SUBSET U /\
          (!z. z IN ball(y,&2 * d) ==> abs(v z - c) <= M) /\
          1 <= i /\ i <= dimindex(:N)
          ==> abs(wan_dpart i v y) <= C * M / d`,
  X_CHOOSE_THEN `K:real` STRIP_ASSUME_TAC (INST_TYPE [`:N`,`:N`] WANL_DPART_BOUND_UNIFORM) THEN
  EXISTS_TAC `sqrt(K * measure(ball(vec 0:real^N,&1)) * &2 pow dimindex(:N)) + &1` THEN
  SUBGOAL_THEN `&0 <= sqrt(K * measure(ball(vec 0:real^N,&1)) * &2 pow dimindex(:N))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LE THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN
    SIMP_TAC[MEASURE_POS_LE; MEASURABLE_BALL; REAL_POW_LE; REAL_POS];
    ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= M` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `abs((v:real^N->real) y - c)` THEN
    REWRITE_TAC[REAL_ABS_POS] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[CENTRE_IN_BALL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`U:real^N->bool`; `v:real^N->real`; `y:real^N`; `d:real`;
                                `c:real`; `i:num`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `drop(integral (ball(y,&2 * d)) (\z. lift(((v:real^N->real) z - c) pow 2))) <=
    M pow 2 * (measure(ball(vec 0:real^N,&1)) * (&2 pow dimindex(:N) * d pow dimindex(:N)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `drop(integral (ball(y:real^N,&2 * d)) (\z. lift(M pow 2)))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC INTEGRAL_DROP_LE THEN REWRITE_TAC[LIFT_DROP] THEN REPEAT CONJ_TAC THENL
       [MP_TAC(ISPECL [`\z. (v:real^N->real) z - c`; `y:real^N`; `&2 * d`]
               WANL_SQ_CONT_INTEGRABLE) THEN
        REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
        REWRITE_TAC[LIFT_SUB] THEN MATCH_MP_TAC CONTINUOUS_ON_SUB THEN
        REWRITE_TAC[CONTINUOUS_ON_CONST] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
        EXISTS_TAC `U:real^N->bool` THEN ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON];
        REWRITE_TAC[INTEGRABLE_ON_CONST; MEASURABLE_BALL];
        X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
        ONCE_REWRITE_TAC[GSYM REAL_LE_SQUARE_ABS] THEN
        ASM_SIMP_TAC[REAL_ARITH `&0 <= M ==> abs M = M`]];
      SIMP_TAC[INTEGRAL_CONST_GEN; MEASURABLE_BALL; DROP_CMUL; LIFT_DROP] THEN
      MP_TAC(ISPECL [`y:real^N`; `&2 * d`] WANL_CP_MEASURE_BALL) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
      REWRITE_TAC[REAL_POW_MUL] THEN MATCH_MP_TAC REAL_EQ_IMP_LE THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sqrt(K * measure(ball(vec 0:real^N,&1)) * &2 pow dimindex(:N)) * M / d` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC WANL_DD_SUP_ARITH THEN
    MAP_EVERY EXISTS_TAC [`inv d pow dimindex(:N)`; `d pow dimindex(:N)`] THEN
    ASM_SIMP_TAC[MEASURE_POS_LE; MEASURABLE_BALL; REAL_POW_LE; REAL_POS] THEN CONJ_TAC THENL
     [REWRITE_TAC[GSYM REAL_POW_MUL] THEN
      ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ; REAL_POW_ONE];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `K * (inv d pow dimindex(:N) * inv d pow 2) *
                drop(integral (ball(y,&2 * d)) (\z. lift(((v:real^N->real) z - c) pow 2)))` THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[GSYM REAL_POW_ADD]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THEN MATCH_MP_TAC REAL_POW_LE THEN
    REWRITE_TAC[REAL_LE_INV_EQ] THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
     [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC]]);;

(* Bounded gradient of a harmonic Hs on B(a,rho) with boundary values Gs,   *)
(* Gs smooth near cball(a,rho): with delta = rho - |y - a| the barrier gives *)
(* |Hs - Gs(y)| <= Q delta on B(y,delta/2), so |D_i Hs(y)| <= 4 C Q.        *)

let WANL_DD_GRAD_BOUND_SCALAR = prove
 (`!(U:real^N->bool) a rho (Gs:real^N->real) (Hs:real^N->real).
        open U /\ cball(a,rho) SUBSET U /\ &0 < rho /\
        smooth_map_on U (\x. lift(Gs x)) /\
        (\x. lift(Hs x)) continuous_on cball(a,rho) /\
        smooth_map_on (ball(a,rho)) (\x. lift(Hs x)) /\
        (!x. x IN ball(a,rho) ==> llap (\y:real^N. mat 1) Hs x = &0) /\
        (!x. x IN sphere(a,rho) ==> Hs x = Gs x)
        ==> ?B. !x i. x IN ball(a,rho) /\ 1 <= i /\ i <= dimindex(:N)
                      ==> abs(wan_dpart i Hs x) <= B`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?M0. !x. x IN cball(a:real^N,rho) ==> abs(llap (\z:real^N. mat 1) Gs x) <= M0`
  (X_CHOOSE_TAC `M0:real`) THENL
   [MP_TAC(ISPECL [`\x. lift(llap (\z:real^N. mat 1) Gs x)`; `cball(a:real^N,rho)`]
                  COMPACT_CONTINUOUS_IMAGE) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[COMPACT_CBALL] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC WANL_DD_LLAP_CONT THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
    REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE; NORM_LIFT] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?L0. !x. x IN cball(a:real^N,rho)
             ==> abs(sum(1..dimindex(:N)) (\i. abs(wan_dpart i (Gs:real^N->real) x))) <= L0`
  (X_CHOOSE_TAC `L0:real`) THENL
   [MP_TAC(ISPECL
     [`\x. lift(sum(1..dimindex(:N)) (\i. abs(wan_dpart i (Gs:real^N->real) x)))`;
      `cball(a:real^N,rho)`] COMPACT_CONTINUOUS_IMAGE) THEN
    REWRITE_TAC[COMPACT_CBALL] THEN
    MATCH_MP_TAC(TAUT `p /\ (q ==> r) ==> (p ==> q) ==> r`) THEN CONJ_TAC THENL
     [ALL_TAC;
      DISCH_THEN(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
      REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE; NORM_LIFT] THEN MESON_TAC[]] THEN
    REWRITE_TAC[LIFT_SUM; o_DEF] THEN
    MATCH_MP_TAC CONTINUOUS_ON_VSUM THEN REWRITE_TAC[FINITE_NUMSEG] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_LIFT_ABS THEN
    SUBGOAL_THEN `(\x. lift(wan_dpart i (Gs:real^N->real) x)) =
                  partial_derivative i (\y. lift(Gs y))` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; wan_dpart; partial_derivative; LIFT_DROP]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_PARTIAL_DERIVATIVE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `M = abs M0` THEN ABBREV_TAC `L = abs L0` THEN
  SUBGOAL_THEN `&0 <= M /\ &0 <= L` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["M"; "L"] THEN REWRITE_TAC[REAL_ABS_POS]; ALL_TAC] THEN
  SUBGOAL_THEN `!x. x IN cball(a,rho) ==> abs(llap (\z:real^N. mat 1) Gs x) <= M`
  (LABEL_TAC "hM") THENL
   [X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `M0:real` THEN ASM_SIMP_TAC[] THEN EXPAND_TAC "M" THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x i. x IN cball(a,rho) /\ 1 <= i /\ i <= dimindex(:N)
          ==> abs(wan_dpart i (Gs:real^N->real) x) <= L`
  (LABEL_TAC "hL") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`\i. abs(wan_dpart i (Gs:real^N->real) x)`; `L:real`;
                   `1..dimindex(:N)`] SUM_POS_BOUND) THEN
    REWRITE_TAC[FINITE_NUMSEG; REAL_ABS_POS] THEN ANTS_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `abs(sum(1..dimindex(:N)) (\i. abs(wan_dpart i (Gs:real^N->real) x)))` THEN
      CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `L0:real` THEN ASM_SIMP_TAC[] THEN
      EXPAND_TAC "L" THEN REAL_ARITH_TAC;
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_NUMSEG]];
    ALL_TAC] THEN
  (* w = Hs - Gs and the barrier *)
  SUBGOAL_THEN `smooth_map_on (ball(a,rho)) (\x. lift((Gs:real^N->real) x))` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `cball(a:real^N,rho)` THEN ASM_REWRITE_TAC[BALL_SUBSET_CBALL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`a:real^N`; `rho:real`; `\x. (Hs:real^N->real) x - Gs x`; `M:real`]
         WANL_DD_BARRIER) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[LIFT_SUB] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUB THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `U:real^N->bool` THEN
      ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON];
      MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN ASM_REWRITE_TAC[OPEN_BALL];
      X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(\x. (Hs:real^N->real) x - Gs x) = (\z. &1 * Hs z + --(&1) * Gs z)`
      SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
      MP_TAC(ISPECL [`ball(a:real^N,rho)`; `Hs:real^N->real`; `Gs:real^N->real`;
                     `&1`; `--(&1)`; `x:real^N`] WANL_LLAP_LINEAR) THEN
      ASM_REWRITE_TAC[OPEN_BALL] THEN DISCH_THEN SUBST1_TAC THEN
      MP_TAC(C MATCH_MP (ASSUME `(x:real^N) IN ball(a,rho)`)
               (ASSUME `!x. x IN ball(a:real^N,rho) ==> llap (\y:real^N. mat 1) Hs x = &0`)) THEN
      USE_THEN "hM" (MP_TAC o SPEC `x:real^N`) THEN
      ANTS_TAC THENL [ASM_MESON_TAC[BALL_SUBSET_CBALL; SUBSET]; ALL_TAC] THEN
      ABBREV_TAC `LG = llap (\z:real^N. mat 1) Gs x` THEN
      ABBREV_TAC `LH = llap (\z:real^N. mat 1) Hs x` THEN REAL_ARITH_TAC;
      X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
      ASM_SIMP_TAC[REAL_SUB_REFL]];
    DISCH_TAC] THEN
  X_CHOOSE_THEN `C:real` STRIP_ASSUME_TAC (INST_TYPE [`:N`,`:N`] WANL_DD_DPART_SUP) THEN
  ABBREV_TAC `Q = M / (&2 * &(dimindex(:N))) * (&3 * rho) + &(dimindex(:N)) * L / &2` THEN
  EXISTS_TAC `&4 * C * Q` THEN
  MAP_EVERY X_GEN_TAC [`y:real^N`; `i:num`] THEN STRIP_TAC THEN
  ABBREV_TAC `dl = rho - norm(y - a:real^N)` THEN
  SUBGOAL_THEN `&0 < dl` ASSUME_TAC THENL
   [EXPAND_TAC "dl" THEN UNDISCH_TAC `(y:real^N) IN ball(a,rho)` THEN
    REWRITE_TAC[IN_BALL; dist] THEN CONV_TAC NORM_ARITH;
    ALL_TAC] THEN
  SUBGOAL_THEN `cball(y:real^N,dl / &2) SUBSET ball(a,rho)` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_CBALL; IN_BALL] THEN X_GEN_TAC `z:real^N` THEN
    EXPAND_TAC "dl" THEN UNDISCH_TAC `&0 < dl` THEN EXPAND_TAC "dl" THEN
    CONV_TAC NORM_ARITH;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z. z IN ball(y,&2 * dl / &4) ==> abs((Hs:real^N->real) z - Gs y) <= Q * dl`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(z:real^N) IN ball(y,dl / &2)` ASSUME_TAC THENL
     [UNDISCH_TAC `(z:real^N) IN ball(y,&2 * dl / &4)` THEN REWRITE_TAC[IN_BALL] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(z:real^N) IN ball(a,rho)` ASSUME_TAC THENL
     [ASM_MESON_TAC[BALL_SUBSET_CBALL; SUBSET]; ALL_TAC] THEN
    SUBGOAL_THEN `(z:real^N) IN cball(a,rho)` ASSUME_TAC THENL
     [ASM_MESON_TAC[BALL_SUBSET_CBALL; SUBSET]; ALL_TAC] THEN
    (* the barrier part *)
    SUBGOAL_THEN
     `abs((Hs:real^N->real) z - Gs z) <= M / (&2 * &(dimindex(:N))) * (&3 * rho) * dl`
    ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `M / (&2 * &(dimindex(:N))) * (rho pow 2 - norm(z - a:real^N) pow 2)` THEN
      CONJ_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o SPEC `z:real^N`) THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[REAL_ARITH `&0 <= &2 * x <=> &0 <= x`; REAL_POS];
        ALL_TAC] THEN
      SUBGOAL_THEN `rho pow 2 - norm(z - a:real^N) pow 2 =
                    (rho - norm(z - a)) * (rho + norm(z - a))` SUBST1_TAC THENL
       [CONV_TAC REAL_RING; ALL_TAC] THEN
      SUBGOAL_THEN `(&3 * rho) * dl = (&3 * dl / &2) * (&2 * rho)` SUBST1_TAC THENL
       [CONV_TAC REAL_RING; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN
      UNDISCH_TAC `(z:real^N) IN ball(y,dl / &2)` THEN
      UNDISCH_TAC `(z:real^N) IN ball(a,rho)` THEN
      REWRITE_TAC[IN_BALL; dist] THEN EXPAND_TAC "dl" THEN CONV_TAC NORM_ARITH;
      ALL_TAC] THEN
    (* the Lipschitz part *)
    SUBGOAL_THEN `abs((Gs:real^N->real) z - Gs y) <= &(dimindex(:N)) * L * dl / &2`
    ASSUME_TAC THENL
     [MP_TAC(ISPECL [`U:real^N->bool`; `Gs:real^N->real`; `y:real^N`; `dl / &2`; `L:real`]
             WANL_SMOOTH_LIPSCHITZ_BALL) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
         [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `cball(a:real^N,rho)` THEN
          ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_TRANS THEN
          EXISTS_TAC `ball(a:real^N,rho)` THEN REWRITE_TAC[BALL_SUBSET_CBALL] THEN
          MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `cball(y:real^N,dl / &2)` THEN
          ASM_REWRITE_TAC[BALL_SUBSET_CBALL];
          REPEAT STRIP_TAC THEN USE_THEN "hL" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
          ASM_MESON_TAC[BALL_SUBSET_CBALL; SUBSET]];
        DISCH_THEN(MP_TAC o SPEC `z:real^N`) THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC(REAL_ARITH `y <= z ==> x <= y ==> x <= z`) THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `(z:real^N) IN ball(y,dl / &2)` THEN REWRITE_TAC[IN_BALL; dist] THEN
        CONV_TAC NORM_ARITH];
      ALL_TAC] THEN
    SUBGOAL_THEN `Q * dl = M / (&2 * &(dimindex(:N))) * (&3 * rho) * dl +
                           &(dimindex(:N)) * L * dl / &2`
    SUBST1_TAC THENL [EXPAND_TAC "Q" THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`ball(a:real^N,rho)`; `Hs:real^N->real`; `y:real^N`; `dl / &4`;
                 `(Gs:real^N->real) y`; `Q * dl`; `i:num`]
         (ASSUME `!(U:real^N->bool) (v:real^N->real) y d c M i.
                    open U /\ smooth_map_on U (\x. lift(v x)) /\
                    (!x. x IN U ==> llap (\z:real^N. mat 1) v x = &0) /\
                    &0 < d /\ cball(y,&2 * d) SUBSET U /\
                    (!z. z IN ball(y,&2 * d) ==> abs(v z - c) <= M) /\
                    1 <= i /\ i <= dimindex(:N)
                    ==> abs(wan_dpart i v y) <= C * M / d`)) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[OPEN_BALL] THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      SUBGOAL_THEN `&2 * dl / &4 = dl / &2` SUBST1_TAC THENL
       [REAL_ARITH_TAC; ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `y = z ==> x <= y ==> x <= z`) THEN
  UNDISCH_TAC `&0 < dl` THEN CONV_TAC REAL_FIELD);;

(* The vector form for the Poisson integral of smooth data on a disc.       *)

let WANL_DD_GRAD_BOUND = prove
 (`!(U:real^2->bool) a rho (G:real^2->real^K).
        open U /\ cball(a,rho) SUBSET U /\ &0 < rho /\ smooth_map_on U G
        ==> ?B. !x i. x IN ball(a,rho) /\ 1 <= i /\ i <= dimindex(:2)
                      ==> norm(partial_derivative i (wanl_dsol a rho G) x) <= B`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(G:real^2->real^K) continuous_on sphere(a:real^2,rho)` ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `U:real^2->bool` THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `cball(a:real^2,rho)` THEN
    ASM_REWRITE_TAC[SPHERE_SUBSET_CBALL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`a:real^2`; `rho:real`; `G:real^2->real^K`] WANL_DSOL_SMOOTH) THEN
  MP_TAC(ISPECL [`a:real^2`; `rho:real`; `G:real^2->real^K`] WANL_DSOL_CONTINUOUS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `H = wanl_dsol a rho (G:real^2->real^K)` THEN
  SUBGOAL_THEN
   `!j. ?B. 1 <= j /\ j <= dimindex(:K)
            ==> !x i. x IN ball(a,rho) /\ 1 <= i /\ i <= dimindex(:2)
                      ==> abs(wan_dpart i (\y. (H:real^2->real^K) y$j) x) <= B`
  MP_TAC THENL
   [X_GEN_TAC `j:num` THEN ASM_CASES_TAC `1 <= j /\ j <= dimindex(:K)` THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC WANL_DD_GRAD_BOUND_SCALAR THEN
    MAP_EVERY EXISTS_TAC [`U:real^2->bool`; `\y. (G:real^2->real^K) y$j`] THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_LIFT_COMPONENT; OPEN_BALL;
                 CONTINUOUS_ON_LIFT_COMPONENT_COMPOSE];
    REWRITE_TAC[SKOLEM_THM] THEN DISCH_THEN(X_CHOOSE_TAC `B:num->real`)] THEN
  EXISTS_TAC `sum(1..dimindex(:K)) (\j. abs(B j))` THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(1..dimindex(:K)) (\j. abs((partial_derivative i (H:real^2->real^K) x)$j))` THEN
  REWRITE_TAC[NORM_LE_L1] THEN MATCH_MP_TAC SUM_LE_NUMSEG THEN
  X_GEN_TAC `j:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`H:real^2->real^K`; `x:real^2`; `i:num`; `j:num`] WANL_DPART_COMPONENT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `ball(a:real^2,rho)` THEN ASM_REWRITE_TAC[OPEN_BALL];
    DISCH_THEN(SUBST1_TAC o SYM)] THEN
  MATCH_MP_TAC(REAL_ARITH `x <= b ==> x <= abs b`) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `j:num`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* W^(1,2) of smooth maps with bounded gradient on bounded open              *)
(* sets; orthogonality of harmonic W^(1,2) maps to W^(1,2)_0 (test          *)
(* functions by integration by parts, then the closure in energy); the      *)
(* Dirichlet principle for smooth data on discs.                            *)
(* ========================================================================= *)

let WANL_DD_W12_BOUNDED = prove
 (`!(s:real^N->bool) (H:real^N->real^K) B.
        open s /\ bounded s /\ smooth_map_on s H /\
        (!x. x IN s ==> norm(H x) <= B) /\
        (!x i. x IN s /\ 1 <= i /\ i <= dimindex(:N)
               ==> norm(partial_derivative i H x) <= B)
        ==> wan_w12 s H /\
            (!i. 1 <= i /\ i <= dimindex(:N)
                 ==> wan_wpd s i H (\x. partial_derivative i H x)) /\
            (!i. 1 <= i /\ i <= dimindex(:N)
                 ==> (\x. partial_derivative i H x) IN lspace s (&2)) /\
            wan_dir s H =
            sum(1..dimindex(:N))
               (\i. drop(integral s (\x. lift(norm(partial_derivative i H x) pow 2))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `measurable(s:real^N->bool) /\ lebesgue_measurable s` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[MEASURABLE_OPEN; LEBESGUE_MEASURABLE_OPEN]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!f:real^N->real^K. f continuous_on s /\ (!x. x IN s ==> norm(f x) <= B)
                       ==> f IN lspace s (&2)`
  (LABEL_TAC "l2") THENL
   [REPEAT STRIP_TAC THEN
    MATCH_MP_TAC(INST_TYPE [`:1`,`:P`] LSPACE_BOUNDED_MEASURABLE) THEN
    EXISTS_TAC `\x:real^N. lift B` THEN REPEAT CONJ_TAC THENL
     [REAL_ARITH_TAC;
      MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC LSPACE_CONST THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN REWRITE_TAC[NORM_LIFT] THEN
      MATCH_MP_TAC(REAL_ARITH `x <= b ==> x <= abs b`) THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= dimindex(:N)
        ==> (\x. partial_derivative i (H:real^N->real^K) x) IN lspace s (&2)`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN STRIP_TAC THEN USE_THEN "l2" MATCH_MP_TAC THEN
    ASM_SIMP_TAC[ETA_AX] THEN MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_PARTIAL_DERIVATIVE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`(:N)`; `(:K)`] WAN_W12_C1) THEN REWRITE_TAC[WAN_W12_C1_STATEMENT] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [UNDISCH_TAC `smooth_map_on s (H:real^N->real^K)` THEN SIMP_TAC[smooth_map_on];
    USE_THEN "l2" MATCH_MP_TAC THEN ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON]]);;

(* The vector Laplacian sum_i D_i D_i H vanishes where H is harmonic.       *)

let WANL_DD_VLAP_ZERO = prove
 (`!(U:real^N->bool) (H:real^N->real^K) x.
        open U /\ x IN U /\ smooth_map_on U H /\
        (!j. 1 <= j /\ j <= dimindex(:K)
             ==> llap (\y:real^N. mat 1) (\y. H y$j) x = &0)
        ==> vsum(1..dimindex(:N)) (\i. partial_derivative i (partial_derivative i H) x) =
            vec 0`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!i. partial_derivative i (partial_derivative i (H:real^N->real^K)) x =
        frechet_derivative (\z. frechet_derivative H (at z) (basis i)) (at x) (basis i)`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN REWRITE_TAC[partial_derivative] THEN AP_THM_TAC THEN AP_THM_TAC THEN
    AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM; partial_derivative];
    ALL_TAC] THEN
  REWRITE_TAC[CART_EQ; VEC_COMPONENT] THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  REWRITE_TAC[VSUM_COMPONENT] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `H:real^N->real^K`; `\v:real^K. lift(v$j)`;
                 `x:real^N`] WANL_LLAP_LINEAR_IMAGE) THEN
  ASM_REWRITE_TAC[LIFT_DROP; LINEAR_LIFT_COMPONENT] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_SIMP_TAC[]);;

(* Continuous maps paired with vector test functions are integrable.        *)

let WANL_DD_CONT_VTEST_INTEGRABLE = prove
 (`!(s:real^N->bool) (f:real^N->real^K) Psi.
        open s /\ f continuous_on s /\ wan_vtest s Psi
        ==> (\x. lift(f x dot Psi x)) integrable_on s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[dot; LIFT_SUM; o_DEF] THEN
  MATCH_MP_TAC INTEGRABLE_VSUM THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `\x. (f:real^N->real^K) x$j`; `\x. (Psi:real^N->real^K) x$j`]
         WAN_TEST_MUL_CONT_INTEGRABLE) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_SIMP_TAC[CONTINUOUS_ON_LIFT_COMPONENT_COMPOSE] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `Psi:real^N->real^K`; `j:num`] WAN_VTEST_COMPONENT) THEN
  ASM_SIMP_TAC[]);;

(* Harmonic maps are weakly harmonic against vector test functions.         *)

let WANL_DD_HARM_VTEST = prove
 (`!(s:real^N->bool) (H:real^N->real^K) Psi.
        open s /\ smooth_map_on s H /\
        (!x j. x IN s /\ 1 <= j /\ j <= dimindex(:K)
               ==> llap (\y:real^N. mat 1) (\y. H y$j) x = &0) /\
        wan_w12 s H /\ wan_vtest s Psi
        ==> sum(1..dimindex(:N))
              (\i. drop(integral s (\x. lift(wan_wd s i H x dot wan_wd s i Psi x)))) = &0`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= dimindex(:N)
        ==> drop(integral s (\x. lift(wan_wd s i (H:real^N->real^K) x dot
                                      wan_wd s i Psi x))) =
            --drop(integral s (\x. lift(partial_derivative i (partial_derivative i H) x dot
                                        Psi x)))`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    MP_TAC(BETA_RULE(ISPECL [`s:real^N->bool`; `i:num`; `H:real^N->real^K`;
                             `\x. partial_derivative i (H:real^N->real^K) x`] WAN_WD_UNIQUE)) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC WAN_WPD_C1 THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `smooth_map_on s (H:real^N->real^K)` THEN SIMP_TAC[smooth_map_on];
      DISCH_TAC] THEN
    MP_TAC(BETA_RULE(ISPECL [`s:real^N->bool`; `i:num`; `Psi:real^N->real^K`;
                             `\x. partial_derivative i (Psi:real^N->real^K) x`] WAN_WD_UNIQUE)) THEN
    ANTS_TAC THENL
     [MP_TAC(ISPECL [`s:real^N->bool`; `Psi:real^N->real^K`] WAN_VTEST_W12) THEN
      ASM_SIMP_TAC[];
      DISCH_TAC] THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `drop(integral s (\x. lift(partial_derivative i (H:real^N->real^K) x dot
                                         partial_derivative i Psi x)))` THEN
    CONJ_TAC THENL
     [AP_TERM_TAC THEN MATCH_MP_TAC INTEGRAL_SPIKE THEN
      EXISTS_TAC
       `{x | x IN s /\ ~(wan_wd s i (H:real^N->real^K) x = partial_derivative i H x)} UNION
        {x | x IN s /\ ~(wan_wd s i (Psi:real^N->real^K) x = partial_derivative i Psi x)}` THEN
      ASM_REWRITE_TAC[NEGLIGIBLE_UNION_EQ] THEN
      X_GEN_TAC `x:real^N` THEN REWRITE_TAC[IN_DIFF; IN_UNION; IN_ELIM_THM] THEN
      STRIP_TAC THEN
      SUBGOAL_THEN `wan_wd s i (H:real^N->real^K) x = partial_derivative i H x /\
                    wan_wd s i (Psi:real^N->real^K) x = partial_derivative i Psi x`
      (fun th -> REWRITE_TAC[th]) THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    MP_TAC(BETA_RULE(ISPECL
      [`s:real^N->bool`; `i:num`; `\x. partial_derivative i (H:real^N->real^K) x`;
       `\x. partial_derivative i (partial_derivative i (H:real^N->real^K)) x`;
       `Psi:real^N->real^K`] WAN_WPD_IMP_VTEST)) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`s:real^N->bool`; `partial_derivative i (H:real^N->real^K)`; `i:num`]
             WAN_WPD_C1) THEN
      REWRITE_TAC[ETA_AX] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[smooth_map_on; SMOOTH_MAP_ON_PARTIAL_DERIVATIVE];
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[DROP_NEG]];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `sum(1..dimindex(:N))
                (\i. --drop(integral s
                       (\x. lift(partial_derivative i (partial_derivative i (H:real^N->real^K)) x dot
                                 (Psi:real^N->real^K) x))))` THEN
  CONJ_TAC THENL [MATCH_MP_TAC SUM_EQ_NUMSEG THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[SUM_NEG; REAL_NEG_EQ_0; WAN_SUM_DROP] THEN
  MP_TAC(BETA_RULE(ISPECL
    [`\i x. lift(partial_derivative i (partial_derivative i (H:real^N->real^K)) x dot
                 (Psi:real^N->real^K) x)`;
     `s:real^N->bool`; `1..dimindex(:N)`] INTEGRAL_VSUM)) THEN
  REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN ANTS_TAC THENL
   [X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    MATCH_MP_TAC WANL_DD_CONT_VTEST_INTEGRABLE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN REWRITE_TAC[ETA_AX] THEN
    REPEAT(MATCH_MP_TAC SMOOTH_MAP_ON_PARTIAL_DERIVATIVE THEN ASM_REWRITE_TAC[]);
    DISCH_THEN(SUBST1_TAC o SYM)] THEN
  SUBGOAL_THEN
   `integral s (\x. vsum(1..dimindex(:N))
                     (\i. lift(partial_derivative i (partial_derivative i (H:real^N->real^K)) x dot
                               (Psi:real^N->real^K) x))) = vec 0`
  (fun th -> REWRITE_TAC[th; DROP_VEC]) THEN
  MATCH_MP_TAC INTEGRAL_EQ_0 THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `vsum(1..dimindex(:N))
      (\i. lift(partial_derivative i (partial_derivative i (H:real^N->real^K)) x dot
                (Psi:real^N->real^K) x)) =
    lift(vsum(1..dimindex(:N)) (\i. partial_derivative i (partial_derivative i H) x) dot Psi x)`
  SUBST1_TAC THENL
   [SIMP_TAC[DOT_LSUM; FINITE_NUMSEG; LIFT_SUM; o_DEF]; ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `H:real^N->real^K`; `x:real^N`] WANL_DD_VLAP_ZERO) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[DOT_LZERO; LIFT_NUM]);;

(* Cauchy-Schwarz for integrals of dot products of L^2 maps.                *)

let WANL_DD_DOT_CS = prove
 (`!(s:real^N->bool) (a:real^N->real^K) b.
        a IN lspace s (&2) /\ b IN lspace s (&2)
        ==> drop(integral s (\x. lift(a x dot b x))) pow 2 <=
            drop(integral s (\x. lift(norm(a x) pow 2))) *
            drop(integral s (\x. lift(norm(b x) pow 2)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `&2`; `&2`; `a:real^N->real^K`; `b:real^N->real^K`]
         LSPACE_INTEGRABLE_PRODUCT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV; DISCH_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `drop(integral s (\x. lift(norm((a:real^N->real^K) x) *
                                        norm((b:real^N->real^K) x)))) pow 2` THEN
  CONJ_TAC THENL
   [ONCE_REWRITE_TAC[GSYM REAL_LE_SQUARE_ABS] THEN
    MATCH_MP_TAC(REAL_ARITH `x <= y ==> x <= abs y`) THEN
    REWRITE_TAC[GSYM NORM_1] THEN
    MATCH_MP_TAC INTEGRAL_NORM_BOUND_INTEGRAL THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[WAN_LSPACE2_DOT_INTEGRABLE] THEN
    REWRITE_TAC[NORM_LIFT; LIFT_DROP; NORM_CAUCHY_SCHWARZ_ABS];
    MP_TAC(ISPECL [`\x. norm((a:real^N->real^K) x)`; `\x. norm((b:real^N->real^K) x)`;
                   `s:real^N->bool`] WANL_INTEGRAL_CS) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_SIMP_TAC[WAN_LSPACE2_SQNORM_INTEGRABLE]]);;

let WANL_DD_LIM_LE0 = prove
 (`!a K (e:num->real). &0 <= K /\ (e ---> &0) sequentially /\ (!n. a <= K * e n)
                       ==> a <= &0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [REALLIM_SEQUENTIALLY]) THEN
  DISCH_THEN(MP_TAC o SPEC `a / (K + &1)`) THEN
  ANTS_TAC THENL [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` (MP_TAC o SPEC `N:num`)) THEN
  REWRITE_TAC[LE_REFL; REAL_SUB_RZERO] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `N:num`) THEN
  SUBGOAL_THEN `K * e(N:num) <= K * a / (K + &1)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `K * a / (K + &1) = a - a / (K + &1)` SUBST1_TAC THENL
   [MP_TAC(REAL_ARITH `&0 <= K ==> ~(K + &1 = &0)`) THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < a / (K + &1)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]);;

(* One term of the orthogonality estimate: replacing the W_0 map by a test   *)
(* map costs at most sqrt(E(H) E(f - phi)).                                  *)

let WANL_DD_ORTHO_TERM = prove
 (`!(s:real^N->bool) (H:real^N->real^K) phi f i.
        open s /\ wan_w12 s H /\ wan_w12 s phi /\ wan_vtest s f /\
        1 <= i /\ i <= dimindex(:N)
        ==> abs(drop(integral s (\x. lift(wan_wd s i H x dot wan_wd s i phi x))) -
                drop(integral s (\x. lift(wan_wd s i H x dot wan_wd s i f x)))) <=
            sqrt(wan_dir s H * wan_dir s (\x. f x - phi x))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `f:real^N->real^K`] WAN_VTEST_W12) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `i:num`; `H:real^N->real^K`] WAN_WD_WORKS) THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `i:num`; `phi:real^N->real^K`] WAN_WD_WORKS) THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `i:num`; `f:real^N->real^K`] WAN_WD_WORKS) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `drop(integral s (\x. lift(wan_wd s i (H:real^N->real^K) x dot wan_wd s i phi x))) -
    drop(integral s (\x. lift(wan_wd s i H x dot wan_wd s i f x))) =
    drop(integral s (\x. lift(wan_wd s i H x dot (wan_wd s i phi x - wan_wd s i f x))))`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM DROP_SUB] THEN AP_TERM_TAC THEN
    REWRITE_TAC[DOT_RSUB; LIFT_SUB] THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC INTEGRAL_SUB THEN CONJ_TAC THEN
    MATCH_MP_TAC WAN_LSPACE2_DOT_INTEGRABLE THEN ASM_REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM POW_2_SQRT_ABS] THEN MATCH_MP_TAC SQRT_MONO_LE THEN
  REWRITE_TAC[REAL_LE_POW_2] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `drop(integral s (\x. lift(norm(wan_wd s i (H:real^N->real^K) x) pow 2))) *
    drop(integral s (\x. lift(norm(wan_wd s i phi x - wan_wd s i (f:real^N->real^K) x)
                             pow 2)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC WANL_DD_DOT_CS THEN ASM_REWRITE_TAC[ETA_AX] THEN
    MATCH_MP_TAC LSPACE_SUB THEN ASM_REWRITE_TAC[ETA_AX] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRAL_DROP_POS THEN ASM_SIMP_TAC[WAN_LSPACE2_SQNORM_INTEGRABLE; ETA_AX] THEN
    REWRITE_TAC[LIFT_DROP; REAL_LE_POW_2];
    MATCH_MP_TAC WAN_WD_SQ_LE_DIR THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC INTEGRAL_DROP_POS THEN REWRITE_TAC[LIFT_DROP; REAL_LE_POW_2] THEN
    MATCH_MP_TAC WAN_LSPACE2_SQNORM_INTEGRABLE THEN
    MATCH_MP_TAC LSPACE_SUB THEN ASM_REWRITE_TAC[ETA_AX] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `drop(integral s (\x. lift(norm(partial_derivative i (f:real^N->real^K) x -
                                             wan_wd s i phi x) pow 2)))` THEN
  CONJ_TAC THENL
   [ALL_TAC; MATCH_MP_TAC WAN_WD_DIFF_SQ_LE_DIR THEN ASM_REWRITE_TAC[]] THEN
  MATCH_MP_TAC REAL_EQ_IMP_LE THEN AP_TERM_TAC THEN MATCH_MP_TAC INTEGRAL_SPIKE THEN
  EXISTS_TAC `{x | x IN s /\ ~(wan_wd s i (f:real^N->real^K) x = partial_derivative i f x)}` THEN
  CONJ_TAC THENL
   [MP_TAC(BETA_RULE(ISPECL [`s:real^N->bool`; `i:num`; `f:real^N->real^K`;
                              `\x. partial_derivative i (f:real^N->real^K) x`] WAN_WD_UNIQUE)) THEN
    ASM_SIMP_TAC[];
    X_GEN_TAC `x:real^N` THEN REWRITE_TAC[IN_DIFF; IN_ELIM_THM] THEN STRIP_TAC THEN
    SUBGOAL_THEN `wan_wd s i (f:real^N->real^K) x = partial_derivative i f x` SUBST1_TAC THENL
     [ASM_MESON_TAC[]; REWRITE_TAC[NORM_SUB]]]);;

(* Orthogonality: smooth harmonic W^(1,2) maps are orthogonal to W^(1,2)_0. *)

let WANL_DD_ORTHO = prove
 (`!(s:real^N->bool) (H:real^N->real^K) phi.
        open s /\ smooth_map_on s H /\
        (!x j. x IN s /\ 1 <= j /\ j <= dimindex(:K)
               ==> llap (\y:real^N. mat 1) (\y. H y$j) x = &0) /\
        wan_w12 s H /\ wan_w120 s phi
        ==> sum(1..dimindex(:N))
              (\i. drop(integral s (\x. lift(wan_wd s i H x dot wan_wd s i phi x)))) = &0`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [wan_w120]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `f:num->real^N->real^K` STRIP_ASSUME_TAC)) THEN
  ABBREV_TAC `X = sum(1..dimindex(:N))
                    (\i. drop(integral s (\x. lift(wan_wd s i (H:real^N->real^K) x dot
                                                  wan_wd s i phi x))))` THEN
  SUBGOAL_THEN `&0 <= wan_dir s (H:real^N->real^K)` ASSUME_TAC THENL
   [MATCH_MP_TAC WAN_DIR_POS THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. X pow 2 <= (&(dimindex(:N)) pow 2 * wan_dir s (H:real^N->real^K)) *
                   wan_dir s (\x. (f:num->real^N->real^K) n x - phi x)`
  ASSUME_TAC THENL
   [X_GEN_TAC `n:num` THEN
    SUBGOAL_THEN `&0 <= wan_dir s (\x. (f:num->real^N->real^K) n x - phi x)` ASSUME_TAC THENL
     [MATCH_MP_TAC WAN_DIR_POS THEN MATCH_MP_TAC WAN_W12_SUB THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`s:real^N->bool`; `(f:num->real^N->real^K) n`] WAN_VTEST_W12) THEN
      ASM_SIMP_TAC[ETA_AX];
      ALL_TAC] THEN
    ABBREV_TAC `ee = wan_dir s (\x. (f:num->real^N->real^K) n x - phi x)` THEN
    SUBGOAL_THEN `abs X <= &(dimindex(:N)) * sqrt(wan_dir s (H:real^N->real^K) * ee)`
    ASSUME_TAC THENL
     [MP_TAC(ISPECL [`s:real^N->bool`; `H:real^N->real^K`; `(f:num->real^N->real^K) n`]
             WANL_DD_HARM_VTEST) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      SUBGOAL_THEN
       `X = sum(1..dimindex(:N))
              (\i. drop(integral s (\x. lift(wan_wd s i (H:real^N->real^K) x dot
                                             wan_wd s i phi x))) -
                   drop(integral s (\x. lift(wan_wd s i H x dot
                                             wan_wd s i ((f:num->real^N->real^K) n) x))))`
      SUBST1_TAC THENL
       [ASM_REWRITE_TAC[SUM_SUB_NUMSEG; REAL_SUB_RZERO]; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `sum(1..dimindex(:N)) (\i. sqrt(wan_dir s (H:real^N->real^K) * ee))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC SUM_ABS_LE THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
        X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN EXPAND_TAC "ee" THEN
        MATCH_MP_TAC WANL_DD_ORTHO_TERM THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[SUM_CONST_NUMSEG; ADD_SUB; REAL_LE_REFL]];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(&(dimindex(:N)) * sqrt(wan_dir s (H:real^N->real^K) * ee)) pow 2` THEN
    CONJ_TAC THENL
     [ONCE_REWRITE_TAC[GSYM REAL_LE_SQUARE_ABS] THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_POW_MUL] THEN
      SUBGOAL_THEN `&0 <= wan_dir s (H:real^N->real^K) * ee` ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      ASM_SIMP_TAC[SQRT_POW_2] THEN REWRITE_TAC[REAL_MUL_ASSOC; REAL_LE_REFL]];
    ALL_TAC] THEN
  MP_TAC(BETA_RULE(ISPECL [`X pow 2`; `&(dimindex(:N)) pow 2 * wan_dir s (H:real^N->real^K)`;
                           `\n. wan_dir s (\x. (f:num->real^N->real^K) n x - phi x)`]
                   WANL_DD_LIM_LE0)) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_POW_LE THEN REWRITE_TAC[REAL_POS];
    ALL_TAC] THEN
  MP_TAC(SPEC `X:real` REAL_LE_POW_2) THEN
  REWRITE_TAC[IMP_IMP; REAL_ARITH `&0 <= x /\ x <= &0 <=> x = &0`] THEN
  REWRITE_TAC[REAL_POW_EQ_0] THEN ARITH_TAC);;

(* Smooth maps and their partial derivatives are bounded on compacts.       *)

let WANL_DD_SMOOTH_COMPACT_BOUNDS = prove
 (`!(U:real^N->bool) (G:real^N->real^K) k.
        open U /\ compact k /\ k SUBSET U /\ smooth_map_on U G
        ==> ?B. !x i. x IN k /\ 1 <= i /\ i <= dimindex(:N)
                      ==> norm(G x) <= B /\ norm(partial_derivative i G x) <= B`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\x. lift(norm((G:real^N->real^K) x) +
                           sum(1..dimindex(:N)) (\i. norm(partial_derivative i G x)))`;
                 `k:real^N->bool`] COMPACT_CONTINUOUS_IMAGE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[LIFT_ADD; LIFT_SUM; o_DEF] THEN
    MATCH_MP_TAC CONTINUOUS_ON_ADD THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_LIFT_NORM_COMPOSE THEN
      ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON];
      MATCH_MP_TAC CONTINUOUS_ON_VSUM THEN REWRITE_TAC[FINITE_NUMSEG] THEN
      X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      MATCH_MP_TAC CONTINUOUS_ON_LIFT_NORM_COMPOSE THEN REWRITE_TAC[ETA_AX] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_PARTIAL_DERIVATIVE THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
  REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE; NORM_LIFT] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN EXISTS_TAC `B:real` THEN
  MAP_EVERY X_GEN_TAC [`x:real^N`; `i:num`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 <= sum(1..dimindex(:N)) (\i. norm(partial_derivative i (G:real^N->real^K) x)) /\
                norm(partial_derivative i (G:real^N->real^K) x) <=
                sum(1..dimindex(:N)) (\i. norm(partial_derivative i G x))`
  MP_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC SUM_POS_LE THEN REWRITE_TAC[NORM_POS_LE];
      MP_TAC(ISPECL [`\i. norm(partial_derivative i (G:real^N->real^K) x)`;
                     `sum(1..dimindex(:N)) (\i. norm(partial_derivative i (G:real^N->real^K) x))`;
                     `1..dimindex(:N)`] SUM_POS_BOUND) THEN
      REWRITE_TAC[FINITE_NUMSEG; NORM_POS_LE; REAL_LE_REFL] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_NUMSEG]];
    MP_TAC(ISPEC `(G:real^N->real^K) x` NORM_POS_LE) THEN REAL_ARITH_TAC]);;

(* The Dirichlet principle for smooth data on a disc.                        *)

let WANL_DD_SMOOTH_DIRICHLET = prove
 (`!(U:real^2->bool) a rho (G:real^2->real^K).
        open U /\ cball(a,rho) SUBSET U /\ &0 < rho /\ smooth_map_on U G
        ==> wan_w12 (ball(a,rho)) (wanl_dsol a rho G) /\
            wan_w120 (ball(a,rho)) (\x. wanl_dsol a rho G x - G x) /\
            (!i. 1 <= i /\ i <= dimindex(:2)
                 ==> (\x. partial_derivative i (wanl_dsol a rho G) x) IN
                     lspace (ball(a,rho)) (&2)) /\
            wan_dir (ball(a,rho)) (wanl_dsol a rho G) =
            sum(1..dimindex(:2))
              (\i. drop(integral (ball(a,rho))
                     (\x. lift(norm(partial_derivative i (wanl_dsol a rho G) x) pow 2)))) /\
            wan_dir (ball(a,rho)) G =
            sum(1..dimindex(:2))
              (\i. drop(integral (ball(a,rho))
                     (\x. lift(norm(partial_derivative i G x) pow 2)))) /\
            wan_dir (ball(a,rho)) (wanl_dsol a rho G) <= wan_dir (ball(a,rho)) G`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(G:real^2->real^K) continuous_on cball(a,rho)` ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `U:real^2->bool` THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON];
    ALL_TAC] THEN
  SUBGOAL_THEN `(G:real^2->real^K) continuous_on sphere(a,rho)` ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `cball(a:real^2,rho)` THEN
    ASM_REWRITE_TAC[SPHERE_SUBSET_CBALL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^2->bool`; `a:real^2`; `rho:real`; `G:real^2->real^K`]
         WANL_DD_GRAD_BOUND) THEN
  MP_TAC(ISPECL [`a:real^2`; `rho:real`; `G:real^2->real^K`] WANL_DSOL_SMOOTH) THEN
  MP_TAC(ISPECL [`a:real^2`; `rho:real`; `G:real^2->real^K`] WANL_DSOL_CONTINUOUS) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `H = wanl_dsol a rho (G:real^2->real^K)` THEN
  STRIP_TAC THEN STRIP_TAC THEN DISCH_THEN(X_CHOOSE_TAC `B1:real`) THEN
  SUBGOAL_THEN `?B2. !x. x IN cball(a:real^2,rho) ==> norm((H:real^2->real^K) x) <= B2`
  (X_CHOOSE_TAC `B2:real`) THENL
   [MP_TAC(ISPECL [`H:real^2->real^K`; `cball(a:real^2,rho)`] COMPACT_CONTINUOUS_IMAGE) THEN
    ASM_REWRITE_TAC[COMPACT_CBALL] THEN DISCH_THEN(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
    REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^2->bool`; `G:real^2->real^K`; `cball(a:real^2,rho)`]
         WANL_DD_SMOOTH_COMPACT_BOUNDS) THEN
  ASM_REWRITE_TAC[COMPACT_CBALL] THEN DISCH_THEN(X_CHOOSE_TAC `B3:real`) THEN
  SUBGOAL_THEN `ball(a:real^2,rho) SUBSET cball(a,rho)` ASSUME_TAC THENL
   [REWRITE_TAC[BALL_SUBSET_CBALL]; ALL_TAC] THEN
  MP_TAC(ISPECL [`ball(a:real^2,rho)`; `H:real^2->real^K`; `max B1 B2`]
         WANL_DD_W12_BOUNDED) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[OPEN_BALL; BOUNDED_BALL] THEN CONJ_TAC THEN REPEAT STRIP_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `x <= b ==> x <= max a b`) THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
      MATCH_MP_TAC(REAL_ARITH `x <= a ==> x <= max a b`) THEN ASM_SIMP_TAC[]];
    STRIP_TAC] THEN
  MP_TAC(ISPECL [`ball(a:real^2,rho)`; `G:real^2->real^K`; `B3:real`]
         WANL_DD_W12_BOUNDED) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[OPEN_BALL; BOUNDED_BALL] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `U:real^2->bool` THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`x:real^2`; `1`]) THEN
      ANTS_TAC THENL
       [REWRITE_TAC[DIMINDEX_2] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM SET_TAC[];
        SIMP_TAC[]];
      REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`x:real^2`; `i:num`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; SIMP_TAC[]]];
    STRIP_TAC] THEN
  SUBGOAL_THEN `wan_w120 (ball(a,rho)) (\x. (H:real^2->real^K) x - G x)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`(:2)`; `(:K)`] WAN_W120_CONT) THEN
    REWRITE_TAC[WAN_W120_CONT_STATEMENT] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_SIMP_TAC[CONTINUOUS_ON_SUB; VECTOR_SUB_REFL] THEN
    MATCH_MP_TAC WAN_W12_SUB THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`ball(a:real^2,rho)`; `H:real^2->real^K`; `\x. (G:real^2->real^K) x - H x`]
         WAN_DIR_ADD) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[OPEN_BALL] THEN MATCH_MP_TAC WAN_W12_SUB THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\x. (H:real^2->real^K) x + (\x. G x - H x) x) = G` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN
  MP_TAC(ISPECL [`ball(a:real^2,rho)`; `H:real^2->real^K`; `\x. (G:real^2->real^K) x - H x`]
         WANL_DD_ORTHO) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[OPEN_BALL] THEN
    SUBGOAL_THEN `(\x. (G:real^2->real^K) x - H x) = (\x. --((\x. H x - G x) x))`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM] THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC WAN_W120_NEG THEN ASM_REWRITE_TAC[OPEN_BALL];
    DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`ball(a:real^2,rho)`; `\x. (G:real^2->real^K) x - H x`] WAN_DIR_POS) THEN
  ANTS_TAC THENL [MATCH_MP_TAC WAN_W12_SUB THEN ASM_REWRITE_TAC[]; REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* Smooth approximations of g near closed discs.  For rho < r               *)
(* take a cutoff psi = 1 on cball(a,rho1), rho1 = (rho + r)/2, mollify the   *)
(* zero extension U of psi g: the mollifications converge uniformly on      *)
(* cball(a,rho), and on ball(a,rho) their partials are mollifications of the *)
(* weak partials of g, so their energy on ball(a,rho) is at most E_r(g).    *)
(* ========================================================================= *)

let WANL_MOLL_LOCAL = prove
 (`!e (u:real^N->real^K) v x.
        &0 < e /\ (!y. y IN ball(x,e) ==> u y = v y)
        ==> wan_moll e u x = wan_moll e v x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[WAN_MOLL_EQ] THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `y:real^N` THEN
  ASM_CASES_TAC `(y:real^N) IN ball(x,e)` THEN ASM_SIMP_TAC[] THEN
  MP_TAC(ISPECL [`e:real`; `x - y:real^N`] WAN_MKE_ZERO) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `~((y:real^N) IN ball(x,e))` THEN
    REWRITE_TAC[IN_BALL; dist] THEN REAL_ARITH_TAC;
    SIMP_TAC[VECTOR_MUL_LZERO]]);;

(* The cutoff extension: continuity, weak partials on the whole space, and   *)
(* the partials agree with those of g where psi = 1.                         *)

let WANL_DD_CUTOFF_EXT = prove
 (`!(a:real^N) r rho1 (g:real^N->real^K) psi.
        &0 < rho1 /\ rho1 < r /\ g continuous_on cball(a,r) /\
        wan_w12 (ball(a,r)) g /\ wan_test (ball(a,r)) psi /\
        (!x. x IN cball(a,rho1) ==> psi x = &1)
        ==> (\x. if x IN ball(a,r) then psi x % g x else vec 0) continuous_on (:real^N) /\
            (!i. 1 <= i /\ i <= dimindex(:N)
                 ==> wan_wpd (:real^N) i
                       (\x. if x IN ball(a,r) then psi x % g x else vec 0)
                       (\x. if x IN ball(a,r)
                            then wan_dpart i psi x % g x +
                                 psi x % wan_wd (ball(a,r)) i g x
                            else vec 0)) /\
            (!i x. x IN ball(a,rho1)
                   ==> (if x IN ball(a,r)
                        then wan_dpart i psi x % g x + psi x % wan_wd (ball(a,r)) i g x
                        else vec 0) = wan_wd (ball(a,r)) i g x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [wan_test]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `k0:real^N->bool` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `ball(a:real^N,rho1) SUBSET ball(a,r) /\ ball(a:real^N,rho1) SUBSET cball(a,rho1)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[BALL_SUBSET_CBALL] THEN MATCH_MP_TAC SUBSET_BALL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN `(:real^N) = ball(a,r) UNION ((:real^N) DIFF k0)` SUBST1_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_UNION_OPEN THEN
    ASM_SIMP_TAC[OPEN_BALL; OPEN_DIFF; OPEN_UNIV; COMPACT_IMP_CLOSED] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_EQ THEN EXISTS_TAC `\x. (psi:real^N->real) x % (g:real^N->real^K) x` THEN
      SIMP_TAC[] THEN MATCH_MP_TAC CONTINUOUS_ON_MUL THEN CONJ_TAC THENL
       [REWRITE_TAC[o_DEF] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
        EXISTS_TAC `(:real^N)` THEN ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON; SUBSET_UNIV];
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `cball(a:real^N,r)` THEN
        ASM_REWRITE_TAC[BALL_SUBSET_CBALL]];
      MATCH_MP_TAC CONTINUOUS_ON_EQ THEN EXISTS_TAC `\x:real^N. vec 0:real^K` THEN
      REWRITE_TAC[CONTINUOUS_ON_CONST; IN_DIFF; IN_UNIV] THEN
      X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(psi:real^N->real) x = &0` SUBST1_TAC THENL
       [ASM_SIMP_TAC[]; REWRITE_TAC[VECTOR_MUL_LZERO; COND_ID]]];
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN MATCH_MP_TAC WAN_WPD_ZERO_EXTENSION THEN
    ASM_SIMP_TAC[OPEN_BALL; WAN_WD_WORKS; ETA_AX];
    MAP_EVERY X_GEN_TAC [`i:num`; `x:real^N`] THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:real^N) IN ball(a,r)` (fun th -> REWRITE_TAC[th]) THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(psi:real^N->real) x = &1` SUBST1_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `wan_dpart i (psi:real^N->real) x = &0` SUBST1_TAC THENL
     [REWRITE_TAC[wan_dpart] THEN
      MP_TAC(ISPECL [`\y. lift((psi:real^N->real) y)`; `\y:real^N. lift(&1)`;
                     `ball(a:real^N,rho1)`; `x:real^N`] WANL_FD_LOCAL_OPEN) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[OPEN_BALL] THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
        AP_TERM_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
        DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[FRECHET_DERIVATIVE_CONST_AT; DROP_VEC]];
      REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_MUL_LID; VECTOR_ADD_LID]]]);;

let WANL_DD_APPROX = prove
 (`!(a:real^N) r rho (g:real^N->real^K) eta.
        &0 < rho /\ rho < r /\ &0 < eta /\ g continuous_on cball(a,r) /\
        wan_w12 (ball(a,r)) g
        ==> ?G. smooth_map_on (:real^N) G /\
                (!x. x IN cball(a,rho) ==> norm(G x - g x) <= eta) /\
                sum(1..dimindex(:N))
                  (\i. drop(integral (ball(a,rho))
                         (\x. lift(norm(partial_derivative i G x) pow 2)))) <=
                wan_dir (ball(a,r)) g`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `rho1 = (rho + r) / &2` THEN
  SUBGOAL_THEN `rho < rho1 /\ rho1 < r` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "rho1" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`ball(a:real^N,r)`; `cball(a:real^N,rho1)`] WAN_SMOOTH_URYSOHN) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[OPEN_BALL; COMPACT_CBALL; SUBSET; IN_CBALL; IN_BALL] THEN
    ASM_REAL_ARITH_TAC;
    DISCH_THEN(X_CHOOSE_THEN `psi:real^N->real` STRIP_ASSUME_TAC)] THEN
  MP_TAC(ISPECL [`a:real^N`; `r:real`; `rho1:real`; `g:real^N->real^K`; `psi:real^N->real`]
         WANL_DD_CUTOFF_EXT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `U = \x. if x IN ball(a:real^N,r) then (psi:real^N->real) x % (g:real^N->real^K) x
                      else vec 0` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "wpd") (LABEL_TAC "eqv"))) THEN
  SUBGOAL_THEN `!x. x IN cball(a:real^N,rho) ==> (U:real^N->real^K) x = g x` ASSUME_TAC THENL
   [X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN EXPAND_TAC "U" THEN
    SUBGOAL_THEN `(x:real^N) IN ball(a,r) /\ x IN cball(a,rho1)` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(x:real^N) IN cball(a,rho)` THEN REWRITE_TAC[IN_CBALL; IN_BALL] THEN
      ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[VECTOR_MUL_LID]];
    ALL_TAC] THEN
  SUBGOAL_THEN `wan_lloc (:real^N) (U:real^N->real^K)` ASSUME_TAC THENL
   [USE_THEN "wpd" (MP_TAC o SPEC `1`) THEN REWRITE_TAC[LE_REFL; DIMINDEX_GE_1] THEN
    SIMP_TAC[wan_wpd];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->real^K`; `cball(a:real^N,rho)`] WAN_MOLL_UNIFORM) THEN
  ASM_REWRITE_TAC[COMPACT_CBALL] THEN DISCH_THEN(MP_TAC o SPEC `eta:real`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `e = min (d / &2) ((rho1 - rho) / &2)` THEN
  SUBGOAL_THEN `&0 < e /\ e < d /\ rho + e < rho1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "e" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  EXISTS_TAC `wan_moll e (U:real^N->real^K)` THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC WAN_MOLL_SMOOTH THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(g:real^N->real^K) x = U x` SUBST1_TAC THENL
     [CONV_TAC SYM_CONV THEN ASM_SIMP_TAC[]; ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(1..dimindex(:N))
                (\i. drop(integral (ball(a:real^N,r))
                       (\x. lift(norm(wan_wd (ball(a,r)) i (g:real^N->real^K) x) pow 2))))` THEN
  CONJ_TAC THENL [ALL_TAC; REWRITE_TAC[wan_dir; REAL_LE_REFL]] THEN
  MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  ABBREV_TAC `W = \x. if x IN ball(a:real^N,rho1)
                      then wan_wd (ball(a,r)) i (g:real^N->real^K) x else vec 0` THEN
  SUBGOAL_THEN
   `!x. x IN ball(a:real^N,rho)
        ==> partial_derivative i (wan_moll e (U:real^N->real^K)) x = wan_moll e W x`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `wan_wpd (:real^N) i (U:real^N->real^K)
        (\x. if x IN ball(a,r)
             then wan_dpart i (psi:real^N->real) x % (g:real^N->real^K) x +
                  psi x % wan_wd (ball(a,r)) i g x
             else vec 0)`
    ASSUME_TAC THENL [USE_THEN "wpd" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL
      [`e:real`; `U:real^N->real^K`;
       `\x. if x IN ball(a:real^N,r)
            then wan_dpart i (psi:real^N->real) x % (g:real^N->real^K) x +
                 psi x % wan_wd (ball(a,r)) i g x
            else vec 0`; `i:num`; `x:real^N`] WAN_MOLL_WPD) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    MATCH_MP_TAC WANL_MOLL_LOCAL THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(y:real^N) IN ball(a,rho1)` ASSUME_TAC THENL
     [UNDISCH_TAC `(y:real^N) IN ball(x,e)` THEN UNDISCH_TAC `(x:real^N) IN ball(a,rho)` THEN
      REWRITE_TAC[IN_BALL] THEN UNDISCH_TAC `rho + e < rho1` THEN CONV_TAC NORM_ARITH;
      ALL_TAC] THEN
    EXPAND_TAC "W" THEN ASM_REWRITE_TAC[] THEN USE_THEN "eqv" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(W:real^N->real^K) IN lspace (:real^N) (&2)` ASSUME_TAC THENL
   [EXPAND_TAC "W" THEN SIMP_TAC[WAN_LSPACE_RESTRICT_UNIV; REAL_ARITH `&0 < &2`; ETA_AX] THEN
    MATCH_MP_TAC LSPACE_SUBSET THEN EXISTS_TAC `ball(a:real^N,r)` THEN
    ASM_SIMP_TAC[WAN_WD_WORKS; LEBESGUE_MEASURABLE_BALL; ETA_AX] THEN
    MATCH_MP_TAC SUBSET_BALL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`e:real`; `W:real^N->real^K`] WAN_MOLL_L2) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `drop(integral (:real^N) (\x. lift(norm(wan_moll e (W:real^N->real^K) x) pow 2)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `drop(integral (ball(a:real^N,rho))
                       (\x. lift(norm(wan_moll e (W:real^N->real^K) x) pow 2)))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_EQ_IMP_LE THEN AP_TERM_TAC THEN MATCH_MP_TAC INTEGRAL_EQ THEN
      ASM_SIMP_TAC[];
      MATCH_MP_TAC INTEGRAL_SUBSET_DROP_LE THEN
      REWRITE_TAC[SUBSET_UNIV; LIFT_DROP; REAL_LE_POW_2] THEN
      CONJ_TAC THEN MATCH_MP_TAC WAN_LSPACE2_SQNORM_INTEGRABLE THEN
      ASM_REWRITE_TAC[ETA_AX] THEN
      MATCH_MP_TAC LSPACE_SUBSET THEN EXISTS_TAC `(:real^N)` THEN
      ASM_REWRITE_TAC[LEBESGUE_MEASURABLE_BALL; SUBSET_UNIV]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `drop(integral (:real^N) (\x. lift(norm((W:real^N->real^K) x) pow 2)))` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `(\x. lift(norm((W:real^N->real^K) x) pow 2)) =
    (\x. if x IN ball(a,rho1)
         then lift(norm(wan_wd (ball(a,r)) i (g:real^N->real^K) x) pow 2) else vec 0)`
  SUBST1_TAC THENL
   [EXPAND_TAC "W" THEN REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN COND_CASES_TAC THEN
    REWRITE_TAC[NORM_0] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[LIFT_NUM];
    ALL_TAC] THEN
  REWRITE_TAC[INTEGRAL_RESTRICT_UNIV] THEN
  MATCH_MP_TAC INTEGRAL_SUBSET_DROP_LE THEN REWRITE_TAC[LIFT_DROP; REAL_LE_POW_2] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SUBSET_BALL THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC WAN_LSPACE2_SQNORM_INTEGRABLE THEN
    MATCH_MP_TAC LSPACE_SUBSET THEN EXISTS_TAC `ball(a:real^N,r)` THEN
    ASM_SIMP_TAC[WAN_WD_WORKS; LEBESGUE_MEASURABLE_BALL; ETA_AX] THEN
    MATCH_MP_TAC SUBSET_BALL THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC WAN_LSPACE2_SQNORM_INTEGRABLE THEN ASM_SIMP_TAC[WAN_WD_WORKS; ETA_AX]]);;

(* ========================================================================= *)
(* The Poisson integral h of g has finite energy: on                        *)
(* ball(a,rho') compare h with the Poisson integral H of a smooth           *)
(* approximation on a slightly larger disc (maximum principle and interior  *)
(* gradient bounds), then monotone convergence; minimality by               *)
(* orthogonality; WAN_DIRICHLET_DISC.                                        *)
(* ========================================================================= *)

let WANL_DD_MAXP_ABS = prove
 (`!(a:real^N) r (v:real^N->real) M.
        &0 < r /\ (\x. lift(v x)) continuous_on cball(a,r) /\
        smooth_map_on (ball(a,r)) (\x. lift(v x)) /\
        (!x. x IN ball(a,r) ==> llap (\y:real^N. mat 1) v x = &0) /\
        (!y. y IN sphere(a,r) ==> abs(v y) <= M)
        ==> !x. x IN cball(a,r) ==> abs(v x) <= M`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`a:real^N`; `r:real`; `v:real^N->real`; `M:real`] WANL_MAXP_SUB) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_REFL] THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `abs x <= m ==> x <= m`) THEN ASM_SIMP_TAC[];
    DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC] THEN
  MP_TAC(ISPECL [`a:real^N`; `r:real`; `\x. --((v:real^N->real) x)`; `M:real`]
         WANL_MAXP_SUB) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[LIFT_NEG] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_NEG THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC SMOOTH_MAP_ON_NEG_OPEN THEN ASM_REWRITE_TAC[OPEN_BALL];
      X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(\x. --((v:real^N->real) x)) = (\z. --(&1) * v z + &0 * v z)`
      SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
      MP_TAC(ISPECL [`ball(a:real^N,r)`; `v:real^N->real`; `v:real^N->real`;
                     `--(&1)`; `&0`; `y:real^N`] WANL_LLAP_LINEAR) THEN
      ASM_REWRITE_TAC[OPEN_BALL] THEN DISCH_THEN SUBST1_TAC THEN
      MP_TAC(C MATCH_MP (ASSUME `(y:real^N) IN ball(a,r)`)
               (ASSUME `!x. x IN ball(a:real^N,r) ==> llap (\y:real^N. mat 1) v x = &0`)) THEN
      ABBREV_TAC `L = llap (\z:real^N. mat 1) v y` THEN REAL_ARITH_TAC;
      X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
      MATCH_MP_TAC(REAL_ARITH `abs x <= m ==> --x <= m`) THEN ASM_SIMP_TAC[]];
    DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

(* Near the sphere a continuous map vanishing on it is small.               *)

let WANL_DD_NEAR_SPHERE = prove
 (`!(a:real^N) r (w:real^N->real^K) eta.
        &0 < r /\ w continuous_on cball(a,r) /\ (!x. x IN sphere(a,r) ==> w x = vec 0) /\
        &0 < eta
        ==> ?del. &0 < del /\
                  !x. x IN cball(a,r) /\ r - del < norm(x - a) ==> norm(w x) < eta`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`w:real^N->real^K`; `cball(a:real^N,r)`] COMPACT_UNIFORMLY_CONTINUOUS) THEN
  ASM_REWRITE_TAC[COMPACT_CBALL; uniformly_continuous_on] THEN
  DISCH_THEN(MP_TAC o SPEC `eta:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `min d (r / &2)` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `x:real^N` THEN STRIP_TAC THEN
  ABBREV_TAC `n = norm(x - a:real^N)` THEN
  SUBGOAL_THEN `&0 < n /\ n <= r` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(x:real^N) IN cball(a,r)` THEN REWRITE_TAC[IN_CBALL; dist] THEN
    ONCE_REWRITE_TAC[NORM_SUB] THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `x0 = a + (r / n) % (x - a:real^N)` THEN
  SUBGOAL_THEN `x0 - x:real^N = (r / n - &1) % (x - a)` ASSUME_TAC THENL
   [EXPAND_TAC "x0" THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `x0 - a:real^N = (r / n) % (x - a)` ASSUME_TAC THENL
   [EXPAND_TAC "x0" THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `norm(x0 - a:real^N) = r /\ norm(x0 - x:real^N) = r - n` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_MUL] THEN
    SUBGOAL_THEN `&1 <= r / n` ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_ARITH `&1 <= x ==> abs x = x /\ abs(x - &1) = x - &1`] THEN
    UNDISCH_TAC `&0 < n` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `(w:real^N->real^K) x0 = vec 0` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_SPHERE; dist] THEN
    ONCE_REWRITE_TAC[NORM_SUB] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `dist((w:real^N->real^K) x,w x0) < eta` MP_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[IN_CBALL; dist] THEN ONCE_REWRITE_TAC[NORM_SUB] THEN
      ASM_REWRITE_TAC[REAL_LE_REFL];
      REWRITE_TAC[dist] THEN ONCE_REWRITE_TAC[NORM_SUB] THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC];
    ASM_REWRITE_TAC[DIST_0]]);;

let WANL_DD_DPART_SUB = prove
 (`!(f:real^N->real) g y i.
        (\x. lift(f x)) differentiable (at y) /\ (\x. lift(g x)) differentiable (at y)
        ==> wan_dpart i (\x. f x - g x) y = wan_dpart i f y - wan_dpart i g y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[wan_dpart; LIFT_SUB; GSYM DROP_SUB] THEN
  AP_TERM_TAC THEN
  SUBGOAL_THEN
   `((\x. lift((f:real^N->real) x) - lift(g x)) has_derivative
     (\h. frechet_derivative (\x. lift(f x)) (at y) h -
          frechet_derivative (\x. lift(g x)) (at y) h)) (at y)`
  MP_TAC THENL
   [MATCH_MP_TAC HAS_DERIVATIVE_SUB THEN
    ASM_REWRITE_TAC[ETA_AX; GSYM FRECHET_DERIVATIVE_WORKS];
    DISCH_THEN(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN REWRITE_TAC[]]);;

let WANL_DD_SQ_COMPARE = prove
 (`!(u:real^K) v.
        (!j. 1 <= j /\ j <= dimindex(:K) ==> abs((u - v)$j) <= &1)
        ==> norm(v) pow 2 <= &2 * norm(u) pow 2 + &2 * &(dimindex(:K)) pow 2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `norm(u - v:real^K) <= &(dimindex(:K))` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum(1..dimindex(:K)) (\j. abs((u - v:real^K)$j))` THEN
    REWRITE_TAC[NORM_LE_L1] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum(1..dimindex(:K)) (\j. &1)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUM_LE_NUMSEG THEN ASM_SIMP_TAC[];
      REWRITE_TAC[SUM_CONST_NUMSEG; ADD_SUB; REAL_MUL_RID; REAL_LE_REFL]];
    ALL_TAC] THEN
  SUBGOAL_THEN `norm(v:real^K) <= norm(u:real^K) + &(dimindex(:K))` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`u:real^K`; `v:real^K`] NORM_TRIANGLE_SUB) THEN
    POP_ASSUM MP_TAC THEN CONV_TAC NORM_ARITH;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(norm(u:real^K) + &(dimindex(:K))) pow 2` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[NORM_POS_LE];
    MP_TAC(SPEC `norm(u:real^K) - &(dimindex(:K))` REAL_LE_POW_2) THEN
    REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC]);;

(* Interior closeness of gradients of two harmonic maps.                    *)

let WANL_DD_GRAD_CLOSE = prove
 (`?C. &0 < C /\
       !(U:real^N->bool) (H:real^N->real^K) h y d M i j.
          open U /\ smooth_map_on U H /\ smooth_map_on U h /\
          (!x j. x IN U /\ 1 <= j /\ j <= dimindex(:K)
                 ==> llap (\y:real^N. mat 1) (\y. H y$j) x = &0 /\
                     llap (\y:real^N. mat 1) (\y. h y$j) x = &0) /\
          &0 < d /\ cball(y,&2 * d) SUBSET U /\
          (!z. z IN ball(y,&2 * d) ==> abs(H z$j - h z$j) <= M) /\
          1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:K)
          ==> abs((partial_derivative i H y - partial_derivative i h y)$j) <= C * M / d`,
  X_CHOOSE_THEN `C:real` STRIP_ASSUME_TAC (INST_TYPE [`:N`,`:N`] WANL_DD_DPART_SUP) THEN
  EXISTS_TAC `C:real` THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(y:real^N) IN U` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
    REWRITE_TAC[CENTRE_IN_CBALL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on U (\x. lift((H:real^N->real^K) x$j)) /\
    smooth_map_on U (\x. lift((h:real^N->real^K) x$j))`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[SMOOTH_MAP_ON_LIFT_COMPONENT]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(partial_derivative i (H:real^N->real^K) y - partial_derivative i h y)$j =
    wan_dpart i (\x. H x$j - (h:real^N->real^K) x$j) y`
  SUBST1_TAC THENL
   [REWRITE_TAC[VECTOR_SUB_COMPONENT] THEN
    MP_TAC(BETA_RULE(ISPECL [`\x. (H:real^N->real^K) x$j`; `\x. (h:real^N->real^K) x$j`;
                   `y:real^N`; `i:num`] WANL_DD_DPART_SUB)) THEN
    ANTS_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
      EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
      DISCH_THEN SUBST1_TAC] THEN
    BINOP_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC WANL_DPART_COMPONENT THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`U:real^N->bool`; `\x. (H:real^N->real^K) x$j - (h:real^N->real^K) x$j`;
                                `y:real^N`; `d:real`; `&0`; `M:real`; `i:num`]) THEN
  REWRITE_TAC[REAL_SUB_RZERO] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[LIFT_SUB] THEN CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(\x. (H:real^N->real^K) x$j - (h:real^N->real^K) x$j) = (\z. &1 * H z$j + --(&1) * h z$j)`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `\x. (H:real^N->real^K) x$j`; `\x. (h:real^N->real^K) x$j`;
                   `&1`; `--(&1)`; `x:real^N`] WANL_LLAP_LINEAR) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    SUBGOAL_THEN
     `llap (\y:real^N. mat 1) (\y. (H:real^N->real^K) y$j) x = &0 /\
      llap (\y:real^N. mat 1) (\y. (h:real^N->real^K) y$j) x = &0`
    MP_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    ABBREV_TAC `L1 = llap (\z:real^N. mat 1) (\y. (H:real^N->real^K) y$j) x` THEN
    ABBREV_TAC `L2 = llap (\z:real^N. mat 1) (\y. (h:real^N->real^K) y$j) x` THEN
    REAL_ARITH_TAC]);;

(* The local energy bound: for rho' < r the energy of the Poisson integral   *)
(* of g on ball(a,rho') is at most 2 E_r(g) + 2 N K^2 |B(a,r)|.             *)

let WANL_DD_LOCAL_ENERGY = prove
 (`!(a:real^2) r (g:real^2->real^K) rho'.
        &0 < r /\ g continuous_on cball(a,r) /\ wan_w12 (ball(a,r)) g /\
        &0 < rho' /\ rho' < r
        ==> sum(1..dimindex(:2))
              (\i. drop(integral (ball(a,rho'))
                     (\x. lift(norm(partial_derivative i (wanl_dsol a r g) x) pow 2)))) <=
            &2 * wan_dir (ball(a,r)) g +
            &2 * &(dimindex(:2)) * &(dimindex(:K)) pow 2 * measure(ball(a:real^2,r))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(g:real^2->real^K) continuous_on sphere(a,r)` ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `cball(a:real^2,r)` THEN
    ASM_REWRITE_TAC[SPHERE_SUBSET_CBALL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`a:real^2`; `r:real`; `g:real^2->real^K`] WANL_DSOL_SMOOTH) THEN
  MP_TAC(ISPECL [`a:real^2`; `r:real`; `g:real^2->real^K`] WANL_DSOL_CONTINUOUS) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `h = wanl_dsol a r (g:real^2->real^K)` THEN
  REPEAT STRIP_TAC THEN
  X_CHOOSE_THEN `C:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "close"))
    (INST_TYPE [`:2`,`:N`] WANL_DD_GRAD_CLOSE) THEN
  ABBREV_TAC `d0 = (r - rho') / &2` THEN
  SUBGOAL_THEN `&0 < d0 /\ rho' + d0 < r` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "d0" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `eta = d0 / (&8 * C + &1)` THEN
  SUBGOAL_THEN `&0 < eta /\ C * (&2 * eta) / (d0 / &4) <= &1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "eta" THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `C * (&2 * d0 / (&8 * C + &1)) / (d0 / &4) = (&8 * C) / (&8 * C + &1)`
    SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < d0` THEN UNDISCH_TAC `&0 < C` THEN CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `&0 < C ==> &0 < &8 * C + &1`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`a:real^2`; `r:real`; `\x. (g:real^2->real^K) x - h x`; `eta:real`]
         WANL_DD_NEAR_SPHERE) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[CONTINUOUS_ON_SUB; VECTOR_SUB_REFL]; ALL_TAC] THEN
  REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `del:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `rho = max (rho' + d0) (r - del / &2)` THEN
  SUBGOAL_THEN `rho' + d0 <= rho /\ rho < r /\ r - del < rho /\ &0 < rho`
  STRIP_ASSUME_TAC THENL [EXPAND_TAC "rho" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`a:real^2`; `r:real`; `rho:real`; `g:real^2->real^K`; `eta:real`]
         WANL_DD_APPROX) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `G:real^2->real^K` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(G:real^2->real^K) continuous_on sphere(a,rho)` ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON; SUBSET_UNIV];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(:real^2)`; `a:real^2`; `rho:real`; `G:real^2->real^K`]
         WANL_DD_SMOOTH_DIRICHLET) THEN
  MP_TAC(ISPECL [`a:real^2`; `rho:real`; `G:real^2->real^K`] WANL_DSOL_SMOOTH) THEN
  MP_TAC(ISPECL [`a:real^2`; `rho:real`; `G:real^2->real^K`] WANL_DSOL_CONTINUOUS) THEN
  ASM_REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV] THEN
  ABBREV_TAC `H = wanl_dsol a rho (G:real^2->real^K)` THEN
  REPEAT STRIP_TAC THEN
  (* the energy of H on ball(a,rho) *)
  SUBGOAL_THEN
   `sum(1..dimindex(:2))
      (\i. drop(integral (ball(a,rho))
             (\x. lift(norm(partial_derivative i (H:real^2->real^K) x) pow 2)))) <=
    wan_dir (ball(a,r)) (g:real^2->real^K)`
  ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  (* componentwise closeness of H and h on cball(a,rho) *)
  SUBGOAL_THEN
   `!j. 1 <= j /\ j <= dimindex(:K)
        ==> !x. x IN cball(a,rho)
                ==> abs((\x. (H:real^2->real^K) x$j - (h:real^2->real^K) x$j) x) <= &2 * eta`
  ASSUME_TAC THENL
   [X_GEN_TAC `j:num` THEN STRIP_TAC THEN MATCH_MP_TAC WANL_DD_MAXP_ABS THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `ball(a:real^2,rho) SUBSET ball(a,r) /\ cball(a:real^2,rho) SUBSET cball(a,r)`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL [MATCH_MP_TAC SUBSET_BALL; MATCH_MP_TAC SUBSET_CBALL] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `smooth_map_on (ball(a,rho)) (\x. lift((H:real^2->real^K) x$j)) /\
      smooth_map_on (ball(a,rho)) (\x. lift((h:real^2->real^K) x$j))`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_LIFT_COMPONENT THEN
      REWRITE_TAC[OPEN_BALL] THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `ball(a:real^2,r)` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[LIFT_SUB] THEN MATCH_MP_TAC CONTINUOUS_ON_SUB THEN CONJ_TAC THEN
      MATCH_MP_TAC CONTINUOUS_ON_LIFT_COMPONENT_COMPOSE THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `cball(a:real^2,r)` THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[LIFT_SUB] THEN MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN
      ASM_REWRITE_TAC[OPEN_BALL];
      X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(\x. (H:real^2->real^K) x$j - (h:real^2->real^K) x$j) =
                    (\z. &1 * H z$j + --(&1) * h z$j)`
      SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
      MP_TAC(ISPECL [`ball(a:real^2,rho)`; `\x. (H:real^2->real^K) x$j`;
                     `\x. (h:real^2->real^K) x$j`; `&1`; `--(&1)`; `x:real^2`]
             WANL_LLAP_LINEAR) THEN
      ASM_REWRITE_TAC[OPEN_BALL] THEN DISCH_THEN SUBST1_TAC THEN
      SUBGOAL_THEN `(x:real^2) IN ball(a,r)` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN
       `llap (\y:real^2. mat 1) (\y. (H:real^2->real^K) y$j) x = &0 /\
        llap (\y:real^2. mat 1) (\y. (h:real^2->real^K) y$j) x = &0`
      MP_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
      ABBREV_TAC `L1 = llap (\z:real^2. mat 1) (\y. (H:real^2->real^K) y$j) x` THEN
      ABBREV_TAC `L2 = llap (\z:real^2. mat 1) (\y. (h:real^2->real^K) y$j) x` THEN
      REAL_ARITH_TAC;
      X_GEN_TAC `y:real^2` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(y:real^2) IN cball(a,rho) /\ y IN cball(a,r) /\ norm(y - a) = rho`
      STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `(y:real^2) IN sphere(a,rho)` THEN
        REWRITE_TAC[IN_SPHERE; IN_CBALL; dist] THEN
        MP_TAC(ISPECL [`y:real^2`; `a:real^2`] NORM_SUB) THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `(H:real^2->real^K) y = G y` SUBST1_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `norm((G:real^2->real^K) y - (h:real^2->real^K) y)` THEN CONJ_TAC THENL
       [MP_TAC(ISPECL [`(G:real^2->real^K) y - (h:real^2->real^K) y`; `j:num`]
               COMPONENT_LE_NORM) THEN
        ASM_REWRITE_TAC[VECTOR_SUB_COMPONENT];
        ALL_TAC] THEN
      MATCH_MP_TAC(NORM_ARITH
       `!G g h:real^K eta. norm(G - g) <= eta /\ norm(g - h) < eta
                           ==> norm(G - h) <= &2 * eta`) THEN
      EXISTS_TAC `(g:real^2->real^K) y` THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `ball(a:real^2,rho') SUBSET ball(a,rho) /\ ball(a:real^2,rho) SUBSET ball(a,r) /\
                cball(a:real^2,rho') SUBSET ball(a,r)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SUBSET_BALL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC SUBSET_BALL THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[SUBSET; IN_CBALL; IN_BALL] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* pointwise comparison of the gradients on ball(a,rho') *)
  SUBGOAL_THEN
   `!i y. 1 <= i /\ i <= dimindex(:2) /\ y IN ball(a,rho')
          ==> norm(partial_derivative i (h:real^2->real^K) y) pow 2 <=
              &2 * norm(partial_derivative i (H:real^2->real^K) y) pow 2 +
              &2 * &(dimindex(:K)) pow 2`
  (LABEL_TAC "pw") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC WANL_DD_SQ_COMPARE THEN
    X_GEN_TAC `j:num` THEN STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `C * (&2 * eta) / (d0 / &4)` THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "close" MATCH_MP_TAC THEN EXISTS_TAC `ball(a:real^2,rho)` THEN
    ASM_REWRITE_TAC[OPEN_BALL] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `ball(a:real^2,r)` THEN
      ASM_REWRITE_TAC[];
      REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN
      SUBGOAL_THEN `(x:real^2) IN ball(a,r)` (fun th -> ASM_SIMP_TAC[th]) THEN
      ASM SET_TAC[];
      ASM_REAL_ARITH_TAC;
      REWRITE_TAC[SUBSET; IN_CBALL; IN_BALL] THEN X_GEN_TAC `z:real^2` THEN
      UNDISCH_TAC `(y:real^2) IN ball(a,rho')` THEN REWRITE_TAC[IN_BALL] THEN
      UNDISCH_TAC `rho' + d0 <= rho` THEN UNDISCH_TAC `&0 < d0` THEN
      CONV_TAC NORM_ARITH;
      X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o check (fun th -> is_forall(concl th) &&
        can (find_term (fun u -> u = `&2 * eta`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `z:real^2`) THEN
      ANTS_TAC THENL
       [UNDISCH_TAC `(z:real^2) IN ball(y,&2 * d0 / &4)` THEN
        UNDISCH_TAC `(y:real^2) IN ball(a,rho')` THEN REWRITE_TAC[IN_BALL; IN_CBALL] THEN
        UNDISCH_TAC `rho' + d0 <= rho` THEN UNDISCH_TAC `&0 < d0` THEN
        CONV_TAC NORM_ARITH;
        REWRITE_TAC[]]];
    ALL_TAC] THEN
  (* integrated comparison *)
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= dimindex(:2)
        ==> drop(integral (ball(a,rho'))
                   (\x. lift(norm(partial_derivative i (h:real^2->real^K) x) pow 2))) <=
            &2 * drop(integral (ball(a,rho))
                   (\x. lift(norm(partial_derivative i (H:real^2->real^K) x) pow 2))) +
            &2 * &(dimindex(:K)) pow 2 * measure(ball(a:real^2,r))`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `(\x. partial_derivative i (H:real^2->real^K) x) IN lspace (ball(a,rho')) (&2) /\
      (\x. partial_derivative i (H:real^2->real^K) x) IN lspace (ball(a,rho)) (&2)`
    STRIP_ASSUME_TAC THENL
     [MATCH_MP_TAC(TAUT `b /\ (b ==> a) ==> a /\ b`) THEN CONJ_TAC THENL
       [ASM_SIMP_TAC[];
        DISCH_TAC THEN MATCH_MP_TAC LSPACE_SUBSET THEN EXISTS_TAC `ball(a:real^2,rho)` THEN
        ASM_REWRITE_TAC[LEBESGUE_MEASURABLE_BALL]];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `(\x. lift(norm(partial_derivative i (h:real^2->real^K) x) pow 2)) integrable_on
      ball(a,rho')`
    ASSUME_TAC THENL
     [MP_TAC(ISPECL [`\x. lift(norm(partial_derivative i (h:real^2->real^K) x) pow 2)`;
                     `a:real^2`; `rho':real`] WANL_CONT_CBALL_INTEGRABLE) THEN
      ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
      REWRITE_TAC[NORM_POW_2] THEN MATCH_MP_TAC CONTINUOUS_ON_LIFT_DOT2 THEN
      MATCH_MP_TAC(TAUT `a ==> a /\ a`) THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `ball(a:real^2,r)` THEN
      ASM_REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_PARTIAL_DERIVATIVE THEN ASM_REWRITE_TAC[OPEN_BALL];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `(\x. lift(norm(partial_derivative i (H:real^2->real^K) x) pow 2)) integrable_on
      ball(a,rho') /\
      (\x. lift(norm(partial_derivative i (H:real^2->real^K) x) pow 2)) integrable_on
      ball(a,rho)`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC WAN_LSPACE2_SQNORM_INTEGRABLE THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC
     `drop(integral (ball(a:real^2,rho'))
             (\x. &2 % lift(norm(partial_derivative i (H:real^2->real^K) x) pow 2) +
                  lift(&2 * &(dimindex(:K)) pow 2)))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC INTEGRAL_DROP_LE THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC INTEGRABLE_ADD THEN
        ASM_SIMP_TAC[INTEGRABLE_CMUL; INTEGRABLE_ON_CONST; MEASURABLE_BALL];
        X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
        REWRITE_TAC[DROP_ADD; DROP_CMUL; LIFT_DROP] THEN
        USE_THEN "pw" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    ASM_SIMP_TAC[INTEGRAL_ADD; INTEGRABLE_CMUL; INTEGRABLE_ON_CONST; MEASURABLE_BALL;
                 INTEGRAL_CMUL; INTEGRAL_CONST_GEN; DROP_ADD; DROP_CMUL; LIFT_DROP] THEN
    SUBGOAL_THEN
     `drop(integral (ball(a:real^2,rho'))
             (\x. lift(norm(partial_derivative i (H:real^2->real^K) x) pow 2))) <=
      drop(integral (ball(a,rho))
             (\x. lift(norm(partial_derivative i H x) pow 2)))`
    ASSUME_TAC THENL
     [MATCH_MP_TAC INTEGRAL_SUBSET_DROP_LE THEN ASM_REWRITE_TAC[LIFT_DROP; REAL_LE_POW_2];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `measure(ball(a:real^2,rho')) * &2 * &(dimindex(:K)) pow 2 <=
      measure(ball(a:real^2,r)) * &2 * &(dimindex(:K)) pow 2`
    ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC MEASURE_SUBSET THEN REWRITE_TAC[MEASURABLE_BALL] THEN
        MATCH_MP_TAC SUBSET_BALL THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
        MATCH_MP_TAC REAL_POW_LE THEN REWRITE_TAC[REAL_POS]];
      ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `sum(1..dimindex(:2))
      (\i. &2 * drop(integral (ball(a,rho))
                 (\x. lift(norm(partial_derivative i (H:real^2->real^K) x) pow 2))) +
           &2 * &(dimindex(:K)) pow 2 * measure(ball(a:real^2,r)))` THEN
  CONJ_TAC THENL [MATCH_MP_TAC SUM_LE_NUMSEG THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[SUM_ADD_NUMSEG; SUM_LMUL; SUM_CONST_NUMSEG; ADD_SUB] THEN
  MATCH_MP_TAC(REAL_ARITH `x <= y /\ c = d ==> &2 * x + c <= &2 * y + d`) THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[]; CONV_TAC REAL_RING]);;

(* Monotone convergence: the partials of the Poisson integral are L^2.      *)

let WANL_DD_PARTIAL_L2 = prove
 (`!(a:real^2) r (g:real^2->real^K).
        &0 < r /\ g continuous_on cball(a,r) /\ wan_w12 (ball(a,r)) g
        ==> !i. 1 <= i /\ i <= dimindex(:2)
                ==> (\x. partial_derivative i (wanl_dsol a r g) x) IN
                    lspace (ball(a,r)) (&2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(g:real^2->real^K) continuous_on sphere(a,r)` ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `cball(a:real^2,r)` THEN
    ASM_REWRITE_TAC[SPHERE_SUBSET_CBALL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`a:real^2`; `r:real`; `g:real^2->real^K`] WANL_DSOL_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `h = wanl_dsol a r (g:real^2->real^K)` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(\x. partial_derivative i (h:real^2->real^K) x) continuous_on ball(a,r)`
  ASSUME_TAC THENL
   [REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_PARTIAL_DERIVATIVE THEN ASM_REWRITE_TAC[OPEN_BALL];
    ALL_TAC] THEN
  ABBREV_TAC `Fq = \x. lift(norm(partial_derivative i (h:real^2->real^K) x) pow 2)` THEN
  ABBREV_TAC `t = \k. r * (&1 - inv(&k + &2))` THEN
  SUBGOAL_THEN `!k. &0 < (t:num->real) k /\ (t:num->real) k < r /\ (t:num->real) k <= (t:num->real)(SUC k)` (LABEL_TAC "t") THENL
   [GEN_TAC THEN EXPAND_TAC "t" THEN REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN
    SUBGOAL_THEN `&0 < inv(&k + &2) /\ inv(&k + &2) < &1 /\ inv((&k + &1) + &2) <= inv(&k + &2)`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_INV THEN REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_INV_LT_1 THEN REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_INV2 THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC(REAL_ARITH `&0 < r * e ==> r * (&1 - e) < r`) THEN
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!k. ball(a:real^2,(t:num->real) k) SUBSET ball(a,r) /\ cball(a:real^2,(t:num->real) k) SUBSET ball(a,r)`
  (LABEL_TAC "sub") THENL
   [GEN_TAC THEN USE_THEN "t" (MP_TAC o SPEC `k:num`) THEN STRIP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUBSET_BALL THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[SUBSET; IN_CBALL; IN_BALL] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!k. (Fq:real^2->real^1) integrable_on ball(a,(t:num->real) k)` ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "Fq" THEN
    MP_TAC(ISPECL [`\x. lift(norm(partial_derivative i (h:real^2->real^K) x) pow 2)`;
                   `a:real^2`; `(t:num->real) k`] WANL_CONT_CBALL_INTEGRABLE) THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
    REWRITE_TAC[NORM_POW_2] THEN MATCH_MP_TAC CONTINUOUS_ON_LIFT_DOT2 THEN
    MATCH_MP_TAC(TAUT `a ==> a /\ a`) THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `ball(a:real^2,r)` THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\k x. if x IN ball(a:real^2,(t:num->real) k) then (Fq:real^2->real^1) x else vec 0`;
                 `Fq:real^2->real^1`; `ball(a:real^2,r)`] MONOTONE_CONVERGENCE_INCREASING) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [X_GEN_TAC `k:num` THEN
      MP_TAC(ISPECL [`Fq:real^2->real^1`; `ball(a:real^2,(t:num->real) k)`; `ball(a:real^2,r)`]
             INTEGRABLE_RESTRICT) THEN
      ASM_SIMP_TAC[];
      MAP_EVERY X_GEN_TAC [`k:num`; `x:real^2`] THEN DISCH_TAC THEN
      USE_THEN "t" (MP_TAC o SPEC `k:num`) THEN STRIP_TAC THEN
      SUBGOAL_THEN `&0 <= drop((Fq:real^2->real^1) x)` ASSUME_TAC THENL
       [EXPAND_TAC "Fq" THEN REWRITE_TAC[LIFT_DROP; REAL_LE_POW_2]; ALL_TAC] THEN
      REPEAT COND_CASES_TAC THEN REWRITE_TAC[DROP_VEC; REAL_LE_REFL] THEN
      TRY(ASM_REAL_ARITH_TAC) THEN
      UNDISCH_TAC `(x:real^2) IN ball(a,(t:num->real) k)` THEN
      UNDISCH_TAC `~((x:real^2) IN ball(a,(t:num->real)(SUC k)))` THEN
      REWRITE_TAC[IN_BALL] THEN ASM_REAL_ARITH_TAC;
      X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN MATCH_MP_TAC LIM_EVENTUALLY THEN
      REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
      SUBGOAL_THEN `?N. r / (r - dist(a:real^2,x)) < &N` (X_CHOOSE_TAC `N:num`) THENL
       [REWRITE_TAC[REAL_ARCH_LT]; ALL_TAC] THEN
      EXISTS_TAC `N:num` THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(x:real^2) IN ball(a,(t:num->real) k)` (fun th -> REWRITE_TAC[th]) THEN
      UNDISCH_TAC `(x:real^2) IN ball(a,r)` THEN REWRITE_TAC[IN_BALL] THEN DISCH_TAC THEN
      EXPAND_TAC "t" THEN
      SUBGOAL_THEN `r * inv(&k + &2) < r - dist(a:real^2,x)` MP_TAC THENL
       [ASM_SIMP_TAC[GSYM real_div; REAL_LT_LDIV_EQ; REAL_ARITH `&0 < &k + &2`] THEN
        MATCH_MP_TAC REAL_LTE_TRANS THEN
        EXISTS_TAC `(r - dist(a:real^2,x)) * &N` THEN CONJ_TAC THENL
         [UNDISCH_TAC `r / (r - dist(a:real^2,x)) < &N` THEN
          ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_SUB_LT] THEN REAL_ARITH_TAC;
          MATCH_MP_TAC REAL_LE_LMUL THEN
          UNDISCH_TAC `N <= k:num` THEN REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN
          ASM_REAL_ARITH_TAC];
        REAL_ARITH_TAC];
      REWRITE_TAC[bounded; FORALL_IN_GSPEC; IN_UNIV] THEN
      EXISTS_TAC `&2 * wan_dir (ball(a,r)) (g:real^2->real^K) +
                  &2 * &(dimindex(:2)) * &(dimindex(:K)) pow 2 * measure(ball(a:real^2,r))` THEN
      X_GEN_TAC `k:num` THEN
      MP_TAC(ISPECL [`Fq:real^2->real^1`; `ball(a:real^2,(t:num->real) k)`; `ball(a:real^2,r)`]
             INTEGRAL_RESTRICT) THEN
      ASM_SIMP_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      USE_THEN "t" (MP_TAC o SPEC `k:num`) THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`a:real^2`; `r:real`; `g:real^2->real^K`; `(t:num->real) k`]
             WANL_DD_LOCAL_ENERGY) THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(REAL_ARITH `x <= y ==> y <= b ==> x <= b`) THEN
      SUBGOAL_THEN `&0 <= drop(integral (ball(a:real^2,(t:num->real) k)) (Fq:real^2->real^1))` ASSUME_TAC THENL
       [MATCH_MP_TAC INTEGRAL_DROP_POS THEN ASM_REWRITE_TAC[] THEN
        EXPAND_TAC "Fq" THEN REWRITE_TAC[LIFT_DROP; REAL_LE_POW_2];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[NORM_1; REAL_ARITH `&0 <= x ==> abs x = x`] THEN
      ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`] THEN
      MP_TAC(ISPECL [`\i. drop(integral (ball(a:real^2,(t:num->real) k))
                          (\x. lift(norm(partial_derivative i (h:real^2->real^K) x) pow 2)))`;
                     `sum(1..dimindex(:2))
                        (\i. drop(integral (ball(a:real^2,(t:num->real) k))
                          (\x. lift(norm(partial_derivative i (h:real^2->real^K) x) pow 2))))`;
                     `1..dimindex(:2)`] SUM_POS_BOUND) THEN
      REWRITE_TAC[FINITE_NUMSEG; REAL_LE_REFL; IN_NUMSEG] THEN ANTS_TAC THENL
       [X_GEN_TAC `j:num` THEN STRIP_TAC THEN MATCH_MP_TAC INTEGRAL_DROP_POS THEN
        REWRITE_TAC[LIFT_DROP; REAL_LE_POW_2] THEN
        MP_TAC(ISPECL [`\x. lift(norm(partial_derivative j (h:real^2->real^K) x) pow 2)`;
                       `a:real^2`; `(t:num->real) k`] WANL_CONT_CBALL_INTEGRABLE) THEN
        ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
        REWRITE_TAC[NORM_POW_2] THEN MATCH_MP_TAC CONTINUOUS_ON_LIFT_DOT2 THEN
        MATCH_MP_TAC(TAUT `a ==> a /\ a`) THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
        EXISTS_TAC `ball(a:real^2,r)` THEN ASM_REWRITE_TAC[ETA_AX] THEN
        MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
        MATCH_MP_TAC SMOOTH_MAP_ON_PARTIAL_DERIVATIVE THEN ASM_REWRITE_TAC[OPEN_BALL];
        DISCH_THEN(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "Fq" THEN
        REWRITE_TAC[]]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1) THEN EXPAND_TAC "Fq" THEN DISCH_TAC THEN
  REWRITE_TAC[lspace; IN_ELIM_THM; RPOW_POW] THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
  ASM_REWRITE_TAC[LEBESGUE_MEASURABLE_BALL]);;

(* ------------------------------------------------------------------------- *)
(* The Dirichlet problem on discs: the Poisson integral of g is the energy  *)
(* minimiser in g + W^(1,2)_0.                                               *)
(* ------------------------------------------------------------------------- *)

let WAN_DIRICHLET_DISC = prove
 (`!kk:K->bool. WAN_DIRICHLET_DISC_STATEMENT kk`,
  GEN_TAC THEN REWRITE_TAC[WAN_DIRICHLET_DISC_STATEMENT] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(g:real^2->real^K) continuous_on sphere(a,r)` ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `cball(a:real^2,r)` THEN
    ASM_REWRITE_TAC[SPHERE_SUBSET_CBALL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`a:real^2`; `r:real`; `g:real^2->real^K`] WANL_DD_PARTIAL_L2) THEN
  MP_TAC(ISPECL [`a:real^2`; `r:real`; `g:real^2->real^K`] WANL_DSOL_SMOOTH) THEN
  MP_TAC(ISPECL [`a:real^2`; `r:real`; `g:real^2->real^K`] WANL_DSOL_CONTINUOUS) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `h = wanl_dsol a r (g:real^2->real^K)` THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `wan_w12 (ball(a,r)) (h:real^2->real^K)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`(:2)`; `(:K)`] WAN_W12_C1) THEN REWRITE_TAC[WAN_W12_C1_STATEMENT] THEN
    DISCH_THEN(MP_TAC o SPECL [`ball(a:real^2,r)`; `h:real^2->real^K`]) THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
    ASM_REWRITE_TAC[OPEN_BALL] THEN CONJ_TAC THENL
     [UNDISCH_TAC `smooth_map_on (ball(a,r)) (h:real^2->real^K)` THEN SIMP_TAC[smooth_map_on];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`h:real^2->real^K`; `cball(a:real^2,r)`] COMPACT_CONTINUOUS_IMAGE) THEN
    ASM_REWRITE_TAC[COMPACT_CBALL] THEN DISCH_THEN(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
    REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC(INST_TYPE [`:1`,`:P`] LSPACE_BOUNDED_MEASURABLE) THEN
    EXISTS_TAC `\x:real^2. lift B` THEN REPEAT CONJ_TAC THENL
     [REAL_ARITH_TAC;
      MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
      REWRITE_TAC[LEBESGUE_MEASURABLE_BALL] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `cball(a:real^2,r)` THEN ASM_REWRITE_TAC[BALL_SUBSET_CBALL];
      MATCH_MP_TAC LSPACE_CONST THEN REWRITE_TAC[MEASURABLE_BALL];
      X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN REWRITE_TAC[NORM_LIFT] THEN
      MATCH_MP_TAC(REAL_ARITH `x <= b ==> x <= abs b`) THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[BALL_SUBSET_CBALL; SUBSET]];
    ALL_TAC] THEN
  SUBGOAL_THEN `wan_w120 (ball(a,r)) (\x. (h:real^2->real^K) x - g x)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`(:2)`; `(:K)`] WAN_W120_CONT) THEN
    REWRITE_TAC[WAN_W120_CONT_STATEMENT] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_SIMP_TAC[CONTINUOUS_ON_SUB; VECTOR_SUB_REFL] THEN
    MATCH_MP_TAC WAN_W12_SUB THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `h:real^2->real^K` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `v:real^2->real^K` THEN STRIP_TAC THEN
  SUBGOAL_THEN `wan_w120 (ball(a,r)) (\x. (v:real^2->real^K) x - h x)` ASSUME_TAC THENL
   [SUBGOAL_THEN `(\x. (v:real^2->real^K) x - h x) =
                  (\x. (\x. v x - (g:real^2->real^K) x) x - (\x. h x - g x) x)`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM] THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC WAN_W120_SUB THEN ASM_REWRITE_TAC[OPEN_BALL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`ball(a:real^2,r)`; `h:real^2->real^K`; `\x. (v:real^2->real^K) x - h x`]
         WAN_DIR_ADD) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[OPEN_BALL] THEN MATCH_MP_TAC WAN_W12_SUB THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\x. (h:real^2->real^K) x + (\x. v x - h x) x) = v` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN
  MP_TAC(ISPECL [`ball(a:real^2,r)`; `h:real^2->real^K`; `\x. (v:real^2->real^K) x - h x`]
         WANL_DD_ORTHO) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[OPEN_BALL]; DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`ball(a:real^2,r)`; `\x. (v:real^2->real^K) x - h x`] WAN_DIR_POS) THEN
  ANTS_TAC THENL [MATCH_MP_TAC WAN_W12_SUB THEN ASM_REWRITE_TAC[]; REAL_ARITH_TAC]);;

