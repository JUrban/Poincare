(* ========================================================================= *)
(* Unit pc_rfa_lalg: pointwise calculus for the maximum principles of the    *)
(* Ricci flow analysis layer: the second-derivative test (the Laplacian llap *)
(* is <= 0 at a local maximum and >= 0 at a local minimum of a smooth        *)
(* function, for any metric field) and homogeneity of llap on smooth         *)
(* functions.  Sectional curvature bounds and the Rayleigh barrier of the    *)
(* tensor maximum principle are in pc_rfa_sec and pc_rfa_raylap.             *)
(* ========================================================================= *)

needs "src/pc_rfa_talg.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* The second-derivative test.  The one-variable test is adapted from        *)
(* earlier HOL Light work.                                                   *)
(* ========================================================================= *)

let RFA_SECOND_DERIVATIVE_LOCAL_MAX = prove
 (`!f g c e.
        &0 < e /\
        (!t. abs t < e ==> (f has_real_derivative g t) (atreal t)) /\
        (g has_real_derivative c) (atreal (&0)) /\
        (!t. abs t < e ==> f t <= f (&0))
        ==> c <= &0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(g:real->real) (&0) = &0` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_DERIVATIVE_ZERO_MAXMIN THEN
    MAP_EVERY EXISTS_TAC [`f:real->real`; `&0`; `real_interval(--e,e)`] THEN
    REWRITE_TAC[REAL_OPEN_REAL_INTERVAL; IN_REAL_INTERVAL] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
      FIRST_X_ASSUM(MATCH_MP_TAC o check (is_forall o concl)) THEN
      ASM_REAL_ARITH_TAC;
      DISJ1_TAC THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* g is positive just to the right of 0 *)
  UNDISCH_TAC `((g:real->real) has_real_derivative c) (atreal (&0))` THEN
  REWRITE_TAC[HAS_REAL_DERIVATIVE_ATREAL; REALLIM_ATREAL] THEN
  DISCH_THEN(MP_TAC o SPEC `c / &2`) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
  ASM_REWRITE_TAC[REAL_SUB_RZERO] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!y. &0 < y /\ y < d ==> &0 < (g:real->real) y` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `y:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_IMP_NZ] THEN DISCH_TAC THEN
    SUBGOAL_THEN `c / &2 < (g:real->real) y / y` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_RDIV_EQ] THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC `c / &2 * y` THEN
    ASM_SIMP_TAC[REAL_LT_MUL; REAL_HALF];
    ALL_TAC] THEN
  (* the mean value theorem on [0,t] gives f(t) > f(0) *)
  ABBREV_TAC `t = min d e / &2` THEN
  SUBGOAL_THEN `&0 < t /\ t < d /\ t < e` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "t" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`f:real->real`; `g:real->real`; `&0`; `t:real`] REAL_MVT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
      X_GEN_TAC `s:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN DISCH_TAC THEN
      MATCH_MP_TAC REAL_CONTINUOUS_ATREAL_WITHINREAL THEN
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_IMP_CONTINUOUS_ATREAL THEN
      EXISTS_TAC `(g:real->real) s` THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REAL_ARITH_TAC;
      X_GEN_TAC `s:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (find_term (fun u -> u = `has_real_derivative`)) (concl th) &&
        is_forall(concl th))) THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[IN_REAL_INTERVAL; REAL_SUB_RZERO] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `&0 < (g:real->real) z * t` MP_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  SUBGOAL_THEN `(f:real->real) t <= f (&0)` MP_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]);;

let RFA_LINE_DERIVATIVE = prove
 (`!(Fn:real^N->real^1) Fd y v s.
        (Fn has_derivative Fd) (at (y + s % v))
        ==> ((\t. drop(Fn(y + t % v))) has_real_derivative drop(Fd v)) (atreal s)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[HAS_REAL_VECTOR_DERIVATIVE_AT; o_DEF; LIFT_DROP] THEN
  REWRITE_TAC[has_vector_derivative] THEN
  SUBGOAL_THEN `linear(Fd:real^N->real^1)` ASSUME_TAC THENL
   [ASM_MESON_TAC[LRG_HAS_DERIVATIVE_IMP_LINEAR]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(\t:real^1. (Fn:real^N->real^1)(y + drop t % v)) = Fn o (\t. y + drop t % v) /\
    (\h:real^1. drop h % (Fd:real^N->real^1) v) = Fd o (\h. drop h % v)`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM] THEN ASM_MESON_TAC[LINEAR_CMUL]; ALL_TAC] THEN
  MATCH_MP_TAC DIFF_CHAIN_AT THEN REWRITE_TAC[LIFT_DROP] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(\h:real^1. drop h % (v:real^N)) = (\h. vec 0 + drop h % v)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; VECTOR_ADD_LID]; ALL_TAC] THEN
  MATCH_MP_TAC HAS_DERIVATIVE_ADD THEN
  REWRITE_TAC[HAS_DERIVATIVE_CONST] THEN
  MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN MATCH_MP_TAC LINEAR_VMUL_DROP THEN
  REWRITE_TAC[LINEAR_ID]);;

let RFA_HESSIAN_LOCAL_MAX = prove
 (`!W (f:real^N->real) y v.
        open W /\ y IN W /\ smooth_map_on W (\z. lift(f z)) /\
        (!z. z IN W ==> f z <= f y)
        ==> drop(frechet_derivative
                  (\z. frechet_derivative (\w. lift(f w)) (at z) v) (at y) v)
            <= &0`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL]) THEN
  DISCH_THEN(MP_TAC o SPEC `y:real^N`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!t. abs t < r / (norm(v:real^N) + &1) ==> y + t % v IN (W:real^N->bool)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
    REWRITE_TAC[IN_BALL; NORM_ARITH `dist(y:real^N,y + x) = norm x`] THEN
    REWRITE_TAC[NORM_MUL] THEN
    SUBGOAL_THEN `&0 < norm(v:real^N) + &1` ASSUME_TAC THENL
     [MP_TAC(ISPEC `v:real^N` NORM_POS_LE) THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `abs t * (norm(v:real^N) + &1)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN REAL_ARITH_TAC;
      ASM_SIMP_TAC[GSYM REAL_LT_RDIV_EQ]];
    ALL_TAC] THEN
  MATCH_MP_TAC RFA_SECOND_DERIVATIVE_LOCAL_MAX THEN
  EXISTS_TAC `\t. (f:real^N->real)(y + t % v)` THEN
  EXISTS_TAC `\t. drop(frechet_derivative (\w. lift((f:real^N->real) w))
                                          (at (y + t % v)) v)` THEN
  EXISTS_TAC `r / (norm(v:real^N) + &1)` THEN BETA_TAC THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `v:real^N` NORM_POS_LE) THEN REAL_ARITH_TAC;
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`\w. lift((f:real^N->real) w)`;
                   `frechet_derivative (\w. lift((f:real^N->real) w)) (at (y + t % v))`;
                   `y:real^N`; `v:real^N`; `t:real`] RFA_LINE_DERIVATIVE) THEN
    REWRITE_TAC[LIFT_DROP; ETA_AX] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `W:real^N->bool` THEN
    ASM_SIMP_TAC[];
    MP_TAC(ISPECL [`\z. frechet_derivative (\w. lift((f:real^N->real) w)) (at z) v`;
                   `frechet_derivative
                     (\z. frechet_derivative (\w. lift((f:real^N->real) w)) (at z) v)
                     (at y)`;
                   `y:real^N`; `v:real^N`; `&0`] RFA_LINE_DERIVATIVE) THEN
    REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_RID] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `W:real^N->bool` THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_FRECHET_DERIVATIVE];
    REPEAT STRIP_TAC THEN REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_RID] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[]]);;

let RFA_SECOND_DERIVATIVE_EXPAND = prove
 (`!W (Fn:real^N->real^1) y v w.
        open W /\ y IN W /\ smooth_map_on W Fn
        ==> drop(frechet_derivative (\z. frechet_derivative Fn (at z) w) (at y) v) =
            sum(1..dimindex(:N))
             (\i. sum(1..dimindex(:N))
               (\j. v$i * w$j *
                    drop(frechet_derivative
                          (\z. frechet_derivative Fn (at z) (basis j)) (at y)
                          (basis i))))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!z. z IN W
        ==> frechet_derivative (Fn:real^N->real^1) (at z) w =
            vsum(1..dimindex(:N))
              (\j. w$j % frechet_derivative Fn (at z) (basis j))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `linear(frechet_derivative (Fn:real^N->real^1) (at z))`
    ASSUME_TAC THENL
     [MATCH_MP_TAC LRG_HAS_DERIVATIVE_IMP_LINEAR THEN
      EXISTS_TAC `Fn:real^N->real^1` THEN EXISTS_TAC `at(z:real^N)` THEN
      REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
      EXISTS_TAC `W:real^N->bool` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM BASIS_EXPANSION] THEN
    ASM_SIMP_TAC[LINEAR_VSUM; FINITE_NUMSEG; o_DEF; LINEAR_CMUL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!j. (\z. frechet_derivative (Fn:real^N->real^1) (at z) (basis j))
        differentiable (at y)`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `W:real^N->bool` THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_FRECHET_DERIVATIVE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `frechet_derivative (\z. frechet_derivative (Fn:real^N->real^1) (at z) w)
                       (at y) =
    (\h. vsum(1..dimindex(:N))
          (\j. w$j % frechet_derivative
                      (\z. frechet_derivative Fn (at z) (basis j)) (at y) h))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC
     `frechet_derivative
       (\z. vsum(1..dimindex(:N))
              (\j. (w:real^N)$j % frechet_derivative (Fn:real^N->real^1) (at z) (basis j)))
       (at y)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LRG_FRECHET_DERIVATIVE_EQ_OPEN THEN
      EXISTS_TAC `W:real^N->bool` THEN ASM_SIMP_TAC[];
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
      MATCH_MP_TAC HAS_DERIVATIVE_VSUM THEN REWRITE_TAC[FINITE_NUMSEG] THEN
      X_GEN_TAC `j:num` THEN DISCH_TAC THEN BETA_TAC THEN
      MATCH_MP_TAC HAS_DERIVATIVE_CMUL THEN REWRITE_TAC[ETA_AX] THEN
      ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS]];
    ALL_TAC] THEN
  BETA_TAC THEN REWRITE_TAC[DROP_VSUM; o_DEF; DROP_CMUL] THEN
  GEN_REWRITE_TAC RAND_CONV [SUM_SWAP_NUMSEG] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  BETA_TAC THEN
  SUBGOAL_THEN
   `linear(frechet_derivative
            (\z. frechet_derivative (Fn:real^N->real^1) (at z) (basis j)) (at y))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC LRG_HAS_DERIVATIVE_IMP_LINEAR THEN
    EXISTS_TAC `\z. frechet_derivative (Fn:real^N->real^1) (at z) (basis j)` THEN
    EXISTS_TAC `at(y:real^N)` THEN ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP LRG_LINEAR_DROP_EXPAND) THEN
  DISCH_THEN(MP_TAC o SPEC `v:real^N`) THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
  REPEAT STRIP_TAC THEN BETA_TAC THEN REAL_ARITH_TAC);;

let RFA_SECOND_DERIVATIVE_LOCAL_MIN = prove
 (`!f g c e.
        &0 < e /\
        (!t. abs t < e ==> (f has_real_derivative g t) (atreal t)) /\
        (g has_real_derivative c) (atreal (&0)) /\
        (!t. abs t < e ==> f (&0) <= f t)
        ==> &0 <= c`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\t. --((f:real->real) t)`; `\t. --((g:real->real) t)`;
                 `--c:real`; `e:real`] RFA_SECOND_DERIVATIVE_LOCAL_MAX) THEN
  ASM_SIMP_TAC[HAS_REAL_DERIVATIVE_NEG; ETA_AX; REAL_LE_NEG2] THEN
  REAL_ARITH_TAC);;

let RFA_HESSIAN_LOCAL_MIN = prove
 (`!W (f:real^N->real) y v.
        open W /\ y IN W /\ smooth_map_on W (\z. lift(f z)) /\
        (!z. z IN W ==> f y <= f z)
        ==> &0 <= drop(frechet_derivative
                        (\z. frechet_derivative (\w. lift(f w)) (at z) v) (at y) v)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL]) THEN
  DISCH_THEN(MP_TAC o SPEC `y:real^N`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!t. abs t < r / (norm(v:real^N) + &1) ==> y + t % v IN (W:real^N->bool)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
    REWRITE_TAC[IN_BALL; NORM_ARITH `dist(y:real^N,y + x) = norm x`] THEN
    REWRITE_TAC[NORM_MUL] THEN
    SUBGOAL_THEN `&0 < norm(v:real^N) + &1` ASSUME_TAC THENL
     [MP_TAC(ISPEC `v:real^N` NORM_POS_LE) THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `abs t * (norm(v:real^N) + &1)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN REAL_ARITH_TAC;
      ASM_SIMP_TAC[GSYM REAL_LT_RDIV_EQ]];
    ALL_TAC] THEN
  MATCH_MP_TAC RFA_SECOND_DERIVATIVE_LOCAL_MIN THEN
  EXISTS_TAC `\t. (f:real^N->real)(y + t % v)` THEN
  EXISTS_TAC `\t. drop(frechet_derivative (\w. lift((f:real^N->real) w))
                                          (at (y + t % v)) v)` THEN
  EXISTS_TAC `r / (norm(v:real^N) + &1)` THEN BETA_TAC THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `v:real^N` NORM_POS_LE) THEN REAL_ARITH_TAC;
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`\w. lift((f:real^N->real) w)`;
                   `frechet_derivative (\w. lift((f:real^N->real) w)) (at (y + t % v))`;
                   `y:real^N`; `v:real^N`; `t:real`] RFA_LINE_DERIVATIVE) THEN
    REWRITE_TAC[LIFT_DROP; ETA_AX] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `W:real^N->bool` THEN
    ASM_SIMP_TAC[];
    MP_TAC(ISPECL [`\z. frechet_derivative (\w. lift((f:real^N->real) w)) (at z) v`;
                   `frechet_derivative
                     (\z. frechet_derivative (\w. lift((f:real^N->real) w)) (at z) v)
                     (at y)`;
                   `y:real^N`; `v:real^N`; `&0`] RFA_LINE_DERIVATIVE) THEN
    REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_RID] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `W:real^N->bool` THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_FRECHET_DERIVATIVE];
    REPEAT STRIP_TAC THEN REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_RID] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[]]);;

let RFA_LLAP_FRAME_CRITICAL = prove
 (`!U W (G:real^N->real^N^N) f y (S:real^N^N).
        metric_field U G /\ y IN U /\ open W /\ y IN W /\
        smooth_map_on W (\z. lift(f z)) /\
        frechet_derivative (\z. lift(f z)) (at y) = (\v. vec 0) /\
        matrix_inv(G y) = transp S ** S
        ==> llap G f y =
            sum(1..dimindex(:N))
             (\r. drop(frechet_derivative
                        (\z. frechet_derivative (\w. lift(f w)) (at z)
                                                (transp S ** basis r))
                        (at y) (transp S ** basis r)))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[llap] THEN ASM_REWRITE_TAC[DROP_VEC; REAL_MUL_RZERO; SUM_0;
                                          REAL_SUB_RZERO] THEN
  MP_TAC(ISPECL [`W:real^N->bool`; `\w. lift((f:real^N->real) w)`; `y:real^N`]
         RFA_SECOND_DERIVATIVE_EXPAND) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> CONV_TAC(RAND_CONV(ONCE_REWRITE_CONV[th]))) THEN
  CONV_TAC(RAND_CONV(ONCE_REWRITE_CONV[SUM_SWAP_NUMSEG])) THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  BETA_TAC THEN ONCE_REWRITE_TAC[SUM_SWAP_NUMSEG] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  BETA_TAC THEN ASM_SIMP_TAC[LRG_TRANSP_MUL_COMPONENT] THEN
  REWRITE_TAC[GSYM SUM_RMUL] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `r:num` THEN STRIP_TAC THEN
  BETA_TAC THEN ASM_SIMP_TAC[LRG_TRANSP_BASIS_COMPONENT] THEN REAL_ARITH_TAC);;

let RFA_LLAP_LOCAL_MAX = prove
 (`!U W (G:real^N->real^N^N) f y.
        metric_field U G /\ y IN U /\ open W /\ y IN W /\
        smooth_map_on W (\z. lift(f z)) /\ (!z. z IN W ==> f z <= f y)
        ==> llap G f y <= &0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`]
         LRG_METRIC_INV_FACTOR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `S:real^N^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `frechet_derivative (\z. lift((f:real^N->real) z)) (at y) =
                (\v. vec 0)` ASSUME_TAC THENL
   [MATCH_MP_TAC DIFFERENTIAL_ZERO_MAXMIN THEN
    MAP_EVERY EXISTS_TAC [`\z. lift((f:real^N->real) z)`; `y:real^N`;
                          `W:real^N->bool`] THEN
    ASM_REWRITE_TAC[LIFT_DROP; GSYM FRECHET_DERIVATIVE_WORKS] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `W:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `W:real^N->bool`; `G:real^N->real^N^N`;
                 `f:real^N->real`; `y:real^N`; `S:real^N^N`]
         RFA_LLAP_FRAME_CRITICAL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sum(1..dimindex(:N)) (\r. &0)` THEN
  CONJ_TAC THENL [ALL_TAC; REWRITE_TAC[SUM_0; REAL_LE_REFL]] THEN
  MATCH_MP_TAC SUM_LE_NUMSEG THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC RFA_HESSIAN_LOCAL_MAX THEN EXISTS_TAC `W:real^N->bool` THEN
  ASM_REWRITE_TAC[]);;

let RFA_LLAP_LOCAL_MIN = prove
 (`!U W (G:real^N->real^N^N) f y.
        metric_field U G /\ y IN U /\ open W /\ y IN W /\
        smooth_map_on W (\z. lift(f z)) /\ (!z. z IN W ==> f y <= f z)
        ==> &0 <= llap G f y`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`]
         LRG_METRIC_INV_FACTOR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `S:real^N^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `frechet_derivative (\z. lift((f:real^N->real) z)) (at y) =
                (\v. vec 0)` ASSUME_TAC THENL
   [MATCH_MP_TAC DIFFERENTIAL_ZERO_MAXMIN THEN
    MAP_EVERY EXISTS_TAC [`\z. lift((f:real^N->real) z)`; `y:real^N`;
                          `W:real^N->bool`] THEN
    ASM_REWRITE_TAC[LIFT_DROP; GSYM FRECHET_DERIVATIVE_WORKS] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `W:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `W:real^N->bool`; `G:real^N->real^N^N`;
                 `f:real^N->real`; `y:real^N`; `S:real^N^N`]
         RFA_LLAP_FRAME_CRITICAL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sum(1..dimindex(:N)) (\r. &0)` THEN
  CONJ_TAC THENL [REWRITE_TAC[SUM_0; REAL_LE_REFL]; ALL_TAC] THEN
  MATCH_MP_TAC SUM_LE_NUMSEG THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC RFA_HESSIAN_LOCAL_MIN THEN EXISTS_TAC `W:real^N->bool` THEN
  ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* The Laplacian llap is homogeneous on smooth functions                     *)
(* (used to pass between maximum and minimum principles).                    *)
(* ========================================================================= *)

let RFA_SUM_MUL_INNER = prove
 (`!(a:num->real) b c n.
        sum(1..n) (\k. a k * c * b k) = c * sum(1..n) (\k. a k * b k)`,
  REWRITE_TAC[GSYM SUM_LMUL] THEN REPEAT GEN_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
  REAL_ARITH_TAC);;

let RFA_LLAP_CMUL = prove
 (`!U (G:real^N->real^N^N) f c y.
        open U /\ smooth_map_on U (\z. lift(f z)) /\ y IN U
        ==> llap G (\z. c * f z) y = c * llap G f y`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!z. z IN U
        ==> frechet_derivative (\w. lift(c * (f:real^N->real) w)) (at z) =
            (\h. c % frechet_derivative (\w. lift(f w)) (at z) h)`
  (LABEL_TAC "d1") THENL
   [REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
    REWRITE_TAC[LIFT_CMUL] THEN MATCH_MP_TAC HAS_DERIVATIVE_CMUL THEN
    REWRITE_TAC[ETA_AX; GSYM FRECHET_DERIVATIVE_WORKS] THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `\w. lift((f:real^N->real) w)`; `z:real^N`;
                   `vec 0:real^N`] LRG_SMOOTH_FRECHET_DIFFERENTIABLE) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!j. frechet_derivative
          (\z. frechet_derivative (\w. lift(c * (f:real^N->real) w)) (at z)
                                  (basis j))
          (at y) =
        (\h. c % frechet_derivative
                   (\z. frechet_derivative (\w. lift(f w)) (at z) (basis j))
                   (at y) h)`
  (LABEL_TAC "d2") THENL
   [GEN_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC
     `frechet_derivative
        (\z. c % frechet_derivative (\w. lift((f:real^N->real) w)) (at z)
                                    (basis j))
        (at y)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LRG_FRECHET_DERIVATIVE_EQ_OPEN THEN
      EXISTS_TAC `U:real^N->bool` THEN ASM_SIMP_TAC[];
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
      MATCH_MP_TAC HAS_DERIVATIVE_CMUL THEN
      REWRITE_TAC[ETA_AX; GSYM FRECHET_DERIVATIVE_WORKS] THEN
      MP_TAC(ISPECL [`U:real^N->bool`; `\w. lift((f:real^N->real) w)`;
                     `y:real^N`; `basis j:real^N`]
             LRG_SMOOTH_FRECHET_DIFFERENTIABLE) THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[llap] THEN
  USE_THEN "d1" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `(y:real^N) IN U`)]) THEN
  USE_THEN "d2" (fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[DROP_CMUL; RFA_SUM_MUL_INNER] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM SUM_LMUL] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  BETA_TAC THEN GEN_REWRITE_TAC RAND_CONV [GSYM SUM_LMUL] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  BETA_TAC THEN REAL_ARITH_TAC);;

let RFA_LLAP_NEG = prove
 (`!U (G:real^N->real^N^N) f y.
        open U /\ smooth_map_on U (\z. lift(f z)) /\ y IN U
        ==> llap G (\z. --f z) y = --llap G f y`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\z. --(f:real^N->real) z) = (\z. --(&1) * f z)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `f:real^N->real`;
                 `--(&1)`; `y:real^N`] RFA_LLAP_CMUL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC);;

