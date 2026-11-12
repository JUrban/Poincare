(* ========================================================================= *)
(* pc_wan_lap2a: the maximum principle and the Dirichlet problem on discs.   *)
(*   - the maximum principle for C^2 functions with nonnegative flat         *)
(*     Laplacian on closed balls of real^N (perturb by eps |x - a|^2 and     *)
(*     use the second-derivative test along coordinate lines);               *)
(*   - the Poisson kernel and Poisson integral of the unit disc (adapted     *)
(*     from earlier HOL Light work, and from 100/fourier.ml of the HOL       *)
(*     Light distribution for the periodic offsets);                         *)
(*   - holomorphic maps are smooth; real parts of holomorphic maps have      *)
(*     zero flat Laplacian;                                                  *)
(*   - wanl_dsol a r g, the solution of the Dirichlet problem on             *)
(*     ball(a,r) in real^2 with continuous data g on sphere(a,r), values     *)
(*     in real^K: continuity on cball(a,r), boundary values, smoothness,     *)
(*     harmonicity, the value at the centre; uniqueness;                     *)
(*   - circle and disc (sub)mean value properties;                           *)
(*   - the statements WAN_MAX_PRINCIPLE_DISC, WAN_MAX_PRINCIPLE_DISC_BALL,   *)
(*     WAN_MEAN_VALUE_2D and WAN_SUBMEAN_2D.                                 *)
(* ========================================================================= *)

needs "src/pc_wan_p4defs.ml";;
needs "100/circle.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* The maximum principle on closed balls of real^N.                          *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* WANL_SECOND_DERIVATIVE_LOCAL_MAX and WANL_NORM_POW_2_LINE are adapted     *)
(* from earlier HOL Light work; WANL_LINE_MAX_SECOND is adapted from the     *)
(* same source to maxima of h + eps |x - p|^2.                               *)
(* ------------------------------------------------------------------------- *)

let WANL_SECOND_DERIVATIVE_LOCAL_MAX = prove
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

let WANL_NORM_POW_2_LINE = prove
 (`!(v:real^N) t i.
        1 <= i /\ i <= dimindex(:N)
        ==> norm(v + t % basis i) pow 2 = norm v pow 2 + &2 * t * v$i + t pow 2`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[NORM_POW_2; DOT_LADD; DOT_RADD; DOT_LMUL; DOT_RMUL; DOT_BASIS;
               VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; BASIS_COMPONENT] THEN
  REWRITE_TAC[DOT_SYM] THEN REAL_ARITH_TAC);;

let WANL_LINE_MAX_SECOND = prove
 (`!(h:real^N->real) g d p q i eps rho e.
        1 <= i /\ i <= dimindex(:N) /\ &0 < e /\ &0 < rho /\
        (!t. abs t < e
             ==> ((\s. h(q + s % basis i)) has_real_derivative g t) (atreal t)) /\
        (g has_real_derivative d) (atreal (&0)) /\
        (!t. abs t < rho
             ==> h(q + t % basis i) + eps * norm((q + t % basis i) - p) pow 2
                 <= h q + eps * norm(q - p) pow 2)
        ==> d + &2 * eps <= &0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`\t. (h:real^N->real)(q + t % basis i) +
         eps * (norm(q - p:real^N) pow 2 + &2 * t * (q - p:real^N)$i + t pow 2)`;
    `\t. (g:real->real) t + eps * (&2 * (q - p:real^N)$i + &2 * t)`;
    `d + &2 * eps`; `min e rho`] WANL_SECOND_DERIVATIVE_LOCAL_MAX) THEN
  ANTS_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
  BETA_TAC THEN REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    X_GEN_TAC `t:real` THEN DISCH_TAC THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_ADD THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (find_term (fun u -> u = `has_real_derivative`)) (concl th) &&
        is_forall(concl th))) THEN
      ASM_REAL_ARITH_TAC;
      REAL_DIFF_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC[REAL_POW_1] THEN REAL_ARITH_TAC];
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_ADD THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      REAL_DIFF_TAC THEN REAL_ARITH_TAC];
    X_GEN_TAC `t:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `t:real` o check (fun th ->
      not (can (find_term (fun u -> u = `has_real_derivative`)) (concl th)) &&
      is_forall(concl th))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `((q:real^N) + t % basis i) - p = (q - p) + t % basis i`
    SUBST1_TAC THENL [VECTOR_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[WANL_NORM_POW_2_LINE] THEN
    REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_RID] THEN REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Real derivatives along lines.                                             *)
(* ------------------------------------------------------------------------- *)

let WANL_LINE_REAL_DERIVATIVE = prove
 (`!(Fn:real^N->real^1) Fd x v t.
        (Fn has_derivative Fd) (at (x + t % v))
        ==> ((\q. drop(Fn(x + q % v))) has_real_derivative drop(Fd v)) (atreal t)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[HAS_REAL_FRECHET_DERIVATIVE_AT] THEN
  SUBGOAL_THEN
   `(lift o (\q. drop((Fn:real^N->real^1)(x + q % v))) o drop) =
    Fn o (\y:real^1. x + drop y % v)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_DROP]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(\y:real^1. drop((Fd:real^N->real^1) v) % y) = Fd o (\y:real^1. drop y % v)`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM] THEN X_GEN_TAC `y:real^1` THEN
    FIRST_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [has_derivative]) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP LINEAR_CMUL th]) THEN
    REWRITE_TAC[GSYM DROP_EQ; DROP_CMUL] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC DIFF_CHAIN_AT THEN ASM_REWRITE_TAC[LIFT_DROP] THEN
  SUBGOAL_THEN `(\y:real^1. drop y % (v:real^N)) = (\h. vec 0 + drop h % v)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; VECTOR_ADD_LID]; ALL_TAC] THEN
  MATCH_MP_TAC HAS_DERIVATIVE_ADD THEN REWRITE_TAC[HAS_DERIVATIVE_CONST] THEN
  MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN
  REWRITE_TAC[linear; DROP_ADD; DROP_CMUL] THEN VECTOR_ARITH_TAC);;

let WANL_SMOOTH_LINE_SECOND = prove
 (`!(U:real^N->bool) (h:real^N->real) q i.
        open U /\ q IN U /\ smooth_map_on U (\x. lift(h x)) /\
        1 <= i /\ i <= dimindex(:N)
        ==> ?e. &0 < e /\
                (!t. abs t < e
                     ==> ((\s. h(q + s % basis i)) has_real_derivative
                          drop(frechet_derivative (\w. lift(h w)) (at (q + t % basis i))
                                 (basis i)))
                         (atreal t)) /\
                ((\t. drop(frechet_derivative (\w. lift(h w)) (at (q + t % basis i))
                             (basis i)))
                 has_real_derivative
                 drop(frechet_derivative
                        (\z. frechet_derivative (\w. lift(h w)) (at z) (basis i))
                        (at q) (basis i)))
                (atreal (&0))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `q:real^N` o GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `e:real` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `t:real` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(q:real^N) + t % basis i IN U` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
      REWRITE_TAC[IN_BALL; NORM_ARITH `dist(q:real^N,q + y) = norm y`] THEN
      ASM_SIMP_TAC[NORM_MUL; NORM_BASIS; REAL_MUL_RID];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`\w. lift((h:real^N->real) w)`;
                   `frechet_derivative (\w. lift((h:real^N->real) w)) (at (q + t % basis i))`;
                   `q:real^N`; `basis i:real^N`; `t:real`] WANL_LINE_REAL_DERIVATIVE) THEN
    REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `\w. lift((h:real^N->real) w)`]
           SMOOTH_MAP_ON_HAS_DERIVATIVE) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\z. frechet_derivative (\w. lift((h:real^N->real) w)) (at z) (basis i)`;
                 `frechet_derivative
                    (\z. frechet_derivative (\w. lift((h:real^N->real) w)) (at z) (basis i))
                    (at q)`;
                 `q:real^N`; `basis i:real^N`; `&0`] WANL_LINE_REAL_DERIVATIVE) THEN
  REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_RID] THEN DISCH_THEN MATCH_MP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`;
                 `\z. frechet_derivative (\w. lift((h:real^N->real) w)) (at z) (basis i)`]
         SMOOTH_MAP_ON_HAS_DERIVATIVE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SMOOTH_MAP_ON_FRECHET_DERIVATIVE THEN
    ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The flat Laplacian of smooth functions: linearity and linear images.      *)
(* ------------------------------------------------------------------------- *)

let WANL_FD_LOCAL_OPEN = prove
 (`!(f:real^M->real^N) g U x.
        open U /\ x IN U /\ (!y. y IN U ==> f y = g y)
        ==> frechet_derivative f (at x) = frechet_derivative g (at x)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `x:real^M` o GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL]) THEN
  ASM_REWRITE_TAC[SUBSET; IN_BALL] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC FRECHET_DERIVATIVE_LOCAL THEN EXISTS_TAC `d:real` THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REWRITE_TAC[]);;

let WANL_FD_LINCOMB = prove
 (`!(f:real^N->real) g c d z.
        (\w. lift(f w)) differentiable (at z) /\ (\w. lift(g w)) differentiable (at z)
        ==> frechet_derivative (\w. lift(c * f w + d * g w)) (at z) =
            (\v. c % frechet_derivative (\w. lift(f w)) (at z) v +
                 d % frechet_derivative (\w. lift(g w)) (at z) v)`,
  REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
  REWRITE_TAC[LIFT_ADD; LIFT_CMUL] THEN MATCH_MP_TAC HAS_DERIVATIVE_ADD THEN
  CONJ_TAC THEN MATCH_MP_TAC HAS_DERIVATIVE_CMUL THEN
  REWRITE_TAC[ETA_AX; GSYM FRECHET_DERIVATIVE_WORKS] THEN ASM_REWRITE_TAC[]);;

let WANL_LLAP_LINEAR = prove
 (`!(U:real^N->bool) (f:real^N->real) g c d y.
        open U /\ y IN U /\ smooth_map_on U (\z. lift(f z)) /\
        smooth_map_on U (\z. lift(g z))
        ==> llap (\z. mat 1) (\z. c * f z + d * g z) y =
            c * llap (\z. mat 1) f y + d * llap (\z. mat 1) g y`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `smooth_map_on U (\z. lift(c * (f:real^N->real) z + d * g z))`
  ASSUME_TAC THENL
   [REWRITE_TAC[LIFT_ADD; LIFT_CMUL] THEN MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CMUL_OPEN];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `\z. c * (f:real^N->real) z + d * g z`; `y:real^N`]
         LLAP_FLAT) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `f:real^N->real`; `y:real^N`] LLAP_FLAT) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `g:real^N->real`; `y:real^N`] LLAP_FLAT) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN
  REWRITE_TAC[GSYM SUM_LMUL; GSYM SUM_ADD_NUMSEG] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN BETA_TAC THEN
  SUBGOAL_THEN
   `!z. z IN U
        ==> frechet_derivative (\w. lift(c * (f:real^N->real) w + d * g w)) (at z) (basis i) =
            c % frechet_derivative (\w. lift(f w)) (at z) (basis i) +
            d % frechet_derivative (\w. lift(g w)) (at z) (basis i)`
  (LABEL_TAC "pw") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`f:real^N->real`; `g:real^N->real`; `c:real`; `d:real`; `z:real^N`]
           WANL_FD_LINCOMB) THEN
    ANTS_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
      EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!(k:real^N->real). smooth_map_on U (\z. lift(k z))
        ==> ((\z. frechet_derivative (\w. lift(k w)) (at z) (basis i)) has_derivative
             frechet_derivative (\z. frechet_derivative (\w. lift(k w)) (at z) (basis i)) (at y))
            (at y)`
  (LABEL_TAC "dk") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`U:real^N->bool`;
                   `\z. frechet_derivative (\w. lift((k:real^N->real) w)) (at z) (basis i)`]
           SMOOTH_MAP_ON_HAS_DERIVATIVE) THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_FRECHET_DERIVATIVE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `frechet_derivative
      (\z. frechet_derivative (\w. lift(c * (f:real^N->real) w + d * g w)) (at z) (basis i))
      (at y) =
    (\v. c % frechet_derivative (\z. frechet_derivative (\w. lift(f w)) (at z) (basis i))
               (at y) v +
         d % frechet_derivative (\z. frechet_derivative (\w. lift(g w)) (at z) (basis i))
               (at y) v)`
  SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
    MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_AT THEN
    EXISTS_TAC `\z. c % frechet_derivative (\w. lift((f:real^N->real) w)) (at z) (basis i) +
                    d % frechet_derivative (\w. lift((g:real^N->real) w)) (at z) (basis i)` THEN
    FIRST_ASSUM(MP_TAC o SPEC `y:real^N` o GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL]) THEN
    ASM_REWRITE_TAC[SUBSET; IN_BALL] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `e:real` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN BETA_TAC THEN CONV_TAC SYM_CONV THEN
      USE_THEN "pw" MATCH_MP_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC HAS_DERIVATIVE_ADD THEN CONJ_TAC THEN
      MATCH_MP_TAC HAS_DERIVATIVE_CMUL THEN REWRITE_TAC[ETA_AX] THEN
      USE_THEN "dk" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    REWRITE_TAC[DROP_ADD; DROP_CMUL]]);;

let WANL_LLAP_LINEAR_IMAGE = prove
 (`!(U:real^N->bool) (h:real^N->real^K) (L:real^K->real^1) y.
        open U /\ y IN U /\ smooth_map_on U h /\ linear L
        ==> llap (\z. mat 1) (\z. drop(L(h z))) y =
            sum(1..dimindex(:N))
              (\i. drop(L(frechet_derivative
                            (\z. frechet_derivative h (at z) (basis i)) (at y) (basis i))))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!z. z IN U ==> (h:real^N->real^K) differentiable (at z)` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on U (\z. lift(drop((L:real^K->real^1)((h:real^N->real^K) z))))`
  ASSUME_TAC THENL
   [REWRITE_TAC[LIFT_DROP] THEN
    SUBGOAL_THEN `(\z. (L:real^K->real^1)((h:real^N->real^K) z)) = L o h` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_LINEAR_O THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `\z. drop((L:real^K->real^1)((h:real^N->real^K) z))`;
                 `y:real^N`] LLAP_FLAT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[LIFT_DROP] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN BETA_TAC THEN
  AP_TERM_TAC THEN
  SUBGOAL_THEN
   `!z. z IN U
        ==> frechet_derivative (\w. (L:real^K->real^1)((h:real^N->real^K) w)) (at z) (basis i) =
            L(frechet_derivative h (at z) (basis i))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
     `frechet_derivative (\w. (L:real^K->real^1)((h:real^N->real^K) w)) (at z) =
      L o frechet_derivative h (at z)`
    (fun th -> REWRITE_TAC[th; o_THM]) THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
    SUBGOAL_THEN `(\w. (L:real^K->real^1)((h:real^N->real^K) w)) = L o h` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC DIFF_CHAIN_AT THEN
    ASM_SIMP_TAC[GSYM FRECHET_DERIVATIVE_WORKS; HAS_DERIVATIVE_LINEAR];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `frechet_derivative
                (\z. (L:real^K->real^1)(frechet_derivative (h:real^N->real^K) (at z) (basis i)))
                (at y) (basis i)` THEN
  CONJ_TAC THENL
   [AP_THM_TAC THEN MATCH_MP_TAC WANL_FD_LOCAL_OPEN THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `frechet_derivative
      (\z. (L:real^K->real^1)(frechet_derivative (h:real^N->real^K) (at z) (basis i))) (at y) =
    L o frechet_derivative (\z. frechet_derivative h (at z) (basis i)) (at y)`
  (fun th -> REWRITE_TAC[th; o_THM]) THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
  SUBGOAL_THEN
   `(\z. (L:real^K->real^1)(frechet_derivative (h:real^N->real^K) (at z) (basis i))) =
    L o (\z. frechet_derivative h (at z) (basis i))` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC DIFF_CHAIN_AT THEN ASM_SIMP_TAC[HAS_DERIVATIVE_LINEAR] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `\z. frechet_derivative (h:real^N->real^K) (at z) (basis i)`]
         SMOOTH_MAP_ON_HAS_DERIVATIVE) THEN
  ASM_SIMP_TAC[SMOOTH_MAP_ON_FRECHET_DERIVATIVE]);;

(* ------------------------------------------------------------------------- *)
(* The maximum principle: a function continuous on cball(a,r), smooth on    *)
(* ball(a,r) with nonnegative flat Laplacian there and at most M on the     *)
(* sphere is at most M on the closed ball.                                  *)
(* ------------------------------------------------------------------------- *)

let WANL_MAXP_EPS = prove
 (`!(a:real^N) r (h:real^N->real) M eps.
        &0 < r /\ &0 < eps /\ (\x. lift(h x)) continuous_on cball(a,r) /\
        smooth_map_on (ball(a,r)) (\x. lift(h x)) /\
        (!x. x IN ball(a,r) ==> &0 <= llap (\y:real^N. mat 1) h x) /\
        (!y. y IN sphere(a,r) ==> h y <= M)
        ==> !x. x IN cball(a,r) ==> h x <= M + eps * r pow 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`\x. (h:real^N->real) x + eps * norm(x - a) pow 2`;
                 `cball(a:real^N,r)`] CONTINUOUS_ATTAINS_SUP) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[COMPACT_CBALL; CBALL_EQ_EMPTY] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[o_DEF; LIFT_ADD; LIFT_CMUL] THEN MATCH_MP_TAC CONTINUOUS_ON_ADD THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN
    REWRITE_TAC[NORM_POW_2; LIFT_DROP] THEN
    MATCH_MP_TAC CONTINUOUS_ON_LIFT_DOT2 THEN
    SIMP_TAC[CONTINUOUS_ON_SUB; CONTINUOUS_ON_ID; CONTINUOUS_ON_CONST];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:real^N`
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "max" o BETA_RULE))) THEN
  ASM_CASES_TAC `(q:real^N) IN ball(a,r)` THENL
   [ALL_TAC;
    SUBGOAL_THEN `(q:real^N) IN sphere(a,r)` ASSUME_TAC THENL
     [UNDISCH_TAC `(q:real^N) IN cball(a,r)` THEN UNDISCH_TAC `~((q:real^N) IN ball(a,r))` THEN
      REWRITE_TAC[IN_BALL; IN_CBALL; IN_SPHERE] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `norm(q - a:real^N) = r` ASSUME_TAC THENL
     [UNDISCH_TAC `(q:real^N) IN sphere(a,r)` THEN REWRITE_TAC[IN_SPHERE; dist] THEN
      CONV_TAC NORM_ARITH;
      ALL_TAC] THEN
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    USE_THEN "max" (MP_TAC o C MATCH_MP (ASSUME `(x:real^N) IN cball(a,r)`)) THEN
    BETA_TAC THEN REWRITE_TAC[ASSUME `norm(q - a:real^N) = r`] THEN
    MP_TAC(C MATCH_MP (ASSUME `(q:real^N) IN sphere(a,r)`)
             (ASSUME `!y. y IN sphere(a:real^N,r) ==> (h:real^N->real) y <= M`)) THEN
    SUBGOAL_THEN `&0 <= eps * norm(x - a:real^N) pow 2` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC]] THEN
  (* q interior: contradiction with the second-derivative test *)
  SUBGOAL_THEN `F` CONTR_TAC THEN
  ABBREV_TAC `rho = r - dist(a:real^N,q)` THEN
  SUBGOAL_THEN `&0 < rho` ASSUME_TAC THENL
   [EXPAND_TAC "rho" THEN UNDISCH_TAC `(q:real^N) IN ball(a,r)` THEN
    REWRITE_TAC[IN_BALL] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= dimindex(:N)
        ==> drop(frechet_derivative
                   (\z. frechet_derivative (\w. lift((h:real^N->real) w)) (at z) (basis i))
                   (at q) (basis i)) + &2 * eps <= &0`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`ball(a:real^N,r)`; `h:real^N->real`; `q:real^N`; `i:num`]
           WANL_SMOOTH_LINE_SECOND) THEN
    ASM_REWRITE_TAC[OPEN_BALL] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC WANL_LINE_MAX_SECOND THEN
    MAP_EVERY EXISTS_TAC
     [`h:real^N->real`;
      `\t. drop(frechet_derivative (\w. lift((h:real^N->real) w)) (at (q + t % basis i))
                 (basis i))`;
      `a:real^N`; `q:real^N`; `i:num`; `rho:real`; `e:real`] THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `t:real` THEN DISCH_TAC THEN
    USE_THEN "max" MATCH_MP_TAC THEN
    REWRITE_TAC[IN_CBALL] THEN
    MATCH_MP_TAC(NORM_ARITH
     `dist(a:real^N,q) + norm(y) <= r ==> dist(a,q + y) <= r`) THEN
    ASM_SIMP_TAC[NORM_MUL; NORM_BASIS] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`ball(a:real^N,r)`; `h:real^N->real`; `q:real^N`] LLAP_FLAT) THEN
  ASM_REWRITE_TAC[OPEN_BALL] THEN DISCH_TAC THEN
  MP_TAC(C MATCH_MP (ASSUME `(q:real^N) IN ball(a,r)`)
           (ASSUME `!x. x IN ball(a:real^N,r) ==> &0 <= llap (\y:real^N. mat 1) h x`)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `sum(1..dimindex(:N))
      (\i. drop(frechet_derivative
                  (\z. frechet_derivative (\w. lift((h:real^N->real) w)) (at z) (basis i))
                  (at q) (basis i))) <=
    sum(1..dimindex(:N)) (\i. --(&2 * eps))`
  MP_TAC THENL
   [MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN BETA_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (is_forall o concl)) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[SUM_CONST_NUMSEG; ADD_SUB] THEN
  UNDISCH_TAC
   `&0 <= sum(1..dimindex(:N))
      (\i. drop(frechet_derivative
                  (\z. frechet_derivative (\w. lift((h:real^N->real) w)) (at z) (basis i))
                  (at q) (basis i)))` THEN
  SPEC_TAC(`sum(1..dimindex(:N))
      (\i. drop(frechet_derivative
                  (\z. frechet_derivative (\w. lift((h:real^N->real) w)) (at z) (basis i))
                  (at q) (basis i)))`,`S:real`) THEN
  MP_TAC(ISPEC `(:N)` DIMINDEX_GE_1) THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN
  SUBGOAL_THEN `&0 < &2 * eps` MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SPEC_TAC(`&(dimindex(:N))`,`n:real`) THEN SPEC_TAC(`&2 * eps`,`c:real`) THEN
  REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `c * &1 <= c * n` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]);;

let WANL_MAXP_SUB = prove
 (`!(a:real^N) r (h:real^N->real) M.
        &0 < r /\ (\x. lift(h x)) continuous_on cball(a,r) /\
        smooth_map_on (ball(a,r)) (\x. lift(h x)) /\
        (!x. x IN ball(a,r) ==> &0 <= llap (\y:real^N. mat 1) h x) /\
        (!y. y IN sphere(a,r) ==> h y <= M)
        ==> !x. x IN cball(a,r) ==> h x <= M`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < r pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`a:real^N`; `r:real`; `h:real^N->real`; `M:real`;
                 `(h(x:real^N) - M) / (&2 * r pow 2)`] WANL_MAXP_EPS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(h(x:real^N) - M) / (&2 * r pow 2) * r pow 2 = (h x - M) / &2`
  SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < r pow 2` THEN CONV_TAC REAL_FIELD; ASM_REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* The Poisson kernel and the Poisson integral of the unit disc, with        *)
(* boundary limits for continuous data and the representation of the Poisson *)
(* integral of real data as the real part of a holomorphic map.              *)
(*                                                                           *)
(* The eight periodic-offset lemmas (REAL_PERIODIC_INTEGER_MULTIPLE ...      *)
(* REAL_INTEGRAL_PERIODIC_OFFSET) are renamed copies of lemmas of            *)
(* 100/fourier.ml of the HOL Light distribution, which is not loaded here.   *)
(* The rest (the constants wanl_poisson_kernel and wanl_poisson_integral,    *)
(* JORDAN_SIN ... POISSON_INTEGRAL_RE_HOLOMORPHIC) is adapted from earlier   *)
(* HOL Light work.                                                           *)
(* ========================================================================= *)

(* from 100/fourier.ml of the HOL Light distribution *)
let WANL_REAL_PERIODIC_INTEGER_MULTIPLE = prove
 (`!f:real->real a.
        (!x. f(x + a) = f x) <=> (!x n. integer n ==> f(x + n * a) = f x)`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [ALL_TAC; MESON_TAC[INTEGER_CLOSED; REAL_MUL_LID]] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `!x n. f(x + &n * a) = (f:real->real) x` ASSUME_TAC THENL
   [GEN_TAC THEN INDUCT_TAC THEN
    ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_ADD_RID] THEN
    ASM_REWRITE_TAC[GSYM REAL_OF_NUM_SUC; REAL_ADD_RDISTRIB;
                    REAL_ADD_ASSOC; REAL_MUL_LID];
    REWRITE_TAC[INTEGER_CASES] THEN REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[REAL_ARITH `(x + -- &n * a) + &n * a = x`]]);;

(* from 100/fourier.ml of the HOL Light distribution *)
let WANL_HAS_REAL_INTEGRAL_OFFSET = prove
 (`!f i a b c. (f has_real_integral i) (real_interval[a,b])
                ==> ((\x. f(x + c)) has_real_integral i)
                    (real_interval[a - c,b - c])`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o SPECL [`&1`; `c:real`] o
   MATCH_MP (REWRITE_RULE[IMP_CONJ] HAS_REAL_INTEGRAL_AFFINITY)) THEN
  REWRITE_TAC[REAL_OF_NUM_EQ; ARITH_EQ; REAL_MUL_LID; REAL_INV_1] THEN
  REWRITE_TAC[REAL_ABS_1; REAL_MUL_LID; REAL_INV_1] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  MATCH_MP_TAC SURJECTIVE_IMAGE_EQ THEN
  REWRITE_TAC[IN_REAL_INTERVAL; EXISTS_REFL;
              REAL_ARITH `x - c:real = y <=> x = y + c`] THEN
  REAL_ARITH_TAC);;

(* from 100/fourier.ml of the HOL Light distribution *)
let WANL_HAS_REAL_INTEGRAL_PERIODIC_OFFSET_LEMMA = prove
 (`!f i a b c.
        (!x. f(x + (b - a)) = f(x)) /\
        (f has_real_integral i) (real_interval[a,a+c])
        ==> (f has_real_integral i) (real_interval[b,b+c])`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM
    (MP_TAC o SPEC `a - b:real` o MATCH_MP WANL_HAS_REAL_INTEGRAL_OFFSET) THEN
  REWRITE_TAC[REAL_ARITH
   `a - (a - b):real = b /\ (a + c) - (a - b) = b + c`] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] HAS_REAL_INTEGRAL_EQ) THEN
  X_GEN_TAC `x:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x + a - b:real`) THEN
  REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  AP_TERM_TAC THEN REAL_ARITH_TAC);;

(* from 100/fourier.ml of the HOL Light distribution *)
let WANL_HAS_REAL_INTEGRAL_PERIODIC_OFFSET_POS = prove
 (`!f i a b c.
        (!x. f(x + (b - a)) = f x) /\ &0 <= c /\ a + c <= b /\
        (f has_real_integral i) (real_interval[a,b])
        ==> ((\x. f(x + c)) has_real_integral i)
             (real_interval[a,b])`,
  let tac =
    REWRITE_TAC[GSYM HAS_REAL_INTEGRAL_INTEGRAL] THEN
    MATCH_MP_TAC REAL_INTEGRABLE_ON_SUBINTERVAL THEN
    EXISTS_TAC `real_interval[a,b]` THEN
    ASM_REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[real_integrable_on]; ASM_REAL_ARITH_TAC] in
  REPEAT STRIP_TAC THEN
  CONJUNCTS_THEN SUBST1_TAC
   (REAL_ARITH `a:real = (a + c) - c /\ b = (b + c) - c`) THEN
  MATCH_MP_TAC WANL_HAS_REAL_INTEGRAL_OFFSET THEN
  SUBGOAL_THEN
   `((f has_real_integral (real_integral(real_interval[a,a+c]) f))
     (real_interval[a,a+c]) /\
     (f has_real_integral (real_integral(real_interval[a+c,b]) f))
     (real_interval[a+c,b])) /\
    ((f has_real_integral (real_integral(real_interval[a+c,b]) f))
     (real_interval[a+c,b]) /\
     (f has_real_integral (real_integral(real_interval[a,a+c]) f))
     (real_interval[b,b+c]))`
  MP_TAC THENL
   [REPEAT CONJ_TAC THEN TRY tac THEN
    MATCH_MP_TAC WANL_HAS_REAL_INTEGRAL_PERIODIC_OFFSET_LEMMA THEN
    EXISTS_TAC `a:real` THEN ASM_REWRITE_TAC[] THEN tac;
    DISCH_THEN(CONJUNCTS_THEN(MP_TAC o MATCH_MP
     (REWRITE_RULE[TAUT `a /\ b /\ c /\ d ==> e <=>
                  c /\ d ==> a /\ b ==> e`] HAS_REAL_INTEGRAL_COMBINE))) THEN
    REPEAT(ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC]) THEN
    ASM_MESON_TAC[HAS_REAL_INTEGRAL_UNIQUE; REAL_ADD_SYM]]);;

(* from 100/fourier.ml of the HOL Light distribution *)
let WANL_HAS_REAL_INTEGRAL_PERIODIC_OFFSET_WEAK = prove
 (`!f i a b c.
        (!x. f(x + (b - a)) = f x) /\ abs(c) <= b - a /\
        (f has_real_integral i) (real_interval[a,b])
        ==> ((\x. f(x + c)) has_real_integral i)
             (real_interval[a,b])`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `&0 <= c` THENL
   [MATCH_MP_TAC WANL_HAS_REAL_INTEGRAL_PERIODIC_OFFSET_POS THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    MP_TAC(ISPECL [`\x. (f:real->real)(--x)`; `i:real`;
                   `--b:real`; `--a:real`; `--c:real`]
          WANL_HAS_REAL_INTEGRAL_PERIODIC_OFFSET_POS) THEN
    ASM_REWRITE_TAC[REAL_NEG_ADD; HAS_REAL_INTEGRAL_REFLECT] THEN
    REWRITE_TAC[REAL_NEG_NEG] THEN DISCH_THEN MATCH_MP_TAC THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    X_GEN_TAC `x:real` THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `--x + (a - b):real`) THEN
    REWRITE_TAC[REAL_ARITH `--(--a - --b):real = a - b`] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN AP_TERM_TAC THEN REAL_ARITH_TAC]);;

(* from 100/fourier.ml of the HOL Light distribution *)
let WANL_HAS_REAL_INTEGRAL_PERIODIC_OFFSET = prove
 (`!f i a b c.
        (!x. f(x + (b - a)) = f x) /\
        (f has_real_integral i) (real_interval[a,b])
        ==> ((\x. f(x + c)) has_real_integral i) (real_interval[a,b])`,
  REPEAT GEN_TAC THEN
  DISJ_CASES_TAC (REAL_ARITH `b <= a \/ a < b`) THEN
  ASM_SIMP_TAC[HAS_REAL_INTEGRAL_NULL_EQ] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `((\x. f(x + (b - a) * frac(c / (b - a)))) has_real_integral i)
    (real_interval[a,b])`
  MP_TAC THENL
   [MATCH_MP_TAC WANL_HAS_REAL_INTEGRAL_PERIODIC_OFFSET_WEAK THEN
    ASM_REWRITE_TAC[REAL_ABS_MUL] THEN
    MATCH_MP_TAC(REAL_ARITH
     `a < b /\ (b - a) * f < (b - a) * &1
      ==> abs(b - a) * f <= b - a`) THEN
    ASM_SIMP_TAC[REAL_SUB_LT; REAL_LT_LMUL_EQ] THEN
    ASM_REWRITE_TAC[real_abs; FLOOR_FRAC];
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] HAS_REAL_INTEGRAL_EQ) THEN
    X_GEN_TAC `x:real` THEN STRIP_TAC THEN REWRITE_TAC[FRAC_FLOOR] THEN
    ASM_SIMP_TAC[REAL_FIELD
     `a < b ==> x + (b - a) * (c / (b - a) - f) =
                (x + c) + --f * (b - a)`] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[WANL_REAL_PERIODIC_INTEGER_MULTIPLE]) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    SIMP_TAC[INTEGER_CLOSED; FLOOR]]);;

(* from 100/fourier.ml of the HOL Light distribution *)
let WANL_REAL_INTEGRABLE_PERIODIC_OFFSET = prove
 (`!f a b c.
        (!x. f(x + (b - a)) = f x) /\
        f real_integrable_on real_interval[a,b]
        ==> (\x. f(x + c)) real_integrable_on real_interval[a,b]`,
  REWRITE_TAC[real_integrable_on] THEN
  MESON_TAC[WANL_HAS_REAL_INTEGRAL_PERIODIC_OFFSET]);;

(* from 100/fourier.ml of the HOL Light distribution *)
let WANL_REAL_INTEGRAL_PERIODIC_OFFSET = prove
 (`!f a b c.
        (!x. f(x + (b - a)) = f x) /\
        f real_integrable_on real_interval[a,b]
        ==> real_integral (real_interval[a,b]) (\x. f(x + c)) =
            real_integral (real_interval[a,b]) f`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_INTEGRAL_UNIQUE THEN
  MATCH_MP_TAC WANL_HAS_REAL_INTEGRAL_PERIODIC_OFFSET THEN
  ASM_REWRITE_TAC[GSYM HAS_REAL_INTEGRAL_INTEGRAL]);;

let WANL_JORDAN_SIN = prove
 (`!x. &0 <= x /\ x <= pi / &2 ==> &2 / pi * x <= sin x`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\x. &2 / pi * x - sin x`; `&0`; `pi / &2`; `x:real`]
    REAL_CONVEX_LOWER_REAL_INTERVAL) THEN
  REWRITE_TAC[IN_REAL_INTERVAL] THEN BETA_TAC THEN
  REWRITE_TAC[SIN_0; SIN_PI2; REAL_MUL_RZERO; REAL_SUB_RZERO] THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`\x. &2 / pi * x - sin x`; `\x. &2 / pi - cos x`; `sin`;
                   `real_interval[&0,pi / &2]`]
      REAL_CONVEX_ON_SECOND_DERIVATIVE) THEN
    REWRITE_TAC[IS_REALINTERVAL_INTERVAL; IN_REAL_INTERVAL] THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [DISCH_THEN(X_CHOOSE_THEN `a:real` MP_TAC) THEN
        REWRITE_TAC[EXTENSION; IN_REAL_INTERVAL; IN_SING] THEN
        DISCH_THEN(fun th -> MP_TAC(SPEC `&0` th) THEN
                             MP_TAC(SPEC `pi / &2` th)) THEN
        MP_TAC PI_POS THEN REAL_ARITH_TAC;
        X_GEN_TAC `y:real` THEN DISCH_TAC THEN
        MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
        MP_TAC(REAL_DIFF_CONV
          `((\x. &2 / pi * x - sin x) has_real_derivative f') (atreal y)`) THEN
        REWRITE_TAC[REAL_MUL_RID; REAL_MUL_LID];
        X_GEN_TAC `y:real` THEN DISCH_TAC THEN
        MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
        MP_TAC(REAL_DIFF_CONV
          `((\x. &2 / pi - cos x) has_real_derivative f') (atreal y)`) THEN
        REWRITE_TAC[REAL_MUL_LID; REAL_SUB_LZERO; REAL_NEG_NEG]];
      DISCH_THEN SUBST1_TAC THEN X_GEN_TAC `y:real` THEN STRIP_TAC THEN
      MATCH_MP_TAC SIN_POS_PI_LE THEN MP_TAC PI_POS THEN ASM_REAL_ARITH_TAC];
    SUBGOAL_THEN `&2 / pi * pi / &2 = &1` SUBST1_TAC THENL
     [MP_TAC PI_POS THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    REAL_ARITH_TAC]);;

let WANL_NORM_CEXP_II_SUB_1_LOWER = prove
 (`!u. abs u <= pi ==> &2 / pi * abs u <= norm(cexp(ii * Cx u) - Cx(&1))`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[DIST_CEXP_II_1] THEN
  SUBGOAL_THEN `sin(abs u / &2) <= abs(sin(u / &2))` MP_TAC THENL
   [DISJ_CASES_TAC(REAL_ARITH `&0 <= u \/ u < &0`) THENL
     [ASM_SIMP_TAC[REAL_ARITH `&0 <= u ==> abs u = u`] THEN REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_ARITH `u < &0 ==> abs u = --u`] THEN
      REWRITE_TAC[real_div; REAL_MUL_LNEG; SIN_NEG] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(SPEC `abs u / &2` WANL_JORDAN_SIN) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]);;

let wanl_poisson_kernel = new_definition
 `wanl_poisson_kernel (z:complex) (s:real) =
    (&1 - norm z pow 2) / norm(cexp(ii * Cx s) - z) pow 2`;;

let WANL_HAS_INTEGRAL_ANGLE_CIRCLEPATH = prove
 (`!h v. (h has_path_integral v) (circlepath(Cx(&0),&1))
         ==> ((\s. ii * cexp(ii * Cx(drop s)) * h(cexp(ii * Cx(drop s))))
              has_integral v) (interval[vec 0,lift(&2 * pi)])`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[HAS_PATH_INTEGRAL; VECTOR_DERIVATIVE_CIRCLEPATH; CIRCLEPATH] THEN
  REWRITE_TAC[COMPLEX_ADD_LID; COMPLEX_MUL_LID] THEN
  DISCH_THEN(MP_TAC o SPECL [`inv(&2 * pi)`; `vec 0:real^1`] o
    MATCH_MP (REWRITE_RULE[IMP_CONJ] HAS_INTEGRAL_AFFINITY)) THEN
  REWRITE_TAC[REAL_INV_EQ_0; REAL_ENTIRE; PI_NZ; REAL_OF_NUM_EQ; ARITH_EQ] THEN
  REWRITE_TAC[DROP_ADD; DROP_CMUL; DROP_VEC; REAL_ADD_RID] THEN
  SUBGOAL_THEN
   `!x. Cx(&2) * Cx pi * ii * Cx(inv(&2 * pi) * x) = ii * Cx x`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN REWRITE_TAC[CX_MUL; CX_INV] THEN
    SUBGOAL_THEN `~(Cx pi = Cx(&0))` MP_TAC THENL
     [REWRITE_TAC[CX_INJ; PI_NZ]; CONV_TAC COMPLEX_FIELD];
    ALL_TAC] THEN
  REWRITE_TAC[DIMINDEX_1; REAL_POW_1; REAL_ABS_INV; REAL_INV_INV] THEN
  REWRITE_TAC[VECTOR_MUL_RZERO; VECTOR_NEG_0] THEN
  REWRITE_TAC[IMAGE_AFFINITY_INTERVAL; INTERVAL_EQ_EMPTY_1; DROP_VEC] THEN
  SIMP_TAC[REAL_ARITH `~(&1 < &0)`; REAL_LE_MUL; REAL_POS; PI_POS_LE;
           REAL_ABS_MUL; REAL_ABS_NUM; REAL_ABS_PI] THEN
  REWRITE_TAC[VECTOR_MUL_RZERO; VECTOR_ADD_RID] THEN
  SUBGOAL_THEN `(&2 * pi) % vec 1:real^1 = lift(&2 * pi)` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM LIFT_NUM; GSYM LIFT_CMUL; REAL_MUL_RID]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `inv(&2 * pi)` o MATCH_MP HAS_INTEGRAL_CMUL) THEN
  REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
  SIMP_TAC[REAL_MUL_LINV; REAL_ENTIRE; PI_NZ; REAL_OF_NUM_EQ; ARITH_EQ;
           VECTOR_MUL_LID] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] HAS_INTEGRAL_EQ) THEN
  X_GEN_TAC `s:real^1` THEN DISCH_TAC THEN REWRITE_TAC[COMPLEX_CMUL] THEN
  REWRITE_TAC[CX_INV; CX_MUL] THEN
  SUBGOAL_THEN `~(Cx pi = Cx(&0))` MP_TAC THENL
   [REWRITE_TAC[CX_INJ; PI_NZ]; CONV_TAC COMPLEX_FIELD]);;

let WANL_POISSON_KERNEL_CX = prove
 (`!z s. norm z < &1
         ==> Cx(wanl_poisson_kernel z s) =
             cexp(ii * Cx s) / (cexp(ii * Cx s) - z) +
             Cx(&1) / (Cx(&1) - cnj z * cexp(ii * Cx s)) - Cx(&1)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[wanl_poisson_kernel] THEN
  ABBREV_TAC `w = cexp(ii * Cx s)` THEN
  SUBGOAL_THEN `norm(w:complex) = &1` ASSUME_TAC THENL
   [EXPAND_TAC "w" THEN REWRITE_TAC[NORM_CEXP_II]; ALL_TAC] THEN
  SUBGOAL_THEN `w * cnj w = Cx(&1)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM COMPLEX_NORM_POW_2] THEN
    ASM_REWRITE_TAC[COMPLEX_POW_ONE]; ALL_TAC] THEN
  SUBGOAL_THEN `~(w - z = Cx(&0))` ASSUME_TAC THENL
   [REWRITE_TAC[COMPLEX_SUB_0] THEN DISCH_THEN SUBST_ALL_TAC THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~(cnj w - cnj z = Cx(&0))` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[GSYM CNJ_SUB; CNJ_EQ_0]; ALL_TAC] THEN
  SUBGOAL_THEN `~(Cx(&1) - cnj z * w = Cx(&0))` ASSUME_TAC THENL
   [REWRITE_TAC[COMPLEX_SUB_0] THEN
    DISCH_THEN(MP_TAC o AP_TERM `norm:complex->real`) THEN
    ASM_REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CNJ; COMPLEX_NORM_CX;
                    REAL_ABS_NUM; REAL_MUL_RID] THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[CX_DIV; CX_SUB; CX_POW; COMPLEX_NORM_POW_2; CNJ_SUB] THEN
  UNDISCH_TAC `w * cnj w = Cx(&1)` THEN
  UNDISCH_TAC `~(w - z = Cx(&0))` THEN
  UNDISCH_TAC `~(cnj w - cnj z = Cx(&0))` THEN
  UNDISCH_TAC `~(Cx(&1) - cnj z * w = Cx(&0))` THEN
  CONV_TAC COMPLEX_FIELD);;

let WANL_UNIT_CIRCLE_DENOMS = prove
 (`!z s. norm z < &1
         ==> ~(cexp(ii * Cx s) = Cx(&0)) /\
             ~(cexp(ii * Cx s) - z = Cx(&0)) /\
             ~(Cx(&1) - cnj z * cexp(ii * Cx s) = Cx(&0))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[CEXP_NZ; COMPLEX_SUB_0] THEN
  CONJ_TAC THEN DISCH_THEN(MP_TAC o AP_TERM `norm:complex->real`) THEN
  REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CNJ; COMPLEX_NORM_CX;
              NORM_CEXP_II; REAL_ABS_NUM; REAL_MUL_RID] THEN
  ASM_REAL_ARITH_TAC);;

let WANL_POISSON_REPRODUCE_POW = prove
 (`!z m. norm z < &1
         ==> ((\s. Cx(wanl_poisson_kernel z (drop s)) * cexp(ii * Cx(drop s)) pow m)
              has_integral (Cx(&2 * pi) * z pow m))
             (interval[vec 0,lift(&2 * pi)])`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `z IN ball(Cx(&0),&1) /\ Cx(&0) IN ball(Cx(&0),&1)`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[COMPLEX_IN_BALL_0; COMPLEX_NORM_0] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(\u:complex. u pow m) holomorphic_on cball(Cx(&0),&1)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HOLOMORPHIC_ON_POW THEN REWRITE_TAC[HOLOMORPHIC_ON_ID];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\u. u pow m / (Cx(&1) - cnj z * u)) holomorphic_on cball(Cx(&0),&1)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HOLOMORPHIC_ON_DIV THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC HOLOMORPHIC_ON_SUB THEN REWRITE_TAC[HOLOMORPHIC_ON_CONST] THEN
      MATCH_MP_TAC HOLOMORPHIC_ON_MUL THEN
      REWRITE_TAC[HOLOMORPHIC_ON_CONST; HOLOMORPHIC_ON_ID];
      X_GEN_TAC `u:complex` THEN REWRITE_TAC[COMPLEX_IN_CBALL_0] THEN
      DISCH_TAC THEN REWRITE_TAC[COMPLEX_SUB_0] THEN
      DISCH_THEN(MP_TAC o AP_TERM `norm:complex->real`) THEN
      REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CNJ; COMPLEX_NORM_CX;
                  REAL_ABS_NUM] THEN
      MP_TAC(ISPEC `u:complex` NORM_POS_LE) THEN
      MP_TAC(ISPEC `z:complex` NORM_POS_LE) THEN
      SUBGOAL_THEN `norm(z:complex) * norm(u:complex) <= norm z * &1` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[NORM_POS_LE];
        ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\u:complex. u pow m`; `Cx(&0)`; `&1`; `z:complex`]
    CAUCHY_INTEGRAL_CIRCLEPATH_SIMPLE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o MATCH_MP WANL_HAS_INTEGRAL_ANGLE_CIRCLEPATH) THEN
  REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`\u. u pow m / (Cx(&1) - cnj z * u)`; `Cx(&0)`; `&1`;
                 `Cx(&0)`] CAUCHY_INTEGRAL_CIRCLEPATH_SIMPLE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o MATCH_MP WANL_HAS_INTEGRAL_ANGLE_CIRCLEPATH) THEN
  REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`\u:complex. u pow m`; `Cx(&0)`; `&1`; `Cx(&0)`]
    CAUCHY_INTEGRAL_CIRCLEPATH_SIMPLE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o MATCH_MP WANL_HAS_INTEGRAL_ANGLE_CIRCLEPATH) THEN
  REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `((\s. --ii *
          ((ii * cexp(ii * Cx(drop s)) * cexp(ii * Cx(drop s)) pow m /
                 (cexp(ii * Cx(drop s)) - z) +
            ii * cexp(ii * Cx(drop s)) * cexp(ii * Cx(drop s)) pow m /
                 (Cx(&1) - cnj z * cexp(ii * Cx(drop s))) /
                 (cexp(ii * Cx(drop s)) - Cx(&0))) -
           ii * cexp(ii * Cx(drop s)) * cexp(ii * Cx(drop s)) pow m /
                (cexp(ii * Cx(drop s)) - Cx(&0))))
     has_integral
     (--ii * ((Cx(&2) * Cx pi * ii * z pow m +
               Cx(&2) * Cx pi * ii * Cx(&0) pow m /
                 (Cx(&1) - cnj z * Cx(&0))) -
              Cx(&2) * Cx pi * ii * Cx(&0) pow m)))
    (interval[vec 0,lift(&2 * pi)])`
  MP_TAC THENL
   [MATCH_MP_TAC HAS_INTEGRAL_COMPLEX_LMUL THEN
    MATCH_MP_TAC HAS_INTEGRAL_SUB THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC HAS_INTEGRAL_ADD THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `--ii * ((Cx(&2) * Cx pi * ii * z pow m +
             Cx(&2) * Cx pi * ii * Cx(&0) pow m /
               (Cx(&1) - cnj z * Cx(&0))) -
            Cx(&2) * Cx pi * ii * Cx(&0) pow m) =
    Cx(&2 * pi) * z pow m`
  SUBST1_TAC THENL
   [REWRITE_TAC[COMPLEX_MUL_RZERO; COMPLEX_SUB_RZERO; COMPLEX_DIV_1; CX_MUL] THEN
    MP_TAC COMPLEX_POW_II_2 THEN CONV_TAC COMPLEX_RING;
    ALL_TAC] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] HAS_INTEGRAL_EQ) THEN
  X_GEN_TAC `s:real^1` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[WANL_POISSON_KERNEL_CX] THEN
  MP_TAC(SPECL [`z:complex`; `drop s`] WANL_UNIT_CIRCLE_DENOMS) THEN
  ASM_REWRITE_TAC[COMPLEX_SUB_RZERO] THEN
  MP_TAC COMPLEX_POW_II_2 THEN
  ABBREV_TAC `c = cexp(ii * Cx(drop s))` THEN
  CONV_TAC COMPLEX_FIELD);;

let WANL_CEXP_II_2PI = prove
 (`cexp(ii * Cx(&2 * pi)) = Cx(&1)`,
  ONCE_REWRITE_TAC[COMPLEX_MUL_SYM] THEN
  MP_TAC(SPEC `&1` CEXP_INTEGER_2PI) THEN
  REWRITE_TAC[INTEGER_CLOSED; REAL_MUL_LID]);;

let WANL_POISSON_KERNEL_PERIODIC = prove
 (`!z s. wanl_poisson_kernel z (s + &2 * pi) = wanl_poisson_kernel z s`,
  REWRITE_TAC[wanl_poisson_kernel; CX_ADD; COMPLEX_ADD_LDISTRIB; CEXP_ADD;
              WANL_CEXP_II_2PI; COMPLEX_MUL_RID]);;

let WANL_POISSON_KERNEL_POS = prove
 (`!z s. norm z < &1 ==> &0 < wanl_poisson_kernel z s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[wanl_poisson_kernel] THEN
  MATCH_MP_TAC REAL_LT_DIV THEN CONJ_TAC THENL
   [MP_TAC(ISPEC `z:complex` NORM_POS_LE) THEN DISCH_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `x * x < &1 ==> &0 < &1 - x pow 2`) THEN
    MATCH_MP_TAC(REAL_ARITH `x * x <= x * &1 /\ x < &1 ==> x * x < &1`) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_POW_LT THEN REWRITE_TAC[NORM_POS_LT; VECTOR_SUB_EQ] THEN
    MP_TAC(SPECL [`z:complex`; `s:real`] WANL_UNIT_CIRCLE_DENOMS) THEN
    ASM_REWRITE_TAC[COMPLEX_SUB_0] THEN STRIP_TAC THEN ASM_REWRITE_TAC[]]);;

let WANL_CEXP_II_DROP_CONTINUOUS = prove
 (`(\s. cexp(ii * Cx(drop s))) continuous_on (:real^1)`,
  SUBGOAL_THEN `(\s. cexp(ii * Cx(drop s))) = cexp o (\s. ii * Cx(drop s))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN REWRITE_TAC[CONTINUOUS_ON_CEXP] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_LMUL THEN
  MATCH_MP_TAC CONTINUOUS_ON_CX_DROP THEN REWRITE_TAC[CONTINUOUS_ON_ID]);;

let WANL_POISSON_KERNEL_CONTINUOUS = prove
 (`!z. norm z < &1
       ==> (\s. Cx(wanl_poisson_kernel z (drop s))) continuous_on (:real^1)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_EQ THEN
  EXISTS_TAC
   `\s. cexp(ii * Cx(drop s)) / (cexp(ii * Cx(drop s)) - z) +
        Cx(&1) / (Cx(&1) - cnj z * cexp(ii * Cx(drop s))) - Cx(&1)` THEN
  ASM_SIMP_TAC[WANL_POISSON_KERNEL_CX] THEN
  MATCH_MP_TAC CONTINUOUS_ON_ADD THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_DIV THEN
    ASM_SIMP_TAC[WANL_UNIT_CIRCLE_DENOMS; WANL_CEXP_II_DROP_CONTINUOUS] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUB THEN
    REWRITE_TAC[CONTINUOUS_ON_CONST; WANL_CEXP_II_DROP_CONTINUOUS];
    MATCH_MP_TAC CONTINUOUS_ON_SUB THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_DIV THEN
    ASM_SIMP_TAC[WANL_UNIT_CIRCLE_DENOMS; CONTINUOUS_ON_CONST] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUB THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_LMUL THEN
    REWRITE_TAC[WANL_CEXP_II_DROP_CONTINUOUS]]);;

let WANL_POISSON_KERNEL_INTEGRAL = prove
 (`!z. norm z < &1
       ==> ((\s. Cx(wanl_poisson_kernel z (drop s))) has_integral Cx(&2 * pi))
           (interval[vec 0,lift(&2 * pi)])`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`z:complex`; `0`] WANL_POISSON_REPRODUCE_POW) THEN
  ASM_REWRITE_TAC[complex_pow; COMPLEX_MUL_RID]);;

let WANL_POISSON_PRODUCT_ABSINT = prove
 (`!bf z. norm z < &1 /\
         (\x. bf(drop x)) absolutely_integrable_on interval[vec 0,lift(&2 * pi)]
         ==> (\s. Cx(wanl_poisson_kernel z (drop s)) * bf(drop s))
             absolutely_integrable_on interval[vec 0,lift(&2 * pi)]`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`( * ):complex->complex->complex`;
                 `\s. Cx(wanl_poisson_kernel z (drop s))`; `\x. (bf:real->complex)(drop x)`;
                 `interval[vec 0,lift(&2 * pi)]`]
    ABSOLUTELY_INTEGRABLE_BOUNDED_MEASURABLE_PRODUCT) THEN
  REWRITE_TAC[BILINEAR_COMPLEX_MUL] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC MEASURABLE_ON_MEASURABLE_SUBSET THEN
    EXISTS_TAC `(:real^1)` THEN
    ASM_SIMP_TAC[SUBSET_UNIV; MEASURABLE_INTERVAL;
                 CONTINUOUS_IMP_MEASURABLE_ON; WANL_POISSON_KERNEL_CONTINUOUS];
    MATCH_MP_TAC COMPACT_IMP_BOUNDED THEN
    MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
    REWRITE_TAC[COMPACT_INTERVAL] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^1)` THEN
    ASM_SIMP_TAC[SUBSET_UNIV; WANL_POISSON_KERNEL_CONTINUOUS]]);;

let WANL_PERIODIC_REAL_INTEGRAL_SHIFT = prove
 (`!h t. (!x. h(x + &2 * pi) = h x) /\
         h real_integrable_on real_interval[&0,&2 * pi]
         ==> h real_integrable_on real_interval[t - pi,t + pi] /\
             real_integral (real_interval[t - pi,t + pi]) h =
             real_integral (real_interval[&0,&2 * pi]) h`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!x. (h:real->real)(x + (&2 * pi - &0)) = h x` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_SUB_RZERO]; ALL_TAC] THEN
  MP_TAC(ISPECL [`h:real->real`; `&0`; `&2 * pi`; `t - pi`]
    WANL_REAL_INTEGRAL_PERIODIC_OFFSET) THEN
  MP_TAC(ISPECL [`h:real->real`; `&0`; `&2 * pi`; `t - pi`]
    WANL_REAL_INTEGRABLE_PERIODIC_OFFSET) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `((\x. (h:real->real)(x + (t - pi))) has_real_integral
     real_integral (real_interval[&0,&2 * pi]) h) (real_interval[&0,&2 * pi])`
  MP_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    ASM_REWRITE_TAC[GSYM HAS_REAL_INTEGRAL_INTEGRAL];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `--(t - pi)` o MATCH_MP WANL_HAS_REAL_INTEGRAL_OFFSET) THEN
  REWRITE_TAC[REAL_ARITH `(x + --(t - pi)) + (t - pi) = x`;
              REAL_ARITH `&0 - --(t - pi) = t - pi`;
              REAL_ARITH `&2 * pi - --(t - pi) = t + pi`; ETA_AX] THEN
  MESON_TAC[HAS_REAL_INTEGRAL_INTEGRABLE; REAL_INTEGRAL_UNIQUE]);;

let wanl_poisson_integral = new_definition
 `wanl_poisson_integral (bf:real->complex) (z:complex) =
    Cx(inv(&2 * pi)) *
    integral (interval[vec 0,lift(&2 * pi)])
             (\s. Cx(wanl_poisson_kernel z (drop s)) * bf(drop s))`;;

let WANL_POISSON_INTEGRAL_ERROR = prove
 (`!bf z t.
     norm z < &1 /\ (!x. bf(x + &2 * pi) = bf x) /\
     (\x. bf(drop x)) absolutely_integrable_on interval[vec 0,lift(&2 * pi)]
     ==> (\s. wanl_poisson_kernel z s * norm(bf s - bf t)) real_integrable_on
         real_interval[t - pi,t + pi] /\
         norm(wanl_poisson_integral bf z - bf t) <=
         inv(&2 * pi) *
         real_integral (real_interval[t - pi,t + pi])
           (\s. wanl_poisson_kernel z s * norm(bf s - bf t))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(\x. (bf:real->complex)(drop x) - bf t) absolutely_integrable_on
    interval[vec 0,lift(&2 * pi)]`
  ASSUME_TAC THENL
   [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_SUB THEN
    ASM_REWRITE_TAC[ABSOLUTELY_INTEGRABLE_CONST]; ALL_TAC] THEN
  MP_TAC(ISPECL [`\x. (bf:real->complex) x - bf t`; `z:complex`]
    WANL_POISSON_PRODUCT_ABSINT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!x. norm(Cx(wanl_poisson_kernel z (drop x)) * ((bf:real->complex)(drop x) - bf t)) =
        wanl_poisson_kernel z (drop x) * norm(bf(drop x) - bf t)`
  ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`; WANL_POISSON_KERNEL_POS];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\s. wanl_poisson_kernel z s * norm((bf:real->complex) s - bf t))
    real_integrable_on real_interval[&0,&2 * pi]`
  ASSUME_TAC THENL
   [REWRITE_TAC[REAL_INTEGRABLE_ON; IMAGE_LIFT_REAL_INTERVAL; LIFT_NUM] THEN
    REWRITE_TAC[o_DEF] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP ABSOLUTELY_INTEGRABLE_NORM) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o MATCH_MP ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE) THEN
    REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\s. wanl_poisson_kernel z s * norm((bf:real->complex) s - bf t)`;
                 `t:real`] WANL_PERIODIC_REAL_INTEGRAL_SHIFT) THEN
  ASM_REWRITE_TAC[WANL_POISSON_KERNEL_PERIODIC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `((\s. Cx(wanl_poisson_kernel z (drop s)) * (bf:real->complex)(drop s))
     integrable_on interval[vec 0,lift(&2 * pi)])`
  ASSUME_TAC THENL
   [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
    MATCH_MP_TAC WANL_POISSON_PRODUCT_ABSINT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\s. Cx(wanl_poisson_kernel z (drop s)) * (bf:real->complex) t)
     has_integral (Cx(&2 * pi) * bf t)) (interval[vec 0,lift(&2 * pi)])`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HAS_INTEGRAL_COMPLEX_RMUL THEN
    ASM_SIMP_TAC[WANL_POISSON_KERNEL_INTEGRAL]; ALL_TAC] THEN
  SUBGOAL_THEN
   `wanl_poisson_integral bf z - bf t =
    Cx(inv(&2 * pi)) *
    integral (interval[vec 0,lift(&2 * pi)])
      (\s. Cx(wanl_poisson_kernel z (drop s)) * ((bf:real->complex)(drop s) - bf t))`
  SUBST1_TAC THENL
   [REWRITE_TAC[wanl_poisson_integral; COMPLEX_SUB_LDISTRIB] THEN
    MP_TAC(ISPECL
     [`\s. Cx(wanl_poisson_kernel z (drop s)) * (bf:real->complex)(drop s)`;
      `\s. Cx(wanl_poisson_kernel z (drop s)) * (bf:real->complex) t`;
      `interval[vec 0,lift(&2 * pi)]`] INTEGRAL_SUB) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[integrable_on];
      DISCH_THEN(SUBST1_TAC o BETA_RULE)] THEN
    FIRST_ASSUM(SUBST1_TAC o MATCH_MP INTEGRAL_UNIQUE) THEN
    REWRITE_TAC[CX_INV; CX_MUL] THEN
    SUBGOAL_THEN `~(Cx pi = Cx(&0))` MP_TAC THENL
     [REWRITE_TAC[CX_INJ; PI_NZ]; CONV_TAC COMPLEX_FIELD];
    ALL_TAC] THEN
  REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX] THEN
  REWRITE_TAC[REAL_ABS_INV; REAL_ABS_MUL; REAL_ABS_NUM; REAL_ABS_PI] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_LE_INV_EQ] THEN MP_TAC PI_POS THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\s. Cx(wanl_poisson_kernel z (drop s)) * ((bf:real->complex)(drop s) - bf t)`;
    `\s. lift(wanl_poisson_kernel z (drop s) * norm((bf:real->complex)(drop s) - bf t))`;
    `interval[vec 0,lift(&2 * pi)]`] INTEGRAL_NORM_BOUND_INTEGRAL) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN ASM_REWRITE_TAC[];
      FIRST_ASSUM(MP_TAC o MATCH_MP ABSOLUTELY_INTEGRABLE_NORM) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o MATCH_MP ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE) THEN
      REWRITE_TAC[];
      ASM_REWRITE_TAC[LIFT_DROP; REAL_LE_REFL]];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `b = c ==> a <= b ==> a <= c`) THEN
  ASM_SIMP_TAC[REAL_INTEGRAL; IMAGE_LIFT_REAL_INTERVAL; LIFT_NUM; o_DEF]);;

let WANL_CEXP_II_CHORD = prove
 (`!s t. norm(cexp(ii * Cx s) - cexp(ii * Cx t)) =
         norm(cexp(ii * Cx(s - t)) - Cx(&1))`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `cexp(ii * Cx s) - cexp(ii * Cx t) =
                cexp(ii * Cx t) * (cexp(ii * Cx(s - t)) - Cx(&1))`
  SUBST1_TAC THENL
   [REWRITE_TAC[COMPLEX_SUB_LDISTRIB; COMPLEX_MUL_RID; GSYM CEXP_ADD] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[CX_SUB] THEN CONV_TAC COMPLEX_RING;
    REWRITE_TAC[COMPLEX_NORM_MUL; NORM_CEXP_II; REAL_MUL_LID]]);;

let WANL_CEXP_II_CHORD_UPPER = prove
 (`!s t. norm(cexp(ii * Cx s) - cexp(ii * Cx t)) <= abs(s - t)`,
  REWRITE_TAC[WANL_CEXP_II_CHORD; DIST_CEXP_II_1] THEN REPEAT GEN_TAC THEN
  MP_TAC(SPEC `(s - t) / &2` REAL_ABS_SIN_BOUND_LE) THEN REAL_ARITH_TAC);;

let WANL_CEXP_II_CHORD_LOWER = prove
 (`!s t. abs(s - t) <= pi
         ==> &2 / pi * abs(s - t) <= norm(cexp(ii * Cx s) - cexp(ii * Cx t))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[WANL_CEXP_II_CHORD] THEN
  MATCH_MP_TAC WANL_NORM_CEXP_II_SUB_1_LOWER THEN ASM_REWRITE_TAC[]);;

let WANL_POISSON_KERNEL_FAR = prove
 (`!z s w eta. norm z < &1 /\ &0 < eta /\
               eta <= norm(cexp(ii * Cx s) - w) /\ norm(z - w) <= eta / &2
               ==> wanl_poisson_kernel z s <= &4 * (&1 - norm z pow 2) / eta pow 2`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[wanl_poisson_kernel] THEN
  SUBGOAL_THEN `eta / &2 <= norm(cexp(ii * Cx s) - z)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`cexp(ii * Cx s) - z`; `z - w:complex`] NORM_TRIANGLE) THEN
    REWRITE_TAC[COMPLEX_RING `(a - z) + (z - w):complex = a - w`] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &1 - norm(z:complex) pow 2` ASSUME_TAC THENL
   [MP_TAC(ISPEC `z:complex` NORM_POS_LE) THEN DISCH_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `x * x <= &1 ==> &0 <= &1 - x pow 2`) THEN
    MATCH_MP_TAC(REAL_ARITH `x * x <= x * &1 /\ x < &1 ==> x * x <= &1`) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&4 * (&1 - norm(z:complex) pow 2) / eta pow 2 =
                (&1 - norm z pow 2) * inv((eta / &2) pow 2)`
  SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < eta` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC]);;

let WANL_POISSON_KERNEL_REAL_INTEGRAL = prove
 (`!z t. norm z < &1
         ==> (\s. wanl_poisson_kernel z s) real_integrable_on real_interval[t - pi,t + pi] /\
             real_integral (real_interval[t - pi,t + pi]) (\s. wanl_poisson_kernel z s) =
             &2 * pi`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `((\s. wanl_poisson_kernel z s) has_real_integral &2 * pi)
                (real_interval[&0,&2 * pi])`
  ASSUME_TAC THENL
   [REWRITE_TAC[HAS_REAL_INTEGRAL; LIFT_NUM] THEN
    MP_TAC(SPEC `z:complex` WANL_POISSON_KERNEL_INTEGRAL) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o ISPEC `\w:complex. lift(Re w)` o
      MATCH_MP (REWRITE_RULE[IMP_CONJ] HAS_INTEGRAL_LINEAR)) THEN
    REWRITE_TAC[o_DEF; RE_CX] THEN ANTS_TAC THENL
     [REWRITE_TAC[linear; RE_ADD; RE_CMUL; LIFT_ADD; LIFT_CMUL]; ALL_TAC] THEN
    REWRITE_TAC[LIFT_DROP];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\s. wanl_poisson_kernel z s`; `t:real`] WANL_PERIODIC_REAL_INTEGRAL_SHIFT) THEN
  REWRITE_TAC[WANL_POISSON_KERNEL_PERIODIC] THEN
  ANTS_TAC THENL [ASM_MESON_TAC[real_integrable_on]; ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[REAL_INTEGRAL_UNIQUE]);;

let WANL_POISSON_INTEGRAL_BOUNDARY_LIMIT = prove
 (`!g t. g continuous_on sphere(Cx(&0),&1)
         ==> (wanl_poisson_integral (\s. g(cexp(ii * Cx s))) --> g(cexp(ii * Cx t)))
             (at (cexp(ii * Cx t)) within ball(Cx(&0),&1))`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `bf = \s. (g:complex->complex)(cexp(ii * Cx s))` THEN
  SUBGOAL_THEN `!s. cexp(ii * Cx s) IN sphere(Cx(&0),&1)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM COMPLEX_VEC_0; IN_SPHERE_0; NORM_CEXP_II]; ALL_TAC] THEN
  SUBGOAL_THEN `!x. (bf:real->complex)(x + &2 * pi) = bf x` ASSUME_TAC THENL
   [EXPAND_TAC "bf" THEN
    REWRITE_TAC[CX_ADD; COMPLEX_ADD_LDISTRIB; CEXP_ADD; WANL_CEXP_II_2PI; COMPLEX_MUL_RID];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\x. (bf:real->complex)(drop x)) absolutely_integrable_on
    interval[vec 0,lift(&2 * pi)]`
  ASSUME_TAC THENL
   [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_CONTINUOUS THEN EXPAND_TAC "bf" THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^1)` THEN
    REWRITE_TAC[SUBSET_UNIV] THEN
    SUBGOAL_THEN `(\x. (g:complex->complex)(cexp(ii * Cx(drop x)))) =
                  g o (\s. cexp(ii * Cx(drop s)))` SUBST1_TAC THENL
     [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN REWRITE_TAC[WANL_CEXP_II_DROP_CONTINUOUS] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `sphere(Cx(&0),&1)` THEN
    ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE];
    ALL_TAC] THEN
  SUBGOAL_THEN `?B. &0 < B /\ !u. u IN sphere(Cx(&0),&1) ==> norm((g:complex->complex) u) <= B`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`g:complex->complex`; `sphere(Cx(&0),&1)`] COMPACT_CONTINUOUS_IMAGE) THEN
    ASM_REWRITE_TAC[COMPACT_SPHERE] THEN
    DISCH_THEN(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
    REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE];
    ALL_TAC] THEN
  REWRITE_TAC[LIM_WITHIN] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  MP_TAC(SPEC `cexp(ii * Cx t)` (REWRITE_RULE[continuous_on]
   (ASSUME `(g:complex->complex) continuous_on sphere(Cx(&0),&1)`))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN
  ASM_REWRITE_TAC[REAL_HALF] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `del = min d1 pi` THEN
  ABBREV_TAC `eta = &2 / pi * del` THEN
  SUBGOAL_THEN `&0 < del /\ del <= d1 /\ del <= pi /\ &0 < eta` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["eta"; "del"] THEN MP_TAC PI_POS THEN
    REPEAT STRIP_TAC THENL
     [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC; REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  EXISTS_TAC `min (eta / &2) (e * eta pow 2 / (&32 * B))` THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_LT_MIN] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LT_DIV THEN ASM_SIMP_TAC[REAL_POW_LT] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `z:complex` THEN REWRITE_TAC[COMPLEX_IN_BALL_0; REAL_LT_MIN] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`bf:real->complex`; `z:complex`; `t:real`] WANL_POISSON_INTEGRAL_ERROR) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `g(cexp(ii * Cx t)) = (bf:real->complex) t` SUBST1_TAC THENL
   [EXPAND_TAC "bf" THEN REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `C = &8 * B * (&1 - norm(z:complex) pow 2) / eta pow 2` THEN
  SUBGOAL_THEN `&0 <= &1 - norm(z:complex) pow 2 /\
                &1 - norm z pow 2 <= &2 * dist(z,cexp(ii * Cx t))`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`cexp(ii * Cx t)`; `z:complex`] NORM_TRIANGLE_SUB) THEN
    REWRITE_TAC[NORM_CEXP_II; dist] THEN
    MP_TAC(ISPECL [`z:complex`; `cexp(ii * Cx t)`] NORM_SUB) THEN
    MP_TAC(ISPEC `z:complex` NORM_POS_LE) THEN
    UNDISCH_TAC `norm(z:complex) < &1` THEN
    REWRITE_TAC[REAL_POW_2] THEN
    REPEAT STRIP_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `x * x <= x * &1 /\ x < &1 ==> &0 <= &1 - x * x`) THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC(REAL_ARITH
       `&1 - x <= d /\ &0 <= (&1 - x) pow 2 ==> &1 - x * x <= &2 * d`) THEN
      REWRITE_TAC[REAL_LE_POW_2] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= C` ASSUME_TAC THENL
   [EXPAND_TAC "C" THEN MATCH_MP_TAC REAL_LE_MUL THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_DIV THEN ASM_SIMP_TAC[REAL_POW_LE; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `C < e / &2` ASSUME_TAC THENL
   [EXPAND_TAC "C" THEN
    SUBGOAL_THEN `&1 - norm(z:complex) pow 2 < e * eta pow 2 / (&16 * B)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LET_TRANS THEN
      EXISTS_TAC `&2 * dist(z:complex,cexp(ii * Cx t))` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(REAL_ARITH `d < y / &2 ==> &2 * d < y`) THEN
      SUBGOAL_THEN `(e * eta pow 2 / (&16 * B)) / &2 = e * eta pow 2 / (&32 * B)`
      SUBST1_TAC THENL [UNDISCH_TAC `&0 < B` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_TAC THEN
    MP_TAC(SPECL [`&8 * B / eta pow 2`; `&1 - norm(z:complex) pow 2`;
                  `e * eta pow 2 / (&16 * B)`] REAL_LT_LMUL) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
       [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LT_DIV THEN ASM_SIMP_TAC[REAL_POW_LT]];
      ALL_TAC] THEN
    EXPAND_TAC "C" THEN
    MATCH_MP_TAC(REAL_ARITH `a = a' /\ b = b' ==> a < b ==> a' < b'`) THEN
    CONJ_TAC THEN UNDISCH_TAC `&0 < B` THEN UNDISCH_TAC `&0 < eta` THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. s IN real_interval[t - pi,t + pi]
        ==> wanl_poisson_kernel z s * norm((bf:real->complex) s - bf t) <=
            e / &2 * wanl_poisson_kernel z s + C`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
    SUBGOAL_THEN `&0 < wanl_poisson_kernel z s` ASSUME_TAC THENL
     [ASM_SIMP_TAC[WANL_POISSON_KERNEL_POS]; ALL_TAC] THEN
    ASM_CASES_TAC `abs(s - t) < del` THENL
     [SUBGOAL_THEN `norm((bf:real->complex) s - bf t) < e / &2` ASSUME_TAC THENL
       [EXPAND_TAC "bf" THEN REWRITE_TAC[GSYM dist] THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[dist] THEN
        MP_TAC(SPECL [`s:real`; `t:real`] WANL_CEXP_II_CHORD_UPPER) THEN
        ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= C /\ x <= y ==> x <= y + C`) THEN
      CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `wanl_poisson_kernel z s <= &4 * (&1 - norm(z:complex) pow 2) / eta pow 2`
    ASSUME_TAC THENL
     [MATCH_MP_TAC WANL_POISSON_KERNEL_FAR THEN EXISTS_TAC `cexp(ii * Cx t)` THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&2 / pi * abs(s - t)` THEN
        CONJ_TAC THENL
         [EXPAND_TAC "eta" THEN MATCH_MP_TAC REAL_LE_LMUL THEN
          CONJ_TAC THENL
           [MATCH_MP_TAC REAL_LE_DIV THEN MP_TAC PI_POS THEN REAL_ARITH_TAC;
            ASM_REAL_ARITH_TAC];
          MATCH_MP_TAC WANL_CEXP_II_CHORD_LOWER THEN ASM_REAL_ARITH_TAC];
        REWRITE_TAC[GSYM dist] THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `norm((bf:real->complex) s - bf t) <= &2 * B` ASSUME_TAC THENL
     [EXPAND_TAC "bf" THEN
      MATCH_MP_TAC(NORM_ARITH `norm(a:complex) <= B /\ norm(b:complex) <= B
                               ==> norm(a - b) <= &2 * B`) THEN
      CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= y /\ x <= C ==> x <= y + C`) THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(&4 * (&1 - norm(z:complex) pow 2) / eta pow 2) * (&2 * B)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_SIMP_TAC[NORM_POS_LE; REAL_LT_IMP_LE];
      EXPAND_TAC "C" THEN MATCH_MP_TAC REAL_EQ_IMP_LE THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(SPECL [`z:complex`; `t:real`] WANL_POISSON_KERNEL_REAL_INTEGRAL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `real_integral (real_interval[t - pi,t + pi])
      (\s. wanl_poisson_kernel z s * norm((bf:real->complex) s - bf t)) <=
    real_integral (real_interval[t - pi,t + pi])
      (\s. e / &2 * wanl_poisson_kernel z s + C)`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRAL_LE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_INTEGRABLE_ADD THEN
    ASM_SIMP_TAC[REAL_INTEGRABLE_LMUL; REAL_INTEGRABLE_CONST];
    ALL_TAC] THEN
  SUBGOAL_THEN `real_integral (real_interval[t - pi,t + pi]) (\s:real. C) =
                C * ((t + pi) - (t - pi))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRAL_CONST THEN MP_TAC PI_POS THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_INTEGRAL_ADD; REAL_INTEGRABLE_LMUL; REAL_INTEGRABLE_CONST;
               REAL_INTEGRAL_LMUL] THEN
  DISCH_TAC THEN REWRITE_TAC[dist] THEN
  UNDISCH_TAC
   `norm(wanl_poisson_integral bf z - (bf:real->complex) t) <=
    inv(&2 * pi) *
    real_integral (real_interval[t - pi,t + pi])
      (\s. wanl_poisson_kernel z s * norm(bf s - bf t))` THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `inv(&2 * pi) * (e / &2 * &2 * pi + C * ((t + pi) - (t - pi)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `inv(&2 * pi) *
                real_integral (real_interval[t - pi,t + pi])
                  (\s. wanl_poisson_kernel z s * norm((bf:real->complex) s - bf t))` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_REWRITE_TAC[REAL_LE_INV_EQ] THEN MP_TAC PI_POS THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `inv(&2 * pi) * (e / &2 * &2 * pi + C * ((t + pi) - (t - pi))) =
                e / &2 + C`
  SUBST1_TAC THENL
   [MP_TAC PI_POS THEN CONV_TAC REAL_FIELD; ASM_REAL_ARITH_TAC]);;

let WANL_POISSON_KERNEL_RE_FORM = prove
 (`!w s. norm w < &1
         ==> wanl_poisson_kernel w s =
             &2 * Re(cexp(ii * Cx s) / (cexp(ii * Cx s) - w)) - &1`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`w:complex`; `s:real`] WANL_POISSON_KERNEL_CX) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o AP_TERM `Re`) THEN REWRITE_TAC[RE_CX] THEN
  DISCH_THEN SUBST1_TAC THEN
  MP_TAC(SPECL [`w:complex`; `s:real`] WANL_UNIT_CIRCLE_DENOMS) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `cnj(cexp(ii * Cx s)) = inv(cexp(ii * Cx s))` MP_TAC THENL
   [REWRITE_TAC[CNJ_CEXP; CNJ_MUL; CNJ_II; CNJ_CX; GSYM CEXP_NEG] THEN
    AP_TERM_TAC THEN CONV_TAC COMPLEX_RING;
    ALL_TAC] THEN
  ABBREV_TAC `e = cexp(ii * Cx s)` THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `Cx(&1) / (Cx(&1) - cnj w * e) = cnj(e / (e - w))` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[CNJ_DIV; CNJ_SUB] THEN
    UNDISCH_TAC `~(e = Cx(&0))` THEN UNDISCH_TAC `~(e - w = Cx(&0))` THEN
    UNDISCH_TAC `~(Cx(&1) - cnj w * e = Cx(&0))` THEN CONV_TAC COMPLEX_FIELD;
    REWRITE_TAC[RE_ADD; RE_SUB; RE_CNJ; RE_CX] THEN REAL_ARITH_TAC]);;

let WANL_CIRCLE_CAUCHY_INTEGRAL_HOLOMORPHIC = prove
 (`!g. g continuous_on sphere(Cx(&0),&1)
       ==> (!w. w IN ball(Cx(&0),&1)
                ==> ((\u. g u / (u - w)) has_path_integral
                     path_integral (circlepath(Cx(&0),&1)) (\u. g u / (u - w)))
                    (circlepath(Cx(&0),&1))) /\
           (\w. path_integral (circlepath(Cx(&0),&1)) (\u. g u / (u - w)))
           holomorphic_on ball(Cx(&0),&1)`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!w. w IN ball(Cx(&0),&1)
        ==> ((\u. (g:complex->complex) u / (u - w)) has_path_integral
             path_integral (circlepath(Cx(&0),&1)) (\u. g u / (u - w)))
            (circlepath(Cx(&0),&1))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_PATH_INTEGRAL_INTEGRAL THEN
    MATCH_MP_TAC PATH_INTEGRABLE_CONTINUOUS_CIRCLEPATH THEN
    SIMP_TAC[PATH_IMAGE_CIRCLEPATH; REAL_POS] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_DIV THEN
    ASM_SIMP_TAC[CONTINUOUS_ON_SUB; CONTINUOUS_ON_ID; CONTINUOUS_ON_CONST] THEN
    X_GEN_TAC `u:complex` THEN
    REWRITE_TAC[GSYM COMPLEX_VEC_0; IN_SPHERE_0; COMPLEX_SUB_0] THEN
    UNDISCH_TAC `(w:complex) IN ball(Cx(&0),&1)` THEN
    REWRITE_TAC[COMPLEX_IN_BALL_0] THEN MESON_TAC[REAL_LT_REFL];
    ASM_REWRITE_TAC[]] THEN
  ASM_SIMP_TAC[HOLOMORPHIC_ON_OPEN; OPEN_BALL] THEN
  X_GEN_TAC `w:complex` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`g:complex->complex`;
                 `\w. path_integral (circlepath(Cx(&0),&1))
                        (\u. (g:complex->complex) u / (u - w))`;
                 `Cx(&0)`; `&1`; `1`] CAUCHY_NEXT_DERIVATIVE_CIRCLEPATH) THEN
  REWRITE_TAC[ARITH_EQ; COMPLEX_POW_1] THEN
  ASM_SIMP_TAC[PATH_IMAGE_CIRCLEPATH; REAL_POS] THEN
  DISCH_THEN(MP_TAC o SPEC `w:complex`) THEN ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

let WANL_POISSON_INTEGRAL_RE_HOLOMORPHIC = prove
 (`!g. g continuous_on sphere(Cx(&0),&1) /\
       (!u. u IN sphere(Cx(&0),&1) ==> Im(g u) = &0)
       ==> ?H. H holomorphic_on ball(Cx(&0),&1) /\
               !w. w IN ball(Cx(&0),&1)
                   ==> wanl_poisson_integral (\s. g(cexp(ii * Cx s))) w = Cx(Re(H w))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `g:complex->complex` WANL_CIRCLE_CAUCHY_INTEGRAL_HOLOMORPHIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `K = \w. path_integral (circlepath(Cx(&0),&1))
                        (\u. (g:complex->complex) u / (u - w))` THEN
  SUBGOAL_THEN `!s. cexp(ii * Cx s) IN sphere(Cx(&0),&1)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM COMPLEX_VEC_0; IN_SPHERE_0; NORM_CEXP_II]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(\x. (g:complex->complex)(cexp(ii * Cx(drop x)))) continuous_on
    interval[vec 0,lift(&2 * pi)]`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^1)` THEN
    REWRITE_TAC[SUBSET_UNIV] THEN
    SUBGOAL_THEN `(\x. (g:complex->complex)(cexp(ii * Cx(drop x)))) =
                  g o (\s. cexp(ii * Cx(drop s)))` SUBST1_TAC THENL
     [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN REWRITE_TAC[WANL_CEXP_II_DROP_CONTINUOUS] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `sphere(Cx(&0),&1)` THEN
    ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE];
    ALL_TAC] THEN
  ABBREV_TAC `I0 = integral (interval[vec 0,lift(&2 * pi)])
                     (\x. (g:complex->complex)(cexp(ii * Cx(drop x))))` THEN
  SUBGOAL_THEN
   `((\x. (g:complex->complex)(cexp(ii * Cx(drop x)))) has_integral I0)
    (interval[vec 0,lift(&2 * pi)])`
  ASSUME_TAC THENL
   [EXPAND_TAC "I0" THEN MATCH_MP_TAC INTEGRABLE_INTEGRAL THEN
    ASM_SIMP_TAC[INTEGRABLE_CONTINUOUS];
    ALL_TAC] THEN
  EXISTS_TAC `\w. Cx(inv(&2 * pi)) * (Cx(&2) * (--ii * (K:complex->complex) w) - I0)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC HOLOMORPHIC_ON_MUL THEN REWRITE_TAC[HOLOMORPHIC_ON_CONST] THEN
    MATCH_MP_TAC HOLOMORPHIC_ON_SUB THEN REWRITE_TAC[HOLOMORPHIC_ON_CONST] THEN
    MATCH_MP_TAC HOLOMORPHIC_ON_MUL THEN REWRITE_TAC[HOLOMORPHIC_ON_CONST] THEN
    MATCH_MP_TAC HOLOMORPHIC_ON_MUL THEN REWRITE_TAC[HOLOMORPHIC_ON_CONST] THEN
    EXPAND_TAC "K" THEN ASM_REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
  X_GEN_TAC `w:complex` THEN DISCH_TAC THEN
  SUBGOAL_THEN `norm(w:complex) < &1` ASSUME_TAC THENL
   [ASM_MESON_TAC[COMPLEX_IN_BALL_0]; ALL_TAC] THEN
  REWRITE_TAC[wanl_poisson_integral; RE_MUL_CX; CX_MUL] THEN AP_TERM_TAC THEN
  MATCH_MP_TAC INTEGRAL_UNIQUE THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `w:complex` o check (is_forall o concl)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o MATCH_MP WANL_HAS_INTEGRAL_ANGLE_CIRCLEPATH) THEN
  DISCH_THEN(MP_TAC o SPEC `--ii` o MATCH_MP HAS_INTEGRAL_COMPLEX_LMUL) THEN
  DISCH_THEN(ASSUME_TAC o BETA_RULE) THEN
  SUBGOAL_THEN
   `((\x. cexp(ii * Cx(drop x)) * (g:complex->complex)(cexp(ii * Cx(drop x))) /
          (cexp(ii * Cx(drop x)) - w))
     has_integral (--ii * (K:complex->complex) w)) (interval[vec 0,lift(&2 * pi)])`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HAS_INTEGRAL_EQ THEN
    EXISTS_TAC `\x. --ii * ii * cexp(ii * Cx(drop x)) *
                    (g:complex->complex)(cexp(ii * Cx(drop x))) /
                    (cexp(ii * Cx(drop x)) - w)` THEN
    CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN BETA_TAC THEN
      REWRITE_TAC[complex_div] THEN
      CONV_TAC COMPLEX_RING;
      EXPAND_TAC "K" THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\x. Cx(&2) * (cexp(ii * Cx(drop x)) * (g:complex->complex)(cexp(ii * Cx(drop x))) /
                    (cexp(ii * Cx(drop x)) - w)) - g(cexp(ii * Cx(drop x))))
     has_integral (Cx(&2) * (--ii * (K:complex->complex) w) - I0))
    (interval[vec 0,lift(&2 * pi)])`
  MP_TAC THENL
   [MATCH_MP_TAC HAS_INTEGRAL_SUB THEN ASM_SIMP_TAC[HAS_INTEGRAL_COMPLEX_LMUL];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o ISPEC `\z:complex. Cx(Re z)` o
    MATCH_MP (REWRITE_RULE[IMP_CONJ] HAS_INTEGRAL_LINEAR)) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[linear; RE_ADD; RE_CMUL; CX_ADD; COMPLEX_CMUL; CX_MUL];
    ALL_TAC] THEN
  REWRITE_TAC[o_DEF] THEN
  DISCH_THEN(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT] HAS_INTEGRAL_EQ)) THEN
  X_GEN_TAC `x:real^1` THEN DISCH_TAC THEN BETA_TAC THEN
  ABBREV_TAC `e = cexp(ii * Cx(drop x))` THEN
  SUBGOAL_THEN `(g:complex->complex) e = Cx(Re(g e))` SUBST1_TAC THENL
   [REWRITE_TAC[COMPLEX_EQ; RE_CX; IM_CX] THEN EXPAND_TAC "e" THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[WANL_POISSON_KERNEL_RE_FORM] THEN
  SUBGOAL_THEN `e * Cx(Re((g:complex->complex) e)) / (e - w) =
                Cx(Re(g e)) * (e / (e - w))`
  SUBST1_TAC THENL [REWRITE_TAC[complex_div] THEN CONV_TAC COMPLEX_RING; ALL_TAC] THEN
  REWRITE_TAC[RE_SUB; RE_MUL_CX; RE_CX; GSYM CX_MUL] THEN AP_TERM_TAC THEN
  REAL_ARITH_TAC);;

(* ========================================================================= *)
(* Holomorphic maps are smooth, and real parts of holomorphic                *)
(* maps have zero flat Laplacian.                                            *)
(* ========================================================================= *)

(* WANL_HOLOMORPHIC_SMOOTH is a renamed copy of BEL_HOLOMORPHIC_SMOOTH of    *)
(* pc_an_beltrami.ml, which is not loaded here (it is large and unrelated).  *)

let WANL_HOLOMORPHIC_SMOOTH = prove
 (`!f s. open s /\ f holomorphic_on s ==> smooth_map_on s f`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[smooth_map_on] THEN
  SUBGOAL_THEN
   `!n (g:complex->complex). g holomorphic_on s
         ==> continuously_differentiable n s g`
   (fun th -> ASM_MESON_TAC[th]) THEN
  INDUCT_TAC THENL
   [REWRITE_TAC[CONTINUOUSLY_DIFFERENTIABLE_0] THEN
    MESON_TAC[HOLOMORPHIC_ON_IMP_CONTINUOUS_ON];
    ALL_TAC] THEN
  X_GEN_TAC `g:complex->complex` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[CONTINUOUSLY_DIFFERENTIABLE_WITHIN_OPEN] THEN
  EXISTS_TAC `\x:complex h:complex. complex_derivative g x * h` THEN
  CONJ_TAC THENL
   [X_GEN_TAC `x:complex` THEN DISCH_TAC THEN
    REWRITE_TAC[GSYM has_complex_derivative] THEN
    REWRITE_TAC[HAS_COMPLEX_DERIVATIVE_DIFFERENTIABLE] THEN
    ASM_MESON_TAC[HOLOMORPHIC_ON_IMP_DIFFERENTIABLE_AT];
    X_GEN_TAC `h:complex` THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC HOLOMORPHIC_ON_MUL THEN
    ASM_SIMP_TAC[ETA_AX; HOLOMORPHIC_COMPLEX_DERIVATIVE; HOLOMORPHIC_ON_CONST]]);;

let WANL_HOLOMORPHIC_FD = prove
 (`!(G:complex->complex) U z.
        open U /\ G holomorphic_on U /\ z IN U
        ==> frechet_derivative G (at z) = (\h. complex_derivative G z * h)`,
  REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
  REWRITE_TAC[GSYM has_complex_derivative] THEN
  REWRITE_TAC[HAS_COMPLEX_DERIVATIVE_DIFFERENTIABLE] THEN
  ASM_MESON_TAC[HOLOMORPHIC_ON_IMP_DIFFERENTIABLE_AT]);;

let WANL_HOLOMORPHIC_FD2 = prove
 (`!(G:complex->complex) U x b.
        open U /\ G holomorphic_on U /\ x IN U
        ==> frechet_derivative (\z. frechet_derivative G (at z) b) (at x) =
            (\h. (complex_derivative (complex_derivative G) x * b) * h)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `frechet_derivative (\z. complex_derivative G z * b) (at (x:complex))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC WANL_FD_LOCAL_OPEN THEN EXISTS_TAC `U:complex->bool` THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:complex` THEN DISCH_TAC THEN BETA_TAC THEN
    MP_TAC(ISPECL [`G:complex->complex`; `U:complex->bool`; `y:complex`]
           WANL_HOLOMORPHIC_FD) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
  REWRITE_TAC[GSYM has_complex_derivative] THEN
  MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_RMUL_AT THEN
  REWRITE_TAC[ETA_AX; HAS_COMPLEX_DERIVATIVE_DIFFERENTIABLE] THEN
  MATCH_MP_TAC HOLOMORPHIC_ON_IMP_DIFFERENTIABLE_AT THEN
  EXISTS_TAC `U:complex->bool` THEN
  ASM_SIMP_TAC[HOLOMORPHIC_COMPLEX_DERIVATIVE]);;

let WANL_RE_HOLOMORPHIC_HARMONIC = prove
 (`!(G:complex->complex) U x.
        open U /\ G holomorphic_on U /\ x IN U
        ==> llap (\y:real^2. mat 1) (\y. Re(G y)) x = &0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:complex->bool`; `G:complex->complex`; `\v:complex. lift(Re v)`;
                 `x:complex`] WANL_LLAP_LINEAR_IMAGE) THEN
  ASM_SIMP_TAC[WANL_HOLOMORPHIC_SMOOTH; LIFT_DROP] THEN
  ANTS_TAC THENL [REWRITE_TAC[linear; RE_ADD; RE_CMUL; LIFT_ADD; LIFT_CMUL]; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[DIMINDEX_2; SUM_2; COMPLEX_BASIS] THEN
  MP_TAC(ISPECL [`G:complex->complex`; `U:complex->bool`; `x:complex`; `Cx(&1)`]
         WANL_HOLOMORPHIC_FD2) THEN
  MP_TAC(ISPECL [`G:complex->complex`; `U:complex->bool`; `x:complex`; `ii`]
         WANL_HOLOMORPHIC_FD2) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN
  REWRITE_TAC[GSYM COMPLEX_MUL_ASSOC; COMPLEX_MUL_RID] THEN
  REWRITE_TAC[GSYM COMPLEX_POW_2; COMPLEX_POW_II_2; COMPLEX_MUL_RNEG; COMPLEX_MUL_RID;
              RE_NEG] THEN
  REAL_ARITH_TAC);;

(* ========================================================================= *)
(* The Dirichlet problem on discs of real^2 with continuous                  *)
(* boundary data g on sphere(a,r) and values in real^K.  Inside the disc     *)
(* wanl_dsol a r g is the Poisson integral of each component, rescaled to    *)
(* the unit disc; on and outside the circle it is g.                         *)
(* ========================================================================= *)

let wanl_dsol = new_definition
 `wanl_dsol (a:real^2) r (g:real^2->real^K) (x:real^2) =
    if x IN ball(a,r)
    then (lambda j. Re(wanl_poisson_integral
                         (\s. Cx(g(a + r % cexp(ii * Cx s))$j)) (inv r % (x - a)))):real^K
    else g x`;;

let WANL_CEXP_II_VECTOR = prove
 (`!t. cexp(ii * Cx t) = vector[cos t; sin t]`,
  GEN_TAC THEN REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2] THEN
  REWRITE_TAC[GSYM RE_DEF; GSYM IM_DEF; RE_CEXP; IM_CEXP; RE_MUL_II; IM_MUL_II;
              RE_CX; IM_CX; REAL_NEG_0; REAL_EXP_0; REAL_MUL_LID]);;

let WANL_WAN_CIRC = prove
 (`!(a:real^2) r t. wan_circ a r t = a + r % cexp(ii * Cx t)`,
  REWRITE_TAC[wan_circ; WANL_CEXP_II_VECTOR]);;

let WANL_UNIT_POLAR = prove
 (`!u:complex. norm u = &1 ==> ?t. u = cexp(ii * Cx t)`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o MATCH_MP COMPLEX_UNIMODULAR_POLAR) THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real` SUBST1_TAC) THEN EXISTS_TAC `t:real` THEN
  REWRITE_TAC[COMPLEX_TRAD; CEXP_EULER; CX_COS; CX_SIN]);;

let WANL_UNIT_SCALE = prove
 (`!(a:real^2) r x. &0 < r
        ==> (x IN ball(a,r) <=> inv r % (x - a) IN ball(Cx(&0),&1)) /\
            (x IN sphere(a,r) <=> norm(inv r % (x - a)) = &1) /\
            a + r % (inv r % (x - a)) = x`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[COMPLEX_IN_BALL_0; IN_BALL; IN_SPHERE; NORM_MUL; REAL_ABS_INV] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < r ==> abs r = r`; VECTOR_MUL_ASSOC; REAL_MUL_RINV;
               REAL_LT_IMP_NZ; VECTOR_MUL_LID] THEN
  REWRITE_TAC[dist; VECTOR_ARITH `a + (x - a):real^2 = x`] THEN
  REWRITE_TAC[NORM_ARITH `norm(a - x:real^2) = norm(x - a)`] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  ASM_SIMP_TAC[GSYM real_div; REAL_LT_LDIV_EQ; REAL_EQ_LDIV_EQ; REAL_MUL_LID]);;

let WANL_DSOL_COMPONENT_CONT = prove
 (`!(a:real^2) r (g:real^2->real^K) j.
        &0 < r /\ g continuous_on sphere(a,r)
        ==> (\u. Cx(g(a + r % u)$j)) continuous_on sphere(Cx(&0),&1) /\
            (!u. u IN sphere(Cx(&0),&1) ==> Im(Cx(g(a + r % u)$j)) = &0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[IM_CX] THEN
  SUBGOAL_THEN `(\u. Cx((g:real^2->real^K)(a + r % u)$j)) =
                (\v. Cx(drop v)) o ((\x. lift(g x$j)) o (\u. a + r % u))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_DROP]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN
    REWRITE_TAC[linear; DROP_ADD; DROP_CMUL; CX_ADD; CX_MUL; COMPLEX_CMUL]] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
   [SIMP_TAC[CONTINUOUS_ON_ADD; CONTINUOUS_ON_CONST; CONTINUOUS_ON_CMUL; CONTINUOUS_ON_ID];
    ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `sphere(a:real^2,r)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_LIFT_COMPONENT_COMPOSE THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_SPHERE] THEN
    REWRITE_TAC[NORM_ARITH `dist(a:real^2,a + y) = norm y`; NORM_MUL; GSYM COMPLEX_VEC_0;
                NORM_ARITH `dist(vec 0:real^2,y) = norm y`] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < r ==> abs r = r`; REAL_MUL_RID]]);;

let WANL_SMOOTH_MAP_ON_EQ = prove
 (`!s (f:real^M->real^N) g.
        open s /\ (!x. x IN s ==> f x = g x) /\ smooth_map_on s f
        ==> smooth_map_on s g`,
  REWRITE_TAC[smooth_map_on] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_EQ_OPEN THEN
  EXISTS_TAC `f:real^M->real^N` THEN ASM_REWRITE_TAC[]);;

let WANL_DSOL_HOLO = prove
 (`!(a:real^2) r (g:real^2->real^K).
        &0 < r /\ g continuous_on sphere(a,r)
        ==> ?H. (!j. 1 <= j /\ j <= dimindex(:K) ==> (H j) holomorphic_on ball(a,r)) /\
                (!x j. x IN ball(a,r) /\ 1 <= j /\ j <= dimindex(:K)
                       ==> (wanl_dsol a r g x)$j = Re(H j x))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!j. 1 <= j /\ j <= dimindex(:K)
        ==> ?H0. H0 holomorphic_on ball(Cx(&0),&1) /\
                 !w. w IN ball(Cx(&0),&1)
                     ==> wanl_poisson_integral
                           (\s. Cx((g:real^2->real^K)(a + r % cexp(ii * Cx s))$j)) w =
                         Cx(Re(H0 w))`
  (MP_TAC o REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM]) THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPEC `\u. Cx((g:real^2->real^K)(a + r % u)$j)`
           WANL_POISSON_INTEGRAL_RE_HOLOMORPHIC) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    MATCH_MP_TAC WANL_DSOL_COMPONENT_CONT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `H0:num->complex->complex` (LABEL_TAC "H0")) THEN
  EXISTS_TAC `\j x. (H0:num->complex->complex) j (Cx(inv r) * (x - a))` THEN
  CONJ_TAC THENL
   [X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    REMOVE_THEN "H0" (MP_TAC o SPEC `j:num`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `(\x. (H0:num->complex->complex) j (Cx(inv r) * (x - a))) =
      H0 j o (\x. Cx(inv r) * (x - a))` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC HOLOMORPHIC_ON_COMPOSE THEN CONJ_TAC THENL
     [SIMP_TAC[HOLOMORPHIC_ON_MUL; HOLOMORPHIC_ON_CONST; HOLOMORPHIC_ON_SUB;
               HOLOMORPHIC_ON_ID];
      MATCH_MP_TAC HOLOMORPHIC_ON_SUBSET THEN EXISTS_TAC `ball(Cx(&0),&1)` THEN
      ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; GSYM COMPLEX_CMUL] THEN
      X_GEN_TAC `x:complex` THEN
      MP_TAC(ISPECL [`a:real^2`; `r:real`; `x:complex`] WANL_UNIT_SCALE) THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`x:complex`; `j:num`] THEN STRIP_TAC THEN BETA_TAC THEN
  REMOVE_THEN "H0" (MP_TAC o SPEC `j:num`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[wanl_dsol; LAMBDA_BETA] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `inv r % (x - a:complex)`) THEN
  MP_TAC(ISPECL [`a:real^2`; `r:real`; `x:complex`] WANL_UNIT_SCALE) THEN
  ASM_SIMP_TAC[] THEN DISCH_THEN(K ALL_TAC) THEN
  REWRITE_TAC[COMPLEX_CMUL] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[RE_CX]);;

let WANL_DSOL_SMOOTH = prove
 (`!(a:real^2) r (g:real^2->real^K).
        &0 < r /\ g continuous_on sphere(a,r)
        ==> smooth_map_on (ball(a,r)) (wanl_dsol a r g) /\
            (!x j. x IN ball(a,r) /\ 1 <= j /\ j <= dimindex(:K)
                   ==> llap (\y:real^2. mat 1) (\y. wanl_dsol a r g y$j) x = &0)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP WANL_DSOL_HOLO) THEN
  DISCH_THEN(X_CHOOSE_THEN `H:num->complex->complex` STRIP_ASSUME_TAC) THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`ball(a:real^2,r)`; `wanl_dsol a r (g:real^2->real^K)`]
           SMOOTH_MAP_ON_COMPONENTWISE) THEN
    REWRITE_TAC[OPEN_BALL] THEN DISCH_THEN SUBST1_TAC THEN
    X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    MATCH_MP_TAC WANL_SMOOTH_MAP_ON_EQ THEN
    EXISTS_TAC `(\z:complex. lift(Re z)) o (H:num->complex->complex) k` THEN
    ASM_SIMP_TAC[OPEN_BALL; o_THM] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_LINEAR_O THEN
    ASM_SIMP_TAC[OPEN_BALL; WANL_HOLOMORPHIC_SMOOTH] THEN
    REWRITE_TAC[linear; RE_ADD; RE_CMUL; LIFT_ADD; LIFT_CMUL];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`x:complex`; `j:num`] THEN STRIP_TAC THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `llap (\y:real^2. mat 1) (\y. Re((H:num->complex->complex) j y)) x` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LLAP_LOCAL THEN EXISTS_TAC `ball(a:complex,r)` THEN
    ASM_SIMP_TAC[OPEN_BALL];
    MATCH_MP_TAC WANL_RE_HOLOMORPHIC_HARMONIC THEN
    EXISTS_TAC `ball(a:complex,r)` THEN ASM_SIMP_TAC[OPEN_BALL; ETA_AX]]);;

(* ------------------------------------------------------------------------- *)
(* Boundary values and continuity on the closed disc.                        *)
(* ------------------------------------------------------------------------- *)

let WANL_DSOL_BOUNDARY_LIMIT = prove
 (`!(a:real^2) r (g:real^2->real^K) y0.
        &0 < r /\ g continuous_on sphere(a,r) /\ y0 IN sphere(a,r)
        ==> (wanl_dsol a r g --> g y0) (at y0 within ball(a,r))`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[LIM_COMPONENTWISE_LIFT] THEN
  X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  ABBREV_TAC `PI = wanl_poisson_integral
                     (\s. Cx((g:real^2->real^K)(a + r % cexp(ii * Cx s))$j))` THEN
  ABBREV_TAC `u0 = inv r % (y0 - a:real^2)` THEN
  SUBGOAL_THEN `norm(u0:complex) = &1 /\ a + r % u0 = y0` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`a:real^2`; `r:real`; `y0:real^2`] WANL_UNIT_SCALE) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(X_CHOOSE_THEN `t0:real` ASSUME_TAC o MATCH_MP WANL_UNIT_POLAR) THEN
  MP_TAC(ISPECL [`\u. Cx((g:real^2->real^K)(a + r % u)$j)`; `t0:real`]
         WANL_POISSON_INTEGRAL_BOUNDARY_LIMIT) THEN
  ANTS_TAC THENL
   [MP_TAC(ISPECL [`a:real^2`; `r:real`; `g:real^2->real^K`; `j:num`]
           WANL_DSOL_COMPONENT_CONT) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `((PI o (\x:real^2. inv r % (x - a))) --> Cx((g:real^2->real^K) y0$j))
    (at y0 within ball(a,r))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC LIM_COMPOSE_WITHIN THEN
    MAP_EVERY EXISTS_TAC [`ball(Cx(&0),&1)`; `u0:complex`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC LIM_AT_WITHIN THEN EXPAND_TAC "u0" THEN
      MATCH_MP_TAC LIM_CMUL THEN MATCH_MP_TAC LIM_SUB THEN
      REWRITE_TAC[LIM_AT_ID; LIM_CONST];
      ALL_TAC] THEN
    REWRITE_TAC[EVENTUALLY_WITHIN] THEN EXISTS_TAC `&1` THEN
    REWRITE_TAC[REAL_LT_01] THEN X_GEN_TAC `x:real^2` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`a:real^2`; `r:real`; `x:real^2`] WANL_UNIT_SCALE) THEN
    ASM_SIMP_TAC[] THEN STRIP_TAC THEN DISCH_TAC THEN
    UNDISCH_TAC `inv r % (x - a:real^2) IN ball(Cx(&0),&1)` THEN
    ASM_REWRITE_TAC[COMPLEX_IN_BALL_0; REAL_LT_REFL];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [LIM_COMPONENTWISE_LIFT]) THEN
  DISCH_THEN(MP_TAC o SPEC `1`) THEN
  REWRITE_TAC[DIMINDEX_2; ARITH; GSYM RE_DEF; RE_CX; o_THM] THEN
  DISCH_TAC THEN MATCH_MP_TAC LIM_TRANSFORM_WITHIN THEN
  EXISTS_TAC `\x:real^2. lift(Re((PI:complex->complex)(inv r % (x - a))))` THEN
  EXISTS_TAC `&1` THEN ASM_REWRITE_TAC[REAL_LT_01] THEN
  X_GEN_TAC `x:real^2` THEN STRIP_TAC THEN
  ASM_SIMP_TAC[wanl_dsol; LAMBDA_BETA]);;

let WANL_DSOL_CONTINUOUS = prove
 (`!(a:real^2) r (g:real^2->real^K).
        &0 < r /\ g continuous_on sphere(a,r)
        ==> wanl_dsol a r g continuous_on cball(a,r) /\
            (!x. x IN sphere(a,r) ==> wanl_dsol a r g x = g x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!x. x IN sphere(a,r) ==> wanl_dsol a r (g:real^2->real^K) x = g x`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[wanl_dsol] THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN
    UNDISCH_TAC `(x:real^2) IN sphere(a,r)` THEN UNDISCH_TAC `(x:real^2) IN ball(a,r)` THEN
    REWRITE_TAC[IN_BALL; IN_SPHERE] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
  X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
  ASM_CASES_TAC `(x:real^2) IN ball(a,r)` THENL
   [MATCH_MP_TAC CONTINUOUS_AT_WITHIN THEN
    MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `ball(a:real^2,r)` THEN
    MP_TAC(ISPECL [`a:real^2`; `r:real`; `g:real^2->real^K`] WANL_DSOL_SMOOTH) THEN
    ASM_SIMP_TAC[OPEN_BALL];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^2) IN sphere(a,r)` ASSUME_TAC THENL
   [UNDISCH_TAC `(x:real^2) IN cball(a,r)` THEN UNDISCH_TAC `~((x:real^2) IN ball(a,r))` THEN
    REWRITE_TAC[IN_BALL; IN_CBALL; IN_SPHERE] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[CONTINUOUS_WITHIN] THEN
  SUBGOAL_THEN `cball(a:real^2,r) = ball(a,r) UNION sphere(a,r)` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_UNION; IN_BALL; IN_CBALL; IN_SPHERE] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[LIM_WITHIN_UNION] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `(x:real^2) IN sphere(a,r)`)]) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC WANL_DSOL_BOUNDARY_LIMIT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC LIM_TRANSFORM_WITHIN THEN
  EXISTS_TAC `g:real^2->real^K` THEN EXISTS_TAC `&1` THEN REWRITE_TAC[REAL_LT_01] THEN
  CONJ_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[GSYM CONTINUOUS_WITHIN] THEN
  MP_TAC(GEN_REWRITE_RULE I [CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN]
          (ASSUME `(g:real^2->real^K) continuous_on sphere(a,r)`)) THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The value at the centre is the circle mean of the data.                   *)
(* ------------------------------------------------------------------------- *)

let WANL_CIRCLE_MAP_CONTINUOUS = prove
 (`!(a:real^2) r (g:real^2->real^K) s.
        &0 < r /\ g continuous_on sphere(a,r)
        ==> (\t. g(a + r % cexp(ii * Cx(drop t)))) continuous_on s`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\t. (g:real^2->real^K)(a + r % cexp(ii * Cx(drop t)))) =
                g o (\t. a + r % cexp(ii * Cx(drop t)))` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_ADD THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
    MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^1)` THEN
    REWRITE_TAC[SUBSET_UNIV; WANL_CEXP_II_DROP_CONTINUOUS];
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `sphere(a:real^2,r)` THEN
    ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_SPHERE] THEN
    REWRITE_TAC[NORM_ARITH `dist(a:real^2,a + y) = norm y`; NORM_MUL; NORM_CEXP_II] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < r ==> abs r = r`; REAL_MUL_RID]]);;

let WANL_DSOL_CENTRE = prove
 (`!(a:real^2) r (g:real^2->real^K).
        &0 < r /\ g continuous_on sphere(a,r)
        ==> wanl_dsol a r g a =
            inv(&2 * pi) % integral (interval[vec 0,lift(&2 * pi)])
                             (\t. g(wan_circ a r (drop t)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[WANL_WAN_CIRC] THEN
  ASM_SIMP_TAC[wanl_dsol; CENTRE_IN_BALL; CART_EQ; LAMBDA_BETA; VECTOR_MUL_COMPONENT] THEN
  X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  REWRITE_TAC[VECTOR_SUB_REFL; VECTOR_MUL_RZERO] THEN
  REWRITE_TAC[wanl_poisson_integral; wanl_poisson_kernel; NORM_0; VECTOR_SUB_RZERO;
              NORM_CEXP_II] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[COMPLEX_MUL_LID; RE_MUL_CX] THEN
  AP_TERM_TAC THEN
  SUBGOAL_THEN
   `(\t. (g:real^2->real^K)(a + r % cexp(ii * Cx(drop t)))) integrable_on
    interval[vec 0,lift(&2 * pi)]`
  ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_CONTINUOUS THEN MATCH_MP_TAC WANL_CIRCLE_MAP_CONTINUOUS THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[INTEGRAL_COMPONENT] THEN
  SUBGOAL_THEN
   `(\t. Cx((g:real^2->real^K)(a + r % cexp(ii * Cx(drop t)))$j)) integrable_on
    interval[vec 0,lift(&2 * pi)]`
  ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_CONTINUOUS THEN
    SUBGOAL_THEN
     `(\t. Cx((g:real^2->real^K)(a + r % cexp(ii * Cx(drop t)))$j)) =
      (\v. Cx(drop v)) o (\t. lift(g(a + r % cexp(ii * Cx(drop t)))$j))`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_DROP]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_LIFT_COMPONENT_COMPOSE THEN
      MATCH_MP_TAC WANL_CIRCLE_MAP_CONTINUOUS THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN
      REWRITE_TAC[linear; DROP_ADD; DROP_CMUL; CX_ADD; CX_MUL; COMPLEX_CMUL]];
    ALL_TAC] THEN
  ASM_SIMP_TAC[RE_DEF; INTEGRAL_COMPONENT] THEN
  REWRITE_TAC[GSYM RE_DEF; RE_CX]);;

(* ------------------------------------------------------------------------- *)
(* Uniqueness: harmonic maps on a closed ball are determined by their values *)
(* on the sphere.                                                            *)
(* ------------------------------------------------------------------------- *)

let WANL_HARMONIC_EQ_CBALL = prove
 (`!(a:real^N) r (u:real^N->real^K) v.
        &0 < r /\ u continuous_on cball(a,r) /\ v continuous_on cball(a,r) /\
        smooth_map_on (ball(a,r)) u /\ smooth_map_on (ball(a,r)) v /\
        (!x j. x IN ball(a,r) /\ 1 <= j /\ j <= dimindex(:K)
               ==> llap (\y:real^N. mat 1) (\y. u y$j) x = &0) /\
        (!x j. x IN ball(a,r) /\ 1 <= j /\ j <= dimindex(:K)
               ==> llap (\y:real^N. mat 1) (\y. v y$j) x = &0) /\
        (!x. x IN sphere(a,r) ==> u x = v x)
        ==> !x. x IN cball(a,r) ==> u x = v x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  REWRITE_TAC[CART_EQ] THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!(p:real^N->real^K) q.
        p continuous_on cball(a,r) /\ q continuous_on cball(a,r) /\
        smooth_map_on (ball(a,r)) p /\ smooth_map_on (ball(a,r)) q /\
        (!x. x IN ball(a,r) ==> llap (\y:real^N. mat 1) (\y. p y$j) x = &0) /\
        (!x. x IN ball(a,r) ==> llap (\y:real^N. mat 1) (\y. q y$j) x = &0) /\
        (!x. x IN sphere(a,r) ==> p x = q x)
        ==> p x$j <= q x$j`
  (fun th -> MATCH_MP_TAC(REAL_ARITH `a <= b /\ b <= a ==> a = b`) THEN
             CONJ_TAC THEN MATCH_MP_TAC th THEN ASM_SIMP_TAC[]) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`a:real^N`; `r:real`;
                 `\y:real^N. (p:real^N->real^K) y$j - (q:real^N->real^K) y$j`; `&0`]
         WANL_MAXP_SUB) THEN
  ANTS_TAC THENL [ALL_TAC; DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN
                           ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC] THEN
  ASM_REWRITE_TAC[LIFT_SUB] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUB THEN CONJ_TAC THEN
    MATCH_MP_TAC CONTINUOUS_ON_LIFT_COMPONENT_COMPOSE THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN
    ASM_SIMP_TAC[OPEN_BALL; SMOOTH_MAP_ON_LIFT_COMPONENT];
    X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`ball(a:real^N,r)`; `\y:real^N. (p:real^N->real^K) y$j`;
                   `\y:real^N. (q:real^N->real^K) y$j`; `&1`; `--(&1)`; `y:real^N`]
           WANL_LLAP_LINEAR) THEN
    ASM_SIMP_TAC[OPEN_BALL; SMOOTH_MAP_ON_LIFT_COMPONENT] THEN
    REWRITE_TAC[REAL_ARITH `&1 * x + --(&1) * y = x - y`] THEN
    DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC;
    X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:real^N` o check (fun th ->
      can (find_term (fun u -> u = `sphere(a:real^N,r)`)) (concl th))) THEN
    ASM_SIMP_TAC[REAL_SUB_REFL; REAL_LE_REFL]]);;

let WANL_DSOL_UNIQUE = prove
 (`!(a:real^2) r (u:real^2->real^K).
        &0 < r /\ u continuous_on cball(a,r) /\ smooth_map_on (ball(a,r)) u /\
        (!x j. x IN ball(a,r) /\ 1 <= j /\ j <= dimindex(:K)
               ==> llap (\y:real^2. mat 1) (\y. u y$j) x = &0)
        ==> !x. x IN cball(a,r) ==> wanl_dsol a r u x = u x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(u:real^2->real^K) continuous_on sphere(a,r)` ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `cball(a:real^2,r)` THEN
    ASM_REWRITE_TAC[SPHERE_SUBSET_CBALL];
    ALL_TAC] THEN
  MATCH_MP_TAC WANL_HARMONIC_EQ_CBALL THEN REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`a:real^2`; `r:real`; `u:real^2->real^K`] WANL_DSOL_CONTINUOUS) THEN
  MP_TAC(ISPECL [`a:real^2`; `r:real`; `u:real^2->real^K`] WANL_DSOL_SMOOTH) THEN
  ASM_SIMP_TAC[]);;

(* ========================================================================= *)
(* Circle and disc (sub)mean value properties.                               *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Disc sub-means from circle sub-means, by polar coordinates                *)
(* (FUBINI_POLAR), adapted from earlier HOL Light work; the circle means are *)
(* taken over [0,2pi] directly (no circlepath conversion, no exceptional     *)
(* set).                                                                     *)
(* ------------------------------------------------------------------------- *)

(* Adapted from earlier HOL Light work. *)

let WANL_CONTINUOUS_BOUNDED_ABSOLUTELY_INTEGRABLE = prove
 (`!(f:real^M->real^N) s B.
     f continuous_on s /\ measurable s /\ (!x. x IN s ==> norm(f x) <= B)
     ==> f absolutely_integrable_on s`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_ABSOLUTELY_INTEGRABLE THEN
  EXISTS_TAC `\x:real^M. lift B` THEN
  ASM_SIMP_TAC[INTEGRABLE_ON_CONST; LIFT_DROP] THEN
  MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
  ASM_SIMP_TAC[MEASURABLE_IMP_LEBESGUE_MEASURABLE]);;

(* Adapted from earlier HOL Light work. *)

let WANL_MEASURE_BALL_TRANSLATE = prove
 (`!t:real^N c:real^N s. measure(ball(t,s)) = measure(ball(c,s))`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `ball(t:real^N,s) = IMAGE (\x. (t - c) + x) (ball(c,s))`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM BALL_TRANSLATION; VECTOR_ARITH `(t - c) + c:real^N = t`];
    REWRITE_TAC[MEASURE_TRANSLATION]]);;

let WANL_DISC_SUBMEAN = prove
 (`!u:complex->real c s.
     &0 < s /\ (lift o u) continuous_on cball(c,s) /\
     (!rho. &0 < rho /\ rho < s
            ==> &2 * pi * u c <=
                drop(integral (interval[vec 0,lift(&2 * pi)])
                       (\t. lift(u(c + Cx rho * cexp(ii * Cx(drop t)))))))
     ==> u c * measure(ball(c,s)) <= drop(integral (ball(c,s)) (lift o u))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\z. lift((u:complex->real)(c + z) - u c)) continuous_on cball(Cx(&0),s)`
  ASSUME_TAC THENL
   [REWRITE_TAC[LIFT_SUB] THEN MATCH_MP_TAC CONTINUOUS_ON_SUB THEN
    REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
    SUBGOAL_THEN `(\z. lift((u:complex->real)(c + z))) = (lift o u) o (\z. c + z)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
    SIMP_TAC[CONTINUOUS_ON_ADD; CONTINUOUS_ON_CONST; CONTINUOUS_ON_ID] THEN
    REWRITE_TAC[GSYM CBALL_TRANSLATION; COMPLEX_ADD_RID] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?B. !z. z IN cball(Cx(&0),s) ==> norm(lift((u:complex->real)(c + z) - u c)) <= B`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\z. lift((u:complex->real)(c + z) - u c)`; `cball(Cx(&0),s)`] COMPACT_CONTINUOUS_IMAGE) THEN
    ASM_REWRITE_TAC[COMPACT_CBALL] THEN
    DISCH_THEN(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
    REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\z. lift((u:complex->real)(c + z) - u c)) absolutely_integrable_on ball(Cx(&0),s)` ASSUME_TAC THENL
   [MATCH_MP_TAC WANL_CONTINUOUS_BOUNDED_ABSOLUTELY_INTEGRABLE THEN EXISTS_TAC `B:real` THEN
    REWRITE_TAC[MEASURABLE_BALL] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `cball(Cx(&0),s)` THEN
      ASM_REWRITE_TAC[BALL_SUBSET_CBALL];
      ASM_MESON_TAC[SUBSET; BALL_SUBSET_CBALL]];
    ALL_TAC] THEN
  MP_TAC(ISPEC `\z. if z IN ball(Cx(&0),s) then lift((u:complex->real)(c + z) - u c) else vec 0` FUBINI_POLAR) THEN
  ASM_REWRITE_TAC[ABSOLUTELY_INTEGRABLE_RESTRICT_UNIV; INTEGRAL_RESTRICT_UNIV] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!r. &0 <= drop r ==>
   &0 <= drop(integral (interval [vec 0,lift (&2 * pi)])
           (\t. drop r % (if Cx (drop r) * cexp (ii * Cx (drop t)) IN ball (Cx (&0),s)
                 then lift((u:complex->real)(c + Cx (drop r) * cexp (ii * Cx (drop t))) - u c)
                 else vec 0)))` ASSUME_TAC THENL
   [X_GEN_TAC `r:real^1` THEN ABBREV_TAC `rho = drop r` THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM COMPLEX_VEC_0; IN_BALL_0; COMPLEX_NORM_MUL; COMPLEX_NORM_CX;
              NORM_CEXP_II; REAL_MUL_RID] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`] THEN
    ASM_CASES_TAC `rho < s` THEN
  ASM_REWRITE_TAC[VECTOR_MUL_RZERO; INTEGRAL_0; DROP_VEC; REAL_LE_REFL] THEN
  ASM_CASES_TAC `rho = &0` THEN
  ASM_REWRITE_TAC[VECTOR_MUL_LZERO; INTEGRAL_0; DROP_VEC; REAL_LE_REFL] THEN
  SUBGOAL_THEN `&0 < rho` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &2 * pi` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN REWRITE_TAC[PI_POS] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\t. lift((u:complex->real)(c + Cx rho * cexp(ii * Cx(drop t))))) has_integral
     integral (interval[vec 0,lift(&2 * pi)])
       (\t. lift(u(c + Cx rho * cexp(ii * Cx(drop t))))))
    (interval[vec 0,lift(&2 * pi)])`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM HAS_INTEGRAL_INTEGRAL] THEN MATCH_MP_TAC INTEGRABLE_CONTINUOUS THEN
    SUBGOAL_THEN `(\t. lift((u:complex->real)(c + Cx rho * cexp(ii * Cx(drop t))))) =
                  (lift o u) o (\t. c + Cx rho * cexp(ii * Cx(drop t)))` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_ADD THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_LMUL THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^1)` THEN
      REWRITE_TAC[SUBSET_UNIV; WANL_CEXP_II_DROP_CONTINUOUS];
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `cball(c:complex,s)` THEN
      ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_CBALL] THEN
      REWRITE_TAC[NORM_ARITH `dist(c:complex,c + y) = norm y`; COMPLEX_NORM_MUL;
                  COMPLEX_NORM_CX; NORM_CEXP_II; REAL_MUL_RID] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `rho:real` o check (fun th ->
    is_forall(concl th) && can (find_term (fun u -> u = `pi`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`vec 0:real^1`; `lift(&2 * pi)`; `lift((u:complex->real) c)`] HAS_INTEGRAL_CONST) THEN
  ASM_SIMP_TAC[CONTENT_1; LIFT_DROP; DROP_VEC; REAL_LT_IMP_LE; REAL_SUB_RZERO] THEN
  DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP HAS_INTEGRAL_SUB o CONJ (ASSUME
   `((\t. lift((u:complex->real)(c + Cx rho * cexp(ii * Cx(drop t))))) has_integral
     integral (interval[vec 0,lift(&2 * pi)])
       (\t. lift(u(c + Cx rho * cexp(ii * Cx(drop t))))))
    (interval[vec 0,lift(&2 * pi)])`)) THEN
  DISCH_THEN(MP_TAC o SPEC `rho:real` o MATCH_MP HAS_INTEGRAL_CMUL) THEN
  REWRITE_TAC[GSYM LIFT_SUB] THEN
  DISCH_THEN(SUBST1_TAC o MATCH_MP INTEGRAL_UNIQUE) THEN
  REWRITE_TAC[DROP_CMUL; DROP_SUB; LIFT_DROP] THEN
  MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
  ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= drop(integral (ball(Cx(&0),s)) (\z. lift((u:complex->real)(c + z) - u c)))` MP_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (is_eq o concl)) THEN
    MATCH_MP_TAC INTEGRAL_DROP_POS THEN
    ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE] THEN
    X_GEN_TAC `r:real^1` THEN REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `integral (ball(c,s)) (lift o (u:complex->real)) =
   integral (ball(Cx(&0),s)) (\z. lift(u(c + z) - u c)) + measure(ball(c:complex,s)) % lift(u c)` SUBST1_TAC THENL
   [SUBST1_TAC(ISPECL [`c:complex`; `Cx(&0)`; `s:real`] WANL_MEASURE_BALL_TRANSLATE) THEN
    MP_TAC(ISPECL [`ball(Cx(&0),s)`; `lift((u:complex->real) c)`] INTEGRAL_CONST_GEN) THEN
    REWRITE_TAC[MEASURABLE_BALL] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MP_TAC(ISPECL [`\z. lift((u:complex->real)(c + z) - u c)`; `\z:complex. lift((u:complex->real) c)`; `ball(Cx(&0),s)`] INTEGRAL_ADD) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE] THEN
      REWRITE_TAC[integrable_on] THEN EXISTS_TAC `measure(ball(Cx(&0),s)) % lift((u:complex->real) c)` THEN
      MATCH_MP_TAC HAS_INTEGRAL_CONST_GEN THEN REWRITE_TAC[MEASURABLE_BALL];
      ALL_TAC] THEN
    REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    SUBGOAL_THEN `ball(c:complex,s) = IMAGE (\z. c + z) (ball(Cx(&0),s))` SUBST1_TAC THENL
     [REWRITE_TAC[GSYM BALL_TRANSLATION; COMPLEX_ADD_RID]; ALL_TAC] THEN
    REWRITE_TAC[GSYM INTEGRAL_TRANSLATION; o_THM] THEN
    AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM; GSYM LIFT_ADD] THEN GEN_TAC THEN
    AP_TERM_TAC THEN REAL_ARITH_TAC;
    REWRITE_TAC[DROP_ADD; DROP_CMUL; LIFT_DROP] THEN REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Circle means of harmonic maps, circle sub-means of subharmonic functions. *)
(* ------------------------------------------------------------------------- *)

let WANL_CIRCLE_MEAN = prove
 (`!(a:real^2) r (u:real^2->real^K).
        &0 < r /\ u continuous_on cball(a,r) /\ smooth_map_on (ball(a,r)) u /\
        (!x j. x IN ball(a,r) /\ 1 <= j /\ j <= dimindex(:K)
               ==> llap (\y:real^2. mat 1) (\y. u y$j) x = &0)
        ==> u a = inv(&2 * pi) % integral (interval[vec 0,lift(&2 * pi)])
                                  (\t. u(wan_circ a r (drop t)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`a:real^2`; `r:real`; `u:real^2->real^K`] WANL_DSOL_UNIQUE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `a:real^2`) THEN
  ASM_SIMP_TAC[CENTRE_IN_CBALL; REAL_LT_IMP_LE] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC WANL_DSOL_CENTRE THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `cball(a:real^2,r)` THEN
  ASM_REWRITE_TAC[SPHERE_SUBSET_CBALL]);;

let WANL_CIRCLE_SUBMEAN = prove
 (`!(a:real^2) r (h:real^2->real).
        &0 < r /\ (\x. lift(h x)) continuous_on cball(a,r) /\
        smooth_map_on (ball(a,r)) (\x. lift(h x)) /\
        (!x. x IN ball(a,r) ==> &0 <= llap (\y:real^2. mat 1) h x)
        ==> h a <= inv(&2 * pi) *
                   drop(integral (interval[vec 0,lift(&2 * pi)])
                          (\t. lift(h(wan_circ a r (drop t)))))`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `U = wanl_dsol a r (\x:real^2. lift(h x))` THEN
  SUBGOAL_THEN `(\x:real^2. lift(h x)) continuous_on sphere(a,r)` ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `cball(a:real^2,r)` THEN
    ASM_REWRITE_TAC[SPHERE_SUBSET_CBALL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`a:real^2`; `r:real`; `\x:real^2. lift(h x)`] WANL_DSOL_CONTINUOUS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "bd")) THEN
  MP_TAC(ISPECL [`a:real^2`; `r:real`; `\x:real^2. lift(h x)`] WANL_DSOL_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "harm")) THEN
  MP_TAC(ISPECL [`a:real^2`; `r:real`; `\x:real^2. lift(h x)`] WANL_DSOL_CENTRE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`a:real^2`; `r:real`; `\y:real^2. h y - drop((U:real^2->real^1) y)`; `&0`]
         WANL_MAXP_SUB) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[LIFT_SUB; LIFT_DROP] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUB THEN ASM_REWRITE_TAC[ETA_AX];
      MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN ASM_REWRITE_TAC[OPEN_BALL; ETA_AX];
      X_GEN_TAC `y:real^2` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`ball(a:real^2,r)`; `h:real^2->real`;
                     `\y:real^2. drop((U:real^2->real^1) y)`; `&1`; `--(&1)`; `y:real^2`]
             WANL_LLAP_LINEAR) THEN
      ASM_REWRITE_TAC[OPEN_BALL; LIFT_DROP; ETA_AX] THEN
      REWRITE_TAC[REAL_ARITH `&1 * x + --(&1) * y = x - y`] THEN
      DISCH_THEN SUBST1_TAC THEN
      USE_THEN "harm" (MP_TAC o SPECL [`y:real^2`; `1`]) THEN
      REWRITE_TAC[DIMINDEX_1; LE_REFL; GSYM drop; ASSUME `(y:real^2) IN ball(a,r)`] THEN
      DISCH_THEN SUBST1_TAC THEN
      MP_TAC(C MATCH_MP (ASSUME `(y:real^2) IN ball(a,r)`)
              (ASSUME `!x. x IN ball(a:real^2,r) ==> &0 <= llap (\y:real^2. mat 1) h x`)) THEN
      REWRITE_TAC[REAL_SUB_RZERO] THEN DISCH_THEN ACCEPT_TAC;
      X_GEN_TAC `y:real^2` THEN DISCH_TAC THEN
      USE_THEN "bd" (MP_TAC o C MATCH_MP (ASSUME `(y:real^2) IN sphere(a,r)`)) THEN
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[LIFT_DROP; REAL_SUB_REFL; REAL_LE_REFL]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `a:real^2`) THEN
  ASM_SIMP_TAC[CENTRE_IN_CBALL; REAL_LT_IMP_LE; DROP_CMUL] THEN REAL_ARITH_TAC);;

(* ========================================================================= *)
(* The statements WAN_MAX_PRINCIPLE_DISC, WAN_MAX_PRINCIPLE_DISC_BALL,       *)
(* WAN_MEAN_VALUE_2D and WAN_SUBMEAN_2D.                                     *)
(* ========================================================================= *)

let WAN_MAX_PRINCIPLE_DISC = prove
 (`WAN_MAX_PRINCIPLE_DISC_STATEMENT`,
  REWRITE_TAC[WAN_MAX_PRINCIPLE_DISC_STATEMENT] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`a:real^2`; `r:real`; `h:real^2->real`; `M:real`] WANL_MAXP_SUB) THEN
  ASM_SIMP_TAC[REAL_LE_REFL]);;

(* The flat Laplacian of e . h is the combination of the component ones.    *)

let WANL_LLAP_DOT_HARMONIC = prove
 (`!(U:real^N->bool) (h:real^N->real^K) e x.
        open U /\ x IN U /\ smooth_map_on U h /\
        (!j. 1 <= j /\ j <= dimindex(:K) ==> llap (\y:real^N. mat 1) (\y. h y$j) x = &0)
        ==> llap (\y:real^N. mat 1) (\y. e dot h y) x = &0`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `V = vsum(1..dimindex(:N))
                    (\i. frechet_derivative
                           (\z. frechet_derivative (h:real^N->real^K) (at z) (basis i))
                           (at x) (basis i))` THEN
  SUBGOAL_THEN `!j. 1 <= j /\ j <= dimindex(:K) ==> (V:real^K)$j = &0` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "V" THEN REWRITE_TAC[VSUM_COMPONENT] THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `h:real^N->real^K`; `\v:real^K. lift(v$j)`;
                   `x:real^N`] WANL_LLAP_LINEAR_IMAGE) THEN
    ASM_REWRITE_TAC[LIFT_DROP; LINEAR_LIFT_COMPONENT] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `h:real^N->real^K`; `\v:real^K. lift(e dot v)`;
                 `x:real^N`] WANL_LLAP_LINEAR_IMAGE) THEN
  ASM_REWRITE_TAC[LIFT_DROP] THEN ANTS_TAC THENL
   [REWRITE_TAC[linear; DOT_RADD; DOT_RMUL; LIFT_ADD; LIFT_CMUL]; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  SIMP_TAC[GSYM DOT_RSUM; FINITE_NUMSEG] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `V:real^K = vec 0` SUBST1_TAC THENL
   [ASM_SIMP_TAC[CART_EQ; VEC_COMPONENT]; REWRITE_TAC[DOT_RZERO]]);;

let WAN_MAX_PRINCIPLE_DISC_BALL = prove
 (`!kk:K->bool. WAN_MAX_PRINCIPLE_DISC_BALL_STATEMENT kk`,
  GEN_TAC THEN REWRITE_TAC[WAN_MAX_PRINCIPLE_DISC_BALL_STATEMENT] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= R` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `a + r % basis 1:real^2` o check (fun th ->
      is_forall(concl th) && can (find_term (fun u -> u = `sphere(a:real^2,r)`)) (concl th))) THEN
    REWRITE_TAC[IN_SPHERE; IN_CBALL; NORM_ARITH `dist(a:real^2,a + y) = norm y`] THEN
    SIMP_TAC[NORM_MUL; NORM_BASIS; DIMINDEX_2; ARITH] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < r ==> abs r * &1 = r`] THEN
    MP_TAC(ISPECL [`c:real^K`; `(h:real^2->real^K)(a + r % basis 1)`] DIST_POS_LE) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `e = (h:real^2->real^K) x - c` THEN
  MP_TAC(ISPECL [`a:real^2`; `r:real`; `\y:real^2. e dot (h:real^2->real^K) y`;
                 `e dot c + norm(e:real^K) * R`] WANL_MAXP_SUB) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_LIFT_DOT2 THEN ASM_REWRITE_TAC[CONTINUOUS_ON_CONST];
      SUBGOAL_THEN `(\y:real^2. lift(e dot (h:real^2->real^K) y)) =
                    (\v. lift(e dot v)) o h` SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_LINEAR_O THEN ASM_REWRITE_TAC[OPEN_BALL] THEN
      REWRITE_TAC[linear; DOT_RADD; DOT_RMUL; LIFT_ADD; LIFT_CMUL];
      X_GEN_TAC `y:real^2` THEN DISCH_TAC THEN
      MATCH_MP_TAC(REAL_ARITH `x = &0 ==> &0 <= x`) THEN
      MATCH_MP_TAC WANL_LLAP_DOT_HARMONIC THEN EXISTS_TAC `ball(a:real^2,r)` THEN
      ASM_SIMP_TAC[OPEN_BALL];
      X_GEN_TAC `y:real^2` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `y:real^2` o check (fun th ->
        is_forall(concl th) && can (find_term (fun u -> u = `sphere(a:real^2,r)`)) (concl th))) THEN
      ASM_REWRITE_TAC[IN_CBALL; dist] THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`e:real^K`; `(h:real^2->real^K) y - c`] NORM_CAUCHY_SCHWARZ) THEN
      REWRITE_TAC[DOT_RSUB] THEN
      SUBGOAL_THEN `norm(e:real^K) * norm((h:real^2->real^K) y - c) <= norm e * R` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
        ONCE_REWRITE_TAC[NORM_SUB] THEN ASM_REWRITE_TAC[];
        REAL_ARITH_TAC]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `x:real^2`) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[IN_CBALL; dist] THEN ONCE_REWRITE_TAC[NORM_SUB] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `e dot (h:real^2->real^K) x = e dot c + norm(e:real^K) pow 2` SUBST1_TAC THENL
   [EXPAND_TAC "e" THEN REWRITE_TAC[NORM_POW_2] THEN
    REWRITE_TAC[DOT_LSUB; DOT_RSUB; DOT_SYM] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[REAL_LE_LADD; REAL_POW_2] THEN DISCH_TAC THEN
  ASM_CASES_TAC `norm(e:real^K) = &0` THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < norm(e:real^K)` ASSUME_TAC THENL
   [MP_TAC(ISPEC `e:real^K` NORM_POS_LE) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `norm(e:real^K) * norm e <= norm e * R` THEN
  ASM_SIMP_TAC[REAL_LE_LMUL_EQ]);;

let WANL_CONT_CBALL_INTEGRABLE = prove
 (`!(f:real^N->real^K) a r.
        f continuous_on cball(a,r)
        ==> f absolutely_integrable_on ball(a,r) /\ f integrable_on ball(a,r)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN
  REWRITE_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE] THEN
  MP_TAC(ISPECL [`f:real^N->real^K`; `cball(a:real^N,r)`] COMPACT_CONTINUOUS_IMAGE) THEN
  ASM_REWRITE_TAC[COMPACT_CBALL] THEN
  DISCH_THEN(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
  REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC WANL_CONTINUOUS_BOUNDED_ABSOLUTELY_INTEGRABLE THEN
  EXISTS_TAC `B:real` THEN REWRITE_TAC[MEASURABLE_BALL] THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `cball(a:real^N,r)` THEN
    ASM_REWRITE_TAC[BALL_SUBSET_CBALL];
    ASM_MESON_TAC[SUBSET; BALL_SUBSET_CBALL]]);;

(* Scalar circle means of harmonic functions on open sets.                   *)

let WANL_HARMONIC_SETUP = prove
 (`!(s:real^2->bool) (h:real^2->real) a r.
        open s /\ &0 < r /\ cball(a,r) SUBSET s /\ smooth_map_on s (\x. lift(h x))
        ==> (\x. lift(h x)) continuous_on cball(a,r) /\
            smooth_map_on (ball(a,r)) (\x. lift(h x))`,
  REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `s:real^2->bool` THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON];
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `s:real^2->bool` THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[SUBSET_TRANS; BALL_SUBSET_CBALL]]);;

let WANL_CIRCLE_MEAN_SCALAR = prove
 (`!(s:real^2->bool) (h:real^2->real) a r.
        open s /\ &0 < r /\ cball(a,r) SUBSET s /\ smooth_map_on s (\x. lift(h x)) /\
        (!x. x IN s ==> llap (\y:real^2. mat 1) h x = &0)
        ==> h a = inv(&2 * pi) *
                  drop(integral (interval[vec 0,lift(&2 * pi)])
                         (\t. lift(h(wan_circ a r (drop t)))))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^2->bool`; `h:real^2->real`; `a:real^2`; `r:real`]
         WANL_HARMONIC_SETUP) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`a:real^2`; `r:real`; `\x:real^2. lift(h x)`] WANL_CIRCLE_MEAN) THEN
  ASM_REWRITE_TAC[DIMINDEX_1; GSYM drop; LIFT_DROP; ETA_AX] THEN
  ANTS_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `j = 1` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[GSYM drop; LIFT_DROP; ETA_AX] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_MESON_TAC[SUBSET; BALL_SUBSET_CBALL];
    DISCH_THEN(MP_TAC o AP_TERM `drop`) THEN REWRITE_TAC[LIFT_DROP; DROP_CMUL]]);;

(* Disc sub-means from circle sub-means at all smaller radii.                *)

let WANL_DISC_FROM_CIRCLE = prove
 (`!(h:real^2->real) a r.
        &0 < r /\ (\x. lift(h x)) continuous_on cball(a,r) /\
        (!rho. &0 < rho /\ rho < r
               ==> h a <= inv(&2 * pi) *
                          drop(integral (interval[vec 0,lift(&2 * pi)])
                                 (\t. lift(h(wan_circ a rho (drop t))))))
        ==> h a <= inv(pi * r pow 2) * drop(integral (ball(a,r)) (\x. lift(h x)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &2 * pi /\ &0 < pi * r pow 2` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LT_MUL THEN
    ASM_SIMP_TAC[PI_POS; REAL_POW_LT] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`h:real^2->real`; `a:real^2`; `r:real`] WANL_DISC_SUBMEAN) THEN
  REWRITE_TAC[o_DEF] THEN ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [X_GEN_TAC `rho:real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `rho:real`) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[WANL_WAN_CIRC; COMPLEX_CMUL] THEN
    ABBREV_TAC `Ir = drop(integral (interval[vec 0,lift(&2 * pi)])
                       (\t. lift((h:real^2->real)(a + Cx rho * cexp(ii * Cx(drop t))))))` THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `(&2 * pi) * (h:real^2->real) a <= (&2 * pi) * (inv(&2 * pi) * Ir)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(&2 * pi) * inv(&2 * pi) * Ir = Ir` (fun th -> REWRITE_TAC[th]) THENL
     [UNDISCH_TAC `&0 < &2 * pi` THEN CONV_TAC REAL_FIELD; REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_SIMP_TAC[AREA_BALL; REAL_LT_IMP_LE] THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN ASM_SIMP_TAC[GSYM real_div; REAL_LE_RDIV_EQ]);;

let WAN_SUBMEAN_2D = prove
 (`WAN_SUBMEAN_2D_STATEMENT`,
  REWRITE_TAC[WAN_SUBMEAN_2D_STATEMENT] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!rho. &0 < rho /\ rho <= r
          ==> (h:real^2->real) a <=
              inv(&2 * pi) * drop(integral (interval[vec 0,lift(&2 * pi)])
                                    (\t. lift(h(wan_circ a rho (drop t)))))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`s:real^2->bool`; `h:real^2->real`; `a:real^2`; `rho:real`]
           WANL_HARMONIC_SETUP) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `cball(a:real^2,r)` THEN ASM_SIMP_TAC[SUBSET_CBALL];
      STRIP_TAC] THEN
    MATCH_MP_TAC WANL_CIRCLE_SUBMEAN THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `(x:real^2) IN ball(a,rho)` THEN UNDISCH_TAC `cball(a:real^2,r) SUBSET s` THEN
    UNDISCH_TAC `rho <= r` THEN REWRITE_TAC[SUBSET; IN_BALL; IN_CBALL] THEN
    MESON_TAC[REAL_LT_IMP_LE; REAL_LE_TRANS];
    ALL_TAC] THEN
  CONJ_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC WANL_DISC_FROM_CIRCLE THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`s:real^2->bool`; `h:real^2->real`; `a:real^2`; `r:real`]
           WANL_HARMONIC_SETUP) THEN ASM_SIMP_TAC[];
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC]);;

let WAN_MEAN_VALUE_2D = prove
 (`WAN_MEAN_VALUE_2D_STATEMENT`,
  REWRITE_TAC[WAN_MEAN_VALUE_2D_STATEMENT] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `smooth_map_on s (\x. lift(--(h:real^2->real) x)) /\
    (!x. x IN s ==> llap (\y:real^2. mat 1) (\x. --(h:real^2->real) x) x = &0)`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[LIFT_NEG; SMOOTH_MAP_ON_NEG_OPEN] THEN REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`s:real^2->bool`; `h:real^2->real`; `h:real^2->real`;
                   `--(&1)`; `&0`; `x:real^2`] WANL_LLAP_LINEAR) THEN
    ASM_SIMP_TAC[REAL_ARITH `--(&1) * a + &0 * b = --a`] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!(k:real^2->real) rho.
        smooth_map_on s (\x. lift(k x)) /\
        (!x. x IN s ==> llap (\y:real^2. mat 1) k x = &0) /\
        &0 < rho /\ rho <= r
        ==> k a = inv(&2 * pi) * drop(integral (interval[vec 0,lift(&2 * pi)])
                                       (\t. lift(k(wan_circ a rho (drop t)))))`
  (LABEL_TAC "cmk") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC WANL_CIRCLE_MEAN_SCALAR THEN
    EXISTS_TAC `s:real^2->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `cball(a:real^2,r)` THEN
    ASM_SIMP_TAC[SUBSET_CBALL];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [USE_THEN "cmk" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^2->bool`; `h:real^2->real`; `a:real^2`; `r:real`]
         WANL_HARMONIC_SETUP) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`h:real^2->real`; `a:real^2`; `r:real`] WANL_DISC_FROM_CIRCLE) THEN
  MP_TAC(ISPECL [`\x:real^2. --(h:real^2->real) x`; `a:real^2`; `r:real`]
         WANL_DISC_FROM_CIRCLE) THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN `(\x:real^2. lift(--(h:real^2->real) x)) continuous_on cball(a,r)`
  ASSUME_TAC THENL
   [REWRITE_TAC[LIFT_NEG] THEN MATCH_MP_TAC CONTINUOUS_ON_NEG THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN
    USE_THEN "cmk" (MP_TAC o SPECL [`\x:real^2. --(h:real^2->real) x`; `rho:real`]) THEN
    BETA_TAC THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[LIFT_NEG] THEN
  MP_TAC(ISPECL [`\x:real^2. lift(h x)`; `a:real^2`; `r:real`] WANL_CONT_CBALL_INTEGRABLE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`\x:real^2. lift(h x)`; `ball(a:real^2,r)`] INTEGRAL_NEG) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[DROP_NEG] THEN
  DISCH_TAC THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN USE_THEN "cmk" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC]);;

