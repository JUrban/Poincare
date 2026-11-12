(* ========================================================================= *)
(* Evolution equations under a local Ricci flow of matrix fields on          *)
(* (a,b) x U (MT Sec 3.4): scalar curvature (LSCALAR_EVOLUTION), volume      *)
(* density (LDENSITY_EVOLUTION), Christoffel symbols                         *)
(* (LCHRISTOFFEL_EVOLUTION); rescaling and pullback of flows                 *)
(* (LRICCI_FLOW_RESCALE, LRICCI_FLOW_PULLBACK).  Builds on pc_lrg,           *)
(* pc_lrg_tensor, pc_lrg_lap and pc_lrg_scale.                               *)
(* ========================================================================= *)

needs "src/pc_lrg_lap.ml";;
needs "src/pc_lrg_scale.ml";;

prioritize_real();;
type_invention_error := true;;

(* Definitions: local Ricci flows (MT Sec 3.4; Chow-Knopf).                  *)

(* A Ricci flow of matrix fields on (a,b) x U. *)

let lricci_flow = new_definition
 `lricci_flow (U:real^N->bool) (a:real) (b:real) (G:real->real^N->real^N^N) <=>
    open U /\ a < b /\
    (!t. a < t /\ t < b ==> metric_field U (G t)) /\
    smooth_map_on (interval(lift a,lift b) PCROSS U)
      (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
           (G (drop(fstcart z)) (sndcart z))) /\
    (!t y i j. a < t /\ t < b /\ y IN U /\
               1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
               ==> ((\s. G s y$i$j) has_real_derivative
                    (--(&2) * lricci (G t) y (basis i) (basis j))) (atreal t))`;;

(* The Ricci tensor as a (0,2)-tensor field. *)

let lric2 = new_definition
 `lric2 (G:real^N->real^N^N) y (u:num->real^N) = lricci G y (u 1) (u 2)`;;




(* ========================================================================= *)
(* Basic facts about local Ricci flows: the space-time domain, the time      *)
(* derivative of the metric as a vector derivative; rescaling and pullback   *)
(* of flows (for LRICCI_FLOW_RESCALE and LRICCI_FLOW_PULLBACK).              *)
(* ========================================================================= *)

let LRG_FLOW_BASIC = prove
 (`!U a b (G:real->real^N->real^N^N).
        lricci_flow U a b G
        ==> open U /\ a < b /\
            open(interval(lift a,lift b) PCROSS U) /\
            (!t x. pastecart (lift t) x IN interval(lift a,lift b) PCROSS U <=>
                   a < t /\ t < b /\ x IN U) /\
            (!t. a < t /\ t < b ==> metric_field U (G t)) /\
            smooth_map_on (interval(lift a,lift b) PCROSS U)
              (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                   (G (drop(fstcart z)) (sndcart z)))`,
  REWRITE_TAC[lricci_flow] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; PASTECART_IN_PCROSS; IN_INTERVAL_1;
               LIFT_DROP; CONJ_ASSOC]);;

let LRG_VECTORIZE_INDEX = prove
 (`!k. 1 <= k /\ k <= dimindex(:N) * dimindex(:N)
       ==> 1 <= 1 + (k - 1) DIV dimindex(:N) /\
           1 + (k - 1) DIV dimindex(:N) <= dimindex(:N) /\
           1 <= 1 + (k - 1) MOD dimindex(:N) /\
           1 + (k - 1) MOD dimindex(:N) <= dimindex(:N)`,
  GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[ARITH_RULE `1 <= 1 + x`; ARITH_RULE `1 + x <= n <=> x < n`] THEN
  SIMP_TAC[RDIV_LT_EQ; MOD_LT_EQ; DIMINDEX_GE_1; LE_1] THEN ASM_ARITH_TAC);;

let LRG_FLOW_VDERIV = prove
 (`!U a b (G:real->real^N->real^N^N) t x.
        lricci_flow U a b G /\ a < t /\ t < b /\ x IN U
        ==> ((\s. vectorize(G (drop s) x)) has_vector_derivative
             vectorize((lambda i j. --(&2) * lricci (G t) x (basis i) (basis j))
                       :real^N^N)) (at (lift t))`,
  REWRITE_TAC[lricci_flow] THEN REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC I [HAS_VECTOR_DERIVATIVE_COMPONENTWISE_AT] THEN
  REWRITE_TAC[DIMINDEX_FINITE_PROD] THEN
  X_GEN_TAC `k:num` THEN STRIP_TAC THEN
  MP_TAC(ISPEC `k:num` LRG_VECTORIZE_INDEX) THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[VECTORIZE_COMPONENT; DIMINDEX_FINITE_PROD] THEN
  SPEC_TAC(`1 + (k - 1) MOD dimindex(:N)`, `j:num`) THEN
  SPEC_TAC(`1 + (k - 1) DIV dimindex(:N)`, `i:num`) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_SIMP_TAC[LAMBDA_BETA] THEN
  SUBGOAL_THEN
   `(\s. lift((G:real->real^N->real^N^N) (drop s) x$i$j)) =
    lift o (\s. G s x$i$j) o drop`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  REWRITE_TAC[GSYM HAS_REAL_VECTOR_DERIVATIVE_AT] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let LRG_SMOOTH_LINEAR = prove
 (`!s (f:real^M->real^N). open s /\ linear f ==> smooth_map_on s f`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(f:real^M->real^N) = f o (\x. x)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_LINEAR_O THEN ASM_REWRITE_TAC[SMOOTH_MAP_ON_ID]);;

let LRG_METRIC_FIELD_SCALE = prove
 (`!U (G:real^N->real^N^N) c.
        metric_field U G /\ &0 < c ==> metric_field U (\z. c %% G z)`,
  REWRITE_TAC[metric_field] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [SUBGOAL_THEN
     `(vectorize:real^N^N->real^(N,N)finite_prod) o
      (\z. c %% (G:real^N->real^N^N) z) =
      (\z. c % (vectorize o G) z)`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM; VECTORIZE_CMUL]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_CMUL_OPEN THEN ASM_REWRITE_TAC[ETA_AX];
    X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:real^N`) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN
    ASM_REWRITE_TAC[TRANSP_MATRIX_CMUL; MATRIX_VECTOR_LMUL; DOT_RMUL] THEN
    ASM_SIMP_TAC[REAL_LT_MUL]]);;

let LRG_HAS_REAL_DERIVATIVE_RESCALE = prove
 (`!f f' q t.
        &0 < q /\ (f has_real_derivative f') (atreal (t / q))
        ==> ((\s. q * f (s / q)) has_real_derivative f') (atreal t)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `((\s:real. s / q) has_real_derivative inv q) (atreal t)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\s:real. s`; `&1`; `inv q`; `t:real`]
           HAS_REAL_DERIVATIVE_RMUL_ATREAL) THEN
    REWRITE_TAC[HAS_REAL_DERIVATIVE_ID; real_div; REAL_MUL_LID];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\s:real. s / q`; `f:real->real`; `inv q`; `f':real`;
                 `t:real`] REAL_DIFF_CHAIN_ATREAL) THEN
  ASM_REWRITE_TAC[o_DEF] THEN
  DISCH_THEN(MP_TAC o SPEC `q:real` o MATCH_MP HAS_REAL_DERIVATIVE_LMUL_ATREAL) THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN `q * f' * inv q = f'` (fun th -> REWRITE_TAC[th]) THEN
  UNDISCH_TAC `&0 < q` THEN CONV_TAC REAL_FIELD);;


(* ========================================================================= *)
(* LRICCI_FLOW_RESCALE and LRICCI_FLOW_PULLBACK.                             *)
(* ========================================================================= *)

let LRG_CONGRUENCE_ENTRY_MATRIX = prove
 (`!(J:real^N^N) (M:real^N^N) i j.
        1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
        ==> (transp J ** M ** J)$i$j =
            sum(1..dimindex(:N))
             (\p. sum(1..dimindex(:N)) (\q. J$p$i * J$q$j * M$p$q))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`J:real^N^N`; `\p q. (M:real^N^N)$p$q`; `i:num`; `j:num`]
         LRG_CONGRUENCE_ENTRY) THEN
  ASM_REWRITE_TAC[LAMBDA_ETA]);;

let LRICCI_FLOW_RESCALE = prove
 (`!U a b (G:real->real^N->real^N^N) q.
        lricci_flow U a b G /\ &0 < q
        ==> lricci_flow U (q * a) (q * b) (\t y. q %% G (t / q) y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(REWRITE_RULE[lricci_flow]
    (ASSUME `lricci_flow (U:real^N->bool) a b (G:real->real^N->real^N^N)`)) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `!t. q * a < t /\ t < q * b ==> a < t / q /\ t / q < b`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_LT_RDIV_EQ] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[lricci_flow] THEN ASM_SIMP_TAC[REAL_LT_LMUL] THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    MATCH_MP_TAC LRG_METRIC_FIELD_SCALE THEN
    REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    SUBGOAL_THEN
     `(\z. vectorize(q %% (G:real->real^N->real^N^N) (drop(fstcart z) / q)
                                                      (sndcart z))) =
      (\z. q % ((\z. vectorize(G (drop(fstcart z)) (sndcart z))) o
                (\z. pastecart (inv q % fstcart z) (sndcart z)
                     :real^(1,N)finite_sum)) z)`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM; VECTORIZE_CMUL; FSTCART_PASTECART;
                  SNDCART_PASTECART; DROP_CMUL; real_div; REAL_MUL_AC];
      ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_CMUL_OPEN THEN
    ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; ETA_AX] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
    EXISTS_TAC `interval(lift a,lift b) PCROSS (U:real^N->bool)` THEN
    ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL] THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_PCROSS;
                  FSTCART_PASTECART; SNDCART_PASTECART; PASTECART_IN_PCROSS;
                  IN_INTERVAL_1; DROP_CMUL; LIFT_DROP] THEN
      MAP_EVERY X_GEN_TAC [`x:real^1`; `y:real^N`] THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `inv q * drop x = drop x / q` SUBST1_TAC THENL
       [REWRITE_TAC[real_div; REAL_MUL_AC]; ALL_TAC] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC LRG_SMOOTH_LINEAR THEN
      SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; ASSUME `open(U:real^N->bool)`] THEN
      MATCH_MP_TAC LINEAR_PASTECART THEN
      SIMP_TAC[LINEAR_COMPOSE_CMUL; LINEAR_FSTCART; LINEAR_SNDCART]];
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `a < t / q /\ t / q < b` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `metric_field U ((G:real->real^N->real^N^N) (t / q))`
    ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `(G:real->real^N->real^N^N) (t / q)`;
                   `q:real`; `y:real^N`; `basis i:real^N`; `basis j:real^N`]
           LRICCI_SCALE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[MATRIX_CMUL_COMPONENT] THEN
    MP_TAC(ISPECL [`\s. (G:real->real^N->real^N^N) s y$i$j`;
                   `--(&2) * lricci ((G:real->real^N->real^N^N) (t / q)) y
                                    (basis i) (basis j)`;
                   `q:real`; `t:real`] LRG_HAS_REAL_DERIVATIVE_RESCALE) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

let LRICCI_FLOW_PULLBACK = prove
 (`!U U' a b (h:real^N->real^N) h' G.
        lricci_flow U a b G /\ diffeomorphism_on U' U h h'
        ==> lricci_flow U' a b (\t. mpullback h (G t))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(REWRITE_RULE[lricci_flow]
    (ASSUME `lricci_flow (U:real^N->bool) a b (G:real->real^N->real^N^N)`)) THEN
  STRIP_TAC THEN
  MP_TAC(REWRITE_RULE[diffeomorphism_on]
    (ASSUME `diffeomorphism_on (U':real^N->bool) U (h:real^N->real^N) h'`)) THEN
  STRIP_TAC THEN
  REWRITE_TAC[lricci_flow] THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN MATCH_MP_TAC METRIC_FIELD_PULLBACK THEN
    MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `h':real^N->real^N`] THEN
    ASM_SIMP_TAC[];
    SUBGOAL_THEN
     `(\z. vectorize(mpullback (h:real^N->real^N)
                      ((G:real->real^N->real^N^N) (drop(fstcart z))) (sndcart z))) =
      (vectorize:real^N^N->real^(N,N)finite_prod) o
      (\z. transp(matrix(frechet_derivative h (at (sndcart z)))) **
           G (drop(fstcart z)) (h(sndcart z)) **
           matrix(frechet_derivative h (at (sndcart z))))`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM; mpullback]; ALL_TAC] THEN
    SUBGOAL_THEN `open(interval(lift a,lift b) PCROSS (U':real^N->bool))`
    ASSUME_TAC THENL [ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL]; ALL_TAC] THEN
    SUBGOAL_THEN
     `smooth_map_on (interval(lift a,lift b) PCROSS (U':real^N->bool))
        ((vectorize:real^N^N->real^(N,N)finite_prod) o
         (\z. matrix(frechet_derivative (h:real^N->real^N) (at (sndcart z)))))`
    ASSUME_TAC THENL
     [SUBGOAL_THEN
       `(vectorize:real^N^N->real^(N,N)finite_prod) o
        (\z. matrix(frechet_derivative (h:real^N->real^N) (at (sndcart z)))) =
        (vectorize o (\x. matrix(frechet_derivative h (at x)))) o
        (sndcart:real^(1,N)finite_sum->real^N)`
      SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
      EXISTS_TAC `U':real^N->bool` THEN
      ASM_SIMP_TAC[LRG_SMOOTH_JACOBIAN; LRG_SMOOTH_LINEAR; LINEAR_SNDCART] THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_PCROSS; SNDCART_PASTECART] THEN
      SIMP_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC LRG_SMOOTH_MATMUL THEN ASM_SIMP_TAC[LRG_SMOOTH_TRANSP] THEN
    MATCH_MP_TAC LRG_SMOOTH_MATMUL THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `(vectorize:real^N^N->real^(N,N)finite_prod) o
      (\z. (G:real->real^N->real^N^N) (drop(fstcart z))
                                      ((h:real^N->real^N) (sndcart z))) =
      (\z. vectorize(G (drop(fstcart z)) (sndcart z))) o
      (\z:real^(1,N)finite_sum. pastecart (fstcart z) (h(sndcart z)))`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM; FSTCART_PASTECART; SNDCART_PASTECART];
      ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
    EXISTS_TAC `interval(lift a,lift b) PCROSS (U:real^N->bool)` THEN
    ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL] THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_PCROSS; FSTCART_PASTECART;
                  SNDCART_PASTECART; PASTECART_IN_PCROSS] THEN
      ASM SET_TAC[];
      MATCH_MP_TAC SMOOTH_MAP_ON_PASTECART_OPEN THEN
      ASM_SIMP_TAC[LRG_SMOOTH_LINEAR; LINEAR_FSTCART] THEN
      SUBGOAL_THEN
       `(\z:real^(1,N)finite_sum. (h:real^N->real^N) (sndcart z)) = h o sndcart`
      SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
      EXISTS_TAC `U':real^N->bool` THEN
      ASM_SIMP_TAC[LRG_SMOOTH_LINEAR; LINEAR_SNDCART] THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_PCROSS; SNDCART_PASTECART] THEN
      SIMP_TAC[]];
    MAP_EVERY X_GEN_TAC [`t:real`; `y:real^N`; `i:num`; `j:num`] THEN
    STRIP_TAC THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `U':real^N->bool`; `h:real^N->real^N`;
                   `h':real^N->real^N`; `y:real^N`] LRG_DIFFEO_DERIV) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `metric_field U ((G:real->real^N->real^N^N) t)` ASSUME_TAC
    THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `U':real^N->bool`; `h:real^N->real^N`;
                   `h':real^N->real^N`; `(G:real->real^N->real^N^N) t`;
                   `y:real^N`; `basis i:real^N`; `basis j:real^N`]
           LRICCI_PULLBACK) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `(G:real->real^N->real^N^N) t`;
                   `(h:real^N->real^N) y`;
                   `frechet_derivative (h:real^N->real^N) (at y) (basis i)`;
                   `frechet_derivative (h:real^N->real^N) (at y) (basis j)`]
           LRG_LRICCI_EXPAND) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    ASM_SIMP_TAC[mpullback; LRG_CONGRUENCE_ENTRY_MATRIX] THEN
    SUBGOAL_THEN
     `--(&2) *
      sum(1..dimindex(:N))
       (\p. frechet_derivative (h:real^N->real^N) (at y) (basis i)$p *
            sum(1..dimindex(:N))
             (\q. frechet_derivative h (at y) (basis j)$q *
                  lricci ((G:real->real^N->real^N^N) t) (h y)
                         (basis p) (basis q))) =
      sum(1..dimindex(:N))
       (\p. sum(1..dimindex(:N))
         (\q. matrix(frechet_derivative h (at y))$p$i *
              matrix(frechet_derivative h (at y))$q$j *
              (--(&2) * lricci (G t) (h y) (basis p) (basis q))))`
    SUBST1_TAC THENL
     [ASM_SIMP_TAC[MATRIX_COMPONENT] THEN REWRITE_TAC[GSYM SUM_LMUL] THEN
      MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `p:num` THEN STRIP_TAC THEN
      BETA_TAC THEN REWRITE_TAC[GSYM SUM_LMUL] THEN
      MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `q:num` THEN STRIP_TAC THEN
      BETA_TAC THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUM THEN
    REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN X_GEN_TAC `p:num` THEN
    STRIP_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUM THEN
    REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN X_GEN_TAC `q:num` THEN
    STRIP_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_LMUL_ATREAL THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_LMUL_ATREAL THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;


(* ========================================================================= *)
(* The derivative of the determinant (Jacobi's formula) and                  *)
(* LDENSITY_EVOLUTION.                                                       *)
(* ========================================================================= *)

let LRG_DET_ADD_ENTRY = prove
 (`!(M:real^N^N) i j c.
        1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
        ==> det(M + c %% (lambda p q. if p = i /\ q = j then &1 else &0)) =
            det M + c * cofactor M$i$j`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`M + c %% (lambda p q. if p = i /\ q = j then &1 else &0):real^N^N`;
    `i:num`] DET_COFACTOR_EXPANSION) THEN
  MP_TAC(ISPECL [`M:real^N^N`; `i:num`] DET_COFACTOR_EXPANSION) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN
   `!l. 1 <= l /\ l <= dimindex(:N)
        ==> cofactor(M + c %% (lambda p q. if p = i /\ q = j then &1 else &0)
                     :real^N^N)$i$l =
            cofactor M$i$l`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN ASM_SIMP_TAC[COFACTOR_ROW; LAMBDA_BETA] THEN
    AP_TERM_TAC THEN
    SIMP_TAC[CART_EQ; LAMBDA_BETA; MATRIX_ADD_COMPONENT;
             MATRIX_CMUL_COMPONENT] THEN
    REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `sum(1..dimindex(:N))
     (\l. M$i$l * cofactor M$i$l +
          c * (if l = j then cofactor (M:real^N^N)$i$j else &0))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `l:num` THEN STRIP_TAC THEN
    BETA_TAC THEN
    ASM_SIMP_TAC[MATRIX_ADD_COMPONENT; MATRIX_CMUL_COMPONENT; LAMBDA_BETA] THEN
    ASM_CASES_TAC `l:num = j` THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    REWRITE_TAC[SUM_ADD_NUMSEG; SUM_LMUL; SUM_DELTA; IN_NUMSEG] THEN
    ASM_REWRITE_TAC[]]);;

let LRG_DIVMOD_EQ = prove
 (`!m k n. ~(n = 0) /\ 1 <= m /\ 1 <= k
           ==> ((m - 1) DIV n = (k - 1) DIV n /\ (m - 1) MOD n = (k - 1) MOD n <=>
                m = k)`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`m - 1`; `n:num`] DIVISION) THEN
  MP_TAC(SPECL [`k - 1`; `n:num`] DIVISION) THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let LRG_VECTORIZE_BASIS = prove
 (`!k. 1 <= k /\ k <= dimindex(:N) * dimindex(:N)
       ==> (basis k:real^(N,N)finite_prod) =
           vectorize((lambda p q. if p = 1 + (k - 1) DIV dimindex(:N) /\
                                     q = 1 + (k - 1) MOD dimindex(:N)
                                  then &1 else &0):real^N^N)`,
  REPEAT STRIP_TAC THEN
  SIMP_TAC[CART_EQ; DIMINDEX_FINITE_PROD; BASIS_COMPONENT;
           VECTORIZE_COMPONENT] THEN
  X_GEN_TAC `m:num` THEN STRIP_TAC THEN
  MP_TAC(ISPEC `m:num` LRG_VECTORIZE_INDEX) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN ASM_SIMP_TAC[LAMBDA_BETA] THEN
  REWRITE_TAC[EQ_ADD_LCANCEL] THEN
  MP_TAC(SPECL [`m:num`; `k:num`; `dimindex(:N)`] LRG_DIVMOD_EQ) THEN
  ASM_SIMP_TAC[DIMINDEX_GE_1; LE_1]);;

let LRG_DET_DIFFERENTIABLE = prove
 (`!x:real^(N,N)finite_prod.
        (\x. lift(det(matrify x:real^N^N))) differentiable at x`,
  GEN_TAC THEN MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_IMP_DIFFERENTIABLE_AT THEN
  EXISTS_TAC `(:real^(N,N)finite_prod)` THEN REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN
  GEN_TAC THEN MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_DET_OPEN THEN
  REWRITE_TAC[OPEN_UNIV] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_LINEAR_OPEN THEN
  REWRITE_TAC[OPEN_UNIV; LRG_LINEAR_MATRIFY_ENTRY]);;

let LRG_DET_DERIV_ENTRY = prove
 (`!(x:real^(N,N)finite_prod) i j.
        1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
        ==> frechet_derivative (\x. lift(det(matrify x:real^N^N))) (at x)
              (vectorize((lambda p q. if p = i /\ q = j then &1 else &0)
                         :real^N^N)) =
            lift(cofactor(matrify x:real^N^N)$i$j)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `x:real^(N,N)finite_prod` LRG_DET_DIFFERENTIABLE) THEN
  REWRITE_TAC[FRECHET_DERIVATIVE_WORKS] THEN DISCH_TAC THEN
  MP_TAC(ISPECL
   [`x:real^(N,N)finite_prod`;
    `vectorize((lambda p q. if p = i /\ q = j then &1 else &0):real^N^N)`;
    `vec 0:real^1`] HAS_DERIVATIVE_LINE_PARAM) THEN DISCH_TAC THEN
  MP_TAC(ISPECL
   [`\c:real^1. x + drop c %
       vectorize((lambda p q. if p = i /\ q = j then &1 else &0):real^N^N)`;
    `\x:real^(N,N)finite_prod. lift(det(matrify x:real^N^N))`;
    `\d:real^1. drop d %
       vectorize((lambda p q. if p = i /\ q = j then &1 else &0):real^N^N)`;
    `frechet_derivative (\x:real^(N,N)finite_prod. lift(det(matrify x:real^N^N)))
                        (at x)`;
    `vec 0:real^1`] DIFF_CHAIN_AT) THEN
  ASM_REWRITE_TAC[DROP_VEC; VECTOR_MUL_LZERO; VECTOR_ADD_RID] THEN
  SUBGOAL_THEN
   `(\x:real^(N,N)finite_prod. lift(det(matrify x:real^N^N))) o
    (\c:real^1. x + drop c %
       vectorize((lambda p q. if p = i /\ q = j then &1 else &0):real^N^N)) =
    (\c. lift(det(matrify x:real^N^N)) +
         drop c % lift(cofactor(matrify x:real^N^N)$i$j))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; MATRIFY_ADD; MATRIFY_CMUL;
                MATRIFY_VECTORIZE] THEN
    X_GEN_TAC `c:real^1` THEN ASM_SIMP_TAC[LRG_DET_ADD_ENTRY] THEN
    REWRITE_TAC[LIFT_ADD; LIFT_CMUL];
    ALL_TAC] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`lift(det(matrify x:real^N^N))`;
                 `lift(cofactor(matrify x:real^N^N)$i$j)`; `vec 0:real^1`]
         HAS_DERIVATIVE_LINE_PARAM) THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `(frechet_derivative (\x:real^(N,N)finite_prod. lift(det(matrify x:real^N^N)))
                        (at x)) o
    (\d:real^1. drop d %
       vectorize((lambda p q. if p = i /\ q = j then &1 else &0):real^N^N)) =
    (\d. drop d % lift(cofactor(matrify x:real^N^N)$i$j))`
  MP_TAC THENL
   [MATCH_MP_TAC FRECHET_DERIVATIVE_UNIQUE_AT THEN
    EXISTS_TAC `\c:real^1. lift(det(matrify x:real^N^N)) +
                           drop c % lift(cofactor(matrify x:real^N^N)$i$j)` THEN
    EXISTS_TAC `vec 0:real^1` THEN ASM_REWRITE_TAC[];
    DISCH_THEN(MP_TAC o C AP_THM `lift(&1)`) THEN
    REWRITE_TAC[o_THM; LIFT_DROP; VECTOR_MUL_LID]]);;

let LRG_SUM_VECTORIZE_PRODUCT = prove
 (`!(A:real^N^N) (B:real^N^N).
        sum(1..dimindex(:N) * dimindex(:N))
           (\k. (vectorize A)$k * (vectorize B)$k) =
        sum(1..dimindex(:N)) (\i. sum(1..dimindex(:N)) (\j. A$i$j * B$i$j))`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`A:real^N^N`; `B:real^N^N`] DOT_VECTORIZE) THEN
  REWRITE_TAC[dot; DIMINDEX_FINITE_PROD; LRG_SUM_ENTRYWISE] THEN
  DISCH_THEN SUBST1_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM TRACE_TRANSP] THEN
  REWRITE_TAC[MATRIX_TRANSP_MUL; TRANSP_TRANSP] THEN
  MATCH_ACCEPT_TAC TRACE_MUL_SYM);;

let LRG_DET_DERIV = prove
 (`!(x:real^(N,N)finite_prod) (H:real^N^N).
        frechet_derivative (\x. lift(det(matrify x:real^N^N))) (at x)
                           (vectorize H) =
        lift(sum(1..dimindex(:N))
              (\i. sum(1..dimindex(:N))
                     (\j. H$i$j * cofactor(matrify x:real^N^N)$i$j)))`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN
   `linear(frechet_derivative
            (\x:real^(N,N)finite_prod. lift(det(matrify x:real^N^N))) (at x))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
    REWRITE_TAC[LRG_DET_DIFFERENTIABLE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!k. 1 <= k /\ k <= dimindex(:N) * dimindex(:N)
        ==> drop(frechet_derivative
                  (\x:real^(N,N)finite_prod. lift(det(matrify x:real^N^N)))
                  (at x) (basis k)) =
            (vectorize(cofactor(matrify x:real^N^N)))$k`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPEC `k:num` LRG_VECTORIZE_INDEX) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN
    ASM_SIMP_TAC[LRG_VECTORIZE_BASIS; LRG_DET_DERIV_ENTRY; VECTORIZE_COMPONENT;
                 DIMINDEX_FINITE_PROD; LIFT_DROP];
    ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM LIFT_DROP] THEN AP_TERM_TAC THEN
  MP_TAC(ISPECL
   [`frechet_derivative
      (\x:real^(N,N)finite_prod. lift(det(matrify x:real^N^N))) (at x)`;
    `vectorize(H:real^N^N)`] LRG_LINEAR_DROP_EXPAND) THEN
  ASM_REWRITE_TAC[DIMINDEX_FINITE_PROD] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `sum(1..dimindex(:N) * dimindex(:N))
      (\k. (vectorize(H:real^N^N))$k *
           (vectorize(cofactor(matrify x:real^N^N)))$k)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
    ASM_SIMP_TAC[];
    REWRITE_TAC[LRG_SUM_VECTORIZE_PRODUCT]]);;

let LRG_HAS_DERIVATIVE_DET_CURVE = prove
 (`!(c:real^1->real^N^N) (H:real^N^N) t0.
        ((\s. vectorize(c s)) has_vector_derivative vectorize H) (at t0)
        ==> ((\s. lift(det(c s))) has_vector_derivative
             lift(sum(1..dimindex(:N))
                   (\i. sum(1..dimindex(:N))
                          (\j. H$i$j * cofactor(c t0)$i$j)))) (at t0)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[has_vector_derivative] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `(\s. lift(det((c:real^1->real^N^N) s))) =
    (\x:real^(N,N)finite_prod. lift(det(matrify x:real^N^N))) o
    (\s. vectorize(c s))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM; MATRIFY_VECTORIZE]; ALL_TAC] THEN
  MP_TAC(ISPEC `vectorize((c:real^1->real^N^N) t0)` LRG_DET_DIFFERENTIABLE) THEN
  REWRITE_TAC[FRECHET_DERIVATIVE_WORKS] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `linear(frechet_derivative
      (\x:real^(N,N)finite_prod. lift(det(matrify x:real^N^N)))
      (at (vectorize((c:real^1->real^N^N) t0))))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
    REWRITE_TAC[LRG_DET_DIFFERENTIABLE];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\s. vectorize((c:real^1->real^N^N) s)`;
    `\x:real^(N,N)finite_prod. lift(det(matrify x:real^N^N))`;
    `\s:real^1. drop s % vectorize(H:real^N^N)`;
    `frechet_derivative
      (\x:real^(N,N)finite_prod. lift(det(matrify x:real^N^N)))
      (at (vectorize((c:real^1->real^N^N) t0)))`;
    `t0:real^1`] DIFF_CHAIN_AT) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(MESON[]
   `(f:real^1->real^1) = g
    ==> (h has_derivative f) (net:(real^1)net)
        ==> (h has_derivative g) net`) THEN
  REWRITE_TAC[FUN_EQ_THM; o_THM] THEN X_GEN_TAC `s:real^1` THEN
  ASM_SIMP_TAC[LINEAR_CMUL; LRG_DET_DERIV; MATRIFY_VECTORIZE]);;

let LDENSITY_EVOLUTION = prove
 (`!U a b (G:real->real^N->real^N^N) t y.
        lricci_flow U a b G /\ a < t /\ t < b /\ y IN U
        ==> ((\s. sqrt(det(G s y))) has_real_derivative
             (--(lscalar (G t) y) * sqrt(det(G t y)))) (atreal t)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `a:real`; `b:real`;
                 `G:real->real^N->real^N^N`] LRG_FLOW_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `metric_field U ((G:real->real^N->real^N^N) t)` ASSUME_TAC
  THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < det((G:real->real^N->real^N^N) t y)` ASSUME_TAC THENL
   [MATCH_MP_TAC DET_POSITIVE_DEFINITE THEN
    REWRITE_TAC[positive_definite; symmetric_matrix] THEN
    ASM_MESON_TAC[metric_field];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\s. det((G:real->real^N->real^N^N) s y)) has_real_derivative
     (--(&2) * lscalar (G t) y * det(G t y))) (atreal t)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`U:real^N->bool`; `a:real`; `b:real`;
                   `G:real->real^N->real^N^N`; `t:real`; `y:real^N`]
           LRG_FLOW_VDERIV) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o MATCH_MP LRG_HAS_DERIVATIVE_DET_CURVE) THEN
    REWRITE_TAC[LIFT_DROP; HAS_REAL_VECTOR_DERIVATIVE_AT] THEN
    MATCH_MP_TAC(MESON[]
     `(f:real^1->real^1) = g /\ (x:real^1) = y
      ==> (f has_vector_derivative x) (net:(real^1)net)
          ==> (g has_vector_derivative y) net`) THEN
    CONJ_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; AP_TERM_TAC] THEN
    ASM_SIMP_TAC[COFACTOR_MATRIX_INV; REAL_LT_IMP_NZ] THEN
    REWRITE_TAC[lscalar; MATRIX_CMUL_COMPONENT; TRANSP_COMPONENT] THEN
    REWRITE_TAC[GSYM SUM_LMUL; GSYM SUM_RMUL] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    BETA_TAC THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    BETA_TAC THEN ASM_SIMP_TAC[LAMBDA_BETA] THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `(G:real->real^N->real^N^N) t`;
                   `y:real^N`; `i:num`; `j:num`] LRG_MATRIX_INV_SYM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\s. det((G:real->real^N->real^N^N) s y)`; `sqrt`;
                 `--(&2) * lscalar ((G:real->real^N->real^N^N) t) y *
                  det(G t y)`;
                 `inv(&2 * sqrt(det((G:real->real^N->real^N^N) t y)))`;
                 `t:real`] REAL_DIFF_CHAIN_ATREAL) THEN
  ASM_SIMP_TAC[HAS_REAL_DERIVATIVE_SQRT; o_DEF] THEN
  MATCH_MP_TAC(MESON[]
   `(x:real) = y
    ==> (f has_real_derivative x) (net:(real)net)
        ==> (f has_real_derivative y) net`) THEN
  SUBGOAL_THEN
   `&0 < sqrt(det((G:real->real^N->real^N^N) t y)) /\
    sqrt(det(G t y)) pow 2 = det(G t y)`
  MP_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LT; SQRT_POW_2; REAL_LT_IMP_LE]; ALL_TAC] THEN
  SPEC_TAC(`sqrt(det((G:real->real^N->real^N^N) t y))`, `r:real`) THEN
  SPEC_TAC(`det((G:real->real^N->real^N^N) t y)`, `d:real`) THEN
  SPEC_TAC(`lscalar ((G:real->real^N->real^N^N) t) y`, `R:real`) THEN
  CONV_TAC REAL_FIELD);;


(* ========================================================================= *)
(* Space-time calculus on interval(lift a,lift b) PCROSS U: time curves and  *)
(* space slices of joint maps, interchange of the time derivative with a     *)
(* space derivative, the time derivative of the metric.                      *)
(* ========================================================================= *)

let LRG_HAS_DERIVATIVE_TIME_CURVE = prove
 (`!(f:real^(1,N)finite_sum->real^P) s0 x.
        f differentiable at (pastecart s0 x)
        ==> ((\s. f(pastecart s x)) has_derivative
             (\s'. frechet_derivative f (at (pastecart s0 x))
                                        (pastecart s' (vec 0)))) (at s0)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\s:real^1. pastecart s (x:real^N)`;
                 `f:real^(1,N)finite_sum->real^P`;
                 `\s':real^1. pastecart s' (vec 0:real^N)`;
                 `frechet_derivative (f:real^(1,N)finite_sum->real^P)
                                     (at (pastecart s0 x))`;
                 `s0:real^1`] DIFF_CHAIN_AT) THEN
  ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS; o_DEF] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  MATCH_MP_TAC HAS_DERIVATIVE_PASTECART THEN
  REWRITE_TAC[HAS_DERIVATIVE_ID; HAS_DERIVATIVE_CONST]);;

let LRG_HAS_DERIVATIVE_SPACE_SLICE = prove
 (`!(f:real^(1,N)finite_sum->real^P) s y.
        f differentiable at (pastecart s y)
        ==> ((\x. f(pastecart s x)) has_derivative
             (\w. frechet_derivative f (at (pastecart s y))
                                       (pastecart (vec 0) w))) (at y)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\x:real^N. pastecart (s:real^1) x`;
                 `f:real^(1,N)finite_sum->real^P`;
                 `\w:real^N. pastecart (vec 0:real^1) w`;
                 `frechet_derivative (f:real^(1,N)finite_sum->real^P)
                                     (at (pastecart s y))`;
                 `y:real^N`] DIFF_CHAIN_AT) THEN
  ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS; o_DEF] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  MATCH_MP_TAC HAS_DERIVATIVE_PASTECART THEN
  REWRITE_TAC[HAS_DERIVATIVE_ID; HAS_DERIVATIVE_CONST]);;

let LRG_SLICE_DERIV = prove
 (`!(f:real^(1,N)finite_sum->real^P) s y w.
        f differentiable at (pastecart s y)
        ==> frechet_derivative (\x. f(pastecart s x)) (at y) w =
            frechet_derivative f (at (pastecart s y)) (pastecart (vec 0) w)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP LRG_HAS_DERIVATIVE_SPACE_SLICE) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM(MATCH_MP FRECHET_DERIVATIVE_AT th)]));;

let LRG_TIME_SPACE_SWAP = prove
 (`!W (f:real^(1,N)finite_sum->real^P) t y w.
        open W /\ smooth_map_on W f /\ pastecart (lift t) y IN W
        ==> ((\s. frechet_derivative (\x. f(pastecart s x)) (at y) w)
             has_vector_derivative
             frechet_derivative
               (\x. frechet_derivative f (at (pastecart (lift t) x))
                                       (pastecart (lift(&1)) (vec 0)))
               (at y) w) (at (lift t))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open {s:real^1 | pastecart s (y:real^N) IN W}` ASSUME_TAC
  THENL
   [MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE_UNIV THEN ASM_REWRITE_TAC[] THEN
    GEN_TAC THEN MATCH_MP_TAC CONTINUOUS_PASTECART THEN
    REWRITE_TAC[CONTINUOUS_AT_ID; CONTINUOUS_CONST];
    ALL_TAC] THEN
  REWRITE_TAC[has_vector_derivative] THEN
  MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_WITHIN_OPEN THEN
  EXISTS_TAC
   `\s:real^1. frechet_derivative (f:real^(1,N)finite_sum->real^P)
                                  (at (pastecart s y)) (pastecart (vec 0) w)` THEN
  EXISTS_TAC `{s:real^1 | pastecart s (y:real^N) IN W}` THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN CONJ_TAC THENL
   [X_GEN_TAC `s:real^1` THEN DISCH_TAC THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC LRG_SLICE_DERIV THEN
    ASM_MESON_TAC[SMOOTH_MAP_ON_DIFFERENTIABLE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\z. frechet_derivative (f:real^(1,N)finite_sum->real^P) (at z)
                            (pastecart (vec 0) w))
    differentiable at (pastecart (lift t) y)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `W:real^(1,N)finite_sum->bool` THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_FRECHET_DERIVATIVE];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP LRG_HAS_DERIVATIVE_TIME_CURVE) THEN
  REWRITE_TAC[] THEN
  MATCH_MP_TAC(MESON[]
   `(f:real^1->real^P) = g
    ==> (h has_derivative f) (net:(real^1)net)
        ==> (h has_derivative g) net`) THEN
  REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `s:real^1` THEN
  SUBGOAL_THEN
   `pastecart s (vec 0:real^N) = drop s % pastecart (lift(&1)) (vec 0)`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM PASTECART_CMUL; VECTOR_MUL_RZERO; GSYM LIFT_CMUL;
                REAL_MUL_RID; LIFT_DROP];
    ALL_TAC] THEN
  ASM_SIMP_TAC[LINEAR_CMUL; LINEAR_FRECHET_DERIVATIVE] THEN AP_TERM_TAC THEN
  MP_TAC(ISPECL [`W:real^(1,N)finite_sum->bool`;
                 `f:real^(1,N)finite_sum->real^P`;
                 `pastecart (lift t) (y:real^N)`;
                 `pastecart (lift(&1)) (vec 0:real^N)`;
                 `pastecart (vec 0:real^1) (w:real^N)`]
         LRG_SECOND_DERIVATIVE_SYM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  CONV_TAC SYM_CONV THEN
  MP_TAC(ISPECL
   [`\z. frechet_derivative (f:real^(1,N)finite_sum->real^P) (at z)
                            (pastecart (lift(&1)) (vec 0:real^N))`;
    `lift t`; `y:real^N`; `w:real^N`] LRG_SLICE_DERIV) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
  EXISTS_TAC `W:real^(1,N)finite_sum->bool` THEN
  ASM_SIMP_TAC[SMOOTH_MAP_ON_FRECHET_DERIVATIVE]);;

let LRG_FLOW_DT = prove
 (`!U a b (G:real->real^N->real^N^N) t x.
        lricci_flow U a b G /\ a < t /\ t < b /\ x IN U
        ==> frechet_derivative
              (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                   (G (drop(fstcart z)) (sndcart z)))
              (at (pastecart (lift t) x)) (pastecart (lift(&1)) (vec 0)) =
            vectorize((lambda i j. --(&2) * lricci (G t) x (basis i) (basis j))
                      :real^N^N)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `a:real`; `b:real`;
                 `G:real->real^N->real^N^N`] LRG_FLOW_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(\z. (vectorize:real^N^N->real^(N,N)finite_prod)
         ((G:real->real^N->real^N^N) (drop(fstcart z)) (sndcart z)))
    differentiable at (pastecart (lift t) x)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `interval(lift a,lift b) PCROSS (U:real^N->bool)` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP LRG_HAS_DERIVATIVE_TIME_CURVE) THEN
  REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `a:real`; `b:real`;
                 `G:real->real^N->real^N^N`; `t:real`; `x:real^N`]
         LRG_FLOW_VDERIV) THEN
  ASM_REWRITE_TAC[has_vector_derivative] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `(\s'. frechet_derivative
            (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                 ((G:real->real^N->real^N^N) (drop(fstcart z)) (sndcart z)))
            (at (pastecart (lift t) x)) (pastecart s' (vec 0))) =
    (\s'. drop s' %
          vectorize((lambda i j. --(&2) * lricci (G t) x (basis i) (basis j))
                    :real^N^N))`
  MP_TAC THENL
   [MATCH_MP_TAC FRECHET_DERIVATIVE_UNIQUE_AT THEN
    EXISTS_TAC `\s. (vectorize:real^N^N->real^(N,N)finite_prod)
                    ((G:real->real^N->real^N^N) (drop s) x)` THEN
    EXISTS_TAC `lift t` THEN ASM_REWRITE_TAC[];
    DISCH_THEN(MP_TAC o C AP_THM `lift(&1)`) THEN
    REWRITE_TAC[LIFT_DROP; VECTOR_MUL_LID]]);;


(* ========================================================================= *)
(* Smoothness and time derivatives of the space derivative of the metric and *)
(* of the Christoffel symbols along a flow.                                  *)
(* ========================================================================= *)

let LRG_LINEAR_MATRIFY_MUL_COMPONENT = prove
 (`!(v:real^N) k.
        linear (\m:real^(N,N)finite_prod. lift(((matrify m:real^N^N) ** v)$k))`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN
   `(\m:real^(N,N)finite_prod. lift(((matrify m:real^N^N) ** v)$k)) =
    (\x:real^N. lift(x$k)) o (\m. matrify m ** v)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC LINEAR_COMPOSE THEN REWRITE_TAC[LINEAR_LIFT_COMPONENT] THEN
  MP_TAC(ISPEC `\(m:real^(N,N)finite_prod) (v:real^N). (matrify m:real^N^N) ** v`
         bilinear) THEN
  REWRITE_TAC[LRG_BILINEAR_MATRIFY_MUL] THEN SIMP_TAC[]);;

let LRG_LINEAR_MATRIFY_DOT = prove
 (`!(u:real^N) v.
        linear (\m:real^(N,N)finite_prod. lift(u dot ((matrify m:real^N^N) ** v)))`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN
   `(\m:real^(N,N)finite_prod. lift(u dot ((matrify m:real^N^N) ** v))) =
    (\x:real^N. lift(u dot x)) o (\m. matrify m ** v)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC LINEAR_COMPOSE THEN REWRITE_TAC[LINEAR_LIFT_DOT] THEN
  MP_TAC(ISPEC `\(m:real^(N,N)finite_prod) (v:real^N). (matrify m:real^N^N) ** v`
         bilinear) THEN
  REWRITE_TAC[LRG_BILINEAR_MATRIFY_MUL] THEN SIMP_TAC[]);;

let LRG_FLOW_MDERIV_JOINT = prove
 (`!(G:real->real^N->real^N^N) s x w.
        (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
             (G (drop(fstcart z)) (sndcart z))) differentiable at (pastecart s x)
        ==> mderiv (G (drop s)) x w =
            matrify(frechet_derivative
                     (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                          (G (drop(fstcart z)) (sndcart z)))
                     (at (pastecart s x)) (pastecart (vec 0) w))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mderiv; o_DEF] THEN AP_TERM_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `w:real^N` o MATCH_MP LRG_SLICE_DERIV) THEN
  REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART]);;

let LRG_FLOW_MDERIV_SMOOTH = prove
 (`!U a b (G:real->real^N->real^N^N) w.
        lricci_flow U a b G
        ==> smooth_map_on (interval(lift a,lift b) PCROSS U)
              (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                   (mderiv (G (drop(fstcart z))) (sndcart z) w))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `a:real`; `b:real`;
                 `G:real->real^N->real^N^N`] LRG_FLOW_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN
  EXISTS_TAC
   `\z. frechet_derivative
          (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
               ((G:real->real^N->real^N^N) (drop(fstcart z)) (sndcart z)))
          (at z) (pastecart (vec 0) w)` THEN
  ASM_SIMP_TAC[SMOOTH_MAP_ON_FRECHET_DERIVATIVE] THEN
  X_GEN_TAC `z:real^(1,N)finite_sum` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`G:real->real^N->real^N^N`; `fstcart(z:real^(1,N)finite_sum)`;
                 `sndcart(z:real^(1,N)finite_sum)`; `w:real^N`]
         LRG_FLOW_MDERIV_JOINT) THEN
  REWRITE_TAC[PASTECART_FST_SND] THEN ANTS_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `interval(lift a,lift b) PCROSS (U:real^N->bool)` THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[VECTORIZE_MATRIFY]]);;

let LRG_FLOW_TIME_SMOOTH = prove
 (`!U a b (G:real->real^N->real^N^N) y.
        lricci_flow U a b G /\ y IN U
        ==> smooth_map_on (interval(lift a,lift b))
              ((vectorize:real^N^N->real^(N,N)finite_prod) o (\s. G (drop s) y)) /\
            smooth_map_on (interval(lift a,lift b))
              ((vectorize:real^N^N->real^(N,N)finite_prod) o
               (\s. matrix_inv(G (drop s) y)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `a:real`; `b:real`;
                 `G:real->real^N->real^N^N`] LRG_FLOW_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `smooth_map_on (interval(lift a,lift b))
      ((vectorize:real^N^N->real^(N,N)finite_prod) o
       (\s. (G:real->real^N->real^N^N) (drop s) y))`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `(vectorize:real^N^N->real^(N,N)finite_prod) o
      (\s. (G:real->real^N->real^N^N) (drop s) y) =
      (\z. vectorize(G (drop(fstcart z)) (sndcart z))) o
      (\s:real^1. pastecart s y)`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM; FSTCART_PASTECART; SNDCART_PASTECART];
      ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
    EXISTS_TAC `interval(lift a,lift b) PCROSS (U:real^N->bool)` THEN
    ASM_REWRITE_TAC[OPEN_INTERVAL] THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; PASTECART_IN_PCROSS] THEN
      ASM_SIMP_TAC[];
      MATCH_MP_TAC SMOOTH_MAP_ON_PASTECART_OPEN THEN
      REWRITE_TAC[OPEN_INTERVAL; SMOOTH_MAP_ON_ID; SMOOTH_MAP_ON_CONST]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LRG_SMOOTH_MATRIX_INV THEN
  ASM_REWRITE_TAC[OPEN_INTERVAL] THEN
  X_GEN_TAC `s:real^1` THEN REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `(G:real->real^N->real^N^N) (drop s)`;
                 `y:real^N`] LRG_METRIC_INVERTIBLE) THEN
  ASM_SIMP_TAC[]);;

let LRG_FLOW_MDERIV_ENTRY_SMOOTH = prove
 (`!U a b (G:real->real^N->real^N^N) w v c k.
        lricci_flow U a b G
        ==> smooth_map_on (interval(lift a,lift b) PCROSS U)
              (\z. lift((mderiv (G (drop(fstcart z))) (sndcart z) w ** v)$k)) /\
            smooth_map_on (interval(lift a,lift b) PCROSS U)
              (\z. lift(c dot (mderiv (G (drop(fstcart z))) (sndcart z) w ** v)))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `a:real`; `b:real`;
                 `G:real->real^N->real^N^N`] LRG_FLOW_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `a:real`; `b:real`;
                 `G:real->real^N->real^N^N`; `w:real^N`]
         LRG_FLOW_MDERIV_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN CONJ_TAC THENL
   [SUBGOAL_THEN
     `(\z. lift((mderiv ((G:real->real^N->real^N^N) (drop(fstcart z)))
                       (sndcart z) w ** v)$k)) =
      (\m:real^(N,N)finite_prod. lift(((matrify m:real^N^N) ** v)$k)) o
      (\z. vectorize(mderiv (G (drop(fstcart z))) (sndcart z) w))`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM; MATRIFY_VECTORIZE]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_LINEAR_O THEN
    ASM_REWRITE_TAC[LRG_LINEAR_MATRIFY_MUL_COMPONENT];
    SUBGOAL_THEN
     `(\z. lift(c dot (mderiv ((G:real->real^N->real^N^N) (drop(fstcart z)))
                              (sndcart z) w ** v))) =
      (\m:real^(N,N)finite_prod. lift(c dot ((matrify m:real^N^N) ** v))) o
      (\z. vectorize(mderiv (G (drop(fstcart z))) (sndcart z) w))`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM; MATRIFY_VECTORIZE]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_LINEAR_O THEN
    ASM_REWRITE_TAC[LRG_LINEAR_MATRIFY_DOT]]);;

let LRG_FLOW_CHRISTOFFEL_SMOOTH = prove
 (`!U a b (G:real->real^N->real^N^N) u v.
        lricci_flow U a b G
        ==> smooth_map_on (interval(lift a,lift b) PCROSS U)
              (\z. christoffel (G (drop(fstcart z))) (sndcart z) u v)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `a:real`; `b:real`;
                 `G:real->real^N->real^N^N`] LRG_FLOW_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[christoffel] THEN
  MATCH_MP_TAC LRG_SMOOTH_MATVEC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC LRG_SMOOTH_MATRIX_INV THEN ASM_REWRITE_TAC[o_DEF] THEN
    REWRITE_TAC[FORALL_IN_PCROSS; FSTCART_PASTECART; SNDCART_PASTECART;
                IN_INTERVAL_1; LIFT_DROP] THEN
    MAP_EVERY X_GEN_TAC [`s:real^1`; `x:real^N`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `(G:real->real^N->real^N^N) (drop s)`;
                   `x:real^N`] LRG_METRIC_INVERTIBLE) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  GEN_REWRITE_TAC I [MATCH_MP SMOOTH_MAP_ON_COMPONENTWISE
    (ASSUME `open(interval(lift a,lift b) PCROSS (U:real^N->bool))`)] THEN
  X_GEN_TAC `k:num` THEN STRIP_TAC THEN ASM_SIMP_TAC[LAMBDA_BETA] THEN
  REWRITE_TAC[LIFT_CMUL; LIFT_ADD; LIFT_SUB] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_CMUL_OPEN THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[LRG_FLOW_MDERIV_ENTRY_SMOOTH];
    MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN
    ASM_SIMP_TAC[LRG_FLOW_MDERIV_ENTRY_SMOOTH]]);;


(* ========================================================================= *)
(* Vector derivatives of time curves; the time derivative of the space       *)
(* derivative of the metric is the space derivative of -2 Ric;               *)
(* LCHRISTOFFEL_EVOLUTION.                                                   *)
(* ========================================================================= *)

let LRG_TIME_CURVE_VDERIV = prove
 (`!(f:real^(1,N)finite_sum->real^P) t x.
        f differentiable at (pastecart (lift t) x)
        ==> ((\s. f(pastecart s x)) has_vector_derivative
             frechet_derivative f (at (pastecart (lift t) x))
                                (pastecart (lift(&1)) (vec 0))) (at (lift t))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[has_vector_derivative] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP LRG_HAS_DERIVATIVE_TIME_CURVE) THEN
  MATCH_MP_TAC(MESON[]
   `(f:real^1->real^P) = g
    ==> (h has_derivative f) (net:(real^1)net)
        ==> (h has_derivative g) net`) THEN
  REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `s:real^1` THEN
  SUBGOAL_THEN
   `pastecart s (vec 0:real^N) = drop s % pastecart (lift(&1)) (vec 0)`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM PASTECART_CMUL; VECTOR_MUL_RZERO; GSYM LIFT_CMUL;
                REAL_MUL_RID; LIFT_DROP];
    ALL_TAC] THEN
  ASM_SIMP_TAC[LINEAR_CMUL; LINEAR_FRECHET_DERIVATIVE]);;

let LRG_VDERIV_UNIQUE_OPEN = prove
 (`!(f:real^1->real^P) g f1 g1 s x.
        open s /\ x IN s /\ (!z. z IN s ==> f z = g z) /\
        (f has_vector_derivative f1) (at x) /\
        (g has_vector_derivative g1) (at x)
        ==> f1 = g1`,
  REWRITE_TAC[has_vector_derivative] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^1->real^P`; `g:real^1->real^P`;
                 `\h:real^1. drop h % (f1:real^P)`;
                 `\h:real^1. drop h % (g1:real^P)`;
                 `s:real^1->bool`; `x:real^1`] LRG_HAS_DERIVATIVE_UNIQUE_OPEN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o C AP_THM `lift(&1)`) THEN
  REWRITE_TAC[LIFT_DROP; VECTOR_MUL_LID]);;

let LRG_VDERIV_DOT_PRODUCT = prove
 (`!(A:real^1->real^N^N) A1 (b:real^1->real^N) b1 a s0.
        ((\s. vectorize(A s)) has_vector_derivative vectorize A1) (at s0) /\
        (b has_vector_derivative b1) (at s0)
        ==> ((\s. lift(a dot (A s ** b s))) has_vector_derivative
             lift(a dot (A1 ** b s0) + a dot (A s0 ** b1))) (at s0)`,
  REWRITE_TAC[has_vector_derivative] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`A:real^1->real^N^N`;
                 `\h:real^1. drop h % vectorize(A1:real^N^N)`;
                 `\s:real^1. (a:real^N)`; `\h:real^1. vec 0:real^N`;
                 `b:real^1->real^N`; `\h:real^1. drop h % (b1:real^N)`;
                 `s0:real^1`] LRG_HAS_DERIVATIVE_DOT_MATVEC) THEN
  ASM_REWRITE_TAC[o_DEF; HAS_DERIVATIVE_CONST] THEN
  MATCH_MP_TAC(MESON[]
   `(f:real^1->real^1) = g
    ==> (h has_derivative f) (net:(real^1)net)
        ==> (h has_derivative g) net`) THEN
  REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `h:real^1` THEN
  REWRITE_TAC[MATRIFY_CMUL; MATRIFY_VECTORIZE; MATRIX_VECTOR_LMUL;
              MATRIX_VECTOR_MUL_RMUL; DOT_LZERO; DOT_RADD; DOT_RMUL;
              REAL_ADD_LID] THEN
  REWRITE_TAC[GSYM LIFT_CMUL] THEN AP_TERM_TAC THEN REAL_ARITH_TAC);;

let LRG_FLOW_RICM_SMOOTH = prove
 (`!U a b (G:real->real^N->real^N^N) t.
        lricci_flow U a b G /\ a < t /\ t < b
        ==> smooth_map_on U
              ((vectorize:real^N^N->real^(N,N)finite_prod) o
               (\x. (lambda i j. --(&2) * lricci (G t) x (basis i) (basis j))
                    :real^N^N))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `a:real`; `b:real`;
                 `G:real->real^N->real^N^N`] LRG_FLOW_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN
  EXISTS_TAC
   `\x:real^N. frechet_derivative
                (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                     ((G:real->real^N->real^N^N) (drop(fstcart z)) (sndcart z)))
                (at (pastecart (lift t) x)) (pastecart (lift(&1)) (vec 0))` THEN
  ASM_REWRITE_TAC[o_THM] THEN CONJ_TAC THENL
   [X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN MATCH_MP_TAC LRG_FLOW_DT THEN
    MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `a:real`; `b:real`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\x:real^N. frechet_derivative
                 (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                      ((G:real->real^N->real^N^N) (drop(fstcart z)) (sndcart z)))
                 (at (pastecart (lift t) x)) (pastecart (lift(&1)) (vec 0))) =
    (\z. frechet_derivative
           (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                ((G:real->real^N->real^N^N) (drop(fstcart z)) (sndcart z)))
           (at z) (pastecart (lift(&1)) (vec 0))) o
    (\x. pastecart (lift t) x)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
  EXISTS_TAC `interval(lift a,lift b) PCROSS (U:real^N->bool)` THEN
  ASM_SIMP_TAC[SMOOTH_MAP_ON_FRECHET_DERIVATIVE] THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[SUBSET; FORALL_IN_IMAGE];
    MATCH_MP_TAC SMOOTH_MAP_ON_PASTECART_OPEN THEN
    ASM_REWRITE_TAC[SMOOTH_MAP_ON_CONST; SMOOTH_MAP_ON_ID]]);;

let LRG_FLOW_MDERIV_DT = prove
 (`!U a b (G:real->real^N->real^N^N) t y w.
        lricci_flow U a b G /\ a < t /\ t < b /\ y IN U
        ==> ((\s. vectorize(mderiv (G (drop s)) y w)) has_vector_derivative
             vectorize(mderiv (\x. (lambda i j. --(&2) * lricci (G t) x
                                                     (basis i) (basis j))
                                   :real^N^N) y w))
            (at (lift t))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `a:real`; `b:real`;
                 `G:real->real^N->real^N^N`] LRG_FLOW_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[mderiv; VECTORIZE_MATRIFY; o_DEF] THEN
  MP_TAC(ISPECL
   [`interval(lift a,lift b) PCROSS (U:real^N->bool)`;
    `\z. (vectorize:real^N^N->real^(N,N)finite_prod)
         ((G:real->real^N->real^N^N) (drop(fstcart z)) (sndcart z))`;
    `t:real`; `y:real^N`; `w:real^N`] LRG_TIME_SPACE_SWAP) THEN
  ASM_REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN
  MATCH_MP_TAC(MESON[]
   `(x:real^(N,N)finite_prod) = y
    ==> (f has_vector_derivative x) (net:(real^1)net)
        ==> (f has_vector_derivative y) net`) THEN
  AP_THM_TAC THEN MATCH_MP_TAC LRG_FRECHET_DERIVATIVE_EQ_OPEN THEN
  EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC LRG_FLOW_DT THEN
  MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `a:real`; `b:real`] THEN
  ASM_REWRITE_TAC[]);;

let LRG_LRICCI_DOT_FORM = prove
 (`!U (G:real^N->real^N^N) z p q.
        metric_field U G /\ z IN U
        ==> lricci G z p q =
            p dot ((lambda i j. lricci G z (basis i) (basis j)):real^N^N ** q)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `z:real^N`;
                 `p:real^N`; `q:real^N`] LRG_LRICCI_EXPAND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[dot; matrix_vector_mul] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  BETA_TAC THEN ASM_SIMP_TAC[LAMBDA_BETA] THEN AP_TERM_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  BETA_TAC THEN ASM_SIMP_TAC[LAMBDA_BETA] THEN REAL_ARITH_TAC);;

let LRG_HDOT = prove
 (`!U (G:real^N->real^N^N) z p q.
        metric_field U G /\ z IN U
        ==> p dot ((lambda i j. --(&2) * lricci G z (basis i) (basis j))
                   :real^N^N ** q) =
            --(&2) * lricci G z p q`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `(lambda i j. --(&2) * lricci (G:real^N->real^N^N) z (basis i) (basis j))
    :real^N^N =
    --(&2) %% (lambda i j. lricci G z (basis i) (basis j))`
  SUBST1_TAC THENL
   [SIMP_TAC[CART_EQ; LAMBDA_BETA; MATRIX_CMUL_COMPONENT]; ALL_TAC] THEN
  REWRITE_TAC[MATRIX_VECTOR_LMUL; DOT_RMUL] THEN AP_TERM_TAC THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC LRG_LRICCI_DOT_FORM THEN
  EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[]);;

let LRG_FLOW_DRIC = prove
 (`!U a b (G:real->real^N->real^N^N) t y p q d.
        lricci_flow U a b G /\ a < t /\ t < b /\ y IN U
        ==> frechet_derivative (\z. lift(lricci (G t) z p q)) (at y) d =
            lift(--(inv(&2)) *
                 (p dot (mderiv (\x. (lambda i j. --(&2) * lricci (G t) x
                                                        (basis i) (basis j))
                                     :real^N^N) y d ** q)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `a:real`; `b:real`;
                 `G:real->real^N->real^N^N`] LRG_FLOW_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `metric_field U ((G:real->real^N->real^N^N) t)` ASSUME_TAC
  THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `((vectorize:real^N^N->real^(N,N)finite_prod) o
     (\x. (lambda i j. --(&2) * lricci ((G:real->real^N->real^N^N) t) x
                                       (basis i) (basis j)):real^N^N))
    differentiable at y`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC LRG_FLOW_RICM_SMOOTH THEN
    MAP_EVERY EXISTS_TAC [`a:real`; `b:real`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `frechet_derivative
     (\z. --(inv(&2)) %
          lift(p dot ((lambda i j. --(&2) * lricci ((G:real->real^N->real^N^N) t)
                                                   z (basis i) (basis j))
                      :real^N^N ** q))) (at y) d` THEN
  CONJ_TAC THENL
   [AP_THM_TAC THEN MATCH_MP_TAC LRG_FRECHET_DERIVATIVE_EQ_OPEN THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `(G:real->real^N->real^N^N) t`;
                   `z:real^N`; `p:real^N`; `q:real^N`] LRG_HDOT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[GSYM LIFT_CMUL] THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\x. (lambda i j. --(&2) * lricci ((G:real->real^N->real^N^N) t) x
                                      (basis i) (basis j)):real^N^N`;
    `y:real^N`; `p:real^N`; `q:real^N`] LRG_HAS_DERIVATIVE_GDOT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o BETA_RULE o SPEC `--(inv(&2))` o
             MATCH_MP HAS_DERIVATIVE_CMUL) THEN
  DISCH_THEN(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
  REWRITE_TAC[LIFT_CMUL]);;

let LRG_FLOW_DH_SYM = prove
 (`!U a b (G:real->real^N->real^N^N) t y d p q.
        lricci_flow U a b G /\ a < t /\ t < b /\ y IN U
        ==> p dot (mderiv (\x. (lambda i j. --(&2) * lricci (G t) x
                                                (basis i) (basis j))
                              :real^N^N) y d ** q) =
            q dot (mderiv (\x. (lambda i j. --(&2) * lricci (G t) x
                                                (basis i) (basis j))
                              :real^N^N) y d ** p)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `a:real`; `b:real`;
                 `G:real->real^N->real^N^N`] LRG_FLOW_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `metric_field U ((G:real->real^N->real^N^N) t)` ASSUME_TAC
  THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `((vectorize:real^N^N->real^(N,N)finite_prod) o
     (\x. (lambda i j. --(&2) * lricci ((G:real->real^N->real^N^N) t) x
                                       (basis i) (basis j)):real^N^N))
    differentiable at y`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC LRG_FLOW_RICM_SMOOTH THEN
    MAP_EVERY EXISTS_TAC [`a:real`; `b:real`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\z. lift(p dot ((lambda i j. --(&2) * lricci ((G:real->real^N->real^N^N) t)
                                                  z (basis i) (basis j))
                     :real^N^N ** q))`;
    `\z. lift(q dot ((lambda i j. --(&2) * lricci ((G:real->real^N->real^N^N) t)
                                                  z (basis i) (basis j))
                     :real^N^N ** p))`;
    `\w. lift(p dot (mderiv (\x. (lambda i j. --(&2) *
                         lricci ((G:real->real^N->real^N^N) t) x
                                (basis i) (basis j)):real^N^N) y w ** q))`;
    `\w. lift(q dot (mderiv (\x. (lambda i j. --(&2) *
                         lricci ((G:real->real^N->real^N^N) t) x
                                (basis i) (basis j)):real^N^N) y w ** p))`;
    `U:real^N->bool`; `y:real^N`] LRG_HAS_DERIVATIVE_UNIQUE_OPEN) THEN
  ASM_SIMP_TAC[LRG_HAS_DERIVATIVE_GDOT] THEN ANTS_TAC THENL
   [X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN AP_TERM_TAC THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `(G:real->real^N->real^N^N) t`;
                   `z:real^N`; `p:real^N`; `q:real^N`] LRG_HDOT) THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `(G:real->real^N->real^N^N) t`;
                   `z:real^N`; `q:real^N`; `p:real^N`] LRG_HDOT) THEN
    ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN
    AP_TERM_TAC THEN MATCH_MP_TAC LRICCI_SYM THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    DISCH_THEN(MP_TAC o C AP_THM `d:real^N`) THEN REWRITE_TAC[LIFT_EQ]]);;

let LRG_LNABLA2_LRIC2 = prove
 (`!(G:real^N->real^N^N) y p q d.
        lnabla 2 G (lric2 G) y
          (\m. if m = 1 then p else if m = 2 then q else d) =
        drop(frechet_derivative (\z. lift(lricci G z p q)) (at y) d) -
        (lricci G y (christoffel G y d p) q + lricci G y p (christoffel G y d q))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[lnabla; lric2; SUM_2] THEN
  REWRITE_TAC[ARITH]);;

let LRG_FLOW_MDOT_DT = prove
 (`!U a b (G:real->real^N->real^N^N) t y p q d.
        lricci_flow U a b G /\ a < t /\ t < b /\ y IN U
        ==> ((\s. lift(p dot (mderiv (G (drop s)) y d ** q)))
             has_vector_derivative
             lift(p dot (mderiv (\x. (lambda i j. --(&2) * lricci (G t) x
                                                       (basis i) (basis j))
                                     :real^N^N) y d ** q))) (at (lift t))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\s. mderiv ((G:real->real^N->real^N^N) (drop s)) y d`;
                 `mderiv (\x. (lambda i j. --(&2) *
                                lricci ((G:real->real^N->real^N^N) t) x
                                       (basis i) (basis j)):real^N^N) y d`;
                 `\s:real^1. (q:real^N)`; `vec 0:real^N`; `p:real^N`;
                 `lift t`] LRG_VDERIV_DOT_PRODUCT) THEN
  REWRITE_TAC[HAS_VECTOR_DERIVATIVE_CONST; MATRIX_VECTOR_MUL_RZERO;
              DOT_RZERO; REAL_ADD_RID] THEN
  DISCH_THEN MATCH_MP_TAC THEN MATCH_MP_TAC LRG_FLOW_MDERIV_DT THEN
  ASM_MESON_TAC[]);;

let LCHRISTOFFEL_EVOLUTION = prove
 (`!U a b (G:real->real^N->real^N^N) t y u v.
        lricci_flow U a b G /\ a < t /\ t < b /\ y IN U
        ==> ?w. ((\s. christoffel (G (drop s)) y u v) has_vector_derivative w)
                  (at (lift t)) /\
                !k. 1 <= k /\ k <= dimindex(:N)
                    ==> (G t y ** w)$k =
                        --(lnabla 2 (G t) (lric2 (G t)) y
                             (\m. if m = 1 then v else if m = 2 then basis k else u) +
                           lnabla 2 (G t) (lric2 (G t)) y
                             (\m. if m = 1 then u else if m = 2 then basis k else v) -
                           lnabla 2 (G t) (lric2 (G t)) y
                             (\m. if m = 1 then u else if m = 2 then v else basis k))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `a:real`; `b:real`;
                 `G:real->real^N->real^N^N`] LRG_FLOW_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `metric_field U ((G:real->real^N->real^N^N) t)` ASSUME_TAC
  THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `a:real`; `b:real`;
                 `G:real->real^N->real^N^N`; `u:real^N`; `v:real^N`]
         LRG_FLOW_CHRISTOFFEL_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `(\z. christoffel ((G:real->real^N->real^N^N) (drop(fstcart z))) (sndcart z)
                    u v) differentiable at (pastecart (lift t) y)`
  MP_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `interval(lift a,lift b) PCROSS (U:real^N->bool)` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP LRG_TIME_CURVE_VDERIV) THEN
  REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN
  SPEC_TAC(`frechet_derivative
             (\z. christoffel ((G:real->real^N->real^N^N) (drop(fstcart z)))
                              (sndcart z) u v)
             (at (pastecart (lift t) y)) (pastecart (lift(&1)) (vec 0))`,
           `w:real^N`) THEN
  X_GEN_TAC `w:real^N` THEN DISCH_TAC THEN EXISTS_TAC `w:real^N` THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `a:real`; `b:real`;
                 `G:real->real^N->real^N^N`; `t:real`; `y:real^N`]
         LRG_FLOW_VDERIV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `basis k dot ((lambda i j. --(&2) * lricci ((G:real->real^N->real^N^N) t) y
                                                (basis i) (basis j)):real^N^N **
                 christoffel (G t) y u v) +
    basis k dot (G t y ** w) =
    inv(&2) *
    (basis k dot (mderiv (\x. (lambda i j. --(&2) * lricci (G t) x
                                                  (basis i) (basis j))
                              :real^N^N) y u ** v) +
     basis k dot (mderiv (\x. (lambda i j. --(&2) * lricci (G t) x
                                                  (basis i) (basis j))
                              :real^N^N) y v ** u) -
     u dot (mderiv (\x. (lambda i j. --(&2) * lricci (G t) x
                                            (basis i) (basis j))
                        :real^N^N) y (basis k) ** v))`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM LIFT_EQ] THEN MATCH_MP_TAC LRG_VDERIV_UNIQUE_OPEN THEN
    EXISTS_TAC
     `\s. lift(basis k dot ((G:real->real^N->real^N^N) (drop s) y **
                            christoffel (G (drop s)) y u v))` THEN
    EXISTS_TAC
     `\s. lift(inv(&2) *
               (basis k dot (mderiv ((G:real->real^N->real^N^N) (drop s)) y u
                             ** v) +
                basis k dot (mderiv (G (drop s)) y v ** u) -
                u dot (mderiv (G (drop s)) y (basis k) ** v)))` THEN
    EXISTS_TAC `interval(lift a,lift b)` THEN EXISTS_TAC `lift t` THEN
    REWRITE_TAC[OPEN_INTERVAL; IN_INTERVAL_1; LIFT_DROP] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [X_GEN_TAC `s:real^1` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
      AP_TERM_TAC THEN MATCH_MP_TAC LRG_CHRISTOFFEL_DOT THEN
      EXISTS_TAC `U:real^N->bool` THEN ASM_SIMP_TAC[];
      MP_TAC(ISPECL
       [`\s. (G:real->real^N->real^N^N) (drop s) y`;
        `(lambda i j. --(&2) * lricci ((G:real->real^N->real^N^N) t) y
                                      (basis i) (basis j)):real^N^N`;
        `\s. christoffel ((G:real->real^N->real^N^N) (drop s)) y u v`;
        `w:real^N`; `basis k:real^N`; `lift t`] LRG_VDERIV_DOT_PRODUCT) THEN
      ASM_REWRITE_TAC[LIFT_DROP];
      REWRITE_TAC[LIFT_CMUL; LIFT_ADD; LIFT_SUB] THEN
      MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_CMUL THEN
      MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_ADD THEN CONJ_TAC THENL
       [MATCH_MP_TAC LRG_FLOW_MDOT_DT THEN ASM_MESON_TAC[];
        MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_SUB THEN CONJ_TAC THEN
        MATCH_MP_TAC LRG_FLOW_MDOT_DT THEN ASM_MESON_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(G t y ** w)$k = basis k dot ((G:real->real^N->real^N^N) t y ** w)`
  SUBST1_TAC THENL [ASM_SIMP_TAC[DOT_BASIS]; ALL_TAC] THEN
  REWRITE_TAC[LRG_LNABLA2_LRIC2] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `a:real`; `b:real`;
                 `G:real->real^N->real^N^N`; `t:real`; `y:real^N`]
         LRG_FLOW_DRIC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th; LIFT_DROP]) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `a:real`; `b:real`;
                 `G:real->real^N->real^N^N`; `t:real`; `y:real^N`;
                 `u:real^N`; `v:real^N`; `basis k:real^N`] LRG_FLOW_DH_SYM) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `a:real`; `b:real`;
                 `G:real->real^N->real^N^N`; `t:real`; `y:real^N`;
                 `v:real^N`; `u:real^N`; `basis k:real^N`] LRG_FLOW_DH_SYM) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `(G:real->real^N->real^N^N) t`; `y:real^N`;
                 `v:real^N`; `u:real^N`] CHRISTOFFEL_SYM) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `(G:real->real^N->real^N^N) t`; `y:real^N`;
                 `u:real^N`; `basis k:real^N`] CHRISTOFFEL_SYM) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `(G:real->real^N->real^N^N) t`; `y:real^N`;
                 `v:real^N`; `basis k:real^N`] CHRISTOFFEL_SYM) THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT(DISCH_THEN SUBST1_TAC) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `(G:real->real^N->real^N^N) t`; `y:real^N`;
                 `christoffel ((G:real->real^N->real^N^N) t) y u v`;
                 `basis k:real^N`] LRICCI_SYM) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `(G:real->real^N->real^N^N) t`; `y:real^N`;
                 `v:real^N`;
                 `christoffel ((G:real->real^N->real^N^N) t) y (basis k) u`]
         LRICCI_SYM) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `(G:real->real^N->real^N^N) t`; `y:real^N`;
                 `basis k:real^N`; `christoffel ((G:real->real^N->real^N^N) t) y u v`]
         LRG_HDOT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MAP_EVERY UNDISCH_TAC
   [`basis k dot ((lambda i j. --(&2) * lricci ((G:real->real^N->real^N^N) t) y
                                                (basis i) (basis j)):real^N^N **
                  christoffel (G t) y u v) =
     --(&2) * lricci (G t) y (basis k) (christoffel (G t) y u v)`;
    `basis k dot ((lambda i j. --(&2) * lricci ((G:real->real^N->real^N^N) t) y
                                                (basis i) (basis j)):real^N^N **
                  christoffel (G t) y u v) +
     basis k dot (G t y ** w) =
     inv(&2) *
     (basis k dot (mderiv (\x. (lambda i j. --(&2) * lricci (G t) x
                                                   (basis i) (basis j))
                               :real^N^N) y u ** v) +
      basis k dot (mderiv (\x. (lambda i j. --(&2) * lricci (G t) x
                                                   (basis i) (basis j))
                               :real^N^N) y v ** u) -
      u dot (mderiv (\x. (lambda i j. --(&2) * lricci (G t) x
                                             (basis i) (basis j))
                         :real^N^N) y (basis k) ** v))`] THEN
  REAL_ARITH_TAC);;


(* ========================================================================= *)
(* Tensor calculus toolkit for the scalar curvature evolution: lnabla        *)
(* commutes with permutations of the tensor slots and is linear in the       *)
(* tensor; derivative of the inverse of a matrix field; the Ricci tensor and *)
(* the scalar curvature are smooth.                                          *)
(* ========================================================================= *)

let LRG_LNABLA_PERMUTE = prove
 (`!n (G:real^N->real^N^N) (tf:real^N->(num->real^N)->real) p y u.
        p permutes 1..n
        ==> lnabla n G (\x u. tf x (\m. u(p m))) y u =
            lnabla n G tf y (\m. u(p m))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(p:num->num)(n + 1) = n + 1` ASSUME_TAC THENL
   [FIRST_ASSUM(MATCH_MP_TAC o CONJUNCT1 o REWRITE_RULE[permutes]) THEN
    REWRITE_TAC[IN_NUMSEG] THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[lnabla] THEN ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN
  MP_TAC(ISPECL
   [`\i. (tf:real^N->(num->real^N)->real) y
          (\m. if (p:num->num) m = i
               then christoffel (G:real^N->real^N^N) y (u(n + 1)) ((u:num->real^N) i)
               else u(p m))`;
    `p:num->num`; `1..n`] SUM_PERMUTE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  REWRITE_TAC[o_THM] THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
  X_GEN_TAC `m:num` THEN
  MP_TAC(ISPECL [`p:num->num`; `1..n`] PERMUTES_INJECTIVE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]));;

let LRG_TENSOR_FIELD_PERMUTE = prove
 (`!n U (tf:real^N->(num->real^N)->real) p.
        ltensor_field n U tf /\ p permutes 1..n
        ==> ltensor_field n U (\x u. tf x (\m. u(p m)))`,
  REWRITE_TAC[ltensor_field] THEN REPEAT STRIP_TAC THENL
   [BETA_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `y:real^N`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN
    X_GEN_TAC `m:num` THEN STRIP_TAC THEN BETA_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    MP_TAC(ISPECL [`p:num->num`; `1..n`; `m:num`] PERMUTES_IN_IMAGE) THEN
    ASM_REWRITE_TAC[IN_NUMSEG];
    BETA_TAC THEN
    MP_TAC(ISPECL [`p:num->num`; `1..n`] PERMUTES_SURJECTIVE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `i':num` o SPEC `i:num`) THEN
    SUBGOAL_THEN `1 <= i' /\ i' <= n` STRIP_ASSUME_TAC THENL
     [MP_TAC(ISPECL [`p:num->num`; `1..n`; `i':num`] PERMUTES_IN_IMAGE) THEN
      ASM_REWRITE_TAC[IN_NUMSEG];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `!v:real^N. (\m. if (p:num->num) m = i then v else (u:num->real^N)(p m)) =
                 (\m. if m = i' then v else u(p m))`
    (fun th -> REWRITE_TAC[th]) THENL
     [GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `m:num` THEN
      BETA_TAC THEN
      UNDISCH_TAC `(p:num->num) i' = i` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      MP_TAC(ISPECL [`p:num->num`; `1..n`] PERMUTES_INJECTIVE) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]);
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:real^N`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL [`i':num`; `\m. (u:num->real^N)((p:num->num) m)`]
               o CONJUNCT2) THEN
    ASM_REWRITE_TAC[]]);;

let LRG_LNABLA_ADD = prove
 (`!k (G:real^N->real^N^N) (tf1:real^N->(num->real^N)->real) tf2 y u.
        (\x. lift(tf1 x u)) differentiable at y /\
        (\x. lift(tf2 x u)) differentiable at y
        ==> lnabla k G (\x u. tf1 x u + tf2 x u) y u =
            lnabla k G tf1 y u + lnabla k G tf2 y u`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[lnabla; LIFT_ADD] THEN
  SUBGOAL_THEN
   `frechet_derivative (\z. lift((tf1:real^N->(num->real^N)->real) z u) +
                            lift(tf2 z u)) (at y) =
    (\h. frechet_derivative (\z. lift(tf1 z u)) (at y) h +
         frechet_derivative (\z. lift(tf2 z u)) (at y) h)`
  SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
    MATCH_MP_TAC HAS_DERIVATIVE_ADD THEN
    ASM_REWRITE_TAC[ETA_AX; GSYM FRECHET_DERIVATIVE_WORKS];
    ALL_TAC] THEN
  REWRITE_TAC[DROP_ADD; SUM_ADD_NUMSEG] THEN REAL_ARITH_TAC);;

let LRG_LNABLA_SUB = prove
 (`!k (G:real^N->real^N^N) (tf1:real^N->(num->real^N)->real) tf2 y u.
        (\x. lift(tf1 x u)) differentiable at y /\
        (\x. lift(tf2 x u)) differentiable at y
        ==> lnabla k G (\x u. tf1 x u - tf2 x u) y u =
            lnabla k G tf1 y u - lnabla k G tf2 y u`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[lnabla; LIFT_SUB] THEN
  SUBGOAL_THEN
   `frechet_derivative (\z. lift((tf1:real^N->(num->real^N)->real) z u) -
                            lift(tf2 z u)) (at y) =
    (\h. frechet_derivative (\z. lift(tf1 z u)) (at y) h -
         frechet_derivative (\z. lift(tf2 z u)) (at y) h)`
  SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
    MATCH_MP_TAC HAS_DERIVATIVE_SUB THEN
    ASM_REWRITE_TAC[ETA_AX; GSYM FRECHET_DERIVATIVE_WORKS];
    ALL_TAC] THEN
  REWRITE_TAC[DROP_SUB; SUM_SUB_NUMSEG] THEN REAL_ARITH_TAC);;

let LRG_LNABLA_CMUL = prove
 (`!k (G:real^N->real^N^N) (tf:real^N->(num->real^N)->real) c y u.
        (\x. lift(tf x u)) differentiable at y
        ==> lnabla k G (\x u. c * tf x u) y u = c * lnabla k G tf y u`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[lnabla; LIFT_CMUL] THEN
  SUBGOAL_THEN
   `frechet_derivative (\z. c % lift((tf:real^N->(num->real^N)->real) z u))
                       (at y) =
    (\h. c % frechet_derivative (\z. lift(tf z u)) (at y) h)`
  SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
    MATCH_MP_TAC HAS_DERIVATIVE_CMUL THEN
    ASM_REWRITE_TAC[ETA_AX; GSYM FRECHET_DERIVATIVE_WORKS];
    ALL_TAC] THEN
  REWRITE_TAC[DROP_CMUL; SUM_LMUL] THEN REAL_ARITH_TAC);;

let LRG_MATRIX_SOLVE_LEFT = prove
 (`!(A:real^N^N) (X:real^N^N) (Y:real^N^N).
        invertible A /\ A ** X + Y = mat 0 ==> X = --(matrix_inv A ** Y)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(A:real^N^N) ** (X:real^N^N) = --(Y:real^N^N)` ASSUME_TAC THENL
   [UNDISCH_TAC `(A:real^N^N) ** (X:real^N^N) + (Y:real^N^N) = mat 0` THEN
    SIMP_TAC[CART_EQ; MATRIX_ADD_COMPONENT; MATRIX_NEG_COMPONENT;
             MAT_0_COMPONENT] THEN
    MESON_TAC[REAL_ARITH `a + b = &0 ==> a = --b`];
    ALL_TAC] THEN
  SUBGOAL_THEN `X:real^N^N = matrix_inv(A:real^N^N) ** (A ** (X:real^N^N))` SUBST1_TAC THENL
   [ASM_SIMP_TAC[MATRIX_MUL_ASSOC; MATRIX_INV; MATRIX_MUL_LID]; ALL_TAC] THEN
  ASM_REWRITE_TAC[MATRIX_MUL_RNEG]);;

let LRG_HAS_DERIVATIVE_MATRIX_INV = prove
 (`!(A:real^M->real^N^N) s y.
        open s /\ y IN s /\ smooth_map_on s (vectorize o A) /\
        (!z. z IN s ==> ~(det(A z) = &0))
        ==> ((vectorize o (\z. matrix_inv(A z))) has_derivative
             (\h. vectorize(--(matrix_inv(A y) **
                              matrify(frechet_derivative (vectorize o A) (at y) h) **
                              matrix_inv(A y))))) (at y)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `invertible((A:real^M->real^N^N) y)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[INVERTIBLE_DET_NZ]; ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on s ((vectorize:real^N^N->real^(N,N)finite_prod) o
                     (\z. matrix_inv((A:real^M->real^N^N) z)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC LRG_SMOOTH_MATRIX_INV THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC
   `Ad = frechet_derivative ((vectorize:real^N^N->real^(N,N)finite_prod) o
                             (A:real^M->real^N^N)) (at y)` THEN
  ABBREV_TAC
   `Bd = frechet_derivative ((vectorize:real^N^N->real^(N,N)finite_prod) o
                             (\z. matrix_inv((A:real^M->real^N^N) z))) (at y)` THEN
  SUBGOAL_THEN
   `((vectorize:real^N^N->real^(N,N)finite_prod) o (A:real^M->real^N^N)
     has_derivative Ad) (at y)`
  ASSUME_TAC THENL
   [EXPAND_TAC "Ad" THEN REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
    ASM_MESON_TAC[SMOOTH_MAP_ON_DIFFERENTIABLE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((vectorize:real^N^N->real^(N,N)finite_prod) o
     (\z. matrix_inv((A:real^M->real^N^N) z)) has_derivative Bd) (at y)`
  ASSUME_TAC THENL
   [EXPAND_TAC "Bd" THEN REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
    ASM_MESON_TAC[SMOOTH_MAP_ON_DIFFERENTIABLE];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\(m1:real^(N,N)finite_prod) (m2:real^(N,N)finite_prod).
       (vectorize:real^N^N->real^(N,N)finite_prod)
       ((matrify m1:real^N^N) ** (matrify m2:real^N^N))`;
    `(vectorize:real^N^N->real^(N,N)finite_prod) o (A:real^M->real^N^N)`;
    `(vectorize:real^N^N->real^(N,N)finite_prod) o
     (\z. matrix_inv((A:real^M->real^N^N) z))`;
    `Ad:real^M->real^(N,N)finite_prod`; `Bd:real^M->real^(N,N)finite_prod`;
    `y:real^M`] HAS_DERIVATIVE_BILINEAR_AT) THEN
  ASM_REWRITE_TAC[LRG_BILINEAR_MATRIX_MUL; o_THM; MATRIFY_VECTORIZE] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL
   [`\z. (vectorize:real^N^N->real^(N,N)finite_prod)
         ((A:real^M->real^N^N) z ** matrix_inv(A z))`;
    `\z:real^M. (vectorize:real^N^N->real^(N,N)finite_prod) (mat 1)`;
    `\d. (vectorize:real^N^N->real^(N,N)finite_prod)
         ((A:real^M->real^N^N) y ** matrify((Bd:real^M->real^(N,N)finite_prod) d)) +
         vectorize(matrify((Ad:real^M->real^(N,N)finite_prod) d) ** matrix_inv(A y))`;
    `\h:real^M. vec 0:real^(N,N)finite_prod`;
    `s:real^M->bool`; `y:real^M`] LRG_HAS_DERIVATIVE_UNIQUE_OPEN) THEN
  ASM_REWRITE_TAC[HAS_DERIVATIVE_CONST] THEN ANTS_TAC THENL
   [X_GEN_TAC `z:real^M` THEN DISCH_TAC THEN REWRITE_TAC[] THEN AP_TERM_TAC THEN
    ASM_SIMP_TAC[MATRIX_INV; INVERTIBLE_DET_NZ];
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN
   `Bd = (\h. (vectorize:real^N^N->real^(N,N)finite_prod)
               (--(matrix_inv((A:real^M->real^N^N) y) **
                   matrify((Ad:real^M->real^(N,N)finite_prod) h) **
                   matrix_inv(A y))))`
  (fun th -> ASM_MESON_TAC[th]) THEN
  REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `d:real^M` THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM VECTORIZE_MATRIFY] THEN AP_TERM_TAC THEN
  MATCH_MP_TAC LRG_MATRIX_SOLVE_LEFT THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o C AP_THM `d:real^M`) THEN
  REWRITE_TAC[GSYM VECTORIZE_ADD; VECTORIZE_EQ_0]);;

let LRG_HAS_DERIVATIVE_GINV_ENTRY = prove
 (`!U (G:real^N->real^N^N) y a b.
        metric_field U G /\ y IN U
        ==> ((\x. lift(matrix_inv(G x)$a$b)) has_derivative
             (\h. lift(--((matrix_inv(G y) ** mderiv G y h **
                           matrix_inv(G y))$a$b)))) (at y)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`G:real^N->real^N^N`; `U:real^N->bool`; `y:real^N`]
         LRG_HAS_DERIVATIVE_MATRIX_INV) THEN
  ANTS_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[metric_field]) THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `z:real^N`]
           LRG_METRIC_INVERTIBLE) THEN
    ASM_REWRITE_TAC[metric_field] THEN SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL
   [`(vectorize:real^N^N->real^(N,N)finite_prod) o
     (\z. matrix_inv((G:real^N->real^N^N) z))`;
    `\v:real^(N,N)finite_prod. lift((matrify v:real^N^N)$a$b)`;
    `\h. (vectorize:real^N^N->real^(N,N)finite_prod)
         (--(matrix_inv((G:real^N->real^N^N) y) **
             matrify(frechet_derivative (vectorize o G) (at y) h) **
             matrix_inv(G y)))`;
    `\v:real^(N,N)finite_prod. lift((matrify v:real^N^N)$a$b)`;
    `y:real^N`] DIFF_CHAIN_AT) THEN
  ASM_SIMP_TAC[HAS_DERIVATIVE_LINEAR; LRG_LINEAR_MATRIFY_ENTRY] THEN
  REWRITE_TAC[o_DEF; MATRIFY_VECTORIZE; mderiv; MATRIX_NEG_COMPONENT]);;

let LRG_LRIC2_FIELD = prove
 (`!U (G:real^N->real^N^N).
        metric_field U G
        ==> ltensor_field 2 U (lric2 G) /\
            (!u. smooth_map_on U (\x. lift(lric2 G x u)))`,
  REPEAT STRIP_TAC THENL
   [REWRITE_TAC[ltensor_field; lric2] THEN X_GEN_TAC `y:real^N` THEN
    DISCH_TAC THEN CONJ_TAC THENL
     [REPEAT GEN_TAC THEN DISCH_TAC THEN
      SUBGOAL_THEN `(u:num->real^N) 1 = u' 1 /\ u 2 = u' 2`
      (fun th -> REWRITE_TAC[th]) THEN
      CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC;
      MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`]
             LRG_LRICCI_LINEAR) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      X_GEN_TAC `i:num` THEN X_GEN_TAC `u:num->real^N` THEN STRIP_TAC THEN
      SUBGOAL_THEN `i = 1 \/ i = 2` (DISJ_CASES_THEN SUBST1_TAC) THENL
       [MAP_EVERY UNDISCH_TAC [`1 <= (i:num)`; `(i:num) <= 2`] THEN ARITH_TAC;
        ASM_REWRITE_TAC[ARITH];
        ASM_REWRITE_TAC[ARITH]]];
    REWRITE_TAC[lric2; lricci] THEN
    MATCH_MP_TAC LRG_SMOOTH_LIFT_SUM_REAL THEN
    RULE_ASSUM_TAC(REWRITE_RULE[metric_field]) THEN
    ASM_REWRITE_TAC[FINITE_NUMSEG] THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_LIFT_COMPONENT THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC LRG_LRIEMANN_SMOOTH THEN ASM_REWRITE_TAC[metric_field]]);;

let LRG_LSCALAR_SMOOTH = prove
 (`!U (G:real^N->real^N^N).
        metric_field U G ==> smooth_map_on U (\x. lift(lscalar G x))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LRG_LRIC2_FIELD) THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
          ==> smooth_map_on U
                (\x. lift(matrix_inv((G:real^N->real^N^N) x)$i$j))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`U:real^N->bool`; `\x. matrix_inv((G:real^N->real^N^N) x)`]
           LRG_SMOOTH_VECTORIZE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC LRG_SMOOTH_MATRIX_INV THEN
    RULE_ASSUM_TAC(REWRITE_RULE[metric_field]) THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `z:real^N`]
           LRG_METRIC_INVERTIBLE) THEN
    ASM_REWRITE_TAC[metric_field] THEN SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[lscalar] THEN
  MATCH_MP_TAC LRG_SMOOTH_LIFT_SUM_REAL THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  MATCH_MP_TAC LRG_SMOOTH_LIFT_SUM_REAL THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  MATCH_MP_TAC LRG_SMOOTH_LIFT_MUL_REAL THEN ASM_SIMP_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `\m. if m = 1 then basis i else basis j:real^N`) THEN
  REWRITE_TAC[lric2; ARITH]);;


(* ========================================================================= *)
(* lnabla commutes with the metric contraction of the first two slots of a   *)
(* tensor field (LRG_LNABLA_CONTRACT).                                       *)
(* ========================================================================= *)

let LRG_BASIS_DOT_MATRIX = prove
 (`!(A:real^N^N) i j.
        1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
        ==> basis i dot (A ** basis j) = A$i$j`,
  SIMP_TAC[DOT_BASIS; MATRIX_VECTOR_MUL_BASIS; column; LAMBDA_BETA]);;

let LRG_SUM3_ROTATE = prove
 (`!(f:num->num->num->real) n.
        sum(1..n) (\a. sum(1..n) (\b. sum(1..n) (\d. f a b d))) =
        sum(1..n) (\d. sum(1..n) (\b. sum(1..n) (\a. f a b d)))`,
  REPEAT GEN_TAC THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `sum(1..n) (\a. sum(1..n) (\d. sum(1..n)
                (\b. (f:num->num->num->real) a b d)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN
    BETA_TAC THEN
    MP_TAC(ISPECL [`1`; `n:num`; `1`; `n:num`;
                   `\b d. (f:num->num->num->real) a b d`] SUM_SWAP_NUMSEG) THEN
    REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `sum(1..n) (\d. sum(1..n) (\a. sum(1..n)
                (\b. (f:num->num->num->real) a b d)))` THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`1`; `n:num`; `1`; `n:num`;
                   `\a d. sum(1..n) (\b. (f:num->num->num->real) a b d)`]
           SUM_SWAP_NUMSEG) THEN
    REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `d:num` THEN STRIP_TAC THEN
  BETA_TAC THEN
  MP_TAC(ISPECL [`1`; `n:num`; `1`; `n:num`;
                 `\a b. (f:num->num->num->real) a b d`] SUM_SWAP_NUMSEG) THEN
  REWRITE_TAC[]);;

let LRG_CONS2_SLOT1 = prove
 (`!k U (tf:real^N->(num->real^N)->real) y X P u.
        ltensor_field (k + 2) U tf /\ y IN U
        ==> sum(1..dimindex(:N))
             (\q. X$q * tf y (\m. if m = 1 then basis q else if m = 2 then P
                                  else u(m - 2))) =
            tf y (\m. if m = 1 then X else if m = 2 then P else u(m - 2))`,
  REWRITE_TAC[ltensor_field] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `y:real^N`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL
   [`1`; `\m. if m = 1 then vec 0 else if m = 2 then (P:real^N)
              else (u:num->real^N)(m - 2)`] o CONJUNCT2) THEN
  REWRITE_TAC[ARITH_RULE `1 <= 1 /\ 1 <= k + 2`] THEN DISCH_TAC THEN
  MP_TAC(ISPECL
   [`(tf:real^N->(num->real^N)->real) y`; `1`;
    `\m. if m = 1 then vec 0 else if m = 2 then (P:real^N)
         else (u:num->real^N)(m - 2)`; `X:real^N`] LRG_SLOT_EXPAND) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!Z:real^N. (\j. if j = 1 then Z
                    else if j = 1 then vec 0 else if j = 2 then (P:real^N)
                    else (u:num->real^N)(j - 2)) =
               (\m. if m = 1 then Z else if m = 2 then P else u(m - 2))`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `j:num` THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[];
    DISCH_THEN(ACCEPT_TAC o SYM)]);;

let LRG_CONS2_SLOT2 = prove
 (`!k U (tf:real^N->(num->real^N)->real) y X P u.
        ltensor_field (k + 2) U tf /\ y IN U
        ==> sum(1..dimindex(:N))
             (\q. X$q * tf y (\m. if m = 1 then P else if m = 2 then basis q
                                  else u(m - 2))) =
            tf y (\m. if m = 1 then P else if m = 2 then X else u(m - 2))`,
  REWRITE_TAC[ltensor_field] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `y:real^N`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL
   [`2`; `\m. if m = 1 then (P:real^N) else if m = 2 then vec 0
              else (u:num->real^N)(m - 2)`] o CONJUNCT2) THEN
  REWRITE_TAC[ARITH_RULE `1 <= 2 /\ 2 <= k + 2`] THEN DISCH_TAC THEN
  MP_TAC(ISPECL
   [`(tf:real^N->(num->real^N)->real) y`; `2`;
    `\m. if m = 1 then (P:real^N) else if m = 2 then vec 0
         else (u:num->real^N)(m - 2)`; `X:real^N`] LRG_SLOT_EXPAND) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!Z:real^N. (\j. if j = 2 then Z
                    else if j = 1 then (P:real^N) else if j = 2 then vec 0
                    else (u:num->real^N)(j - 2)) =
               (\m. if m = 1 then P else if m = 2 then Z else u(m - 2))`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `j:num` THEN
    ASM_CASES_TAC `j = 1` THEN ASM_REWRITE_TAC[ARITH] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[];
    DISCH_THEN(ACCEPT_TAC o SYM)]);;

let LRG_GINV_MDERIV_GINV = prove
 (`!U (G:real^N->real^N^N) y e a b.
        metric_field U G /\ y IN U /\
        1 <= a /\ a <= dimindex(:N) /\ 1 <= b /\ b <= dimindex(:N)
        ==> (matrix_inv(G y) ** mderiv G y e ** matrix_inv(G y))$a$b =
            sum(1..dimindex(:N))
             (\c. matrix_inv(G y)$a$c * (christoffel G y e (basis c))$b) +
            sum(1..dimindex(:N))
             (\d. matrix_inv(G y)$d$b * (christoffel G y e (basis d))$a)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[LRG_MATRIX_MUL_COMPONENT] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `sum(1..dimindex(:N))
     (\c. sum(1..dimindex(:N))
       (\d. matrix_inv((G:real^N->real^N^N) y)$a$c *
            ((basis d dot (G y ** christoffel G y e (basis c))) *
             matrix_inv(G y)$d$b +
             (basis c dot (G y ** christoffel G y e (basis d))) *
             matrix_inv(G y)$d$b)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `c:num` THEN STRIP_TAC THEN
    BETA_TAC THEN ASM_SIMP_TAC[LRG_MATRIX_MUL_COMPONENT; GSYM SUM_LMUL] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `d:num` THEN STRIP_TAC THEN
    BETA_TAC THEN
    MP_TAC(ISPECL [`mderiv (G:real^N->real^N^N) y e`; `c:num`; `d:num`]
           LRG_BASIS_DOT_MATRIX) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`;
                   `basis c:real^N`; `e:real^N`; `basis d:real^N`]
           LRG_MDERIV_CHRISTOFFEL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ADD_LDISTRIB; SUM_ADD_NUMSEG] THEN BINOP_TAC THENL
   [MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `c:num` THEN STRIP_TAC THEN
    BETA_TAC THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`;
                   `christoffel (G:real^N->real^N^N) y e (basis c)`; `b:num`]
           LRG_COMPONENT_METRIC) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
    X_GEN_TAC `d:num` THEN STRIP_TAC THEN BETA_TAC THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`;
                   `d:num`; `b:num`] LRG_MATRIX_INV_SYM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC;
    MP_TAC(ISPECL
     [`1`; `dimindex(:N)`; `1`; `dimindex(:N)`;
      `\c d. matrix_inv((G:real^N->real^N^N) y)$a$c *
             (basis c dot (G y ** christoffel G y e (basis d))) *
             matrix_inv(G y)$d$b`] SUM_SWAP_NUMSEG) THEN
    REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `d:num` THEN STRIP_TAC THEN
    BETA_TAC THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`;
                   `christoffel (G:real^N->real^N^N) y e (basis d)`; `a:num`]
           LRG_COMPONENT_METRIC) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
    X_GEN_TAC `c:num` THEN STRIP_TAC THEN BETA_TAC THEN REAL_ARITH_TAC]);;

let LRG_CONTRACT_GAMMA = prove
 (`!k U (G:real^N->real^N^N) (tf:real^N->(num->real^N)->real) y e u.
        metric_field U G /\ ltensor_field (k + 2) U tf /\ y IN U
        ==> sum(1..dimindex(:N))
             (\a. sum(1..dimindex(:N))
               (\b. (matrix_inv(G y) ** mderiv G y e ** matrix_inv(G y))$a$b *
                    tf y (\m. if m = 1 then basis a else if m = 2 then basis b
                              else u(m - 2)))) =
            sum(1..dimindex(:N))
             (\a. sum(1..dimindex(:N))
               (\b. matrix_inv(G y)$a$b *
                    (tf y (\m. if m = 1 then christoffel G y e (basis a)
                               else if m = 2 then basis b else u(m - 2)) +
                     tf y (\m. if m = 1 then basis a
                               else if m = 2 then christoffel G y e (basis b)
                               else u(m - 2)))))`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `sum(1..dimindex(:N))
     (\a. sum(1..dimindex(:N))
       (\b. sum(1..dimindex(:N))
              (\c. matrix_inv((G:real^N->real^N^N) y)$a$c *
                   (christoffel G y e (basis c))$b) *
            (tf:real^N->(num->real^N)->real) y
              (\m. if m = 1 then basis a else if m = 2 then basis b
                   else u(m - 2)))) +
    sum(1..dimindex(:N))
     (\a. sum(1..dimindex(:N))
       (\b. sum(1..dimindex(:N))
              (\d. matrix_inv((G:real^N->real^N^N) y)$d$b *
                   (christoffel G y e (basis d))$a) *
            tf y (\m. if m = 1 then basis a else if m = 2 then basis b
                      else u(m - 2))))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM SUM_ADD_NUMSEG] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN
    BETA_TAC THEN REWRITE_TAC[GSYM SUM_ADD_NUMSEG] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `b:num` THEN STRIP_TAC THEN
    BETA_TAC THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`;
                   `e:real^N`; `a:num`; `b:num`] LRG_GINV_MDERIV_GINV) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ADD_LDISTRIB; SUM_ADD_NUMSEG] THEN
  MATCH_MP_TAC(REAL_ARITH `a = d /\ b = c ==> a + b = c + d`) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN
    BETA_TAC THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC
     `sum(1..dimindex(:N))
       (\c. matrix_inv((G:real^N->real^N^N) y)$a$c *
            sum(1..dimindex(:N))
             (\q. (christoffel G y e (basis c))$q *
                  (tf:real^N->(num->real^N)->real) y
                   (\m. if m = 1 then basis a else if m = 2 then basis q
                        else u(m - 2))))` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[GSYM SUM_RMUL; GSYM SUM_LMUL; GSYM REAL_MUL_ASSOC] THEN
      MP_TAC(ISPECL
       [`1`; `dimindex(:N)`; `1`; `dimindex(:N)`;
        `\b c. matrix_inv((G:real^N->real^N^N) y)$a$c *
               (christoffel G y e (basis c))$b *
               (tf:real^N->(num->real^N)->real) y
                (\m. if m = 1 then basis a else if m = 2 then basis b
                     else u(m - 2))`] SUM_SWAP_NUMSEG) THEN
      REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
      MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
      REAL_ARITH_TAC;
      MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `c:num` THEN STRIP_TAC THEN
      BETA_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC LRG_CONS2_SLOT2 THEN
      MAP_EVERY EXISTS_TAC [`k:num`; `U:real^N->bool`] THEN ASM_REWRITE_TAC[]];
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC
     `sum(1..dimindex(:N))
       (\d. sum(1..dimindex(:N))
         (\b. matrix_inv((G:real^N->real^N^N) y)$d$b *
              sum(1..dimindex(:N))
               (\a. (christoffel G y e (basis d))$a *
                    (tf:real^N->(num->real^N)->real) y
                     (\m. if m = 1 then basis a else if m = 2 then basis b
                          else u(m - 2)))))` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[GSYM SUM_RMUL; GSYM SUM_LMUL; GSYM REAL_MUL_ASSOC] THEN
      MP_TAC(ISPECL
       [`\a b d. matrix_inv((G:real^N->real^N^N) y)$d$b *
                 (christoffel G y e (basis d))$a *
                 (tf:real^N->(num->real^N)->real) y
                  (\m. if m = 1 then basis a else if m = 2 then basis b
                       else u(m - 2))`; `dimindex(:N)`] LRG_SUM3_ROTATE) THEN
      REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
      MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
      MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
      REAL_ARITH_TAC;
      MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `d:num` THEN STRIP_TAC THEN
      BETA_TAC THEN
      MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `b:num` THEN STRIP_TAC THEN
      BETA_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC LRG_CONS2_SLOT1 THEN
      MAP_EVERY EXISTS_TAC [`k:num`; `U:real^N->bool`] THEN ASM_REWRITE_TAC[]]]);;

let LRG_SUM_SPLIT2 = prove
 (`!(f:num->real) k. sum(1..k + 2) f = f 1 + f 2 + sum(1..k) (\i. f(i + 2))`,
  GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[ADD_CLAUSES; SUM_2; SUM_CLAUSES_NUMSEG; ARITH] THEN
    REAL_ARITH_TAC;
    ASM_REWRITE_TAC[ADD_CLAUSES; SUM_CLAUSES_NUMSEG;
                    ARITH_RULE `1 <= SUC n`] THEN
    REWRITE_TAC[ADD_CLAUSES] THEN REAL_ARITH_TAC]);;

let LRG_LNABLA_CONS2 = prove
 (`!k (G:real^N->real^N^N) (tf:real^N->(num->real^N)->real) y a b u.
        lnabla (k + 2) G tf y
          (\m. if m = 1 then a else if m = 2 then b else u(m - 2)) =
        drop(frechet_derivative
              (\z. lift(tf z (\m. if m = 1 then a else if m = 2 then b
                                  else u(m - 2)))) (at y) (u(k + 1))) -
        (tf y (\m. if m = 1 then christoffel G y (u(k + 1)) a
                   else if m = 2 then b else u(m - 2)) +
         tf y (\m. if m = 1 then a
                   else if m = 2 then christoffel G y (u(k + 1)) b
                   else u(m - 2)) +
         sum(1..k)
          (\i. tf y (\m. if m = 1 then a else if m = 2 then b
                         else if m - 2 = i then christoffel G y (u(k + 1)) (u i)
                         else u(m - 2))))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[lnabla; LRG_SUM_SPLIT2] THEN
  REWRITE_TAC[ARITH_RULE `~((k + 2) + 1 = 1) /\ ~((k + 2) + 1 = 2) /\
                          ((k + 2) + 1) - 2 = k + 1`] THEN
  AP_TERM_TAC THEN REWRITE_TAC[ARITH] THEN BINOP_TAC THENL
   [AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `j:num` THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  BINOP_TAC THENL
   [AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `j:num` THEN
    ASM_CASES_TAC `j = 1` THEN ASM_REWRITE_TAC[ARITH] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  BETA_TAC THEN
  REWRITE_TAC[ARITH_RULE `(i + 2 = 1 <=> F) /\ (i + 2 = 2 <=> i = 0) /\
                          (i + 2) - 2 = i`] THEN
  ASM_SIMP_TAC[ARITH_RULE `1 <= i ==> ~(i = 0)`] THEN
  AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `j:num` THEN
  ASM_CASES_TAC `j = 1` THEN ASM_REWRITE_TAC[] THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `j = 2` THEN ASM_REWRITE_TAC[] THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `j - 2 = i` THEN ASM_REWRITE_TAC[] THENL
   [SUBGOAL_THEN `j = i + 2` (fun th -> REWRITE_TAC[th]) THEN ASM_ARITH_TAC;
    SUBGOAL_THEN `~(j = i + 2)` (fun th -> REWRITE_TAC[th]) THEN ASM_ARITH_TAC]);;

let LRG_DCONTRACT = prove
 (`!U (G:real^N->real^N^N) (tf:real^N->(num->real^N)->real) y u e.
        metric_field U G /\ (!u. smooth_map_on U (\x. lift(tf x u))) /\ y IN U
        ==> frechet_derivative
              (\z. lift(sum(1..dimindex(:N))
                     (\a. sum(1..dimindex(:N))
                       (\b. matrix_inv(G z)$a$b *
                            tf z (\m. if m = 1 then basis a
                                      else if m = 2 then basis b
                                      else u(m - 2)))))) (at y) e =
            lift(sum(1..dimindex(:N))
                  (\a. sum(1..dimindex(:N))
                    (\b. matrix_inv(G y)$a$b *
                         drop(frechet_derivative
                               (\z. lift(tf z (\m. if m = 1 then basis a
                                                   else if m = 2 then basis b
                                                   else u(m - 2)))) (at y) e) -
                         (matrix_inv(G y) ** mderiv G y e ** matrix_inv(G y))$a$b *
                         tf y (\m. if m = 1 then basis a
                                   else if m = 2 then basis b else u(m - 2)))))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!a b. ((\z. lift(matrix_inv((G:real^N->real^N^N) z)$a$b *
                     (tf:real^N->(num->real^N)->real) z
                       (\m. if m = 1 then basis a else if m = 2 then basis b
                            else u(m - 2)))) has_derivative
           (\h. lift(matrix_inv(G y)$a$b *
                     drop(frechet_derivative
                           (\z. lift(tf z (\m. if m = 1 then basis a
                                               else if m = 2 then basis b
                                               else u(m - 2)))) (at y) h) -
                     (matrix_inv(G y) ** mderiv G y h ** matrix_inv(G y))$a$b *
                     tf y (\m. if m = 1 then basis a else if m = 2 then basis b
                               else u(m - 2))))) (at y)`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN
    MP_TAC(ISPECL
     [`\z. matrix_inv((G:real^N->real^N^N) z)$a$b`;
      `\h. --((matrix_inv((G:real^N->real^N^N) y) ** mderiv G y h **
               matrix_inv(G y))$a$b)`;
      `\z. lift((tf:real^N->(num->real^N)->real) z
                (\m. if m = 1 then basis a else if m = 2 then basis b
                     else u(m - 2)))`;
      `frechet_derivative
        (\z. lift((tf:real^N->(num->real^N)->real) z
                  (\m. if m = 1 then basis a else if m = 2 then basis b
                       else u(m - 2)))) (at y)`;
      `y:real^N`] HAS_DERIVATIVE_MUL_AT) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [REWRITE_TAC[o_DEF] THEN MATCH_MP_TAC LRG_HAS_DERIVATIVE_GINV_ENTRY THEN
        EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
        MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
        EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    MATCH_MP_TAC(MESON[]
     `(f:real^N->real^1) = g /\ (h:real^N->real^1) = k
      ==> (f has_derivative h) (at y) ==> (g has_derivative k) (at y)`) THEN
    REWRITE_TAC[FUN_EQ_THM; LIFT_CMUL; LIFT_SUB; LIFT_DROP] THEN
    REPEAT STRIP_TAC THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\z. lift(sum(1..dimindex(:N))
            (\a. sum(1..dimindex(:N))
              (\b. matrix_inv((G:real^N->real^N^N) z)$a$b *
                   (tf:real^N->(num->real^N)->real) z
                     (\m. if m = 1 then basis a else if m = 2 then basis b
                          else u(m - 2)))))) has_derivative
     (\h. lift(sum(1..dimindex(:N))
            (\a. sum(1..dimindex(:N))
              (\b. matrix_inv(G y)$a$b *
                   drop(frechet_derivative
                         (\z. lift(tf z (\m. if m = 1 then basis a
                                             else if m = 2 then basis b
                                             else u(m - 2)))) (at y) h) -
                   (matrix_inv(G y) ** mderiv G y h ** matrix_inv(G y))$a$b *
                   tf y (\m. if m = 1 then basis a else if m = 2 then basis b
                             else u(m - 2))))))) (at y)`
  MP_TAC THENL
   [REWRITE_TAC[LIFT_SUM; o_DEF] THEN
    MATCH_MP_TAC HAS_DERIVATIVE_VSUM THEN REWRITE_TAC[FINITE_NUMSEG] THEN
    X_GEN_TAC `a:num` THEN DISCH_TAC THEN
    MATCH_MP_TAC HAS_DERIVATIVE_VSUM THEN REWRITE_TAC[FINITE_NUMSEG] THEN
    X_GEN_TAC `b:num` THEN DISCH_TAC THEN ASM_REWRITE_TAC[];
    DISCH_THEN(fun th -> REWRITE_TAC[GSYM(MATCH_MP FRECHET_DERIVATIVE_AT th)])]);;

let LRG_LNABLA_CONTRACT = prove
 (`!k U (G:real^N->real^N^N) (tf:real^N->(num->real^N)->real) y u.
        metric_field U G /\ ltensor_field (k + 2) U tf /\
        (!u. smooth_map_on U (\x. lift(tf x u))) /\ y IN U
        ==> lnabla k G
              (\x u. sum(1..dimindex(:N))
                      (\a. sum(1..dimindex(:N))
                        (\b. matrix_inv(G x)$a$b *
                             tf x (\m. if m = 1 then basis a
                                       else if m = 2 then basis b
                                       else u(m - 2))))) y u =
            sum(1..dimindex(:N))
             (\a. sum(1..dimindex(:N))
               (\b. matrix_inv(G y)$a$b *
                    lnabla (k + 2) G tf y
                      (\m. if m = 1 then basis a else if m = 2 then basis b
                           else u(m - 2))))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LRG_LNABLA_CONS2] THEN
  REWRITE_TAC[lnabla] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`;
                 `tf:real^N->(num->real^N)->real`; `y:real^N`;
                 `u:num->real^N`; `(u:num->real^N)(k + 1)`] LRG_DCONTRACT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[LIFT_DROP; SUM_SUB_NUMSEG] THEN
  MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `tf:real^N->(num->real^N)->real`; `y:real^N`;
                 `(u:num->real^N)(k + 1)`; `u:num->real^N`]
         LRG_CONTRACT_GAMMA) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN
   `sum(1..k)
     (\i. sum(1..dimindex(:N))
       (\a. sum(1..dimindex(:N))
         (\b. matrix_inv((G:real^N->real^N^N) y)$a$b *
              (tf:real^N->(num->real^N)->real) y
               (\m. if m = 1 then basis a else if m = 2 then basis b
                    else if m - 2 = i
                         then christoffel G y ((u:num->real^N)(k + 1)) (u i)
                         else u(m - 2))))) =
    sum(1..dimindex(:N))
     (\a. sum(1..k)
       (\i. sum(1..dimindex(:N))
         (\b. matrix_inv(G y)$a$b *
              tf y (\m. if m = 1 then basis a else if m = 2 then basis b
                        else if m - 2 = i
                             then christoffel G y (u(k + 1)) (u i)
                             else u(m - 2)))))`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL
     [`1`; `k:num`; `1`; `dimindex(:N)`;
      `\i a. sum(1..dimindex(:N))
              (\b. matrix_inv((G:real^N->real^N^N) y)$a$b *
                   (tf:real^N->(num->real^N)->real) y
                    (\m. if m = 1 then basis a else if m = 2 then basis b
                         else if m - 2 = i
                              then christoffel G y ((u:num->real^N)(k + 1)) (u i)
                              else u(m - 2)))`] SUM_SWAP_NUMSEG) THEN
    REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!a. sum(1..k)
         (\i. sum(1..dimindex(:N))
           (\b. matrix_inv((G:real^N->real^N^N) y)$a$b *
                (tf:real^N->(num->real^N)->real) y
                 (\m. if m = 1 then basis a else if m = 2 then basis b
                      else if m - 2 = i
                           then christoffel G y ((u:num->real^N)(k + 1)) (u i)
                           else u(m - 2)))) =
        sum(1..dimindex(:N))
         (\b. matrix_inv(G y)$a$b *
              sum(1..k)
               (\i. tf y (\m. if m = 1 then basis a else if m = 2 then basis b
                              else if m - 2 = i
                                   then christoffel G y (u(k + 1)) (u i)
                                   else u(m - 2))))`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN REWRITE_TAC[GSYM SUM_LMUL] THEN
    MP_TAC(ISPECL
     [`1`; `k:num`; `1`; `dimindex(:N)`;
      `\i b. matrix_inv((G:real^N->real^N^N) y)$a$b *
             (tf:real^N->(num->real^N)->real) y
              (\m. if m = 1 then basis a else if m = 2 then basis b
                   else if m - 2 = i
                        then christoffel G y ((u:num->real^N)(k + 1)) (u i)
                        else u(m - 2))`] SUM_SWAP_NUMSEG) THEN
    REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_SUB_LDISTRIB; REAL_ADD_LDISTRIB; SUM_SUB_NUMSEG;
              SUM_ADD_NUMSEG] THEN
  REAL_ARITH_TAC);;


(* ========================================================================= *)
(* Contractions of the curvature tensors: Ricci from Rm, the differential of *)
(* the scalar curvature from nabla Ric, symmetries of nabla Ric and nabla    *)
(* Rm, and the twice contracted second Bianchi identity div Ric = dR / 2.    *)
(* ========================================================================= *)

let LRG_TUPLE_TAC =
  REWRITE_TAC[FUN_EQ_THM; swap] THEN X_GEN_TAC `m:num` THEN
  REWRITE_TAC[ARITH_RULE `m - 2 = 1 <=> m = 3`;
              ARITH_RULE `m - 2 = 2 <=> m = 4`;
              ARITH_RULE `m - 2 = 3 <=> m = 5`] THEN
  MAP_EVERY (fun n -> ASM_CASES_TAC (mk_eq(`m:num`, mk_small_numeral n)) THEN
                      ASM_REWRITE_TAC[ARITH]) [1;2;3;4;5];;

let LRG_LRM4_CONTRACT13 = prove
 (`!U (G:real^N->real^N^N) x p q.
        metric_field U G /\ x IN U
        ==> sum(1..dimindex(:N))
             (\a. sum(1..dimindex(:N))
               (\c. matrix_inv(G x)$a$c *
                    lrm4 G x (\m. if m = 1 then basis a else if m = 2 then p
                                  else if m = 3 then basis c else q))) =
            lricci G x p q`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[lrm4; lricci; ARITH] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN
  BETA_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC LRG_COMPONENT_METRIC THEN
  EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[]);;

let LRG_DSCALAR_CONTRACT = prove
 (`!U (G:real^N->real^N^N) x u.
        metric_field U G /\ x IN U
        ==> sum(1..dimindex(:N))
             (\a. sum(1..dimindex(:N))
               (\b. matrix_inv(G x)$a$b *
                    lnabla 2 G (lric2 G) x
                      (\m. if m = 1 then basis a else if m = 2 then basis b
                           else u(m - 2)))) =
            drop(frechet_derivative (\w. lift(lscalar G w)) (at x) (u 1))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`0`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `lric2 (G:real^N->real^N^N)`; `x:real^N`; `u:num->real^N`]
         LRG_LNABLA_CONTRACT) THEN
  REWRITE_TAC[ADD_CLAUSES] THEN ASM_SIMP_TAC[LRG_LRIC2_FIELD] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[lnabla; lric2; ARITH; SUM_CLAUSES_NUMSEG; REAL_SUB_RZERO] THEN
  REWRITE_TAC[GSYM lscalar]);;

let LRG_N2_SYM = prove
 (`!U (G:real^N->real^N^N) x u.
        metric_field U G /\ x IN U
        ==> lnabla 2 G (lric2 G) x u =
            lnabla 2 G (lric2 G) x (\m. u(swap(1,2) m))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`2`; `G:real^N->real^N^N`; `lric2 (G:real^N->real^N^N)`;
                 `swap(1,2)`; `x:real^N`; `u:num->real^N`]
         LRG_LNABLA_PERMUTE) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC PERMUTES_SWAP THEN REWRITE_TAC[IN_NUMSEG] THEN ARITH_TAC;
    DISCH_THEN(SUBST1_TAC o SYM)] THEN
  MATCH_MP_TAC LRG_LNABLA_LOCAL THEN EXISTS_TAC `U:real^N->bool` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[lric2; swap; ARITH] THEN
  MATCH_MP_TAC LRICCI_SYM THEN EXISTS_TAC `U:real^N->bool` THEN
  ASM_REWRITE_TAC[]);;

let LRG_NRM_ANTI34 = prove
 (`!U (G:real^N->real^N^N) x u.
        metric_field U G /\ x IN U
        ==> lnabla 4 G (lrm4 G) x (\m. u(swap(3,4) m)) =
            --(lnabla 4 G (lrm4 G) x u)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`4`; `G:real^N->real^N^N`; `lrm4 (G:real^N->real^N^N)`;
                 `swap(3,4)`; `x:real^N`; `u:num->real^N`]
         LRG_LNABLA_PERMUTE) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC PERMUTES_SWAP THEN REWRITE_TAC[IN_NUMSEG] THEN ARITH_TAC;
    DISCH_THEN(SUBST1_TAC o SYM)] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `lnabla 4 G (\x u. --(&1) * lrm4 (G:real^N->real^N^N) x u) x u` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LRG_LNABLA_LOCAL THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[lrm4; swap; ARITH] THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `z:real^N`;
                   `(u:num->real^N) 1`; `(u:num->real^N) 2`;
                   `(u:num->real^N) 3`; `(u:num->real^N) 4`]
           LRIEMANN_METRIC_ANTISYM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`4`; `G:real^N->real^N^N`; `lrm4 (G:real^N->real^N^N)`;
                 `--(&1)`; `x:real^N`; `u:num->real^N`] LRG_LNABLA_CMUL) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `U:real^N->bool` THEN
    ASM_SIMP_TAC[LRM4_TENSOR_FIELD] THEN ASM_MESON_TAC[metric_field];
    DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC]);;

let LRG_NRM_CONTRACT13 = prove
 (`!U (G:real^N->real^N^N) x p q r.
        metric_field U G /\ x IN U
        ==> sum(1..dimindex(:N))
             (\a. sum(1..dimindex(:N))
               (\c. matrix_inv(G x)$a$c *
                    lnabla 4 G (lrm4 G) x
                      (\m. if m = 1 then basis a else if m = 2 then p
                           else if m = 3 then basis c else if m = 4 then q
                           else r))) =
            lnabla 2 G (lric2 G) x
              (\m. if m = 1 then p else if m = 2 then q else r)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  SUBGOAL_THEN `swap(2,3) permutes 1..4` ASSUME_TAC THENL
   [MATCH_MP_TAC PERMUTES_SWAP THEN REWRITE_TAC[IN_NUMSEG] THEN ARITH_TAC;
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LRM4_TENSOR_FIELD) THEN
  MP_TAC(BETA_RULE(ISPECL
   [`2`; `U:real^N->bool`; `G:real^N->real^N^N`;
    `\x u. lrm4 (G:real^N->real^N^N) x (\m. u(swap(2,3) m))`; `x:real^N`;
    `\m. if m = 1 then (p:real^N) else if m = 2 then q else r`]
   LRG_LNABLA_CONTRACT)) THEN
  REWRITE_TAC[ARITH] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC LRG_TENSOR_FIELD_PERMUTE THEN ASM_REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
  MATCH_MP_TAC(MESON[] `(a:real) = c /\ (b:real) = d ==> a = b ==> d = c`) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LRG_LNABLA_LOCAL THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC[lrm4; lric2; swap; ARITH] THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `z:real^N`;
                   `(u:num->real^N) 1`; `(u:num->real^N) 2`]
           LRG_LRM4_CONTRACT13) THEN
    ASM_REWRITE_TAC[lrm4; ARITH];
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN
    BETA_TAC THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `c:num` THEN
    STRIP_TAC THEN BETA_TAC THEN AP_TERM_TAC THEN
    MP_TAC(ISPECL [`4`; `G:real^N->real^N^N`; `lrm4 (G:real^N->real^N^N)`;
                   `swap(2,3)`; `x:real^N`;
                   `\m. if m = 1 then basis a else if m = 2 then basis c
                        else if m - 2 = 1 then (p:real^N)
                        else if m - 2 = 2 then q else r`]
           LRG_LNABLA_PERMUTE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    AP_TERM_TAC THEN LRG_TUPLE_TAC]);;

let LRG_SUM4_SWAP = prove
 (`!(f:num->num->num->num->real) n.
        sum(1..n) (\b. sum(1..n) (\d. sum(1..n) (\a. sum(1..n)
          (\c. f a b c d)))) =
        sum(1..n) (\a. sum(1..n) (\c. sum(1..n) (\b. sum(1..n)
          (\d. f a b c d))))`,
  REPEAT GEN_TAC THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `sum(1..n) (\b. sum(1..n) (\a. sum(1..n) (\c. sum(1..n)
                (\d. (f:num->num->num->num->real) a b c d))))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `b:num` THEN STRIP_TAC THEN
    BETA_TAC THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `sum(1..n) (\a. sum(1..n) (\d. sum(1..n)
                  (\c. (f:num->num->num->num->real) a b c d)))` THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`1`; `n:num`; `1`; `n:num`;
                     `\d a. sum(1..n) (\c. (f:num->num->num->num->real) a b c d)`]
             SUM_SWAP_NUMSEG) THEN REWRITE_TAC[];
      MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN
      BETA_TAC THEN
      MP_TAC(ISPECL [`1`; `n:num`; `1`; `n:num`;
                     `\d c. (f:num->num->num->num->real) a b c d`]
             SUM_SWAP_NUMSEG) THEN REWRITE_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `sum(1..n) (\a. sum(1..n) (\b. sum(1..n) (\c. sum(1..n)
                (\d. (f:num->num->num->num->real) a b c d))))` THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`1`; `n:num`; `1`; `n:num`;
                   `\b a. sum(1..n) (\c. sum(1..n)
                            (\d. (f:num->num->num->num->real) a b c d))`]
           SUM_SWAP_NUMSEG) THEN REWRITE_TAC[];
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN
    BETA_TAC THEN
    MP_TAC(ISPECL [`1`; `n:num`; `1`; `n:num`;
                   `\b c. sum(1..n) (\d. (f:num->num->num->num->real) a b c d)`]
           SUM_SWAP_NUMSEG) THEN REWRITE_TAC[]]);;

let LRG_DOUBLE_CONTRACT_SWAP = prove
 (`!(A:num->num->real) (B:num->num->real) (X:num->num->num->num->real) n.
        sum(1..n) (\b. sum(1..n) (\d. A b d *
          sum(1..n) (\a. sum(1..n) (\c. B a c * X a b c d)))) =
        sum(1..n) (\a. sum(1..n) (\c. B a c *
          sum(1..n) (\b. sum(1..n) (\d. A b d * X a b c d))))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM SUM_LMUL] THEN
  MP_TAC(ISPECL [`\a b c d. (A:num->num->real) b d *
                            (B:num->num->real) a c *
                            (X:num->num->num->num->real) a b c d`;
                 `n:num`] LRG_SUM4_SWAP) THEN
  REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REPEAT(MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN BETA_TAC) THEN
  REAL_ARITH_TAC);;

let LRG_CONTRACTED_BIANCHI = prove
 (`!U (G:real^N->real^N^N) x e.
        metric_field U G /\ x IN U
        ==> sum(1..dimindex(:N))
             (\a. sum(1..dimindex(:N))
               (\c. matrix_inv(G x)$a$c *
                    lnabla 2 G (lric2 G) x
                      (\m. if m = 1 then basis a else if m = 2 then e
                           else basis c))) =
            inv(&2) * drop(frechet_derivative (\w. lift(lscalar G w)) (at x) e)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `sum(1..dimindex(:N))
     (\b. sum(1..dimindex(:N))
       (\d. matrix_inv((G:real^N->real^N^N) x)$b$d *
            sum(1..dimindex(:N))
             (\a. sum(1..dimindex(:N))
               (\c. matrix_inv(G x)$a$c *
                    lnabla 4 G (lrm4 G) x
                     (\m. if m = 1 then basis a else if m = 2 then basis b
                          else if m = 3 then basis c else if m = 4 then basis d
                          else e))))) =
    drop(frechet_derivative (\w. lift(lscalar G w)) (at x) e)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC
     `sum(1..dimindex(:N))
       (\b. sum(1..dimindex(:N))
         (\d. matrix_inv((G:real^N->real^N^N) x)$b$d *
              lnabla 2 G (lric2 G) x
                (\m. if m = 1 then basis b else if m = 2 then basis d
                     else (\m:num. e) (m - 2))))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `b:num` THEN STRIP_TAC THEN
      BETA_TAC THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `d:num` THEN
      STRIP_TAC THEN BETA_TAC THEN AP_TERM_TAC THEN
      MATCH_MP_TAC LRG_NRM_CONTRACT13 THEN EXISTS_TAC `U:real^N->bool` THEN
      ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `x:real^N`;
                     `\m:num. (e:real^N)`] LRG_DSCALAR_CONTRACT) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum(1..dimindex(:N))
     (\b. sum(1..dimindex(:N))
       (\d. matrix_inv((G:real^N->real^N^N) x)$b$d *
            sum(1..dimindex(:N))
             (\a. sum(1..dimindex(:N))
               (\c. matrix_inv(G x)$a$c *
                    lnabla 4 G (lrm4 G) x
                     (\m. if m = 1 then basis a else if m = 2 then basis b
                          else if m = 3 then e else if m = 4 then basis c
                          else basis d))))) =
    --(sum(1..dimindex(:N))
        (\a. sum(1..dimindex(:N))
          (\c. matrix_inv(G x)$a$c *
               lnabla 2 G (lric2 G) x
                 (\m. if m = 1 then basis a else if m = 2 then e
                      else basis c))))`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM SUM_NEG] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `b:num` THEN STRIP_TAC THEN
    BETA_TAC THEN REWRITE_TAC[GSYM SUM_NEG] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `d:num` THEN STRIP_TAC THEN
    BETA_TAC THEN REWRITE_TAC[GSYM REAL_MUL_RNEG] THEN AP_TERM_TAC THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `x:real^N`;
                   `basis b:real^N`; `e:real^N`; `basis d:real^N`]
           LRG_NRM_CONTRACT13) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[GSYM SUM_NEG] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN
    BETA_TAC THEN REWRITE_TAC[GSYM SUM_NEG] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `c:num` THEN STRIP_TAC THEN
    BETA_TAC THEN REWRITE_TAC[GSYM REAL_MUL_RNEG] THEN AP_TERM_TAC THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `x:real^N`;
                   `\m. if m = 1 then basis a else if m = 2 then basis b
                        else if m = 3 then basis c else if m = 4 then (e:real^N)
                        else basis d`] LRG_NRM_ANTI34) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `x = y ==> x = --z ==> y = --z`) THEN
    AP_TERM_TAC THEN LRG_TUPLE_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum(1..dimindex(:N))
     (\b. sum(1..dimindex(:N))
       (\d. matrix_inv((G:real^N->real^N^N) x)$b$d *
            sum(1..dimindex(:N))
             (\a. sum(1..dimindex(:N))
               (\c. matrix_inv(G x)$a$c *
                    lnabla 4 G (lrm4 G) x
                     (\m. if m = 1 then basis a else if m = 2 then basis b
                          else if m = 3 then basis d else if m = 4 then e
                          else basis c))))) =
    --(sum(1..dimindex(:N))
        (\a. sum(1..dimindex(:N))
          (\c. matrix_inv(G x)$a$c *
               lnabla 2 G (lric2 G) x
                 (\m. if m = 1 then basis a else if m = 2 then e
                      else basis c))))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC
     `sum(1..dimindex(:N))
       (\b. sum(1..dimindex(:N))
         (\d. matrix_inv((G:real^N->real^N^N) x)$b$d *
              sum(1..dimindex(:N))
               (\a. sum(1..dimindex(:N))
                 (\c. matrix_inv(G x)$a$c *
                      --(lnabla 4 G (lrm4 G) x
                          (\m. if m = 1 then basis d else if m = 2 then e
                               else if m = 3 then basis b
                               else if m = 4 then basis a else basis c))))))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `b:num` THEN STRIP_TAC THEN
      BETA_TAC THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `d:num` THEN
      STRIP_TAC THEN BETA_TAC THEN AP_TERM_TAC THEN
      MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN
      BETA_TAC THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `c:num` THEN
      STRIP_TAC THEN BETA_TAC THEN AP_TERM_TAC THEN
      MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `x:real^N`;
                     `basis a:real^N`; `basis b:real^N`; `basis d:real^N`;
                     `e:real^N`; `basis c:real^N`] LRG_LNABLA_LRM4_PAIR) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `x:real^N`;
                     `\m. if m = 1 then basis d else if m = 2 then (e:real^N)
                          else if m = 3 then basis b else if m = 4 then basis a
                          else basis c`] LRG_NRM_ANTI34) THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(REAL_ARITH `x = y ==> x = --z ==> y = --z`) THEN
      AP_TERM_TAC THEN LRG_TUPLE_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[REAL_MUL_RNEG; SUM_NEG] THEN AP_TERM_TAC THEN
    MP_TAC(ISPECL
     [`\b d. matrix_inv((G:real^N->real^N^N) x)$b$d`;
      `\a c. matrix_inv((G:real^N->real^N^N) x)$a$c`;
      `\a b c d. lnabla 4 (G:real^N->real^N^N) (lrm4 G) x
                  (\m. if m = 1 then basis d else if m = 2 then (e:real^N)
                       else if m = 3 then basis b else if m = 4 then basis a
                       else basis c)`;
      `dimindex(:N)`] LRG_DOUBLE_CONTRACT_SWAP) THEN
    REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN
    BETA_TAC THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `c:num` THEN
    STRIP_TAC THEN BETA_TAC THEN AP_TERM_TAC THEN
    MP_TAC(ISPECL
     [`1`; `dimindex(:N)`; `1`; `dimindex(:N)`;
      `\b d. matrix_inv((G:real^N->real^N^N) x)$b$d *
             lnabla 4 G (lrm4 G) x
              (\m. if m = 1 then basis d else if m = 2 then (e:real^N)
                   else if m = 3 then basis b else if m = 4 then basis a
                   else basis c)`] SUM_SWAP_NUMSEG) THEN
    REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC
     `lnabla 2 (G:real^N->real^N^N) (lric2 G) x
       (\m. if m = 1 then (e:real^N) else if m = 2 then basis a
            else basis c)` THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `x:real^N`;
                     `e:real^N`; `basis a:real^N`; `basis c:real^N`]
             LRG_NRM_CONTRACT13) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `d:num` THEN STRIP_TAC THEN
      BETA_TAC THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `b:num` THEN
      STRIP_TAC THEN BETA_TAC THEN
      MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `x:real^N`;
                     `b:num`; `d:num`] LRG_MATRIX_INV_SYM) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REFL_TAC;
      MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `x:real^N`;
                     `\m. if m = 1 then (e:real^N) else if m = 2 then basis a
                          else basis c`] LRG_N2_SYM) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      AP_TERM_TAC THEN LRG_TUPLE_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `x:real^N`]
         LRM4_BIANCHI2) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `sum(1..dimindex(:N))
     (\b. sum(1..dimindex(:N))
       (\d. matrix_inv((G:real^N->real^N^N) x)$b$d *
            sum(1..dimindex(:N))
             (\a. sum(1..dimindex(:N))
               (\c. matrix_inv(G x)$a$c *
                    (lnabla 4 G (lrm4 G) x
                      (\m. if m = 1 then basis a else if m = 2 then basis b
                           else if m = 3 then basis c else if m = 4 then basis d
                           else e) +
                     lnabla 4 G (lrm4 G) x
                      (\m. if m = 1 then basis a else if m = 2 then basis b
                           else if m = 3 then basis d else if m = 4 then e
                           else basis c) +
                     lnabla 4 G (lrm4 G) x
                      (\m. if m = 1 then basis a else if m = 2 then basis b
                           else if m = 3 then e else if m = 4 then basis c
                           else basis d)))))) = &0`
  MP_TAC THENL
   [ASM_REWRITE_TAC[REAL_MUL_RZERO; SUM_0]; ALL_TAC] THEN
  REWRITE_TAC[REAL_ADD_LDISTRIB; SUM_ADD_NUMSEG] THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;


(* ========================================================================= *)
(* Traces of the second covariant derivative of Ricci:                       *)
(* g^pq g^kl nabla_k nabla_l R_pq = Delta R and                              *)
(* g^pq g^kl nabla_k nabla_p R_ql = Delta R / 2.                             *)
(* ========================================================================= *)

let LRG_LNABLA_AGREE = prove
 (`!k U (G:real^N->real^N^N) (tf:real^N->(num->real^N)->real) x u u'.
        open U /\ x IN U /\ ltensor_field k U tf /\
        (!m. 1 <= m /\ m <= k + 1 ==> u m = u' m)
        ==> lnabla k G tf x u = lnabla k G tf x u'`,
  REWRITE_TAC[ltensor_field] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[lnabla] THEN
  SUBGOAL_THEN `(u:num->real^N)(k + 1) = u'(k + 1)` SUBST1_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
  BINOP_TAC THENL
   [AP_TERM_TAC THEN AP_THM_TAC THEN
    MATCH_MP_TAC LRG_FRECHET_DERIVATIVE_EQ_OPEN THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN REWRITE_TAC[] THEN AP_TERM_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `z:real^N`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN
    X_GEN_TAC `m:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `(u:num->real^N) i = u' i /\ u m = u' m`
      (fun th -> REWRITE_TAC[th]) THEN
    CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]);;

let LRG_N2_FIELD = prove
 (`!U (G:real^N->real^N^N).
        metric_field U G
        ==> ltensor_field 3 U (lnabla 2 G (lric2 G)) /\
            (!u. smooth_map_on U (\x. lift(lnabla 2 G (lric2 G) x u)))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`2`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `lric2 (G:real^N->real^N^N)`] LNABLA_TENSOR_FIELD) THEN
  REWRITE_TAC[ARITH] THEN ASM_SIMP_TAC[LRG_LRIC2_FIELD]);;

let LRG_N3_TRACE12 = prove
 (`!U (G:real^N->real^N^N) y.
        metric_field U G /\ y IN U
        ==> sum(1..dimindex(:N))
             (\k. sum(1..dimindex(:N))
               (\l. matrix_inv(G y)$k$l *
                    sum(1..dimindex(:N))
                     (\p. sum(1..dimindex(:N))
                       (\q. matrix_inv(G y)$p$q *
                            lnabla 3 G (lnabla 2 G (lric2 G)) y
                              (\m. if m = 1 then basis p else if m = 2 then basis q
                                   else if m = 3 then basis l else basis k))))) =
            llap G (lscalar G) y`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LRG_N2_FIELD) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`;
                 `lscalar (G:real^N->real^N^N)`; `y:real^N`] LRG_LLAP_LNABLA) THEN
  ASM_SIMP_TAC[LRG_LSCALAR_SMOOTH] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
  BETA_TAC THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `l:num` THEN
  STRIP_TAC THEN BETA_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `lnabla 1 (G:real^N->real^N^N)
     (\x u. sum(1..dimindex(:N))
             (\a. sum(1..dimindex(:N))
               (\b. matrix_inv(G x)$a$b *
                    lnabla 2 G (lric2 G) x
                      (\m. if m = 1 then basis a else if m = 2 then basis b
                           else u(m - 2))))) y
     (\m. if m = 1 then basis l else basis k)` THEN
  CONJ_TAC THENL
   [MP_TAC(BETA_RULE(ISPECL
     [`1`; `U:real^N->bool`; `G:real^N->real^N^N`;
      `lnabla 2 (G:real^N->real^N^N) (lric2 G)`; `y:real^N`;
      `\m. if m = 1 then basis l else basis k:real^N`] LRG_LNABLA_CONTRACT)) THEN
    REWRITE_TAC[ARITH] THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `p:num` THEN STRIP_TAC THEN
    BETA_TAC THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `q:num` THEN
    STRIP_TAC THEN BETA_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    LRG_TUPLE_TAC;
    MATCH_MP_TAC LRG_LNABLA_LOCAL THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC LRG_DSCALAR_CONTRACT THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[]]);;

let LRG_N3_TRACE13 = prove
 (`!U (G:real^N->real^N^N) y.
        metric_field U G /\ y IN U
        ==> sum(1..dimindex(:N))
             (\k. sum(1..dimindex(:N))
               (\l. matrix_inv(G y)$k$l *
                    sum(1..dimindex(:N))
                     (\p. sum(1..dimindex(:N))
                       (\q. matrix_inv(G y)$p$q *
                            lnabla 3 G (lnabla 2 G (lric2 G)) y
                              (\m. if m = 1 then basis q else if m = 2 then basis l
                                   else if m = 3 then basis p else basis k))))) =
            inv(&2) * llap G (lscalar G) y`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LRG_N2_FIELD) THEN
  SUBGOAL_THEN `swap(2,3) permutes 1..3` ASSUME_TAC THENL
   [MATCH_MP_TAC PERMUTES_SWAP THEN REWRITE_TAC[IN_NUMSEG] THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`;
                 `lscalar (G:real^N->real^N^N)`; `y:real^N`] LRG_LLAP_LNABLA) THEN
  ASM_SIMP_TAC[LRG_LSCALAR_SMOOTH] THEN DISCH_THEN SUBST1_TAC THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM SUM_LMUL] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
  BETA_TAC THEN GEN_REWRITE_TAC RAND_CONV [GSYM SUM_LMUL] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `l:num` THEN
  STRIP_TAC THEN BETA_TAC THEN
  REWRITE_TAC[REAL_ARITH `inv(&2) * a * b = a * inv(&2) * b`] THEN
  AP_TERM_TAC THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `sum(1..dimindex(:N))
     (\a. sum(1..dimindex(:N))
       (\b. matrix_inv((G:real^N->real^N^N) y)$a$b *
            lnabla 3 G (\x u. lnabla 2 G (lric2 G) x (\m. u(swap(2,3) m))) y
              (\m. if m = 1 then basis a else if m = 2 then basis b
                   else if m - 2 = 1 then basis l else basis k)))` THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL
     [`1`; `dimindex(:N)`; `1`; `dimindex(:N)`;
      `\p q. matrix_inv((G:real^N->real^N^N) y)$p$q *
             lnabla 3 G (lnabla 2 G (lric2 G)) y
               (\m. if m = 1 then basis q else if m = 2 then basis l
                    else if m = 3 then basis p else basis k)`]
     SUM_SWAP_NUMSEG) THEN
    REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN
    BETA_TAC THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `b:num` THEN
    STRIP_TAC THEN BETA_TAC THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`;
                   `b:num`; `a:num`] LRG_MATRIX_INV_SYM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN
    MP_TAC(ISPECL [`3`; `G:real^N->real^N^N`;
                   `lnabla 2 (G:real^N->real^N^N) (lric2 G)`; `swap(2,3)`;
                   `y:real^N`;
                   `\m. if m = 1 then basis a else if m = 2 then basis b
                        else if m - 2 = 1 then basis l else basis k:real^N`]
           LRG_LNABLA_PERMUTE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    AP_TERM_TAC THEN LRG_TUPLE_TAC;
    ALL_TAC] THEN
  MP_TAC(BETA_RULE(ISPECL
   [`1`; `U:real^N->bool`; `G:real^N->real^N^N`;
    `\x u. lnabla 2 (G:real^N->real^N^N) (lric2 G) x (\m. u(swap(2,3) m))`;
    `y:real^N`; `\m. if m = 1 then basis l else basis k:real^N`]
   LRG_LNABLA_CONTRACT)) THEN
  REWRITE_TAC[ARITH] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LRG_TENSOR_FIELD_PERMUTE THEN
    ASM_REWRITE_TAC[ETA_AX];
    DISCH_THEN(SUBST1_TAC o SYM)] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `lnabla 1 (G:real^N->real^N^N)
     (\z u. inv(&2) * drop(frechet_derivative (\w. lift(lscalar G w)) (at z)
                                              (u 1))) y
     (\m. if m = 1 then basis l else basis k)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LRG_LNABLA_LOCAL THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `z:real^N` THEN X_GEN_TAC `u:num->real^N` THEN
    DISCH_TAC THEN BETA_TAC THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `z:real^N`;
                   `(u:num->real^N) 1`] LRG_CONTRACTED_BIANCHI) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN
    BETA_TAC THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `c:num` THEN
    STRIP_TAC THEN BETA_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC LRG_LNABLA_AGREE THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_SIMP_TAC[LRG_LRIC2_FIELD; ARITH] THEN
    REWRITE_TAC[ARITH_RULE `1 <= m /\ m <= 3 <=> m = 1 \/ m = 2 \/ m = 3`] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[swap; ARITH];
    MATCH_MP_TAC LRG_LNABLA_CMUL THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[LIFT_DROP] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_FRECHET_DERIVATIVE THEN
    ASM_SIMP_TAC[LRG_LSCALAR_SMOOTH]]);;

let LRG_N3_SYM = prove
 (`!U (G:real^N->real^N^N) y u.
        metric_field U G /\ y IN U
        ==> lnabla 3 G (lnabla 2 G (lric2 G)) y u =
            lnabla 3 G (lnabla 2 G (lric2 G)) y (\m. u(swap(1,2) m))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`3`; `G:real^N->real^N^N`;
                 `lnabla 2 (G:real^N->real^N^N) (lric2 G)`;
                 `swap(1,2)`; `y:real^N`; `u:num->real^N`]
         LRG_LNABLA_PERMUTE) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC PERMUTES_SWAP THEN REWRITE_TAC[IN_NUMSEG] THEN ARITH_TAC;
    DISCH_THEN(SUBST1_TAC o SYM)] THEN
  MATCH_MP_TAC LRG_LNABLA_LOCAL THEN EXISTS_TAC `U:real^N->bool` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LRG_N2_SYM THEN
  EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[]);;

let LRG_PALATINI_TRACE = prove
 (`!U (G:real^N->real^N^N) y.
        metric_field U G /\ y IN U
        ==> sum(1..dimindex(:N))
     (\p. sum(1..dimindex(:N))
       (\q. matrix_inv((G:real^N->real^N^N) y)$p$q *
            sum(1..dimindex(:N))
             (\k. sum(1..dimindex(:N))
               (\l. matrix_inv(G y)$k$l *
                (--(lnabla 3 G (lnabla 2 G (lric2 G)) y
                  (\m. if m = 1 then basis q else if m = 2 then basis l
                       else if m = 3 then basis p else basis k) +
                    lnabla 3 G (lnabla 2 G (lric2 G)) y
                  (\m. if m = 1 then basis p else if m = 2 then basis l
                       else if m = 3 then basis q else basis k) -
                    lnabla 3 G (lnabla 2 G (lric2 G)) y
                  (\m. if m = 1 then basis p else if m = 2 then basis q
                       else if m = 3 then basis l else basis k)) -
                 --(lnabla 3 G (lnabla 2 G (lric2 G)) y
                  (\m. if m = 1 then basis q else if m = 2 then basis l
                       else if m = 3 then basis k else basis p) +
                    lnabla 3 G (lnabla 2 G (lric2 G)) y
                  (\m. if m = 1 then basis k else if m = 2 then basis l
                       else if m = 3 then basis q else basis p) -
                    lnabla 3 G (lnabla 2 G (lric2 G)) y
                  (\m. if m = 1 then basis k else if m = 2 then basis q
                       else if m = 3 then basis l else basis p))))))) =
            llap G (lscalar G) y`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[REAL_ARITH `--(a + b - c) - --(d + e - f) =
                          ((((--a - b) + c) + d) + e) - f`] THEN
  REWRITE_TAC[REAL_ADD_LDISTRIB; REAL_SUB_LDISTRIB; REAL_MUL_RNEG;
              SUM_ADD_NUMSEG; SUM_SUB_NUMSEG; SUM_NEG] THEN
  SUBGOAL_THEN
   `sum(1..dimindex(:N))
     (\p. sum(1..dimindex(:N))
       (\q. matrix_inv((G:real^N->real^N^N) y)$p$q *
            sum(1..dimindex(:N))
             (\k. sum(1..dimindex(:N))
               (\l. matrix_inv(G y)$k$l *
                lnabla 3 G (lnabla 2 G (lric2 G)) y
                  (\m. if m = 1 then basis q else if m = 2 then basis l
                       else if m = 3 then basis p else basis k))))) =
    inv(&2) * llap G (lscalar G) y`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL
     [`\b d. matrix_inv((G:real^N->real^N^N) y)$b$d`;
      `\a c. matrix_inv((G:real^N->real^N^N) y)$a$c`;
      `\a b c d. lnabla 3 (G:real^N->real^N^N) (lnabla 2 G (lric2 G)) y
                  (\m. if m = 1 then basis d else if m = 2 then basis c
                       else if m = 3 then basis b else basis a)`;
      `dimindex(:N)`] LRG_DOUBLE_CONTRACT_SWAP) THEN
    REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC LRG_N3_TRACE13 THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum(1..dimindex(:N))
     (\p. sum(1..dimindex(:N))
       (\q. matrix_inv((G:real^N->real^N^N) y)$p$q *
            sum(1..dimindex(:N))
             (\k. sum(1..dimindex(:N))
               (\l. matrix_inv(G y)$k$l *
                lnabla 3 G (lnabla 2 G (lric2 G)) y
                  (\m. if m = 1 then basis p else if m = 2 then basis l
                       else if m = 3 then basis q else basis k))))) =
    inv(&2) * llap G (lscalar G) y`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    MP_TAC(ISPECL
     [`1`; `dimindex(:N)`; `1`; `dimindex(:N)`;
      `\p q. matrix_inv((G:real^N->real^N^N) y)$p$q *
             sum(1..dimindex(:N))
              (\k. sum(1..dimindex(:N))
                (\l. matrix_inv(G y)$k$l *
                     lnabla 3 G (lnabla 2 G (lric2 G)) y
                      (\m. if m = 1 then basis p else if m = 2 then basis l
                           else if m = 3 then basis q else basis k)))`]
     SUM_SWAP_NUMSEG) THEN
    REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `p:num` THEN STRIP_TAC THEN
    BETA_TAC THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `q:num` THEN
    STRIP_TAC THEN BETA_TAC THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`;
                   `q:num`; `p:num`] LRG_MATRIX_INV_SYM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REFL_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum(1..dimindex(:N))
     (\p. sum(1..dimindex(:N))
       (\q. matrix_inv((G:real^N->real^N^N) y)$p$q *
            sum(1..dimindex(:N))
             (\k. sum(1..dimindex(:N))
               (\l. matrix_inv(G y)$k$l *
                lnabla 3 G (lnabla 2 G (lric2 G)) y
                  (\m. if m = 1 then basis p else if m = 2 then basis q
                       else if m = 3 then basis l else basis k))))) =
    llap G (lscalar G) y`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL
     [`\b d. matrix_inv((G:real^N->real^N^N) y)$b$d`;
      `\a c. matrix_inv((G:real^N->real^N^N) y)$a$c`;
      `\a b c d. lnabla 3 (G:real^N->real^N^N) (lnabla 2 G (lric2 G)) y
                  (\m. if m = 1 then basis b else if m = 2 then basis d
                       else if m = 3 then basis c else basis a)`;
      `dimindex(:N)`] LRG_DOUBLE_CONTRACT_SWAP) THEN
    REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC LRG_N3_TRACE12 THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum(1..dimindex(:N))
     (\p. sum(1..dimindex(:N))
       (\q. matrix_inv((G:real^N->real^N^N) y)$p$q *
            sum(1..dimindex(:N))
             (\k. sum(1..dimindex(:N))
               (\l. matrix_inv(G y)$k$l *
                lnabla 3 G (lnabla 2 G (lric2 G)) y
                  (\m. if m = 1 then basis q else if m = 2 then basis l
                       else if m = 3 then basis k else basis p))))) =
    inv(&2) * llap G (lscalar G) y`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`]
           LRG_N3_TRACE13) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `p:num` THEN STRIP_TAC THEN
    BETA_TAC THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `q:num` THEN
    STRIP_TAC THEN BETA_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    BETA_TAC THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `l:num` THEN
    STRIP_TAC THEN BETA_TAC THEN AP_TERM_TAC THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`;
                   `\m. if m = 1 then basis q else if m = 2 then basis l
                        else if m = 3 then basis k else basis p:real^N`]
           LRG_N3_SYM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    AP_TERM_TAC THEN LRG_TUPLE_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum(1..dimindex(:N))
     (\p. sum(1..dimindex(:N))
       (\q. matrix_inv((G:real^N->real^N^N) y)$p$q *
            sum(1..dimindex(:N))
             (\k. sum(1..dimindex(:N))
               (\l. matrix_inv(G y)$k$l *
                lnabla 3 G (lnabla 2 G (lric2 G)) y
                  (\m. if m = 1 then basis k else if m = 2 then basis l
                       else if m = 3 then basis q else basis p))))) =
    llap G (lscalar G) y`
  ASSUME_TAC THENL
   [MATCH_MP_TAC LRG_N3_TRACE12 THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum(1..dimindex(:N))
     (\p. sum(1..dimindex(:N))
       (\q. matrix_inv((G:real^N->real^N^N) y)$p$q *
            sum(1..dimindex(:N))
             (\k. sum(1..dimindex(:N))
               (\l. matrix_inv(G y)$k$l *
                lnabla 3 G (lnabla 2 G (lric2 G)) y
                  (\m. if m = 1 then basis k else if m = 2 then basis q
                       else if m = 3 then basis l else basis p))))) =
    inv(&2) * llap G (lscalar G) y`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`]
           LRG_N3_TRACE13) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `p:num` THEN STRIP_TAC THEN
    BETA_TAC THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `q:num` THEN
    STRIP_TAC THEN BETA_TAC THEN AP_TERM_TAC THEN
    MP_TAC(ISPECL
     [`1`; `dimindex(:N)`; `1`; `dimindex(:N)`;
      `\k l. matrix_inv((G:real^N->real^N^N) y)$k$l *
             lnabla 3 G (lnabla 2 G (lric2 G)) y
              (\m. if m = 1 then basis k else if m = 2 then basis q
                   else if m = 3 then basis l else basis p)`]
     SUM_SWAP_NUMSEG) THEN
    REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `l:num` THEN STRIP_TAC THEN
    BETA_TAC THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `k:num` THEN
    STRIP_TAC THEN BETA_TAC THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`;
                   `k:num`; `l:num`] LRG_MATRIX_INV_SYM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REFL_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;


(* ========================================================================= *)
(* The time derivative of the Christoffel symbols as a field on U, its       *)
(* lowered form in terms of nabla Ric, and the time derivative of the        *)
(* curvature tensor lriemann along a flow.                                   *)
(* ========================================================================= *)

let LRG_FLOW_GAMMA_VDERIV = prove
 (`!U a b (G:real->real^N->real^N^N) t y u v.
        lricci_flow U a b G /\ a < t /\ t < b /\ y IN U
        ==> ((\s. christoffel (G (drop s)) y u v) has_vector_derivative
             frechet_derivative
              (\z. christoffel (G (drop(fstcart z))) (sndcart z) u v)
              (at (pastecart (lift t) y)) (pastecart (lift(&1)) (vec 0)))
            (at (lift t))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `a:real`; `b:real`;
                 `G:real->real^N->real^N^N`] LRG_FLOW_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL
   [`\z. christoffel ((G:real->real^N->real^N^N) (drop(fstcart z)))
                     (sndcart z) (u:real^N) v`; `t:real`; `y:real^N`]
   LRG_TIME_CURVE_VDERIV) THEN
  REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
  EXISTS_TAC `interval(lift a,lift b) PCROSS (U:real^N->bool)` THEN
  ASM_SIMP_TAC[LRG_FLOW_CHRISTOFFEL_SMOOTH]);;

let LRG_FLOW_DGAMMA = prove
 (`!U a b (G:real->real^N->real^N^N) t x u v k.
        lricci_flow U a b G /\ a < t /\ t < b /\ x IN U /\
        1 <= k /\ k <= dimindex(:N)
        ==> (G t x **
             frechet_derivative
              (\z. christoffel (G (drop(fstcart z))) (sndcart z) u v)
              (at (pastecart (lift t) x)) (pastecart (lift(&1)) (vec 0)))$k =
            --(lnabla 2 (G t) (lric2 (G t)) x
                 (\m. if m = 1 then v else if m = 2 then basis k else u) +
               lnabla 2 (G t) (lric2 (G t)) x
                 (\m. if m = 1 then u else if m = 2 then basis k else v) -
               lnabla 2 (G t) (lric2 (G t)) x
                 (\m. if m = 1 then u else if m = 2 then v else basis k))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `a:real`; `b:real`;
                 `G:real->real^N->real^N^N`; `t:real`; `x:real^N`;
                 `u:real^N`; `v:real^N`] LCHRISTOFFEL_EVOLUTION) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `frechet_derivative
     (\z. christoffel ((G:real->real^N->real^N^N) (drop(fstcart z))) (sndcart z)
                      u v)
     (at (pastecart (lift t) x)) (pastecart (lift(&1)) (vec 0)) = w`
  (fun th -> ASM_SIMP_TAC[th]) THEN
  MATCH_MP_TAC VECTOR_DERIVATIVE_UNIQUE_AT THEN
  EXISTS_TAC `\s. christoffel ((G:real->real^N->real^N^N) (drop s)) x u v` THEN
  EXISTS_TAC `lift t` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC LRG_FLOW_GAMMA_VDERIV THEN
  MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `a:real`; `b:real`] THEN
  ASM_REWRITE_TAC[]);;

let LRG_TUPLE3_SLOT2 = prove
 (`!U (tf:real^N->(num->real^N)->real) x c p r.
        ltensor_field 3 U tf /\ x IN U
        ==> sum(1..dimindex(:N))
             (\k. c$k * tf x (\m. if m = 1 then p else if m = 2 then basis k
                                  else r)) =
            tf x (\m. if m = 1 then p else if m = 2 then c else r)`,
  REWRITE_TAC[ltensor_field] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL
   [`2`; `\m. if m = 1 then (p:real^N) else if m = 2 then vec 0 else r`]
   o CONJUNCT2) THEN
  REWRITE_TAC[ARITH] THEN DISCH_TAC THEN
  MP_TAC(ISPECL
   [`(tf:real^N->(num->real^N)->real) x`; `2`;
    `\m. if m = 1 then (p:real^N) else if m = 2 then vec 0 else r`;
    `c:real^N`] LRG_SLOT_EXPAND) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!Z:real^N. (\j. if j = 2 then Z
                    else if j = 1 then (p:real^N) else if j = 2 then vec 0
                    else r) =
               (\m. if m = 1 then p else if m = 2 then Z else r)`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `j:num` THEN
    ASM_CASES_TAC `j = 1` THEN ASM_REWRITE_TAC[ARITH] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[];
    DISCH_THEN(ACCEPT_TAC o SYM)]);;

let LRG_TUPLE3_SLOT3 = prove
 (`!U (tf:real^N->(num->real^N)->real) x c p q.
        ltensor_field 3 U tf /\ x IN U
        ==> sum(1..dimindex(:N))
             (\k. c$k * tf x (\m. if m = 1 then p else if m = 2 then q
                                  else basis k)) =
            tf x (\m. if m = 1 then p else if m = 2 then q else c)`,
  REWRITE_TAC[ltensor_field] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "agree") (LABEL_TAC "lin")) THEN
  SUBGOAL_THEN
   `!Z:real^N. (tf:real^N->(num->real^N)->real) x
                 (\m. if m = 1 then p else if m = 2 then q else Z) =
               tf x (\j. if j = 3 then Z
                         else if j = 1 then p else if j = 2 then q else vec 0)`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN USE_THEN "agree" MATCH_MP_TAC THEN
    X_GEN_TAC `m:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `m = 1 \/ m = 2 \/ m = 3` STRIP_ASSUME_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`1 <= (m:num)`; `(m:num) <= 3`] THEN ARITH_TAC;
      ASM_REWRITE_TAC[ARITH];
      ASM_REWRITE_TAC[ARITH];
      ASM_REWRITE_TAC[ARITH]];
    ALL_TAC] THEN
  USE_THEN "lin" (MP_TAC o SPECL
   [`3`; `\m. if m = 1 then (p:real^N) else if m = 2 then q else vec 0`]) THEN
  REWRITE_TAC[ARITH] THEN DISCH_TAC THEN
  MP_TAC(ISPECL
   [`(tf:real^N->(num->real^N)->real) x`; `3`;
    `\m. if m = 1 then (p:real^N) else if m = 2 then q else vec 0`;
    `c:real^N`] LRG_SLOT_EXPAND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ACCEPT_TAC o SYM));;

let LRG_FLOW_Q_FORM = prove
 (`!U a b (G:real->real^N->real^N^N) t x u v c.
        lricci_flow U a b G /\ a < t /\ t < b /\ x IN U
        ==> c dot (G t x **
                   frechet_derivative
                    (\z. christoffel (G (drop(fstcart z))) (sndcart z) u v)
                    (at (pastecart (lift t) x)) (pastecart (lift(&1)) (vec 0))) =
            --(lnabla 2 (G t) (lric2 (G t)) x
                 (\m. if m = 1 then v else if m = 2 then c else u) +
               lnabla 2 (G t) (lric2 (G t)) x
                 (\m. if m = 1 then u else if m = 2 then c else v) -
               lnabla 2 (G t) (lric2 (G t)) x
                 (\m. if m = 1 then u else if m = 2 then v else c))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `a:real`; `b:real`;
                 `G:real->real^N->real^N^N`] LRG_FLOW_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `metric_field U ((G:real->real^N->real^N^N) t)` ASSUME_TAC
  THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LRG_N2_FIELD) THEN
  GEN_REWRITE_TAC LAND_CONV [dot] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `sum(1..dimindex(:N))
     (\k. (c:real^N)$k *
          --(lnabla 2 ((G:real->real^N->real^N^N) t) (lric2 (G t)) x
               (\m. if m = 1 then v else if m = 2 then basis k else u) +
             lnabla 2 (G t) (lric2 (G t)) x
               (\m. if m = 1 then u else if m = 2 then basis k else v) -
             lnabla 2 (G t) (lric2 (G t)) x
               (\m. if m = 1 then u else if m = 2 then v else basis k)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    BETA_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC LRG_FLOW_DGAMMA THEN
    MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `a:real`; `b:real`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_MUL_RNEG; SUM_NEG; REAL_ADD_LDISTRIB; REAL_SUB_LDISTRIB;
              SUM_ADD_NUMSEG; SUM_SUB_NUMSEG] THEN
  AP_TERM_TAC THEN BINOP_TAC THENL
   [MATCH_MP_TAC LRG_TUPLE3_SLOT2 THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    BINOP_TAC THENL
     [MATCH_MP_TAC LRG_TUPLE3_SLOT2 THEN EXISTS_TAC `U:real^N->bool` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC LRG_TUPLE3_SLOT3 THEN EXISTS_TAC `U:real^N->bool` THEN
      ASM_REWRITE_TAC[]]]);;

let LRG_FLOW_GAMMA2_VDERIV = prove
 (`!U a b (G:real->real^N->real^N^N) t y u v w.
        lricci_flow U a b G /\ a < t /\ t < b /\ y IN U
        ==> ((\s. christoffel (G (drop s)) y u
                    (christoffel (G (drop s)) y v w)) has_vector_derivative
             (christoffel (G t) y u
                (frechet_derivative
                  (\z. christoffel (G (drop(fstcart z))) (sndcart z) v w)
                  (at (pastecart (lift t) y)) (pastecart (lift(&1)) (vec 0))) +
              frechet_derivative
               (\z. christoffel (G (drop(fstcart z))) (sndcart z) u
                                (christoffel (G t) y v w))
               (at (pastecart (lift t) y)) (pastecart (lift(&1)) (vec 0))))
            (at (lift t))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `a:real`; `b:real`;
                 `G:real->real^N->real^N^N`] LRG_FLOW_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[has_vector_derivative] THEN
  MP_TAC(ISPECL
   [`\s. christoffel ((G:real->real^N->real^N^N) (drop s)) y u`;
    `\s. christoffel ((G:real->real^N->real^N^N) (drop s)) y v w`;
    `\h:real^1. drop h %
       frechet_derivative
        (\z. christoffel ((G:real->real^N->real^N^N) (drop(fstcart z)))
                         (sndcart z) v w)
        (at (pastecart (lift t) y)) (pastecart (lift(&1)) (vec 0))`;
    `interval(lift a,lift b)`; `lift t`] LRG_HAS_DERIVATIVE_LINFAM) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [REWRITE_TAC[OPEN_INTERVAL; IN_INTERVAL_1; LIFT_DROP] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [X_GEN_TAC `s:real^1` THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`U:real^N->bool`; `(G:real->real^N->real^N^N) (drop s)`;
                     `y:real^N`] LRG_CHRISTOFFEL_LINEAR) THEN
      ASM_SIMP_TAC[];
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`U:real^N->bool`; `a:real`; `b:real`;
                     `G:real->real^N->real^N^N`; `t:real`; `y:real^N`;
                     `u:real^N`; `basis i:real^N`] LRG_FLOW_GAMMA_VDERIV) THEN
      ASM_REWRITE_TAC[has_vector_derivative] THEN MESON_TAC[differentiable];
      MP_TAC(ISPECL [`U:real^N->bool`; `a:real`; `b:real`;
                     `G:real->real^N->real^N^N`; `t:real`; `y:real^N`;
                     `v:real^N`; `w:real^N`] LRG_FLOW_GAMMA_VDERIV) THEN
      ASM_REWRITE_TAC[has_vector_derivative]];
    ALL_TAC] THEN
  MATCH_MP_TAC(MESON[]
   `(f:real^1->real^N) = g
    ==> (h has_derivative f) (net:(real^1)net)
        ==> (h has_derivative g) net`) THEN
  REWRITE_TAC[FUN_EQ_THM; LIFT_DROP] THEN X_GEN_TAC `h:real^1` THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `(G:real->real^N->real^N^N) t`;
                 `y:real^N`] LRG_CHRISTOFFEL_LINEAR) THEN
  ASM_SIMP_TAC[LINEAR_CMUL] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `a:real`; `b:real`;
                 `G:real->real^N->real^N^N`; `t:real`; `y:real^N`;
                 `u:real^N`; `christoffel ((G:real->real^N->real^N^N) t) y v w`]
         LRG_FLOW_GAMMA_VDERIV) THEN
  ASM_REWRITE_TAC[has_vector_derivative] THEN
  DISCH_THEN(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
  REWRITE_TAC[VECTOR_ADD_LDISTRIB]);;

let LRG_FLOW_DRIEMANN = prove
 (`!U a b (G:real->real^N->real^N^N) t y u v w.
        lricci_flow U a b G /\ a < t /\ t < b /\ y IN U
        ==> ((\s. lriemann (G (drop s)) y u v w) has_vector_derivative
             (frechet_derivative
               (\x. frechet_derivative
                     (\z. christoffel (G (drop(fstcart z))) (sndcart z) v w)
                     (at (pastecart (lift t) x)) (pastecart (lift(&1)) (vec 0)))
               (at y) u -
              frechet_derivative
               (\x. frechet_derivative
                     (\z. christoffel (G (drop(fstcart z))) (sndcart z) u w)
                     (at (pastecart (lift t) x)) (pastecart (lift(&1)) (vec 0)))
               (at y) v +
              (christoffel (G t) y u
                (frechet_derivative
                  (\z. christoffel (G (drop(fstcart z))) (sndcart z) v w)
                  (at (pastecart (lift t) y)) (pastecart (lift(&1)) (vec 0))) +
               frechet_derivative
                (\z. christoffel (G (drop(fstcart z))) (sndcart z) u
                                 (christoffel (G t) y v w))
                (at (pastecart (lift t) y)) (pastecart (lift(&1)) (vec 0))) -
              (christoffel (G t) y v
                (frechet_derivative
                  (\z. christoffel (G (drop(fstcart z))) (sndcart z) u w)
                  (at (pastecart (lift t) y)) (pastecart (lift(&1)) (vec 0))) +
               frechet_derivative
                (\z. christoffel (G (drop(fstcart z))) (sndcart z) v
                                 (christoffel (G t) y u w))
                (at (pastecart (lift t) y)) (pastecart (lift(&1)) (vec 0)))))
            (at (lift t))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `a:real`; `b:real`;
                 `G:real->real^N->real^N^N`] LRG_FLOW_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[lriemann] THEN
  MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_ADD THEN CONJ_TAC THENL
   [MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_SUB THEN CONJ_TAC THENL
     [MP_TAC(ISPECL
       [`interval(lift a,lift b) PCROSS (U:real^N->bool)`;
        `\z. christoffel ((G:real->real^N->real^N^N) (drop(fstcart z)))
                         (sndcart z) v w`;
        `t:real`; `y:real^N`; `u:real^N`] LRG_TIME_SPACE_SWAP) THEN
      ASM_SIMP_TAC[LRG_FLOW_CHRISTOFFEL_SMOOTH; FSTCART_PASTECART;
                   SNDCART_PASTECART];
      MP_TAC(ISPECL
       [`interval(lift a,lift b) PCROSS (U:real^N->bool)`;
        `\z. christoffel ((G:real->real^N->real^N^N) (drop(fstcart z)))
                         (sndcart z) u w`;
        `t:real`; `y:real^N`; `v:real^N`] LRG_TIME_SPACE_SWAP) THEN
      ASM_SIMP_TAC[LRG_FLOW_CHRISTOFFEL_SMOOTH; FSTCART_PASTECART;
                   SNDCART_PASTECART]];
    MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_SUB THEN CONJ_TAC THEN
    MATCH_MP_TAC LRG_FLOW_GAMMA2_VDERIV THEN
    MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `a:real`; `b:real`] THEN
    ASM_REWRITE_TAC[]]);;


(* ========================================================================= *)
(* The lowered Palatini identity for the time derivative of the curvature,   *)
(* in terms of the (0,3)-tensor Q(u,v,c) = <dGamma(u,v),c>.  The constant    *)
(* ldgamma names the time derivative of the Christoffel symbols at (t,x) (an *)
(* abbreviation used only inside proofs).                                    *)
(* ========================================================================= *)

let ldgamma = new_definition
 `ldgamma (G:real->real^N->real^N^N) t x u v =
    frechet_derivative
     (\z. christoffel (G (drop(fstcart z))) (sndcart z) u v)
     (at (pastecart (lift t) x)) (pastecart (lift(&1)) (vec 0))`;;

let LRG_LDGAMMA_SMOOTH = prove
 (`!U a b (G:real->real^N->real^N^N) t u v.
        lricci_flow U a b G /\ a < t /\ t < b
        ==> smooth_map_on U (\x. ldgamma G t x u v)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `a:real`; `b:real`;
                 `G:real->real^N->real^N^N`] LRG_FLOW_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[ldgamma] THEN
  SUBGOAL_THEN
   `(\x:real^N. frechet_derivative
                 (\z. christoffel ((G:real->real^N->real^N^N) (drop(fstcart z)))
                                  (sndcart z) u v)
                 (at (pastecart (lift t) x)) (pastecart (lift(&1)) (vec 0))) =
    (\z. frechet_derivative
          (\z. christoffel ((G:real->real^N->real^N^N) (drop(fstcart z)))
                           (sndcart z) u v)
          (at z) (pastecart (lift(&1)) (vec 0))) o
    (\x. pastecart (lift t) x)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
  EXISTS_TAC `interval(lift a,lift b) PCROSS (U:real^N->bool)` THEN
  ASM_SIMP_TAC[SMOOTH_MAP_ON_FRECHET_DERIVATIVE; LRG_FLOW_CHRISTOFFEL_SMOOTH] THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[SUBSET; FORALL_IN_IMAGE];
    MATCH_MP_TAC SMOOTH_MAP_ON_PASTECART_OPEN THEN
    ASM_REWRITE_TAC[SMOOTH_MAP_ON_CONST; SMOOTH_MAP_ON_ID]]);;

let LRG_FLOW_DQ = prove
 (`!U a b (G:real->real^N->real^N^N) t y u v c e.
        lricci_flow U a b G /\ a < t /\ t < b /\ y IN U
        ==> frechet_derivative
              (\z. lift(c dot (G t z ** ldgamma G t z u v))) (at y) e =
            lift(c dot (mderiv (G t) y e ** ldgamma G t y u v) +
                 c dot (G t y ** frechet_derivative (\x. ldgamma G t x u v)
                                                    (at y) e))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `a:real`; `b:real`;
                 `G:real->real^N->real^N^N`] LRG_FLOW_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `metric_field U ((G:real->real^N->real^N^N) t)` ASSUME_TAC
  THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL
   [`(G:real->real^N->real^N^N) t`;
    `frechet_derivative ((vectorize:real^N^N->real^(N,N)finite_prod) o
                         (G:real->real^N->real^N^N) t) (at y)`;
    `\z:real^N. (c:real^N)`; `\w:real^N. vec 0:real^N`;
    `\x. ldgamma (G:real->real^N->real^N^N) t x u v`;
    `frechet_derivative (\x. ldgamma (G:real->real^N->real^N^N) t x u v) (at y)`;
    `y:real^N`] LRG_HAS_DERIVATIVE_DOT_MATVEC) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[HAS_DERIVATIVE_CONST] THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`U:real^N->bool`; `(G:real->real^N->real^N^N) t`;
                     `y:real^N`] LRG_METRIC_FIELD_DIFF) THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[];
      REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
      EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC LRG_LDGAMMA_SMOOTH THEN
      MAP_EVERY EXISTS_TAC [`a:real`; `b:real`] THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM(MATCH_MP FRECHET_DERIVATIVE_AT th)]) THEN
  REWRITE_TAC[mderiv; DOT_LZERO; REAL_ADD_LID; DOT_RADD]);;

let LRG_FLOW_PALATINI = prove
 (`!U a b (G:real->real^N->real^N^N) t y u v w c.
        lricci_flow U a b G /\ a < t /\ t < b /\ y IN U
        ==> c dot (G t y **
                   (frechet_derivative (\x. ldgamma G t x v w) (at y) u -
                    frechet_derivative (\x. ldgamma G t x u w) (at y) v +
                    (christoffel (G t) y u (ldgamma G t y v w) +
                     ldgamma G t y u (christoffel (G t) y v w)) -
                    (christoffel (G t) y v (ldgamma G t y u w) +
                     ldgamma G t y v (christoffel (G t) y u w)))) =
            lnabla 3 (G t) (\x p. p 3 dot (G t x ** ldgamma G t x (p 1) (p 2))) y
              (\m. if m = 1 then v else if m = 2 then w else if m = 3 then c
                   else u) -
            lnabla 3 (G t) (\x p. p 3 dot (G t x ** ldgamma G t x (p 1) (p 2))) y
              (\m. if m = 1 then u else if m = 2 then w else if m = 3 then c
                   else v)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `a:real`; `b:real`;
                 `G:real->real^N->real^N^N`] LRG_FLOW_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `metric_field U ((G:real->real^N->real^N^N) t)` ASSUME_TAC
  THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[lnabla; SUM_3; ARITH] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `a:real`; `b:real`;
                 `G:real->real^N->real^N^N`; `t:real`; `y:real^N`]
         LRG_FLOW_DQ) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th; LIFT_DROP]) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `(G:real->real^N->real^N^N) t`; `y:real^N`;
                 `c:real^N`; `u:real^N`;
                 `ldgamma (G:real->real^N->real^N^N) t y v w`]
         LRG_MDERIV_CHRISTOFFEL) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `(G:real->real^N->real^N^N) t`; `y:real^N`;
                 `c:real^N`; `v:real^N`;
                 `ldgamma (G:real->real^N->real^N^N) t y u w`]
         LRG_MDERIV_CHRISTOFFEL) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `(G:real->real^N->real^N^N) t`; `y:real^N`;
                 `ldgamma (G:real->real^N->real^N^N) t y v w`;
                 `christoffel ((G:real->real^N->real^N^N) t) y u c`]
         LRG_METRIC_SYM) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `(G:real->real^N->real^N^N) t`; `y:real^N`;
                 `ldgamma (G:real->real^N->real^N^N) t y u w`;
                 `christoffel ((G:real->real^N->real^N^N) t) y v c`]
         LRG_METRIC_SYM) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `(G:real->real^N->real^N^N) t`; `y:real^N`;
                 `v:real^N`; `u:real^N`] CHRISTOFFEL_SYM) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_ADD_LDISTRIB; MATRIX_VECTOR_MUL_SUB_LDISTRIB;
              DOT_RADD; DOT_RSUB] THEN
  REAL_ARITH_TAC);;

let LRG_FLOW_NQ = prove
 (`!U a b (G:real->real^N->real^N^N) t y p1 p2 p3 p4.
        lricci_flow U a b G /\ a < t /\ t < b /\ y IN U
        ==> lnabla 3 (G t) (\x p. p 3 dot (G t x ** ldgamma G t x (p 1) (p 2))) y
              (\m. if m = 1 then p1 else if m = 2 then p2 else if m = 3 then p3
                   else p4) =
            --(lnabla 3 (G t) (lnabla 2 (G t) (lric2 (G t))) y
                 (\m. if m = 1 then p2 else if m = 2 then p3 else if m = 3 then p1
                      else p4) +
               lnabla 3 (G t) (lnabla 2 (G t) (lric2 (G t))) y
                 (\m. if m = 1 then p1 else if m = 2 then p3 else if m = 3 then p2
                      else p4) -
               lnabla 3 (G t) (lnabla 2 (G t) (lric2 (G t))) y
                 (\m. if m = 1 then p1 else if m = 2 then p2 else if m = 3 then p3
                      else p4))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `a:real`; `b:real`;
                 `G:real->real^N->real^N^N`] LRG_FLOW_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `metric_field U ((G:real->real^N->real^N^N) t)` ASSUME_TAC
  THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LRG_N2_FIELD) THEN
  SUBGOAL_THEN `swap(1,2) o swap(2,3) permutes 1..3 /\ swap(2,3) permutes 1..3`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [MATCH_MP_TAC PERMUTES_COMPOSE; ALL_TAC] THEN
    REPEAT CONJ_TAC THEN MATCH_MP_TAC PERMUTES_SWAP THEN
    REWRITE_TAC[IN_NUMSEG] THEN ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `lnabla 3 ((G:real->real^N->real^N^N) t)
     (\z P. --(&1) *
            (lnabla 2 (G t) (lric2 (G t)) z (\m. P((swap(1,2) o swap(2,3)) m)) +
             (lnabla 2 (G t) (lric2 (G t)) z (\m. P(swap(2,3) m)) -
              lnabla 2 (G t) (lric2 (G t)) z P))) y
     (\m. if m = 1 then p1 else if m = 2 then p2 else if m = 3 then p3
          else p4)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LRG_LNABLA_LOCAL THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `z:real^N` THEN
    X_GEN_TAC `P:num->real^N` THEN DISCH_TAC THEN BETA_TAC THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `a:real`; `b:real`;
                   `G:real->real^N->real^N^N`; `t:real`; `z:real^N`;
                   `(P:num->real^N) 1`; `(P:num->real^N) 2`;
                   `(P:num->real^N) 3`] LRG_FLOW_Q_FORM) THEN
    ASM_REWRITE_TAC[GSYM ldgamma] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC(REAL_ARITH
     `a = a' /\ b = b' /\ c = c' ==> --(a + b - c) = --(&1) * (a' + (b' - c'))`) THEN
    REPEAT CONJ_TAC THEN MATCH_MP_TAC LRG_LNABLA_AGREE THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_SIMP_TAC[LRG_LRIC2_FIELD; ARITH] THEN
    REWRITE_TAC[ARITH_RULE `1 <= m /\ m <= 3 <=> m = 1 \/ m = 2 \/ m = 3`] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[swap; o_THM; ARITH];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!P. (\x. lift(lnabla 2 ((G:real->real^N->real^N^N) t) (lric2 (G t)) x P))
        differentiable at y`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  W(fun (asl,w) -> MP_TAC(PART_MATCH (lhs o rand) LRG_LNABLA_CMUL (lhand w))) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[LIFT_ADD; LIFT_SUB] THEN
    MATCH_MP_TAC DIFFERENTIABLE_ADD THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC DIFFERENTIABLE_SUB THEN ASM_REWRITE_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  W(fun (asl,w) -> MP_TAC(PART_MATCH (lhs o rand) LRG_LNABLA_ADD (rand(lhand w)))) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[LIFT_SUB] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC DIFFERENTIABLE_SUB THEN ASM_REWRITE_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  W(fun (asl,w) -> MP_TAC(PART_MATCH (lhs o rand) LRG_LNABLA_SUB
                           (rand(rand(lhand w))))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`3`; `(G:real->real^N->real^N^N) t`;
                 `lnabla 2 ((G:real->real^N->real^N^N) t) (lric2 (G t))`;
                 `swap(1,2) o swap(2,3)`; `y:real^N`;
                 `\m. if m = 1 then (p1:real^N) else if m = 2 then p2
                      else if m = 3 then p3 else p4`] LRG_LNABLA_PERMUTE) THEN
  MP_TAC(ISPECL [`3`; `(G:real->real^N->real^N^N) t`;
                 `lnabla 2 ((G:real->real^N->real^N^N) t) (lric2 (G t))`;
                 `swap(2,3)`; `y:real^N`;
                 `\m. if m = 1 then (p1:real^N) else if m = 2 then p2
                      else if m = 3 then p3 else p4`] LRG_LNABLA_PERMUTE) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN
  REWRITE_TAC[ETA_AX] THEN
  MATCH_MP_TAC(REAL_ARITH
   `a = a' /\ b = b' ==> --(&1) * (a + (b - c)) = --(a' + b' - c)`) THEN
  CONJ_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; swap; o_THM] THEN X_GEN_TAC `m:num` THEN
  MAP_EVERY (fun n -> ASM_CASES_TAC (mk_eq(`m:num`, mk_small_numeral n)) THEN
                      ASM_REWRITE_TAC[ARITH]) [1;2;3]);;


(* ========================================================================= *)
(* Time derivatives of the inverse metric and of the Ricci tensor at a       *)
(* point, the squared norm of Ricci, and LSCALAR_EVOLUTION.                  *)
(* ========================================================================= *)

let LRG_VDERIV_COMPONENT_REAL = prove
 (`!(f:real->real^N) f' t k.
        ((\s. f(drop s)) has_vector_derivative f') (at (lift t)) /\
        1 <= k /\ k <= dimindex(:N)
        ==> ((\s. f s$k) has_real_derivative f'$k) (atreal t)`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [HAS_VECTOR_DERIVATIVE_COMPONENTWISE_AT] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `k:num`) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(\x. lift((f:real->real^N)(drop x)$k)) =
                lift o (\s. f s$k) o drop`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  REWRITE_TAC[GSYM HAS_REAL_VECTOR_DERIVATIVE_AT]);;

let LRG_VDERIV_MATRIX_ENTRY_REAL = prove
 (`!(A:real->real^N^N) M t p q.
        ((\s. vectorize(A(drop s))) has_vector_derivative vectorize M)
        (at (lift t))
        ==> ((\s. A s$p$q) has_real_derivative M$p$q) (atreal t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[has_vector_derivative] THEN DISCH_TAC THEN
  REWRITE_TAC[HAS_REAL_VECTOR_DERIVATIVE_AT; has_vector_derivative] THEN
  MP_TAC(ISPECL
   [`\s. (vectorize:real^N^N->real^(N,N)finite_prod)((A:real->real^N^N)(drop s))`;
    `\v:real^(N,N)finite_prod. lift((matrify v:real^N^N)$p$q)`;
    `\x:real^1. drop x % (vectorize:real^N^N->real^(N,N)finite_prod) M`;
    `\v:real^(N,N)finite_prod. lift((matrify v:real^N^N)$p$q)`;
    `lift t`] DIFF_CHAIN_AT) THEN
  ASM_SIMP_TAC[HAS_DERIVATIVE_LINEAR; LRG_LINEAR_MATRIFY_ENTRY] THEN
  REWRITE_TAC[o_DEF; MATRIFY_VECTORIZE; MATRIFY_CMUL; MATRIX_CMUL_COMPONENT;
              LIFT_CMUL]);;

let LRG_FLOW_DGINV = prove
 (`!U a b (G:real->real^N->real^N^N) t y.
        lricci_flow U a b G /\ a < t /\ t < b /\ y IN U
        ==> ((\s. vectorize(matrix_inv(G (drop s) y))) has_vector_derivative
             vectorize(--(matrix_inv(G t y) **
                          (lambda i j. --(&2) * lricci (G t) y (basis i) (basis j)) **
                          matrix_inv(G t y)))) (at (lift t))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `a:real`; `b:real`;
                 `G:real->real^N->real^N^N`] LRG_FLOW_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `a:real`; `b:real`;
                 `G:real->real^N->real^N^N`; `y:real^N`] LRG_FLOW_TIME_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`\s. (G:real->real^N->real^N^N) (drop s) y`;
                 `interval(lift a,lift b)`; `lift t`]
         LRG_HAS_DERIVATIVE_MATRIX_INV) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[OPEN_INTERVAL; IN_INTERVAL_1; LIFT_DROP] THEN
    X_GEN_TAC `s:real^1` THEN REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP] THEN
    STRIP_TAC THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `(G:real->real^N->real^N^N) (drop s)`;
                   `y:real^N`] LRG_METRIC_INVERTIBLE) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `a:real`; `b:real`;
                 `G:real->real^N->real^N^N`; `t:real`; `y:real^N`]
         LRG_FLOW_VDERIV) THEN
  ASM_REWRITE_TAC[has_vector_derivative] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `frechet_derivative ((vectorize:real^N^N->real^(N,N)finite_prod) o
                        (\s. (G:real->real^N->real^N^N) (drop s) y)) (at (lift t)) =
    (\x. drop x % vectorize((lambda i j. --(&2) *
                                lricci (G t) y (basis i) (basis j)):real^N^N))`
  SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
    ASM_REWRITE_TAC[o_DEF];
    ALL_TAC] THEN
  REWRITE_TAC[o_DEF; LIFT_DROP] THEN
  MATCH_MP_TAC(MESON[]
   `(f:real^1->real^(N,N)finite_prod) = g
    ==> (h has_derivative f) (net:(real^1)net)
        ==> (h has_derivative g) net`) THEN
  REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `x:real^1` THEN
  REWRITE_TAC[MATRIFY_CMUL; MATRIFY_VECTORIZE; MATRIX_MUL_LMUL;
              MATRIX_MUL_RMUL; GSYM VECTORIZE_CMUL] THEN
  AP_TERM_TAC THEN REWRITE_TAC[MATRIX_NEG_MINUS1; MATRIX_CMUL_ASSOC] THEN
  REWRITE_TAC[REAL_MUL_SYM]);;

let LRG_FLOW_DRICCI = prove
 (`!U a b (G:real->real^N->real^N^N) t y p q.
        lricci_flow U a b G /\ a < t /\ t < b /\ y IN U
        ==> ((\s. lricci (G s) y p q) has_real_derivative
             sum(1..dimindex(:N))
              (\k. sum(1..dimindex(:N))
                (\l. matrix_inv(G t y)$k$l *
                     (lnabla 3 (G t)
                        (\x p. p 3 dot (G t x ** ldgamma G t x (p 1) (p 2))) y
                        (\m. if m = 1 then p else if m = 2 then q
                             else if m = 3 then basis l else basis k) -
                      lnabla 3 (G t)
                        (\x p. p 3 dot (G t x ** ldgamma G t x (p 1) (p 2))) y
                        (\m. if m = 1 then basis k else if m = 2 then q
                             else if m = 3 then basis l else p))))) (atreal t)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `a:real`; `b:real`;
                 `G:real->real^N->real^N^N`] LRG_FLOW_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `metric_field U ((G:real->real^N->real^N^N) t)` ASSUME_TAC
  THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[lricci] THEN MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUM THEN
  REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN X_GEN_TAC `k:num` THEN
  STRIP_TAC THEN BETA_TAC THEN
  MP_TAC(REWRITE_RULE[GSYM ldgamma]
    (ISPECL [`U:real^N->bool`; `a:real`; `b:real`;
             `G:real->real^N->real^N^N`; `t:real`; `y:real^N`;
             `basis k:real^N`; `p:real^N`; `q:real^N`] LRG_FLOW_DRIEMANN)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `k:num` o MATCH_MP
    (REWRITE_RULE[IMP_CONJ] LRG_VDERIV_COMPONENT_REAL)) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(MESON[]
   `(x:real) = y ==> (f has_real_derivative x) (net:(real)net)
                     ==> (f has_real_derivative y) net`) THEN
  W(fun (asl,w) ->
     MP_TAC(ISPECL [`U:real^N->bool`; `(G:real->real^N->real^N^N) t`;
                    `y:real^N`; rand(rator(lhand w)); `k:num`]
            LRG_COMPONENT_METRIC)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `l:num` THEN STRIP_TAC THEN
  BETA_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC LRG_FLOW_PALATINI THEN
  MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `a:real`; `b:real`] THEN
  ASM_REWRITE_TAC[]);;

let LRG_SUM_INDEX_TUPLES_2 = prove
 (`!f. sum (index_tuples 2 (:N)) f =
       sum(1..dimindex(:N))
        (\p. sum(1..dimindex(:N))
              (\q. f (\m. if m = 2 then q else if m = 1 then p else 0)))`,
  GEN_TAC THEN
  MP_TAC(ISPECL [`f:(num->num)->real`; `1`] LRG_SUM_INDEX_TUPLES_SUC) THEN
  REWRITE_TAC[ARITH] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL
   [`\i. sum(1..dimindex(:N))
          (\q. (f:(num->num)->real) (\m. if m = 2 then q else i m))`; `0`]
   LRG_SUM_INDEX_TUPLES_SUC) THEN
  REWRITE_TAC[ARITH; LRG_SUM_INDEX_TUPLES_0]);;

let LRG_LTNORM2_RIC = prove
 (`!U (G:real^N->real^N^N) y.
        metric_field U G /\ y IN U
        ==> &2 * ltnorm2 2 G (lric2 G) y =
            sum(1..dimindex(:N))
             (\p. sum(1..dimindex(:N))
               (\q. (--(matrix_inv(G y) **
                        (lambda i j. --(&2) * lricci G y (basis i) (basis j)) **
                        matrix_inv(G y)))$p$q *
                    lricci G y (basis p) (basis q)))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[ltnorm2; LRG_SUM_INDEX_TUPLES_2; PRODUCT_2; lric2; ARITH] THEN
  REWRITE_TAC[GSYM SUM_LMUL] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `p:num` THEN STRIP_TAC THEN
  BETA_TAC THEN REWRITE_TAC[GSYM SUM_LMUL] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `q:num` THEN STRIP_TAC THEN
  BETA_TAC THEN
  ASM_SIMP_TAC[MATRIX_NEG_COMPONENT; LRG_MATRIX_MUL_COMPONENT] THEN
  REWRITE_TAC[GSYM SUM_LMUL; GSYM SUM_RMUL; GSYM SUM_NEG] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN
  BETA_TAC THEN ASM_SIMP_TAC[LRG_MATRIX_MUL_COMPONENT] THEN
  REWRITE_TAC[GSYM SUM_LMUL; GSYM SUM_RMUL; GSYM SUM_NEG] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `b:num` THEN STRIP_TAC THEN
  BETA_TAC THEN ASM_SIMP_TAC[LAMBDA_BETA] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`;
                 `b:num`; `q:num`] LRG_MATRIX_INV_SYM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC);;

let LSCALAR_EVOLUTION = prove
 (`!U a b (G:real->real^N->real^N^N) t y.
        lricci_flow U a b G /\ a < t /\ t < b /\ y IN U
        ==> ((\s. lscalar (G s) y) has_real_derivative
             (llap (G t) (lscalar (G t)) y +
              &2 * ltnorm2 2 (G t) (lric2 (G t)) y)) (atreal t)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `a:real`; `b:real`;
                 `G:real->real^N->real^N^N`] LRG_FLOW_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `metric_field U ((G:real->real^N->real^N^N) t)` ASSUME_TAC
  THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `(G:real->real^N->real^N^N) t`; `y:real^N`]
         LRG_PALATINI_TRACE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `(G:real->real^N->real^N^N) t`; `y:real^N`]
         LRG_LTNORM2_RIC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[GSYM SUM_ADD_NUMSEG] THEN REWRITE_TAC[lscalar] THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUM THEN
  REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN X_GEN_TAC `p:num` THEN
  STRIP_TAC THEN BETA_TAC THEN REWRITE_TAC[GSYM SUM_ADD_NUMSEG] THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUM THEN
  REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN X_GEN_TAC `q:num` THEN
  STRIP_TAC THEN BETA_TAC THEN
  MP_TAC(ISPECL
   [`\s. matrix_inv((G:real->real^N->real^N^N) s y)$p$q`;
    `(--(matrix_inv((G:real->real^N->real^N^N) t y) **
         (lambda i j. --(&2) * lricci (G t) y (basis i) (basis j)) **
         matrix_inv(G t y)))$p$q`;
    `\s. lricci ((G:real->real^N->real^N^N) s) y (basis p) (basis q)`;
    `sum(1..dimindex(:N))
      (\k. sum(1..dimindex(:N))
        (\l. matrix_inv((G:real->real^N->real^N^N) t y)$k$l *
             (lnabla 3 (G t)
                (\x p. p 3 dot (G t x ** ldgamma G t x (p 1) (p 2))) y
                (\m. if m = 1 then basis p else if m = 2 then basis q
                     else if m = 3 then basis l else basis k) -
              lnabla 3 (G t)
                (\x p. p 3 dot (G t x ** ldgamma G t x (p 1) (p 2))) y
                (\m. if m = 1 then basis k else if m = 2 then basis q
                     else if m = 3 then basis l else basis p))))`;
    `t:real`] HAS_REAL_DERIVATIVE_MUL_ATREAL) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC LRG_VDERIV_MATRIX_ENTRY_REAL THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC LRG_FLOW_DGINV THEN
      MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `a:real`; `b:real`] THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC LRG_FLOW_DRICCI THEN
      MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `a:real`; `b:real`] THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `a:real`; `b:real`;
                 `G:real->real^N->real^N^N`; `t:real`; `y:real^N`]
         LRG_FLOW_NQ) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[]);;

