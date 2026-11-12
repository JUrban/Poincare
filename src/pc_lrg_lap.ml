(* ========================================================================= *)
(* Squared gradient norm and Laplacian of scalar functions on open subsets   *)
(* of real^N: naturality under diffeomorphisms, locality, positivity of the  *)
(* gradient norm, the flat Laplacian.  Builds on pc_lrg and pc_lrg_tensor    *)
(* (the Hessian is lnabla 1 of df).                                          *)
(* ========================================================================= *)

needs "src/pc_lrg_tensor.ml";;

prioritize_real();;
type_invention_error := true;;

(* Definitions: squared gradient norm and Laplacian of scalar functions in   *)
(* a chart.                                                                  *)

let lgrad2 = new_definition
 `lgrad2 (G:real^N->real^N^N) (f:real^N->real) (y:real^N) =
    sum(1..dimindex(:N))
     (\i. sum(1..dimindex(:N))
       (\j. matrix_inv(G y)$i$j *
            drop(frechet_derivative (\z. lift(f z)) (at y) (basis i)) *
            drop(frechet_derivative (\z. lift(f z)) (at y) (basis j))))`;;

let llap = new_definition
 `llap (G:real^N->real^N^N) (f:real^N->real) (y:real^N) =
    sum(1..dimindex(:N))
     (\i. sum(1..dimindex(:N))
       (\j. matrix_inv(G y)$i$j *
            (drop(frechet_derivative
                   (\z. frechet_derivative (\w. lift(f w)) (at z) (basis j))
                   (at y) (basis i)) -
             sum(1..dimindex(:N))
              (\k. (christoffel G y (basis i) (basis j))$k *
                   drop(frechet_derivative (\z. lift(f z)) (at y) (basis k))))))`;;



(* ========================================================================= *)
(* Lemmas.  Contraction of a congruence-transformed array with the inverse   *)
(* of the congruent matrix; bilinear expansion of 2-tensors; Jacobians of    *)
(* diffeomorphisms; the differential of f as a 1-tensor field; the Laplacian *)
(* as the trace of lnabla 1 of the differential.                             *)
(* ========================================================================= *)

let LRG_CONGRUENCE_ENTRY = prove
 (`!(J:real^N^N) (b:num->num->real) i j.
        1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
        ==> (transp J ** ((lambda p q. b p q):real^N^N) ** J)$i$j =
            sum(1..dimindex(:N))
             (\p. sum(1..dimindex(:N)) (\q. J$p$i * J$q$j * b p q))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[LRG_MATRIX_MUL_COMPONENT] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `p:num` THEN STRIP_TAC THEN
  BETA_TAC THEN
  ASM_SIMP_TAC[LRG_MATRIX_MUL_COMPONENT; TRANSP_COMPONENT; GSYM SUM_LMUL] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `q:num` THEN STRIP_TAC THEN
  BETA_TAC THEN ASM_SIMP_TAC[LAMBDA_BETA] THEN REAL_ARITH_TAC);;

let LRG_CONTRACT_CONGRUENCE = prove
 (`!(J:real^N^N) (A:real^N^N) (b:num->num->real) (c:num->num->real).
        invertible J /\ invertible A /\
        (!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
               ==> c i j = sum(1..dimindex(:N))
                             (\p. sum(1..dimindex(:N))
                                    (\q. J$p$i * J$q$j * b p q)))
        ==> sum(1..dimindex(:N))
             (\i. sum(1..dimindex(:N))
                    (\j. matrix_inv(transp J ** A ** J)$i$j * c i j)) =
            sum(1..dimindex(:N))
             (\i. sum(1..dimindex(:N)) (\j. matrix_inv A$i$j * b i j))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `sum(1..dimindex(:N))
     (\i. sum(1..dimindex(:N))
       (\j. matrix_inv(transp J ** A ** J:real^N^N)$i$j *
            (c:num->num->real) i j)) =
    sum(1..dimindex(:N))
     (\i. sum(1..dimindex(:N))
       (\j. matrix_inv(transp J ** A ** J:real^N^N)$i$j *
            (transp J ** ((lambda p q. (b:num->num->real) p q):real^N^N) **
             J)$i$j))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    BETA_TAC THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN
    STRIP_TAC THEN BETA_TAC THEN ASM_SIMP_TAC[LRG_CONGRUENCE_ENTRY];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum(1..dimindex(:N))
     (\i. sum(1..dimindex(:N))
       (\j. matrix_inv(A:real^N^N)$i$j * (b:num->num->real) i j)) =
    sum(1..dimindex(:N))
     (\i. sum(1..dimindex(:N))
       (\j. matrix_inv(A:real^N^N)$i$j *
            ((lambda p q. (b:num->num->real) p q):real^N^N)$i$j))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    BETA_TAC THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN
    STRIP_TAC THEN BETA_TAC THEN ASM_SIMP_TAC[LAMBDA_BETA];
    ALL_TAC] THEN
  REWRITE_TAC[LRG_SUM_ENTRYWISE] THEN
  SUBGOAL_THEN `invertible(transp(J:real^N^N))` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[INVERTIBLE_TRANSP]; ALL_TAC] THEN
  SUBGOAL_THEN
   `matrix_inv(transp J ** A ** J:real^N^N) =
    matrix_inv J ** matrix_inv A ** matrix_inv(transp J)`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[MATRIX_INV_MUL; INVERTIBLE_MATRIX_MUL; MATRIX_MUL_ASSOC];
    ALL_TAC] THEN
  REWRITE_TAC[MATRIX_TRANSP_MUL; TRANSP_TRANSP] THEN
  REWRITE_TAC[GSYM MATRIX_MUL_ASSOC] THEN
  MP_TAC(ISPECL [`J:real^N^N`; `matrix_inv(A:real^N^N)`;
                 `transp((lambda p q. (b:num->num->real) p q):real^N^N)`]
         LRG_TRACE_CONGRUENCE) THEN
  ASM_REWRITE_TAC[GSYM MATRIX_MUL_ASSOC]);;

let LRG_TENSOR2_EXPAND = prove
 (`!U (tf:real^N->(num->real^N)->real) y v w.
        ltensor_field 2 U tf /\ y IN U
        ==> tf y (\m. if m = 1 then w else v) =
            sum(1..dimindex(:N))
             (\p. sum(1..dimindex(:N))
                    (\q. v$p * w$q *
                         tf y (\m. if m = 1 then basis q else basis p)))`,
  REWRITE_TAC[ltensor_field] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `y:real^N`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "agree") (LABEL_TAC "lin")) THEN
  SUBGOAL_THEN
   `!a b:real^N. (tf:real^N->(num->real^N)->real) y
                   (\j. if j = 1 then a else b) =
                 tf y (\j. if j = 2 then b else a)`
  (LABEL_TAC "swap") THENL
   [REPEAT GEN_TAC THEN USE_THEN "agree" MATCH_MP_TAC THEN
    X_GEN_TAC `m:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `m = 1 \/ m = 2` (DISJ_CASES_THEN SUBST1_TAC) THENL
     [MAP_EVERY UNDISCH_TAC [`1 <= (m:num)`; `(m:num) <= 2`] THEN ARITH_TAC;
      REWRITE_TAC[ARITH];
      REWRITE_TAC[ARITH]];
    ALL_TAC] THEN
  MP_TAC(BETA_RULE(ISPECL [`(tf:real^N->(num->real^N)->real) y`; `1`;
                           `\m:num. (v:real^N)`; `w:real^N`] LRG_SLOT_EXPAND)) THEN
  ANTS_TAC THENL
   [USE_THEN "lin" (MP_TAC o BETA_RULE o SPECL [`1`; `\m:num. (v:real^N)`]) THEN
    REWRITE_TAC[ARITH];
    DISCH_THEN SUBST1_TAC] THEN
  GEN_REWRITE_TAC RAND_CONV [SUM_SWAP_NUMSEG] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `q:num` THEN STRIP_TAC THEN
  BETA_TAC THEN USE_THEN "swap" (fun th -> REWRITE_TAC[th]) THEN
  MP_TAC(BETA_RULE(ISPECL [`(tf:real^N->(num->real^N)->real) y`; `2`;
                           `\m:num. basis q:real^N`; `v:real^N`]
                          LRG_SLOT_EXPAND)) THEN
  ANTS_TAC THENL
   [USE_THEN "lin" (MP_TAC o BETA_RULE o SPECL [`2`; `\m:num. basis q:real^N`]) THEN
    REWRITE_TAC[ARITH];
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
  X_GEN_TAC `p:num` THEN STRIP_TAC THEN BETA_TAC THEN
  REWRITE_TAC[REAL_MUL_AC]);;

let LRG_DIFFEO_JACOBIAN_INVERTIBLE = prove
 (`!U U' (h:real^N->real^N) h' y.
        diffeomorphism_on U' U h h' /\ y IN U'
        ==> invertible(matrix(frechet_derivative h (at y)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `U':real^N->bool`; `h:real^N->real^N`;
                 `h':real^N->real^N`; `y:real^N`] LRG_DIFFEO_DERIV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `linear(frechet_derivative (h':real^N->real^N)
                                          (at ((h:real^N->real^N) y)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC LRG_DIFFEO_INV_LINEAR THEN
    MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `U':real^N->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[INVERTIBLE_LEFT_INVERSE] THEN
  EXISTS_TAC `matrix(frechet_derivative (h':real^N->real^N)
                                        (at ((h:real^N->real^N) y)))` THEN
  ASM_SIMP_TAC[GSYM MATRIX_COMPOSE] THEN
  SUBGOAL_THEN
   `frechet_derivative (h':real^N->real^N) (at ((h:real^N->real^N) y)) o
    frechet_derivative h (at y) = (\x. x)`
  SUBST1_TAC THENL
   [ASM_REWRITE_TAC[FUN_EQ_THM; o_THM]; REWRITE_TAC[MATRIX_ID]]);;

let LRG_COMPOSE_DERIV = prove
 (`!U U' (h:real^N->real^N) h' (f:real^N->real) x.
        diffeomorphism_on U' U h h' /\ smooth_map_on U (\z. lift(f z)) /\
        x IN U'
        ==> !v. frechet_derivative (\z. lift((f o h) z)) (at x) v =
                frechet_derivative (\z. lift(f z)) (at (h x))
                                   (frechet_derivative h (at x) v)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `U':real^N->bool`; `h:real^N->real^N`;
                 `h':real^N->real^N`; `x:real^N`] LRG_DIFFEO_DERIV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[diffeomorphism_on]; ALL_TAC] THEN
  REWRITE_TAC[o_THM] THEN
  MP_TAC(BETA_RULE(ISPECL [`h:real^N->real^N`; `\z. lift((f:real^N->real) z)`;
                           `x:real^N`; `v:real^N`]
                          LRG_FRECHET_DERIVATIVE_CHAIN)) THEN
  DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
   [REWRITE_TAC[differentiable] THEN ASM_MESON_TAC[];
    MP_TAC(ISPECL [`U:real^N->bool`; `\z. lift((f:real^N->real) z)`;
                   `(h:real^N->real^N) x`; `v:real^N`]
           LRG_SMOOTH_FRECHET_DIFFERENTIABLE) THEN
    ASM_SIMP_TAC[]]);;

let LRG_DROP_LINEAR_MATRIX = prove
 (`!(L:real^N->real^1) (M:real^N->real^N) i.
        linear L /\ 1 <= i /\ i <= dimindex(:N)
        ==> drop(L(M(basis i))) =
            sum(1..dimindex(:N)) (\p. matrix M$p$i * drop(L(basis p)))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[MATRIX_COMPONENT] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC LRG_LINEAR_DROP_EXPAND THEN
  ASM_REWRITE_TAC[]);;

let LRG_DF_TENSOR_FIELD = prove
 (`!U (f:real^N->real).
        open U /\ smooth_map_on U (\z. lift(f z))
        ==> ltensor_field 1 U
              (\z u. drop(frechet_derivative (\w. lift(f w)) (at z) (u 1))) /\
            (!u. smooth_map_on U
                   (\z. lift(drop(frechet_derivative (\w. lift(f w)) (at z)
                                                     (u 1)))))`,
  REPEAT STRIP_TAC THENL
   [REWRITE_TAC[ltensor_field] THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN BETA_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `1`) THEN REWRITE_TAC[ARITH] THEN
      DISCH_THEN SUBST1_TAC THEN REFL_TAC;
      REPEAT STRIP_TAC THEN BETA_TAC THEN
      SUBGOAL_THEN `i = 1` SUBST1_TAC THENL
       [MAP_EVERY UNDISCH_TAC [`1 <= (i:num)`; `(i:num) <= 1`] THEN ARITH_TAC;
        ALL_TAC] THEN
      REWRITE_TAC[LIFT_DROP; ETA_AX] THEN
      MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
      MP_TAC(ISPECL [`U:real^N->bool`; `\w. lift((f:real^N->real) w)`;
                     `y:real^N`; `vec 0:real^N`]
             LRG_SMOOTH_FRECHET_DIFFERENTIABLE) THEN
      ASM_SIMP_TAC[]];
    REWRITE_TAC[LIFT_DROP] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_FRECHET_DERIVATIVE THEN ASM_REWRITE_TAC[]]);;

let LRG_LLAP_LNABLA = prove
 (`!U (G:real^N->real^N^N) f y.
        open U /\ smooth_map_on U (\z. lift(f z)) /\ y IN U
        ==> llap G f y =
            sum(1..dimindex(:N))
             (\i. sum(1..dimindex(:N))
               (\j. matrix_inv(G y)$i$j *
                    lnabla 1 G
                     (\z u. drop(frechet_derivative (\w. lift(f w)) (at z) (u 1)))
                     y (\m. if m = 1 then basis j else basis i)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `linear(frechet_derivative (\z. lift((f:real^N->real) z)) (at y))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `\z. lift((f:real^N->real) z)`;
                   `y:real^N`; `vec 0:real^N`]
           LRG_SMOOTH_FRECHET_DIFFERENTIABLE) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[llap; lnabla] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  BETA_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  BETA_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[SUM_SING_NUMSEG] THEN BETA_TAC THEN
  REWRITE_TAC[ARITH; LIFT_DROP] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC LRG_LINEAR_DROP_EXPAND THEN
  ASM_REWRITE_TAC[ETA_AX]);;

let LRG_CHRISTOFFEL_CONST = prove
 (`!(A:real^N^N) z u v. christoffel (\z. A) z u v = vec 0`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[christoffel; mderiv; o_DEF; FRECHET_DERIVATIVE_CONST_AT;
              MATRIFY_0; MATRIX_VECTOR_MUL_LZERO; DOT_RZERO; VEC_COMPONENT;
              REAL_ADD_LID; REAL_SUB_REFL; REAL_MUL_RZERO] THEN
  SUBGOAL_THEN `(lambda k. &0):real^N = vec 0` SUBST1_TAC THENL
   [SIMP_TAC[CART_EQ; LAMBDA_BETA; VEC_COMPONENT]; ALL_TAC] THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_RZERO]);;

let LRG_QUADFORM_SUM = prove
 (`!(A:real^N^N) (x:num->real).
        sum(1..dimindex(:N))
         (\i. sum(1..dimindex(:N)) (\j. A$i$j * x i * x j)) =
        ((lambda i. x i):real^N) dot (A ** ((lambda i. x i):real^N))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[dot; matrix_vector_mul] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  BETA_TAC THEN ASM_SIMP_TAC[LAMBDA_BETA] THEN REWRITE_TAC[GSYM SUM_LMUL] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  BETA_TAC THEN ASM_SIMP_TAC[LAMBDA_BETA] THEN REAL_ARITH_TAC);;

let LRG_QUADFORM_POS = prove
 (`!U (G:real^N->real^N^N) y (x:num->real).
        metric_field U G /\ y IN U
        ==> &0 <= sum(1..dimindex(:N))
                   (\i. sum(1..dimindex(:N))
                          (\j. matrix_inv(G y)$i$j * x i * x j))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`]
         LRG_METRIC_INV_POSDEF) THEN
  ASM_REWRITE_TAC[positive_definite] THEN STRIP_TAC THEN
  REWRITE_TAC[LRG_QUADFORM_SUM] THEN
  SPEC_TAC(`(lambda i. (x:num->real) i):real^N`, `v:real^N`) THEN
  GEN_TAC THEN ASM_CASES_TAC `v:real^N = vec 0` THEN
  ASM_REWRITE_TAC[DOT_LZERO; REAL_LE_REFL] THEN
  ASM_MESON_TAC[REAL_LT_IMP_LE]);;


(* ========================================================================= *)
(* Locality, positivity of the gradient norm, the Laplacian of the flat      *)
(* metric.                                                                   *)
(* ========================================================================= *)

let LGRAD2_LOCAL = prove
 (`!(G1:real^N->real^N^N) G2 f1 f2 s y.
        open s /\ y IN s /\ (!z. z IN s ==> G1 z = G2 z /\ f1 z = f2 z)
        ==> lgrad2 G1 f1 y = lgrad2 G2 f2 y`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(G1:real^N->real^N^N) y = G2 y` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `frechet_derivative (\z. lift((f1:real^N->real) z)) (at y) =
    frechet_derivative (\z. lift((f2:real^N->real) z)) (at y)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC LRG_FRECHET_DERIVATIVE_EQ_OPEN THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN BETA_TAC THEN ASM_MESON_TAC[];
    ASM_REWRITE_TAC[lgrad2]]);;

let LLAP_LOCAL = prove
 (`!(G1:real^N->real^N^N) G2 f1 f2 s y.
        open s /\ y IN s /\ (!z. z IN s ==> G1 z = G2 z /\ f1 z = f2 z)
        ==> llap G1 f1 y = llap G2 f2 y`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(G1:real^N->real^N^N) y = G2 y` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN s
        ==> frechet_derivative (\w. lift((f1:real^N->real) w)) (at x) =
            frechet_derivative (\w. lift((f2:real^N->real) w)) (at x)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC LRG_FRECHET_DERIVATIVE_EQ_OPEN THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN BETA_TAC THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!v. frechet_derivative
          (\z. frechet_derivative (\w. lift((f1:real^N->real) w)) (at z) v)
          (at y) =
        frechet_derivative
          (\z. frechet_derivative (\w. lift((f2:real^N->real) w)) (at z) v)
          (at y)`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC LRG_FRECHET_DERIVATIVE_EQ_OPEN THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!u v. christoffel (G1:real^N->real^N^N) y u v = christoffel G2 y u v`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC CHRISTOFFEL_LOCAL THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `frechet_derivative (\z. lift((f1:real^N->real) z)) (at y) =
    frechet_derivative (\z. lift((f2:real^N->real) z)) (at y)`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[llap]);;

let LGRAD2_POS = prove
 (`!U (G:real^N->real^N^N) f y.
        metric_field U G /\ y IN U ==> &0 <= lgrad2 G f y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[lgrad2] THEN
  MP_TAC(BETA_RULE(ISPECL
   [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`;
    `\i. drop(frechet_derivative (\z. lift((f:real^N->real) z)) (at y)
                                 (basis i))`] LRG_QUADFORM_POS)) THEN
  ASM_REWRITE_TAC[]);;

let LLAP_FLAT = prove
 (`!U f (y:real^N).
        open U /\ y IN U /\ smooth_map_on U (\z. lift(f z))
        ==> llap (\z. mat 1) f y =
            sum(1..dimindex(:N))
              (\i. drop(frechet_derivative
                     (\z. frechet_derivative (\w. lift(f w)) (at z) (basis i))
                     (at y) (basis i)))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[llap; LRG_CHRISTOFFEL_CONST; MATRIX_INV_I; VEC_COMPONENT;
              REAL_MUL_LZERO; SUM_0; REAL_SUB_RZERO] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  BETA_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `sum(1..dimindex(:N))
     (\j. if j = i
          then drop(frechet_derivative
                     (\z. frechet_derivative (\w. lift((f:real^N->real) w))
                                             (at z) (basis i))
                     (at y) (basis i))
          else &0)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    BETA_TAC THEN ASM_SIMP_TAC[MAT_COMPONENT] THEN
    ASM_CASES_TAC `i:num = j` THENL
     [ASM_REWRITE_TAC[REAL_MUL_LID];
      SUBGOAL_THEN `~(j:num = i)` (fun th -> ASM_REWRITE_TAC[th; REAL_MUL_LZERO]) THEN
      ASM_MESON_TAC[]];
    REWRITE_TAC[SUM_DELTA; IN_NUMSEG] THEN ASM_REWRITE_TAC[]]);;


(* ========================================================================= *)
(* Naturality of the gradient norm and of the Laplacian under                *)
(* diffeomorphisms.  The Hessian is lnabla 1 of the differential             *)
(* (LRG_LLAP_LNABLA), whose pullback is LNABLA_PULLBACK.                     *)
(* ========================================================================= *)

let LGRAD2_PULLBACK = prove
 (`!U U' (h:real^N->real^N) h' G f y.
        metric_field U G /\ diffeomorphism_on U' U h h' /\
        smooth_map_on U (\z. lift(f z)) /\ y IN U'
        ==> lgrad2 (mpullback h G) (f o h) y = lgrad2 G f (h y)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `U':real^N->bool`; `h:real^N->real^N`;
                 `h':real^N->real^N`; `y:real^N`] LRG_DIFFEO_DERIV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  SUBGOAL_THEN
   `linear(frechet_derivative (\z. lift((f:real^N->real) z))
                              (at ((h:real^N->real^N) y)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `\z. lift((f:real^N->real) z)`;
                   `(h:real^N->real^N) y`; `vec 0:real^N`]
           LRG_SMOOTH_FRECHET_DIFFERENTIABLE) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `U':real^N->bool`; `h:real^N->real^N`;
                 `h':real^N->real^N`; `f:real^N->real`; `y:real^N`]
         LRG_COMPOSE_DERIV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REWRITE_TAC[lgrad2; mpullback] THEN
  MATCH_MP_TAC LRG_CONTRACT_CONGRUENCE THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC LRG_DIFFEO_JACOBIAN_INVERTIBLE THEN
    MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `U':real^N->bool`;
                          `h':real^N->real^N`] THEN
    ASM_REWRITE_TAC[];
    ASM_MESON_TAC[LRG_METRIC_INVERTIBLE];
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[LRG_DROP_LINEAR_MATRIX] THEN
  REWRITE_TAC[GSYM SUM_RMUL] THEN REWRITE_TAC[GSYM SUM_LMUL] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `p:num` THEN STRIP_TAC THEN
  BETA_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `q:num` THEN STRIP_TAC THEN
  BETA_TAC THEN REAL_ARITH_TAC);;

let LLAP_PULLBACK = prove
 (`!U U' (h:real^N->real^N) h' G f y.
        metric_field U G /\ diffeomorphism_on U' U h h' /\
        smooth_map_on U (\z. lift(f z)) /\ y IN U'
        ==> llap (mpullback h G) (f o h) y = llap G f (h y)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `U':real^N->bool`; `h:real^N->real^N`;
                 `h':real^N->real^N`; `y:real^N`] LRG_DIFFEO_DERIV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(REWRITE_RULE[diffeomorphism_on]
    (ASSUME `diffeomorphism_on (U':real^N->bool) U (h:real^N->real^N) h'`)) THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `f:real^N->real`] LRG_DF_TENSOR_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `smooth_map_on U' (\z. lift(((f:real^N->real) o (h:real^N->real^N)) z))`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `(\z. lift(((f:real^N->real) o (h:real^N->real^N)) z)) =
      (\z. lift(f z)) o h`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[SUBSET_REFL];
    ALL_TAC] THEN
  (* the differential of f o h is the pullback of the differential of f *)
  SUBGOAL_THEN
   `!z u. z IN U'
          ==> drop(frechet_derivative
                    (\w. lift(((f:real^N->real) o (h:real^N->real^N)) w))
                    (at z) (u 1)) =
              ltpullback h
                (\z u. drop(frechet_derivative (\w. lift(f w)) (at z) (u 1)))
                z u`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[ltpullback] THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `U':real^N->bool`; `h:real^N->real^N`;
                   `h':real^N->real^N`; `f:real^N->real`; `z:real^N`]
           LRG_COMPOSE_DERIV) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  (* hence the Hessians correspond *)
  SUBGOAL_THEN
   `!u. lnabla 1 (mpullback h G)
          (\z u. drop(frechet_derivative
                       (\w. lift(((f:real^N->real) o (h:real^N->real^N)) w))
                       (at z) (u 1))) y u =
        lnabla 1 (G:real^N->real^N^N)
          (\z u. drop(frechet_derivative (\w. lift(f w)) (at z) (u 1))) (h y)
          (\m. frechet_derivative h (at y) (u m))`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC
     `lnabla 1 (mpullback h G)
        (ltpullback (h:real^N->real^N)
          (\z u. drop(frechet_derivative (\w. lift((f:real^N->real) w))
                                         (at z) (u 1)))) y u` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LRG_LNABLA_LOCAL THEN EXISTS_TAC `U':real^N->bool` THEN
      ASM_REWRITE_TAC[] THEN BETA_TAC THEN ASM_SIMP_TAC[];
      MP_TAC(BETA_RULE(ISPECL
        [`1`; `U:real^N->bool`; `U':real^N->bool`; `h:real^N->real^N`;
         `h':real^N->real^N`; `G:real^N->real^N^N`;
         `\z u. drop(frechet_derivative (\w. lift((f:real^N->real) w))
                                        (at z) ((u:num->real^N) 1))`;
         `y:real^N`; `u:num->real^N`] LNABLA_PULLBACK)) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[ltpullback]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ltensor_field 2 U
      (lnabla 1 (G:real^N->real^N^N)
        (\z u. drop(frechet_derivative (\w. lift((f:real^N->real) w))
                                       (at z) (u 1))))`
  ASSUME_TAC THENL
   [MP_TAC(BETA_RULE(ISPECL
      [`1`; `U:real^N->bool`; `G:real^N->real^N^N`;
       `\z u. drop(frechet_derivative (\w. lift((f:real^N->real) w))
                                      (at z) ((u:num->real^N) 1))`]
      LNABLA_TENSOR_FIELD)) THEN
    ASM_REWRITE_TAC[ARITH] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U':real^N->bool`; `mpullback (h:real^N->real^N) G`;
                 `(f:real^N->real) o (h:real^N->real^N)`; `y:real^N`]
         LRG_LLAP_LNABLA) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `f:real^N->real`;
                 `(h:real^N->real^N) y`] LRG_LLAP_LNABLA) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[mpullback] THEN
  MATCH_MP_TAC LRG_CONTRACT_CONGRUENCE THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC LRG_DIFFEO_JACOBIAN_INVERTIBLE THEN
    MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `U':real^N->bool`;
                          `h':real^N->real^N`] THEN
    ASM_REWRITE_TAC[];
    ASM_MESON_TAC[LRG_METRIC_INVERTIBLE];
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN REWRITE_TAC[COND_RAND] THEN
  MP_TAC(ISPECL
    [`U:real^N->bool`;
     `lnabla 1 (G:real^N->real^N^N)
        (\z u. drop(frechet_derivative (\w. lift((f:real^N->real) w))
                                       (at z) (u 1)))`;
     `(h:real^N->real^N) y`;
     `frechet_derivative (h:real^N->real^N) (at y) (basis i)`;
     `frechet_derivative (h:real^N->real^N) (at y) (basis j)`]
    LRG_TENSOR2_EXPAND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_SIMP_TAC[MATRIX_COMPONENT]);;

