(* ========================================================================= *)
(* Unit pc_p2c_cgglue (Part 2C, used in the pc_p2c_cg route): the limit      *)
(* chart system of a subsequence.  Jet bounds of the normal coordinate       *)
(* metrics from their C^m distances to the flat metric, the pseudo-distance  *)
(* limit D, the limits of the metrics and of the transition maps, and the    *)
(* p2cl_system for pc_p2c_cglim.                                             *)
(* ========================================================================= *)

needs "src/pc_p2c_cgunif.ml";;
needs "src/pc_p2c_cgsub.ml";;
needs "src/pc_p2c_cglim.ml";;
needs "src/pc_p2a_lgeo2.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Flat covariant derivatives are iterated partials, and the                 *)
(* C^m distance to the flat metric bounds the jets of the metric.            *)
(* ------------------------------------------------------------------------- *)

let P2CG_FLAT_ITER_PARTIAL = prove
 (`!k U (tf:real^N->(num->real^N)->real).
     open U /\ ltensor_field k U tf /\ (!u. smooth_map_on U (\y. lift(tf y u)))
     ==> !L u0. ALL (\j. 1 <= j /\ j <= dimindex(:N)) L
                ==> ?p. (!m. 1 <= m /\ m <= k ==> p m = u0 m) /\
                        (!m. k < m /\ m <= k + LENGTH L
                             ==> ?j. 1 <= j /\ j <= dimindex(:N) /\ p m = basis j) /\
                        !y. y IN U
                            ==> iterated_partial L (\y. lift(tf y u0)) y =
                                lift(lnabla_iter k (LENGTH L) p2c_flat tf y p)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `tf:real^N->(num->real^N)->real`]
                P2C_FLAT_ITER_FIELD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "fit") THEN
  LIST_INDUCT_TAC THENL
   [X_GEN_TAC `u0:num->real^N` THEN DISCH_TAC THEN EXISTS_TAC `u0:num->real^N` THEN
    REWRITE_TAC[LENGTH; ADD_CLAUSES; iterated_partial; lnabla_iter; LIFT_DROP] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `u0:num->real^N` THEN REWRITE_TAC[ALL] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `u0:num->real^N`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:num->real^N` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `\m. if m = k + LENGTH(t:num list) + 1 then basis h else (p:num->real^N) m` THEN
  REWRITE_TAC[LENGTH] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `m:num` THEN STRIP_TAC THEN
    COND_CASES_TAC THENL [ASM_ARITH_TAC; ASM_SIMP_TAC[]];
    X_GEN_TAC `m:num` THEN STRIP_TAC THEN COND_CASES_TAC THENL
     [EXISTS_TAC `h:num` THEN ASM_REWRITE_TAC[];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
  REWRITE_TAC[iterated_partial; lnabla_iter; partial_derivative] THEN
  ABBREV_TAC `p' = \m. if m = k + LENGTH(t:num list) + 1 then basis h else (p:num->real^N) m` THEN
  SUBGOAL_THEN
   `!z. z IN U
        ==> lnabla_iter k (LENGTH(t:num list)) p2c_flat (tf:real^N->(num->real^N)->real) z p' =
            lnabla_iter k (LENGTH t) p2c_flat tf z p`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
    USE_THEN "fit" (MP_TAC o SPEC `LENGTH(t:num list)`) THEN
    DISCH_THEN(MP_TAC o CONJUNCT1) THEN REWRITE_TAC[ltensor_field] THEN
    DISCH_THEN(MP_TAC o SPEC `z:real^N`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN
    X_GEN_TAC `m:num` THEN STRIP_TAC THEN EXPAND_TAC "p'" THEN REWRITE_TAC[] THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k + LENGTH(t:num list)`; `U:real^N->bool`;
                 `lnabla_iter k (LENGTH(t:num list)) p2c_flat (tf:real^N->(num->real^N)->real)`;
                 `y:real^N`; `p':num->real^N`] P2C_FLAT_LNABLA) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    USE_THEN "fit" (MP_TAC o SPEC `LENGTH(t:num list)`) THEN SIMP_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[LIFT_DROP; ARITH_RULE `(k + l) + 1 = k + l + 1`] THEN
  SUBGOAL_THEN `(p':num->real^N) (k + LENGTH(t:num list) + 1) = basis h` SUBST1_TAC THENL
   [EXPAND_TAC "p'" THEN REWRITE_TAC[]; ALL_TAC] THEN
  AP_THM_TAC THEN MATCH_MP_TAC GEOI_FRECHET_DERIVATIVE_LOCAL THEN
  EXISTS_TAC `U:real^N->bool` THEN ASM_SIMP_TAC[]);;

(* A single squared component of a flat iterated derivative is bounded by   *)
(* its flat tensor norm, and hence by the C^m distance.                      *)

let P2CG_LCK_PARTIAL = prove
 (`!U (G:real^N->real^N^N) m L u0 y.
     open U /\ metric_field U G /\ y IN U /\
     ALL (\j. 1 <= j /\ j <= dimindex(:N)) L /\ LENGTH L <= m /\
     (!i. 1 <= i /\ i <= 2 ==> ?j. 1 <= j /\ j <= dimindex(:N) /\ u0 i = basis j)
     ==> (drop(iterated_partial L
                (\z. lift(lmetric2 G z u0 - lmetric2 p2c_flat z u0)) y)) pow 2
         <= lck_dist2 m p2c_flat G y`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `p2c_flat:real^N->real^N^N`; `G:real^N->real^N^N`]
                LRG_LMETRIC2_DIFF_FIELD) THEN
  ASM_SIMP_TAC[P2C_FLAT_METRIC_FIELD] THEN STRIP_TAC THEN
  ABBREV_TAC `tf = \z u. lmetric2 (G:real^N->real^N^N) z u - lmetric2 p2c_flat z u` THEN
  SUBGOAL_THEN `!u. smooth_map_on U (\y. lift((tf:real^N->(num->real^N)->real) y u))`
  ASSUME_TAC THENL [EXPAND_TAC "tf" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`2`; `U:real^N->bool`; `tf:real^N->(num->real^N)->real`]
                P2CG_FLAT_ITER_PARTIAL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPECL [`L:num list`; `u0:num->real^N`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:num->real^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(\z. lift(lmetric2 (G:real^N->real^N^N) z u0 - lmetric2 p2c_flat z u0)) =
                (\z. lift((tf:real^N->(num->real^N)->real) z u0))`
  SUBST1_TAC THENL [EXPAND_TAC "tf" THEN REWRITE_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[LIFT_DROP] THEN
  MP_TAC(ISPECL [`2`; `U:real^N->bool`; `tf:real^N->(num->real^N)->real`]
                P2C_FLAT_ITER_FIELD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `LENGTH(L:num list)`) THEN
  STRIP_TAC THEN
  ABBREV_TAC `T2 = lnabla_iter 2 (LENGTH(L:num list)) p2c_flat (tf:real^N->(num->real^N)->real)` THEN
  SUBGOAL_THEN
   `?q. q IN index_tuples (2 + LENGTH(L:num list)) (:N) /\
        !i. 1 <= i /\ i <= 2 + LENGTH L ==> (p:num->real^N) i = basis(q i)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `!i. 1 <= i /\ i <= 2 + LENGTH(L:num list)
                      ==> ?j. 1 <= j /\ j <= dimindex(:N) /\ (p:num->real^N) i = basis j`
    MP_TAC THENL
     [X_GEN_TAC `i:num` THEN STRIP_TAC THEN ASM_CASES_TAC `i <= 2` THENL
       [ASM_SIMP_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC];
      ALL_TAC] THEN
    GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV) [RIGHT_IMP_EXISTS_THM] THEN
    REWRITE_TAC[SKOLEM_THM] THEN DISCH_THEN(X_CHOOSE_TAC `jf:num->num`) THEN
    EXISTS_TAC `\i. if 1 <= i /\ i <= 2 + LENGTH(L:num list) then (jf:num->num) i else 0` THEN
    REWRITE_TAC[index_tuples; IN_ELIM_THM] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(T2:real^N->(num->real^N)->real) y p = T2 y (\m. basis(q m))`
  SUBST1_TAC THENL
   [UNDISCH_TAC `ltensor_field (2 + LENGTH(L:num list)) U
                   (T2:real^N->(num->real^N)->real)` THEN
    REWRITE_TAC[ltensor_field] THEN DISCH_THEN(MP_TAC o SPEC `y:real^N`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  TRANS_TAC REAL_LE_TRANS `ltnorm2 (2 + LENGTH(L:num list)) p2c_flat T2 (y:real^N)` THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`2 + LENGTH(L:num list)`; `U:real^N->bool`;
                   `T2:real^N->(num->real^N)->real`; `y:real^N`] P2C_FLAT_LTNORM2) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    MP_TAC(ISPECL [`{q:num->num}`; `index_tuples (2 + LENGTH(L:num list)) (:N)`;
                   `\p:num->num. ((T2:real^N->(num->real^N)->real) y (\m. basis(p m))) pow 2`]
                  SUM_SUBSET_SIMPLE) THEN
    REWRITE_TAC[SUM_SING; LRG_INDEX_TUPLES_FINITE; SING_SUBSET] THEN
    ASM_REWRITE_TAC[REAL_LE_POW_2];
    ALL_TAC] THEN
  REWRITE_TAC[lck_dist2] THEN
  MP_TAC(ISPECL [`{LENGTH(L:num list)}`; `0..m`;
                 `\l. ltnorm2 (2 + l) p2c_flat
                        (lnabla_iter 2 l p2c_flat
                           (\z u. lmetric2 (G:real^N->real^N^N) z u - lmetric2 p2c_flat z u)) y`]
                SUM_SUBSET_SIMPLE) THEN
  REWRITE_TAC[SUM_SING; FINITE_NUMSEG; SING_SUBSET; IN_NUMSEG; LE_0] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  X_GEN_TAC `l:num` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`2 + l`; `U:real^N->bool`;
                 `lnabla_iter 2 l p2c_flat (tf:real^N->(num->real^N)->real)`; `y:real^N`]
                P2C_FLAT_LTNORM2) THEN
  MP_TAC(ISPECL [`2`; `U:real^N->bool`; `tf:real^N->(num->real^N)->real`]
                P2C_FLAT_ITER_FIELD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `l:num`) THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC SUM_POS_LE THEN REWRITE_TAC[LRG_INDEX_TUPLES_FINITE; REAL_LE_POW_2]);;

let P2CG_ENTRY_PARTIAL = prove
 (`!U (G:real^N->real^N^N) m L a b y.
     open U /\ metric_field U G /\ y IN U /\
     ALL (\j. 1 <= j /\ j <= dimindex(:N)) L /\ LENGTH L <= m /\
     1 <= a /\ a <= dimindex(:N) /\ 1 <= b /\ b <= dimindex(:N)
     ==> norm(iterated_partial L (\z. lift(G z$a$b)) y) <=
         sqrt(lck_dist2 m p2c_flat G y) + &1`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `u0 = \i. if i = 1 then basis a else basis b:real^N` THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `p2c_flat:real^N->real^N^N`; `G:real^N->real^N^N`]
                LRG_LMETRIC2_DIFF_FIELD) THEN
  ASM_SIMP_TAC[P2C_FLAT_METRIC_FIELD] THEN DISCH_THEN(MP_TAC o SPEC `u0:num->real^N` o CONJUNCT2) THEN
  REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `!z. lmetric2 (G:real^N->real^N^N) z u0 = G z$a$b /\
                    lmetric2 p2c_flat z u0 = if (a:num) = (b:num) then &1 else &0`
  MP_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "u0" THEN
    ASM_SIMP_TAC[lmetric2; p2c_flat; ARITH_RULE `~(2 = 1)`; MATRIX_VECTOR_MUL_LID;
                 MATRIX_VECTOR_MUL_BASIS; DOT_BASIS; BASIS_COMPONENT; column; LAMBDA_BETA];
    DISCH_THEN(LABEL_TAC "lm")] THEN
  SUBGOAL_THEN
   `(\z. lift((G:real^N->real^N^N) z$a$b)) =
    (\z. lift(lmetric2 G z u0 - lmetric2 p2c_flat z u0) +
         lift(if (a:num) = (b:num) then &1 else &0))`
  SUBST1_TAC THENL
   [ASM_REWRITE_TAC[FUN_EQ_THM; GSYM LIFT_ADD; REAL_ARITH `x - d + d:real = x`];
    REMOVE_THEN "lm" (K ALL_TAC)] THEN
  MP_TAC(ISPECL [`L:num list`; `U:real^N->bool`;
                 `\z. lift(lmetric2 (G:real^N->real^N^N) z u0 - lmetric2 p2c_flat z u0)`;
                 `\z:real^N. lift(if (a:num) = (b:num) then &1 else &0)`] PDE_ITERATED_PARTIAL_ADD_OPEN) THEN
  ASM_REWRITE_TAC[SMOOTH_MAP_ON_CONST] THEN DISCH_THEN(MP_TAC o SPEC `y:real^N`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[P2CT_ITERATED_PARTIAL_CONST] THEN
  MATCH_MP_TAC(NORM_ARITH `norm(x:real^1) <= a /\ norm(y:real^1) <= &1 ==> norm(x + y) <= a + &1`) THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `m:num`; `L:num list`;
                   `u0:num->real^N`; `y:real^N`] P2CG_LCK_PARTIAL) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN EXPAND_TAC "u0" THEN
      COND_CASES_TAC THENL [EXISTS_TAC `a:num`; EXISTS_TAC `b:num`] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_TAC THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM LIFT_DROP] THEN REWRITE_TAC[NORM_LIFT] THEN
    MATCH_MP_TAC REAL_LE_RSQRT THEN REWRITE_TAC[REAL_POW2_ABS] THEN FIRST_ASSUM ACCEPT_TAC;
    COND_CASES_TAC THEN REWRITE_TAC[NORM_0; REAL_POS; NORM_LIFT] THEN
    COND_CASES_TAC THEN REAL_ARITH_TAC]);;

let P2CG_LCK_JETN = prove
 (`!U (G:real^N->real^N^N) m B y.
     open U /\ metric_field U G /\ y IN U /\ lck_dist2 m p2c_flat G y <= B
     ==> pde_jetn m ((vectorize:real^N^N->real^(N,N)finite_prod) o G) y <=
         &(CARD(pde_index_lists m (:N))) * &(dimindex(:(N,N)finite_prod)) *
         (sqrt(abs B) + &1)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pde_jetn] THEN
  MATCH_MP_TAC SUM_BOUND THEN REWRITE_TAC[PDE_INDEX_LISTS_FINITE] THEN
  X_GEN_TAC `L:num list` THEN REWRITE_TAC[pde_index_lists; IN_ELIM_THM] THEN STRIP_TAC THEN
  W(MP_TAC o PART_MATCH lhand NORM_LE_L1 o lhand o snd) THEN
  MATCH_MP_TAC(REAL_ARITH `b <= c ==> a <= b ==> a <= c`) THEN
  GEN_REWRITE_TAC (RAND_CONV o LAND_CONV o RAND_CONV) [GSYM CARD_NUMSEG_1] THEN
  MATCH_MP_TAC SUM_BOUND THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  X_GEN_TAC `q:num` THEN STRIP_TAC THEN
  SUBGOAL_THEN `metric_field U (G:real^N->real^N^N)` MP_TAC THENL
   [ASM_REWRITE_TAC[]; REWRITE_TAC[metric_field] THEN STRIP_TAC] THEN
  MP_TAC(ISPECL [`L:num list`; `\v:real^(N,N)finite_prod. lift(v$q)`;
                 `(vectorize:real^N^N->real^(N,N)finite_prod) o (G:real^N->real^N^N)`;
                 `U:real^N->bool`; `y:real^N`] PDE_ITERATED_PARTIAL_LINEAR_COMPOSE) THEN
  ASM_REWRITE_TAC[LINEAR_LIFT_COMPONENT; o_THM] THEN
  DISCH_THEN(MP_TAC o AP_TERM `norm:real^1->real`) THEN REWRITE_TAC[NORM_LIFT] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[DIMINDEX_FINITE_PROD]) THEN
  ASM_SIMP_TAC[VECTORIZE_COMPONENT] THEN
  TRANS_TAC REAL_LE_TRANS `sqrt(lck_dist2 m p2c_flat (G:real^N->real^N^N) y) + &1` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC P2CG_ENTRY_PARTIAL THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~(dimindex(:N) = 0)` MP_TAC THENL [REWRITE_TAC[DIMINDEX_NONZERO]; ALL_TAC] THEN
    DISCH_TAC THEN ASM_SIMP_TAC[ARITH_RULE `1 <= 1 + n`; ARITH_RULE `1 + a <= n <=> a < n`;
                                RDIV_LT_EQ; MOD_LT_EQ] THEN
    ASM_ARITH_TAC;
    REWRITE_TAC[REAL_LE_RADD] THEN MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* metric-side estimates for transitions: the inverse of a                   *)
(* metric with G >= 1/2 has bounded entries, and an isometry between metrics *)
(* with G <= 2 and H >= 1/2 has partial derivatives of norm at most 2.       *)
(* ------------------------------------------------------------------------- *)

let P2CG_GINV_VEC = prove
 (`!U (G:real^N->real^N^N) z.
     metric_field U G /\ z IN U /\ (!a. inv(&2) * (a dot a) <= a dot (G z ** a))
     ==> norm((vectorize:real^N^N->real^(N,N)finite_prod) (matrix_inv(G z))) <=
         &2 * &(dimindex(:(N,N)finite_prod))`,
  REPEAT STRIP_TAC THEN
  W(MP_TAC o PART_MATCH lhand NORM_LE_L1 o lhand o snd) THEN
  MATCH_MP_TAC(REAL_ARITH `b <= c ==> a <= b ==> a <= c`) THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV o RAND_CONV) [GSYM CARD_NUMSEG_1] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  MATCH_MP_TAC SUM_BOUND THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  X_GEN_TAC `q:num` THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[DIMINDEX_FINITE_PROD]) THEN
  ASM_SIMP_TAC[VECTORIZE_COMPONENT] THEN
  ABBREV_TAC `a = 1 + (q - 1) DIV dimindex(:N)` THEN
  ABBREV_TAC `b = 1 + (q - 1) MOD dimindex(:N)` THEN
  SUBGOAL_THEN `1 <= a /\ a <= dimindex(:N) /\ 1 <= b /\ b <= dimindex(:N)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["a"; "b"] THEN
    SUBGOAL_THEN `~(dimindex(:N) = 0)` MP_TAC THENL [REWRITE_TAC[DIMINDEX_NONZERO]; ALL_TAC] THEN
    DISCH_TAC THEN ASM_SIMP_TAC[ARITH_RULE `1 <= 1 + n`; ARITH_RULE `1 + a <= n <=> a < n`;
                                RDIV_LT_EQ; MOD_LT_EQ] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `z:real^N`] P2C_GINV_NORM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `basis b:real^N`) THEN
  ASM_SIMP_TAC[NORM_BASIS; MATRIX_VECTOR_MUL_BASIS] THEN
  MP_TAC(ISPECL [`column b (matrix_inv((G:real^N->real^N^N) z))`; `a:num`] COMPONENT_LE_NORM) THEN
  ASM_SIMP_TAC[column; LAMBDA_BETA] THEN REAL_ARITH_TAC);;

let P2CG_ISOM_DT_BOUND = prove
 (`!(Tm:real^N->real^N) G H z.
     G z = mpullback Tm H z /\ Tm differentiable at z /\
     (!a. a dot (G z ** a) <= &2 * (a dot a)) /\
     (!a. inv(&2) * (a dot a) <= a dot (H (Tm z) ** a))
     ==> !i. 1 <= i /\ i <= dimindex(:N) ==> norm(partial_derivative i Tm z) <= &2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  REWRITE_TAC[partial_derivative] THEN
  ABBREV_TAC `v = frechet_derivative (Tm:real^N->real^N) (at z) (basis i)` THEN
  SUBGOAL_THEN `basis i dot ((G:real^N->real^N^N) z ** basis i) =
                v dot ((H:real^N->real^N^N) (Tm z) ** v)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN EXPAND_TAC "v" THEN MATCH_MP_TAC LRG_MPULLBACK_DOT THEN
    UNDISCH_TAC `(Tm:real^N->real^N) differentiable at z` THEN
    REWRITE_TAC[FRECHET_DERIVATIVE_WORKS] THEN
    DISCH_THEN(ACCEPT_TAC o CONJUNCT1 o REWRITE_RULE[has_derivative]);
    ALL_TAC] THEN
  SUBGOAL_THEN `basis i dot basis i:real^N = &1` ASSUME_TAC THENL
   [ASM_SIMP_TAC[DOT_BASIS; BASIS_COMPONENT]; ALL_TAC] THEN
  SUBGOAL_THEN `(v:real^N) dot v <= &4` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `v:real^N` o check (fun th -> can (find_term ((=) `H:real^N->real^N^N`)) (concl th))) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `basis i:real^N` o check (fun th -> can (find_term ((=) `G:real^N->real^N^N`)) (concl th) && is_forall(concl th))) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[vector_norm] THEN MATCH_MP_TAC REAL_LE_LSQRT THEN
  ASM_REWRITE_TAC[DOT_POS_LE] THEN ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Transitions between two normal charts.  On an open set V of               *)
(* the first chart whose image lies in the second injectivity ball, the      *)
(* transition p2cg_trans is a diffeomorphism onto its image and pulls the    *)
(* second exp metric back to the first.                                       *)
(* ------------------------------------------------------------------------- *)

let p2cg_trans = new_definition
 `p2cg_trans (top:A topology,atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N)
             (y1:A) (E1:real^N^N) (y2:A) (E2:real^N^N) (r2:real) (z:real^N) =
    @w. w IN ball(vec 0,r2) /\
        mfd_exp (top,atlas) g y2 (E2 ** w) = mfd_exp (top,atlas) g y1 (E1 ** z)`;;

let P2CG_PARAM_CHART_DIFF = prove
 (`!top atlas s (e:real^N->A) c w.
     smooth_manifold_atlas top atlas /\ mfd_param top atlas s e /\
     c IN atlas /\ w IN s /\ e w IN FST c
     ==> (\x. SND c (e x)) differentiable at w`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `s:real^N->bool`; `e:real^N->A`] GRGD_PARAM_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e':A->real^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `open {x | x IN s /\ (e:real^N->A) x IN FST(c:(A->bool)#(A->real^N))}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC OPEN_IN_OPEN_TRANS THEN EXISTS_TAC `s:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`e:real^N->A`; `subtopology euclidean (s:real^N->bool)`; `top:A topology`;
                   `FST(c:(A->bool)#(A->real^N))`] OPEN_IN_CONTINUOUS_MAP_PREIMAGE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[SMOOTH_MANIFOLD_ATLAS_CHART; PAIR];
      REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; TOPSPACE_EUCLIDEAN; INTER_UNIV]];
    ALL_TAC] THEN
  UNDISCH_TAC `mfd_smooth_map (open_set_atlas s) (atlas:((A->bool)#(A->real^N))->bool) s
                              (e:real^N->A)` THEN
  REWRITE_TAC[mfd_smooth_map] THEN
  DISCH_THEN(MP_TAC o SPECL [`(s:real^N->bool,(\x:real^N. x))`;
                             `c:(A->bool)#(A->real^N)`]) THEN
  ASM_REWRITE_TAC[open_set_atlas; IN_SING; FST; SND; IMAGE_ID; INTER_IDEMPOT] THEN
  DISCH_TAC THEN MATCH_MP_TAC DIFFERENTIABLE_TRANSFORM_AT THEN
  EXISTS_TAC `SND(c:(A->bool)#(A->real^N)) o (e:real^N->A) o chart_inv (s,(\x:real^N. x))` THEN
  FIRST_ASSUM(MP_TAC o SPEC `w:real^N` o GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL]) THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:real^N) IN s` ASSUME_TAC THENL
     [UNDISCH_TAC `ball(w:real^N,d) SUBSET
                    {x | x IN s /\ (e:real^N->A) x IN FST(c:(A->bool)#(A->real^N))}` THEN
      REWRITE_TAC[SUBSET; IN_BALL; IN_ELIM_THM] THEN
      DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN ASM_MESON_TAC[DIST_SYM];
      ASM_SIMP_TAC[o_THM; MFDM_CHART_INV_ID]];
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `{x | x IN s /\ (e:real^N->A) x IN FST(c:(A->bool)#(A->real^N))}` THEN
    ASM_REWRITE_TAC[IN_ELIM_THM]]);;

let P2CG_MPULLBACK_LOCAL = prove
 (`!(h:real^N->real^N) h' (G:real^N->real^N^N) s z.
     open s /\ z IN s /\ (!w. w IN s ==> h w = h' w)
     ==> mpullback h G z = mpullback h' G z`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mpullback] THEN
  SUBGOAL_THEN `frechet_derivative (h:real^N->real^N) (at z) = frechet_derivative h' (at z)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC GEOI_FRECHET_DERIVATIVE_LOCAL THEN EXISTS_TAC `s:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[]]);;

let P2CG_DIFFEO_EQ = prove
 (`!s t (f:real^N->real^N) g f'.
     diffeomorphism_on s t f g /\ (!x. x IN s ==> f' x = f x)
     ==> IMAGE f' s = t /\ diffeomorphism_on s t f' g`,
  REPEAT GEN_TAC THEN REWRITE_TAC[diffeomorphism_on] THEN STRIP_TAC THEN
  SUBGOAL_THEN `IMAGE (f':real^N->real^N) s = t` ASSUME_TAC THENL
   [UNDISCH_TAC `IMAGE (f:real^N->real^N) s = t` THEN ASM SET_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[];
    X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(g:real^N->real^N) y IN s` ASSUME_TAC THENL [ASM SET_TAC[]; ASM_SIMP_TAC[]];
    MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN EXISTS_TAC `f:real^N->real^N` THEN ASM_SIMP_TAC[]]);;

let P2CG_MPULLBACK_PT = prove
 (`!(h:real^N->real^N) G G' z.
     G(h z) = G'(h z) ==> mpullback h G z = mpullback h G' z`,
  SIMP_TAC[mpullback]);;

let P2CG_PULLBACK_CHAIN = prove
 (`!(atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) (e1:real^N->A) e2 T12
    (G1:real^N->real^N^N) G2 V z.
     open V /\ z IN V /\
     (!w. w IN V ==> e2 (T12 w) = e1 w) /\
     T12 differentiable at z /\
     (SND(chart_at atlas (e1 z)) o e2) differentiable at (T12 z) /\
     G1 z = mpullback (SND(chart_at atlas (e1 z)) o e1)
                      (metric_local atlas (chart_at atlas (e1 z)) g) z /\
     G2 (T12 z) = mpullback (SND(chart_at atlas (e1 z)) o e2)
                            (metric_local atlas (chart_at atlas (e1 z)) g) (T12 z)
     ==> G1 z = mpullback T12 G2 z`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^N))->bool) ((e1:real^N->A) z)` THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`T12:real^N->real^N`; `G2:real^N->real^N^N`;
                 `mpullback (SND(c:(A->bool)#(A->real^N)) o (e2:real^N->A))
                            (metric_local (atlas:((A->bool)#(A->real^N))->bool) c (g:A->real^N^N))`;
                 `z:real^N`] P2CG_MPULLBACK_PT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`T12:real^N->real^N`; `SND(c:(A->bool)#(A->real^N)) o (e2:real^N->A)`;
                 `metric_local (atlas:((A->bool)#(A->real^N))->bool) c (g:A->real^N^N)`;
                 `z:real^N`] P2A_MPULLBACK_COMPOSE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC P2CG_MPULLBACK_LOCAL THEN EXISTS_TAC `V:real^N->bool` THEN
  ASM_SIMP_TAC[o_THM]);;

let P2CG_TRANS_PACKAGE = prove
 (`!top atlas (g:A->real^N^N) y1 E1 r1 K1 y2 E2 r2 K2 V.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     y1 IN topspace top /\ mfd_orthonormal_frame g y1 E1 /\ mfd_inj_ball (top,atlas) g y1 r1 /\
     y2 IN topspace top /\ mfd_orthonormal_frame g y2 E2 /\ mfd_inj_ball (top,atlas) g y2 r2 /\
     &0 < r1 /\ &0 < r2 /\ &0 <= K1 /\ K1 * r1 pow 2 <= &1 /\
     &0 <= K2 /\ K2 * r2 pow 2 <= &1 /\
     (!z. z IN mfd_ball (top,atlas) g y1 r1 ==> mfd_rm_norm atlas g z <= K1) /\
     (!z. z IN mfd_ball (top,atlas) g y2 r2 ==> mfd_rm_norm atlas g z <= K2) /\
     open V /\ V SUBSET ball(vec 0,r1) /\
     (!z. z IN V ==> mfd_exp (top,atlas) g y1 (E1 ** z) IN mfd_ball (top,atlas) g y2 r2)
     ==> (?Ti. diffeomorphism_on V (IMAGE (p2cg_trans (top,atlas) g y1 E1 y2 E2 r2) V)
                                   (p2cg_trans (top,atlas) g y1 E1 y2 E2 r2) Ti) /\
         IMAGE (p2cg_trans (top,atlas) g y1 E1 y2 E2 r2) V SUBSET ball(vec 0,r2) /\
         (!z. z IN V
              ==> mfd_exp (top,atlas) g y2 (E2 ** p2cg_trans (top,atlas) g y1 E1 y2 E2 r2 z) =
                  mfd_exp (top,atlas) g y1 (E1 ** z)) /\
         (!z. z IN V
              ==> cmp_expmetric (top,atlas) g y1 E1 z =
                  mpullback (p2cg_trans (top,atlas) g y1 E1 y2 E2 r2)
                            (cmp_expmetric (top,atlas) g y2 E2) z)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `e1 = \w:real^N. mfd_exp (top,atlas) (g:A->real^N^N) y1 ((E1:real^N^N) ** w)` THEN
  ABBREV_TAC `e2 = \w:real^N. mfd_exp (top,atlas) (g:A->real^N^N) y2 ((E2:real^N^N) ** w)` THEN
  ABBREV_TAC `T12 = p2cg_trans (top,atlas) (g:A->real^N^N) y1 E1 y2 E2 r2` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `y1:A`; `E1:real^N^N`; `r1:real`] P2CU_NCH_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "par1") (CONJUNCTS_THEN2 (LABEL_TAC "img1")
    (CONJUNCTS_THEN2 (K ALL_TAC) (K ALL_TAC)))) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `y2:A`; `E2:real^N^N`; `r2:real`] P2CU_NCH_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "par2") (CONJUNCTS_THEN2 (LABEL_TAC "img2")
    (CONJUNCTS_THEN2 (K ALL_TAC) (LABEL_TAC "inj2")))) THEN
  USE_THEN "par1" (MP_TAC o REWRITE_RULE[mfd_param]) THEN
  DISCH_THEN(X_CHOOSE_THEN `e1':A->real^N` (LABEL_TAC "d1")) THEN
  USE_THEN "par2" (MP_TAC o REWRITE_RULE[mfd_param]) THEN
  DISCH_THEN(X_CHOOSE_THEN `e2':A->real^N` (LABEL_TAC "d2")) THEN
  SUBGOAL_THEN `smooth_manifold_atlas euclidean (open_set_atlas (:real^N))` ASSUME_TAC THENL
   [MP_TAC(ISPEC `(:real^N)` OPEN_SET_ATLAS) THEN REWRITE_TAC[OPEN_UNIV; SUBTOPOLOGY_UNIV];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`euclidean:(real^N)topology`; `open_set_atlas(:real^N)`; `ball(vec 0:real^N,r1)`;
                 `top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `IMAGE (e1:real^N->A) (ball(vec 0,r1))`; `e1:real^N->A`; `e1':A->real^N`;
                 `V:real^N->bool`] MFD_DIFFEO_RESTRICT) THEN
  ASM_REWRITE_TAC[GSYM OPEN_IN] THEN DISCH_TAC THEN
  SUBGOAL_THEN `open_in top (IMAGE (e1:real^N->A) V)` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [mfd_diffeo]) THEN SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (e1:real^N->A) V SUBSET IMAGE (e2:real^N->A) (ball(vec 0:real^N,r2))` ASSUME_TAC THENL
   [USE_THEN "img2" (fun th -> REWRITE_TAC[th]) THEN EXPAND_TAC "e1" THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  USE_THEN "d2" (MP_TAC o MATCH_MP MFD_DIFFEO_SYM) THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `IMAGE (e2:real^N->A) (ball(vec 0,r2))`;
                 `euclidean:(real^N)topology`; `open_set_atlas(:real^N)`; `ball(vec 0:real^N,r2)`;
                 `e2':A->real^N`; `e2:real^N->A`; `IMAGE (e1:real^N->A) V`] MFD_DIFFEO_RESTRICT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`euclidean:(real^N)topology`; `open_set_atlas(:real^N)`; `V:real^N->bool`;
                 `top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `IMAGE (e1:real^N->A) V`;
                 `euclidean:(real^N)topology`; `open_set_atlas(:real^N)`;
                 `IMAGE (e2':A->real^N) (IMAGE (e1:real^N->A) V)`;
                 `e1:real^N->A`; `e1':A->real^N`; `e2':A->real^N`; `e2:real^N->A`]
                MFD_DIFFEO_COMPOSE) THEN
  ASM_REWRITE_TAC[MFD_DIFFEO_EUCLIDEAN] THEN DISCH_TAC THEN
  USE_THEN "d2" (STRIP_ASSUME_TAC o MATCH_MP MFD_DIFFEO_MAPS) THEN
  SUBGOAL_THEN `!z. z IN V ==> (T12:real^N->real^N) z = e2'((e1:real^N->A) z) /\
                               e2'(e1 z) IN ball(vec 0,r2) /\ (e2:real^N->A)(e2'(e1 z)) = e1 z`
  (LABEL_TAC "T") THENL
   [X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(e1:real^N->A) z IN IMAGE (e2:real^N->A) (ball(vec 0,r2))` ASSUME_TAC THENL
     [UNDISCH_TAC `IMAGE (e1:real^N->A) V SUBSET IMAGE (e2:real^N->A) (ball(vec 0:real^N,r2))` THEN
      ASM SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(e2':A->real^N) ((e1:real^N->A) z) IN ball(vec 0,r2) /\
                  (e2:real^N->A)(e2'(e1 z)) = e1 z` STRIP_ASSUME_TAC THENL
     [ASM SET_TAC[]; ASM_REWRITE_TAC[]] THEN
    EXPAND_TAC "T12" THEN REWRITE_TAC[p2cg_trans] THEN
    MATCH_MP_TAC SELECT_UNIQUE THEN X_GEN_TAC `w:real^N` THEN
    UNDISCH_TAC `(e2:real^N->A)(e2'((e1:real^N->A) z)) = e1 z` THEN
    MAP_EVERY EXPAND_TAC ["e1"; "e2"] THEN REWRITE_TAC[] THEN DISCH_TAC THEN
    EQ_TAC THENL [ALL_TAC; DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN
                           UNDISCH_TAC `(e2':A->real^N)((e1:real^N->A) z) IN ball(vec 0,r2)` THEN
                           EXPAND_TAC "e1" THEN REWRITE_TAC[]] THEN
    STRIP_TAC THEN USE_THEN "inj2" MATCH_MP_TAC THEN
    UNDISCH_TAC `(e2':A->real^N)((e1:real^N->A) z) IN ball(vec 0,r2)` THEN
    EXPAND_TAC "e1" THEN REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IN_BALL_0]) THEN REWRITE_TAC[IN_BALL_0] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!w. w IN V ==> (e2:real^N->A) ((T12:real^N->real^N) w) = (e1:real^N->A) w`
  (LABEL_TAC "eT") THENL
   [X_GEN_TAC `w:real^N` THEN DISCH_TAC THEN
    USE_THEN "T" (STRIP_ASSUME_TAC o C MP (ASSUME `(w:real^N) IN V`) o SPEC `w:real^N`) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:real^N->bool`; `IMAGE (e2':A->real^N) (IMAGE (e1:real^N->A) V)`;
                 `(e2':A->real^N) o (e1:real^N->A)`; `(e1':A->real^N) o (e2:real^N->A)`;
                 `T12:real^N->real^N`] P2CG_DIFFEO_EQ) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[o_THM];
    STRIP_TAC] THEN
  REPEAT CONJ_TAC THENL
   [EXISTS_TAC `(e1':A->real^N) o (e2:real^N->A)` THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM_SIMP_TAC[];
    X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
    USE_THEN "eT" (MP_TAC o C MP (ASSUME `(z:real^N) IN V`) o SPEC `z:real^N`) THEN
    MAP_EVERY EXPAND_TAC ["e1"; "e2"] THEN SIMP_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
  USE_THEN "eT" (ASSUME_TAC o C MP (ASSUME `(z:real^N) IN V`) o SPEC `z:real^N`) THEN
  USE_THEN "T" (STRIP_ASSUME_TAC o C MP (ASSUME `(z:real^N) IN V`) o SPEC `z:real^N`) THEN
  SUBGOAL_THEN `(z:real^N) IN ball(vec 0,r1)` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(T12:real^N->real^N) z IN ball(vec 0,r2)` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(e1:real^N->A) z IN topspace top` ASSUME_TAC THENL
   [UNDISCH_TAC `open_in top (IMAGE (e1:real^N->A) V)` THEN
    DISCH_THEN(MP_TAC o MATCH_MP OPEN_IN_SUBSET) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `(e1:real^N->A) z`]
                CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC P2CG_PULLBACK_CHAIN THEN
  MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                        `e1:real^N->A`; `e2:real^N->A`; `V:real^N->bool`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `V:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[diffeomorphism_on];
    REWRITE_TAC[o_DEF] THEN MATCH_MP_TAC P2CG_PARAM_CHART_DIFF THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                          `ball(vec 0:real^N,r2)`] THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "par2" ACCEPT_TAC;
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `y1:A`; `E1:real^N^N`; `r1:real`; `K1:real`]
                  P2CU_EXPMETRIC_FACTS) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `z:real^N` o last o CONJUNCTS) THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "e1" THEN SIMP_TAC[];
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `y2:A`; `E2:real^N^N`; `r2:real`; `K2:real`]
                  P2CU_EXPMETRIC_FACTS) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `(T12:real^N->real^N) z` o last o CONJUNCTS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `(e2:real^N->A) ((T12:real^N->real^N) z) = (e1:real^N->A) z` THEN
    MAP_EVERY EXPAND_TAC ["e1"; "e2"] THEN
    UNDISCH_TAC `(T12:real^N->real^N) z = e2'((e1:real^N->A) z)` THEN
    EXPAND_TAC "e1" THEN DISCH_THEN(SUBST1_TAC o SYM) THEN SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Level data.  For every level j: a radius rho j < 1 and a                  *)
(* curvature bound K j with K j rho j^2 <= 1 valid on balls B(y,rho j) for   *)
(* y in B(x k,j + 3) (eventually), C^m bounds of the normal coordinate      *)
(* metrics there, and nets yc j k s of B(x k,j + 1) with spacing rho j / 8.  *)
(* ------------------------------------------------------------------------- *)

let p2cg_levels = new_definition
 `p2cg_levels (top:num->A topology) (atlas:num->((A->bool)#(A->real^3))->bool)
              (h:num->A->real^3^3) (x:num->A) (rho:num->real) (K:num->real)
              (N0:num->num) (B:num->num->real) (NB:num->num->num) (P:num->num)
              (Nn:num->num) (yc:num->num->num->A) <=>
           (!j. &0 < rho j /\ rho j < &1 /\ &0 <= K j /\ K j * rho j pow 2 <= &1) /\
           (!j k y. N0 j <= k /\ y IN mfd_ball (top k,atlas k) (h k) (x k) (&j + &3)
                    ==> mfd_inj_ball (top k,atlas k) (h k) y (rho j) /\
                        (!z. z IN mfd_ball (top k,atlas k) (h k) y (rho j)
                             ==> mfd_rm_norm (atlas k) (h k) z <= K j)) /\
           (!j m k y E. NB j m <= k /\ y IN mfd_ball (top k,atlas k) (h k) (x k) (&j + &3) /\
                        mfd_orthonormal_frame (h k) y E
                        ==> metric_field (ball(vec 0,rho j))
                              (cmp_expmetric (top k,atlas k) (h k) y E) /\
                            !w. norm w < rho j / &2
                                ==> lck_dist2 m (\z. mat 1)
                                      (cmp_expmetric (top k,atlas k) (h k) y E) w <= B j m) /\
           (!j k. Nn j <= k
                  ==> yc j k 0 = x k /\
                      (!s. yc j k s IN mfd_ball (top k,atlas k) (h k) (x k) (&j + &1)) /\
                      (!p. p IN mfd_ball (top k,atlas k) (h k) (x k) (&j + &1)
                           ==> ?s. s < P j /\
                                   mfd_dist (top k,atlas k) (h k) (yc j k s) p < rho j / &8))`;;

let P2CG_LEVELS = prove
 (`!top atlas (h:num->A->real^3^3) x.
     P2C_REQ_CGT_STATEMENT (:A) /\ p2cu_seq top atlas h x
     ==> ?rho K N0 B NB P Nn yc. p2cg_levels top atlas h x rho K N0 B NB P Nn yc`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!j. ?rho K N0. &0 < rho /\ rho < &1 /\ &0 <= K /\ K * rho pow 2 <= &1 /\
          (!k y. N0 <= k /\ y IN mfd_ball ((top:num->A topology) k,atlas k) ((h:num->A->real^3^3) k)
                                           ((x:num->A) k) (&j + &3)
                 ==> mfd_inj_ball (top k,atlas k) (h k) y rho /\
                     (!z. z IN mfd_ball (top k,atlas k) (h k) y rho
                          ==> mfd_rm_norm (atlas k) (h k) z <= K)) /\
          !m. ?B N. !k y E. N <= k /\ y IN mfd_ball (top k,atlas k) (h k) (x k) (&j + &3) /\
                            mfd_orthonormal_frame (h k) y E
                            ==> metric_field (ball(vec 0,rho))
                                  (cmp_expmetric (top k,atlas k) (h k) y E) /\
                                !w. norm w < rho / &2
                                    ==> lck_dist2 m (\z. mat 1)
                                          (cmp_expmetric (top k,atlas k) (h k) y E) w <= B`
  MP_TAC THENL
   [X_GEN_TAC `j:num` THEN MATCH_MP_TAC P2CU_CHARTS THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `rho:num->real` (X_CHOOSE_THEN `K:num->real`
    (X_CHOOSE_THEN `N0:num->num` (LABEL_TAC "ch")))) THEN
  SUBGOAL_THEN
   `!j. ?P Nn. !k. Nn <= k
                   ==> ?y. y 0 = (x:num->A) k /\
                           (!s. y s IN mfd_ball ((top:num->A topology) k,atlas k) ((h:num->A->real^3^3) k)
                                                (x k) (&j + &1)) /\
                           (!p. p IN mfd_ball (top k,atlas k) (h k) (x k) (&j + &1)
                                ==> ?s. s < P /\
                                        mfd_dist (top k,atlas k) (h k) (y s) p <
                                        (rho:num->real) j / &8)`
  MP_TAC THENL
   [X_GEN_TAC `j:num` THEN MATCH_MP_TAC P2CU_NET THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "ch" (MP_TAC o SPEC `j:num`) THEN STRIP_TAC THEN
    CONJ_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `P:num->num` (X_CHOOSE_THEN `Nn:num->num` (LABEL_TAC "net"))) THEN
  USE_THEN "ch" (MP_TAC o GEN `j:num` o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o
                 CONJUNCT2 o SPEC `j:num`) THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:num->num->real` (X_CHOOSE_THEN `NB:num->num->num` (LABEL_TAC "bd"))) THEN
  USE_THEN "net" (MP_TAC o REWRITE_RULE[SKOLEM_THM] o
                  GEN_REWRITE_RULE (BINDER_CONV o BINDER_CONV) [RIGHT_IMP_EXISTS_THM]) THEN
  DISCH_THEN(X_CHOOSE_THEN `yc:num->num->num->A` (LABEL_TAC "yc")) THEN
  MAP_EVERY EXISTS_TAC [`rho:num->real`; `K:num->real`; `N0:num->num`; `B:num->num->real`;
                        `NB:num->num->num`; `P:num->num`; `Nn:num->num`;
                        `yc:num->num->num->A`] THEN
  REWRITE_TAC[p2cg_levels] THEN REPEAT CONJ_TAC THENL
   [GEN_TAC THEN USE_THEN "ch" (MP_TAC o SPEC `j:num`) THEN SIMP_TAC[];
    REPEAT GEN_TAC THEN USE_THEN "ch" (MP_TAC o SPEC `j:num`) THEN
    DISCH_THEN(ACCEPT_TAC o SPECL [`k:num`; `y:A`] o
               CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2);
    REPEAT GEN_TAC THEN DISCH_TAC THEN USE_THEN "bd" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    REPEAT GEN_TAC THEN DISCH_TAC THEN USE_THEN "yc" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The charts of the sequence.  Chart a has level NUMFST a and               *)
(* net index NUMSND a; centre yc (NUMFST a) k (NUMSND a), an orthonormal     *)
(* frame there, radius rho(NUMFST a), and the normal map p2cg_nch.  Chart    *)
(* facts hold from the index p2cg_nv a on.                                    *)
(* ------------------------------------------------------------------------- *)

let p2cg_ctr = new_definition
 `p2cg_ctr (yc:num->num->num->A) k a = yc (NUMFST a) k (NUMSND a)`;;

let p2cg_frm = new_definition
 `p2cg_frm (h:num->A->real^3^3) (yc:num->num->num->A) k a =
    @E:real^3^3. mfd_orthonormal_frame (h k) (p2cg_ctr yc k a) E`;;

let p2cg_nch = new_definition
 `p2cg_nch (top:num->A topology) (atlas:num->((A->bool)#(A->real^3))->bool)
           (h:num->A->real^3^3) (yc:num->num->num->A) k a (w:real^3) =
    mfd_exp (top k,atlas k) (h k) (p2cg_ctr yc k a) (p2cg_frm h yc k a ** w)`;;

let p2cg_nv = new_definition
 `p2cg_nv (N0:num->num) (Nn:num->num) a = N0 (NUMFST a) + Nn (NUMFST a)`;;

(* The facts about a chart from p2cg_nv a on. *)

let P2CG_CHART_OK = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc a k.
     p2cu_seq top atlas h x /\ p2cg_levels top atlas h x rho K N0 B NB P Nn yc /\
     p2cg_nv N0 Nn a <= k
     ==> p2cg_ctr yc k a IN mfd_ball (top k,atlas k) (h k) (x k) (&(NUMFST a) + &1) /\
         p2cg_ctr yc k a IN topspace(top k) /\
         mfd_orthonormal_frame (h k) (p2cg_ctr yc k a) (p2cg_frm h yc k a) /\
         mfd_inj_ball (top k,atlas k) (h k) (p2cg_ctr yc k a) (rho(NUMFST a)) /\
         (!z. z IN mfd_ball (top k,atlas k) (h k) (p2cg_ctr yc k a) (rho(NUMFST a))
              ==> mfd_rm_norm (atlas k) (h k) z <= K(NUMFST a)) /\
         (!w. norm w < rho(NUMFST a)
              ==> p2cg_nch top atlas h yc k a w IN
                  mfd_ball (top k,atlas k) (h k) (x k) (&(NUMFST a) + &2))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2cg_levels; p2cg_nv] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o SPEC `k:num` o CONJUNCT1 o GEN_REWRITE_RULE I [p2cu_seq]) THEN
  SUBGOAL_THEN `p2cg_ctr (yc:num->num->num->A) k a IN mfd_ball ((top:num->A topology) k,
                                             (atlas:num->((A->bool)#(A->real^3))->bool) k)
                                   ((h:num->A->real^3^3) k) ((x:num->A) k) (&(NUMFST a) + &1)`
  ASSUME_TAC THENL
   [REWRITE_TAC[p2cg_ctr] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`NUMFST a`; `k:num`] o
                  check (fun th -> can (find_term ((=) `yc:num->num->num->A`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `p2cg_ctr (yc:num->num->num->A) k a IN topspace((top:num->A topology) k)` ASSUME_TAC THENL
   [ASM_MESON_TAC[P2CU_BALL_SUBSET; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `mfd_orthonormal_frame ((h:num->A->real^3^3) k) (p2cg_ctr yc k a)
                  (p2cg_frm (h:num->A->real^3^3) (yc:num->num->num->A) k a)` ASSUME_TAC THENL
   [REWRITE_TAC[p2cg_frm] THEN CONV_TAC SELECT_CONV THEN
    MATCH_MP_TAC P2CU_FRAME_EXISTS THEN
    MAP_EVERY EXISTS_TAC [`(top:num->A topology) k`;
                          `(atlas:num->((A->bool)#(A->real^3))->bool) k`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_inj_ball ((top:num->A topology) k,(atlas:num->((A->bool)#(A->real^3))->bool) k)
                 ((h:num->A->real^3^3) k) (p2cg_ctr (yc:num->num->num->A) k a) (rho(NUMFST a)) /\
    (!z. z IN mfd_ball (top k,atlas k) (h k) (p2cg_ctr yc k a) (rho(NUMFST a))
         ==> mfd_rm_norm (atlas k) (h k) z <= K(NUMFST a))`
  STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (find_term (fun t -> is_const t &&
       fst(dest_const t) = "mfd_inj_ball")) (concl th))) THEN
    CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC(SET_RULE `!x:A s t. x IN s /\ s SUBSET t ==> x IN t`) THEN
    EXISTS_TAC `mfd_ball ((top:num->A topology) k,(atlas:num->((A->bool)#(A->real^3))->bool) k)
                         ((h:num->A->real^3^3) k) ((x:num->A) k) (&(NUMFST a) + &1)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P2CU_BALL_MONO THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`(top:num->A topology) k`; `(atlas:num->((A->bool)#(A->real^3))->bool) k`;
                 `(h:num->A->real^3^3) k`; `p2cg_ctr (yc:num->num->num->A) k a`; `p2cg_frm (h:num->A->real^3^3) (yc:num->num->num->A) k a`;
                 `rho(NUMFST a):real`] P2CU_NCH_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `w:real^3` o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN REWRITE_TAC[p2cg_nch] THEN
  MATCH_MP_TAC(SET_RULE `!x:A s t. x IN s /\ s SUBSET t ==> x IN t`) THEN
  EXISTS_TAC `mfd_ball ((top:num->A topology) k,(atlas:num->((A->bool)#(A->real^3))->bool) k)
                       ((h:num->A->real^3^3) k) (p2cg_ctr (yc:num->num->num->A) k a) (rho(NUMFST a))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN ASM_REWRITE_TAC[];
    TRANS_TAC SUBSET_TRANS
     `mfd_ball ((top:num->A topology) k,(atlas:num->((A->bool)#(A->real^3))->bool) k)
               ((h:num->A->real^3^3) k) ((x:num->A) k) ((&(NUMFST a) + &1) + rho(NUMFST a))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC P2CU_BALL_SHIFT THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC P2CU_BALL_MONO THEN
      SUBGOAL_THEN `(rho:num->real)(NUMFST a) < &1` MP_TAC THENL
       [ASM_MESON_TAC[]; REAL_ARITH_TAC]]]);;

(* Distances between pairs of points. *)

let P2CG_DIST4 = prove
 (`!top atlas (g:A->real^N^N) p q p' q'.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_joinable (top,atlas) p q /\ mfd_joinable (top,atlas) p p' /\
     mfd_joinable (top,atlas) q q'
     ==> abs(mfd_dist (top,atlas) g p q - mfd_dist (top,atlas) g p' q') <=
         mfd_dist (top,atlas) g p p' + mfd_dist (top,atlas) g q q'`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `mfd_joinable (top,atlas:((A->bool)#(A->real^N))->bool) p' q /\
                mfd_joinable (top,atlas) p' q' /\ mfd_joinable (top,atlas) p' p /\
                mfd_joinable (top,atlas) q' q /\ mfd_joinable (top,atlas) p q'`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[MFD_JOINABLE_SYM; MFD_JOINABLE_TRANS]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `p:A`; `p':A`; `q:A`] MFD_DIST_TRIANGLE) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `p':A`; `q':A`; `q:A`] MFD_DIST_TRIANGLE) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `p':A`; `p:A`; `q':A`] MFD_DIST_TRIANGLE) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `p:A`; `q:A`; `q':A`] MFD_DIST_TRIANGLE) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `p:A`; `p':A`] MFD_DIST_SYM) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `q:A`; `q':A`] MFD_DIST_SYM) THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The pseudo-distance limit D.  The functions                               *)
(* (z,w) |-> d_k(E_{k,a} z, E_{k,b} w) on cball(0,rho_a/2) x cball(0,rho_b/2)  *)
(* are bounded and uniformly Lipschitz from p2cg_nv a + p2cg_nv b on, so a   *)
(* subsequence converges uniformly for all pairs (a,b) (P2CS_AA_DIAG_GEN).   *)
(* ------------------------------------------------------------------------- *)

let p2cg_df = new_definition
 `p2cg_df (top:num->A topology) (atlas:num->((A->bool)#(A->real^3))->bool)
          (h:num->A->real^3^3) (yc:num->num->num->A) k (ab:num#num)
          (v:real^(3,3)finite_sum) =
    lift(mfd_dist (top k,atlas k) (h k) (p2cg_nch top atlas h yc k (FST ab) (fstcart v))
                                        (p2cg_nch top atlas h yc k (SND ab) (sndcart v)))`;;

let p2cg_dsq = new_definition
 `p2cg_dsq (rho:num->real) (ab:num#num) =
    cball(vec 0:real^3,rho(NUMFST(FST ab)) / &2) PCROSS
    cball(vec 0:real^3,rho(NUMFST(SND ab)) / &2)`;;

let P2CG_IN_PCROSS = prove
 (`!s t (v:real^(M,N)finite_sum). v IN s PCROSS t <=> fstcart v IN s /\ sndcart v IN t`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `v:real^(M,N)finite_sum` PASTECART_FST_SND) THEN
  DISCH_THEN(fun th -> GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [GSYM th]) THEN
  REWRITE_TAC[PASTECART_IN_PCROSS]);;

let P2CG_SQRT2_LT = prove
 (`sqrt(&2) < &3 / &2`,
  MATCH_MP_TAC REAL_LT_LSQRT THEN REAL_ARITH_TAC);;

(* Two points of a chart image, and their joinability to the base point. *)

let P2CG_NCH_FACTS = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc a k w.
     p2cu_seq top atlas h x /\ p2cg_levels top atlas h x rho K N0 B NB P Nn yc /\
     p2cg_nv N0 Nn a <= k /\ norm w < rho(NUMFST a)
     ==> mfd_joinable (top k,atlas k) (x k) (p2cg_nch top atlas h yc k a w) /\
         mfd_dist (top k,atlas k) (h k) (x k) (p2cg_nch top atlas h yc k a w) <
         &(NUMFST a) + &2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:num->A topology`; `atlas:num->((A->bool)#(A->real^3))->bool`;
                 `h:num->A->real^3^3`; `x:num->A`; `rho:num->real`; `K:num->real`;
                 `N0:num->num`; `B:num->num->real`; `NB:num->num->num`; `P:num->num`;
                 `Nn:num->num`; `yc:num->num->num->A`; `a:num`; `k:num`] P2CG_CHART_OK) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `w:real^3` o last o CONJUNCTS) THEN
  ASM_REWRITE_TAC[mfd_ball; IN_ELIM_THM]);;

let P2CG_DF_BOUND = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc ab k v.
     p2cu_seq top atlas h x /\ p2cg_levels top atlas h x rho K N0 B NB P Nn yc /\
     p2cg_nv N0 Nn (FST ab) + p2cg_nv N0 Nn (SND ab) <= k /\ v IN p2cg_dsq rho ab
     ==> norm(p2cg_df top atlas h yc k ab v) <=
         &(NUMFST(FST ab)) + &(NUMFST(SND ab)) + &6`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2cg_dsq; p2cg_df; NORM_LIFT] THEN
  REWRITE_TAC[P2CG_IN_PCROSS; IN_CBALL_0] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o SPEC `k:num` o CONJUNCT1 o GEN_REWRITE_RULE I [p2cu_seq]) THEN
  SUBGOAL_THEN `!j. &0 < (rho:num->real) j /\ rho j < &1` ASSUME_TAC THENL
   [UNDISCH_TAC `p2cg_levels (top:num->A topology) atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc` THEN
    REWRITE_TAC[p2cg_levels] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:num->A topology`; `atlas:num->((A->bool)#(A->real^3))->bool`;
                 `h:num->A->real^3^3`; `x:num->A`; `rho:num->real`; `K:num->real`;
                 `N0:num->num`; `B:num->num->real`; `NB:num->num->num`; `P:num->num`;
                 `Nn:num->num`; `yc:num->num->num->A`; `FST(ab:num#num)`; `k:num`;
                 `fstcart(v:real^(3,3)finite_sum)`] P2CG_NCH_FACTS) THEN
  MP_TAC(ISPECL [`top:num->A topology`; `atlas:num->((A->bool)#(A->real^3))->bool`;
                 `h:num->A->real^3^3`; `x:num->A`; `rho:num->real`; `K:num->real`;
                 `N0:num->num`; `B:num->num->real`; `NB:num->num->num`; `P:num->num`;
                 `Nn:num->num`; `yc:num->num->num->A`; `SND(ab:num#num)`; `k:num`;
                 `sndcart(v:real^(3,3)finite_sum)`] P2CG_NCH_FACTS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `NUMFST(SND(ab:num#num))`) THEN
    UNDISCH_TAC `norm(sndcart(v:real^(3,3)finite_sum)) <= rho(NUMFST(SND(ab:num#num))) / &2` THEN
    REAL_ARITH_TAC;
    STRIP_TAC] THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `NUMFST(FST(ab:num#num))`) THEN
    UNDISCH_TAC `norm(fstcart(v:real^(3,3)finite_sum)) <= rho(NUMFST(FST(ab:num#num))) / &2` THEN
    REAL_ARITH_TAC;
    STRIP_TAC] THEN
  ABBREV_TAC `p = p2cg_nch (top:num->A topology) atlas (h:num->A->real^3^3) yc k (FST(ab:num#num))
                    (fstcart(v:real^(3,3)finite_sum))` THEN
  ABBREV_TAC `q = p2cg_nch (top:num->A topology) atlas (h:num->A->real^3^3) yc k (SND(ab:num#num))
                    (sndcart(v:real^(3,3)finite_sum))` THEN
  MP_TAC(ISPECL [`(top:num->A topology) k`; `(atlas:num->((A->bool)#(A->real^3))->bool) k`;
                 `(h:num->A->real^3^3) k`; `p:A`; `(x:num->A) k`; `q:A`] MFD_DIST_TRIANGLE) THEN
  MP_TAC(ISPECL [`(top:num->A topology) k`; `(atlas:num->((A->bool)#(A->real^3))->bool) k`;
                 `(h:num->A->real^3^3) k`; `(x:num->A) k`; `p:A`] MFD_DIST_SYM) THEN
  MP_TAC(ISPECL [`(top:num->A topology) k`; `(atlas:num->((A->bool)#(A->real^3))->bool) k`;
                 `(h:num->A->real^3^3) k`; `p:A`; `q:A`] MFD_DIST_POS_LE) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `mfd_joinable ((top:num->A topology) k,(atlas:num->((A->bool)#(A->real^3))->bool) k)
                  p (x k) /\ mfd_joinable (top k,atlas k) p q` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MFD_JOINABLE_SYM; MFD_JOINABLE_TRANS]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let P2CG_NCH_LIP = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc a k w1 w2.
     p2cu_seq top atlas h x /\ p2cg_levels top atlas h x rho K N0 B NB P Nn yc /\
     p2cg_nv N0 Nn a <= k /\ norm w1 < rho(NUMFST a) /\ norm w2 < rho(NUMFST a)
     ==> mfd_joinable (top k,atlas k) (p2cg_nch top atlas h yc k a w1)
                                      (p2cg_nch top atlas h yc k a w2) /\
         mfd_dist (top k,atlas k) (h k) (p2cg_nch top atlas h yc k a w1)
                                        (p2cg_nch top atlas h yc k a w2)
         <= sqrt(&2) * norm(w1 - w2) /\
         (norm w1 < rho(NUMFST a) / &4 /\ norm w2 < rho(NUMFST a) / &4
          ==> norm(w1 - w2) <=
              sqrt(&2) * mfd_dist (top k,atlas k) (h k) (p2cg_nch top atlas h yc k a w1)
                                                       (p2cg_nch top atlas h yc k a w2))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:num->A topology`; `atlas:num->((A->bool)#(A->real^3))->bool`;
                 `h:num->A->real^3^3`; `x:num->A`; `rho:num->real`; `K:num->real`;
                 `N0:num->num`; `B:num->num->real`; `NB:num->num->num`; `P:num->num`;
                 `Nn:num->num`; `yc:num->num->num->A`; `a:num`; `k:num`] P2CG_CHART_OK) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o SPEC `k:num` o CONJUNCT1 o GEN_REWRITE_RULE I [p2cu_seq]) THEN
  SUBGOAL_THEN `&0 < (rho:num->real)(NUMFST a) /\ &0 <= (K:num->real)(NUMFST a) /\
                K(NUMFST a) * rho(NUMFST a) pow 2 <= &1` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `p2cg_levels (top:num->A topology) atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc` THEN
    REWRITE_TAC[p2cg_levels] THEN SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[p2cg_nch] THEN
  MATCH_MP_TAC(TAUT `(a /\ b) /\ c ==> a /\ b /\ c`) THEN CONJ_TAC THENL
   [MATCH_MP_TAC P2CU_NCH_LIP_UPPER THEN
    MAP_EVERY EXISTS_TAC [`rho(NUMFST a):real`; `K(NUMFST a):real`] THEN ASM_REWRITE_TAC[];
    STRIP_TAC THEN MATCH_MP_TAC P2CU_NCH_LIP_LOWER THEN
    MAP_EVERY EXISTS_TAC [`rho(NUMFST a):real`; `K(NUMFST a):real`] THEN ASM_REWRITE_TAC[]]);;

let P2CG_ARITH1 = prove
 (`!a b s x y n. a <= s * x /\ b <= s * y /\ x <= n /\ y <= n /\ &0 <= s /\ s < &3 / &2 /\
                 &0 <= n
                 ==> a + b <= &3 * n`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `s * x <= s * n /\ s * y <= s * n` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `s * n <= &3 / &2 * n` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let P2CG_DF_LIP = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc ab k v v'.
     p2cu_seq top atlas h x /\ p2cg_levels top atlas h x rho K N0 B NB P Nn yc /\
     p2cg_nv N0 Nn (FST ab) + p2cg_nv N0 Nn (SND ab) <= k /\
     v IN p2cg_dsq rho ab /\ v' IN p2cg_dsq rho ab
     ==> norm(p2cg_df top atlas h yc k ab v - p2cg_df top atlas h yc k ab v') <=
         &3 * norm(v - v')`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2cg_dsq; P2CG_IN_PCROSS; IN_CBALL_0] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o SPEC `k:num` o CONJUNCT1 o GEN_REWRITE_RULE I [p2cu_seq]) THEN
  SUBGOAL_THEN `!j. &0 < (rho:num->real) j` ASSUME_TAC THENL
   [UNDISCH_TAC `p2cg_levels (top:num->A topology) atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc` THEN
    REWRITE_TAC[p2cg_levels] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `p2cg_nv N0 Nn (FST(ab:num#num)) <= k /\ p2cg_nv N0 Nn (SND(ab:num#num)) <= k`
  STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `ra = (rho:num->real)(NUMFST(FST(ab:num#num)))` THEN
  ABBREV_TAC `rb = (rho:num->real)(NUMFST(SND(ab:num#num)))` THEN
  SUBGOAL_THEN `&0 < ra /\ &0 < rb` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["ra"; "rb"] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:num->A topology`; `atlas:num->((A->bool)#(A->real^3))->bool`;
                 `h:num->A->real^3^3`; `x:num->A`; `rho:num->real`; `K:num->real`;
                 `N0:num->num`; `B:num->num->real`; `NB:num->num->num`; `P:num->num`;
                 `Nn:num->num`; `yc:num->num->num->A`; `FST(ab:num#num)`; `k:num`;
                 `fstcart(v:real^(3,3)finite_sum)`; `fstcart(v':real^(3,3)finite_sum)`]
                P2CG_NCH_LIP) THEN
  MP_TAC(ISPECL [`top:num->A topology`; `atlas:num->((A->bool)#(A->real^3))->bool`;
                 `h:num->A->real^3^3`; `x:num->A`; `rho:num->real`; `K:num->real`;
                 `N0:num->num`; `B:num->num->real`; `NB:num->num->num`; `P:num->num`;
                 `Nn:num->num`; `yc:num->num->num->A`; `SND(ab:num#num)`; `k:num`;
                 `sndcart(v:real^(3,3)finite_sum)`; `sndcart(v':real^(3,3)finite_sum)`]
                P2CG_NCH_LIP) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(ISPECL [`top:num->A topology`; `atlas:num->((A->bool)#(A->real^3))->bool`;
                 `h:num->A->real^3^3`; `x:num->A`; `rho:num->real`; `K:num->real`;
                 `N0:num->num`; `B:num->num->real`; `NB:num->num->num`; `P:num->num`;
                 `Nn:num->num`; `yc:num->num->num->A`; `FST(ab:num#num)`; `k:num`;
                 `fstcart(v:real^(3,3)finite_sum)`] P2CG_NCH_FACTS) THEN
  MP_TAC(ISPECL [`top:num->A topology`; `atlas:num->((A->bool)#(A->real^3))->bool`;
                 `h:num->A->real^3^3`; `x:num->A`; `rho:num->real`; `K:num->real`;
                 `N0:num->num`; `B:num->num->real`; `NB:num->num->num`; `P:num->num`;
                 `Nn:num->num`; `yc:num->num->num->A`; `SND(ab:num#num)`; `k:num`;
                 `sndcart(v:real^(3,3)finite_sum)`] P2CG_NCH_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  REWRITE_TAC[p2cg_df; GSYM LIFT_SUB; NORM_LIFT] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) P2CG_DIST4 o lhand o snd) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[MFD_JOINABLE_SYM; MFD_JOINABLE_TRANS]; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `b <= c ==> a <= b ==> a <= c`) THEN
  MP_TAC(ISPEC `v - v':real^(3,3)finite_sum` NORM_FSTCART) THEN
  MP_TAC(ISPEC `v - v':real^(3,3)finite_sum` NORM_SNDCART) THEN
  REWRITE_TAC[FSTCART_SUB; SNDCART_SUB] THEN
  MP_TAC P2CG_SQRT2_LT THEN MP_TAC(SPEC `&2` SQRT_POS_LE) THEN REWRITE_TAC[REAL_POS] THEN
  REPEAT DISCH_TAC THEN
  MATCH_MP_TAC P2CG_ARITH1 THEN EXISTS_TAC `sqrt(&2)` THEN
  MAP_EVERY EXISTS_TAC
   [`norm(fstcart(v:real^(3,3)finite_sum) - fstcart(v':real^(3,3)finite_sum))`;
    `norm(sndcart(v:real^(3,3)finite_sum) - sndcart(v':real^(3,3)finite_sum))`] THEN
  ASM_REWRITE_TAC[NORM_POS_LE]);;

let P2CG_DLIM = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc.
     p2cu_seq top atlas h x /\ p2cg_levels top atlas h x rho K N0 B NB P Nn yc
     ==> ?s1 D. (!m n:num. m < n ==> s1 m < s1 n) /\
                !ab. D ab continuous_on p2cg_dsq rho ab /\
                     !e. &0 < e
                         ==> ?Kn. !n v. Kn <= n /\ v IN p2cg_dsq rho ab
                                        ==> norm(p2cg_df top atlas h yc (s1 n) ab v -
                                                 D ab v) < e`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`\ab k. p2cg_df (top:num->A topology) atlas (h:num->A->real^3^3) (yc:num->num->num->A) k ab`;
    `p2cg_dsq (rho:num->real)`;
    `\ab:num#num. &(NUMFST(FST ab)) + &(NUMFST(SND ab)) + &6`;
    `\ab:num#num. p2cg_nv (N0:num->num) (Nn:num->num) (FST ab) + p2cg_nv N0 Nn (SND ab)`]
   P2CS_AA_DIAG_GEN) THEN
  BETA_TAC THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REWRITE_TAC[GSYM CROSS_UNIV] THEN MATCH_MP_TAC COUNTABLE_CROSS THEN
      REWRITE_TAC[NUM_COUNTABLE];
      GEN_TAC THEN REWRITE_TAC[p2cg_dsq] THEN MATCH_MP_TAC COMPACT_PCROSS THEN
      REWRITE_TAC[COMPACT_CBALL];
      MAP_EVERY X_GEN_TAC [`ab:num#num`; `n:num`; `v:real^(3,3)finite_sum`] THEN STRIP_TAC THEN
      MATCH_MP_TAC P2CG_DF_BOUND THEN
      MAP_EVERY EXISTS_TAC [`x:num->A`; `rho:num->real`; `K:num->real`; `N0:num->num`;
                            `B:num->num->real`; `NB:num->num->num`; `P:num->num`;
                            `Nn:num->num`] THEN
      ASM_REWRITE_TAC[];
      MAP_EVERY X_GEN_TAC [`ab:num#num`; `v:real^(3,3)finite_sum`; `e:real`] THEN STRIP_TAC THEN
      EXISTS_TAC `e / &4` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MAP_EVERY X_GEN_TAC [`n:num`; `v':real^(3,3)finite_sum`] THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`top:num->A topology`; `atlas:num->((A->bool)#(A->real^3))->bool`;
                     `h:num->A->real^3^3`; `x:num->A`; `rho:num->real`; `K:num->real`;
                     `N0:num->num`; `B:num->num->real`; `NB:num->num->num`; `P:num->num`;
                     `Nn:num->num`; `yc:num->num->num->A`; `ab:num#num`; `n:num`;
                     `v:real^(3,3)finite_sum`; `v':real^(3,3)finite_sum`] P2CG_DF_LIP) THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `s1:num->num` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[SKOLEM_THM]) THEN
  DISCH_THEN(X_CHOOSE_TAC `D:num#num->real^(3,3)finite_sum->real^1`) THEN
  MAP_EVERY EXISTS_TAC [`s1:num->num`; `D:num#num->real^(3,3)finite_sum->real^1`] THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The metric limits.  The normal coordinate metrics p2cg_G of               *)
(* the charts have jet bounds of every order on ball(0,rho_a/2) (P2CG_LCK_    *)
(* JETN), so along a further subsequence they converge in C-infinity on      *)
(* ball(0,3 rho_a/8) (P2CS_JET_SUBSEQ).                                     *)
(* ------------------------------------------------------------------------- *)

let p2cg_G = new_definition
 `p2cg_G (top:num->A topology) (atlas:num->((A->bool)#(A->real^3))->bool)
         (h:num->A->real^3^3) (yc:num->num->num->A) k a =
    cmp_expmetric (top k,atlas k) (h k) (p2cg_ctr yc k a) (p2cg_frm h yc k a)`;;

let P2CG_G_FIELD = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc a k m.
     p2cu_seq top atlas h x /\ p2cg_levels top atlas h x rho K N0 B NB P Nn yc /\
     p2cg_nv N0 Nn a + NB (NUMFST a) m <= k
     ==> metric_field (ball(vec 0,rho(NUMFST a))) (p2cg_G top atlas h yc k a) /\
         !w. w IN ball(vec 0,rho(NUMFST a) / &2)
             ==> pde_jetn m ((vectorize:real^3^3->real^(3,3)finite_prod) o
                             p2cg_G top atlas h yc k a) w <=
                 &(CARD(pde_index_lists m (:3))) * &(dimindex(:(3,3)finite_prod)) *
                 (sqrt(abs(B (NUMFST a) m)) + &1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:num->A topology`; `atlas:num->((A->bool)#(A->real^3))->bool`;
                 `h:num->A->real^3^3`; `x:num->A`; `rho:num->real`; `K:num->real`;
                 `N0:num->num`; `B:num->num->real`; `NB:num->num->num`; `P:num->num`;
                 `Nn:num->num`; `yc:num->num->num->A`; `a:num`; `k:num`] P2CG_CHART_OK) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; STRIP_TAC] THEN
  UNDISCH_TAC `p2cg_levels (top:num->A topology) atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc` THEN
  REWRITE_TAC[p2cg_levels] THEN
  DISCH_THEN(MP_TAC o SPECL [`NUMFST a`; `m:num`; `k:num`;
                             `p2cg_ctr (yc:num->num->num->A) k a`;
                             `p2cg_frm (h:num->A->real^3^3) (yc:num->num->num->A) k a`] o
             CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC(SET_RULE `!x:A s t. x IN s /\ s SUBSET t ==> x IN t`) THEN
    EXISTS_TAC `mfd_ball ((top:num->A topology) k,(atlas:num->((A->bool)#(A->real^3))->bool) k)
                         ((h:num->A->real^3^3) k) ((x:num->A) k) (&(NUMFST a) + &1)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P2CU_BALL_MONO THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM p2cg_G] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `w:real^3` THEN REWRITE_TAC[IN_BALL_0] THEN DISCH_TAC THEN
  MATCH_MP_TAC P2CG_LCK_JETN THEN EXISTS_TAC `ball(vec 0:real^3,rho(NUMFST a))` THEN
  REWRITE_TAC[OPEN_BALL; IN_BALL_0; p2c_flat] THEN ASM_SIMP_TAC[] THEN
  SUBGOAL_THEN `&0 < (rho:num->real)(NUMFST a)` ASSUME_TAC THENL
   [MP_TAC(ISPEC `w:real^3` NORM_POS_LE) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* The normal coordinate metrics are uniformly equivalent to the flat one. *)

let P2CG_G_EQUIV = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc a k w v.
     p2cu_seq top atlas h x /\ p2cg_levels top atlas h x rho K N0 B NB P Nn yc /\
     p2cg_nv N0 Nn a <= k /\ norm w < rho(NUMFST a)
     ==> inv(&2) * norm v pow 2 <= v dot (p2cg_G top atlas h yc k a w ** v) /\
         v dot (p2cg_G top atlas h yc k a w ** v) <= &2 * norm v pow 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:num->A topology`; `atlas:num->((A->bool)#(A->real^3))->bool`;
                 `h:num->A->real^3^3`; `x:num->A`; `rho:num->real`; `K:num->real`;
                 `N0:num->num`; `B:num->num->real`; `NB:num->num->num`; `P:num->num`;
                 `Nn:num->num`; `yc:num->num->num->A`; `a:num`; `k:num`] P2CG_CHART_OK) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o SPEC `k:num` o CONJUNCT1 o GEN_REWRITE_RULE I [p2cu_seq]) THEN
  SUBGOAL_THEN `&0 < (rho:num->real)(NUMFST a) /\ &0 <= (K:num->real)(NUMFST a) /\
                K(NUMFST a) * rho(NUMFST a) pow 2 <= &1` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `p2cg_levels (top:num->A topology) atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc` THEN
    REWRITE_TAC[p2cg_levels] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(top:num->A topology) k`; `(atlas:num->((A->bool)#(A->real^3))->bool) k`;
                 `(h:num->A->real^3^3) k`; `p2cg_ctr (yc:num->num->num->A) k a`;
                 `p2cg_frm (h:num->A->real^3^3) (yc:num->num->num->A) k a`;
                 `(rho:num->real)(NUMFST a)`; `(K:num->real)(NUMFST a)`] P2CU_EXPMETRIC_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`w:real^3`; `v:real^3`] o
             CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
  ASM_REWRITE_TAC[p2cg_G]);;

(* Limits of symmetric matrices with uniform two-sided bounds. *)

let P2CG_MATRIX_LIMIT = prove
 (`!(Gs:num->real^N^N) G0 c1 c2.
     ((\n. vectorize(Gs n)) --> vectorize G0) sequentially /\
     (?N. !n. N <= n ==> transp(Gs n) = Gs n /\
                         !v. c1 * norm v pow 2 <= v dot (Gs n ** v) /\
                             v dot (Gs n ** v) <= c2 * norm v pow 2)
     ==> transp G0 = G0 /\
         !v. c1 * norm v pow 2 <= v dot (G0 ** v) /\ v dot (G0 ** v) <= c2 * norm v pow 2`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_TAC `N:num`)) THEN CONJ_TAC THENL
   [REWRITE_TAC[GSYM VECTORIZE_EQ] THEN
    MATCH_MP_TAC(ISPEC `sequentially` LIM_UNIQUE) THEN
    EXISTS_TAC `\n. vectorize(transp((Gs:num->real^N^N) n))` THEN
    REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`sequentially`; `vectorize o (transp:real^N^N->real^N^N) o matrify`;
                     `\n. vectorize((Gs:num->real^N^N) n)`; `vectorize(G0:real^N^N)`]
                    LIM_LINEAR) THEN
      ASM_REWRITE_TAC[LINEAR_TRANSP; o_THM; MATRIFY_VECTORIZE];
      MATCH_MP_TAC LIM_TRANSFORM_EVENTUALLY THEN
      EXISTS_TAC `\n. vectorize((Gs:num->real^N^N) n)` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `N:num` THEN ASM_SIMP_TAC[]];
    X_GEN_TAC `v:real^N` THEN
    SUBGOAL_THEN `((\n. lift(v dot ((Gs:num->real^N^N) n ** v))) --> lift(v dot (G0 ** v)))
                  sequentially` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`sequentially`;
                     `\y:real^(N,N)finite_prod. lift(v dot (matrify y ** v))`;
                     `\n. vectorize((Gs:num->real^N^N) n)`; `vectorize(G0:real^N^N)`]
                    LIM_LINEAR) THEN
      ASM_REWRITE_TAC[MATRIFY_VECTORIZE] THEN DISCH_THEN MATCH_MP_TAC THEN
      REWRITE_TAC[linear; MATRIFY_ADD; MATRIFY_CMUL; MATRIX_VECTOR_MUL_ADD_RDISTRIB;
                  MATRIX_VECTOR_LMUL; DOT_RADD; DOT_RMUL; LIFT_ADD; LIFT_CMUL];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`sequentially`; `\n. lift(v dot ((Gs:num->real^N^N) n ** v))`;
                     `lift(v dot ((G0:real^N^N) ** v))`; `c1 * norm(v:real^N) pow 2`]
                    LIM_DROP_LBOUND);
      MP_TAC(ISPECL [`sequentially`; `\n. lift(v dot ((Gs:num->real^N^N) n ** v))`;
                     `lift(v dot ((G0:real^N^N) ** v))`; `c2 * norm(v:real^N) pow 2`]
                    LIM_DROP_UBOUND)] THEN
    ASM_REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY; LIFT_DROP; EVENTUALLY_SEQUENTIALLY] THEN
    DISCH_THEN MATCH_MP_TAC THEN EXISTS_TAC `N:num` THEN ASM_SIMP_TAC[]]);;

(* The metric limits along a further subsequence of a given one. *)

let P2CG_GLIM = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc (s:num->num).
     p2cu_seq top atlas h x /\ p2cg_levels top atlas h x rho K N0 B NB P Nn yc /\
     (!m n:num. m < n ==> s m < s n)
     ==> ?s2 Gl. (!m n:num. m < n ==> s2 m < s2 n) /\
                 !a. metric_field (ball(vec 0,&3 * rho(NUMFST a) / &8)) (Gl a) /\
                     (!w v. w IN ball(vec 0,&3 * rho(NUMFST a) / &8)
                            ==> inv(&2) * norm v pow 2 <= v dot (Gl a w ** v) /\
                                v dot (Gl a w ** v) <= &2 * norm v pow 2) /\
                     !l. ALL (\j. 1 <= j /\ j <= dimindex(:3)) l
                         ==> !e. &0 < e
                                 ==> ?Kn. !n w. Kn <= n /\
                                                w IN ball(vec 0,&3 * rho(NUMFST a) / &8)
                                                ==> norm(iterated_partial l
                                                          ((vectorize:real^3^3->real^(3,3)finite_prod) o
                                                           p2cg_G top atlas h yc (s(s2 n)) a) w -
                                                         iterated_partial l (vectorize o Gl a) w)
                                                    < e`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!j. &0 < (rho:num->real) j` (LABEL_TAC "rho") THENL
   [UNDISCH_TAC `p2cg_levels (top:num->A topology) atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc` THEN
    REWRITE_TAC[p2cg_levels] THEN SIMP_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(LABEL_TAC "sbig" o MATCH_MP MONOTONE_BIGGER) THEN
  MP_TAC(ISPECL
   [`\a n. (vectorize:real^3^3->real^(3,3)finite_prod) o
           p2cg_G (top:num->A topology) atlas (h:num->A->real^3^3) (yc:num->num->num->A)
                  ((s:num->num) n) a`;
    `\a:num. ball(vec 0:real^3,(rho:num->real)(NUMFST a) / &2)`;
    `\a:num. vec 0:real^3`;
    `\a:num. &3 * (rho:num->real)(NUMFST a) / &8`] P2CS_JET_SUBSEQ) THEN
  BETA_TAC THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REWRITE_TAC[NUM_COUNTABLE];
      X_GEN_TAC `a:num` THEN REWRITE_TAC[OPEN_BALL; SUBSET; IN_CBALL_0; IN_BALL_0] THEN
      REMOVE_THEN "rho" (MP_TAC o SPEC `NUMFST a`) THEN REAL_ARITH_TAC;
      X_GEN_TAC `a:num` THEN
      EXISTS_TAC `p2cg_nv (N0:num->num) (Nn:num->num) a + (NB:num->num->num) (NUMFST a) 0` THEN
      X_GEN_TAC `n:num` THEN DISCH_TAC THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
      EXISTS_TAC `ball(vec 0:real^3,(rho:num->real)(NUMFST a))` THEN CONJ_TAC THENL
       [REWRITE_TAC[SUBSET; IN_BALL_0] THEN
        REMOVE_THEN "rho" (MP_TAC o SPEC `NUMFST a`) THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      MP_TAC(ISPECL [`top:num->A topology`; `atlas:num->((A->bool)#(A->real^3))->bool`;
                     `h:num->A->real^3^3`; `x:num->A`; `rho:num->real`; `K:num->real`;
                     `N0:num->num`; `B:num->num->real`; `NB:num->num->num`; `P:num->num`;
                     `Nn:num->num`; `yc:num->num->num->A`; `a:num`; `(s:num->num) n`; `0`]
                    P2CG_G_FIELD) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN REMOVE_THEN "sbig" (MP_TAC o SPEC `n:num`) THEN
        UNDISCH_TAC `p2cg_nv (N0:num->num) (Nn:num->num) a + (NB:num->num->num) (NUMFST a) 0 <= n` THEN
        ARITH_TAC;
        SIMP_TAC[metric_field]];
      MAP_EVERY X_GEN_TAC [`a:num`; `m:num`] THEN
      EXISTS_TAC `&(CARD(pde_index_lists m (:3))) * &(dimindex(:(3,3)finite_prod)) *
                  (sqrt(abs((B:num->num->real) (NUMFST a) m)) + &1)` THEN
      EXISTS_TAC `p2cg_nv (N0:num->num) (Nn:num->num) a + (NB:num->num->num) (NUMFST a) m` THEN
      MAP_EVERY X_GEN_TAC [`n:num`; `w:real^3`] THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`top:num->A topology`; `atlas:num->((A->bool)#(A->real^3))->bool`;
                     `h:num->A->real^3^3`; `x:num->A`; `rho:num->real`; `K:num->real`;
                     `N0:num->num`; `B:num->num->real`; `NB:num->num->num`; `P:num->num`;
                     `Nn:num->num`; `yc:num->num->num->A`; `a:num`; `(s:num->num) n`; `m:num`]
                    P2CG_G_FIELD) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN REMOVE_THEN "sbig" (MP_TAC o SPEC `n:num`) THEN
        UNDISCH_TAC `p2cg_nv (N0:num->num) (Nn:num->num) a + (NB:num->num->num) (NUMFST a) m <= n` THEN
        ARITH_TAC;
        DISCH_THEN(MP_TAC o SPEC `w:real^3` o CONJUNCT2) THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `s2:num->num`
    (X_CHOOSE_THEN `H:num->real^3->real^(3,3)finite_prod` STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM(LABEL_TAC "s2big" o MATCH_MP MONOTONE_BIGGER) THEN
  MAP_EVERY EXISTS_TAC
   [`s2:num->num`;
    `\a:num w:real^3. (matrify:real^(3,3)finite_prod->real^3^3)
                        ((H:num->real^3->real^(3,3)finite_prod) a w)`] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `a:num` THEN
  SUBGOAL_THEN `(vectorize:real^3^3->real^(3,3)finite_prod) o
                (\w:real^3. matrify((H:num->real^3->real^(3,3)finite_prod) a w)) = H a`
  (LABEL_TAC "vm") THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; VECTORIZE_MATRIFY]; ALL_TAC] THEN
  USE_THEN "vm" SUBST1_TAC THEN
  SUBGOAL_THEN
   `!w. w IN ball(vec 0:real^3,&3 * (rho:num->real)(NUMFST a) / &8)
        ==> transp(matrify((H:num->real^3->real^(3,3)finite_prod) a w)) = matrify(H a w) /\
            !v. inv(&2) * norm v pow 2 <= v dot (matrify(H a w) ** v) /\
                v dot (matrify(H a w) ** v) <= &2 * norm v pow 2`
  (LABEL_TAC "lim") THENL
   [X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN MATCH_MP_TAC P2CG_MATRIX_LIMIT THEN
    EXISTS_TAC `\n. p2cg_G (top:num->A topology) atlas (h:num->A->real^3^3)
                           (yc:num->num->num->A) ((s:num->num)((s2:num->num) n)) a w` THEN
    REWRITE_TAC[VECTORIZE_MATRIFY] THEN CONJ_TAC THENL
     [MP_TAC(ISPECL
       [`\n. (vectorize:real^3^3->real^(3,3)finite_prod) o
             p2cg_G (top:num->A topology) atlas (h:num->A->real^3^3) (yc:num->num->num->A)
                    ((s:num->num)((s2:num->num) n)) a`;
        `(H:num->real^3->real^(3,3)finite_prod) a`;
        `ball(vec 0:real^3,&3 * (rho:num->real)(NUMFST a) / &8)`; `w:real^3`] P2CS_UNIF_LIM) THEN
      ASM_REWRITE_TAC[o_THM] THEN DISCH_THEN MATCH_MP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `[]:num list` o CONJUNCT2 o SPEC `a:num`) THEN
      REWRITE_TAC[ALL; iterated_partial; o_THM];
      ALL_TAC] THEN
    EXISTS_TAC `p2cg_nv (N0:num->num) (Nn:num->num) a + (NB:num->num->num) (NUMFST a) 0` THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `p2cg_nv (N0:num->num) (Nn:num->num) a + (NB:num->num->num) (NUMFST a) 0 <=
                  (s:num->num)((s2:num->num) n)` ASSUME_TAC THENL
     [REMOVE_THEN "sbig" (MP_TAC o SPEC `(s2:num->num) n`) THEN
      REMOVE_THEN "s2big" (MP_TAC o SPEC `n:num`) THEN
      UNDISCH_TAC `p2cg_nv (N0:num->num) (Nn:num->num) a + (NB:num->num->num) (NUMFST a) 0 <= n` THEN
      ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `norm(w:real^3) < (rho:num->real)(NUMFST a)` ASSUME_TAC THENL
     [UNDISCH_TAC `w IN ball(vec 0:real^3,&3 * (rho:num->real)(NUMFST a) / &8)` THEN
      REWRITE_TAC[IN_BALL_0] THEN REMOVE_THEN "rho" (MP_TAC o SPEC `NUMFST a`) THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`top:num->A topology`; `atlas:num->((A->bool)#(A->real^3))->bool`;
                     `h:num->A->real^3^3`; `x:num->A`; `rho:num->real`; `K:num->real`;
                     `N0:num->num`; `B:num->num->real`; `NB:num->num->num`; `P:num->num`;
                     `Nn:num->num`; `yc:num->num->num->A`; `a:num`;
                     `(s:num->num)((s2:num->num) n)`; `0`] P2CG_G_FIELD) THEN
      ASM_REWRITE_TAC[metric_field] THEN
      DISCH_THEN(MP_TAC o SPEC `w:real^3` o last o CONJUNCTS o CONJUNCT1) THEN
      ASM_REWRITE_TAC[IN_BALL_0] THEN SIMP_TAC[];
      X_GEN_TAC `v:real^3` THEN MATCH_MP_TAC P2CG_G_EQUIV THEN
      MAP_EVERY EXISTS_TAC [`x:num->A`; `rho:num->real`; `K:num->real`; `N0:num->num`;
                            `B:num->num->real`; `NB:num->num->num`; `P:num->num`;
                            `Nn:num->num`] THEN
      ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[metric_field; OPEN_BALL] THEN BETA_TAC THEN
    USE_THEN "vm" (fun th -> REWRITE_TAC[th]) THEN CONJ_TAC THENL
     [FIRST_ASSUM(MATCH_ACCEPT_TAC o CONJUNCT1 o SPEC `a:num`); ALL_TAC] THEN
    X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
    USE_THEN "lim" (MP_TAC o C MP (ASSUME
      `w IN ball(vec 0:real^3,&3 * (rho:num->real)(NUMFST a) / &8)`) o SPEC `w:real^3`) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `v:real^3` THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `inv(&2) * norm(v:real^3) pow 2` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
     [REAL_ARITH_TAC; MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[NORM_POS_LT]];
    MAP_EVERY X_GEN_TAC [`w:real^3`; `v:real^3`] THEN DISCH_TAC THEN
    USE_THEN "lim" (MP_TAC o SPEC `w:real^3`) THEN ASM_SIMP_TAC[];
    FIRST_X_ASSUM(MATCH_ACCEPT_TAC o CONJUNCT2 o SPEC `a:num`)]);;

(* ------------------------------------------------------------------------- *)
(* The pseudo-distance system.  Along a D-subsequence the limit              *)
(* D is nonnegative, symmetric, satisfies the triangle inequality, vanishes  *)
(* on the diagonal, equals the norm against the chart centre, and dominates  *)
(* the coordinate distance on ball(0,rho/4) up to the factor sqrt 2.         *)
(* ------------------------------------------------------------------------- *)

let p2cg_std = [`top:num->A topology`; `atlas:num->((A->bool)#(A->real^3))->bool`;
                `h:num->A->real^3^3`; `x:num->A`; `rho:num->real`; `K:num->real`;
                `N0:num->num`; `B:num->num->real`; `NB:num->num->num`; `P:num->num`;
                `Nn:num->num`; `yc:num->num->num->A`];;

let p2cg_dk = new_definition
 `p2cg_dk (top:num->A topology) (atlas:num->((A->bool)#(A->real^3))->bool)
          (h:num->A->real^3^3) (yc:num->num->num->A) k a (z:real^3) b (w:real^3) =
    mfd_dist (top k,atlas k) (h k) (p2cg_nch top atlas h yc k a z)
                                   (p2cg_nch top atlas h yc k b w)`;;

let p2cg_dv = new_definition
 `p2cg_dv (D:num#num->real^(3,3)finite_sum->real^1) a (z:real^3) b (w:real^3) =
    drop(D (a,b) (pastecart z w))`;;

let p2cg_dsys = new_definition
 `p2cg_dsys (top:num->A topology) (atlas:num->((A->bool)#(A->real^3))->bool)
            (h:num->A->real^3^3) (yc:num->num->num->A) (rho:num->real) (s:num->num)
            (D:num#num->real^(3,3)finite_sum->real^1) <=>
    (!m n:num. m < n ==> s m < s n) /\
    !ab. D ab continuous_on p2cg_dsq rho ab /\
         !e. &0 < e
             ==> ?Kn. !n v. Kn <= n /\ v IN p2cg_dsq rho ab
                            ==> norm(p2cg_df top atlas h yc (s n) ab v - D ab v) < e`;;

let P2CG_DSYS_EXISTS = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc.
     p2cu_seq top atlas h x /\ p2cg_levels top atlas h x rho K N0 B NB P Nn yc
     ==> ?s D. p2cg_dsys top atlas h yc rho s D`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p2cg_dsys] THEN
  MP_TAC(ISPECL p2cg_std P2CG_DLIM) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN ACCEPT_TAC);;

let P2CG_DSYS_SUBSEQ = prove
 (`!top atlas (h:num->A->real^3^3) yc rho s D (r:num->num).
     p2cg_dsys top atlas h yc rho s D /\ (!m n:num. m < n ==> r m < r n)
     ==> p2cg_dsys top atlas h yc rho (s o r) D`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2cg_dsys; o_THM] THEN STRIP_TAC THEN CONJ_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `ab:num#num` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e:real` o CONJUNCT2 o SPEC `ab:num#num`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `Kn:num`) THEN
  EXISTS_TAC `Kn:num` THEN MAP_EVERY X_GEN_TAC [`n:num`; `v:real^(3,3)finite_sum`] THEN
  STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[MONOTONE_BIGGER]);;

let P2CG_D_SEQ = prove
 (`!top atlas (h:num->A->real^3^3) yc rho s D a b z w.
     p2cg_dsys top atlas h yc rho s D /\
     z IN cball(vec 0,rho(NUMFST a) / &2) /\ w IN cball(vec 0,rho(NUMFST b) / &2)
     ==> !e. &0 < e
             ==> ?N. !n. N <= n
                         ==> abs(p2cg_dk top atlas h yc (s n) a z b w - p2cg_dv D a z b w)
                             < e`,
  REWRITE_TAC[p2cg_dsys] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e:real` o CONJUNCT2 o SPEC `(a:num,b:num)`) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN
  DISCH_THEN(fun th -> X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    MP_TAC(SPECL [`n:num`; `pastecart (z:real^3) (w:real^3)`] th)) THEN
  ASM_REWRITE_TAC[p2cg_dsq; p2cg_df; p2cg_dk; p2cg_dv; PASTECART_IN_PCROSS;
                  FSTCART_PASTECART; SNDCART_PASTECART; FST; SND; NORM_1; DROP_SUB;
                  LIFT_DROP]);;

(* Limits of eventual inequalities between real sequences along a subsequence. *)

let P2CG_REAL_LIM_LE = prove
 (`!(f:num->real) g1 g2 (s:num->num) x y1 y2.
     (!e. &0 < e ==> ?N. !n. N <= n ==> abs(f(s n) - x) < e) /\
     (!e. &0 < e ==> ?N. !n. N <= n ==> abs(g1(s n) - y1) < e) /\
     (!e. &0 < e ==> ?N. !n. N <= n ==> abs(g2(s n) - y2) < e) /\
     (!m n:num. m < n ==> s m < s n) /\
     (?M. !k. M <= k ==> f k <= g1 k + g2 k)
     ==> x <= y1 + y2`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "f") (CONJUNCTS_THEN2 (LABEL_TAC "g1")
    (CONJUNCTS_THEN2 (LABEL_TAC "g2") (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_TAC `M:num`))))) THEN
  FIRST_ASSUM(LABEL_TAC "big" o MATCH_MP MONOTONE_BIGGER) THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  ABBREV_TAC `e = (x - (y1 + y2)) / &3` THEN
  SUBGOAL_THEN `&0 < e` ASSUME_TAC THENL [EXPAND_TAC "e" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REMOVE_THEN "f" (X_CHOOSE_TAC `N1:num` o C MP (ASSUME `&0 < e`) o SPEC `e:real`) THEN
  REMOVE_THEN "g1" (X_CHOOSE_TAC `N2:num` o C MP (ASSUME `&0 < e`) o SPEC `e:real`) THEN
  REMOVE_THEN "g2" (X_CHOOSE_TAC `N3:num` o C MP (ASSUME `&0 < e`) o SPEC `e:real`) THEN
  ABBREV_TAC `n = M + N1 + N2 + N3:num` THEN
  SUBGOAL_THEN `abs((f:num->real)((s:num->num) n) - x) < e /\
                abs((g1:num->real)(s n) - y1) < e /\ abs((g2:num->real)(s n) - y2) < e /\
                f(s n) <= g1(s n) + g2(s n)` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THENL
     [EXPAND_TAC "n" THEN ARITH_TAC;
      EXPAND_TAC "n" THEN ARITH_TAC;
      EXPAND_TAC "n" THEN ARITH_TAC;
      MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `n:num` THEN
      USE_THEN "big" (fun th -> REWRITE_TAC[th]) THEN EXPAND_TAC "n" THEN ARITH_TAC];
    ASM_REAL_ARITH_TAC]);;

let P2CG_REAL_LIM_LE1 = prove
 (`!(f:num->real) g (s:num->num) x y.
     (!e. &0 < e ==> ?N. !n. N <= n ==> abs(f(s n) - x) < e) /\
     (!e. &0 < e ==> ?N. !n. N <= n ==> abs(g(s n) - y) < e) /\
     (!m n:num. m < n ==> s m < s n) /\
     (?M. !k. M <= k ==> f k <= g k)
     ==> x <= y`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:num->real`; `g:num->real`; `\k:num. &0`; `s:num->num`;
                 `x:real`; `y:real`; `&0`] P2CG_REAL_LIM_LE) THEN
  BETA_TAC THEN REWRITE_TAC[REAL_ADD_RID; REAL_SUB_REFL; REAL_ABS_0] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [MESON_TAC[]; ASM_MESON_TAC[]]);;

(* Finite-level facts about the chart distances. *)

let P2CG_NCH_BASIC = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc a k.
     p2cu_seq top atlas h x /\ p2cg_levels top atlas h x rho K N0 B NB P Nn yc /\
     p2cg_nv N0 Nn a <= k
     ==> p2cg_nch top atlas h yc k a (vec 0) = p2cg_ctr yc k a /\
         !w. norm w < rho(NUMFST a)
             ==> mfd_joinable (top k,atlas k) (x k) (p2cg_nch top atlas h yc k a w) /\
                 mfd_dist (top k,atlas k) (h k) (p2cg_ctr yc k a)
                          (p2cg_nch top atlas h yc k a w) = norm w`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL (p2cg_std @ [`a:num`; `k:num`]) P2CG_CHART_OK) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o SPEC `k:num` o CONJUNCT1 o GEN_REWRITE_RULE I [p2cu_seq]) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[p2cg_nch; MATRIX_VECTOR_MUL_RZERO] THEN
    MP_TAC(ISPECL [`(top:num->A topology) k`; `(atlas:num->((A->bool)#(A->real^3))->bool) k`;
                   `(h:num->A->real^3^3) k`; `p2cg_ctr (yc:num->num->num->A) k a`]
                  MFD_EXP_DOM) THEN
    ASM_SIMP_TAC[];
    X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN CONJ_TAC THENL
     [MP_TAC(ISPECL (p2cg_std @ [`a:num`; `k:num`; `w:real^3`]) P2CG_NCH_FACTS) THEN
      ASM_SIMP_TAC[];
      MP_TAC(ISPECL [`(top:num->A topology) k`; `(atlas:num->((A->bool)#(A->real^3))->bool) k`;
                     `(h:num->A->real^3^3) k`; `p2cg_ctr (yc:num->num->num->A) k a`;
                     `p2cg_frm (h:num->A->real^3^3) (yc:num->num->num->A) k a`;
                     `(rho:num->real)(NUMFST a)`] P2CU_NCH_FACTS) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o SPEC `w:real^3` o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
      ASM_SIMP_TAC[p2cg_nch]]]);;

let P2CG_DK_SYM = prove
 (`!top atlas (h:num->A->real^3^3) x yc k a z b w.
     p2cu_seq top atlas h x
     ==> p2cg_dk top atlas h yc k b w a z = p2cg_dk top atlas h yc k a z b w`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p2cg_dk] THEN MATCH_MP_TAC MFD_DIST_SYM THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o SPEC `k:num` o CONJUNCT1 o GEN_REWRITE_RULE I [p2cu_seq]) THEN
  ASM_REWRITE_TAC[]);;

let P2CG_DK_JOIN = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc k a z b w.
     p2cu_seq top atlas h x /\ p2cg_levels top atlas h x rho K N0 B NB P Nn yc /\
     p2cg_nv N0 Nn a <= k /\ p2cg_nv N0 Nn b <= k /\
     norm z < rho(NUMFST a) /\ norm w < rho(NUMFST b)
     ==> mfd_joinable (top k,atlas k) (p2cg_nch top atlas h yc k a z)
                                      (p2cg_nch top atlas h yc k b w)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o SPEC `k:num` o CONJUNCT1 o GEN_REWRITE_RULE I [p2cu_seq]) THEN
  MATCH_MP_TAC MFD_JOINABLE_TRANS THEN EXISTS_TAC `(x:num->A) k` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL (p2cg_std @ [`a:num`; `k:num`; `z:real^3`]) P2CG_NCH_FACTS) THEN
  MP_TAC(ISPECL (p2cg_std @ [`b:num`; `k:num`; `w:real^3`]) P2CG_NCH_FACTS) THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[MFD_JOINABLE_SYM]);;

let P2CG_DK_POS = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc k a z b w.
     p2cu_seq top atlas h x /\ p2cg_levels top atlas h x rho K N0 B NB P Nn yc /\
     p2cg_nv N0 Nn a <= k /\ p2cg_nv N0 Nn b <= k /\
     norm z < rho(NUMFST a) /\ norm w < rho(NUMFST b)
     ==> &0 <= p2cg_dk top atlas h yc k a z b w`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p2cg_dk] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o SPEC `k:num` o CONJUNCT1 o GEN_REWRITE_RULE I [p2cu_seq]) THEN
  MATCH_MP_TAC MFD_DIST_POS_LE THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC P2CG_DK_JOIN THEN
  MAP_EVERY EXISTS_TAC [`x:num->A`; `rho:num->real`; `K:num->real`; `N0:num->num`;
                        `B:num->num->real`; `NB:num->num->num`; `P:num->num`;
                        `Nn:num->num`] THEN
  ASM_REWRITE_TAC[]);;

let P2CG_DK_TRI = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc k a z b w c u.
     p2cu_seq top atlas h x /\ p2cg_levels top atlas h x rho K N0 B NB P Nn yc /\
     p2cg_nv N0 Nn a <= k /\ p2cg_nv N0 Nn b <= k /\ p2cg_nv N0 Nn c <= k /\
     norm z < rho(NUMFST a) /\ norm w < rho(NUMFST b) /\ norm u < rho(NUMFST c)
     ==> p2cg_dk top atlas h yc k a z c u <=
         p2cg_dk top atlas h yc k a z b w + p2cg_dk top atlas h yc k b w c u`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p2cg_dk] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o SPEC `k:num` o CONJUNCT1 o GEN_REWRITE_RULE I [p2cu_seq]) THEN
  MATCH_MP_TAC MFD_DIST_TRIANGLE THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THEN MATCH_MP_TAC P2CG_DK_JOIN THEN
  MAP_EVERY EXISTS_TAC [`x:num->A`; `rho:num->real`; `K:num->real`; `N0:num->num`;
                        `B:num->num->real`; `NB:num->num->num`; `P:num->num`;
                        `Nn:num->num`] THEN
  ASM_REWRITE_TAC[]);;

let P2CG_DK_REFL0 = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc k a z.
     p2cu_seq top atlas h x /\ p2cg_levels top atlas h x rho K N0 B NB P Nn yc /\
     p2cg_nv N0 Nn a <= k /\ norm z < rho(NUMFST a)
     ==> p2cg_dk top atlas h yc k a z a (vec 0) = norm z`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL (p2cg_std @ [`a:num`; `k:num`]) P2CG_NCH_BASIC) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `z:real^3`)) THEN
  ASM_REWRITE_TAC[p2cg_dk] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (SUBST1_TAC o SYM)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o SPEC `k:num` o CONJUNCT1 o GEN_REWRITE_RULE I [p2cu_seq]) THEN
  MATCH_MP_TAC MFD_DIST_SYM THEN ASM_REWRITE_TAC[]);;

let P2CG_DK_DIAG = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc k a z.
     p2cu_seq top atlas h x /\ p2cg_levels top atlas h x rho K N0 B NB P Nn yc /\
     p2cg_nv N0 Nn a <= k /\ norm z < rho(NUMFST a)
     ==> p2cg_dk top atlas h yc k a z a z = &0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p2cg_dk] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o SPEC `k:num` o CONJUNCT1 o GEN_REWRITE_RULE I [p2cu_seq]) THEN
  MATCH_MP_TAC MFD_DIST_REFL THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL (p2cg_std @ [`a:num`; `k:num`; `z:real^3`]) P2CG_NCH_FACTS) THEN
  ASM_MESON_TAC[MFD_JOINABLE_IN_TOPSPACE]);;

let P2CG_DK_LOWER = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc k a z z'.
     p2cu_seq top atlas h x /\ p2cg_levels top atlas h x rho K N0 B NB P Nn yc /\
     p2cg_nv N0 Nn a <= k /\ norm z < rho(NUMFST a) / &4 /\ norm z' < rho(NUMFST a) / &4
     ==> norm(z - z') <= sqrt(&2) * p2cg_dk top atlas h yc k a z a z'`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p2cg_dk] THEN
  SUBGOAL_THEN `&0 < (rho:num->real)(NUMFST a)` ASSUME_TAC THENL
   [UNDISCH_TAC `p2cg_levels (top:num->A topology) atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc` THEN
    REWRITE_TAC[p2cg_levels] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL (p2cg_std @ [`a:num`; `k:num`; `z:real^3`; `z':real^3`]) P2CG_NCH_LIP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MATCH_MP_TAC o last o CONJUNCTS) THEN ASM_REWRITE_TAC[]);;

let P2CG_DK_REACH = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc k a z b.
     p2cu_seq top atlas h x /\ p2cg_levels top atlas h x rho K N0 B NB P Nn yc /\
     p2cg_nv N0 Nn a <= k /\ p2cg_nv N0 Nn b <= k /\ norm z < rho(NUMFST a) /\
     p2cg_dk top atlas h yc k a z b (vec 0) < rho(NUMFST b) / &2
     ==> ?w. norm w < rho(NUMFST b) / &2 /\
             p2cg_nch top atlas h yc k b w = p2cg_nch top atlas h yc k a z`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < (rho:num->real)(NUMFST b)` ASSUME_TAC THENL
   [UNDISCH_TAC `p2cg_levels (top:num->A topology) atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc` THEN
    REWRITE_TAC[p2cg_levels] THEN SIMP_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o SPEC `k:num` o CONJUNCT1 o GEN_REWRITE_RULE I [p2cu_seq]) THEN
  MP_TAC(ISPECL (p2cg_std @ [`b:num`; `k:num`]) P2CG_CHART_OK) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL (p2cg_std @ [`b:num`; `k:num`]) P2CG_NCH_BASIC) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "zero") (LABEL_TAC "dist")) THEN
  SUBGOAL_THEN `mfd_joinable ((top:num->A topology) k,(atlas:num->((A->bool)#(A->real^3))->bool) k)
                  (p2cg_ctr (yc:num->num->num->A) k b)
                  (p2cg_nch top atlas (h:num->A->real^3^3) yc k a z) /\
                mfd_dist (top k,atlas k) (h k) (p2cg_ctr yc k b) (p2cg_nch top atlas h yc k a z) <
                rho(NUMFST b) / &2`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "zero" (SUBST1_TAC o SYM) THEN CONJ_TAC THENL
     [MATCH_MP_TAC P2CG_DK_JOIN THEN
      MAP_EVERY EXISTS_TAC [`x:num->A`; `rho:num->real`; `K:num->real`; `N0:num->num`;
                            `B:num->num->real`; `NB:num->num->num`; `P:num->num`;
                            `Nn:num->num`] THEN
      ASM_REWRITE_TAC[NORM_0];
      MP_TAC(ISPECL [`top:num->A topology`; `atlas:num->((A->bool)#(A->real^3))->bool`;
                     `h:num->A->real^3^3`; `x:num->A`; `yc:num->num->num->A`; `k:num`;
                     `a:num`; `z:real^3`; `b:num`; `vec 0:real^3`] P2CG_DK_SYM) THEN
      ASM_REWRITE_TAC[p2cg_dk] THEN DISCH_THEN SUBST1_TAC THEN
      UNDISCH_TAC `p2cg_dk (top:num->A topology) atlas (h:num->A->real^3^3)
                     (yc:num->num->num->A) k a z b (vec 0) < rho(NUMFST b) / &2` THEN
      ASM_REWRITE_TAC[p2cg_dk]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(top:num->A topology) k`; `(atlas:num->((A->bool)#(A->real^3))->bool) k`;
                 `(h:num->A->real^3^3) k`; `p2cg_ctr (yc:num->num->num->A) k b`;
                 `p2cg_frm (h:num->A->real^3^3) (yc:num->num->num->A) k b`;
                 `(rho:num->real)(NUMFST b)`] P2CU_NCH_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2) THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_BALL_0; mfd_ball; IN_ELIM_THM] THEN
  DISCH_THEN(MP_TAC o SPEC `p2cg_nch (top:num->A topology) atlas (h:num->A->real^3^3)
                                    (yc:num->num->num->A) k a z`) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `mfd_dist ((top:num->A topology) k,(atlas:num->((A->bool)#(A->real^3))->bool) k)
                  ((h:num->A->real^3^3) k) (p2cg_ctr (yc:num->num->num->A) k b)
                  (p2cg_nch top atlas h yc k a z) < rho(NUMFST b)`
  (fun th -> REWRITE_TAC[th]) THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^3` (CONJUNCTS_THEN2
    (ASSUME_TAC o REWRITE_RULE[GSYM p2cg_nch]) ASSUME_TAC)) THEN
  EXISTS_TAC `w:real^3` THEN ASM_REWRITE_TAC[] THEN
  USE_THEN "dist" (MP_TAC o C MP (ASSUME `norm(w:real^3) < rho(NUMFST b)`) o
                   SPEC `w:real^3`) THEN
  DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT2) THEN
  UNDISCH_TAC `mfd_dist ((top:num->A topology) k,(atlas:num->((A->bool)#(A->real^3))->bool) k)
                 ((h:num->A->real^3^3) k) (p2cg_ctr (yc:num->num->num->A) k b)
                 (p2cg_nch top atlas h yc k a z) < rho(NUMFST b) / &2` THEN
  ASM_REWRITE_TAC[]);;

(* The limit facts. *)

let P2CG_RHO_POS = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc j.
     p2cg_levels top atlas h x rho K N0 B NB P Nn yc ==> &0 < rho j /\ rho j < &1`,
  REWRITE_TAC[p2cg_levels] THEN MESON_TAC[]);;

let P2CG_CBALL_NORM = prove
 (`!(z:real^3) r. &0 < r /\ z IN cball(vec 0,r / &2) ==> norm z < r /\ norm z <= r / &2`,
  REWRITE_TAC[IN_CBALL_0] THEN REAL_ARITH_TAC);;

let P2CG_D_UNIF = prove
 (`!top atlas (h:num->A->real^3^3) yc rho s D a b e.
     p2cg_dsys top atlas h yc rho s D /\ &0 < e
     ==> ?N. !n z w. N <= n /\ z IN cball(vec 0,rho(NUMFST a) / &2) /\
                     w IN cball(vec 0,rho(NUMFST b) / &2)
                     ==> abs(p2cg_dk top atlas h yc (s n) a z b w - p2cg_dv D a z b w) < e`,
  REWRITE_TAC[p2cg_dsys] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e:real` o CONJUNCT2 o SPEC `(a:num,b:num)`) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN
  DISCH_TAC THEN MAP_EVERY X_GEN_TAC [`n:num`; `z:real^3`; `w:real^3`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `pastecart (z:real^3) (w:real^3)`]) THEN
  ASM_REWRITE_TAC[p2cg_dsq; p2cg_df; p2cg_dk; p2cg_dv; PASTECART_IN_PCROSS;
                  FSTCART_PASTECART; SNDCART_PASTECART; FST; SND; NORM_1; DROP_SUB;
                  LIFT_DROP]);;

let P2CG_DV_POS = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc s D a z b w.
     p2cu_seq top atlas h x /\ p2cg_levels top atlas h x rho K N0 B NB P Nn yc /\
     p2cg_dsys top atlas h yc rho s D /\
     z IN cball(vec 0,rho(NUMFST a) / &2) /\ w IN cball(vec 0,rho(NUMFST b) / &2)
     ==> &0 <= p2cg_dv D a z b w`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [p2cg_dsys]) THEN
  SUBGOAL_THEN `norm(z:real^3) < rho(NUMFST a) /\ norm(w:real^3) < rho(NUMFST b)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[P2CG_CBALL_NORM; P2CG_RHO_POS]; ALL_TAC] THEN
  MATCH_MP_TAC P2CG_REAL_LIM_LE1 THEN
  MAP_EVERY EXISTS_TAC
   [`\k:num. &0`;
    `\k. p2cg_dk (top:num->A topology) atlas (h:num->A->real^3^3) (yc:num->num->num->A)
                 k a z b w`;
    `s:num->num`] THEN
  BETA_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[REAL_SUB_REFL; REAL_ABS_0] THEN MESON_TAC[];
    MATCH_MP_TAC P2CG_D_SEQ THEN EXISTS_TAC `rho:num->real` THEN ASM_REWRITE_TAC[];
    EXISTS_TAC `p2cg_nv (N0:num->num) (Nn:num->num) a + p2cg_nv N0 Nn b` THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC P2CG_DK_POS THEN
    MAP_EVERY EXISTS_TAC [`x:num->A`; `rho:num->real`; `K:num->real`; `N0:num->num`;
                          `B:num->num->real`; `NB:num->num->num`; `P:num->num`;
                          `Nn:num->num`] THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]);;

let P2CG_DV_SYM = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc s D a z b w.
     p2cu_seq top atlas h x /\ p2cg_levels top atlas h x rho K N0 B NB P Nn yc /\
     p2cg_dsys top atlas h yc rho s D /\
     z IN cball(vec 0,rho(NUMFST a) / &2) /\ w IN cball(vec 0,rho(NUMFST b) / &2)
     ==> p2cg_dv D b w a z = p2cg_dv D a z b w`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [p2cg_dsys]) THEN
  REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN CONJ_TAC THEN
  MATCH_MP_TAC P2CG_REAL_LIM_LE1 THENL
   [MAP_EVERY EXISTS_TAC
     [`\k. p2cg_dk (top:num->A topology) atlas (h:num->A->real^3^3) (yc:num->num->num->A)
                   k b w a z`;
      `\k. p2cg_dk (top:num->A topology) atlas (h:num->A->real^3^3) (yc:num->num->num->A)
                   k a z b w`;
      `s:num->num`];
    MAP_EVERY EXISTS_TAC
     [`\k. p2cg_dk (top:num->A topology) atlas (h:num->A->real^3^3) (yc:num->num->num->A)
                   k a z b w`;
      `\k. p2cg_dk (top:num->A topology) atlas (h:num->A->real^3^3) (yc:num->num->num->A)
                   k b w a z`;
      `s:num->num`]] THEN
  BETA_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
  TRY(MATCH_MP_TAC P2CG_D_SEQ THEN EXISTS_TAC `rho:num->real` THEN ASM_REWRITE_TAC[] THEN
      NO_TAC) THEN
  EXISTS_TAC `0` THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:num->A topology`; `atlas:num->((A->bool)#(A->real^3))->bool`;
                 `h:num->A->real^3^3`; `x:num->A`; `yc:num->num->num->A`; `k:num`;
                 `a:num`; `z:real^3`; `b:num`; `w:real^3`] P2CG_DK_SYM) THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let P2CG_DV_REFL0 = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc s D a z.
     p2cu_seq top atlas h x /\ p2cg_levels top atlas h x rho K N0 B NB P Nn yc /\
     p2cg_dsys top atlas h yc rho s D /\ z IN cball(vec 0,rho(NUMFST a) / &2)
     ==> p2cg_dv D a z a (vec 0) = norm z`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [p2cg_dsys]) THEN
  SUBGOAL_THEN `norm(z:real^3) < rho(NUMFST a) /\
                vec 0 IN cball(vec 0:real^3,rho(NUMFST a) / &2)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[CENTRE_IN_CBALL] THEN
    MP_TAC(ISPECL (p2cg_std @ [`NUMFST a`]) P2CG_RHO_POS) THEN
    ASM_MESON_TAC[P2CG_CBALL_NORM; REAL_ARITH `&0 < r ==> &0 <= r / &2`];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN CONJ_TAC THEN
  MATCH_MP_TAC P2CG_REAL_LIM_LE1 THENL
   [MAP_EVERY EXISTS_TAC
     [`\k. p2cg_dk (top:num->A topology) atlas (h:num->A->real^3^3) (yc:num->num->num->A)
                   k a z a (vec 0)`;
      `\k:num. norm(z:real^3)`; `s:num->num`];
    MAP_EVERY EXISTS_TAC
     [`\k:num. norm(z:real^3)`;
      `\k. p2cg_dk (top:num->A topology) atlas (h:num->A->real^3^3) (yc:num->num->num->A)
                   k a z a (vec 0)`; `s:num->num`]] THEN
  BETA_TAC THEN ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_ABS_0] THEN REPEAT CONJ_TAC THEN
  TRY(MESON_TAC[] THEN NO_TAC) THEN
  TRY(MATCH_MP_TAC P2CG_D_SEQ THEN EXISTS_TAC `rho:num->real` THEN ASM_REWRITE_TAC[] THEN
      NO_TAC) THEN
  EXISTS_TAC `p2cg_nv (N0:num->num) (Nn:num->num) a` THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL (p2cg_std @ [`k:num`; `a:num`; `z:real^3`]) P2CG_DK_REFL0) THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let P2CG_DV_DIAG = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc s D a z.
     p2cu_seq top atlas h x /\ p2cg_levels top atlas h x rho K N0 B NB P Nn yc /\
     p2cg_dsys top atlas h yc rho s D /\ z IN cball(vec 0,rho(NUMFST a) / &2)
     ==> p2cg_dv D a z a z = &0`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [p2cg_dsys]) THEN
  SUBGOAL_THEN `norm(z:real^3) < rho(NUMFST a)` ASSUME_TAC THENL
   [ASM_MESON_TAC[P2CG_CBALL_NORM; P2CG_RHO_POS]; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN CONJ_TAC THEN
  MATCH_MP_TAC P2CG_REAL_LIM_LE1 THENL
   [MAP_EVERY EXISTS_TAC
     [`\k. p2cg_dk (top:num->A topology) atlas (h:num->A->real^3^3) (yc:num->num->num->A)
                   k a z a z`;
      `\k:num. &0`; `s:num->num`];
    MAP_EVERY EXISTS_TAC
     [`\k:num. &0`;
      `\k. p2cg_dk (top:num->A topology) atlas (h:num->A->real^3^3) (yc:num->num->num->A)
                   k a z a z`; `s:num->num`]] THEN
  BETA_TAC THEN ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_ABS_0] THEN REPEAT CONJ_TAC THEN
  TRY(MESON_TAC[] THEN NO_TAC) THEN
  TRY(MATCH_MP_TAC P2CG_D_SEQ THEN EXISTS_TAC `rho:num->real` THEN ASM_REWRITE_TAC[] THEN
      NO_TAC) THEN
  EXISTS_TAC `p2cg_nv (N0:num->num) (Nn:num->num) a` THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL (p2cg_std @ [`k:num`; `a:num`; `z:real^3`]) P2CG_DK_DIAG) THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let P2CG_DV_TRI = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc s D a z b w c u.
     p2cu_seq top atlas h x /\ p2cg_levels top atlas h x rho K N0 B NB P Nn yc /\
     p2cg_dsys top atlas h yc rho s D /\
     z IN cball(vec 0,rho(NUMFST a) / &2) /\ w IN cball(vec 0,rho(NUMFST b) / &2) /\
     u IN cball(vec 0,rho(NUMFST c) / &2)
     ==> p2cg_dv D a z c u <= p2cg_dv D a z b w + p2cg_dv D b w c u`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [p2cg_dsys]) THEN
  SUBGOAL_THEN `norm(z:real^3) < rho(NUMFST a) /\ norm(w:real^3) < rho(NUMFST b) /\
                norm(u:real^3) < rho(NUMFST c)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[P2CG_CBALL_NORM; P2CG_RHO_POS]; ALL_TAC] THEN
  MATCH_MP_TAC P2CG_REAL_LIM_LE THEN
  MAP_EVERY EXISTS_TAC
   [`\k. p2cg_dk (top:num->A topology) atlas (h:num->A->real^3^3) (yc:num->num->num->A)
                 k a z c u`;
    `\k. p2cg_dk (top:num->A topology) atlas (h:num->A->real^3^3) (yc:num->num->num->A)
                 k a z b w`;
    `\k. p2cg_dk (top:num->A topology) atlas (h:num->A->real^3^3) (yc:num->num->num->A)
                 k b w c u`;
    `s:num->num`] THEN
  BETA_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
  TRY(MATCH_MP_TAC P2CG_D_SEQ THEN EXISTS_TAC `rho:num->real` THEN ASM_REWRITE_TAC[] THEN
      NO_TAC) THEN
  EXISTS_TAC `p2cg_nv (N0:num->num) (Nn:num->num) a + p2cg_nv N0 Nn b + p2cg_nv N0 Nn c` THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC P2CG_DK_TRI THEN
  MAP_EVERY EXISTS_TAC [`x:num->A`; `rho:num->real`; `K:num->real`; `N0:num->num`;
                        `B:num->num->real`; `NB:num->num->num`; `P:num->num`;
                        `Nn:num->num`] THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let P2CG_DV_LOWER = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc s D a z z'.
     p2cu_seq top atlas h x /\ p2cg_levels top atlas h x rho K N0 B NB P Nn yc /\
     p2cg_dsys top atlas h yc rho s D /\
     norm z < rho(NUMFST a) / &4 /\ norm z' < rho(NUMFST a) / &4
     ==> norm(z - z') <= sqrt(&2) * p2cg_dv D a z a z'`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [p2cg_dsys]) THEN
  SUBGOAL_THEN `&0 < (rho:num->real)(NUMFST a)` ASSUME_TAC THENL
   [ASM_MESON_TAC[P2CG_RHO_POS]; ALL_TAC] THEN
  SUBGOAL_THEN `(z:real^3) IN cball(vec 0,rho(NUMFST a) / &2) /\
                (z':real^3) IN cball(vec 0,rho(NUMFST a) / &2)`
  STRIP_ASSUME_TAC THENL [REWRITE_TAC[IN_CBALL_0] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt(&2)` ASSUME_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LT THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN ASM_SIMP_TAC[GSYM REAL_LE_LDIV_EQ] THEN
  MATCH_MP_TAC P2CG_REAL_LIM_LE1 THEN
  MAP_EVERY EXISTS_TAC
   [`\k:num. norm(z - z':real^3) / sqrt(&2)`;
    `\k. p2cg_dk (top:num->A topology) atlas (h:num->A->real^3^3) (yc:num->num->num->A)
                 k a z a z'`;
    `s:num->num`] THEN
  BETA_TAC THEN ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_ABS_0] THEN REPEAT CONJ_TAC THENL
   [MESON_TAC[];
    MATCH_MP_TAC P2CG_D_SEQ THEN EXISTS_TAC `rho:num->real` THEN ASM_REWRITE_TAC[];
    EXISTS_TAC `p2cg_nv (N0:num->num) (Nn:num->num) a` THEN REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    MATCH_MP_TAC P2CG_DK_LOWER THEN
    MAP_EVERY EXISTS_TAC [`x:num->A`; `rho:num->real`; `K:num->real`; `N0:num->num`;
                          `B:num->num->real`; `NB:num->num->num`; `P:num->num`;
                          `Nn:num->num`] THEN
    ASM_REWRITE_TAC[]]);;

let P2CG_DV_CONT = prove
 (`!top atlas (h:num->A->real^3^3) yc rho s D a b.
     p2cg_dsys top atlas h yc rho s D
     ==> (!z. z IN cball(vec 0,rho(NUMFST a) / &2)
              ==> (lift o (\w. p2cg_dv D a z b w)) continuous_on
                  cball(vec 0,rho(NUMFST b) / &2)) /\
         (!w. w IN cball(vec 0,rho(NUMFST b) / &2)
              ==> (lift o (\z. p2cg_dv D a z b w)) continuous_on
                  cball(vec 0,rho(NUMFST a) / &2))`,
  REWRITE_TAC[p2cg_dsys] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o CONJUNCT1 o SPEC `(a:num,b:num)` o CONJUNCT2) THEN
  REWRITE_TAC[p2cg_dsq; FST; SND] THEN DISCH_TAC THEN
  REWRITE_TAC[o_DEF; p2cg_dv; LIFT_DROP] THEN CONJ_TAC THENL
   [X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`\w:real^3. pastecart (z:real^3) w`;
                   `(D:num#num->real^(3,3)finite_sum->real^1) (a,b)`;
                   `cball(vec 0:real^3,rho(NUMFST b) / &2)`] CONTINUOUS_ON_COMPOSE);
    X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`\z:real^3. pastecart z (w:real^3)`;
                   `(D:num#num->real^(3,3)finite_sum->real^1) (a,b)`;
                   `cball(vec 0:real^3,rho(NUMFST a) / &2)`] CONTINUOUS_ON_COMPOSE)] THEN
  REWRITE_TAC[o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THEN
  TRY(MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN
      REWRITE_TAC[CONTINUOUS_ON_CONST; CONTINUOUS_ON_ID] THEN NO_TAC) THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] CONTINUOUS_ON_SUBSET) o
                check (fun th -> is_comb(concl th) && can (find_term (fun t -> is_const t &&
                  fst(dest_const t) = "continuous_on")) (concl th))) THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; PASTECART_IN_PCROSS] THEN BETA_TAC THEN
  REWRITE_TAC[PASTECART_IN_PCROSS] THEN ASM_SIMP_TAC[]);;

let P2CG_DV_REACH = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc s D a z b.
     p2cu_seq top atlas h x /\ p2cg_levels top atlas h x rho K N0 B NB P Nn yc /\
     p2cg_dsys top atlas h yc rho s D /\ z IN cball(vec 0,rho(NUMFST a) / &2) /\
     p2cg_dv D a z b (vec 0) < rho(NUMFST b) / &2
     ==> ?w. w IN cball(vec 0,rho(NUMFST b) / &2) /\ p2cg_dv D a z b w = &0`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [p2cg_dsys]) THEN
  FIRST_ASSUM(LABEL_TAC "big" o MATCH_MP MONOTONE_BIGGER) THEN
  SUBGOAL_THEN `&0 < (rho:num->real)(NUMFST b) /\ norm(z:real^3) < rho(NUMFST a) /\
                vec 0 IN cball(vec 0:real^3,rho(NUMFST b) / &2)` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[CENTRE_IN_CBALL] THEN
    MP_TAC(ISPECL (p2cg_std @ [`NUMFST b`]) P2CG_RHO_POS) THEN
    ASM_MESON_TAC[P2CG_CBALL_NORM; P2CG_RHO_POS; REAL_ARITH `&0 < r ==> &0 <= r / &2`];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\w. p2cg_dv (D:num#num->real^(3,3)finite_sum->real^1) a z b w`;
                 `cball(vec 0:real^3,rho(NUMFST b) / &2)`] CONTINUOUS_ATTAINS_INF) THEN
  BETA_TAC THEN REWRITE_TAC[COMPACT_CBALL; CBALL_EQ_EMPTY] THEN ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ISPECL [`top:num->A topology`; `atlas:num->((A->bool)#(A->real^3))->bool`;
                   `h:num->A->real^3^3`; `yc:num->num->num->A`; `rho:num->real`;
                   `s:num->num`; `D:num#num->real^(3,3)finite_sum->real^1`; `a:num`; `b:num`]
                  P2CG_DV_CONT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `w0:real^3` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "min"))) THEN
  EXISTS_TAC `w0:real^3` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN CONJ_TAC THENL
   [ALL_TAC;
    MP_TAC(ISPECL (p2cg_std @ [`s:num->num`; `D:num#num->real^(3,3)finite_sum->real^1`;
                               `a:num`; `z:real^3`; `b:num`; `w0:real^3`]) P2CG_DV_POS) THEN
    ASM_REWRITE_TAC[]] THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  ABBREV_TAC `e = min (p2cg_dv D a z b w0) (rho(NUMFST b) / &2 - p2cg_dv D a z b (vec 0))` THEN
  SUBGOAL_THEN `&0 < e` ASSUME_TAC THENL [EXPAND_TAC "e" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:num->A topology`; `atlas:num->((A->bool)#(A->real^3))->bool`;
                 `h:num->A->real^3^3`; `yc:num->num->num->A`; `rho:num->real`;
                 `s:num->num`; `D:num#num->real^(3,3)finite_sum->real^1`; `a:num`; `b:num`;
                 `e:real`] P2CG_D_UNIF) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `N:num` (LABEL_TAC "unif")) THEN
  ABBREV_TAC `n = N + p2cg_nv (N0:num->num) (Nn:num->num) a + p2cg_nv N0 Nn b` THEN
  SUBGOAL_THEN `N <= n /\ p2cg_nv (N0:num->num) (Nn:num->num) a <= (s:num->num) n /\
                p2cg_nv N0 Nn b <= s n` STRIP_ASSUME_TAC THENL
   [USE_THEN "big" (MP_TAC o SPEC `n:num`) THEN EXPAND_TAC "n" THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `p2cg_dk (top:num->A topology) atlas (h:num->A->real^3^3)
                  (yc:num->num->num->A) ((s:num->num) n) a z b (vec 0) < rho(NUMFST b) / &2`
  ASSUME_TAC THENL
   [USE_THEN "unif" (MP_TAC o SPECL [`n:num`; `z:real^3`; `vec 0:real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN EXPAND_TAC "e" THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL (p2cg_std @ [`(s:num->num) n`; `a:num`; `z:real^3`; `b:num`]) P2CG_DK_REACH) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `w1:real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(w1:real^3) IN cball(vec 0,rho(NUMFST b) / &2)` ASSUME_TAC THENL
   [REWRITE_TAC[IN_CBALL_0] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `p2cg_dk (top:num->A topology) atlas (h:num->A->real^3^3)
                  (yc:num->num->num->A) ((s:num->num) n) a z b w1 = &0` ASSUME_TAC THENL
   [REWRITE_TAC[p2cg_dk] THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL (p2cg_std @ [`(s:num->num) n`; `a:num`; `z:real^3`]) P2CG_DK_DIAG) THEN
    ASM_REWRITE_TAC[p2cg_dk];
    ALL_TAC] THEN
  USE_THEN "unif" (MP_TAC o SPECL [`n:num`; `z:real^3`; `w1:real^3`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  USE_THEN "min" (MP_TAC o SPEC `w1:real^3`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `p2cg_dk (top:num->A topology) atlas (h:num->A->real^3^3)
                 (yc:num->num->num->A) ((s:num->num) n) a z b w1 = &0` THEN
  EXPAND_TAC "e" THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The limit chart system.  Domains are the balls of radius                  *)
(* rho_a/4, the overlap of a with b consists of the points whose D-distance  *)
(* to the centre of b is below rho_b/4, and the transition from a to b sends *)
(* z to the unique w at D-distance zero.  The laws of p2cl_system except     *)
(* smoothness, and p2cl_separated.                                           *)
(* ------------------------------------------------------------------------- *)

let p2cg_dm = new_definition
 `p2cg_dm (rho:num->real) a = ball(vec 0:real^3,rho(NUMFST a) / &4)`;;

let p2cg_om = new_definition
 `p2cg_om (rho:num->real) (D:num#num->real^(3,3)finite_sum->real^1) a b =
    {z:real^3 | z IN ball(vec 0,rho(NUMFST a) / &4) /\
                p2cg_dv D a z b (vec 0) < rho(NUMFST b) / &4}`;;

let p2cg_tr = new_definition
 `p2cg_tr (rho:num->real) (D:num#num->real^(3,3)finite_sum->real^1) a b (z:real^3) =
    @w:real^3. w IN cball(vec 0,rho(NUMFST b) / &2) /\ p2cg_dv D a z b w = &0`;;

let P2CG_BALL4_CBALL = prove
 (`!(z:real^3) r. z IN ball(vec 0,r / &4)
                  ==> z IN cball(vec 0,r / &2) /\ norm z < r / &4 /\ &0 < r`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_BALL_0; IN_CBALL_0] THEN
  MP_TAC(ISPEC `z:real^3` NORM_POS_LE) THEN REAL_ARITH_TAC);;

let P2CG_CENTRE_CBALL = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc b.
     p2cg_levels top atlas h x rho K N0 B NB P Nn yc
     ==> vec 0 IN cball(vec 0:real^3,rho(NUMFST b) / &2) /\ &0 < rho(NUMFST b)`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o SPEC `NUMFST b` o MATCH_MP P2CG_RHO_POS) THEN
  REWRITE_TAC[CENTRE_IN_CBALL] THEN REAL_ARITH_TAC);;

let P2CG_DV_ZERO_NORM = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc s D a z b w.
     p2cu_seq top atlas h x /\ p2cg_levels top atlas h x rho K N0 B NB P Nn yc /\
     p2cg_dsys top atlas h yc rho s D /\
     z IN cball(vec 0,rho(NUMFST a) / &2) /\ w IN cball(vec 0,rho(NUMFST b) / &2) /\
     p2cg_dv D a z b w = &0
     ==> norm w <= p2cg_dv D a z b (vec 0)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL (p2cg_std @ [`b:num`]) P2CG_CENTRE_CBALL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL (p2cg_std @ [`s:num->num`; `D:num#num->real^(3,3)finite_sum->real^1`;
                             `b:num`; `w:real^3`]) P2CG_DV_REFL0) THEN
  MP_TAC(ISPECL (p2cg_std @ [`s:num->num`; `D:num#num->real^(3,3)finite_sum->real^1`;
                             `b:num`; `w:real^3`; `a:num`; `z:real^3`; `b:num`;
                             `vec 0:real^3`]) P2CG_DV_TRI) THEN
  MP_TAC(ISPECL (p2cg_std @ [`s:num->num`; `D:num#num->real^(3,3)finite_sum->real^1`;
                             `a:num`; `z:real^3`; `b:num`; `w:real^3`]) P2CG_DV_SYM) THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let P2CG_DV_ZERO_UNIQUE = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc s D a z b w w'.
     p2cu_seq top atlas h x /\ p2cg_levels top atlas h x rho K N0 B NB P Nn yc /\
     p2cg_dsys top atlas h yc rho s D /\ z IN cball(vec 0,rho(NUMFST a) / &2) /\
     norm w < rho(NUMFST b) / &4 /\ norm w' < rho(NUMFST b) / &4 /\
     p2cg_dv D a z b w = &0 /\ p2cg_dv D a z b w' = &0
     ==> w = w'`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL (p2cg_std @ [`b:num`]) P2CG_CENTRE_CBALL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(w:real^3) IN cball(vec 0,rho(NUMFST b) / &2) /\
                (w':real^3) IN cball(vec 0,rho(NUMFST b) / &2)` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[IN_CBALL_0] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `p2cg_dv D b (w:real^3) b (w':real^3) = &0` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN CONJ_TAC THENL
     [MP_TAC(ISPECL (p2cg_std @ [`s:num->num`; `D:num#num->real^(3,3)finite_sum->real^1`;
                                 `b:num`; `w:real^3`; `a:num`; `z:real^3`; `b:num`;
                                 `w':real^3`]) P2CG_DV_TRI) THEN
      MP_TAC(ISPECL (p2cg_std @ [`s:num->num`; `D:num#num->real^(3,3)finite_sum->real^1`;
                                 `a:num`; `z:real^3`; `b:num`; `w:real^3`]) P2CG_DV_SYM) THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      MP_TAC(ISPECL (p2cg_std @ [`s:num->num`; `D:num#num->real^(3,3)finite_sum->real^1`;
                                 `b:num`; `w:real^3`; `b:num`; `w':real^3`]) P2CG_DV_POS) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL (p2cg_std @ [`s:num->num`; `D:num#num->real^(3,3)finite_sum->real^1`;
                             `b:num`; `w:real^3`; `w':real^3`]) P2CG_DV_LOWER) THEN
  ASM_REWRITE_TAC[REAL_MUL_RZERO; NORM_LE_0; VECTOR_SUB_EQ]);;

let P2CG_TR_PROPS = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc s D a b z.
     p2cu_seq top atlas h x /\ p2cg_levels top atlas h x rho K N0 B NB P Nn yc /\
     p2cg_dsys top atlas h yc rho s D /\ z IN p2cg_om rho D a b
     ==> p2cg_tr rho D a b z IN ball(vec 0,rho(NUMFST b) / &4) /\
         p2cg_dv D a z b (p2cg_tr rho D a b z) = &0 /\
         (!w. w IN cball(vec 0,rho(NUMFST b) / &2) /\ p2cg_dv D a z b w = &0
              ==> p2cg_tr rho D a b z = w)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2cg_om; IN_ELIM_THM] THEN STRIP_TAC THEN
  MP_TAC(ISPECL (p2cg_std @ [`b:num`]) P2CG_CENTRE_CBALL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2CG_BALL4_CBALL) THEN
  SUBGOAL_THEN `p2cg_tr rho D a b (z:real^3) IN cball(vec 0:real^3,rho(NUMFST b) / &2) /\
                p2cg_dv D a z b (p2cg_tr rho D a b z) = &0` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[p2cg_tr] THEN CONV_TAC SELECT_CONV THEN
    MP_TAC(ISPECL (p2cg_std @ [`s:num->num`; `D:num#num->real^(3,3)finite_sum->real^1`;
                               `a:num`; `z:real^3`; `b:num`]) P2CG_DV_REACH) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!w:real^3. w IN cball(vec 0,rho(NUMFST b) / &2) /\ p2cg_dv D a z b w = &0
                           ==> norm w < rho(NUMFST b) / &4` ASSUME_TAC THENL
   [X_GEN_TAC `w:real^3` THEN STRIP_TAC THEN
    MP_TAC(ISPECL (p2cg_std @ [`s:num->num`; `D:num#num->real^(3,3)finite_sum->real^1`;
                               `a:num`; `z:real^3`; `b:num`; `w:real^3`]) P2CG_DV_ZERO_NORM) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[IN_BALL_0] THEN CONJ_TAC THENL [ASM_MESON_TAC[]; ASM_REWRITE_TAC[]] THEN
  X_GEN_TAC `w:real^3` THEN STRIP_TAC THEN
  MATCH_MP_TAC P2CG_DV_ZERO_UNIQUE THEN
  MAP_EVERY EXISTS_TAC (p2cg_std @ [`s:num->num`; `D:num#num->real^(3,3)finite_sum->real^1`;
                                    `a:num`; `z:real^3`; `b:num`]) THEN
  ASM_MESON_TAC[]);;

let P2CG_OM_OPEN = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc s D a b.
     p2cu_seq top atlas h x /\ p2cg_levels top atlas h x rho K N0 B NB P Nn yc /\
     p2cg_dsys top atlas h yc rho s D
     ==> open (p2cg_om rho D a b)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p2cg_om] THEN
  MP_TAC(ISPECL (p2cg_std @ [`b:num`]) P2CG_CENTRE_CBALL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`lift o (\z:real^3. p2cg_dv (D:num#num->real^(3,3)finite_sum->real^1)
                                          a z b (vec 0))`;
                 `ball(vec 0:real^3,rho(NUMFST a) / &4)`;
                 `{y:real^1 | y$1 < rho(NUMFST b) / &4}`] CONTINUOUS_OPEN_PREIMAGE) THEN
  REWRITE_TAC[OPEN_BALL; OPEN_HALFSPACE_COMPONENT_LT; IN_ELIM_THM; o_THM] THEN
  REWRITE_TAC[GSYM drop; LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN
  MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
  EXISTS_TAC `cball(vec 0:real^3,rho(NUMFST a) / &2)` THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`top:num->A topology`; `atlas:num->((A->bool)#(A->real^3))->bool`;
                   `h:num->A->real^3^3`; `yc:num->num->num->A`; `rho:num->real`;
                   `s:num->num`; `D:num#num->real^(3,3)finite_sum->real^1`; `a:num`; `b:num`]
                  P2CG_DV_CONT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[SUBSET] THEN MESON_TAC[P2CG_BALL4_CBALL]]);;

let P2CG_IN_OM = prove
 (`!rho D a b (z:real^3).
     z IN p2cg_om rho D a b <=>
     z IN ball(vec 0,rho(NUMFST a) / &4) /\ p2cg_dv D a z b (vec 0) < rho(NUMFST b) / &4`,
  REWRITE_TAC[p2cg_om; IN_ELIM_THM]);;

let P2CG_SYS_LAWS = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc s D.
     p2cu_seq top atlas h x /\ p2cg_levels top atlas h x rho K N0 B NB P Nn yc /\
     p2cg_dsys top atlas h yc rho s D
     ==> (!a. open (p2cg_dm rho a)) /\
         (!a b. open (p2cg_om rho D a b) /\ p2cg_om rho D a b SUBSET p2cg_dm rho a) /\
         (!a. p2cg_om rho D a a = p2cg_dm rho a) /\
         (!a z. z IN p2cg_dm rho a ==> p2cg_tr rho D a a z = z) /\
         (!a b z. z IN p2cg_om rho D a b
                  ==> p2cg_tr rho D a b z IN p2cg_om rho D b a /\
                      p2cg_tr rho D b a (p2cg_tr rho D a b z) = z) /\
         (!a b c z. z IN p2cg_om rho D a b /\ z IN p2cg_om rho D a c
                    ==> p2cg_tr rho D a b z IN p2cg_om rho D b c /\
                        p2cg_tr rho D b c (p2cg_tr rho D a b z) = p2cg_tr rho D a c z)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!a. p2cg_om rho D a a = p2cg_dm rho a` (LABEL_TAC "omaa") THENL
   [GEN_TAC THEN REWRITE_TAC[p2cg_om; p2cg_dm; EXTENSION; IN_ELIM_THM] THEN
    X_GEN_TAC `z:real^3` THEN EQ_TAC THEN SIMP_TAC[] THEN DISCH_TAC THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2CG_BALL4_CBALL) THEN
    MP_TAC(ISPECL (p2cg_std @ [`s:num->num`; `D:num#num->real^(3,3)finite_sum->real^1`;
                               `a:num`; `z:real^3`]) P2CG_DV_REFL0) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[p2cg_dm; OPEN_BALL];
    REPEAT GEN_TAC THEN CONJ_TAC THENL
     [MP_TAC(ISPECL (p2cg_std @ [`s:num->num`; `D:num#num->real^(3,3)finite_sum->real^1`;
                                 `a:num`; `b:num`]) P2CG_OM_OPEN) THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[p2cg_om; p2cg_dm; SUBSET; IN_ELIM_THM] THEN SIMP_TAC[]];
    MAP_EVERY X_GEN_TAC [`a:num`; `z:real^3`] THEN DISCH_TAC THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2CG_BALL4_CBALL o REWRITE_RULE[p2cg_dm]) THEN
    MP_TAC(ISPECL (p2cg_std @ [`s:num->num`; `D:num#num->real^(3,3)finite_sum->real^1`;
                               `a:num`; `a:num`; `z:real^3`]) P2CG_TR_PROPS) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MATCH_MP_TAC o last o CONJUNCTS) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P2CG_DV_DIAG THEN
    MAP_EVERY EXISTS_TAC (p2cg_std @ [`s:num->num`]) THEN ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`a:num`; `b:num`; `z:real^3`] THEN DISCH_TAC THEN
    MP_TAC(ISPECL (p2cg_std @ [`s:num->num`; `D:num#num->real^(3,3)finite_sum->real^1`;
                               `a:num`; `b:num`; `z:real^3`]) P2CG_TR_PROPS) THEN
    ASM_REWRITE_TAC[] THEN
    ABBREV_TAC `w = p2cg_tr rho D a b (z:real^3)` THEN STRIP_TAC THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [P2CG_IN_OM]) THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2CG_BALL4_CBALL o
                check (fun th -> can (find_term ((=) `z:real^3`)) (concl th))) THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2CG_BALL4_CBALL o
                check (fun th -> can (find_term ((=) `w:real^3`)) (concl th))) THEN
    MP_TAC(ISPECL (p2cg_std @ [`a:num`]) P2CG_CENTRE_CBALL) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL (p2cg_std @ [`s:num->num`; `D:num#num->real^(3,3)finite_sum->real^1`;
                               `a:num`; `z:real^3`; `b:num`; `w:real^3`]) P2CG_DV_SYM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `(w:real^3) IN p2cg_om rho D b a` ASSUME_TAC THENL
     [REWRITE_TAC[p2cg_om; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL (p2cg_std @ [`s:num->num`; `D:num#num->real^(3,3)finite_sum->real^1`;
                                 `b:num`; `w:real^3`; `a:num`; `z:real^3`; `a:num`;
                                 `vec 0:real^3`]) P2CG_DV_TRI) THEN
      MP_TAC(ISPECL (p2cg_std @ [`s:num->num`; `D:num#num->real^(3,3)finite_sum->real^1`;
                                 `a:num`; `z:real^3`]) P2CG_DV_REFL0) THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL (p2cg_std @ [`s:num->num`; `D:num#num->real^(3,3)finite_sum->real^1`;
                               `b:num`; `a:num`; `w:real^3`]) P2CG_TR_PROPS) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MATCH_MP_TAC o last o CONJUNCTS) THEN
    ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`a:num`; `b:num`; `c:num`; `z:real^3`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL (p2cg_std @ [`s:num->num`; `D:num#num->real^(3,3)finite_sum->real^1`;
                               `a:num`; `b:num`; `z:real^3`]) P2CG_TR_PROPS) THEN
    MP_TAC(ISPECL (p2cg_std @ [`s:num->num`; `D:num#num->real^(3,3)finite_sum->real^1`;
                               `a:num`; `c:num`; `z:real^3`]) P2CG_TR_PROPS) THEN
    ASM_REWRITE_TAC[] THEN
    ABBREV_TAC `w = p2cg_tr rho D a b (z:real^3)` THEN
    ABBREV_TAC `u = p2cg_tr rho D a c (z:real^3)` THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC))) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC))) THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [P2CG_IN_OM]) THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2CG_BALL4_CBALL o
                check (fun th -> can (find_term ((=) `z:real^3`)) (concl th))) THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2CG_BALL4_CBALL o
                check (fun th -> can (find_term ((=) `w:real^3`)) (concl th))) THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2CG_BALL4_CBALL o
                check (fun th -> can (find_term ((=) `u:real^3`)) (concl th))) THEN
    MP_TAC(ISPECL (p2cg_std @ [`c:num`]) P2CG_CENTRE_CBALL) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `p2cg_dv D b (w:real^3) c (u:real^3) = &0` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN CONJ_TAC THENL
       [MP_TAC(ISPECL (p2cg_std @ [`s:num->num`; `D:num#num->real^(3,3)finite_sum->real^1`;
                                   `b:num`; `w:real^3`; `a:num`; `z:real^3`; `c:num`;
                                   `u:real^3`]) P2CG_DV_TRI) THEN
        MP_TAC(ISPECL (p2cg_std @ [`s:num->num`; `D:num#num->real^(3,3)finite_sum->real^1`;
                                   `a:num`; `z:real^3`; `b:num`; `w:real^3`]) P2CG_DV_SYM) THEN
        ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
        MP_TAC(ISPECL (p2cg_std @ [`s:num->num`; `D:num#num->real^(3,3)finite_sum->real^1`;
                                   `b:num`; `w:real^3`; `c:num`; `u:real^3`]) P2CG_DV_POS) THEN
        ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `(w:real^3) IN p2cg_om rho D b c` ASSUME_TAC THENL
     [REWRITE_TAC[p2cg_om; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL (p2cg_std @ [`s:num->num`; `D:num#num->real^(3,3)finite_sum->real^1`;
                                 `b:num`; `w:real^3`; `c:num`; `u:real^3`; `c:num`;
                                 `vec 0:real^3`]) P2CG_DV_TRI) THEN
      MP_TAC(ISPECL (p2cg_std @ [`s:num->num`; `D:num#num->real^(3,3)finite_sum->real^1`;
                                 `c:num`; `u:real^3`]) P2CG_DV_REFL0) THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL (p2cg_std @ [`s:num->num`; `D:num#num->real^(3,3)finite_sum->real^1`;
                               `b:num`; `c:num`; `w:real^3`]) P2CG_TR_PROPS) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MATCH_MP_TAC o last o CONJUNCTS) THEN
    ASM_REWRITE_TAC[]]);;

let P2CG_SEPARATED = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc s D.
     p2cu_seq top atlas h x /\ p2cg_levels top atlas h x rho K N0 B NB P Nn yc /\
     p2cg_dsys top atlas h yc rho s D
     ==> p2cl_separated (p2cg_dm rho) (p2cg_om rho D) (p2cg_tr rho D)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[p2cl_separated] THEN
  MAP_EVERY X_GEN_TAC [`a:num`; `b:num`; `z:real^3`; `w:real^3`] THEN
  REWRITE_TAC[p2cg_dm] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2CG_BALL4_CBALL o
              check (fun th -> can (find_term ((=) `z:real^3`)) (concl th))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2CG_BALL4_CBALL o
              check (fun th -> can (find_term ((=) `w:real^3`)) (concl th))) THEN
  MP_TAC(ISPECL (p2cg_std @ [`b:num`]) P2CG_CENTRE_CBALL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < p2cg_dv D a (z:real^3) b (w:real^3)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_LT_LE] THEN CONJ_TAC THENL
     [MP_TAC(ISPECL (p2cg_std @ [`s:num->num`; `D:num#num->real^(3,3)finite_sum->real^1`;
                                 `a:num`; `z:real^3`; `b:num`; `w:real^3`]) P2CG_DV_POS) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(ASSUME_TAC o SYM) THEN
    FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN
    REWRITE_TAC[TAUT `~p ==> F <=> p`] THEN
    SUBGOAL_THEN `(z:real^3) IN p2cg_om rho D a b` ASSUME_TAC THENL
     [REWRITE_TAC[P2CG_IN_OM] THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL (p2cg_std @ [`s:num->num`; `D:num#num->real^(3,3)finite_sum->real^1`;
                                 `a:num`; `z:real^3`; `b:num`; `w:real^3`; `b:num`;
                                 `vec 0:real^3`]) P2CG_DV_TRI) THEN
      MP_TAC(ISPECL (p2cg_std @ [`s:num->num`; `D:num#num->real^(3,3)finite_sum->real^1`;
                                 `b:num`; `w:real^3`]) P2CG_DV_REFL0) THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL (p2cg_std @ [`s:num->num`; `D:num#num->real^(3,3)finite_sum->real^1`;
                               `a:num`; `b:num`; `z:real^3`]) P2CG_TR_PROPS) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MATCH_MP_TAC o last o CONJUNCTS) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT1 o SPEC `(a:num,b:num)` o CONJUNCT2 o
              GEN_REWRITE_RULE I [p2cg_dsys]) THEN
  REWRITE_TAC[continuous_on; p2cg_dsq; FST; SND] THEN
  DISCH_THEN(MP_TAC o SPEC `pastecart (z:real^3) (w:real^3)`) THEN
  REWRITE_TAC[PASTECART_IN_PCROSS] THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `p2cg_dv D a (z:real^3) b (w:real^3) / &2`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "cont"))) THEN
  MAP_EVERY EXISTS_TAC [`ball(z:real^3,d / &2)`; `ball(w:real^3,d / &2)`] THEN
  ASM_REWRITE_TAC[OPEN_BALL; CENTRE_IN_BALL; REAL_HALF] THEN
  X_GEN_TAC `y:real^3` THEN REWRITE_TAC[IN_INTER; IN_BALL] THEN STRIP_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL (p2cg_std @ [`s:num->num`; `D:num#num->real^(3,3)finite_sum->real^1`;
                             `a:num`; `b:num`; `y:real^3`]) P2CG_TR_PROPS) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `v = p2cg_tr rho D a b (y:real^3)` THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [P2CG_IN_OM]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2CG_BALL4_CBALL o
              check (fun th -> concl th = `(y:real^3) IN ball(vec 0,rho(NUMFST a) / &4)`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2CG_BALL4_CBALL o
              check (fun th -> concl th = `(v:real^3) IN ball(vec 0,rho(NUMFST b) / &4)`)) THEN
  SUBGOAL_THEN `dist((D:num#num->real^(3,3)finite_sum->real^1) (a,b) (pastecart y v),
                     D (a,b) (pastecart z w)) < p2cg_dv D a (z:real^3) b (w:real^3) / &2`
  MP_TAC THENL
   [USE_THEN "cont" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[PASTECART_IN_PCROSS; dist; PASTECART_SUB] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `norm((y:real^3) - z) + norm((v:real^3) - w)` THEN
    REWRITE_TAC[NORM_PASTECART_LE] THEN
    UNDISCH_TAC `dist(z:real^3,y) < d / &2` THEN UNDISCH_TAC `dist(w:real^3,v) < d / &2` THEN
    REWRITE_TAC[dist] THEN MP_TAC(ISPECL [`y:real^3`; `z:real^3`] NORM_SUB) THEN
    MP_TAC(ISPECL [`v:real^3`; `w:real^3`] NORM_SUB) THEN REAL_ARITH_TAC;
    REWRITE_TAC[dist; NORM_1; DROP_SUB; GSYM p2cg_dv] THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The finite transitions on good balls.  A ball cball(c,2r)                 *)
(* is good for (a,b) if it lies in ball(0,rho_a/2) and D(a,.;b,0) stays below *)
(* 3 rho_b/8 on it.  From some index on, the normal coordinate transitions    *)
(* are diffeomorphisms there into ball(0,rho_b/2), isometries of the normal   *)
(* coordinate metrics, with jet bounds of every order.                        *)
(* ------------------------------------------------------------------------- *)

let p2cg_qv = new_definition
 `p2cg_qv = @q:num->real^3.
     {x:real^3 | !i. 1 <= i /\ i <= dimindex(:3) ==> rational(x$i)} = IMAGE q (:num)`;;

let P2CG_QV_DENSE = prove
 (`!(z:real^3) e. &0 < e ==> ?n. norm(p2cg_qv n - z) < e`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `{x:real^3 | !i. 1 <= i /\ i <= dimindex(:3) ==> rational(x$i)} =
                IMAGE p2cg_qv (:num)` ASSUME_TAC THENL
   [REWRITE_TAC[p2cg_qv] THEN CONV_TAC SELECT_CONV THEN
    MATCH_MP_TAC COUNTABLE_AS_IMAGE THEN REWRITE_TAC[COUNTABLE_RATIONAL_COORDINATES] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN EXISTS_TAC `vec 0:real^3` THEN
    SIMP_TAC[VEC_COMPONENT; RATIONAL_NUM];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`z:real^3`;
                 `{x:real^3 | !i. 1 <= i /\ i <= dimindex(:3) ==> rational(x$i)}`]
                CLOSURE_APPROACHABLE) THEN
  REWRITE_TAC[CLOSURE_RATIONAL_COORDINATES; IN_UNIV] THEN
  DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[IN_IMAGE; IN_UNIV; dist] THEN MESON_TAC[]);;

let p2cg_good = new_definition
 `p2cg_good (rho:num->real) (D:num#num->real^(3,3)finite_sum->real^1) a b (c:real^3) r <=>
    &0 < r /\ cball(c,&2 * r) SUBSET ball(vec 0,rho(NUMFST a) / &2) /\
    !z. z IN cball(c,&2 * r) ==> p2cg_dv D a z b (vec 0) < &3 * rho(NUMFST b) / &8`;;

let p2cg_T = new_definition
 `p2cg_T (top:num->A topology) (atlas:num->((A->bool)#(A->real^3))->bool)
         (h:num->A->real^3^3) (yc:num->num->num->A) (rho:num->real) k a b =
    p2cg_trans (top k,atlas k) (h k) (p2cg_ctr yc k a) (p2cg_frm h yc k a)
               (p2cg_ctr yc k b) (p2cg_frm h yc k b) (rho(NUMFST b))`;;

(* The finite package on a ball where the chart images stay near the centre of b. *)

let P2CG_T_GOOD = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc a b c r k.
     p2cu_seq top atlas h x /\ p2cg_levels top atlas h x rho K N0 B NB P Nn yc /\
     p2cg_nv N0 Nn a <= k /\ p2cg_nv N0 Nn b <= k /\
     &0 < r /\ cball(c,&2 * r) SUBSET ball(vec 0,rho(NUMFST a) / &2) /\
     (!z. z IN cball(c,&2 * r)
          ==> p2cg_dk top atlas h yc k a z b (vec 0) < rho(NUMFST b) / &2)
     ==> (?Ti. diffeomorphism_on (ball(c,&2 * r))
                 (IMAGE (p2cg_T top atlas h yc rho k a b) (ball(c,&2 * r)))
                 (p2cg_T top atlas h yc rho k a b) Ti) /\
         IMAGE (p2cg_T top atlas h yc rho k a b) (ball(c,&2 * r)) SUBSET
         ball(vec 0,rho(NUMFST b) / &2) /\
         (!z. z IN ball(c,&2 * r)
              ==> p2cg_nch top atlas h yc k b (p2cg_T top atlas h yc rho k a b z) =
                  p2cg_nch top atlas h yc k a z) /\
         (!z. z IN ball(c,&2 * r)
              ==> p2cg_G top atlas h yc k a z =
                  mpullback (p2cg_T top atlas h yc rho k a b) (p2cg_G top atlas h yc k b) z)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o SPEC `k:num` o CONJUNCT1 o GEN_REWRITE_RULE I [p2cu_seq]) THEN
  MP_TAC(ISPECL (p2cg_std @ [`a:num`; `k:num`]) P2CG_CHART_OK) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL (p2cg_std @ [`b:num`; `k:num`]) P2CG_CHART_OK) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL (p2cg_std @ [`b:num`; `k:num`]) P2CG_NCH_BASIC) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "zero") (LABEL_TAC "dist")) THEN
  SUBGOAL_THEN `&0 < (rho:num->real)(NUMFST a) /\ &0 <= (K:num->real)(NUMFST a) /\
                K(NUMFST a) * rho(NUMFST a) pow 2 <= &1 /\
                &0 < rho(NUMFST b) /\ &0 <= K(NUMFST b) /\
                K(NUMFST b) * rho(NUMFST b) pow 2 <= &1` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `p2cg_levels (top:num->A topology) atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc` THEN
    REWRITE_TAC[p2cg_levels] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z:real^3. z IN ball(c,&2 * r) ==> norm z < rho(NUMFST a) / &2`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(z:real^3) IN ball(vec 0,rho(NUMFST a) / &2)` MP_TAC THENL
     [ASM_MESON_TAC[SUBSET; BALL_SUBSET_CBALL]; REWRITE_TAC[IN_BALL_0]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z:real^3. z IN ball(c,&2 * r)
               ==> mfd_joinable ((top:num->A topology) k,
                                 (atlas:num->((A->bool)#(A->real^3))->bool) k)
                     (p2cg_ctr (yc:num->num->num->A) k b)
                     (p2cg_nch top atlas (h:num->A->real^3^3) yc k a z) /\
                   mfd_dist (top k,atlas k) (h k) (p2cg_ctr yc k b)
                     (p2cg_nch top atlas h yc k a z) < rho(NUMFST b) / &2`
  (LABEL_TAC "near") THENL
   [X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    USE_THEN "zero" (SUBST1_TAC o SYM) THEN CONJ_TAC THENL
     [MATCH_MP_TAC P2CG_DK_JOIN THEN
      MAP_EVERY EXISTS_TAC [`x:num->A`; `rho:num->real`; `K:num->real`; `N0:num->num`;
                            `B:num->num->real`; `NB:num->num->num`; `P:num->num`;
                            `Nn:num->num`] THEN
      ASM_REWRITE_TAC[NORM_0] THEN
      MATCH_MP_TAC(REAL_ARITH `x < r / &2 /\ &0 < r ==> x < r`) THEN ASM_SIMP_TAC[];
      MP_TAC(ISPECL [`top:num->A topology`; `atlas:num->((A->bool)#(A->real^3))->bool`;
                     `h:num->A->real^3^3`; `x:num->A`; `yc:num->num->num->A`; `k:num`;
                     `a:num`; `z:real^3`; `b:num`; `vec 0:real^3`] P2CG_DK_SYM) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[p2cg_dk] THEN DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[GSYM p2cg_dk] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_MESON_TAC[SUBSET; BALL_SUBSET_CBALL]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(top:num->A topology) k`; `(atlas:num->((A->bool)#(A->real^3))->bool) k`;
                 `(h:num->A->real^3^3) k`;
                 `p2cg_ctr (yc:num->num->num->A) k a`;
                 `p2cg_frm (h:num->A->real^3^3) (yc:num->num->num->A) k a`;
                 `(rho:num->real)(NUMFST a)`; `(K:num->real)(NUMFST a)`;
                 `p2cg_ctr (yc:num->num->num->A) k b`;
                 `p2cg_frm (h:num->A->real^3^3) (yc:num->num->num->A) k b`;
                 `(rho:num->real)(NUMFST b)`; `(K:num->real)(NUMFST b)`;
                 `ball(c:real^3,&2 * r)`] P2CG_TRANS_PACKAGE) THEN
  REWRITE_TAC[GSYM p2cg_T; GSYM p2cg_G] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[OPEN_BALL] THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_BALL_0] THEN
      X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
      MATCH_MP_TAC(REAL_ARITH `x < r / &2 /\ &0 < r ==> x < r`) THEN ASM_SIMP_TAC[];
      X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
      USE_THEN "near" (MP_TAC o C MP (ASSUME `(z:real^3) IN ball(c,&2 * r)`) o
                       SPEC `z:real^3`) THEN
      REWRITE_TAC[mfd_ball; IN_ELIM_THM; p2cg_nch] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM p2cg_nch] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "eq") ASSUME_TAC))) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_BALL_0] THEN
  X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
  SUBGOAL_THEN `norm(p2cg_T (top:num->A topology) atlas (h:num->A->real^3^3)
                  (yc:num->num->num->A) rho k a b z) < rho(NUMFST b)` ASSUME_TAC THENL
   [UNDISCH_TAC `IMAGE (p2cg_T (top:num->A topology) atlas (h:num->A->real^3^3)
                    (yc:num->num->num->A) rho k a b) (ball(c,&2 * r)) SUBSET
                 ball(vec 0,rho(NUMFST b))` THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_BALL_0] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  USE_THEN "dist" (MP_TAC o C MP (ASSUME
    `norm(p2cg_T (top:num->A topology) atlas (h:num->A->real^3^3)
            (yc:num->num->num->A) rho k a b z) < rho(NUMFST b)`) o
    SPEC `p2cg_T (top:num->A topology) atlas (h:num->A->real^3^3)
            (yc:num->num->num->A) rho k a b z`) THEN
  DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT2) THEN
  USE_THEN "eq" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `(z:real^3) IN ball(c,&2 * r)`)]) THEN
  USE_THEN "near" (MP_TAC o C MP (ASSUME `(z:real^3) IN ball(c,&2 * r)`) o SPEC `z:real^3`) THEN
  SIMP_TAC[]);;

(* Jet bounds of the finite transitions on a good ball, uniform in the index. *)

let P2CG_T_FINITE_JET = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc a b m.
     ?C. !c r k y.
       p2cu_seq top atlas h x /\ p2cg_levels top atlas h x rho K N0 B NB P Nn yc /\
       p2cg_nv N0 Nn a + NB (NUMFST a) (SUC m) <= k /\
       p2cg_nv N0 Nn b + NB (NUMFST b) (SUC m) <= k /\
       &0 < r /\ cball(c,&2 * r) SUBSET ball(vec 0,rho(NUMFST a) / &2) /\
       (!z. z IN cball(c,&2 * r)
            ==> p2cg_dk top atlas h yc k a z b (vec 0) < rho(NUMFST b) / &2) /\
       y IN ball(c,&2 * r)
       ==> pde_jetn m (p2cg_T top atlas h yc rho k a b) y <= C`,
  REPEAT GEN_TAC THEN
  ABBREV_TAC
   `Bm = max (&(CARD(pde_index_lists (SUC m) (:3))) * &(dimindex(:(3,3)finite_prod)) *
              (sqrt(abs((B:num->num->real) (NUMFST a) (SUC m))) + &1))
             (&(CARD(pde_index_lists (SUC m) (:3))) * &(dimindex(:(3,3)finite_prod)) *
              (sqrt(abs(B (NUMFST b) (SUC m))) + &1))` THEN
  MP_TAC(ISPECL [`m:num`; `Bm:real`; `&2 * &(dimindex(:(3,3)finite_prod))`; `&2`]
                (INST_TYPE [`:3`,`:N`] P2CT_ISOM_JET)) THEN
  DISCH_THEN(X_CHOOSE_THEN `C0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "iso"))) THEN
  EXISTS_TAC `(rho:num->real)(NUMFST b) + &(CARD(pde_index_lists (SUC m) (:3))) * &3 * C0` THEN
  MAP_EVERY X_GEN_TAC [`c:real^3`; `r:real`; `k:num`; `y:real^3`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL (p2cg_std @ [`a:num`; `b:num`; `c:real^3`; `r:real`; `k:num`]) P2CG_T_GOOD) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `Tm = p2cg_T (top:num->A topology) atlas (h:num->A->real^3^3)
                          (yc:num->num->num->A) rho k a b` THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `Ti:real^3->real^3`)
    (CONJUNCTS_THEN2 (LABEL_TAC "img") (CONJUNCTS_THEN2 (K ALL_TAC) (LABEL_TAC "pb")))) THEN
  MP_TAC(ISPECL (p2cg_std @ [`a:num`; `k:num`; `SUC m`]) P2CG_G_FIELD) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "fa") (LABEL_TAC "ja")) THEN
  MP_TAC(ISPECL (p2cg_std @ [`b:num`; `k:num`; `SUC m`]) P2CG_G_FIELD) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "fb") (LABEL_TAC "jb")) THEN
  SUBGOAL_THEN `&0 < (rho:num->real)(NUMFST a) /\ &0 < rho(NUMFST b)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[P2CG_RHO_POS]; ALL_TAC] THEN
  SUBGOAL_THEN `norm(y:real^3) < rho(NUMFST a) / &2 /\
                norm((Tm:real^3->real^3) y) < rho(NUMFST b) / &2` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [SUBGOAL_THEN `(y:real^3) IN ball(vec 0,rho(NUMFST a) / &2)` MP_TAC THENL
       [ASM_MESON_TAC[SUBSET; BALL_SUBSET_CBALL]; REWRITE_TAC[IN_BALL_0]];
      USE_THEN "img" (MP_TAC o REWRITE_RULE[SUBSET; FORALL_IN_IMAGE; IN_BALL_0]) THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!v:real^3. inv(&2) * (v dot v) <=
               v dot (p2cg_G (top:num->A topology) atlas (h:num->A->real^3^3)
                        (yc:num->num->num->A) k a y ** v) /\
               v dot (p2cg_G top atlas h yc k a y ** v) <= &2 * (v dot v) /\
               inv(&2) * (v dot v) <= v dot (p2cg_G top atlas h yc k b ((Tm:real^3->real^3) y) ** v) /\
               v dot (p2cg_G top atlas h yc k b (Tm y) ** v) <= &2 * (v dot v)`
  (LABEL_TAC "eqv") THENL
   [X_GEN_TAC `v:real^3` THEN REWRITE_TAC[GSYM NORM_POW_2] THEN
    MP_TAC(ISPECL (p2cg_std @ [`a:num`; `k:num`; `y:real^3`; `v:real^3`]) P2CG_G_EQUIV) THEN
    MP_TAC(ISPECL (p2cg_std @ [`b:num`; `k:num`; `(Tm:real^3->real^3) y`; `v:real^3`])
                  P2CG_G_EQUIV) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    STRIP_TAC THEN ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!i. 1 <= i /\ i <= dimindex(:3)
                    ==> pde_jetn m (partial_derivative i (Tm:real^3->real^3)) y <= C0`
  ASSUME_TAC THENL
   [USE_THEN "iso" MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC
     [`ball(c:real^3,&2 * r)`; `IMAGE (Tm:real^3->real^3) (ball(c,&2 * r))`;
      `Ti:real^3->real^3`;
      `p2cg_G (top:num->A topology) atlas (h:num->A->real^3^3) (yc:num->num->num->A) k a`;
      `p2cg_G (top:num->A topology) atlas (h:num->A->real^3^3) (yc:num->num->num->A) k b`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN
      EXISTS_TAC `ball(vec 0:real^3,rho(NUMFST b))` THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL
       [UNDISCH_TAC `diffeomorphism_on (ball(c:real^3,&2 * r))
                       (IMAGE (Tm:real^3->real^3) (ball(c,&2 * r))) Tm (Ti:real^3->real^3)` THEN
        REWRITE_TAC[diffeomorphism_on] THEN SIMP_TAC[];
        MATCH_MP_TAC SUBSET_TRANS THEN
        EXISTS_TAC `ball(vec 0:real^3,rho(NUMFST b) / &2)` THEN
        USE_THEN "img" (fun th -> REWRITE_TAC[th]) THEN
        MATCH_MP_TAC SUBSET_BALL THEN ASM_REAL_ARITH_TAC];
      MATCH_MP_TAC METRIC_FIELD_SUBSET THEN
      EXISTS_TAC `ball(vec 0:real^3,rho(NUMFST a))` THEN ASM_REWRITE_TAC[OPEN_BALL] THEN
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `ball(vec 0:real^3,rho(NUMFST a) / &2)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `cball(c:real^3,&2 * r)` THEN
        ASM_REWRITE_TAC[BALL_SUBSET_CBALL];
        ALL_TAC] THEN
      MATCH_MP_TAC SUBSET_BALL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `&(CARD(pde_index_lists (SUC m) (:3))) * &(dimindex(:(3,3)finite_prod)) *
                  (sqrt(abs((B:num->num->real) (NUMFST a) (SUC m))) + &1)` THEN
      CONJ_TAC THENL
       [USE_THEN "ja" MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_BALL_0];
        EXPAND_TAC "Bm" THEN REAL_ARITH_TAC];
      MATCH_MP_TAC P2CG_GINV_VEC THEN
      EXISTS_TAC `ball(vec 0:real^3,rho(NUMFST a))` THEN ASM_REWRITE_TAC[IN_BALL_0] THEN
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `&(CARD(pde_index_lists (SUC m) (:3))) * &(dimindex(:(3,3)finite_prod)) *
                  (sqrt(abs((B:num->num->real) (NUMFST b) (SUC m))) + &1)` THEN
      CONJ_TAC THENL
       [USE_THEN "jb" MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_BALL_0];
        EXPAND_TAC "Bm" THEN REAL_ARITH_TAC];
      MATCH_MP_TAC P2CG_GINV_VEC THEN
      EXISTS_TAC `ball(vec 0:real^3,rho(NUMFST b))` THEN ASM_REWRITE_TAC[IN_BALL_0] THEN
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC P2CG_ISOM_DT_BOUND THEN
      MAP_EVERY EXISTS_TAC
       [`p2cg_G (top:num->A topology) atlas (h:num->A->real^3^3) (yc:num->num->num->A) k a`;
        `p2cg_G (top:num->A topology) atlas (h:num->A->real^3^3) (yc:num->num->num->A) k b`] THEN
      ASM_SIMP_TAC[] THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
      EXISTS_TAC `ball(c:real^3,&2 * r)` THEN ASM_REWRITE_TAC[OPEN_BALL] THEN
      UNDISCH_TAC `diffeomorphism_on (ball(c:real^3,&2 * r))
                     (IMAGE (Tm:real^3->real^3) (ball(c,&2 * r))) Tm (Ti:real^3->real^3)` THEN
      REWRITE_TAC[diffeomorphism_on] THEN SIMP_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `pde_jetn (SUC m) (Tm:real^3->real^3) y` THEN
  CONJ_TAC THENL [MATCH_MP_TAC PDE_JETN_MONO THEN ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `norm((Tm:real^3->real^3) y) + &(CARD(pde_index_lists (SUC m) (:3))) *
              sum(1..dimindex(:3)) (\i. pde_jetn m (partial_derivative i Tm) y)` THEN
  REWRITE_TAC[P2CT_JETN_SUC_BOUND] THEN
  MATCH_MP_TAC(REAL_ARITH `x <= r /\ s <= t ==> x + s <= r + t`) THEN CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sum(1..dimindex(:3)) (\i. C0)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE_NUMSEG THEN ASM_SIMP_TAC[];
    REWRITE_TAC[SUM_CONST_NUMSEG; DIMINDEX_3] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REAL_ARITH_TAC]);;

(* On a good ball the finite hypotheses hold from some index on. *)

let P2CG_GOOD_EVENTUALLY = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc s D a b c r M.
     p2cu_seq top atlas h x /\ p2cg_levels top atlas h x rho K N0 B NB P Nn yc /\
     p2cg_dsys top atlas h yc rho s D /\ p2cg_good rho D a b c r
     ==> ?N. !n. N <= n
                 ==> M <= s n /\
                     !z. z IN cball(c,&2 * r)
                         ==> p2cg_dk top atlas h yc (s n) a z b (vec 0) < rho(NUMFST b) / &2`,
  REWRITE_TAC[p2cg_good] THEN REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [p2cg_dsys]) THEN
  FIRST_ASSUM(LABEL_TAC "big" o MATCH_MP MONOTONE_BIGGER) THEN
  MP_TAC(ISPECL (p2cg_std @ [`b:num`]) P2CG_CENTRE_CBALL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:num->A topology`; `atlas:num->((A->bool)#(A->real^3))->bool`;
                 `h:num->A->real^3^3`; `yc:num->num->num->A`; `rho:num->real`;
                 `s:num->num`; `D:num#num->real^(3,3)finite_sum->real^1`; `a:num`; `b:num`;
                 `rho(NUMFST b) / &8`] P2CG_D_UNIF) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` (LABEL_TAC "unif")) THEN
  EXISTS_TAC `N + M:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN CONJ_TAC THENL
   [USE_THEN "big" (MP_TAC o SPEC `n:num`) THEN ASM_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(z:real^3) IN cball(vec 0,rho(NUMFST a) / &2)` ASSUME_TAC THENL
   [ASM_MESON_TAC[SUBSET; BALL_SUBSET_CBALL]; ALL_TAC] THEN
  USE_THEN "unif" (MP_TAC o SPECL [`n:num`; `z:real^3`; `vec 0:real^3`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o C MP (ASSUME `(z:real^3) IN cball(c,&2 * r)`) o SPEC `z:real^3` o
                check (fun th -> can (find_term (fun t -> is_const t &&
                  fst(dest_const t) = "p2cg_dv")) (concl th) && is_forall(concl th))) THEN
  REAL_ARITH_TAC);;

let P2CG_JETN_ZERO = prove
 (`!m (y:real^3). pde_jetn m (\z:real^3. vec 0:real^3) y = &0`,
  REWRITE_TAC[pde_jetn; P2CT_ITERATED_PARTIAL_CONST; COND_ID; NORM_0; SUM_0]);;

(* The transition limits on good rational balls. *)

let P2CG_TLIM = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc s D.
     p2cu_seq top atlas h x /\ p2cg_levels top atlas h x rho K N0 B NB P Nn yc /\
     p2cg_dsys top atlas h yc rho s D
     ==> ?s3 Ht. (!m n:num. m < n ==> s3 m < s3 n) /\
                 !a b n p.
                   p2cg_good rho D a b (p2cg_qv n) (inv(&2 pow p))
                   ==> smooth_map_on (ball(p2cg_qv n,inv(&2 pow p))) (Ht (a,b,n,p)) /\
                       !l. ALL (\j. 1 <= j /\ j <= dimindex(:3)) l
                           ==> !e. &0 < e
                                   ==> ?Kn. !k y. Kn <= k /\ y IN ball(p2cg_qv n,inv(&2 pow p))
                                                  ==> norm(iterated_partial l
                                                            (p2cg_T top atlas h yc rho
                                                                    (s(s3 k)) a b) y -
                                                           iterated_partial l (Ht (a,b,n,p)) y)
                                                      < e`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`\(i:num#num#num#num) k.
       if p2cg_good rho D (FST i) (FST(SND i)) (p2cg_qv(FST(SND(SND i))))
                    (inv(&2 pow SND(SND(SND i))))
       then p2cg_T (top:num->A topology) atlas (h:num->A->real^3^3) (yc:num->num->num->A)
                   rho ((s:num->num) k) (FST i) (FST(SND i))
       else (\z:real^3. vec 0:real^3)`;
    `\i:num#num#num#num. ball(p2cg_qv(FST(SND(SND i))),&2 * inv(&2 pow SND(SND(SND i))))`;
    `\i:num#num#num#num. p2cg_qv(FST(SND(SND i)))`;
    `\i:num#num#num#num. inv(&2 pow SND(SND(SND i)))`] P2CS_JET_SUBSEQ) THEN
  BETA_TAC THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REWRITE_TAC[GSYM CROSS_UNIV] THEN
      REPEAT(MATCH_MP_TAC COUNTABLE_CROSS THEN CONJ_TAC) THEN REWRITE_TAC[NUM_COUNTABLE];
      X_GEN_TAC `i:num#num#num#num` THEN REWRITE_TAC[OPEN_BALL; SUBSET; IN_CBALL; IN_BALL] THEN
      SUBGOAL_THEN `&0 < inv(&2 pow SND(SND(SND(i:num#num#num#num))))` MP_TAC THENL
       [MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC REAL_POW_LT THEN REAL_ARITH_TAC;
        REAL_ARITH_TAC];
      X_GEN_TAC `i:num#num#num#num` THEN
      ASM_CASES_TAC `p2cg_good rho D (FST(i:num#num#num#num)) (FST(SND i))
                       (p2cg_qv(FST(SND(SND i)))) (inv(&2 pow SND(SND(SND i))))` THEN
      ASM_REWRITE_TAC[SMOOTH_MAP_ON_CONST] THEN
      MP_TAC(ISPECL (p2cg_std @ [`s:num->num`; `D:num#num->real^(3,3)finite_sum->real^1`;
                                 `FST(i:num#num#num#num)`; `FST(SND(i:num#num#num#num))`;
                                 `p2cg_qv(FST(SND(SND(i:num#num#num#num))))`;
                                 `inv(&2 pow SND(SND(SND(i:num#num#num#num))))`;
                                 `p2cg_nv (N0:num->num) (Nn:num->num) (FST(i:num#num#num#num)) +
                                  p2cg_nv N0 Nn (FST(SND i))`])
                    P2CG_GOOD_EVENTUALLY) THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN
      DISCH_TAC THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      UNDISCH_TAC `p2cg_good rho D (FST(i:num#num#num#num)) (FST(SND i))
                     (p2cg_qv(FST(SND(SND i)))) (inv(&2 pow SND(SND(SND i))))` THEN
      REWRITE_TAC[p2cg_good] THEN STRIP_TAC THEN
      MP_TAC(ISPECL (p2cg_std @ [`FST(i:num#num#num#num)`; `FST(SND(i:num#num#num#num))`;
                                 `p2cg_qv(FST(SND(SND(i:num#num#num#num))))`;
                                 `inv(&2 pow SND(SND(SND(i:num#num#num#num))))`;
                                 `(s:num->num) n`]) P2CG_T_GOOD) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_TAC `Ti:real^3->real^3` o CONJUNCT1) THEN
      ASM_MESON_TAC[diffeomorphism_on];
      MAP_EVERY X_GEN_TAC [`i:num#num#num#num`; `m:num`] THEN
      ASM_CASES_TAC `p2cg_good rho D (FST(i:num#num#num#num)) (FST(SND i))
                       (p2cg_qv(FST(SND(SND i)))) (inv(&2 pow SND(SND(SND i))))` THEN
      ASM_REWRITE_TAC[P2CG_JETN_ZERO] THENL
       [ALL_TAC; EXISTS_TAC `&0` THEN REWRITE_TAC[REAL_LE_REFL]] THEN
      MP_TAC(ISPECL (p2cg_std @ [`FST(i:num#num#num#num)`; `FST(SND(i:num#num#num#num))`;
                                 `m:num`]) P2CG_T_FINITE_JET) THEN
      DISCH_THEN(X_CHOOSE_TAC `C:real`) THEN EXISTS_TAC `C:real` THEN
      MP_TAC(ISPECL (p2cg_std @ [`s:num->num`; `D:num#num->real^(3,3)finite_sum->real^1`;
                                 `FST(i:num#num#num#num)`; `FST(SND(i:num#num#num#num))`;
                                 `p2cg_qv(FST(SND(SND(i:num#num#num#num))))`;
                                 `inv(&2 pow SND(SND(SND(i:num#num#num#num))))`;
                                 `p2cg_nv (N0:num->num) (Nn:num->num) (FST(i:num#num#num#num)) +
                                  (NB:num->num->num) (NUMFST(FST i)) (SUC m) +
                                  p2cg_nv N0 Nn (FST(SND i)) + NB (NUMFST(FST(SND i))) (SUC m)`])
                    P2CG_GOOD_EVENTUALLY) THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN
      DISCH_TAC THEN MAP_EVERY X_GEN_TAC [`n:num`; `y:real^3`] THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `n:num` o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "p2cg_dk")) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      UNDISCH_TAC `p2cg_good rho D (FST(i:num#num#num#num)) (FST(SND i))
                     (p2cg_qv(FST(SND(SND i)))) (inv(&2 pow SND(SND(SND i))))` THEN
      REWRITE_TAC[p2cg_good] THEN STRIP_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      MAP_EVERY EXISTS_TAC [`p2cg_qv(FST(SND(SND(i:num#num#num#num))))`;
                            `inv(&2 pow SND(SND(SND(i:num#num#num#num))))`] THEN
      ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `s3:num->num`
    (X_CHOOSE_THEN `Ht:num#num#num#num->real^3->real^3` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`s3:num->num`; `Ht:num#num#num#num->real^3->real^3`] THEN
  ASM_REWRITE_TAC[] THEN MAP_EVERY X_GEN_TAC [`a:num`; `b:num`; `n:num`; `p:num`] THEN
  DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(a:num,b:num,n:num,p:num)`) THEN
  ASM_REWRITE_TAC[FST; SND]);;

(* Limits of finite transition values are zeros of D. *)

let P2CG_DV_ZERO_LIMIT = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc s D a y b (sg:num->num)
    (wk:num->real^3) w.
     p2cu_seq top atlas h x /\ p2cg_levels top atlas h x rho K N0 B NB P Nn yc /\
     p2cg_dsys top atlas h yc rho s D /\ y IN cball(vec 0,rho(NUMFST a) / &2) /\
     (!m n:num. m < n ==> sg m < sg n) /\
     (?N. !k. N <= k ==> wk k IN cball(vec 0,rho(NUMFST b) / &2) /\
                         p2cg_dk top atlas h yc (s(sg k)) a y b (wk k) = &0) /\
     (!e. &0 < e ==> ?N. !k. N <= k ==> norm(wk k - w) < e)
     ==> w IN cball(vec 0,rho(NUMFST b) / &2) /\ p2cg_dv D a y b w = &0`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (X_CHOOSE_THEN `N0k:num` (LABEL_TAC "fin"))
       (LABEL_TAC "conv"))))))) THEN
  FIRST_ASSUM(LABEL_TAC "sgbig" o MATCH_MP MONOTONE_BIGGER o
              check (fun th -> can (find_term ((=) `sg:num->num`)) (concl th))) THEN
  SUBGOAL_THEN `(w:real^3) IN cball(vec 0,rho(NUMFST b) / &2)` ASSUME_TAC THENL
   [REWRITE_TAC[IN_CBALL_0; GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    USE_THEN "conv" (MP_TAC o SPEC `norm(w:real^3) - rho(NUMFST b) / &2`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_TAC `N1:num`) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `N0k + N1:num`) THEN
    ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    USE_THEN "fin" (MP_TAC o SPEC `N0k + N1:num`) THEN
    ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[IN_CBALL_0] THEN
    MP_TAC(ISPECL [`w:real^3`; `(wk:num->real^3)(N0k + N1)`] NORM_TRIANGLE_SUB) THEN
    MP_TAC(ISPECL [`w:real^3`; `(wk:num->real^3)(N0k + N1)`] NORM_SUB) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN CONJ_TAC THENL
   [ALL_TAC;
    MP_TAC(ISPECL (p2cg_std @ [`s:num->num`; `D:num#num->real^(3,3)finite_sum->real^1`;
                               `a:num`; `y:real^3`; `b:num`; `w:real^3`]) P2CG_DV_POS) THEN
    ASM_REWRITE_TAC[]] THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  ABBREV_TAC `e = p2cg_dv D a (y:real^3) b (w:real^3)` THEN
  MP_TAC(ISPECL [`top:num->A topology`; `atlas:num->((A->bool)#(A->real^3))->bool`;
                 `h:num->A->real^3^3`; `yc:num->num->num->A`; `rho:num->real`;
                 `s:num->num`; `D:num#num->real^(3,3)finite_sum->real^1`; `a:num`; `b:num`]
                P2CG_DV_CONT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o C MP (ASSUME `(y:real^3) IN cball(vec 0,rho(NUMFST a) / &2)`) o
             SPEC `y:real^3` o CONJUNCT1) THEN
  REWRITE_TAC[continuous_on; o_THM; DIST_LIFT] THEN
  DISCH_THEN(MP_TAC o SPEC `w:real^3`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "cont"))) THEN
  MP_TAC(ISPECL [`top:num->A topology`; `atlas:num->((A->bool)#(A->real^3))->bool`;
                 `h:num->A->real^3^3`; `yc:num->num->num->A`; `rho:num->real`;
                 `s:num->num`; `D:num#num->real^(3,3)finite_sum->real^1`; `a:num`; `b:num`;
                 `e / &2`] P2CG_D_UNIF) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `N1:num` (LABEL_TAC "unif")) THEN
  USE_THEN "conv" (MP_TAC o C MP (ASSUME `&0 < d`) o SPEC `d:real`) THEN
  DISCH_THEN(X_CHOOSE_THEN `N2:num` (LABEL_TAC "dk")) THEN
  ABBREV_TAC `k = N0k + N1 + N2:num` THEN
  USE_THEN "fin" (MP_TAC o SPEC `k:num`) THEN
  ANTS_TAC THENL [EXPAND_TAC "k" THEN ARITH_TAC; STRIP_TAC] THEN
  USE_THEN "dk" (MP_TAC o SPEC `k:num`) THEN
  ANTS_TAC THENL [EXPAND_TAC "k" THEN ARITH_TAC; DISCH_TAC] THEN
  USE_THEN "cont" (MP_TAC o SPEC `(wk:num->real^3) k`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[dist]; DISCH_TAC] THEN
  USE_THEN "unif" (MP_TAC o SPECL [`(sg:num->num) k`; `y:real^3`; `(wk:num->real^3) k`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN USE_THEN "sgbig" (MP_TAC o SPEC `k:num`) THEN
    EXPAND_TAC "k" THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN UNDISCH_TAC
   `abs(p2cg_dv D a y b ((wk:num->real^3) k) - e) < e / &2` THEN
  REAL_ARITH_TAC);;

(* On a good ball the transition limit is the D-transition. *)

let P2CG_HT_EQ_TR = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc s D (s3:num->num)
    (Ht:real^3->real^3) a b n p y.
     p2cu_seq top atlas h x /\ p2cg_levels top atlas h x rho K N0 B NB P Nn yc /\
     p2cg_dsys top atlas h yc rho s D /\ (!m n:num. m < n ==> s3 m < s3 n) /\
     p2cg_good rho D a b (p2cg_qv n) (inv(&2 pow p)) /\
     (!e. &0 < e
          ==> ?Kn. !k y. Kn <= k /\ y IN ball(p2cg_qv n,inv(&2 pow p))
                         ==> norm(p2cg_T top atlas h yc rho (s(s3 k)) a b y - Ht y) < e) /\
     y IN ball(p2cg_qv n,inv(&2 pow p)) /\ y IN p2cg_om rho D a b
     ==> Ht y = p2cg_tr rho D a b y`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "conv") STRIP_ASSUME_TAC)))))) THEN
  FIRST_ASSUM(LABEL_TAC "s3big" o MATCH_MP MONOTONE_BIGGER o
              check (fun th -> can (find_term ((=) `s3:num->num`)) (concl th))) THEN
  MP_TAC(ISPECL (p2cg_std @ [`s:num->num`; `D:num#num->real^(3,3)finite_sum->real^1`;
                             `a:num`; `b:num`; `p2cg_qv n`; `inv(&2 pow p)`;
                             `p2cg_nv (N0:num->num) (Nn:num->num) a + p2cg_nv N0 Nn b`])
                P2CG_GOOD_EVENTUALLY) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `N:num` (LABEL_TAC "ev")) THEN
  UNDISCH_TAC `p2cg_good rho D a b (p2cg_qv n) (inv(&2 pow p))` THEN
  REWRITE_TAC[p2cg_good] THEN STRIP_TAC THEN
  ABBREV_TAC `c = p2cg_qv n` THEN ABBREV_TAC `r = inv(&2 pow p)` THEN
  SUBGOAL_THEN `(y:real^3) IN ball(c,&2 * r)` ASSUME_TAC THENL
   [UNDISCH_TAC `(y:real^3) IN ball(c,r)` THEN REWRITE_TAC[IN_BALL] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^3) IN cball(vec 0,rho(NUMFST a) / &2) /\ norm y < rho(NUMFST a)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `(y:real^3) IN ball(vec 0,rho(NUMFST a) / &2)` MP_TAC THENL
     [ASM_MESON_TAC[SUBSET; BALL_SUBSET_CBALL]; ALL_TAC] THEN
    MP_TAC(ISPECL (p2cg_std @ [`NUMFST a`]) P2CG_RHO_POS) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[IN_BALL_0; IN_CBALL_0] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL (p2cg_std @ [`s:num->num`; `D:num#num->real^(3,3)finite_sum->real^1`;
                             `a:num`; `b:num`; `y:real^3`]) P2CG_TR_PROPS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> CONV_TAC SYM_CONV THEN MATCH_MP_TAC(last(CONJUNCTS th))) THEN
  MATCH_MP_TAC P2CG_DV_ZERO_LIMIT THEN
  MAP_EVERY EXISTS_TAC (filter (fun t -> t <> `rho:num->real`) p2cg_std @
                       [`s:num->num`; `s3:num->num`;
     `\k. p2cg_T (top:num->A topology) atlas (h:num->A->real^3^3) (yc:num->num->num->A)
                 rho ((s:num->num)((s3:num->num) k)) a b y`]) THEN
  BETA_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [EXISTS_TAC `N:num` THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    USE_THEN "ev" (MP_TAC o SPEC `(s3:num->num) k`) THEN
    ANTS_TAC THENL [USE_THEN "s3big" (MP_TAC o SPEC `k:num`) THEN ASM_ARITH_TAC; ALL_TAC] THEN
    STRIP_TAC THEN
    MP_TAC(ISPECL (p2cg_std @ [`a:num`; `b:num`; `c:real^3`; `r:real`;
                               `(s:num->num)((s3:num->num) k)`]) P2CG_T_GOOD) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (LABEL_TAC "img")
      (CONJUNCTS_THEN2 (LABEL_TAC "nch") (K ALL_TAC)))) THEN
    CONJ_TAC THENL
     [USE_THEN "img" (MP_TAC o REWRITE_RULE[SUBSET; FORALL_IN_IMAGE]) THEN
      DISCH_THEN(MP_TAC o C MP (ASSUME `(y:real^3) IN ball(c,&2 * r)`) o SPEC `y:real^3`) THEN
      REWRITE_TAC[IN_BALL_0; IN_CBALL_0] THEN REAL_ARITH_TAC;
      REWRITE_TAC[p2cg_dk] THEN
      USE_THEN "nch" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `(y:real^3) IN ball(c,&2 * r)`)]) THEN
      REWRITE_TAC[GSYM p2cg_dk] THEN MATCH_MP_TAC P2CG_DK_DIAG THEN
      MAP_EVERY EXISTS_TAC [`x:num->A`; `rho:num->real`; `K:num->real`; `N0:num->num`;
                            `B:num->num->real`; `NB:num->num->num`; `P:num->num`;
                            `Nn:num->num`] THEN
      ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC];
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    USE_THEN "conv" (MP_TAC o C MP (ASSUME `&0 < e`) o SPEC `e:real`) THEN
    DISCH_THEN(X_CHOOSE_TAC `Kn:num`) THEN EXISTS_TAC `Kn:num` THEN
    X_GEN_TAC `k:num` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[]]);;

(* Every point of an overlap lies in a good rational ball. *)

let P2CG_GOOD_COVER = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc s D a b z.
     p2cu_seq top atlas h x /\ p2cg_levels top atlas h x rho K N0 B NB P Nn yc /\
     p2cg_dsys top atlas h yc rho s D /\ z IN p2cg_om rho D a b
     ==> ?n p. p2cg_good rho D a b (p2cg_qv n) (inv(&2 pow p)) /\
               z IN ball(p2cg_qv n,inv(&2 pow p))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [P2CG_IN_OM]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2CG_BALL4_CBALL o
              check (fun th -> concl th = `(z:real^3) IN ball(vec 0,rho(NUMFST a) / &4)`)) THEN
  MP_TAC(ISPECL (p2cg_std @ [`b:num`]) P2CG_CENTRE_CBALL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:num->A topology`; `atlas:num->((A->bool)#(A->real^3))->bool`;
                 `h:num->A->real^3^3`; `yc:num->num->num->A`; `rho:num->real`;
                 `s:num->num`; `D:num#num->real^(3,3)finite_sum->real^1`; `a:num`; `b:num`]
                P2CG_DV_CONT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o C MP (ASSUME `vec 0 IN cball(vec 0:real^3,rho(NUMFST b) / &2)`) o
             SPEC `vec 0:real^3` o CONJUNCT2) THEN
  REWRITE_TAC[continuous_on; o_THM; DIST_LIFT] THEN
  DISCH_THEN(MP_TAC o SPEC `z:real^3`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `rho(NUMFST b) / &8`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "cont"))) THEN
  MP_TAC(ISPECL [`inv(&2)`; `min d (rho(NUMFST a) / &4) / &4`] REAL_ARCH_POW_INV) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_POW_INV] THEN DISCH_THEN(X_CHOOSE_TAC `p:num`) THEN
  SUBGOAL_THEN `&0 < inv(&2 pow p)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC REAL_POW_LT THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`z:real^3`; `inv(&2 pow p)`] P2CG_QV_DENSE) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN
  MAP_EVERY EXISTS_TAC [`n:num`; `p:num`] THEN
  ABBREV_TAC `c = p2cg_qv n` THEN ABBREV_TAC `r = inv(&2 pow p)` THEN
  REWRITE_TAC[p2cg_good; IN_BALL] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!z':real^3. z' IN cball(c,&2 * r) ==> norm(z' - z) < &3 * r`
  ASSUME_TAC THENL
   [X_GEN_TAC `z':real^3` THEN REWRITE_TAC[IN_CBALL; dist] THEN
    MP_TAC(ISPECL [`z' - c:real^3`; `c - z:real^3`] NORM_TRIANGLE) THEN
    MP_TAC(ISPECL [`c:real^3`; `z':real^3`] NORM_SUB) THEN
    REWRITE_TAC[VECTOR_ARITH `(z' - c) + (c - z):real^3 = z' - z`] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `cball(c:real^3,&2 * r) SUBSET ball(vec 0,rho(NUMFST a) / &2)` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_BALL_0] THEN X_GEN_TAC `z':real^3` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o C MP (ASSUME `(z':real^3) IN cball(c,&2 * r)`) o SPEC `z':real^3`) THEN
    MP_TAC(ISPECL [`z':real^3`; `z:real^3`] NORM_TRIANGLE_SUB) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `z':real^3` THEN DISCH_TAC THEN
    USE_THEN "cont" (MP_TAC o SPEC `z':real^3`) THEN ANTS_TAC THENL
     [CONJ_TAC THENL
       [SUBGOAL_THEN `(z':real^3) IN ball(vec 0,rho(NUMFST a) / &2)` MP_TAC THENL
         [ASM SET_TAC[]; REWRITE_TAC[IN_BALL_0; IN_CBALL_0] THEN REAL_ARITH_TAC];
        REWRITE_TAC[dist] THEN
        FIRST_X_ASSUM(MP_TAC o C MP (ASSUME `(z':real^3) IN cball(c,&2 * r)`) o
                      SPEC `z':real^3`) THEN
        ASM_REAL_ARITH_TAC];
      ASM_REAL_ARITH_TAC];
    UNDISCH_TAC `norm(c - z:real^3) < r` THEN REWRITE_TAC[dist] THEN
    MESON_TAC[NORM_SUB]]);;

(* Smoothness of the transitions. *)

let P2CG_TR_SMOOTH = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc s D (s3:num->num) Ht.
     p2cu_seq top atlas h x /\ p2cg_levels top atlas h x rho K N0 B NB P Nn yc /\
     p2cg_dsys top atlas h yc rho s D /\ (!m n:num. m < n ==> s3 m < s3 n) /\
     (!a b n p.
        p2cg_good rho D a b (p2cg_qv n) (inv(&2 pow p))
        ==> smooth_map_on (ball(p2cg_qv n,inv(&2 pow p))) (Ht (a,b,n,p)) /\
            !l. ALL (\j. 1 <= j /\ j <= dimindex(:3)) l
                ==> !e. &0 < e
                        ==> ?Kn. !k y. Kn <= k /\ y IN ball(p2cg_qv n,inv(&2 pow p))
                                       ==> norm(iterated_partial l
                                                 (p2cg_T top atlas h yc rho (s(s3 k)) a b) y -
                                                iterated_partial l (Ht (a,b,n,p)) y) < e)
     ==> !a b. smooth_map_on (p2cg_om rho D a b) (p2cg_tr rho D a b)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MAP_EVERY X_GEN_TAC [`a:num`; `b:num`] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN CONJ_TAC THENL
   [MP_TAC(ISPECL (p2cg_std @ [`s:num->num`; `D:num#num->real^(3,3)finite_sum->real^1`;
                               `a:num`; `b:num`]) P2CG_OM_OPEN) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
  MP_TAC(ISPECL (p2cg_std @ [`s:num->num`; `D:num#num->real^(3,3)finite_sum->real^1`;
                             `a:num`; `b:num`; `z:real^3`]) P2CG_GOOD_COVER) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` (X_CHOOSE_THEN `p:num` STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`a:num`; `b:num`; `n:num`; `p:num`] o
                check (fun th -> can (find_term ((=) `Ht:num#num#num#num->real^3->real^3`))
                                     (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `[]:num list`)) THEN
  REWRITE_TAC[ALL; iterated_partial] THEN DISCH_TAC THEN
  EXISTS_TAC `ball(p2cg_qv n,inv(&2 pow p)) INTER p2cg_om rho D a b` THEN
  ASM_REWRITE_TAC[IN_INTER] THEN CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_INTER THEN REWRITE_TAC[OPEN_BALL] THEN
    MP_TAC(ISPECL (p2cg_std @ [`s:num->num`; `D:num#num->real^(3,3)finite_sum->real^1`;
                               `a:num`; `b:num`]) P2CG_OM_OPEN) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
  EXISTS_TAC `(Ht:num#num#num#num->real^3->real^3) (a,b,n,p)` THEN CONJ_TAC THENL
   [X_GEN_TAC `y:real^3` THEN REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN
    MATCH_MP_TAC P2CG_HT_EQ_TR THEN
    MAP_EVERY EXISTS_TAC (filter (fun t -> t <> `rho:num->real`) p2cg_std @
                          [`s:num->num`; `s3:num->num`; `n:num`; `p:num`]) THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
    EXISTS_TAC `ball(p2cg_qv n,inv(&2 pow p))` THEN ASM_REWRITE_TAC[INTER_SUBSET]]);;

(* ------------------------------------------------------------------------- *)
(* Compatibility of the limit metrics with the transitions.                  *)
(* The finite identities G_a = T^ G_b (pullback by the normal coordinate     *)
(* transition) pass to the limit: the Jacobians converge by the C^1 limits   *)
(* on good balls, the pulled-back metric values by uniform convergence and   *)
(* a uniform Lipschitz bound.                                                 *)
(* ------------------------------------------------------------------------- *)

let P2CG_PB_LIMIT = prove
 (`!(Jn:num->real^N^N) J (Gn:num->real^N^N) G0 (An:num->real^N^N) A.
     ((\n. vectorize(Jn n)) --> vectorize J) sequentially /\
     ((\n. vectorize(Gn n)) --> vectorize G0) sequentially /\
     ((\n. vectorize(An n)) --> vectorize A) sequentially /\
     (?N. !n. N <= n ==> An n = transp(Jn n) ** Gn n ** Jn n)
     ==> A = transp J ** G0 ** J`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_TAC `N:num`)))) THEN
  SUBGOAL_THEN `((\n. vectorize((Gn:num->real^N^N) n ** (Jn:num->real^N^N) n)) -->
                 vectorize((G0:real^N^N) ** (J:real^N^N))) sequentially` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`sequentially`;
                   `\(m1:real^(N,N)finite_prod) (m2:real^(N,N)finite_prod).
                      (vectorize:real^N^N->real^(N,N)finite_prod)(matrify m1 ** matrify m2)`;
                   `\n. (vectorize:real^N^N->real^(N,N)finite_prod)((Gn:num->real^N^N) n)`;
                   `\n. (vectorize:real^N^N->real^(N,N)finite_prod)((Jn:num->real^N^N) n)`;
                   `(vectorize:real^N^N->real^(N,N)finite_prod) G0`;
                   `(vectorize:real^N^N->real^(N,N)finite_prod) J`] LIM_BILINEAR) THEN
    ASM_REWRITE_TAC[BILINEAR_MATRIX_MUL; MATRIFY_VECTORIZE];
    ALL_TAC] THEN
  SUBGOAL_THEN `((\n. vectorize(transp((Jn:num->real^N^N) n))) -->
                 vectorize(transp(J:real^N^N))) sequentially` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`sequentially`; `vectorize o (transp:real^N^N->real^N^N) o matrify`;
                   `\n. (vectorize:real^N^N->real^(N,N)finite_prod)((Jn:num->real^N^N) n)`;
                   `(vectorize:real^N^N->real^(N,N)finite_prod) J`] LIM_LINEAR) THEN
    ASM_REWRITE_TAC[LINEAR_TRANSP; o_THM; MATRIFY_VECTORIZE];
    ALL_TAC] THEN
  SUBGOAL_THEN `((\n. vectorize(transp((Jn:num->real^N^N) n) ** (Gn:num->real^N^N) n ** Jn n)) -->
                 vectorize(transp(J:real^N^N) ** (G0:real^N^N) ** J)) sequentially`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`sequentially`;
                   `\(m1:real^(N,N)finite_prod) (m2:real^(N,N)finite_prod).
                      (vectorize:real^N^N->real^(N,N)finite_prod)(matrify m1 ** matrify m2)`;
                   `\n. (vectorize:real^N^N->real^(N,N)finite_prod)(transp((Jn:num->real^N^N) n))`;
                   `\n. (vectorize:real^N^N->real^(N,N)finite_prod)((Gn:num->real^N^N) n ** Jn n)`;
                   `(vectorize:real^N^N->real^(N,N)finite_prod)(transp J)`;
                   `(vectorize:real^N^N->real^(N,N)finite_prod)((G0:real^N^N) ** (J:real^N^N))`]
                  LIM_BILINEAR) THEN
    ASM_REWRITE_TAC[BILINEAR_MATRIX_MUL; MATRIFY_VECTORIZE];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM VECTORIZE_EQ] THEN
  MATCH_MP_TAC(ISPEC `sequentially` LIM_UNIQUE) THEN
  EXISTS_TAC `\n. (vectorize:real^N^N->real^(N,N)finite_prod)((An:num->real^N^N) n)` THEN
  ASM_REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN
  MATCH_MP_TAC LIM_TRANSFORM_EVENTUALLY THEN
  EXISTS_TAC `\n. (vectorize:real^N^N->real^(N,N)finite_prod)
                    (transp((Jn:num->real^N^N) n) ** (Gn:num->real^N^N) n ** Jn n)` THEN
  ASM_REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `N:num` THEN ASM_SIMP_TAC[]);;

let P2CG_ARITH2 = prove
 (`!c d e x. &0 <= c /\ &0 <= d /\ &0 < e /\ x <= c * d /\ d * (&2 * (c + &1)) < e
             ==> x < e / &2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `c * d <= (c + &1) * d` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* Convergence of Jacobian matrices from the convergence of first partials. *)

let P2CG_JAC_CONV = prove
 (`!(Tk:num->real^N->real^N) Hh z.
     (!j. 1 <= j /\ j <= dimindex(:N)
          ==> ((\k. partial_derivative j (Tk k) z) --> partial_derivative j Hh z) sequentially)
     ==> ((\k. vectorize(matrix(frechet_derivative (Tk k) (at z)))) -->
          vectorize(matrix(frechet_derivative Hh (at z)))) sequentially`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LIM_VECTORIZE_COMPONENTWISE] THEN
  MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[MATRIX_COMPONENT] THEN REWRITE_TAC[GSYM partial_derivative] THEN
  MATCH_MP_TAC LIM_COMPONENT THEN ASM_SIMP_TAC[]);;

(* Convergence of the metric of chart b at moving points. *)

let P2CG_GB_CONV = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc (s:num->num) (s3:num->num)
    (Gl:real^3->real^3^3) b (Tk:num->real^3) w0.
     p2cu_seq top atlas h x /\ p2cg_levels top atlas h x rho K N0 B NB P Nn yc /\
     (!m n:num. m < n ==> s m < s n) /\ (!m n:num. m < n ==> s3 m < s3 n) /\
     (!e. &0 < e
          ==> ?Kn. !n w. Kn <= n /\ w IN ball(vec 0,&3 * rho(NUMFST b) / &8)
                         ==> norm(vectorize(p2cg_G top atlas h yc (s n) b w) -
                                  vectorize(Gl w)) < e) /\
     norm w0 < rho(NUMFST b) / &4 /\
     (?N. !k. N <= k ==> norm(Tk k) < rho(NUMFST b) / &2) /\
     (!e. &0 < e ==> ?N. !k. N <= k ==> norm(Tk k - w0) < e)
     ==> ((\k. (vectorize:real^3^3->real^(3,3)finite_prod)
                 (p2cg_G top atlas h yc (s(s3 k)) b (Tk k))) --> vectorize(Gl w0))
         sequentially`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "gconv") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (X_CHOOSE_THEN `N0k:num` (LABEL_TAC "tin")) (LABEL_TAC "tconv")))))))) THEN
  FIRST_ASSUM(LABEL_TAC "sbig" o MATCH_MP MONOTONE_BIGGER o
              check (fun th -> can (find_term ((=) `s:num->num`)) (concl th))) THEN
  FIRST_ASSUM(LABEL_TAC "s3big" o MATCH_MP MONOTONE_BIGGER o
              check (fun th -> can (find_term ((=) `s3:num->num`)) (concl th))) THEN
  SUBGOAL_THEN `&0 < (rho:num->real)(NUMFST b)` ASSUME_TAC THENL
   [ASM_MESON_TAC[P2CG_RHO_POS]; ALL_TAC] THEN
  ABBREV_TAC `Lb = &(CARD(pde_index_lists 1 (:3))) * &(dimindex(:(3,3)finite_prod)) *
                   (sqrt(abs((B:num->num->real) (NUMFST b) 1)) + &1)` THEN
  SUBGOAL_THEN `&0 <= Lb` ASSUME_TAC THENL
   [EXPAND_TAC "Lb" THEN MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 <= x + &1`) THEN
    MATCH_MP_TAC SQRT_POS_LE THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!k (w:real^3) w'. p2cg_nv (N0:num->num) (Nn:num->num) b + (NB:num->num->num) (NUMFST b) 1 <= k /\
                      norm w < rho(NUMFST b) / &2 /\ norm w' < rho(NUMFST b) / &2
                      ==> norm((vectorize:real^3^3->real^(3,3)finite_prod)
                                 (p2cg_G (top:num->A topology) atlas (h:num->A->real^3^3)
                                         (yc:num->num->num->A) k b w) -
                               vectorize(p2cg_G top atlas h yc k b w')) <=
                          (&3 * Lb) * norm(w - w')`
  (LABEL_TAC "lip") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL (p2cg_std @ [`b:num`; `k:num`; `1`]) P2CG_G_FIELD) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "jet")) THEN
    MP_TAC(ISPECL [`(vectorize:real^3^3->real^(3,3)finite_prod) o
                    p2cg_G (top:num->A topology) atlas (h:num->A->real^3^3)
                           (yc:num->num->num->A) k b`;
                   `ball(vec 0:real^3,rho(NUMFST b) / &2)`;
                   `ball(vec 0:real^3,rho(NUMFST b) / &2)`;
                   `[]:num list`; `1`; `Lb:real`] P2CS_PARTIAL_LIPSCHITZ) THEN
    REWRITE_TAC[OPEN_BALL; CONVEX_BALL; SUBSET_REFL; ALL; LENGTH; iterated_partial; o_THM;
                DIMINDEX_3] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ANTS_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
        EXISTS_TAC `ball(vec 0:real^3,rho(NUMFST b))` THEN CONJ_TAC THENL
         [MATCH_MP_TAC SUBSET_BALL THEN ASM_REAL_ARITH_TAC;
          ASM_MESON_TAC[metric_field]];
        USE_THEN "jet" (fun th -> REWRITE_TAC[th])];
      DISCH_THEN(MP_TAC o SPECL [`w:real^3`; `w':real^3`]) THEN ASM_REWRITE_TAC[IN_BALL_0]];
    ALL_TAC] THEN
  REWRITE_TAC[LIM_SEQUENTIALLY; dist] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < e / &2 /\ &0 < e / (&2 * (&3 * Lb + &1))` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "gconv" (MP_TAC o C MP (ASSUME `&0 < e / &2`) o SPEC `e / &2`) THEN
  DISCH_THEN(X_CHOOSE_THEN `N1:num` (LABEL_TAC "g1")) THEN
  USE_THEN "tconv" (MP_TAC o C MP (ASSUME `&0 < e / (&2 * (&3 * Lb + &1))`) o
                    SPEC `e / (&2 * (&3 * Lb + &1))`) THEN
  DISCH_THEN(X_CHOOSE_THEN `N2:num` (LABEL_TAC "t2")) THEN
  EXISTS_TAC `N0k + N1 + N2 + p2cg_nv (N0:num->num) (Nn:num->num) b +
              (NB:num->num->num) (NUMFST b) 1` THEN
  X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `N1 <= (s3:num->num) k /\
                p2cg_nv (N0:num->num) (Nn:num->num) b + (NB:num->num->num) (NUMFST b) 1 <=
                (s:num->num)(s3 k)` STRIP_ASSUME_TAC THENL
   [USE_THEN "s3big" (MP_TAC o SPEC `k:num`) THEN
    USE_THEN "sbig" (MP_TAC o SPEC `(s3:num->num) k`) THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "tin" (MP_TAC o SPEC `k:num`) THEN ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
  USE_THEN "t2" (MP_TAC o SPEC `k:num`) THEN ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
  USE_THEN "g1" (MP_TAC o SPECL [`(s3:num->num) k`; `w0:real^3`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_BALL_0] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  USE_THEN "lip" (MP_TAC o SPECL [`(s:num->num)((s3:num->num) k)`; `(Tk:num->real^3) k`;
                                  `w0:real^3`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN
   `norm((vectorize:real^3^3->real^(3,3)finite_prod)
           (p2cg_G (top:num->A topology) atlas (h:num->A->real^3^3) (yc:num->num->num->A)
                   ((s:num->num)((s3:num->num) k)) b ((Tk:num->real^3) k)) -
         vectorize(p2cg_G top atlas h yc (s(s3 k)) b w0)) < e / &2`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P2CG_ARITH2 THEN
    MAP_EVERY EXISTS_TAC [`&3 * Lb`; `norm((Tk:num->real^3) k - w0)`] THEN
    ASM_REWRITE_TAC[NORM_POS_LE] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `norm((Tk:num->real^3) k - w0) < e / (&2 * (&3 * Lb + &1))` THEN
    SUBGOAL_THEN `&0 < &2 * (&3 * Lb + &1)` MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SIMP_TAC[REAL_LT_RDIV_EQ];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC
   `norm((vectorize:real^3^3->real^(3,3)finite_prod)
           (p2cg_G (top:num->A topology) atlas (h:num->A->real^3^3) (yc:num->num->num->A)
                   ((s:num->num)((s3:num->num) k)) b ((Tk:num->real^3) k)) -
         vectorize(p2cg_G top atlas h yc (s(s3 k)) b w0)) +
    norm(vectorize(p2cg_G top atlas h yc (s(s3 k)) b w0) - vectorize((Gl:real^3->real^3^3) w0))` THEN
  CONJ_TAC THENL [REWRITE_TAC[GSYM dist; DIST_TRIANGLE]; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* The compatibility of the limit metrics with the limit transitions. *)

let P2CG_COMPAT = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc s D (s3:num->num) Ht
    (Gl:num->real^3->real^3^3).
     p2cu_seq top atlas h x /\ p2cg_levels top atlas h x rho K N0 B NB P Nn yc /\
     p2cg_dsys top atlas h yc rho s D /\ (!m n:num. m < n ==> s3 m < s3 n) /\
     (!a b n p.
        p2cg_good rho D a b (p2cg_qv n) (inv(&2 pow p))
        ==> smooth_map_on (ball(p2cg_qv n,inv(&2 pow p))) (Ht (a,b,n,p)) /\
            !l. ALL (\j. 1 <= j /\ j <= dimindex(:3)) l
                ==> !e. &0 < e
                        ==> ?Kn. !k y. Kn <= k /\ y IN ball(p2cg_qv n,inv(&2 pow p))
                                       ==> norm(iterated_partial l
                                                 (p2cg_T top atlas h yc rho (s(s3 k)) a b) y -
                                                iterated_partial l (Ht (a,b,n,p)) y) < e) /\
     (!a e. &0 < e
            ==> ?Kn. !n w. Kn <= n /\ w IN ball(vec 0,&3 * rho(NUMFST a) / &8)
                           ==> norm(vectorize(p2cg_G top atlas h yc (s n) a w) -
                                    vectorize(Gl a w)) < e)
     ==> !a b z. z IN p2cg_om rho D a b
                 ==> Gl a z = mpullback (p2cg_tr rho D a b) (Gl b) z`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "ht") (LABEL_TAC "gl")))))) THEN
  MAP_EVERY X_GEN_TAC [`a:num`; `b:num`; `z:real^3`] THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [p2cg_dsys]) THEN
  FIRST_ASSUM(LABEL_TAC "s3big" o MATCH_MP MONOTONE_BIGGER o
              check (fun th -> can (find_term ((=) `s3:num->num`)) (concl th))) THEN
  MP_TAC(ISPECL (p2cg_std @ [`s:num->num`; `D:num#num->real^(3,3)finite_sum->real^1`;
                             `a:num`; `b:num`; `z:real^3`]) P2CG_GOOD_COVER) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` (X_CHOOSE_THEN `p:num` STRIP_ASSUME_TAC)) THEN
  USE_THEN "ht" (MP_TAC o C MP (ASSUME `p2cg_good rho D a b (p2cg_qv n) (inv(&2 pow p))`) o
                 SPECL [`a:num`; `b:num`; `n:num`; `p:num`]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "conv")) THEN
  ABBREV_TAC `Hi = (Ht:num#num#num#num->real^3->real^3) (a,b,n,p)` THEN
  SUBGOAL_THEN `!e. &0 < e
                    ==> ?Kn. !k y. Kn <= k /\ y IN ball(p2cg_qv n,inv(&2 pow p))
                                   ==> norm(p2cg_T (top:num->A topology) atlas
                                              (h:num->A->real^3^3) (yc:num->num->num->A) rho
                                              ((s:num->num)((s3:num->num) k)) a b y -
                                            (Hi:real^3->real^3) y) < e`
  (LABEL_TAC "c0") THENL
   [USE_THEN "conv" (MP_TAC o SPEC `[]:num list`) THEN REWRITE_TAC[ALL; iterated_partial];
    ALL_TAC] THEN
  SUBGOAL_THEN `open(ball(p2cg_qv n,inv(&2 pow p)) INTER p2cg_om rho D a b)` ASSUME_TAC THENL
   [MATCH_MP_TAC OPEN_INTER THEN REWRITE_TAC[OPEN_BALL] THEN
    MP_TAC(ISPECL (p2cg_std @ [`s:num->num`; `D:num#num->real^(3,3)finite_sum->real^1`;
                               `a:num`; `b:num`]) P2CG_OM_OPEN) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y. y IN ball(p2cg_qv n,inv(&2 pow p)) INTER p2cg_om rho D a b
                    ==> (Hi:real^3->real^3) y = p2cg_tr rho D a b y`
  (LABEL_TAC "eq") THENL
   [X_GEN_TAC `y:real^3` THEN REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN
    MATCH_MP_TAC P2CG_HT_EQ_TR THEN
    MAP_EVERY EXISTS_TAC (filter (fun t -> t <> `rho:num->real`) p2cg_std @
                          [`s:num->num`; `s3:num->num`; `n:num`; `p:num`]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `frechet_derivative (p2cg_tr rho D a b) (at z) =
                frechet_derivative (Hi:real^3->real^3) (at z)` ASSUME_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC GEOI_FRECHET_DERIVATIVE_LOCAL THEN
    EXISTS_TAC `ball(p2cg_qv n,inv(&2 pow p)) INTER p2cg_om rho D a b` THEN
    ASM_REWRITE_TAC[IN_INTER];
    ALL_TAC] THEN
  MP_TAC(ISPECL (p2cg_std @ [`s:num->num`; `D:num#num->real^(3,3)finite_sum->real^1`;
                             `a:num`; `b:num`; `z:real^3`]) P2CG_TR_PROPS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(STRIP_ASSUME_TAC o REWRITE_RULE[IN_BALL_0]) THEN
  SUBGOAL_THEN `(Hi:real^3->real^3) z = p2cg_tr rho D a b z` ASSUME_TAC THENL
   [USE_THEN "eq" MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_INTER]; ALL_TAC] THEN
  MP_TAC(ISPECL (p2cg_std @ [`s:num->num`; `D:num#num->real^(3,3)finite_sum->real^1`;
                             `a:num`; `b:num`; `p2cg_qv n`; `inv(&2 pow p)`;
                             `p2cg_nv (N0:num->num) (Nn:num->num) a + p2cg_nv N0 Nn b`])
                P2CG_GOOD_EVENTUALLY) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `N:num` (LABEL_TAC "ev")) THEN
  SUBGOAL_THEN
   `!k. N <= k
        ==> IMAGE (p2cg_T (top:num->A topology) atlas (h:num->A->real^3^3)
                     (yc:num->num->num->A) rho ((s:num->num)((s3:num->num) k)) a b)
                  (ball(p2cg_qv n,&2 * inv(&2 pow p))) SUBSET ball(vec 0,rho(NUMFST b) / &2) /\
            (!y. y IN ball(p2cg_qv n,&2 * inv(&2 pow p))
                 ==> p2cg_G top atlas h yc (s(s3 k)) a y =
                     mpullback (p2cg_T top atlas h yc rho (s(s3 k)) a b)
                               (p2cg_G top atlas h yc (s(s3 k)) b) y)`
  (LABEL_TAC "fin") THENL
   [X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    USE_THEN "ev" (MP_TAC o SPEC `(s3:num->num) k`) THEN
    ANTS_TAC THENL [USE_THEN "s3big" (MP_TAC o SPEC `k:num`) THEN ASM_ARITH_TAC; ALL_TAC] THEN
    STRIP_TAC THEN
    UNDISCH_TAC `p2cg_good rho D a b (p2cg_qv n) (inv(&2 pow p))` THEN
    REWRITE_TAC[p2cg_good] THEN STRIP_TAC THEN
    MP_TAC(ISPECL (p2cg_std @ [`a:num`; `b:num`; `p2cg_qv n`; `inv(&2 pow p)`;
                               `(s:num->num)((s3:num->num) k)`]) P2CG_T_GOOD) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(z:real^3) IN ball(p2cg_qv n,&2 * inv(&2 pow p))` ASSUME_TAC THENL
   [UNDISCH_TAC `(z:real^3) IN ball(p2cg_qv n,inv(&2 pow p))` THEN
    REWRITE_TAC[IN_BALL] THEN
    SUBGOAL_THEN `&0 < inv(&2 pow p)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC REAL_POW_LT THEN REAL_ARITH_TAC;
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[mpullback] THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC P2CG_PB_LIMIT THEN
  MAP_EVERY EXISTS_TAC
   [`\k. matrix(frechet_derivative (p2cg_T (top:num->A topology) atlas (h:num->A->real^3^3)
                  (yc:num->num->num->A) rho ((s:num->num)((s3:num->num) k)) a b) (at z))`;
    `\k. p2cg_G (top:num->A topology) atlas (h:num->A->real^3^3) (yc:num->num->num->A)
                ((s:num->num)((s3:num->num) k)) b
                (p2cg_T top atlas h yc rho (s(s3 k)) a b z)`;
    `\k. p2cg_G (top:num->A topology) atlas (h:num->A->real^3^3) (yc:num->num->num->A)
                ((s:num->num)((s3:num->num) k)) a z`] THEN
  BETA_TAC THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC P2CG_JAC_CONV THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN BETA_TAC THEN
    MP_TAC(ISPECL [`\k. partial_derivative j
                         (p2cg_T (top:num->A topology) atlas (h:num->A->real^3^3)
                            (yc:num->num->num->A) rho ((s:num->num)((s3:num->num) k)) a b)`;
                   `partial_derivative j (Hi:real^3->real^3)`;
                   `ball(p2cg_qv n,inv(&2 pow p))`; `z:real^3`] P2CS_UNIF_LIM) THEN
    BETA_TAC THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "conv" (MP_TAC o SPEC `[j]:num list`) THEN
    REWRITE_TAC[ALL; iterated_partial] THEN ASM_REWRITE_TAC[];
    SUBGOAL_THEN `?N. !k. N <= k
                          ==> norm(p2cg_T (top:num->A topology) atlas (h:num->A->real^3^3)
                                     (yc:num->num->num->A) rho
                                     ((s:num->num)((s3:num->num) k)) a b z) <
                              rho(NUMFST b) / &2`
    ASSUME_TAC THENL
     [EXISTS_TAC `N:num` THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
      USE_THEN "fin" (MP_TAC o CONJUNCT1 o C MP (ASSUME `N:num <= k`) o SPEC `k:num`) THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_BALL_0] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `!e. &0 < e
                      ==> ?N. !k. N <= k
                                  ==> norm(p2cg_T (top:num->A topology) atlas
                                             (h:num->A->real^3^3) (yc:num->num->num->A) rho
                                             ((s:num->num)((s3:num->num) k)) a b z -
                                           p2cg_tr rho D a b z) < e`
    ASSUME_TAC THENL
     [X_GEN_TAC `e:real` THEN DISCH_TAC THEN
      USE_THEN "c0" (MP_TAC o C MP (ASSUME `&0 < e`) o SPEC `e:real`) THEN
      DISCH_THEN(X_CHOOSE_TAC `Kn:num`) THEN EXISTS_TAC `Kn:num` THEN
      X_GEN_TAC `k:num` THEN DISCH_TAC THEN
      UNDISCH_TAC `(Hi:real^3->real^3) z = p2cg_tr rho D a b z` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL (p2cg_std @ [`s:num->num`; `s3:num->num`;
                               `(Gl:num->real^3->real^3^3) b`; `b:num`;
                               `\k. p2cg_T (top:num->A topology) atlas (h:num->A->real^3^3)
                                      (yc:num->num->num->A) rho
                                      ((s:num->num)((s3:num->num) k)) a b z`;
                               `p2cg_tr rho D a b z`]) P2CG_GB_CONV) THEN
    BETA_TAC THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN TRY(USE_THEN "gl" (ACCEPT_TAC o SPEC `b:num`));
      DISCH_THEN ACCEPT_TAC];
    REWRITE_TAC[LIM_SEQUENTIALLY; dist] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    USE_THEN "gl" (MP_TAC o C MP (ASSUME `&0 < e`) o SPECL [`a:num`; `e:real`]) THEN
    DISCH_THEN(X_CHOOSE_THEN `Kn:num` (LABEL_TAC "kn")) THEN EXISTS_TAC `Kn:num` THEN
    X_GEN_TAC `k:num` THEN DISCH_TAC THEN USE_THEN "kn" MATCH_MP_TAC THEN CONJ_TAC THENL
     [USE_THEN "s3big" (MP_TAC o SPEC `k:num`) THEN ASM_ARITH_TAC;
      FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [P2CG_IN_OM] o
                  check (fun th -> concl th = `(z:real^3) IN p2cg_om rho D a b`)) THEN
      REWRITE_TAC[IN_BALL_0] THEN
      MP_TAC(ISPECL (p2cg_std @ [`NUMFST a`]) P2CG_RHO_POS) THEN ASM_REWRITE_TAC[] THEN
      REAL_ARITH_TAC];
    EXISTS_TAC `N:num` THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    USE_THEN "fin" (MP_TAC o CONJUNCT2 o C MP (ASSUME `N:num <= k`) o SPEC `k:num`) THEN
    DISCH_THEN(MP_TAC o C MP (ASSUME `(z:real^3) IN ball(p2cg_qv n,&2 * inv(&2 pow p))`) o
               SPEC `z:real^3`) THEN
    REWRITE_TAC[mpullback]]);;

(* ------------------------------------------------------------------------- *)
(* The limit data along one subsequence and the glued limit.                 *)
(* p2cg_limit collects the D-limit, the limit metrics with their C-infinity  *)
(* convergence, the chart system with separation and compatibility, and the  *)
(* C-infinity convergence of the transitions near every point of an overlap. *)
(* The glued limit manifold comes from pc_p2c_cglim.                         *)
(* ------------------------------------------------------------------------- *)

let p2cg_limit = new_definition
 `p2cg_limit (top:num->A topology) (atlas:num->((A->bool)#(A->real^3))->bool)
             (h:num->A->real^3^3) (yc:num->num->num->A) (rho:num->real) (sq:num->num)
             (D:num#num->real^(3,3)finite_sum->real^1) (Gl:num->real^3->real^3^3) <=>
    p2cg_dsys top atlas h yc rho sq D /\
    p2cl_system (p2cg_dm rho) (p2cg_om rho D) (p2cg_tr rho D) /\
    p2cl_separated (p2cg_dm rho) (p2cg_om rho D) (p2cg_tr rho D) /\
    (!a. metric_field (ball(vec 0,&3 * rho(NUMFST a) / &8)) (Gl a) /\
         (!w v. w IN ball(vec 0,&3 * rho(NUMFST a) / &8)
                ==> inv(&2) * norm v pow 2 <= v dot (Gl a w ** v) /\
                    v dot (Gl a w ** v) <= &2 * norm v pow 2) /\
         !l. ALL (\j. 1 <= j /\ j <= dimindex(:3)) l
             ==> !e. &0 < e
                     ==> ?Kn. !n w. Kn <= n /\ w IN ball(vec 0,&3 * rho(NUMFST a) / &8)
                                    ==> norm(iterated_partial l
                                              ((vectorize:real^3^3->real^(3,3)finite_prod) o
                                               p2cg_G top atlas h yc (sq n) a) w -
                                             iterated_partial l (vectorize o Gl a) w) < e) /\
    (!a b z. z IN p2cg_om rho D a b
             ==> Gl a z = mpullback (p2cg_tr rho D a b) (Gl b) z) /\
    (!a b z. z IN p2cg_om rho D a b
             ==> ?r. &0 < r /\ ball(z,r) SUBSET p2cg_om rho D a b /\
                     !l. ALL (\j. 1 <= j /\ j <= dimindex(:3)) l
                         ==> !e. &0 < e
                                 ==> ?Kn. !k y. Kn <= k /\ y IN ball(z,r)
                                                ==> norm(iterated_partial l
                                                          (p2cg_T top atlas h yc rho (sq k) a b)
                                                          y -
                                                         iterated_partial l (p2cg_tr rho D a b)
                                                          y) < e)`;;

(* C-infinity convergence of the transitions near each point of an overlap. *)

let P2CG_TR_CONV = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc s D (s3:num->num) Ht.
     p2cu_seq top atlas h x /\ p2cg_levels top atlas h x rho K N0 B NB P Nn yc /\
     p2cg_dsys top atlas h yc rho s D /\ (!m n:num. m < n ==> s3 m < s3 n) /\
     (!a b n p.
        p2cg_good rho D a b (p2cg_qv n) (inv(&2 pow p))
        ==> smooth_map_on (ball(p2cg_qv n,inv(&2 pow p))) (Ht (a,b,n,p)) /\
            !l. ALL (\j. 1 <= j /\ j <= dimindex(:3)) l
                ==> !e. &0 < e
                        ==> ?Kn. !k y. Kn <= k /\ y IN ball(p2cg_qv n,inv(&2 pow p))
                                       ==> norm(iterated_partial l
                                                 (p2cg_T top atlas h yc rho (s(s3 k)) a b) y -
                                                iterated_partial l (Ht (a,b,n,p)) y) < e)
     ==> !a b z. z IN p2cg_om rho D a b
                 ==> ?r. &0 < r /\ ball(z,r) SUBSET p2cg_om rho D a b /\
                         !l. ALL (\j. 1 <= j /\ j <= dimindex(:3)) l
                             ==> !e. &0 < e
                                     ==> ?Kn. !k y. Kn <= k /\ y IN ball(z,r)
                                                    ==> norm(iterated_partial l
                                                              (p2cg_T top atlas h yc rho
                                                                      (s(s3 k)) a b) y -
                                                             iterated_partial l
                                                              (p2cg_tr rho D a b) y) < e`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ht"))))) THEN
  MAP_EVERY X_GEN_TAC [`a:num`; `b:num`; `z:real^3`] THEN DISCH_TAC THEN
  MP_TAC(ISPECL (p2cg_std @ [`s:num->num`; `D:num#num->real^(3,3)finite_sum->real^1`;
                             `a:num`; `b:num`; `z:real^3`]) P2CG_GOOD_COVER) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` (X_CHOOSE_THEN `p:num` STRIP_ASSUME_TAC)) THEN
  USE_THEN "ht" (MP_TAC o C MP (ASSUME `p2cg_good rho D a b (p2cg_qv n) (inv(&2 pow p))`) o
                 SPECL [`a:num`; `b:num`; `n:num`; `p:num`]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "conv")) THEN
  SUBGOAL_THEN `open(ball(p2cg_qv n,inv(&2 pow p)) INTER p2cg_om rho D a b)` ASSUME_TAC THENL
   [MATCH_MP_TAC OPEN_INTER THEN REWRITE_TAC[OPEN_BALL] THEN
    MP_TAC(ISPECL (p2cg_std @ [`s:num->num`; `D:num#num->real^(3,3)finite_sum->real^1`;
                               `a:num`; `b:num`]) P2CG_OM_OPEN) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `z:real^3` o GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL]) THEN
  ASM_REWRITE_TAC[IN_INTER] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `r:real` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `l:num list` THEN DISCH_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  USE_THEN "conv" (MP_TAC o C MP (ASSUME `&0 < e`) o SPEC `e:real` o
                   C MP (ASSUME `ALL (\j. 1 <= j /\ j <= dimindex(:3)) l`) o
                   SPEC `l:num list`) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `Kn:num` THEN
  DISCH_THEN(LABEL_TAC "kn") THEN MAP_EVERY X_GEN_TAC [`k:num`; `y:real^3`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(y:real^3) IN ball(p2cg_qv n,inv(&2 pow p)) INTER p2cg_om rho D a b`
  ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `iterated_partial l (p2cg_tr rho D a b) (y:real^3) =
                iterated_partial l ((Ht:num#num#num#num->real^3->real^3) (a,b,n,p)) y`
  SUBST1_TAC THENL
   [MATCH_MP_TAC TEXT_ITERATED_PARTIAL_LOCAL_AT THEN
    EXISTS_TAC `ball(p2cg_qv n,inv(&2 pow p)) INTER p2cg_om rho D a b` THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC P2CG_HT_EQ_TR THEN
    MAP_EVERY EXISTS_TAC (filter (fun t -> t <> `rho:num->real`) p2cg_std @
                          [`s:num->num`; `s3:num->num`; `n:num`; `p:num`]) THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [USE_THEN "conv" (MP_TAC o SPEC `[]:num list`) THEN REWRITE_TAC[ALL; iterated_partial];
      ASM SET_TAC[]];
    USE_THEN "kn" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]]);;

(* The limit data exist along a subsequence. *)

let P2CG_LIMIT_EXISTS = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc.
     p2cu_seq top atlas h x /\ p2cg_levels top atlas h x rho K N0 B NB P Nn yc
     ==> ?sq D Gl. p2cg_limit top atlas h yc rho sq D Gl`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL p2cg_std P2CG_DSYS_EXISTS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s1:num->num`
    (X_CHOOSE_THEN `D:num#num->real^(3,3)finite_sum->real^1` ASSUME_TAC)) THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [p2cg_dsys]) THEN
  MP_TAC(ISPECL (p2cg_std @ [`s1:num->num`]) P2CG_GLIM) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s2:num->num`
    (X_CHOOSE_THEN `Gl:num->real^3->real^3^3` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "gl")))) THEN
  SUBGOAL_THEN `p2cg_dsys (top:num->A topology) atlas (h:num->A->real^3^3)
                  (yc:num->num->num->A) rho ((s1:num->num) o (s2:num->num)) D`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P2CG_DSYS_SUBSEQ THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL (p2cg_std @ [`(s1:num->num) o (s2:num->num)`;
                             `D:num#num->real^(3,3)finite_sum->real^1`]) P2CG_TLIM) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s3:num->num`
    (X_CHOOSE_THEN `Ht:num#num#num#num->real^3->real^3` (CONJUNCTS_THEN2 ASSUME_TAC
       (LABEL_TAC "ht")))) THEN
  FIRST_ASSUM(LABEL_TAC "s3big" o MATCH_MP MONOTONE_BIGGER o
              check (fun th -> can (find_term ((=) `s3:num->num`)) (concl th))) THEN
  SUBGOAL_THEN
   `!a e. &0 < e
          ==> ?Kn. !n w. Kn <= n /\ w IN ball(vec 0,&3 * rho(NUMFST a) / &8)
                         ==> norm(vectorize(p2cg_G (top:num->A topology) atlas
                                    (h:num->A->real^3^3) (yc:num->num->num->A)
                                    (((s1:num->num) o (s2:num->num)) n) a w) -
                                  vectorize((Gl:num->real^3->real^3^3) a w)) < e`
  (LABEL_TAC "g0") THENL
   [REPEAT STRIP_TAC THEN
    USE_THEN "gl" (MP_TAC o C MP (ASSUME `&0 < e`) o SPEC `e:real` o
                   C MP (REWRITE_CONV[ALL] `ALL (\j. 1 <= j /\ j <= dimindex(:3)) []` |>
                          EQT_ELIM) o
                   SPEC `[]:num list` o CONJUNCT2 o CONJUNCT2 o SPEC `a:num`) THEN
    REWRITE_TAC[iterated_partial; o_THM];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`((s1:num->num) o (s2:num->num)) o (s3:num->num)`;
                        `D:num#num->real^(3,3)finite_sum->real^1`;
                        `Gl:num->real^3->real^3^3`] THEN
  REWRITE_TAC[p2cg_limit] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC P2CG_DSYS_SUBSEQ THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[p2cl_system] THEN
    MP_TAC(ISPECL (p2cg_std @ [`(s1:num->num) o (s2:num->num)`;
                               `D:num#num->real^(3,3)finite_sum->real^1`]) P2CG_SYS_LAWS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL (p2cg_std @ [`(s1:num->num) o (s2:num->num)`;
                               `D:num#num->real^(3,3)finite_sum->real^1`; `s3:num->num`;
                               `Ht:num#num#num#num->real^3->real^3`]) P2CG_TR_SMOOTH) THEN
    ASM_REWRITE_TAC[];
    MP_TAC(ISPECL (p2cg_std @ [`(s1:num->num) o (s2:num->num)`;
                               `D:num#num->real^(3,3)finite_sum->real^1`]) P2CG_SEPARATED) THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `a:num` THEN USE_THEN "gl" (MP_TAC o SPEC `a:num`) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `l:num list` THEN DISCH_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o C MP (ASSUME `&0 < e`) o SPEC `e:real` o
                  C MP (ASSUME `ALL (\j. 1 <= j /\ j <= dimindex(:3)) l`) o
                  SPEC `l:num list`) THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `Kn:num` THEN DISCH_THEN(LABEL_TAC "kn") THEN
    MAP_EVERY X_GEN_TAC [`n:num`; `w:real^3`] THEN STRIP_TAC THEN
    REWRITE_TAC[o_THM] THEN USE_THEN "kn" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "s3big" (MP_TAC o SPEC `n:num`) THEN ASM_ARITH_TAC;
    MP_TAC(ISPECL (p2cg_std @ [`(s1:num->num) o (s2:num->num)`;
                               `D:num#num->real^(3,3)finite_sum->real^1`; `s3:num->num`;
                               `Ht:num#num#num#num->real^3->real^3`;
                               `Gl:num->real^3->real^3^3`]) P2CG_COMPAT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_ACCEPT_TAC;
    MP_TAC(ISPECL (p2cg_std @ [`(s1:num->num) o (s2:num->num)`;
                               `D:num#num->real^(3,3)finite_sum->real^1`; `s3:num->num`;
                               `Ht:num#num#num#num->real^3->real^3`]) P2CG_TR_CONV) THEN
    ASM_REWRITE_TAC[o_THM]]);;

(* The glued limit manifold of a subsequence. *)

let P2CG_GLUED_LIMIT = prove
 (`!top atlas (h:num->A->real^3^3) x.
     P2C_REQ_CGT_STATEMENT (:A) /\ p2cu_seq top atlas h x
     ==> ?rho K N0 B NB P Nn yc sq D Gl (kp:num->real^3->real^3).
           p2cg_levels top atlas h x rho K N0 B NB P Nn yc /\
           p2cg_limit top atlas h yc rho sq D Gl /\
           p2cl_glue (p2cg_dm rho) (p2cg_om rho D) (p2cg_tr rho D) kp /\
           hausdorff_space (p2cl_top (p2cg_dm rho) kp) /\
           smooth_manifold_atlas (p2cl_top (p2cg_dm rho) kp) (p2cl_atlas (p2cg_dm rho) kp) /\
           riemannian_metric (p2cl_atlas (p2cg_dm rho) kp) (p2cl_metric (p2cg_dm rho) kp Gl) /\
           topspace (p2cl_top (p2cg_dm rho) kp) =
           UNIONS {IMAGE (kp i) (p2cg_dm rho i) | i IN (:num)} /\
           (!i. p2cl_chart (p2cg_dm rho) kp i IN p2cl_atlas (p2cg_dm rho) kp /\
                FST(p2cl_chart (p2cg_dm rho) kp i) = IMAGE (kp i) (p2cg_dm rho i) /\
                !z. z IN p2cg_dm rho i ==> SND(p2cl_chart (p2cg_dm rho) kp i) (kp i z) = z) /\
           (!i y. y IN p2cg_dm rho i
                  ==> metric_local (p2cl_atlas (p2cg_dm rho) kp) (p2cl_chart (p2cg_dm rho) kp i)
                                   (p2cl_metric (p2cg_dm rho) kp Gl) y = Gl i y)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:num->A topology`; `atlas:num->((A->bool)#(A->real^3))->bool`;
                 `h:num->A->real^3^3`; `x:num->A`] P2CG_LEVELS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL p2cg_std P2CG_LIMIT_EXISTS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `sq:num->num` (X_CHOOSE_THEN
    `D:num#num->real^(3,3)finite_sum->real^1` (X_CHOOSE_TAC `Gl:num->real^3->real^3^3`))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2cg_limit]) THEN
  MP_TAC(ISPECL [`p2cg_dm rho`; `p2cg_om rho D`; `p2cg_tr rho D`] P2CL_GLUE_EXISTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `kp:num->real^3->real^3`) THEN
  MAP_EVERY EXISTS_TAC [`rho:num->real`; `K:num->real`; `N0:num->num`; `B:num->num->real`;
                        `NB:num->num->num`; `P:num->num`; `Nn:num->num`;
                        `yc:num->num->num->A`; `sq:num->num`;
                        `D:num#num->real^(3,3)finite_sum->real^1`;
                        `Gl:num->real^3->real^3^3`; `kp:num->real^3->real^3`] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC P2CL_GLUED_MANIFOLD THEN
  MAP_EVERY EXISTS_TAC [`p2cg_om rho D`; `p2cg_tr rho D`] THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `a:num` THEN MATCH_MP_TAC METRIC_FIELD_SUBSET THEN
  EXISTS_TAC `ball(vec 0:real^3,&3 * rho(NUMFST a) / &8)` THEN
  ASM_REWRITE_TAC[p2cg_dm; OPEN_BALL] THEN MATCH_MP_TAC SUBSET_BALL THEN
  MP_TAC(ISPECL (p2cg_std @ [`NUMFST a`]) P2CG_RHO_POS) THEN ASM_REWRITE_TAC[] THEN
  REAL_ARITH_TAC);;

