(* ========================================================================= *)
(* Unit pc_p3_s16end (Part 3 proofs; MT Ch 16, for Prop 16.5): analytic      *)
(* tools for the closeness of the rescaled caps to the standard solution up  *)
(* to the end of a window.  C^0 time-Lipschitz bounds of quadratic forms     *)
(* (P3N_LIP_ENTRY), lck convergence from jet bounds and C^0 convergence      *)
(* (P3N_SEQ_LCK), Lemma 11.2 on a persisting open set with a flexible window *)
(* (P3N_L112_WINDOW), pinching (P3N_PINCH_RM, P3N_SCALAR_LE_RM) and          *)
(* Hamilton's compactness with variable right ends (P3N_HAM_VAR).            *)
(*                                                                           *)
(* Contents: time-Lipschitz bounds; jets and lck convergence; Lemma 11.2     *)
(* windows; pinching; Hamilton with variable ends.                           *)
(* ========================================================================= *)

needs "src/pc_p3_s16disc.ml";;
needs "src/pc_p2c_flham.ml";;
needs "src/pc_p2c_flasm.ml";;
needs "src/pc_p2a_par.ml";;
needs "src/pc_p2c_fl511.ml";;
needs "src/pc_rfa_pinch.ml";;
needs "src/pc_rfa_shi329.ml";;
needs "src/pc_p2c_flloc.ml";;
needs "src/pc_p2c_rmdjb.ml";;
needs "src/pc_p2c_flseq.ml";;
let p3n_saved_interface = !the_interface;;
needs "Multivariate/cross.ml";;
the_interface := p3n_saved_interface;;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* Time-Lipschitz bounds for local Ricci flows with bounded                *)
(* curvature: the quadratic forms (P3N_LIP_QFORM, from d/dt g = -2 Ric and *)
(* RFA_LRIC_BOUND) and, by polarization, the entries (P3N_LIP_ENTRY).      *)
(* ========================================================================= *)

let P3N_LIP_QFORM = prove
 (`!U a b (G:real->real^N->real^N^N) y v t1 t2 D Lm.
     lricci_flow U a b G /\ y IN U /\ a < t1 /\ t1 <= t2 /\ t2 < b /\
     &0 <= D /\ &0 <= Lm /\
     (!t. t1 <= t /\ t <= t2
          ==> lrm_deriv_norm2 0 (G t) y <= D /\ v dot (G t y ** v) <= Lm * (v dot v))
     ==> abs(v dot (G t2 y ** v) - v dot (G t1 y ** v))
         <= (&2 * &(dimindex(:N)) * sqrt D * Lm * (v dot v)) * (t2 - t1)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\s. v dot ((G:real->real^N->real^N^N) s y ** v)`;
                 `\s. --(&2) * lricci ((G:real->real^N->real^N^N) s) y v v`;
                 `real_interval[t1,t2]`;
                 `&2 * &(dimindex(:N)) * sqrt D * Lm * ((v:real^N) dot v)`]
                REAL_DIFFERENTIABLE_BOUND) THEN
  REWRITE_TAC[IS_REALINTERVAL_INTERVAL; IN_REAL_INTERVAL] THEN ANTS_TAC THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
      MATCH_MP_TAC RFA_LQFORM_DERIV THEN
      MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `a:real`; `b:real`] THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `metric_field U ((G:real->real^N->real^N^N) t)` ASSUME_TAC THENL
     [UNDISCH_TAC `lricci_flow U a b (G:real->real^N->real^N^N)` THEN
      REWRITE_TAC[lricci_flow] THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `t:real`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `(G:real->real^N->real^N^N) t`; `y:real^N`;
                   `D:real`; `v:real^N`] RFA_LRIC_BOUND) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 <= v dot ((G:real->real^N->real^N^N) t y ** v)` ASSUME_TAC THENL
     [MATCH_MP_TAC RFA_METRIC_QPOS THEN EXISTS_TAC `U:real^N->bool` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= &(dimindex(:N)) * sqrt D` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_POS; SQRT_POS_LE]; ALL_TAC] THEN
    SUBGOAL_THEN `(&(dimindex(:N)) * sqrt D) * (v dot ((G:real->real^N->real^N^N) t y ** v))
                  <= (&(dimindex(:N)) * sqrt D) * (Lm * ((v:real^N) dot v))` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `abs(lricci ((G:real->real^N->real^N^N) t) y v v) <=
                 (&(dimindex(:N)) * sqrt D) * (v dot (G t y ** v))` THEN
    REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_NEG; REAL_ABS_NUM] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`t2:real`; `t1:real`]) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `y = z ==> x <= y ==> x <= z`) THEN
  AP_TERM_TAC THEN ASM_REAL_ARITH_TAC);;

let P3N_LIP_ENTRY = prove
 (`!U a b (G:real->real^N->real^N^N) y t1 t2 D Lm p q.
     lricci_flow U a b G /\ y IN U /\ a < t1 /\ t1 <= t2 /\ t2 < b /\
     &0 <= D /\ &0 <= Lm /\
     1 <= p /\ p <= dimindex(:N) /\ 1 <= q /\ q <= dimindex(:N) /\
     (!t v. t1 <= t /\ t <= t2
            ==> lrm_deriv_norm2 0 (G t) y <= D /\ v dot (G t y ** v) <= Lm * (v dot v))
     ==> abs(G t2 y$p$q - G t1 y$p$q)
         <= (&8 * &(dimindex(:N)) * sqrt D * Lm) * (t2 - t1)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!t. t1 <= t /\ t <= t2
                    ==> transp((G:real->real^N->real^N^N) t y) = G t y`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    UNDISCH_TAC `lricci_flow U a b (G:real->real^N->real^N^N)` THEN
    REWRITE_TAC[lricci_flow] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `t:real` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> t = `metric_field:(real^N->bool)->(real^N->real^N^N)->bool`))
          (concl th))) THEN
    REWRITE_TAC[metric_field] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `y:real^N` o CONJUNCT2 o CONJUNCT2) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t. t1 <= t /\ t <= t2
        ==> (G:real->real^N->real^N^N) t y$p$q =
            ((basis p + basis q) dot (G t y ** (basis p + basis q)) -
             basis p dot (G t y ** basis p) - basis q dot (G t y ** basis q)) / &2`
  (fun th -> ASM_SIMP_TAC[th; REAL_LE_REFL]) THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `t:real`) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    REWRITE_TAC[MATRIX_VECTOR_MUL_ADD_LDISTRIB; DOT_LADD; DOT_RADD] THEN
    ASM_SIMP_TAC[RFB_BASIS_DOT_MATRIX] THEN
    SUBGOAL_THEN `(G:real->real^N->real^N^N) t y$q$p = G t y$p$q` SUBST1_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o AP_TERM `\M:real^N^N. M$p$q`) THEN
      ASM_SIMP_TAC[TRANSP_COMPONENT];
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `a:real`; `b:real`; `G:real->real^N->real^N^N`; `y:real^N`]
                P3N_LIP_QFORM) THEN
  DISCH_THEN(fun th ->
    MP_TAC(SPECL [`basis p + basis q:real^N`; `t1:real`; `t2:real`; `D:real`; `Lm:real`] th) THEN
    MP_TAC(SPECL [`basis p:real^N`; `t1:real`; `t2:real`; `D:real`; `Lm:real`] th) THEN
    MP_TAC(SPECL [`basis q:real^N`; `t1:real`; `t2:real`; `D:real`; `Lm:real`] th)) THEN
  ASM_SIMP_TAC[] THEN
  SUBGOAL_THEN `(basis p:real^N) dot basis p = &1 /\ (basis q:real^N) dot basis q = &1 /\
                (basis p + basis q:real^N) dot (basis p + basis q) <= &4`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[DOT_BASIS_BASIS; DOT_LADD; DOT_RADD] THEN
    COND_CASES_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `X = (basis p + basis q:real^N) dot (basis p + basis q)` THEN
  SUBGOAL_THEN `&0 <= &(dimindex(:N)) * sqrt D * Lm * (t2 - t1)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[SQRT_POS_LE] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(&(dimindex(:N)) * sqrt D * Lm * (t2 - t1)) * X <=
                (&(dimindex(:N)) * sqrt D * Lm * (t2 - t1)) * &4` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `&0 <= &(dimindex(:N)) * sqrt D * Lm * (t2 - t1)` THEN
  REAL_ARITH_TAC);;

(* ========================================================================= *)
(* From entrywise jet bounds and entrywise C^0 convergence to               *)
(* lck_dist2 convergence (P3N_SEQ_LCK, via P2CI_LCK_COMPACT).  P3N_VEC_JET  *)
(* is RFA_JB_VEC_NORM for an arbitrary index predicate.                      *)
(* ========================================================================= *)

let P3N_VEC_JET = prove
 (`!(P:B->bool) V K m (Gc:B->real^N->real^N^N).
     open V /\ K SUBSET V /\ (!i. P i ==> metric_field V (Gc i)) /\
     (!p q. 1 <= p /\ p <= dimindex(:N) /\ 1 <= q /\ q <= dimindex(:N)
            ==> ?C. !i l y. P i /\ l IN pde_index_lists m (:N) /\ y IN K
                            ==> abs(drop(iterated_partial l
                                   (\z. lift(Gc i z$p$q)) y)) <= C)
     ==> ?C. !i l y. P i /\ l IN pde_index_lists m (:N) /\ y IN K
                     ==> norm(iterated_partial l
                                ((vectorize:real^N^N->real^(N,N)finite_prod) o Gc i) y) <= C`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "mf") (LABEL_TAC "jb")))) THEN
  SUBGOAL_THEN
   `!p q. ?C. 1 <= p /\ p <= dimindex(:N) /\ 1 <= q /\ q <= dimindex(:N)
              ==> !i l y. P i /\ l IN pde_index_lists m (:N) /\ y IN K
                          ==> abs(drop(iterated_partial l
                                   (\z. lift((Gc:B->real^N->real^N^N) i z$p$q)) y)) <= C`
  MP_TAC THENL
   [MAP_EVERY X_GEN_TAC [`p:num`; `q:num`] THEN REWRITE_TAC[RIGHT_EXISTS_IMP_THM] THEN
    DISCH_TAC THEN USE_THEN "jb" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `Cp:num->num->real` (LABEL_TAC "cp")) THEN
  EXISTS_TAC `sum(1..dimindex(:(N,N)finite_prod))
                (\k. (Cp:num->num->real) (1 + (k - 1) DIV dimindex(:N))
                                         (1 + (k - 1) MOD dimindex(:N)))` THEN
  MAP_EVERY X_GEN_TAC [`i:B`; `l:num list`; `y:real^N`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(y:real^N) IN V` ASSUME_TAC THENL
   [UNDISCH_TAC `K SUBSET (V:real^N->bool)` THEN UNDISCH_TAC `(y:real^N) IN K` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on V ((vectorize:real^N^N->real^(N,N)finite_prod) o
                                 (Gc:B->real^N->real^N^N) i)` ASSUME_TAC THENL
   [SUBGOAL_THEN `metric_field V ((Gc:B->real^N->real^N^N) i)` MP_TAC THENL
     [USE_THEN "mf" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; SIMP_TAC[metric_field]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(1..dimindex(:(N,N)finite_prod))
                (\k. abs((iterated_partial l
                         ((vectorize:real^N^N->real^(N,N)finite_prod) o
                          (Gc:B->real^N->real^N^N) i) y)$k))` THEN
  REWRITE_TAC[NORM_LE_L1] THEN MATCH_MP_TAC SUM_LE_NUMSEG THEN
  X_GEN_TAC `k:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `1 <= 1 + (k - 1) DIV dimindex(:N) /\ 1 + (k - 1) DIV dimindex(:N) <= dimindex(:N) /\
    1 <= 1 + (k - 1) MOD dimindex(:N) /\ 1 + (k - 1) MOD dimindex(:N) <= dimindex(:N)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `1 <= 1 + a`] THEN CONJ_TAC THEN
    MATCH_MP_TAC(ARITH_RULE `a < b ==> 1 + a <= b`) THEN
    SIMP_TAC[DIVISION; LE_1; DIMINDEX_GE_1; RDIV_LT_EQ] THEN
    UNDISCH_TAC `k <= dimindex(:(N,N)finite_prod)` THEN
    UNDISCH_TAC `1 <= k` THEN REWRITE_TAC[DIMINDEX_FINITE_PROD] THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`l:num list`; `V:real^N->bool`;
                 `(vectorize:real^N^N->real^(N,N)finite_prod) o (Gc:B->real^N->real^N^N) i`;
                 `k:num`; `y:real^N`] RFA_ITERATED_PARTIAL_LIFT_COMPONENT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o AP_TERM `drop`) THEN REWRITE_TAC[LIFT_DROP] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  SUBGOAL_THEN
   `(\z. lift((((vectorize:real^N^N->real^(N,N)finite_prod) o
                (Gc:B->real^N->real^N^N) i) z)$k)) =
    (\z. lift(Gc i z$(1 + (k - 1) DIV dimindex(:N))$(1 + (k - 1) MOD dimindex(:N))))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM] THEN GEN_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC VECTORIZE_COMPONENT THEN
    UNDISCH_TAC `k <= dimindex(:(N,N)finite_prod)` THEN
    UNDISCH_TAC `1 <= k` THEN REWRITE_TAC[DIMINDEX_FINITE_PROD] THEN ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "cp" (MP_TAC o SPECL [`1 + (k - 1) DIV dimindex(:N)`;
                                 `1 + (k - 1) MOD dimindex(:N)`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let P3N_VEC_C0 = prove
 (`!(A:real^N^N) B e.
     (!p q. 1 <= p /\ p <= dimindex(:N) /\ 1 <= q /\ q <= dimindex(:N)
            ==> abs(A$p$q - B$p$q) <= e)
     ==> norm((vectorize:real^N^N->real^(N,N)finite_prod) A - vectorize B)
         <= &(dimindex(:N) * dimindex(:N)) * e`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(1..dimindex(:(N,N)finite_prod))
                (\k. abs(((vectorize:real^N^N->real^(N,N)finite_prod) A - vectorize B)$k))` THEN
  REWRITE_TAC[NORM_LE_L1] THEN
  REWRITE_TAC[GSYM DIMINDEX_FINITE_PROD] THEN
  GEN_REWRITE_TAC (RAND_CONV o LAND_CONV o RAND_CONV) [GSYM CARD_NUMSEG_1] THEN
  MATCH_MP_TAC SUM_BOUND THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  X_GEN_TAC `k:num` THEN STRIP_TAC THEN
  ASM_SIMP_TAC[VECTOR_SUB_COMPONENT; VECTORIZE_COMPONENT; GSYM DIMINDEX_FINITE_PROD] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  REWRITE_TAC[ARITH_RULE `1 <= 1 + a`] THEN CONJ_TAC THEN
  MATCH_MP_TAC(ARITH_RULE `a < b ==> 1 + a <= b`) THEN
  SIMP_TAC[DIVISION; LE_1; DIMINDEX_GE_1; RDIV_LT_EQ] THEN
  UNDISCH_TAC `k <= dimindex(:(N,N)finite_prod)` THEN
  UNDISCH_TAC `1 <= k` THEN REWRITE_TAC[DIMINDEX_FINITE_PROD] THEN ARITH_TAC);;

let P3N_NSUM2_BOUND = prove
 (`!(f:num->num->num) n p q.
     1 <= p /\ p <= n /\ 1 <= q /\ q <= n
     ==> f p q <= nsum(1..n) (\p. nsum(1..n) (\q. f p q))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC `nsum(1..n) (\q. (f:num->num->num) p q)` THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`\q. (f:num->num->num) p q`; `nsum(1..n) (\q. (f:num->num->num) p q)`;
                   `1..n`] NSUM_POS_BOUND) THEN
    REWRITE_TAC[FINITE_NUMSEG; LE_REFL; IN_NUMSEG] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`\p. nsum(1..n) (\q. (f:num->num->num) p q)`;
                   `nsum(1..n) (\p. nsum(1..n) (\q. (f:num->num->num) p q))`;
                   `1..n`] NSUM_POS_BOUND) THEN
    REWRITE_TAC[FINITE_NUMSEG; LE_REFL; IN_NUMSEG] THEN DISCH_THEN(MP_TAC o SPEC `p:num`) THEN
    ASM_REWRITE_TAC[]]);;

let P3N_SEQ_LCK = prove
 (`!V K K' (G0:real^N->real^N^N) (Hs:num->real^N->real^N^N).
     open V /\ compact K /\ K SUBSET V /\ K' SUBSET V /\
     (!z. z IN K ==> ?r. &0 < r /\ ball(z,r) SUBSET K') /\
     metric_field V G0 /\ (!k. metric_field V (Hs k)) /\
     (!m p q. 1 <= p /\ p <= dimindex(:N) /\ 1 <= q /\ q <= dimindex(:N)
              ==> ?B N. !k l y. N <= k /\ l IN pde_index_lists m (:N) /\ y IN K'
                                ==> abs(drop(iterated_partial l
                                       (\z. lift(Hs k z$p$q)) y)) <= B) /\
     (!e. &0 < e
          ==> ?N. !k y p q. N <= k /\ y IN K' /\
                            1 <= p /\ p <= dimindex(:N) /\ 1 <= q /\ q <= dimindex(:N)
                            ==> abs(Hs k y$p$q - G0 y$p$q) < e)
     ==> !m e. &0 < e ==> ?N. !k y. N <= k /\ y IN K ==> lck_dist2 m G0 (Hs k) y < e`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (LABEL_TAC "nb") (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (LABEL_TAC "mf") (CONJUNCTS_THEN2 (LABEL_TAC "jet")
    (LABEL_TAC "c0"))))))))) THEN
  MATCH_MP_TAC P2CI_LCK_COMPACT THEN EXISTS_TAC `V:real^N->bool` THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
  USE_THEN "nb" (MP_TAC o SPEC `z:real^N`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[p2ci_near] THEN EXISTS_TAC `r:real` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `ball(z:real^N,r) SUBSET V` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [EXISTS_TAC `0` THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `V:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "mf" (MP_TAC o SPEC `k:num`) THEN
    SIMP_TAC[metric_field];
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `V:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `metric_field V (G0:real^N->real^N^N)` THEN
    SIMP_TAC[metric_field];
    X_GEN_TAC `m:num` THEN
    USE_THEN "jet" (MP_TAC o REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM] o
                    SPEC `m:num`) THEN
    DISCH_THEN(X_CHOOSE_THEN `Bq:num->num->real` (X_CHOOSE_THEN `Nq:num->num->num`
      (LABEL_TAC "jq"))) THEN
    ABBREV_TAC `N0 = nsum(1..dimindex(:N)) (\p. nsum(1..dimindex(:N))
                                              (\q. (Nq:num->num->num) p q))` THEN
    MP_TAC(ISPECL [`\k:num. N0 <= k`; `V:real^N->bool`; `K':real^N->bool`; `m:num`;
                   `Hs:num->real^N->real^N^N`] P3N_VEC_JET) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      REPEAT STRIP_TAC THEN EXISTS_TAC `(Bq:num->num->real) p q` THEN
      MAP_EVERY X_GEN_TAC [`k:num`; `l:num list`; `y:real^N`] THEN STRIP_TAC THEN
      USE_THEN "jq" (MP_TAC o SPECL [`p:num`; `q:num`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `N0:num` THEN ASM_REWRITE_TAC[] THEN
      EXPAND_TAC "N0" THEN MATCH_MP_TAC P3N_NSUM2_BOUND THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_TAC `C:real`) THEN
    EXISTS_TAC `&(CARD(pde_index_lists m (:N))) * C` THEN EXISTS_TAC `N0:num` THEN
    MAP_EVERY X_GEN_TAC [`k:num`; `y:real^N`] THEN STRIP_TAC THEN
    REWRITE_TAC[pde_jetn] THEN MATCH_MP_TAC SUM_BOUND THEN
    REWRITE_TAC[PDE_INDEX_LISTS_FINITE] THEN X_GEN_TAC `l:num list` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`k:num`; `l:num list`; `y:real^N`]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM SET_TAC[];
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    USE_THEN "c0" (MP_TAC o SPEC `e / (&2 * &(dimindex(:N) * dimindex(:N)))`) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LT_MUL THEN REWRITE_TAC[REAL_OF_NUM_LT; LE_1; MULT_EQ_0] THEN
      SIMP_TAC[DIMINDEX_GE_1; LE_1; ARITH_RULE `0 < 2`; MULT_EQ_0;
               ARITH_RULE `1 <= n ==> ~(n = 0)`] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN EXISTS_TAC `N:num` THEN
    MAP_EVERY X_GEN_TAC [`k:num`; `y:real^N`] THEN STRIP_TAC THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `&(dimindex(:N) * dimindex(:N)) *
                e / (&2 * &(dimindex(:N) * dimindex(:N)))` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[o_THM] THEN MATCH_MP_TAC P3N_VEC_C0 THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC REAL_LT_IMP_LE THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      SUBGOAL_THEN `~(&(dimindex(:N) * dimindex(:N)) = &0)` ASSUME_TAC THENL
       [REWRITE_TAC[REAL_OF_NUM_EQ; MULT_EQ_0] THEN
        SIMP_TAC[DIMINDEX_GE_1; ARITH_RULE `1 <= n ==> ~(n = 0)`];
        ALL_TAC] THEN
      SUBGOAL_THEN `&(dimindex(:N) * dimindex(:N)) *
                    e / (&2 * &(dimindex(:N) * dimindex(:N))) = e / &2`
      SUBST1_TAC THENL
       [UNDISCH_TAC `~(&(dimindex(:N) * dimindex(:N)) = &0)` THEN CONV_TAC REAL_FIELD;
        UNDISCH_TAC `&0 < e` THEN REAL_ARITH_TAC]]]);;

(* ========================================================================= *)
(* MT Lemma 11.2 on a whole persisting open set, with radii                 *)
(* adapted to each point (P3N_L112_WINDOW): its time window depends only on *)
(* the curvature at the base time, so a small enough radius (inside the set) *)
(* gives the bound at every point of the set, not only away from its edge.  *)
(* ========================================================================= *)

let P3N_OPEN_TRANSFER = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) top' (atlas':((A->bool)#(A->real^N))->bool) W U.
     mfd_diffeo top atlas W top' atlas' W (\y. y) (\y. y) /\ open_in top U /\ U SUBSET W
     ==> open_in top' U`,
  REWRITE_TAC[mfd_diffeo; HOMEOMORPHIC_MAPS_ID] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC OPEN_IN_TRANS_FULL THEN EXISTS_TAC `W:A->bool` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC OPEN_IN_SUBSET_TOPSPACE THEN ASM_REWRITE_TAC[]);;

let P3N_L112_WINDOW = prove
 (`!u:A->bool.
     P2_LEMMA_11_2_STATEMENT u
     ==> ?eps0. &0 < eps0 /\
         !(hs:(A)rfs_history) C eps r0 B t0 t1 D.
           rfs_history_ok hs /\ p2c_regular_view (rfs_view hs) /\
           &1 < C /\ &0 < eps /\ eps <= eps0 /\ &0 < r0 /\
           (!x t. t0 <= t /\ t <= t1 /\ x IN topspace(rfs_top_at hs t) /\
                  inv(r0 pow 2) <= rfs_vscalar (rfs_view hs) t x
                  ==> p3_canon_at (rfs_view hs) C eps x t) /\
           t0 < t1 /\ open_in (rfs_vtop (rfs_view hs) t0) B /\
           rfs_persists (rfs_view hs) B t0 t1 /\ &0 <= D /\
           (!z. z IN B ==> rfs_vscalar (rfs_view hs) t0 z <= D) /\
           t1 - t0 <= inv(&16 * max C (&2) * (D + inv(r0 pow 2)))
           ==> !s z. t0 <= s /\ s <= t1 /\ z IN B
                     ==> rfs_vscalar (rfs_view hs) s z <= &2 * (D + inv(r0 pow 2))`,
  GEN_TAC THEN REWRITE_TAC[P2_LEMMA_11_2_STATEMENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `eps0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "L112"))) THEN
  EXISTS_TAC `eps0:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`hs:(A)rfs_history`; `C:real`; `eps:real`; `r0:real`; `B:A->bool`;
                       `t0:real`; `t1:real`; `D:real`] THEN
  STRIP_TAC THEN MAP_EVERY X_GEN_TAC [`s:real`; `z:A`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < inv(r0 pow 2)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_INV THEN ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  ASM_CASES_TAC `s:real = t0` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `D:real` THEN ASM_SIMP_TAC[] THEN
    UNDISCH_TAC `&0 < inv(r0 pow 2)` THEN UNDISCH_TAC `&0 <= D` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `t0 < s` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(z:A) IN topspace(rfs_vtop (rfs_view (hs:(A)rfs_history)) t0)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`rfs_vtop (rfs_view (hs:(A)rfs_history)) t0`; `B:A->bool`] OPEN_IN_SUBSET) THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(z:A) IN B` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(z:A) IN topspace(rfs_top_at (hs:(A)rfs_history) t0)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[GSYM P2C_RFS_VIEW_PARTS]; ALL_TAC] THEN
  MP_TAC(ISPECL [`rfs_view (hs:(A)rfs_history)`; `t0:real`; `z:A`] P2C_REGULAR_SLICE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`rfs_vtop (rfs_view (hs:(A)rfs_history)) t0`;
                 `rfs_vatlas (rfs_view (hs:(A)rfs_history)) t0`;
                 `rfs_vmetric (rfs_view (hs:(A)rfs_history)) t0`; `B:A->bool`; `z:A`]
                MFD_BALL_NEIGHBOURHOOD_BASE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `r1:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `Cp = max C (&2)` THEN
  SUBGOAL_THEN `&2 <= Cp /\ C <= Cp /\ &0 < Cp` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "Cp" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `Rz = rfs_vscalar (rfs_view (hs:(A)rfs_history)) t0 z` THEN
  SUBGOAL_THEN `Rz <= D` ASSUME_TAC THENL
   [EXPAND_TAC "Rz" THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `rr = min r1 (inv(&2 * Cp * sqrt(max Rz (inv(r0 pow 2)))))` THEN
  SUBGOAL_THEN `&0 < rr /\ rr <= r1 /\
                rr <= inv(&2 * Cp * sqrt(max Rz (inv(r0 pow 2))))` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "rr" THEN REWRITE_TAC[REAL_LT_MIN; REAL_MIN_LE; REAL_LE_REFL] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_INV THEN
    MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SQRT_POS_LT THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `rfs_vball (rfs_view (hs:(A)rfs_history)) t0 z rr SUBSET B` ASSUME_TAC THENL
   [REWRITE_TAC[P2C_VIEW_EXPAND] THEN MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `mfd_ball (rfs_vtop (rfs_view (hs:(A)rfs_history)) t0,
                          rfs_vatlas (rfs_view hs) t0) (rfs_vmetric (rfs_view hs) t0) z r1` THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; mfd_ball; IN_ELIM_THM] THEN GEN_TAC THEN
    MATCH_MP_TAC MONO_AND THEN REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!x t. t0 <= t /\ t <= s /\ x IN topspace(rfs_top_at (hs:(A)rfs_history) t) /\
                      inv(r0 pow 2) <= rfs_vscalar (rfs_view hs) t x
                      ==> p3_canon_at (rfs_view hs) Cp eps x t` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPEC `UNIV:A->bool` P2B_CANON_MONO_C) THEN
    REWRITE_TAC[P2B_CANON_MONO_C_STATEMENT] THEN DISCH_THEN MATCH_MP_TAC THEN
    EXISTS_TAC `C:real` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`rfs_view (hs:(A)rfs_history)`; `t:real`; `x:A`] P2C_REGULAR_SLICE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[P2C_RFS_VIEW_PARTS]; STRIP_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (find_term (fun t -> t = `t1:real`)) (concl th) && is_forall (concl th))) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `abs(s - t0) <= inv(&16 * Cp * (max (&0) Rz + inv(r0 pow 2)))` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(&16 * Cp * (D + inv(r0 pow 2)))` THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `t1 - t0 <= inv(&16 * Cp * (D + inv(r0 pow 2)))` THEN
      UNDISCH_TAC `t0 < s` THEN UNDISCH_TAC `s <= t1` THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `&0 < inv(r0 pow 2)` THEN REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
         [UNDISCH_TAC `&0 < Cp` THEN REAL_ARITH_TAC; ALL_TAC] THEN
        UNDISCH_TAC `Rz <= D` THEN UNDISCH_TAC `&0 <= D` THEN REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `rfs_persists (rfs_view (hs:(A)rfs_history)) (rfs_vball (rfs_view hs) t0 z rr) t0 s`
  ASSUME_TAC THENL
   [REWRITE_TAC[P2C_VIEW_EXPAND] THEN X_GEN_TAC `u:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `rfs_persists (rfs_view (hs:(A)rfs_history)) B t0 u` ASSUME_TAC THENL
     [UNDISCH_TAC `rfs_persists (rfs_view (hs:(A)rfs_history)) B t0 t1` THEN
      REWRITE_TAC[P2C_VIEW_EXPAND] THEN DISCH_TAC THEN X_GEN_TAC `u':real` THEN
      STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o SPECL [`B:A->bool`; `t0:real`; `u:real`] o last o CONJUNCTS o
                GEN_REWRITE_RULE I [p2c_regular_view]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `rfs_persists (rfs_view (hs:(A)rfs_history)) B t0 t1` THEN
      REWRITE_TAC[P2C_VIEW_EXPAND] THEN DISCH_THEN(MP_TAC o SPEC `u:real`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      MATCH_MP_TAC(INST_TYPE [`:3`,`:N`] P3N_OPEN_TRANSFER) THEN
      MAP_EVERY EXISTS_TAC [`rfs_vtop (rfs_view (hs:(A)rfs_history)) t0`;
                            `rfs_vatlas (rfs_view (hs:(A)rfs_history)) t0`;
                            `rfs_vatlas (rfs_view (hs:(A)rfs_history)) u`; `B:A->bool`] THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC MFD_BALL_OPEN THEN ASM_REWRITE_TAC[];
        UNDISCH_TAC `rfs_vball (rfs_view (hs:(A)rfs_history)) t0 z rr SUBSET B` THEN
        REWRITE_TAC[P2C_VIEW_EXPAND]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `min t0 s = t0 /\ max t0 s = s` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `t0 < s` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "L112" (MP_TAC o SPECL [`hs:(A)rfs_history`; `Cp:real`; `eps:real`; `r0:real`;
                                   `z:A`; `t0:real`; `s:real`; `rr:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`s:real`; `z:A`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_LE_REFL] THEN REWRITE_TAC[P2C_VIEW_EXPAND] THEN
    ASM_SIMP_TAC[MFD_CENTRE_IN_BALL];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `Rz <= D` THEN UNDISCH_TAC `&0 <= D` THEN REAL_ARITH_TAC);;

(* ========================================================================= *)
(* In dimension 3 every sectional curvature is at most                     *)
(* R/2 - 2 sec_min (complete a G-orthonormal basis of the plane by the     *)
(* cross product, and use K(P) = R/2 - Ric(n,n) on the frame), so under    *)
(* the Hamilton-Ivey pinching the curvature norm is bounded by the scalar  *)
(* curvature (P3N_PINCH_RM).                                                *)
(* ========================================================================= *)

let P3N_LSEC_UPPER = prove
 (`!U (G:real^3->real^3^3) y u v m0.
     metric_field U G /\ y IN U /\ ~collinear {vec 0,u,v} /\
     (!a b. ~collinear {vec 0,a,b} ==> m0 <= lsectional G y a b)
     ==> lsectional G y u v <= lscalar G y / &2 - &2 * m0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `u:real^3`; `v:real^3`]
                P3S_PLANE_ONB) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `c1:real` (X_CHOOSE_THEN `c2:real` (X_CHOOSE_THEN `c:real`
    STRIP_ASSUME_TAC))) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `G:real^3->real^3^3`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  ABBREV_TAC `u1:real^3 = c1 % u` THEN ABBREV_TAC `v1:real^3 = c2 % (v - c % u)` THEN
  SUBGOAL_THEN `(v1:real^3) dot ((G:real^3->real^3^3) y ** u1) = &0` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `v1:real^3`;
                   `u1:real^3`] LRG_METRIC_SYM) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `z:real^3 = u1 cross v1` THEN
  SUBGOAL_THEN `~(z:real^3 = vec 0)` ASSUME_TAC THENL
   [EXPAND_TAC "z" THEN ASM_REWRITE_TAC[CROSS_EQ_0]; ALL_TAC] THEN
  ABBREV_TAC `w0:real^3 = z - (z dot ((G:real^3->real^3^3) y ** u1)) % u1 -
                              (z dot (G y ** v1)) % v1` THEN
  SUBGOAL_THEN `~(w0:real^3 = vec 0)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `(z:real^3) = (z dot ((G:real^3->real^3^3) y ** u1)) % u1 +
                               (z dot (G y ** v1)) % v1` ASSUME_TAC THENL
     [UNDISCH_TAC `(w0:real^3) = vec 0` THEN EXPAND_TAC "w0" THEN VECTOR_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(z:real^3) dot z = &0` MP_TAC THENL
     [FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THEN
      REWRITE_TAC[DOT_RADD; DOT_RMUL] THEN EXPAND_TAC "z" THEN
      REWRITE_TAC[DOT_CROSS_SELF] THEN REAL_ARITH_TAC;
      ASM_REWRITE_TAC[DOT_EQ_0]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(w0:real^3) dot ((G:real^3->real^3^3) y ** u1) = &0 /\
                w0 dot (G y ** v1) = &0` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "w0" THEN REWRITE_TAC[DOT_LSUB; DOT_LMUL] THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(u1:real^3) dot ((G:real^3->real^3^3) y ** w0) = &0 /\
                (v1:real^3) dot (G y ** w0) = &0` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `u1:real^3`;
                     `w0:real^3`] LRG_METRIC_SYM);
      MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `v1:real^3`;
                     `w0:real^3`] LRG_METRIC_SYM)] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `nw = (w0:real^3) dot ((G:real^3->real^3^3) y ** w0)` THEN
  SUBGOAL_THEN `&0 < nw` ASSUME_TAC THENL
   [EXPAND_TAC "nw" THEN MATCH_MP_TAC LRG_METRIC_POS THEN
    EXISTS_TAC `U:real^3->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `w1:real^3 = inv(sqrt nw) % w0` THEN
  SUBGOAL_THEN `inv(sqrt nw) * inv(sqrt nw) * nw = &1` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_MUL_ASSOC; GSYM REAL_INV_MUL] THEN
    SUBGOAL_THEN `sqrt nw * sqrt nw = nw` SUBST1_TAC THENL
     [ASM_SIMP_TAC[GSYM REAL_POW_2; SQRT_POW_2; REAL_LT_IMP_LE]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_MUL_LINV THEN ASM_SIMP_TAC[REAL_LT_IMP_NZ];
    ALL_TAC] THEN
  SUBGOAL_THEN `w1 dot ((G:real^3->real^3^3) y ** w1) = &1 /\
                u1 dot (G y ** w1) = &0 /\ v1 dot (G y ** w1) = &0 /\
                w1 dot (G y ** u1) = &0 /\ w1 dot (G y ** v1) = &0`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "w1" THEN
    REWRITE_TAC[MATRIX_VECTOR_MUL_RMUL; DOT_RMUL; DOT_LMUL] THEN
    ASM_REWRITE_TAC[REAL_MUL_RZERO];
    ALL_TAC] THEN
  SUBGOAL_THEN `lsectional (G:real^3->real^3^3) y u1 v1 = lpcurv G y (\m. w1) /\
                lsectional G y u1 w1 = lpcurv G y (\m. v1) /\
                lsectional G y v1 w1 = lpcurv G y (\m. u1)` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC RFA_LSECTIONAL_PCURV_3D THEN
    EXISTS_TAC `U:real^3->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `lpcurv (G:real^3->real^3^3) y (\m. u1) + lpcurv G y (\m. v1) +
                lpcurv G y (\m. w1) = lscalar G y / &2` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`(G:real^3->real^3^3) y`; `u1:real^3`; `v1:real^3`; `w1:real^3`]
                  RFA_ORTHO3_MATRIX) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN MATCH_MP_TAC LRG_METRIC_SYM THEN
      EXISTS_TAC `U:real^3->bool` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `S:real^3^3` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `S:real^3^3`]
                  RFA_SCAL_FRAME) THEN
    ASM_REWRITE_TAC[DIMINDEX_3; SUM_3] THEN DISCH_TAC THEN
    REWRITE_TAC[lpcurv; lmetric2; lric2] THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `m0 <= lsectional (G:real^3->real^3^3) y u1 w1 /\
                m0 <= lsectional G y v1 w1` MP_TAC THENL
   [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN MATCH_MP_TAC P3S_ON_NONCOLL THEN
    MAP_EVERY EXISTS_TAC [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN UNDISCH_TAC `lpcurv (G:real^3->real^3^3) y (\m. u1) +
                lpcurv G y (\m. v1) + lpcurv G y (\m. w1) = lscalar G y / &2` THEN
  REAL_ARITH_TAC);;

let P3N_SEC_UPPER = prove
 (`!top atlas (g:A->real^3^3) x u v.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     x IN topspace top /\ ~collinear {vec 0,u,v}
     ==> mfd_sectional atlas g x u v <=
         mfd_scalar atlas g x / &2 - &2 * mfd_sec_min atlas g x`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[mfd_sectional; mfd_scalar] THEN MATCH_MP_TAC P3N_LSEC_UPPER THEN
  EXISTS_TAC `IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)))
                    (FST(chart_at atlas x))` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `riemannian_metric (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3)` THEN
    REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `x:A`; `a:real^3`; `b:real^3`] RFA_SEC_GE_SECMIN) THEN
    ASM_REWRITE_TAC[mfd_sectional]]);;

let P3N_PINCH_RM = prove
 (`!top atlas (g:A->real^3^3) t x.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     x IN topspace top /\ &0 <= t /\ rfs_pinched_at atlas g t x
     ==> mfd_rm_norm atlas g x <= &2 * abs(mfd_scalar atlas g x) + &2 * exp(&4)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC RFA_MFD_RM_NORM_LE THEN
  REWRITE_TAC[DIMINDEX_3; ARITH] THEN MAP_EVERY X_GEN_TAC [`u:real^3`; `v:real^3`] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `x:A`; `u:real^3`; `v:real^3`] RFA_SEC_GE_SECMIN) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `x:A`; `u:real^3`; `v:real^3`] P3N_SEC_UPPER) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `m = mfd_sec_min atlas (g:A->real^3^3) x` THEN
  ABBREV_TAC `R = mfd_scalar atlas (g:A->real^3^3) x` THEN
  ABBREV_TAC `K = mfd_sectional atlas (g:A->real^3^3) x u v` THEN
  SUBGOAL_THEN `--m <= abs R / &2 + exp(&4)` MP_TAC THENL
   [ASM_CASES_TAC `&0 < --m` THENL
     [ALL_TAC; MP_TAC(SPEC `&4` REAL_EXP_POS_LT) THEN ASM_REAL_ARITH_TAC] THEN
    UNDISCH_TAC `rfs_pinched_at atlas (g:A->real^3^3) t x` THEN
    ASM_REWRITE_TAC[rfs_pinched_at] THEN STRIP_TAC THEN
    ASM_CASES_TAC `exp(&4) <= --m` THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    SUBGOAL_THEN `&4 <= log(--m)` ASSUME_TAC THENL
     [GEN_REWRITE_TAC LAND_CONV [GSYM LOG_EXP] THEN MATCH_MP_TAC LOG_MONO_LE_IMP THEN
      ASM_REWRITE_TAC[REAL_EXP_POS_LT];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= log(&1 + t)` ASSUME_TAC THENL
     [MATCH_MP_TAC LOG_POS THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&2 * --m * &1 <= &2 * --m * (log(--m) + log(&1 + t) - &3)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(SPEC `&4` REAL_EXP_POS_LT) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPEC `&4` REAL_EXP_POS_LT) THEN REAL_ARITH_TAC);;
let P3N_FRAME3 = prove
 (`!U (G:real^3->real^3^3) y u v.
     metric_field U G /\ y IN U /\ ~collinear {vec 0,u,v}
     ==> ?u1 v1 w1. lsectional G y u1 v1 = lsectional G y u v /\
                    ~collinear {vec 0,u1,v1} /\ ~collinear {vec 0,u1,w1} /\
                    ~collinear {vec 0,v1,w1} /\
                    lscalar G y = &2 * (lsectional G y u1 v1 + lsectional G y u1 w1 +
                                        lsectional G y v1 w1)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `u:real^3`; `v:real^3`]
                P3S_PLANE_ONB) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `c1:real` (X_CHOOSE_THEN `c2:real` (X_CHOOSE_THEN `c:real`
    STRIP_ASSUME_TAC))) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `G:real^3->real^3^3`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  ABBREV_TAC `u1:real^3 = c1 % u` THEN ABBREV_TAC `v1:real^3 = c2 % (v - c % u)` THEN
  SUBGOAL_THEN `(v1:real^3) dot ((G:real^3->real^3^3) y ** u1) = &0` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `v1:real^3`;
                   `u1:real^3`] LRG_METRIC_SYM) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `z:real^3 = u1 cross v1` THEN
  SUBGOAL_THEN `~(z:real^3 = vec 0)` ASSUME_TAC THENL
   [EXPAND_TAC "z" THEN ASM_REWRITE_TAC[CROSS_EQ_0]; ALL_TAC] THEN
  ABBREV_TAC `w0:real^3 = z - (z dot ((G:real^3->real^3^3) y ** u1)) % u1 -
                              (z dot (G y ** v1)) % v1` THEN
  SUBGOAL_THEN `~(w0:real^3 = vec 0)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `(z:real^3) = (z dot ((G:real^3->real^3^3) y ** u1)) % u1 +
                               (z dot (G y ** v1)) % v1` ASSUME_TAC THENL
     [UNDISCH_TAC `(w0:real^3) = vec 0` THEN EXPAND_TAC "w0" THEN VECTOR_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(z:real^3) dot z = &0` MP_TAC THENL
     [FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THEN
      REWRITE_TAC[DOT_RADD; DOT_RMUL] THEN EXPAND_TAC "z" THEN
      REWRITE_TAC[DOT_CROSS_SELF] THEN REAL_ARITH_TAC;
      ASM_REWRITE_TAC[DOT_EQ_0]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(w0:real^3) dot ((G:real^3->real^3^3) y ** u1) = &0 /\
                w0 dot (G y ** v1) = &0` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "w0" THEN REWRITE_TAC[DOT_LSUB; DOT_LMUL] THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(u1:real^3) dot ((G:real^3->real^3^3) y ** w0) = &0 /\
                (v1:real^3) dot (G y ** w0) = &0` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `u1:real^3`;
                     `w0:real^3`] LRG_METRIC_SYM);
      MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `v1:real^3`;
                     `w0:real^3`] LRG_METRIC_SYM)] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `nw = (w0:real^3) dot ((G:real^3->real^3^3) y ** w0)` THEN
  SUBGOAL_THEN `&0 < nw` ASSUME_TAC THENL
   [EXPAND_TAC "nw" THEN MATCH_MP_TAC LRG_METRIC_POS THEN
    EXISTS_TAC `U:real^3->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `w1:real^3 = inv(sqrt nw) % w0` THEN
  SUBGOAL_THEN `inv(sqrt nw) * inv(sqrt nw) * nw = &1` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_MUL_ASSOC; GSYM REAL_INV_MUL] THEN
    SUBGOAL_THEN `sqrt nw * sqrt nw = nw` SUBST1_TAC THENL
     [ASM_SIMP_TAC[GSYM REAL_POW_2; SQRT_POW_2; REAL_LT_IMP_LE]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_MUL_LINV THEN ASM_SIMP_TAC[REAL_LT_IMP_NZ];
    ALL_TAC] THEN
  SUBGOAL_THEN `w1 dot ((G:real^3->real^3^3) y ** w1) = &1 /\
                u1 dot (G y ** w1) = &0 /\ v1 dot (G y ** w1) = &0 /\
                w1 dot (G y ** u1) = &0 /\ w1 dot (G y ** v1) = &0`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "w1" THEN
    REWRITE_TAC[MATRIX_VECTOR_MUL_RMUL; DOT_RMUL; DOT_LMUL] THEN
    ASM_REWRITE_TAC[REAL_MUL_RZERO];
    ALL_TAC] THEN
  SUBGOAL_THEN `lsectional (G:real^3->real^3^3) y u1 v1 = lpcurv G y (\m. w1) /\
                lsectional G y u1 w1 = lpcurv G y (\m. v1) /\
                lsectional G y v1 w1 = lpcurv G y (\m. u1)` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC RFA_LSECTIONAL_PCURV_3D THEN
    EXISTS_TAC `U:real^3->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `lpcurv (G:real^3->real^3^3) y (\m. u1) + lpcurv G y (\m. v1) +
                lpcurv G y (\m. w1) = lscalar G y / &2` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`(G:real^3->real^3^3) y`; `u1:real^3`; `v1:real^3`; `w1:real^3`]
                  RFA_ORTHO3_MATRIX) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN MATCH_MP_TAC LRG_METRIC_SYM THEN
      EXISTS_TAC `U:real^3->bool` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `S:real^3^3` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `S:real^3^3`]
                  RFA_SCAL_FRAME) THEN
    ASM_REWRITE_TAC[DIMINDEX_3; SUM_3] THEN DISCH_TAC THEN
    REWRITE_TAC[lpcurv; lmetric2; lric2] THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`u1:real^3`; `v1:real^3`; `w1:real^3`] THEN
  REPEAT CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    MATCH_MP_TAC P3S_ON_NONCOLL THEN
    MAP_EVERY EXISTS_TAC [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`] THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC P3S_ON_NONCOLL THEN
    MAP_EVERY EXISTS_TAC [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`] THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC P3S_ON_NONCOLL THEN
    MAP_EVERY EXISTS_TAC [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`] THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[ASSUME `lsectional (G:real^3->real^3^3) y u1 v1 = lpcurv G y (\m. w1)`;
                ASSUME `lsectional (G:real^3->real^3^3) y u1 w1 = lpcurv G y (\m. v1)`;
                ASSUME `lsectional (G:real^3->real^3^3) y v1 w1 = lpcurv G y (\m. u1)`] THEN
    UNDISCH_TAC `lpcurv (G:real^3->real^3^3) y (\m. u1) + lpcurv G y (\m. v1) +
                 lpcurv G y (\m. w1) = lscalar G y / &2` THEN
    REAL_ARITH_TAC]);;

let P3N_SCALAR_LE_RM = prove
 (`!top atlas (g:A->real^3^3) x.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\ x IN topspace top
     ==> abs(mfd_scalar atlas g x) <= &6 * mfd_rm_norm atlas g x`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)))
                        (FST(chart_at atlas x))`;
                 `metric_local atlas (chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A))
                    (g:A->real^3^3)`;
                 `SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)) x`;
                 `basis 1:real^3`; `basis 2:real^3`] P3N_FRAME3) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `riemannian_metric (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3)` THEN
      REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC APX_ORTHO_NOT_COLLINEAR THEN
      SIMP_TAC[NORM_BASIS; DOT_BASIS_BASIS; DIMINDEX_3; ARITH]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `u1:real^3` (X_CHOOSE_THEN `v1:real^3` (X_CHOOSE_THEN `w1:real^3`
    STRIP_ASSUME_TAC))) THEN
  REWRITE_TAC[mfd_scalar] THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `x:A`] MFD_SECTIONAL_LE_RM_NORM) THEN
  ASM_REWRITE_TAC[mfd_sectional] THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o SPECL [`u1:real^3`; `v1:real^3`]) THEN
  FIRST_ASSUM(MP_TAC o SPECL [`u1:real^3`; `w1:real^3`]) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`v1:real^3`; `w1:real^3`]) THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* ========================================================================= *)
(* Hamilton's lemma uniformly over families of local Ricci                  *)
(* flows from a common base time 0 up to VARIABLE end times en n <= Bd      *)
(* (P3N_HAM_VAR): the instance of P2CH_LOCAL on the windows t + n L,        *)
(* 0 <= t < en n, each point joined to its base n L by a segment on which   *)
(* the flow has a smooth extension (below 0 from the given extension FF,    *)
(* above t because t < en n).                                                *)
(* ========================================================================= *)

let P3N_HAM_VAR = prove
 (`!V K (Gs:num->real->real^N->real^N^N) (en:num->real) Bd Lm.
     open V /\ compact K /\ K SUBSET V /\ &0 <= Lm /\
     (!n. &0 < en n /\ en n <= Bd) /\
     (!n. lricci_flow V (&0) (en n) (Gs n)) /\
     (!n t. &0 <= t /\ t < en n ==> metric_field V (Gs n t)) /\
     (!n. ?e (FF:real^(1,N)finite_sum->real^(N,N)finite_prod).
            &0 < e /\ smooth_map_on (interval(lift(--e),lift(en n)) PCROSS V) FF /\
            (!t y. &0 <= t /\ t < en n /\ y IN V
                   ==> FF(pastecart (lift t) y) = vectorize(Gs n t y))) /\
     (!n t y p q. &0 <= t /\ t < en n /\ y IN K /\ 1 <= p /\ p <= dimindex(:N) /\
                  1 <= q /\ q <= dimindex(:N) ==> abs(Gs n t y$p$q) <= Lm) /\
     (!n t y v. &0 <= t /\ t < en n /\ y IN K
                ==> norm v pow 2 <= Lm * (v dot (Gs n t y ** v))) /\
     (!j. ?C. !n t y. &0 <= t /\ t < en n /\ y IN K ==> lrm_deriv_norm2 j (Gs n t) y <= C) /\
     (!m p q. 1 <= p /\ p <= dimindex(:N) /\ 1 <= q /\ q <= dimindex(:N)
              ==> ?B. !n l y. l IN pde_index_lists m (:N) /\ y IN K
                              ==> abs(drop(iterated_partial l (\z. lift(Gs n (&0) z$p$q)) y))
                                  <= B)
     ==> !m p q. 1 <= p /\ p <= dimindex(:N) /\ 1 <= q /\ q <= dimindex(:N)
                 ==> ?B. !n t l y. &0 <= t /\ t < en n /\ l IN pde_index_lists m (:N) /\
                                   y IN K
                                   ==> abs(drop(iterated_partial l
                                                 (\z. lift(Gs n t z$p$q)) y)) <= B`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "en") (CONJUNCTS_THEN2 (LABEL_TAC "lf")
    (CONJUNCTS_THEN2 (LABEL_TAC "mf") (CONJUNCTS_THEN2 (LABEL_TAC "ext")
    (CONJUNCTS_THEN2 (LABEL_TAC "ent") (CONJUNCTS_THEN2 (LABEL_TAC "eqv")
    (CONJUNCTS_THEN2 (LABEL_TAC "rmd") (LABEL_TAC "ini")))))))))))) THEN
  SUBGOAL_THEN `&0 <= Bd` ASSUME_TAC THENL
   [USE_THEN "en" (MP_TAC o SPEC `0`) THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `L = &2 * (Bd + &1)` THEN
  SUBGOAL_THEN `&0 < L /\ !n t. &0 <= t /\ t < (en:num->real) n ==> abs t < L / &2 /\ abs t <= Bd`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "L" THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN USE_THEN "en" (MP_TAC o SPEC `n:num`) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `Gc = p2ch_win (Gs:num->real->real^N->real^N^N) L` THEN
  SUBGOAL_THEN `!n t. &0 <= t /\ t < (en:num->real) n
                      ==> (Gc:real->real^N->real^N^N) (t + &n * L) = Gs n t`
  (LABEL_TAC "win") THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "Gc" THEN MATCH_MP_TAC P2CH_WIN THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!n b. &0 < b /\ b <= (en:num->real) n
                      ==> lricci_flow V (&n * L) (b + &n * L) (Gc:real->real^N->real^N^N)`
  (LABEL_TAC "lfc") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC RFA_LRICCI_FLOW_EQ THEN
    EXISTS_TAC `\s. (Gs:num->real->real^N->real^N^N) n (s - &n * L)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC P2CA_LRICCI_FLOW_SUBINTERVAL THEN
      MAP_EVERY EXISTS_TAC [`&0 + &n * L`; `(en:num->real) n + &n * L`] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC P2CH_LRICCI_FLOW_SHIFT THEN USE_THEN "lf" (fun th ->
          REWRITE_TAC[ETA_AX; SPEC `n:num` th]);
        ASM_REAL_ARITH_TAC];
      MAP_EVERY X_GEN_TAC [`s:real`; `y:real^N`] THEN STRIP_TAC THEN REWRITE_TAC[] THEN
      USE_THEN "win" (MP_TAC o SPECL [`n:num`; `s - &n * L`]) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[REAL_SUB_ADD] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`{t + &n * L | n,t | &0 <= t /\ t < (en:num->real) n}`; `{&n * L | n IN (:num)}`;
    `{t + &n * L | n,t | &0 < t /\ t < (en:num->real) n}`; `V:real^N->bool`; `K:real^N->bool`;
    `Gc:real->real^N->real^N^N`; `Lm:real`; `Bd:real`] P2CH_LOCAL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_GSPEC; IN_UNIV; IN_ELIM_THM] THEN
      X_GEN_TAC `n:num` THEN MAP_EVERY EXISTS_TAC [`n:num`; `&0`] THEN
      REWRITE_TAC[REAL_ADD_LID; REAL_LE_REFL] THEN USE_THEN "en" (fun th ->
        REWRITE_TAC[SPEC `n:num` th]);
      REWRITE_TAC[SUBSET; FORALL_IN_GSPEC; IN_ELIM_THM] THEN
      MAP_EVERY X_GEN_TAC [`n:num`; `t:real`] THEN STRIP_TAC THEN
      MAP_EVERY EXISTS_TAC [`n:num`; `t:real`] THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC;
      REWRITE_TAC[FORALL_IN_GSPEC] THEN
      MAP_EVERY X_GEN_TAC [`n:num`; `t:real`] THEN STRIP_TAC THEN ASM_SIMP_TAC[];
      REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_GSPEC] THEN
      MAP_EVERY X_GEN_TAC [`n:num`; `t:real`] THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC[];
      REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_GSPEC] THEN
      MAP_EVERY X_GEN_TAC [`n:num`; `t:real`] THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC[];
      X_GEN_TAC `j:num` THEN
      USE_THEN "rmd" (X_CHOOSE_TAC `C:real` o SPEC `j:num`) THEN
      EXISTS_TAC `C:real` THEN
      REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_GSPEC] THEN
      MAP_EVERY X_GEN_TAC [`n:num`; `t:real`] THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC[];
      REWRITE_TAC[FORALL_IN_GSPEC] THEN
      MAP_EVERY X_GEN_TAC [`n:num`; `t:real`] THEN STRIP_TAC THEN
      USE_THEN "ext" (X_CHOOSE_THEN `e:real` (X_CHOOSE_THEN
        `FF:real^(1,N)finite_sum->real^(N,N)finite_prod` STRIP_ASSUME_TAC) o SPEC `n:num`) THEN
      ABBREV_TAC `d = ((en:num->real) n - t) / &2` THEN
      SUBGOAL_THEN `&0 < d /\ t + d < (en:num->real) n /\ t + &2 * d = en n` STRIP_ASSUME_TAC THENL
       [EXPAND_TAC "d" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MAP_EVERY EXISTS_TAC
       [`&n * L`; `&n * L`; `(t + d) + &n * L`; `min e d`;
        `\w:real^(1,N)finite_sum. (FF:real^(1,N)finite_sum->real^(N,N)finite_prod)
                                  (pastecart (lift(&1 * drop(fstcart w) + --(&n * L)))
                                             (sndcart w))`] THEN
      REPEAT CONJ_TAC THENL
       [REWRITE_TAC[IN_ELIM_THM; IN_UNIV] THEN EXISTS_TAC `n:num` THEN REWRITE_TAC[];
        REWRITE_TAC[REAL_ARITH `(t + n) - n:real = t`] THEN ASM_MESON_TAC[];
        ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC;
        USE_THEN "lfc" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
        X_GEN_TAC `s:real` THEN STRIP_TAC THEN
        USE_THEN "win" (MP_TAC o SPECL [`n:num`; `s - &n * L`]) THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        REWRITE_TAC[REAL_SUB_ADD] THEN DISCH_THEN SUBST1_TAC THEN
        USE_THEN "mf" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
        MP_TAC(ISPECL [`FF:real^(1,N)finite_sum->real^(N,N)finite_prod`; `V:real^N->bool`;
                       `--e:real`; `(en:num->real) n`;
                       `&n * L - min e d`; `((t + d) + &n * L) + min e d`; `&1`;
                       `--(&n * L):real`] RFB_SMOOTH_TIME_AFFINE) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]];
        MAP_EVERY X_GEN_TAC [`s:real`; `y:real^N`] THEN STRIP_TAC THEN
        REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
        REWRITE_TAC[REAL_MUL_LID; GSYM real_sub] THEN
        USE_THEN "win" (MP_TAC o SPECL [`n:num`; `s - &n * L`]) THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        REWRITE_TAC[REAL_SUB_ADD] THEN DISCH_THEN SUBST1_TAC THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
        X_GEN_TAC `s:real` THEN STRIP_TAC THEN REWRITE_TAC[IN_ELIM_THM] THEN
        MAP_EVERY EXISTS_TAC [`n:num`; `s - &n * L`] THEN
        REWRITE_TAC[REAL_SUB_ADD] THEN ASM_REAL_ARITH_TAC];
      REWRITE_TAC[FORALL_IN_GSPEC] THEN
      MAP_EVERY X_GEN_TAC [`n:num`; `t:real`] THEN STRIP_TAC THEN
      MAP_EVERY EXISTS_TAC [`&n * L`; `(en:num->real) n + &n * L`] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      USE_THEN "lfc" MATCH_MP_TAC THEN USE_THEN "en" (MP_TAC o SPEC `n:num`) THEN
      REAL_ARITH_TAC;
      MAP_EVERY X_GEN_TAC [`m:num`; `p:num`; `q:num`] THEN STRIP_TAC THEN
      REWRITE_TAC[rfa_jb; IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_GSPEC; IN_UNIV] THEN
      SUBGOAL_THEN `!n. (Gc:real->real^N->real^N^N) (&n * L) = Gs n (&0)` ASSUME_TAC THENL
       [GEN_TAC THEN USE_THEN "win" (MP_TAC o SPECL [`n:num`; `&0`]) THEN
        ANTS_TAC THENL
         [REWRITE_TAC[REAL_LE_REFL] THEN USE_THEN "en" (fun th -> REWRITE_TAC[SPEC `n:num` th]);
          REWRITE_TAC[REAL_ADD_LID]];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [GEN_TAC THEN MATCH_MP_TAC PDE_SMOOTH_G_ENTRY THEN REWRITE_TAC[ETA_AX] THEN
        USE_THEN "mf" MATCH_MP_TAC THEN REWRITE_TAC[REAL_LE_REFL] THEN
        USE_THEN "en" (fun th -> REWRITE_TAC[SPEC `n:num` th]);
        USE_THEN "ini" (MP_TAC o SPECL [`m:num`; `p:num`; `q:num`]) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        MATCH_MP_TAC MONO_EXISTS THEN MESON_TAC[]]];
    ALL_TAC] THEN
  DISCH_THEN(fun th -> MAP_EVERY X_GEN_TAC [`m:num`; `p:num`; `q:num`] THEN STRIP_TAC THEN
    MP_TAC(SPECL [`m:num`; `p:num`; `q:num`] th)) THEN
  ASM_REWRITE_TAC[rfa_jb; IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_GSPEC] THEN
  DISCH_THEN(K ALL_TAC) THEN DISCH_THEN(X_CHOOSE_TAC `B:real`) THEN EXISTS_TAC `B:real` THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `t:real`] THEN REPEAT DISCH_TAC THEN
  X_GEN_TAC `l:num list` THEN DISCH_TAC THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
  USE_THEN "win" (MP_TAC o SPECL [`n:num`; `t:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `t:real`]) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> ASM_SIMP_TAC[th]));;

