(* ========================================================================= *)
(* Unit pc_p2a_wkdec: decomposition of a smooth positive definite matrix     *)
(* field A into rank-one pieces W_k d_k d_k^T with fixed directions d_k and  *)
(* smooth nonnegative weights near a compact set (the input format of the    *)
(* barrier principle P2AW_NBP of pc_p2a_wk5), and the identities that turn   *)
(* the directional sums back into the divergence form of A.  Locally:        *)
(* polarization in an eigenbasis of A at a centre; globally: a smooth        *)
(* partition of unity.  Headline P2AW_NBP_MATRIX: the barrier principle in   *)
(* divergence form on an open set s where A is smooth, symmetric and         *)
(* positive definite.                                                        *)
(*                                                                           *)
(* First: Kronecker sums and the polarization identity in the standard       *)
(* basis.                                                                    *)
(* ========================================================================= *)

needs "src/pc_p2a_wk5.ml";;

prioritize_real();;
type_invention_error := true;;

let p2aw_wp = new_definition
 `p2aw_wp (B:real^N^N) (c0:real) (i:num) (j:num) =
    if i = j then (B$i$i - (&(dimindex(:N)) - &1) * c0) / &4 else (c0 + B$i$j) / &4`;;

let p2aw_wm = new_definition
 `p2aw_wm (B:real^N^N) (c0:real) (i:num) (j:num) =
    if i = j then &0 else (c0 - B$i$j) / &4`;;

let P2AW_SUM_KRON = prove
 (`!(f:num->real) a n.
     1 <= a /\ a <= n ==> sum(1..n) (\i. (if a = i then &1 else &0) * f i) = f a`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\i. (if a = i then &1 else &0) * (f:num->real) i) =
                (\i. if i = a then f a else &0)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
    ASM_CASES_TAC `a:num = x` THEN ASM_REWRITE_TAC[REAL_MUL_LID; REAL_MUL_LZERO] THEN
    ASM_MESON_TAC[];
    ASM_REWRITE_TAC[SUM_DELTA; IN_NUMSEG]]);;

let P2AW_SUM_COND_CONST = prove
 (`!a n X Y. 1 <= a /\ a <= n
             ==> sum(1..n) (\j. if a = j then X else Y) = X + (&n - &1) * Y`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\j. if (a:num) = j then (X:real) else Y) =
                (\j. Y + (if a = j then &1 else &0) * (X - Y))` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN COND_CASES_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[SUM_ADD_NUMSEG; SUM_CONST_NUMSEG] THEN
  ASM_SIMP_TAC[P2AW_SUM_KRON] THEN
  ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB; ARITH_RULE `1 <= a /\ a <= n ==> 1 <= n + 1`;
               ARITH_RULE `(n + 1) - 1 = n`] THEN
  SUBGOAL_THEN `1 <= n` MP_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SIMP_TAC[GSYM REAL_OF_NUM_LE; GSYM REAL_OF_NUM_ADD] THEN REAL_ARITH_TAC);;

let P2AW_POLAR_STD = prove
 (`!(B:real^N^N) c0 a c.
     (!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N) ==> B$i$j = B$j$i) /\
     1 <= a /\ a <= dimindex(:N) /\ 1 <= c /\ c <= dimindex(:N)
     ==> sum(1..dimindex(:N))
           (\i. sum(1..dimindex(:N))
             (\j. p2aw_wp B c0 i j * (basis i + basis j:real^N)$a *
                  (basis i + basis j:real^N)$c +
                  p2aw_wm B c0 i j * (basis i - basis j:real^N)$a *
                  (basis i - basis j:real^N)$c)) =
         B$a$c`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[VECTOR_ADD_COMPONENT; VECTOR_SUB_COMPONENT; BASIS_COMPONENT] THEN
  ABBREV_TAC `n = dimindex(:N)` THEN
  SUBGOAL_THEN
   `!i j. p2aw_wp (B:real^N^N) c0 i j *
          ((if a = i then &1 else &0) + (if a = j then &1 else &0)) *
          ((if c = i then &1 else &0) + (if c = j then &1 else &0)) +
          p2aw_wm B c0 i j *
          ((if a = i then &1 else &0) - (if a = j then &1 else &0)) *
          ((if c = i then &1 else &0) - (if c = j then &1 else &0)) =
          (if a = i then &1 else &0) *
          ((if c = i then &1 else &0) * (p2aw_wp B c0 i j + p2aw_wm B c0 i j)) +
          (if a = j then &1 else &0) *
          ((if c = j then &1 else &0) * (p2aw_wp B c0 i j + p2aw_wm B c0 i j)) +
          (if a = i then &1 else &0) *
          ((if c = j then &1 else &0) * (p2aw_wp B c0 i j - p2aw_wm B c0 i j)) +
          (if c = i then &1 else &0) *
          ((if a = j then &1 else &0) * (p2aw_wp B c0 i j - p2aw_wm B c0 i j))`
  (fun th -> REWRITE_TAC[th]) THENL
   [REPEAT GEN_TAC THEN
    MAP_EVERY ASM_CASES_TAC [`a:num = i`; `a:num = j`; `c:num = i`; `c:num = j`] THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[SUM_ADD_NUMSEG; SUM_LMUL] THEN ASM_SIMP_TAC[P2AW_SUM_KRON] THEN
  REWRITE_TAC[SUM_LMUL] THEN ASM_SIMP_TAC[P2AW_SUM_KRON] THEN
  REWRITE_TAC[p2aw_wp; p2aw_wm] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `sum(1..n) (\j. if a = j then ((B:real^N^N)$a$a - (&n - &1) * c0) / &4
                   else (c0 + B$a$j) / &4) +
    sum(1..n) (\j. if a = j then &0 else (c0 - B$a$j) / &4) =
    (B$a$a - (&n - &1) * c0) / &4 + (&n - &1) * (c0 / &2) /\
    sum(1..n) (\i. (if i = a then ((B:real^N^N)$i$i - (&n - &1) * c0) / &4
                    else (c0 + B$i$a) / &4) +
                   (if i = a then &0 else (c0 - B$i$a) / &4)) =
    (B$a$a - (&n - &1) * c0) / &4 + (&n - &1) * (c0 / &2)`
  (fun th -> REWRITE_TAC[th]) THENL
   [CONJ_TAC THENL [REWRITE_TAC[GSYM SUM_ADD_NUMSEG]; ALL_TAC] THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `sum(1..n) (\j. if a = j then ((B:real^N^N)$a$a - (&n - &1) * c0) / &4
                               else c0 / &2)` THEN
    (CONJ_TAC THENL
      [MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN BETA_TAC THEN
       ASM_CASES_TAC `a:num = j` THEN ASM_REWRITE_TAC[] THEN TRY REAL_ARITH_TAC THEN
       ASM_MESON_TAC[];
       ASM_SIMP_TAC[P2AW_SUM_COND_CONST]]);
    ALL_TAC] THEN
  ASM_CASES_TAC `a:num = c` THENL
   [FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN REWRITE_TAC[] THEN REAL_ARITH_TAC;
    SUBGOAL_THEN `~(c:num = a)` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(B:real^N^N)$c$a = B$a$c` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th))) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]);;

let P2AW_SUM_SWAP4 = prove
 (`!(G:num->num->num->num->real) n.
     sum(1..n) (\i. sum(1..n) (\j. sum(1..n) (\k. sum(1..n) (\l. G i j k l)))) =
     sum(1..n) (\k. sum(1..n) (\l. sum(1..n) (\i. sum(1..n) (\j. G i j k l))))`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o ABS_CONV) [SUM_SWAP_NUMSEG] THEN BETA_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [SUM_SWAP_NUMSEG] THEN BETA_TAC THEN
  AP_TERM_TAC THEN ABS_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o ABS_CONV) [SUM_SWAP_NUMSEG] THEN BETA_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [SUM_SWAP_NUMSEG] THEN BETA_TAC THEN REFL_TAC);;

(* The polarization in the frame of an orthogonal matrix P: with            *)
(* B = P^T A P, A = sum_ij wp_ij (P(e_i + e_j))(P(e_i + e_j))^T +            *)
(* wm_ij (P(e_i - e_j))(P(e_i - e_j))^T, componentwise.                      *)

let P2AW_POLAR_ROT = prove
 (`!(A:real^N^N) (P:real^N^N) c0 a c.
     symmetric_matrix A /\ orthogonal_matrix P /\
     1 <= a /\ a <= dimindex(:N) /\ 1 <= c /\ c <= dimindex(:N)
     ==> sum(1..dimindex(:N))
           (\i. sum(1..dimindex(:N))
             (\j. p2aw_wp (transp P ** A ** P) c0 i j *
                  (P ** (basis i + basis j))$a * (P ** (basis i + basis j))$c +
                  p2aw_wm (transp P ** A ** P) c0 i j *
                  (P ** (basis i - basis j))$a * (P ** (basis i - basis j))$c)) =
         A$a$c`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `B = transp (P:real^N^N) ** (A:real^N^N) ** P` THEN
  SUBGOAL_THEN `!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
                      ==> (B:real^N^N)$i$j = B$j$i`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `transp(B:real^N^N) = B` MP_TAC THENL
     [EXPAND_TAC "B" THEN REWRITE_TAC[MATRIX_TRANSP_MUL; TRANSP_TRANSP] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[symmetric_matrix]) THEN
      REWRITE_TAC[MATRIX_MUL_ASSOC; ASSUME `transp(A:real^N^N) = A`];
      DISCH_THEN(fun th -> REPEAT STRIP_TAC THEN
        GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [GSYM th] THEN
        REWRITE_TAC[TRANSP_COMPONENT])];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(A:real^N^N)$a$c =
    sum(1..dimindex(:N)) (\k. sum(1..dimindex(:N))
      (\l. ((P:real^N^N)$a$k * P$c$l) * (B:real^N^N)$k$l))`
  SUBST1_TAC THENL
   [SUBGOAL_THEN `(A:real^N^N) = (P:real^N^N) ** (B:real^N^N) ** transp P` SUBST1_TAC THENL
     [EXPAND_TAC "B" THEN RULE_ASSUM_TAC(REWRITE_RULE[orthogonal_matrix]) THEN
      FIRST_X_ASSUM(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC o check (fun th ->
        is_conj(concl th))) THEN
      REWRITE_TAC[MATRIX_MUL_ASSOC; ASSUME `(P:real^N^N) ** transp P = mat 1`;
                  MATRIX_MUL_LID] THEN
      REWRITE_TAC[GSYM MATRIX_MUL_ASSOC; ASSUME `(P:real^N^N) ** transp P = mat 1`;
                  MATRIX_MUL_RID];
      ALL_TAC] THEN
    ASM_SIMP_TAC[matrix_mul; LAMBDA_BETA; TRANSP_COMPONENT] THEN
    REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
    REPEAT STRIP_TAC THEN BETA_TAC THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
    REPEAT STRIP_TAC THEN BETA_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!v:real^N. (P ** v)$a * (P ** v)$c =
               sum(1..dimindex(:N)) (\k. sum(1..dimindex(:N))
                 (\l. ((P:real^N^N)$a$k * P$c$l) * (v$k * v$l)))`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN ASM_SIMP_TAC[MATRIX_VECTOR_MUL_COMPONENT; dot] THEN
    SIMP_TAC[REAL_MUL_SUM; FINITE_NUMSEG] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN BETA_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM SUM_LMUL; GSYM SUM_ADD_NUMSEG] THEN
  GEN_REWRITE_TAC LAND_CONV [P2AW_SUM_SWAP4] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `l:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MP_TAC(ISPECL [`B:real^N^N`; `c0:real`; `k:num`; `l:num`] P2AW_POLAR_STD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
  REPEAT STRIP_TAC THEN BETA_TAC THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
  REPEAT STRIP_TAC THEN BETA_TAC THEN REAL_ARITH_TAC);;

(* ========================================================================= *)
(* The local decomposition.  Near a point c where the matrix field A is      *)
(* continuous, symmetric and positive definite, the weights p2aw_wp, p2aw_wm *)
(* of B(x) = P^T A(x) P (P an orthogonal eigenframe of A(c), c0 = min        *)
(* eigenvalue / (2n)) are nonnegative.                                       *)
(* ========================================================================= *)

let P2AW_DIAG_ENTRY = prove
 (`!(X:real^N^N) i. 1 <= i /\ i <= dimindex(:N) ==> X$i$i = basis i dot (X ** basis i)`,
  SIMP_TAC[DOT_BASIS; MATRIX_VECTOR_MUL_BASIS; column; LAMBDA_BETA]);;

let P2AW_ROT_DIAG_POS = prove
 (`!(A:real^N^N) P i.
     orthogonal_matrix P /\ (!v. ~(v = vec 0) ==> &0 < v dot (A ** v)) /\
     1 <= i /\ i <= dimindex(:N)
     ==> &0 < (transp P ** A ** P)$i$i`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[P2AW_DIAG_ENTRY] THEN
  REWRITE_TAC[GSYM MATRIX_VECTOR_MUL_ASSOC] THEN
  MP_TAC(ISPECL [`transp(P:real^N^N)`; `basis i:real^N`; `(A:real^N^N) ** (P:real^N^N) ** basis i`]
                DOT_LMUL_MATRIX) THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[VECTOR_MATRIX_MUL_TRANSP; TRANSP_TRANSP] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPEC `i:num` BASIS_NONZERO) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `basis i:real^N = transp (P:real^N^N) ** P ** basis i` SUBST1_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[orthogonal_matrix]) THEN
    ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_ASSOC; MATRIX_VECTOR_MUL_LID];
    ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_RZERO]]);;

let P2AW_FINITE_POS_LB = prove
 (`!(f:num->real) n. (!i. 1 <= i /\ i <= n ==> &0 < f i)
                     ==> ?m. &0 < m /\ !i. 1 <= i /\ i <= n ==> m <= f i`,
  GEN_TAC THEN INDUCT_TAC THENL
   [DISCH_TAC THEN EXISTS_TAC `&1` THEN REWRITE_TAC[REAL_LT_01] THEN ARITH_TAC;
    DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[ARITH_RULE `i <= n ==> i <= SUC n`]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `m:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `min m ((f:num->real)(SUC n))` THEN
    SUBGOAL_THEN `&0 < (f:num->real)(SUC n)` ASSUME_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[REAL_LT_MIN] THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    ASM_CASES_TAC `i = SUC n` THENL
     [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC(REAL_ARITH `m <= x ==> min m y <= x`) THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]]);;

let P2AW_FINITE_NBHD = prove
 (`!(Q:K->real^M->bool) Ix c.
     FINITE Ix /\ (!k. k IN Ix ==> ?r. &0 < r /\ !x. dist(x,c) < r ==> Q k x)
     ==> ?r. &0 < r /\ !k x. k IN Ix /\ dist(x,c) < r ==> Q k x`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  SPEC_TAC(`Ix:K->bool`,`Ix:K->bool`) THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  CONJ_TAC THENL [MESON_TAC[NOT_IN_EMPTY; REAL_LT_01]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`a:K`; `t:K->bool`] THEN STRIP_TAC THEN
  REWRITE_TAC[IN_INSERT] THEN DISCH_THEN(LABEL_TAC "H") THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r1:real` STRIP_ASSUME_TAC) THEN
  USE_THEN "H" (MP_TAC o SPEC `a:K`) THEN REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r2:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `min r1 r2` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  ASM_MESON_TAC[REAL_LT_MIN]);;

let P2AW_ROT_ENTRY_CONT = prove
 (`!(A:real^M->real^N^N) (P:real^N^N) c i j.
     (!k l. 1 <= k /\ k <= dimindex(:N) /\ 1 <= l /\ l <= dimindex(:N)
            ==> (\x. lift(A x$k$l)) continuous at c) /\
     1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
     ==> (\x. lift((transp P ** A x ** P)$i$j)) continuous at c`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[matrix_mul; LAMBDA_BETA; TRANSP_COMPONENT] THEN
  REWRITE_TAC[LIFT_SUM; o_DEF] THEN MATCH_MP_TAC CONTINUOUS_VSUM THEN
  REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
  BETA_TAC THEN ASM_SIMP_TAC[LAMBDA_BETA] THEN
  REWRITE_TAC[LIFT_CMUL] THEN MATCH_MP_TAC CONTINUOUS_CMUL THEN
  REWRITE_TAC[LIFT_SUM; o_DEF] THEN MATCH_MP_TAC CONTINUOUS_VSUM THEN
  REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN X_GEN_TAC `l:num` THEN STRIP_TAC THEN
  BETA_TAC THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[LIFT_CMUL] THEN
  MATCH_MP_TAC CONTINUOUS_CMUL THEN ASM_SIMP_TAC[]);;

let P2AW_LOCAL_DECOMP = prove
 (`!(A:real^M->real^N^N) c.
     (!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
            ==> (\x. lift(A x$i$j)) continuous at c) /\
     symmetric_matrix(A c) /\ (!v. ~(v = vec 0) ==> &0 < v dot (A c ** v))
     ==> ?P c0 r. orthogonal_matrix P /\ &0 < c0 /\ &0 < r /\
                  !x i j. dist(x,c) < r /\ 1 <= i /\ i <= dimindex(:N) /\
                          1 <= j /\ j <= dimindex(:N)
                          ==> &0 <= p2aw_wp (transp P ** A x ** P) c0 i j /\
                              &0 <= p2aw_wm (transp P ** A x ** P) c0 i j`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP SYMMETRIC_MATRIX_DIAGONALIZABLE_EXPLICIT) THEN
  DISCH_THEN(X_CHOOSE_THEN `P:real^N^N` (X_CHOOSE_THEN `d:num->real` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN
   `!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
          ==> (transp (P:real^N^N) ** (A:real^M->real^N^N) c ** P)$i$j = if i = j then (d:num->real) i else &0`
  ASSUME_TAC THENL [ASM_SIMP_TAC[LAMBDA_BETA]; ALL_TAC] THEN
  SUBGOAL_THEN `!i. 1 <= i /\ i <= dimindex(:N) ==> &0 < (d:num->real) i` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL [`i:num`; `i:num`] o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `d:num->real`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC P2AW_ROT_DIAG_POS THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`d:num->real`; `dimindex(:N)`] P2AW_FINITE_POS_LB) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `m:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `&1 <= &(dimindex(:N))` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LE; DIMINDEX_GE_1]; ALL_TAC] THEN
  ABBREV_TAC `c0 = m / (&2 * &(dimindex(:N)))` THEN
  SUBGOAL_THEN `&0 < c0 /\ &2 * &(dimindex(:N)) * c0 = m` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "c0" THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
      UNDISCH_TAC `&1 <= &(dimindex(:N))` THEN CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\(p:num#num) (x:real^M). abs((transp (P:real^N^N) ** (A:real^M->real^N^N) x ** P)$(FST p)$(SND p) -
                                 (transp P ** A c ** P)$(FST p)$(SND p)) < c0 / &2`;
    `(1..dimindex(:N)) CROSS (1..dimindex(:N))`; `c:real^M`] P2AW_FINITE_NBHD) THEN
  SIMP_TAC[FINITE_CROSS; FINITE_NUMSEG; FORALL_PAIR_THM; IN_CROSS; IN_NUMSEG] THEN
  ANTS_TAC THENL
   [MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`A:real^M->real^N^N`; `P:real^N^N`; `c:real^M`; `i:num`; `j:num`]
                  P2AW_ROT_ENTRY_CONT) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN REWRITE_TAC[continuous_at] THEN
    DISCH_THEN(MP_TAC o SPEC `c0 / &2`) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
    REWRITE_TAC[DIST_LIFT] THEN MESON_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`P:real^N^N`; `c0:real`; `r:real`] THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`x:real^M`; `i:num`; `j:num`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`i:num`; `j:num`; `x:real^M`]) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`i:num`; `j:num`] o check (fun th ->
    is_forall(concl th) && can (find_term ((=) `d:num->real`)) (concl th) &&
    length(fst(strip_forall(concl th))) = 2)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[p2aw_wp; p2aw_wm] THEN
  ASM_CASES_TAC `i:num = j` THEN ASM_REWRITE_TAC[] THENL
   [FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `m:real`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `&2 * &(dimindex(:N)) * c0 = m` THEN UNDISCH_TAC `&0 < c0` THEN
    UNDISCH_TAC `&0 < m` THEN REAL_ARITH_TAC;
    REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* A smooth partition of unity on a compact set kp covered by finitely many  *)
(* half balls: theta_j are tests on the full balls, >= 0, and sum_j theta_j  *)
(* = 1 on kp (theta_j = chi_j / S with smooth Urysohn bumps chi_j and S = (1 *)
(* - psi) + sum_j chi_j >= 1, psi = 1 on kp).                                *)
(* ========================================================================= *)

let P2AW_SMOOTH_PARTITION = prove
 (`!(kp:real^M->bool) (cs:num->real^M) (rs:num->real) J.
     compact kp /\ (!j. 1 <= j /\ j <= J ==> &0 < rs j) /\
     kp SUBSET UNIONS (IMAGE (\j. ball(cs j, rs j / &2)) (1..J))
     ==> ?theta. (!j. 1 <= j /\ j <= J
                      ==> wan_test (ball(cs j, rs j)) (theta j) /\ (!x. &0 <= theta j x)) /\
                 (!x. x IN kp ==> sum(1..J) (\j. theta j x) = &1)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `?chi:num->real^M->real.
      !j. 1 <= j /\ j <= J
          ==> wan_test (ball(cs j, rs j)) (chi j) /\ (!x. &0 <= chi j x /\ chi j x <= &1) /\
              (!x. x IN cball(cs j, rs j / &2) ==> chi j x = &1)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM SKOLEM_THM; GSYM RIGHT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `j:num` THEN STRIP_TAC THEN MATCH_MP_TAC WAN_SMOOTH_URYSOHN THEN
    REWRITE_TAC[OPEN_BALL; COMPACT_CBALL; SUBSET; IN_CBALL; IN_BALL] THEN
    SUBGOAL_THEN `&0 < (rs:num->real) j` MP_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `U = UNIONS (IMAGE (\j. ball((cs:num->real^M) j, rs j / &2)) (1..J))` THEN
  SUBGOAL_THEN `open(U:real^M->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "U" THEN MATCH_MP_TAC OPEN_UNIONS THEN
    REWRITE_TAC[FORALL_IN_IMAGE; OPEN_BALL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^M->bool`; `kp:real^M->bool`] WAN_SMOOTH_URYSOHN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `psi:real^M->real` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [wan_test]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `kpsi:real^M->bool` STRIP_ASSUME_TAC)) THEN
  ABBREV_TAC `S = \x:real^M. (&1 - psi x) + sum(1..J) (\j. (chi:num->real^M->real) j x)` THEN
  SUBGOAL_THEN `!x:real^M. &1 <= S x` ASSUME_TAC THENL
   [X_GEN_TAC `x:real^M` THEN EXPAND_TAC "S" THEN BETA_TAC THEN
    SUBGOAL_THEN `&0 <= sum(1..J) (\j. (chi:num->real^M->real) j x)` ASSUME_TAC THENL
     [MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
    ASM_CASES_TAC `(x:real^M) IN U` THENL
     [UNDISCH_TAC `(x:real^M) IN U` THEN EXPAND_TAC "U" THEN
      REWRITE_TAC[IN_UNIONS; EXISTS_IN_IMAGE; IN_NUMSEG] THEN
      DISCH_THEN(X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) THEN
      MP_TAC(ISPECL [`\j. (chi:num->real^M->real) j x`; `1..J`; `j:num`]
                    P2AW_SUM_MEMBER_LE) THEN
      ASM_SIMP_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
      SUBGOAL_THEN `(chi:num->real^M->real) j x = &1` SUBST1_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o SPEC `j:num`) THEN ASM_REWRITE_TAC[] THEN
        DISCH_THEN(MATCH_MP_TAC o CONJUNCT2 o CONJUNCT2) THEN
        UNDISCH_TAC `(x:real^M) IN ball(cs(j:num),rs j / &2)` THEN
        REWRITE_TAC[IN_BALL; IN_CBALL] THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `(psi:real^M->real) x <= &1` MP_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      REAL_ARITH_TAC;
      SUBGOAL_THEN `(psi:real^M->real) x = &0` SUBST1_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]; ALL_TAC] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on (:real^M) (\x. lift((S:real^M->real) x))` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN REWRITE_TAC[LIFT_ADD; LIFT_SUB; LIFT_SUM; o_DEF] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN REWRITE_TAC[OPEN_UNIV] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN
      ASM_REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_CONST];
      MATCH_MP_TAC SMOOTH_MAP_ON_VSUM_OPEN THEN
      REWRITE_TAC[OPEN_UNIV; FINITE_NUMSEG; IN_NUMSEG] THEN
      X_GEN_TAC `j:num` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o check (fun th ->
        can (find_term ((=) `chi:num->real^M->real`)) (concl th) && is_forall(concl th))) THEN
      ASM_REWRITE_TAC[wan_test] THEN SIMP_TAC[]];
    ALL_TAC] THEN
  EXISTS_TAC `\j x. (chi:num->real^M->real) j x / (S:real^M->real) x` THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o check (fun th ->
      can (find_term ((=) `chi:num->real^M->real`)) (concl th) && is_forall(concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [wan_test]) THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `kc:real^M->bool` STRIP_ASSUME_TAC)) THEN
      REWRITE_TAC[wan_test] THEN CONJ_TAC THENL
       [REWRITE_TAC[real_div] THEN
        MP_TAC(ISPECL [`(:real^M)`; `\x. lift((chi:num->real^M->real) j x)`;
                       `\x. lift(inv((S:real^M->real) x))`] SMOOTH_MAP_ON_MUL_LIFT_OPEN) THEN
        REWRITE_TAC[LIFT_DROP; OPEN_UNIV] THEN DISCH_THEN MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[] THEN
        MP_TAC(ISPECL [`(:real^M)`; `\x. lift((S:real^M->real) x)`]
                      CUTOFF_SMOOTH_MAP_ON_LIFT_INV) THEN
        REWRITE_TAC[LIFT_DROP; OPEN_UNIV; IN_UNIV] THEN DISCH_THEN MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:real^M` THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `x:real^M` o check (fun th ->
          can (find_term ((=) `S:real^M->real`)) (concl th) && is_forall(concl th) &&
          not(can (find_term (fun t -> is_const t && fst(dest_const t) = "smooth_map_on"))
                  (concl th)))) THEN
        REAL_ARITH_TAC;
        EXISTS_TAC `kc:real^M->bool` THEN ASM_SIMP_TAC[real_div; REAL_MUL_LZERO]];
      X_GEN_TAC `x:real^M` THEN MATCH_MP_TAC REAL_LE_DIV THEN ASM_SIMP_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `x:real^M` o check (fun th ->
        can (find_term ((=) `S:real^M->real`)) (concl th) && is_forall(concl th) &&
        not(can (find_term (fun t -> is_const t && fst(dest_const t) = "smooth_map_on"))
                (concl th)))) THEN
      REAL_ARITH_TAC];
    X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN REWRITE_TAC[real_div; SUM_RMUL] THEN
    SUBGOAL_THEN `(S:real^M->real) x = sum(1..J) (\j. (chi:num->real^M->real) j x)`
    ASSUME_TAC THENL
     [EXPAND_TAC "S" THEN BETA_TAC THEN ASM_SIMP_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN MATCH_MP_TAC REAL_MUL_RINV THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^M` o check (fun th ->
      can (find_term ((=) `S:real^M->real`)) (concl th) && is_forall(concl th) &&
      not(can (find_term (fun t -> is_const t && fst(dest_const t) = "smooth_map_on"))
              (concl th)))) THEN
    REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* Calculus of directional derivatives in space-time real^(N,1)finite_sum:   *)
(* spatial directions pastecart d 0 as combinations of the partials          *)
(* wan_xder, finite sums and constant multiples.                             *)
(* ========================================================================= *)

let P2AW_XDER_D1 = prove
 (`!(f:real^(N,1)finite_sum->real) z i.
     wan_xder i f z = p2aw_d1 f (pastecart (basis i) (vec 0)) z`,
  REWRITE_TAC[wan_xder; p2aw_d1]);;

let P2AW_D1_PASTE = prove
 (`!(f:real^(N,1)finite_sum->real) z (d:real^N).
     (\w. lift(f w)) differentiable (at z)
     ==> p2aw_d1 f (pastecart d (vec 0)) z = sum(1..dimindex(:N)) (\a. d$a * wan_xder a f z)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p2aw_d1] THEN
  SUBGOAL_THEN `pastecart d (vec 0) =
                vsum(1..dimindex(:N)) (\a. d$a % pastecart (basis a:real^N) (vec 0:real^1))`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`1..dimindex(:N)`; `\a. (d:real^N)$a % basis a:real^N`;
                   `\a:num. (d:real^N)$a % (vec 0:real^1)`] PASTECART_VSUM) THEN
    REWRITE_TAC[FINITE_NUMSEG; PASTECART_CMUL] THEN
    REWRITE_TAC[BASIS_EXPANSION; VECTOR_MUL_RZERO; VSUM_0];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP LINEAR_FRECHET_DERIVATIVE) THEN
  SIMP_TAC[LINEAR_VSUM; FINITE_NUMSEG; o_DEF; LINEAR_CMUL; DROP_VSUM; DROP_CMUL; wan_xder]);;

let P2AW_D1_SUM = prove
 (`!(g:K->real^M->real) Ix e z.
     FINITE Ix /\ (!k. k IN Ix ==> (\w. lift(g k w)) differentiable (at z))
     ==> p2aw_d1 (\w. sum Ix (\k. g k w)) e z = sum Ix (\k. p2aw_d1 (g k) e z)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p2aw_d1; LIFT_SUM; o_DEF] THEN
  SUBGOAL_THEN
   `((\w. vsum Ix (\k. lift((g:K->real^M->real) k w))) has_derivative
     (\h. vsum Ix (\k. frechet_derivative (\w. lift(g k w)) (at z) h))) (at z)`
  MP_TAC THENL
   [MATCH_MP_TAC HAS_DERIVATIVE_VSUM THEN ASM_REWRITE_TAC[ETA_AX] THEN
    ASM_SIMP_TAC[GSYM FRECHET_DERIVATIVE_WORKS];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_SIMP_TAC[DROP_VSUM; o_DEF]);;

let P2AW_D1_CMUL = prove
 (`!(g:real^M->real) c e z.
     (\w. lift(g w)) differentiable (at z)
     ==> p2aw_d1 (\w. c * g w) e z = c * p2aw_d1 g e z`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p2aw_d1; LIFT_CMUL] THEN
  FIRST_ASSUM(MP_TAC o BETA_RULE o SPEC `c:real` o MATCH_MP HAS_DERIVATIVE_CMUL o
    REWRITE_RULE[FRECHET_DERIVATIVE_WORKS]) THEN
  DISCH_THEN(MP_TAC o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[DROP_CMUL]);;

(* ========================================================================= *)
(* The polarization family indexed by k = (i,(j,b)) in (1..n) x ((1..n) x    *)
(* {0,1}): directions P (e_i +- e_j) and weights wp, wm of P^T A P; the      *)
(* exact identity A = sum_k W_k d_k d_k^T, nonnegativity near a point, and   *)
(* the norm bound |d_k| <= 2.                                                *)
(* ========================================================================= *)

let P2AW_SUM_CROSS = prove
 (`!(s:A->bool) (t:B->bool) f.
     FINITE s /\ FINITE t ==> sum (s CROSS t) f = sum s (\i. sum t (\j. f(i,j)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:A->bool`; `\i:A. (t:B->bool)`; `\i j. (f:A#B->real)(i,j)`]
                SUM_SUM_PRODUCT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[CROSS] THEN
  AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM]);;

let P2AW_SUM_01 = prove
 (`!(f:num->real). sum(0..1) f = f 0 + f 1`,
  GEN_TAC THEN REWRITE_TAC[ONE; SUM_CLAUSES_NUMSEG] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[ONE]);;

let p2aw_pix = new_definition
 `p2aw_pix (n:num) = (1..n) CROSS ((1..n) CROSS (0..1))`;;

let p2aw_pdir = new_definition
 `p2aw_pdir (P:real^N^N) (k:num#num#num) =
    P ** (basis (FST k) + (if SND(SND k) = 0 then &1 else -- &1) % basis (FST(SND k)))`;;

let p2aw_pwt = new_definition
 `p2aw_pwt (P:real^N^N) (c0:real) (A:real^N^N) (k:num#num#num) =
    if SND(SND k) = 0 then p2aw_wp (transp P ** A ** P) c0 (FST k) (FST(SND k))
    else p2aw_wm (transp P ** A ** P) c0 (FST k) (FST(SND k))`;;

let P2AW_PIX_FINITE = prove
 (`!n. FINITE(p2aw_pix n)`,
  SIMP_TAC[p2aw_pix; FINITE_CROSS; FINITE_NUMSEG]);;

let P2AW_PFAM_ID = prove
 (`!(A:real^N^N) P c0 a c.
     symmetric_matrix A /\ orthogonal_matrix P /\
     1 <= a /\ a <= dimindex(:N) /\ 1 <= c /\ c <= dimindex(:N)
     ==> A$a$c = sum (p2aw_pix (dimindex(:N)))
                     (\k. p2aw_pwt P c0 A k * p2aw_pdir P k$a * p2aw_pdir P k$c)`,
  REPEAT STRIP_TAC THEN
  SIMP_TAC[p2aw_pix; P2AW_SUM_CROSS; FINITE_CROSS; FINITE_NUMSEG] THEN
  REWRITE_TAC[P2AW_SUM_01; p2aw_pwt; p2aw_pdir; ARITH_EQ] THEN
  REWRITE_TAC[VECTOR_MUL_LID; VECTOR_MUL_LNEG; GSYM VECTOR_SUB] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC P2AW_POLAR_ROT THEN ASM_REWRITE_TAC[]);;

let P2AW_PFAM_NONNEG = prove
 (`!(A:real^N^N) P c0 k.
     (!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
            ==> &0 <= p2aw_wp (transp P ** A ** P) c0 i j /\
                &0 <= p2aw_wm (transp P ** A ** P) c0 i j) /\
     k IN p2aw_pix (dimindex(:N))
     ==> &0 <= p2aw_pwt P c0 A k`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FORALL_PAIR_THM; p2aw_pix] THEN
  SPEC_TAC(`k:num#num#num`,`k:num#num#num`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; IN_CROSS; IN_NUMSEG; p2aw_pwt] THEN
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[]);;

let P2AW_ORTH_NORM = prove
 (`!(P:real^N^N) v. orthogonal_matrix P ==> norm(P ** v) = norm v`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[NORM_EQ] THEN
  REWRITE_TAC[GSYM DOT_LMUL_MATRIX; VECTOR_MATRIX_MUL_TRANSP] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[orthogonal_matrix]) THEN
  ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_ASSOC; MATRIX_VECTOR_MUL_LID]);;

let P2AW_PDIR_NORM = prove
 (`!(P:real^N^N) k.
     orthogonal_matrix P /\ k IN p2aw_pix (dimindex(:N)) ==> norm(p2aw_pdir P k) <= &2`,
  REWRITE_TAC[FORALL_PAIR_THM; p2aw_pix; IN_CROSS; IN_NUMSEG; p2aw_pdir] THEN
  MAP_EVERY X_GEN_TAC [`P:real^N^N`; `i:num`; `j:num`; `b:num`] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[P2AW_ORTH_NORM] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `norm(basis i:real^N) +
              norm((if b = 0 then &1 else -- &1) % basis j:real^N)` THEN
  REWRITE_TAC[NORM_TRIANGLE; NORM_MUL] THEN
  ASM_SIMP_TAC[NORM_BASIS] THEN COND_CASES_TAC THEN
  REWRITE_TAC[REAL_ABS_NEG; REAL_ABS_NUM] THEN REAL_ARITH_TAC);;

(* ========================================================================= *)
(* The polarization family turns the directional sums of the                 *)
(* barrier principle into the matrix forms:                                  *)
(*   sum_k W_k (D_k u)(D_k phi) = sum_ab A_ab (D_a u)(D_b phi),              *)
(*   sum_k D_k (W_k D_k psi)     = sum_a D_a (sum_b A_ab D_b psi).           *)
(* ========================================================================= *)

let P2AW_AFFINE_SMOOTH = prove
 (`!(O:real^M->bool) (g:real^M->real) alpha beta.
     open O /\ smooth_map_on O (\x. lift(g x))
     ==> smooth_map_on O (\x. lift(alpha * g x + beta))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LIFT_ADD; LIFT_CMUL] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN
  ASM_SIMP_TAC[SMOOTH_MAP_ON_CMUL_OPEN; SMOOTH_MAP_ON_CONST]);;

let P2AW_PWT_SMOOTH = prove
 (`!(O:real^M->bool) (A:real^M->real^N^N) P c0 k.
     open O /\
     (!a b. 1 <= a /\ a <= dimindex(:N) /\ 1 <= b /\ b <= dimindex(:N)
            ==> smooth_map_on O (\x. lift(A x$a$b))) /\
     k IN p2aw_pix (dimindex(:N))
     ==> smooth_map_on O (\x. lift(p2aw_pwt P c0 (A x) k))`,
  REWRITE_TAC[FORALL_PAIR_THM; p2aw_pix; IN_CROSS; IN_NUMSEG] THEN
  MAP_EVERY X_GEN_TAC [`O:real^M->bool`; `A:real^M->real^N^N`; `P:real^N^N`; `c0:real`;
                       `i:num`; `j:num`; `b:num`] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!p q. 1 <= p /\ p <= dimindex(:N) /\ 1 <= q /\ q <= dimindex(:N)
          ==> smooth_map_on O (\x. lift((transp (P:real^N^N) ** (A:real^M->real^N^N) x ** P)$p$q))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN ASM_SIMP_TAC[matrix_mul; LAMBDA_BETA; TRANSP_COMPONENT] THEN
    REWRITE_TAC[LIFT_SUM; o_DEF] THEN MATCH_MP_TAC SMOOTH_MAP_ON_VSUM_OPEN THEN
    ASM_REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN X_GEN_TAC `r:num` THEN STRIP_TAC THEN
    BETA_TAC THEN ASM_SIMP_TAC[LAMBDA_BETA] THEN REWRITE_TAC[LIFT_CMUL] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_CMUL_OPEN THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[LIFT_SUM; o_DEF] THEN MATCH_MP_TAC SMOOTH_MAP_ON_VSUM_OPEN THEN
    ASM_REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN X_GEN_TAC `t:num` THEN STRIP_TAC THEN
    BETA_TAC THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[LIFT_CMUL] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_CMUL_OPEN THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[p2aw_pwt; p2aw_wp; p2aw_wm] THEN
  ASM_CASES_TAC `b = 0` THEN ASM_CASES_TAC `i:num = j` THEN
  ASM_REWRITE_TAC[LIFT_NUM; SMOOTH_MAP_ON_CONST] THENL
   [SUBGOAL_THEN `!x:real^M. ((transp (P:real^N^N) ** (A:real^M->real^N^N) x ** P)$j$j -
                             (&(dimindex(:N)) - &1) * c0) / &4 =
                            inv(&4) * (transp P ** A x ** P)$j$j +
                            --((&(dimindex(:N)) - &1) * c0 / &4)`
    (fun th -> REWRITE_TAC[th]) THENL [GEN_TAC THEN REAL_ARITH_TAC; ALL_TAC];
    SUBGOAL_THEN `!x:real^M. (c0 + (transp (P:real^N^N) ** (A:real^M->real^N^N) x ** P)$i$j) / &4 =
                            inv(&4) * (transp P ** A x ** P)$i$j + c0 / &4`
    (fun th -> REWRITE_TAC[th]) THENL [GEN_TAC THEN REAL_ARITH_TAC; ALL_TAC];
    SUBGOAL_THEN `!x:real^M. (c0 - (transp (P:real^N^N) ** (A:real^M->real^N^N) x ** P)$i$j) / &4 =
                            --inv(&4) * (transp P ** A x ** P)$i$j + c0 / &4`
    (fun th -> REWRITE_TAC[th]) THENL [GEN_TAC THEN REAL_ARITH_TAC; ALL_TAC]] THEN
  MATCH_MP_TAC P2AW_AFFINE_SMOOTH THEN ASM_SIMP_TAC[]);;

let P2AW_SUM_SWAP3 = prove
 (`!(G:num->num->K->real) s n.
     FINITE s
     ==> sum(1..n) (\a. sum(1..n) (\b. sum s (\k. G a b k))) =
         sum s (\k. sum(1..n) (\a. sum(1..n) (\b. G a b k)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\a:num k:K. sum(1..n) (\b. (G:num->num->K->real) a b k)`;
                 `1..n`; `s:K->bool`] SUM_SWAP) THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MP_TAC(ISPECL [`\b:num k:K. (G:num->num->K->real) a b k`; `1..n`; `s:K->bool`]
                SUM_SWAP) THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG]);;

let P2AW_PFAM_BIL = prove
 (`!(A:real^N^N) P c0 (u:real^(N,1)finite_sum->real) phi z.
     symmetric_matrix A /\ orthogonal_matrix P /\
     (\w. lift(u w)) differentiable (at z) /\ (\w. lift(phi w)) differentiable (at z)
     ==> sum (p2aw_pix (dimindex(:N)))
           (\k. p2aw_pwt P c0 A k * p2aw_d1 u (pastecart (p2aw_pdir P k) (vec 0)) z *
                p2aw_d1 phi (pastecart (p2aw_pdir P k) (vec 0)) z) =
         sum(1..dimindex(:N)) (\a. sum(1..dimindex(:N))
           (\b. A$a$b * wan_xder a u z * wan_xder b phi z))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[P2AW_D1_PASTE] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `sum (p2aw_pix (dimindex(:N))) (\k. sum(1..dimindex(:N)) (\a. sum(1..dimindex(:N))
     (\b. (p2aw_pwt P c0 (A:real^N^N) k * p2aw_pdir P k$a * p2aw_pdir P k$b) *
          wan_xder a (u:real^(N,1)finite_sum->real) z * wan_xder b phi z)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `k:num#num#num` THEN DISCH_TAC THEN BETA_TAC THEN
    SIMP_TAC[REAL_MUL_SUM; FINITE_NUMSEG; GSYM SUM_LMUL] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN BETA_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SIMP_TAC[GSYM P2AW_SUM_SWAP3; P2AW_PIX_FINITE] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `b:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MP_TAC(ISPECL [`A:real^N^N`; `P:real^N^N`; `c0:real`; `a:num`; `b:num`] P2AW_PFAM_ID) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[SUM_RMUL]);;

let P2AW_PFAM_DIV = prove
 (`!(O:real^(N,1)finite_sum->bool) (A:real^(N,1)finite_sum->real^N^N) P c0 psi z.
     open O /\ z IN O /\ orthogonal_matrix P /\
     (!y. y IN O ==> symmetric_matrix(A y)) /\
     (!a b. 1 <= a /\ a <= dimindex(:N) /\ 1 <= b /\ b <= dimindex(:N)
            ==> smooth_map_on O (\x. lift(A x$a$b))) /\
     smooth_map_on O (\x. lift(psi x))
     ==> sum (p2aw_pix (dimindex(:N)))
           (\k. p2aw_dlim (\y. p2aw_pwt P c0 (A y) k) (pastecart (p2aw_pdir P k) (vec 0))
                          psi z) =
         sum(1..dimindex(:N))
           (\a. wan_xder a (\w. sum(1..dimindex(:N)) (\b. A w$a$b * wan_xder b psi w)) z)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `G = \k w. p2aw_pwt (P:real^N^N) c0 ((A:real^(N,1)finite_sum->real^N^N) w) k *
                        p2aw_d1 psi (pastecart (p2aw_pdir (P:real^N^N) k) (vec 0:real^1)) w` THEN
  SUBGOAL_THEN
   `!k. k IN p2aw_pix (dimindex(:N))
        ==> smooth_map_on O (\w. lift((G:num#num#num->real^(N,1)finite_sum->real) k w))`
  ASSUME_TAC THENL
   [X_GEN_TAC `k:num#num#num` THEN DISCH_TAC THEN EXPAND_TAC "G" THEN
    REWRITE_TAC[LIFT_CMUL] THEN
    MP_TAC(ISPECL [`O:real^(N,1)finite_sum->bool`;
                   `\w. lift(p2aw_pwt (P:real^N^N) c0 ((A:real^(N,1)finite_sum->real^N^N) w) k)`;
                   `\w. lift(p2aw_d1 psi (pastecart (p2aw_pdir (P:real^N^N) k) (vec 0:real^1)) w)`]
                  SMOOTH_MAP_ON_MUL_LIFT_OPEN) THEN
    REWRITE_TAC[LIFT_DROP; GSYM LIFT_CMUL] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_SIMP_TAC[P2AW_PWT_SMOOTH; P2AW_D1_SMOOTH];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!k. k IN p2aw_pix (dimindex(:N))
        ==> p2aw_dlim (\y. p2aw_pwt P c0 ((A:real^(N,1)finite_sum->real^N^N) y) k)
                      (pastecart (p2aw_pdir (P:real^N^N) k) (vec 0:real^1)) psi z =
            sum(1..dimindex(:N))
              (\a. p2aw_pdir P k$a * wan_xder a ((G:num#num#num->real^(N,1)finite_sum->real) k) z)`
  ASSUME_TAC THENL
   [X_GEN_TAC `k:num#num#num` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`(G:num#num#num->real^(N,1)finite_sum->real) k`; `z:real^(N,1)finite_sum`;
                   `p2aw_pdir (P:real^N^N) k`] P2AW_D1_PASTE) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `O:real^(N,1)finite_sum->bool` THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    EXPAND_TAC "G" THEN
    MP_TAC(ISPECL [`O:real^(N,1)finite_sum->bool`;
                   `\y. p2aw_pwt (P:real^N^N) c0 ((A:real^(N,1)finite_sum->real^N^N) y) k`;
                   `\y. p2aw_d1 psi (pastecart (p2aw_pdir (P:real^N^N) k) (vec 0:real^1)) y`;
                   `pastecart (p2aw_pdir (P:real^N^N) k) (vec 0:real^1)`; `z:real^(N,1)finite_sum`]
                  P2AW_D1_PRODUCT) THEN
    ASM_SIMP_TAC[P2AW_PWT_SMOOTH; P2AW_D1_SMOOTH; ETA_AX] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[p2aw_dlim; P2AW_D2_D1; ETA_AX] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `sum (p2aw_pix (dimindex(:N)))
    (\k. sum(1..dimindex(:N))
      (\a. p2aw_pdir (P:real^N^N) k$a *
           wan_xder a ((G:num#num#num->real^(N,1)finite_sum->real) k) z))` THEN
  CONJ_TAC THENL [MATCH_MP_TAC SUM_EQ THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`\k:num#num#num a:num. p2aw_pdir (P:real^N^N) k$a *
                   wan_xder a ((G:num#num#num->real^(N,1)finite_sum->real) k) z`;
                 `p2aw_pix (dimindex(:N))`; `1..dimindex(:N)`] SUM_SWAP) THEN
  REWRITE_TAC[P2AW_PIX_FINITE; FINITE_NUMSEG] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN BETA_TAC THEN
  SUBGOAL_THEN
   `sum (p2aw_pix (dimindex(:N)))
      (\k. p2aw_pdir (P:real^N^N) k$a *
           wan_xder a ((G:num#num#num->real^(N,1)finite_sum->real) k) z) =
    wan_xder a (\w. sum (p2aw_pix (dimindex(:N))) (\k. p2aw_pdir P k$a * G k w)) z`
  SUBST1_TAC THENL
   [REWRITE_TAC[P2AW_XDER_D1] THEN
    W(fun (asl,w) -> MP_TAC(ISPECL
      [`\k:num#num#num w. p2aw_pdir (P:real^N^N) k$a *
                          (G:num#num#num->real^(N,1)finite_sum->real) k w`;
       `p2aw_pix (dimindex(:N))`; `pastecart (basis a:real^N) (vec 0:real^1)`;
       `z:real^(N,1)finite_sum`] P2AW_D1_SUM)) THEN
    REWRITE_TAC[P2AW_PIX_FINITE] THEN ANTS_TAC THENL
     [X_GEN_TAC `k:num#num#num` THEN DISCH_TAC THEN REWRITE_TAC[LIFT_CMUL] THEN
      MATCH_MP_TAC DIFFERENTIABLE_CMUL THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
      EXISTS_TAC `O:real^(N,1)finite_sum->bool` THEN ASM_SIMP_TAC[];
      DISCH_THEN SUBST1_TAC] THEN
    MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `k:num#num#num` THEN DISCH_TAC THEN BETA_TAC THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC P2AW_D1_CMUL THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `O:real^(N,1)finite_sum->bool` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  GEN_REWRITE_TAC BINOP_CONV [P2AW_XDER_D1] THEN MATCH_MP_TAC P2AW_D1_LOCAL THEN
  EXISTS_TAC `O:real^(N,1)finite_sum->bool` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `w:real^(N,1)finite_sum` THEN DISCH_TAC THEN
  EXPAND_TAC "G" THEN
  SUBGOAL_THEN `(\v. lift((psi:real^(N,1)finite_sum->real) v)) differentiable (at w)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `O:real^(N,1)finite_sum->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[P2AW_D1_PASTE] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `sum(1..dimindex(:N)) (\b. sum (p2aw_pix (dimindex(:N)))
     (\k. p2aw_pwt (P:real^N^N) c0 ((A:real^(N,1)finite_sum->real^N^N) w) k *
          p2aw_pdir P k$a * p2aw_pdir P k$b) * wan_xder b psi w)` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM SUM_RMUL] THEN
    MP_TAC(ISPECL [`\b:num k:num#num#num.
                     (p2aw_pwt (P:real^N^N) c0 ((A:real^(N,1)finite_sum->real^N^N) w) k *
                      p2aw_pdir P k$a * p2aw_pdir P k$b) * wan_xder b psi w`;
                   `1..dimindex(:N)`; `p2aw_pix (dimindex(:N))`] SUM_SWAP) THEN
    REWRITE_TAC[P2AW_PIX_FINITE; FINITE_NUMSEG] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `k:num#num#num` THEN DISCH_TAC THEN BETA_TAC THEN
    REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
    REPEAT STRIP_TAC THEN BETA_TAC THEN REAL_ARITH_TAC;
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `b:num` THEN STRIP_TAC THEN BETA_TAC THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC P2AW_PFAM_ID THEN ASM_SIMP_TAC[]]);;

(* ========================================================================= *)
(* The barrier principle in matrix form on an open set O where the           *)
(* polarization weights of one frame P are nonnegative.                      *)
(* ========================================================================= *)

let P2AW_LIP_NULL = prove
 (`!(O:real^M->bool) u kp.
     open O /\ wan_loclip O u /\ compact kp /\ kp SUBSET O
     ==> ?V. open V /\ kp SUBSET V /\ V SUBSET O /\
             negligible {x | x IN V /\ ~((\w. lift(u w)) differentiable (at x))}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`O:real^M->bool`; `kp:real^M->bool`] WAN_COMPACT_NBHD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `{x + y:real^M | x IN kp /\ y IN ball(vec 0,d)}` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC RADEMACHER_OPEN THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `{x + y:real^M | x IN kp /\ y IN cball(vec 0,d)}` o
    REWRITE_RULE[wan_loclip] o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "wan_loclip")) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `L:real`) THEN
  EXISTS_TAC `L:real` THEN REWRITE_TAC[GSYM LIFT_SUB; NORM_LIFT] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]);;

let P2AW_NBP_FRAME = prove
 (`!(O:real^(N,1)finite_sum->bool) (A:real^(N,1)finite_sum->real^N^N) P c0
    (u:real^(N,1)finite_sum->real) Fb phi.
     open O /\ orthogonal_matrix P /\
     (!y. y IN O ==> symmetric_matrix(A y)) /\
     (!a b. 1 <= a /\ a <= dimindex(:N) /\ 1 <= b /\ b <= dimindex(:N)
            ==> smooth_map_on O (\x. lift(A x$a$b))) /\
     (!x i j. x IN O /\ 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
              ==> &0 <= p2aw_wp (transp P ** A x ** P) c0 i j /\
                  &0 <= p2aw_wm (transp P ** A x ** P) c0 i j) /\
     wan_loclip O u /\ wan_test O phi /\ (!x. &0 <= phi x) /\
     (!kk. compact kk /\ kk SUBSET O
           ==> ?C d. &0 < d /\
                     !x v t. x IN kk /\ norm v <= &2 /\ abs t < d
                             ==> u(x + t % pastecart v (vec 0)) + u(x - t % pastecart v (vec 0)) -
                                 &2 * u x <= C * t pow 2) /\
     (\x. lift(Fb x)) measurable_on O /\
     (!kk. compact kk /\ kk SUBSET O ==> ?C. !x. x IN kk ==> abs(Fb x) <= C) /\
     (?N. negligible N /\
          !x. x IN O /\ ~(x IN N) /\ &0 < phi x
              ==> ?psi r. &0 < r /\ ball(x,r) SUBSET O /\
                          smooth_map_on (ball(x,r)) (\y. lift(psi y)) /\
                          (!v t. norm v <= &2 /\ x + t % pastecart v (vec 0) IN ball(x,r) /\
                                 x - t % pastecart v (vec 0) IN ball(x,r)
                                 ==> u(x + t % pastecart v (vec 0)) <=
                                     psi(x + t % pastecart v (vec 0)) /\
                                     u(x - t % pastecart v (vec 0)) <=
                                     psi(x - t % pastecart v (vec 0))) /\
                          psi x = u x /\
                          sum(1..dimindex(:N))
                            (\a. wan_xder a (\w. sum(1..dimindex(:N))
                                                   (\b. A w$a$b * wan_xder b psi w)) x)
                          <= Fb x)
     ==> (\x. lift(phi x * Fb x)) integrable_on O /\
         (\x. lift(sum(1..dimindex(:N)) (\a. sum(1..dimindex(:N))
                (\b. A x$a$b * wan_xder a u x * wan_xder b phi x)))) integrable_on O /\
         &0 <= drop(integral O (\x. lift(phi x * Fb x))) +
               drop(integral O (\x. lift(sum(1..dimindex(:N)) (\a. sum(1..dimindex(:N))
                      (\b. A x$a$b * wan_xder a u x * wan_xder b phi x)))))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (LABEL_TAC "NN") (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (LABEL_TAC "SC") (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (LABEL_TAC "FB") (X_CHOOSE_THEN `N:real^(N,1)finite_sum->bool`
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "BAR")))))))))))))) THEN
  MP_TAC(ISPECL [`O:real^(N,1)finite_sum->bool`; `u:real^(N,1)finite_sum->real`;
                 `p2aw_pix (dimindex(:N))`;
                 `\k. pastecart (p2aw_pdir (P:real^N^N) k) (vec 0:real^1)`;
                 `\k x. p2aw_pwt (P:real^N^N) c0 ((A:real^(N,1)finite_sum->real^N^N) x) k`;
                 `Fb:real^(N,1)finite_sum->real`; `phi:real^(N,1)finite_sum->real`]
                P2AW_NBP) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[P2AW_PIX_FINITE] THEN REPEAT CONJ_TAC THENL
     [X_GEN_TAC `k:num#num#num` THEN DISCH_TAC THEN CONJ_TAC THENL
       [MATCH_MP_TAC P2AW_PWT_SMOOTH THEN ASM_REWRITE_TAC[];
        X_GEN_TAC `x:real^(N,1)finite_sum` THEN DISCH_TAC THEN
        MATCH_MP_TAC P2AW_PFAM_NONNEG THEN ASM_SIMP_TAC[]];
      X_GEN_TAC `kk:real^(N,1)finite_sum->bool` THEN STRIP_TAC THEN
      USE_THEN "SC" (MP_TAC o SPEC `kk:real^(N,1)finite_sum->bool`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `C:real` THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_SIMP_TAC[P2AW_PDIR_NORM];
      EXISTS_TAC `N:real^(N,1)finite_sum->bool` THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `x:real^(N,1)finite_sum` THEN STRIP_TAC THEN
      USE_THEN "BAR" (MP_TAC o SPEC `x:real^(N,1)finite_sum`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `psi:real^(N,1)finite_sum->real` THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `r:real` THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        ASM_SIMP_TAC[P2AW_PDIR_NORM];
        ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `sum(1..dimindex(:N))
        (\a. wan_xder a (\w. sum(1..dimindex(:N))
          (\b. (A:real^(N,1)finite_sum->real^N^N) w$a$b *
               wan_xder b (psi:real^(N,1)finite_sum->real) w)) x)` THEN
      ASM_REWRITE_TAC[REAL_LE_REFL] THEN
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC P2AW_PFAM_DIV THEN
      EXISTS_TAC `ball(x:real^(N,1)finite_sum,r)` THEN
      ASM_REWRITE_TAC[CENTRE_IN_BALL; OPEN_BALL] THEN CONJ_TAC THENL
       [ASM SET_TAC[];
        REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
        EXISTS_TAC `O:real^(N,1)finite_sum->bool` THEN ASM_SIMP_TAC[]]];
    ALL_TAC] THEN
  REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [wan_test] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "wan_test")) (concl th))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `kp:real^(N,1)finite_sum->bool` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`O:real^(N,1)finite_sum->bool`; `u:real^(N,1)finite_sum->real`;
                 `kp:real^(N,1)finite_sum->bool`] P2AW_LIP_NULL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `V:real^(N,1)finite_sum->bool` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `Nu = {x | x IN V /\ ~((\w. lift((u:real^(N,1)finite_sum->real) w))
                                     differentiable (at x))}` THEN
  SUBGOAL_THEN
   `!x. x IN O DIFF Nu
        ==> lift(sum(1..dimindex(:N)) (\a. sum(1..dimindex(:N))
               (\b. (A:real^(N,1)finite_sum->real^N^N) x$a$b * wan_xder a u x *
                    wan_xder b phi x))) =
            vsum (p2aw_pix (dimindex(:N)))
              (\k. lift(p2aw_pwt (P:real^N^N) c0 (A x) k *
                        p2aw_d1 u (pastecart (p2aw_pdir P k) (vec 0)) x *
                        p2aw_d1 phi (pastecart (p2aw_pdir P k) (vec 0)) x))`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^(N,1)finite_sum` THEN REWRITE_TAC[IN_DIFF] THEN STRIP_TAC THEN
    W(fun (asl,w) -> SUBGOAL_THEN (mk_eq(rand w, mk_comb(`lift`,
        mk_comb(mk_comb(`sum:(num#num#num->bool)->(num#num#num->real)->real`,
                        lhand(rand w)),
                mk_abs(bndvar(rand(rand w)), rand(body(rand(rand w))))))))
      SUBST1_TAC) THENL
     [REWRITE_TAC[LIFT_SUM; o_DEF]; ALL_TAC] THEN
    REWRITE_TAC[LIFT_EQ] THEN
    ASM_CASES_TAC `(x:real^(N,1)finite_sum) IN V` THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC P2AW_PFAM_BIL THEN ASM_SIMP_TAC[] THEN CONJ_TAC THENL
       [UNDISCH_TAC `~((x:real^(N,1)finite_sum) IN Nu)` THEN EXPAND_TAC "Nu" THEN
        ASM_REWRITE_TAC[IN_ELIM_THM];
        MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
        EXISTS_TAC `(:real^(N,1)finite_sum)` THEN ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV]];
      SUBGOAL_THEN `~((x:real^(N,1)finite_sum) IN kp)` ASSUME_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `!d. p2aw_d1 (phi:real^(N,1)finite_sum->real) d x = &0` ASSUME_TAC THENL
       [GEN_TAC THEN MATCH_MP_TAC P2AW_SUPPORT_D1 THEN
        EXISTS_TAC `kp:real^(N,1)finite_sum->bool` THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[P2AW_XDER_D1; REAL_MUL_RZERO; SUM_0]];
    ALL_TAC] THEN
  SUBGOAL_THEN `negligible(Nu:real^(N,1)finite_sum->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "Nu" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(\x. vsum (p2aw_pix (dimindex(:N)))
      (\k. lift(p2aw_pwt (P:real^N^N) c0 ((A:real^(N,1)finite_sum->real^N^N) x) k *
                p2aw_d1 u (pastecart (p2aw_pdir P k) (vec 0)) x *
                p2aw_d1 phi (pastecart (p2aw_pdir P k) (vec 0)) x))) integrable_on O`
  ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_VSUM THEN ASM_SIMP_TAC[P2AW_PIX_FINITE]; ALL_TAC] THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL
     [`\x. vsum (p2aw_pix (dimindex(:N)))
        (\k. lift(p2aw_pwt (P:real^N^N) c0 ((A:real^(N,1)finite_sum->real^N^N) x) k *
                  p2aw_d1 u (pastecart (p2aw_pdir P k) (vec 0)) x *
                  p2aw_d1 phi (pastecart (p2aw_pdir P k) (vec 0)) x))`;
      `\x. lift(sum(1..dimindex(:N)) (\a. sum(1..dimindex(:N))
         (\b. (A:real^(N,1)finite_sum->real^N^N) x$a$b * wan_xder a u x *
              wan_xder b phi x)))`;
      `Nu:real^(N,1)finite_sum->bool`; `O:real^(N,1)finite_sum->bool`] INTEGRABLE_SPIKE) THEN
    REWRITE_TAC[] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `integral O (\x. lift(sum(1..dimindex(:N)) (\a. sum(1..dimindex(:N))
       (\b. (A:real^(N,1)finite_sum->real^N^N) x$a$b * wan_xder a u x * wan_xder b phi x)))) =
    vsum (p2aw_pix (dimindex(:N)))
      (\k. integral O (\x. lift(p2aw_pwt (P:real^N^N) c0 (A x) k *
                                p2aw_d1 u (pastecart (p2aw_pdir P k) (vec 0)) x *
                                p2aw_d1 phi (pastecart (p2aw_pdir P k) (vec 0)) x)))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `integral O (\x. vsum (p2aw_pix (dimindex(:N)))
      (\k. lift(p2aw_pwt (P:real^N^N) c0 ((A:real^(N,1)finite_sum->real^N^N) x) k *
                p2aw_d1 u (pastecart (p2aw_pdir P k) (vec 0)) x *
                p2aw_d1 phi (pastecart (p2aw_pdir P k) (vec 0)) x)))` THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL
       [`\x. vsum (p2aw_pix (dimindex(:N)))
          (\k. lift(p2aw_pwt (P:real^N^N) c0 ((A:real^(N,1)finite_sum->real^N^N) x) k *
                    p2aw_d1 u (pastecart (p2aw_pdir P k) (vec 0)) x *
                    p2aw_d1 phi (pastecart (p2aw_pdir P k) (vec 0)) x))`;
        `\x. lift(sum(1..dimindex(:N)) (\a. sum(1..dimindex(:N))
           (\b. (A:real^(N,1)finite_sum->real^N^N) x$a$b * wan_xder a u x *
                wan_xder b phi x)))`;
        `Nu:real^(N,1)finite_sum->bool`; `O:real^(N,1)finite_sum->bool`] INTEGRAL_SPIKE) THEN
      REWRITE_TAC[] THEN ASM_SIMP_TAC[];
      MP_TAC(ISPECL
       [`\k x. lift(p2aw_pwt (P:real^N^N) c0 ((A:real^(N,1)finite_sum->real^N^N) x) k *
                    p2aw_d1 u (pastecart (p2aw_pdir P k) (vec 0)) x *
                    p2aw_d1 phi (pastecart (p2aw_pdir P k) (vec 0)) x)`;
        `O:real^(N,1)finite_sum->bool`; `p2aw_pix (dimindex(:N))`] INTEGRAL_VSUM) THEN
      REWRITE_TAC[P2AW_PIX_FINITE] THEN ASM_SIMP_TAC[ETA_AX]];
    ALL_TAC] THEN
  ASM_SIMP_TAC[DROP_VSUM; P2AW_PIX_FINITE; o_DEF]);;

(* ========================================================================= *)
(* The barrier principle in matrix form on an open set s with A smooth,      *)
(* symmetric and positive definite: local frames on balls, a finite cover of *)
(* the support of the test, a partition of unity of the test and summation   *)
(* of the frame inequalities of the previous section.                        *)
(* ========================================================================= *)

let P2AW_INTEGRAL_SUPERSET = prove
 (`!(f:real^M->real^1) s t.
     (!x. ~(x IN s) ==> f x = vec 0) /\ s SUBSET t /\ f integrable_on s
     ==> f integrable_on t /\ integral t f = integral s f`,
  REPEAT STRIP_TAC THENL
   [ASM_MESON_TAC[INTEGRABLE_ON_SUPERSET];
    MATCH_MP_TAC INTEGRAL_UNIQUE THEN MATCH_MP_TAC HAS_INTEGRAL_ON_SUPERSET THEN
    EXISTS_TAC `s:real^M->bool` THEN ASM_REWRITE_TAC[GSYM HAS_INTEGRAL_INTEGRAL]]);;

let P2AW_LOCAL_FRAME_BALL = prove
 (`!(s:real^M->bool) (A:real^M->real^N^N) c.
     open s /\ c IN s /\
     (!a b. 1 <= a /\ a <= dimindex(:N) /\ 1 <= b /\ b <= dimindex(:N)
            ==> smooth_map_on s (\x. lift(A x$a$b))) /\
     symmetric_matrix(A c) /\ (!v. ~(v = vec 0) ==> &0 < v dot (A c ** v))
     ==> ?P c0 r. orthogonal_matrix P /\ &0 < r /\ ball(c,r) SUBSET s /\
                  !x i j. x IN ball(c,r) /\ 1 <= i /\ i <= dimindex(:N) /\
                          1 <= j /\ j <= dimindex(:N)
                          ==> &0 <= p2aw_wp (transp P ** A x ** P) c0 i j /\
                              &0 <= p2aw_wm (transp P ** A x ** P) c0 i j`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`A:real^M->real^N^N`; `c:real^M`] P2AW_LOCAL_DECOMP) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `s:real^M->bool` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `P:real^N^N` (X_CHOOSE_THEN `c0:real`
    (X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC))) THEN
  FIRST_ASSUM(MP_TAC o SPEC `c:real^M` o GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`P:real^N^N`; `c0:real`; `min r e:real`] THEN
  ASM_REWRITE_TAC[REAL_LT_MIN] THEN CONJ_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `ball(c:real^M,e)` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET; IN_BALL] THEN GEN_TAC THEN REAL_ARITH_TAC;
    REPEAT GEN_TAC THEN REWRITE_TAC[IN_BALL] THEN STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REAL_ARITH_TAC]);;

let P2AW_FRAME_COVER = prove
 (`!(s:real^M->bool) (A:real^M->real^N^N) kp.
     open s /\ compact kp /\ kp SUBSET s /\
     (!a b. 1 <= a /\ a <= dimindex(:N) /\ 1 <= b /\ b <= dimindex(:N)
            ==> smooth_map_on s (\x. lift(A x$a$b))) /\
     (!y. y IN s ==> symmetric_matrix(A y) /\ !v. ~(v = vec 0) ==> &0 < v dot (A y ** v))
     ==> ?J (cs:num->real^M) rs (Ps:num->real^N^N) c0s.
           (!j. 1 <= j /\ j <= J
                ==> &0 < rs j /\ ball(cs j, rs j) SUBSET s /\ orthogonal_matrix(Ps j) /\
                    !x i k. x IN ball(cs j, rs j) /\ 1 <= i /\ i <= dimindex(:N) /\
                            1 <= k /\ k <= dimindex(:N)
                            ==> &0 <= p2aw_wp (transp(Ps j) ** A x ** Ps j) (c0s j) i k /\
                                &0 <= p2aw_wm (transp(Ps j) ** A x ** Ps j) (c0s j) i k) /\
           kp SUBSET UNIONS (IMAGE (\j. ball(cs j, rs j / &2)) (1..J))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!c. ?P c0 r. (c:real^M) IN kp
                 ==> orthogonal_matrix P /\ &0 < r /\ ball(c,r) SUBSET s /\
                     !x i k. x IN ball(c,r) /\ 1 <= i /\ i <= dimindex(:N) /\
                             1 <= k /\ k <= dimindex(:N)
                             ==> &0 <= p2aw_wp (transp P ** (A:real^M->real^N^N) x ** P) c0 i k /\
                                 &0 <= p2aw_wm (transp P ** A x ** P) c0 i k`
  MP_TAC THENL
   [X_GEN_TAC `c:real^M` THEN REWRITE_TAC[RIGHT_EXISTS_IMP_THM] THEN DISCH_TAC THEN
    MATCH_MP_TAC P2AW_LOCAL_FRAME_BALL THEN
    SUBGOAL_THEN `(c:real^M) IN s` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `P:real^M->real^N^N` (X_CHOOSE_THEN `c0:real^M->real`
    (X_CHOOSE_THEN `r:real^M->real` (LABEL_TAC "LOC")))) THEN
  FIRST_ASSUM(MP_TAC o SPEC `IMAGE (\c:real^M. ball(c, (r:real^M->real) c / &2)) kp` o
    GEN_REWRITE_RULE I [COMPACT_EQ_HEINE_BOREL]) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FORALL_IN_IMAGE; OPEN_BALL] THEN
    REWRITE_TAC[SUBSET; IN_UNIONS; EXISTS_IN_IMAGE; IN_BALL] THEN
    X_GEN_TAC `c:real^M` THEN DISCH_TAC THEN EXISTS_TAC `c:real^M` THEN
    ASM_REWRITE_TAC[DIST_REFL] THEN
    USE_THEN "LOC" (MP_TAC o SPEC `c:real^M`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    STRIP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `ff:(real^M->bool)->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`\c:real^M. ball(c, (r:real^M->real) c / &2)`; `kp:real^M->bool`;
                 `ff:(real^M->bool)->bool`] FINITE_SUBSET_IMAGE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `D:real^M->bool`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC))) THEN
  MP_TAC(ISPEC `D:real^M->bool` FINITE_INDEX_NUMSEG) THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `J = CARD(D:real^M->bool)` THEN
  DISCH_THEN(X_CHOOSE_THEN `g:num->real^M` (CONJUNCTS_THEN2 (K ALL_TAC) ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC
   [`J:num`; `g:num->real^M`; `\j. (r:real^M->real)((g:num->real^M) j)`;
    `\j. (P:real^M->real^N^N)((g:num->real^M) j)`; `\j. (c0:real^M->real)((g:num->real^M) j)`] THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `j IN 1..J` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[IN_NUMSEG]; ALL_TAC] THEN
    SUBGOAL_THEN `(g:num->real^M) j IN kp` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    USE_THEN "LOC" (MP_TAC o SPEC `(g:num->real^M) j`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `kp SUBSET UNIONS (IMAGE (\c:real^M. ball(c, (r:real^M->real) c / &2)) D)` THEN
  ASM_REWRITE_TAC[GSYM IMAGE_o; o_DEF] THEN DISCH_THEN ACCEPT_TAC);;

let P2AW_NBP_PIECE = prove
 (`!(s:real^(N,1)finite_sum->bool) (A:real^(N,1)finite_sum->real^N^N) P c0 c rc
    (u:real^(N,1)finite_sum->real) Fb phi theta.
     (?N. negligible N /\
          !x. x IN s /\ ~(x IN N) /\ &0 < phi x
              ==> ?psi r. &0 < r /\ ball(x,r) SUBSET s /\
                          smooth_map_on (ball(x,r)) (\y. lift(psi y)) /\
                          (!v t. norm v <= &2 /\ x + t % pastecart v (vec 0) IN ball(x,r) /\
                                 x - t % pastecart v (vec 0) IN ball(x,r)
                                 ==> u(x + t % pastecart v (vec 0)) <=
                                     psi(x + t % pastecart v (vec 0)) /\
                                     u(x - t % pastecart v (vec 0)) <=
                                     psi(x - t % pastecart v (vec 0))) /\
                          psi x = u x /\
                          sum(1..dimindex(:N))
                            (\a. wan_xder a (\w. sum(1..dimindex(:N))
                                                   (\b. A w$a$b * wan_xder b psi w)) x)
                          <= Fb x) /\
     open s /\ orthogonal_matrix P /\ ball(c,rc) SUBSET s /\
     (!y. y IN s ==> symmetric_matrix(A y)) /\
     (!a b. 1 <= a /\ a <= dimindex(:N) /\ 1 <= b /\ b <= dimindex(:N)
            ==> smooth_map_on s (\x. lift(A x$a$b))) /\
     (!x i j. x IN ball(c,rc) /\ 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
              ==> &0 <= p2aw_wp (transp P ** A x ** P) c0 i j /\
                  &0 <= p2aw_wm (transp P ** A x ** P) c0 i j) /\
     wan_loclip s u /\ wan_test s phi /\ (!x. &0 <= phi x) /\
     wan_test (ball(c,rc)) theta /\ (!x. &0 <= theta x) /\
     (!kk. compact kk /\ kk SUBSET s
           ==> ?C d. &0 < d /\
                     !x v t. x IN kk /\ norm v <= &2 /\ abs t < d
                             ==> u(x + t % pastecart v (vec 0)) + u(x - t % pastecart v (vec 0)) -
                                 &2 * u x <= C * t pow 2) /\
     (\x. lift(Fb x)) measurable_on s /\
     (!kk. compact kk /\ kk SUBSET s ==> ?C. !x. x IN kk ==> abs(Fb x) <= C)
     ==> (\x. lift((phi x * theta x) * Fb x)) integrable_on s /\
         (\x. lift(sum(1..dimindex(:N)) (\a. sum(1..dimindex(:N))
                (\b. A x$a$b * wan_xder a u x * wan_xder b (\y. phi y * theta y) x))))
           integrable_on s /\
         &0 <= drop(integral s (\x. lift((phi x * theta x) * Fb x))) +
               drop(integral s (\x. lift(sum(1..dimindex(:N)) (\a. sum(1..dimindex(:N))
                      (\b. A x$a$b * wan_xder a u x * wan_xder b (\y. phi y * theta y) x)))))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `N:real^(N,1)finite_sum->bool` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "BAR")))
    STRIP_ASSUME_TAC) THEN
  MP_TAC(ASSUME `wan_test (s:real^(N,1)finite_sum->bool) phi`) THEN REWRITE_TAC[wan_test] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC)) THEN
  MP_TAC(ASSUME `wan_test (ball(c:real^(N,1)finite_sum,rc)) theta`) THEN REWRITE_TAC[wan_test] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `kt:real^(N,1)finite_sum->bool` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN
   `smooth_map_on (:real^(N,1)finite_sum) (\x. lift((phi:real^(N,1)finite_sum->real) x * theta x))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`(:real^(N,1)finite_sum)`; `\x. lift((phi:real^(N,1)finite_sum->real) x)`;
                   `\x. lift((theta:real^(N,1)finite_sum->real) x)`] SMOOTH_MAP_ON_LIFT_MUL) THEN
    ASM_REWRITE_TAC[OPEN_UNIV; LIFT_DROP];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x. ~(x IN kt) ==> (phi:real^(N,1)finite_sum->real) x * theta x = &0`
  ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_MUL_RZERO]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!x b. ~(x IN kt) ==> wan_xder b (\y. (phi:real^(N,1)finite_sum->real) y * theta y) x = &0`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[P2AW_XDER_D1] THEN MATCH_MP_TAC P2AW_SUPPORT_D1 THEN
    EXISTS_TAC `kt:real^(N,1)finite_sum->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`ball(c:real^(N,1)finite_sum,rc)`; `A:real^(N,1)finite_sum->real^N^N`;
                 `P:real^N^N`; `c0:real`; `u:real^(N,1)finite_sum->real`;
                 `Fb:real^(N,1)finite_sum->real`;
                 `\y. (phi:real^(N,1)finite_sum->real) y * theta y`] P2AW_NBP_FRAME) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REWRITE_TAC[OPEN_BALL];
      ASM_REWRITE_TAC[];
      ASM_MESON_TAC[SUBSET];
      REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
      EXISTS_TAC `s:real^(N,1)finite_sum->bool` THEN ASM_SIMP_TAC[];
      ASM_REWRITE_TAC[];
      UNDISCH_TAC `wan_loclip s (u:real^(N,1)finite_sum->real)` THEN
      REWRITE_TAC[wan_loclip] THEN ASM_MESON_TAC[SUBSET_TRANS];
      REWRITE_TAC[wan_test] THEN ASM_REWRITE_TAC[] THEN
      EXISTS_TAC `kt:real^(N,1)finite_sum->bool` THEN ASM_REWRITE_TAC[];
      GEN_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `kk:real^(N,1)finite_sum->bool` THEN STRIP_TAC THEN
      FIRST_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[SUBSET_TRANS];
      MATCH_MP_TAC MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
      EXISTS_TAC `s:real^(N,1)finite_sum->bool` THEN
      ASM_SIMP_TAC[LEBESGUE_MEASURABLE_OPEN; OPEN_BALL];
      X_GEN_TAC `kk:real^(N,1)finite_sum->bool` THEN STRIP_TAC THEN
      FIRST_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[SUBSET_TRANS];
      ALL_TAC] THEN
    EXISTS_TAC `N:real^(N,1)finite_sum->bool` THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `x:real^(N,1)finite_sum` THEN STRIP_TAC THEN
    SUBGOAL_THEN `&0 < (phi:real^(N,1)finite_sum->real) x` ASSUME_TAC THENL
     [ASM_CASES_TAC `(phi:real^(N,1)finite_sum->real) x = &0` THENL
       [UNDISCH_TAC `&0 < (phi:real^(N,1)finite_sum->real) x * theta x` THEN
        ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_LT_REFL];
        MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ ~(x = &0) ==> &0 < x`) THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    REMOVE_THEN "BAR" (MP_TAC o SPEC `x:real^(N,1)finite_sum`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `psi:real^(N,1)finite_sum->real`
      (X_CHOOSE_THEN `r1:real` STRIP_ASSUME_TAC)) THEN
    EXISTS_TAC `psi:real^(N,1)finite_sum->real` THEN
    EXISTS_TAC `min r1 (rc - dist(c:real^(N,1)finite_sum,x))` THEN
    SUBGOAL_THEN `dist(c:real^(N,1)finite_sum,x) < rc` ASSUME_TAC THENL
     [ASM_MESON_TAC[IN_BALL]; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      REWRITE_TAC[SUBSET; IN_BALL] THEN X_GEN_TAC `y:real^(N,1)finite_sum` THEN
      MP_TAC(ISPECL [`c:real^(N,1)finite_sum`; `x:real^(N,1)finite_sum`;
                     `y:real^(N,1)finite_sum`] DIST_TRIANGLE) THEN
      REAL_ARITH_TAC;
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
      EXISTS_TAC `ball(x:real^(N,1)finite_sum,r1)` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBSET; IN_BALL] THEN GEN_TAC THEN REAL_ARITH_TAC;
      REPEAT GEN_TAC THEN REWRITE_TAC[IN_BALL] THEN STRIP_TAC THEN
      FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_BALL] THEN ASM_REAL_ARITH_TAC;
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[]];
    STRIP_TAC] THEN
  MP_TAC(ISPECL [`\x. lift(((phi:real^(N,1)finite_sum->real) x * theta x) * Fb x)`;
                 `ball(c:real^(N,1)finite_sum,rc)`; `s:real^(N,1)finite_sum->bool`]
                P2AW_INTEGRAL_SUPERSET) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:real^(N,1)finite_sum` THEN DISCH_TAC THEN
    SUBGOAL_THEN `~((x:real^(N,1)finite_sum) IN kt)`
      (fun th -> ASM_SIMP_TAC[th; REAL_MUL_LZERO; LIFT_NUM]) THEN
    ASM SET_TAC[];
    STRIP_TAC] THEN
  MP_TAC(ISPECL [`\x. lift(sum(1..dimindex(:N)) (\a. sum(1..dimindex(:N))
                     (\b. (A:real^(N,1)finite_sum->real^N^N) x$a$b * wan_xder a u x *
                          wan_xder b (\y. (phi:real^(N,1)finite_sum->real) y * theta y) x)))`;
                 `ball(c:real^(N,1)finite_sum,rc)`; `s:real^(N,1)finite_sum->bool`]
                P2AW_INTEGRAL_SUPERSET) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:real^(N,1)finite_sum` THEN DISCH_TAC THEN
    SUBGOAL_THEN `~((x:real^(N,1)finite_sum) IN kt)`
      (fun th -> ASM_SIMP_TAC[th; REAL_MUL_RZERO; SUM_0; LIFT_NUM]) THEN
    ASM SET_TAC[];
    STRIP_TAC] THEN
  ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* The global matrix-form barrier principle P2AW_NBP_MATRIX on an open set s *)
(* where A is smooth, symmetric and positive definite.                       *)
(* ========================================================================= *)

let P2AW_NBP_MATRIX = prove
 (`!(s:real^(N,1)finite_sum->bool) (A:real^(N,1)finite_sum->real^N^N)
    (u:real^(N,1)finite_sum->real) Fb phi.
     open s /\
     (!y. y IN s ==> symmetric_matrix(A y) /\ !v. ~(v = vec 0) ==> &0 < v dot (A y ** v)) /\
     (!a b. 1 <= a /\ a <= dimindex(:N) /\ 1 <= b /\ b <= dimindex(:N)
            ==> smooth_map_on s (\x. lift(A x$a$b))) /\
     wan_loclip s u /\ wan_test s phi /\ (!x. &0 <= phi x) /\
     (!kk. compact kk /\ kk SUBSET s
           ==> ?C d. &0 < d /\
                     !x v t. x IN kk /\ norm v <= &2 /\ abs t < d
                             ==> u(x + t % pastecart v (vec 0)) + u(x - t % pastecart v (vec 0)) -
                                 &2 * u x <= C * t pow 2) /\
     (\x. lift(Fb x)) measurable_on s /\
     (!kk. compact kk /\ kk SUBSET s ==> ?C. !x. x IN kk ==> abs(Fb x) <= C) /\
     (?N. negligible N /\
          !x. x IN s /\ ~(x IN N) /\ &0 < phi x
              ==> ?psi r. &0 < r /\ ball(x,r) SUBSET s /\
                          smooth_map_on (ball(x,r)) (\y. lift(psi y)) /\
                          (!v t. norm v <= &2 /\ x + t % pastecart v (vec 0) IN ball(x,r) /\
                                 x - t % pastecart v (vec 0) IN ball(x,r)
                                 ==> u(x + t % pastecart v (vec 0)) <=
                                     psi(x + t % pastecart v (vec 0)) /\
                                     u(x - t % pastecart v (vec 0)) <=
                                     psi(x - t % pastecart v (vec 0))) /\
                          psi x = u x /\
                          sum(1..dimindex(:N))
                            (\a. wan_xder a (\w. sum(1..dimindex(:N))
                                                   (\b. A w$a$b * wan_xder b psi w)) x)
                          <= Fb x)
     ==> (\x. lift(phi x * Fb x)) integrable_on s /\
         (\x. lift(sum(1..dimindex(:N)) (\a. sum(1..dimindex(:N))
                (\b. A x$a$b * wan_xder a u x * wan_xder b phi x)))) integrable_on s /\
         &0 <= drop(integral s (\x. lift(phi x * Fb x))) +
               drop(integral s (\x. lift(sum(1..dimindex(:N)) (\a. sum(1..dimindex(:N))
                      (\b. A x$a$b * wan_xder a u x * wan_xder b phi x)))))`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> ASSUME_TAC th THEN STRIP_ASSUME_TAC th) THEN
  SUBGOAL_THEN `!y. y IN s ==> symmetric_matrix((A:real^(N,1)finite_sum->real^N^N) y)`
  ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ASSUME `wan_test (s:real^(N,1)finite_sum->bool) phi`) THEN REWRITE_TAC[wan_test] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `kp:real^(N,1)finite_sum->bool` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`s:real^(N,1)finite_sum->bool`; `A:real^(N,1)finite_sum->real^N^N`;
                 `kp:real^(N,1)finite_sum->bool`] P2AW_FRAME_COVER) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `J:num` (X_CHOOSE_THEN `cs:num->real^(N,1)finite_sum`
    (X_CHOOSE_THEN `rs:num->real` (X_CHOOSE_THEN `Ps:num->real^N^N`
    (X_CHOOSE_THEN `c0s:num->real` (CONJUNCTS_THEN2 (LABEL_TAC "FR") ASSUME_TAC)))))) THEN
  MP_TAC(ISPECL [`kp:real^(N,1)finite_sum->bool`; `cs:num->real^(N,1)finite_sum`;
                 `rs:num->real`; `J:num`] P2AW_SMOOTH_PARTITION) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    USE_THEN "FR" (MP_TAC o SPEC `j:num`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `theta:num->real^(N,1)finite_sum->real`
    (CONJUNCTS_THEN2 (LABEL_TAC "TH") (LABEL_TAC "ONE"))) THEN
  (* each piece *)
  SUBGOAL_THEN
   `!j. j IN 1..J
        ==> (\x. lift(((phi:real^(N,1)finite_sum->real) x * theta j x) * Fb x)) integrable_on s /\
            (\x. lift(sum(1..dimindex(:N)) (\a. sum(1..dimindex(:N))
               (\b. (A:real^(N,1)finite_sum->real^N^N) x$a$b * wan_xder a u x *
                    wan_xder b (\y. phi y * theta j y) x)))) integrable_on s /\
            &0 <= drop(integral s (\x. lift((phi x * theta j x) * Fb x))) +
                  drop(integral s (\x. lift(sum(1..dimindex(:N)) (\a. sum(1..dimindex(:N))
                     (\b. A x$a$b * wan_xder a u x * wan_xder b (\y. phi y * theta j y) x)))))`
  (LABEL_TAC "PC") THENL
   [X_GEN_TAC `j:num` THEN REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
    USE_THEN "FR" (MP_TAC o SPEC `j:num`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN STRIP_TAC THEN
    USE_THEN "TH" (MP_TAC o SPEC `j:num`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN STRIP_TAC THEN
    MATCH_MP_TAC(ISPECL [`s:real^(N,1)finite_sum->bool`; `A:real^(N,1)finite_sum->real^N^N`;
                         `(Ps:num->real^N^N) j`; `(c0s:num->real) j`;
                         `(cs:num->real^(N,1)finite_sum) j`; `(rs:num->real) j`;
                         `u:real^(N,1)finite_sum->real`; `Fb:real^(N,1)finite_sum->real`;
                         `phi:real^(N,1)finite_sum->real`;
                         `(theta:num->real^(N,1)finite_sum->real) j`] P2AW_NBP_PIECE) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the partition of the test *)
  SUBGOAL_THEN `!x. sum(1..J) (\j. (phi:real^(N,1)finite_sum->real) x * theta j x) = phi x`
  (LABEL_TAC "PU") THENL
   [X_GEN_TAC `x:real^(N,1)finite_sum` THEN REWRITE_TAC[SUM_LMUL] THEN
    ASM_CASES_TAC `(x:real^(N,1)finite_sum) IN kp` THENL
     [USE_THEN "ONE" (fun th -> ASM_SIMP_TAC[th; REAL_MUL_RID]);
      ASM_SIMP_TAC[REAL_MUL_LZERO]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!j. 1 <= j /\ j <= J
        ==> smooth_map_on (:real^(N,1)finite_sum)
              (\y. lift((phi:real^(N,1)finite_sum->real) y * theta j y))`
  (LABEL_TAC "SMJ") THENL
   [REPEAT STRIP_TAC THEN
    USE_THEN "TH" (MP_TAC o SPEC `j:num`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[wan_test] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`(:real^(N,1)finite_sum)`; `\x. lift((phi:real^(N,1)finite_sum->real) x)`;
                   `\x. lift((theta:num->real^(N,1)finite_sum->real) j x)`]
                  SMOOTH_MAP_ON_LIFT_MUL) THEN
    ASM_REWRITE_TAC[OPEN_UNIV; LIFT_DROP];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x b. wan_xder b (phi:real^(N,1)finite_sum->real) x =
          sum(1..J) (\j. wan_xder b (\y. phi y * theta j y) x)`
  (LABEL_TAC "DX") THENL
   [REPEAT GEN_TAC THEN
    SUBGOAL_THEN
     `wan_xder b (phi:real^(N,1)finite_sum->real) x =
      wan_xder b (\y. sum(1..J) (\j. phi y * theta j y)) x`
    SUBST1_TAC THENL
     [AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
      USE_THEN "PU" (fun th -> REWRITE_TAC[th]);
      ALL_TAC] THEN
    REWRITE_TAC[P2AW_XDER_D1] THEN
    MP_TAC(ISPECL [`\j y. (phi:real^(N,1)finite_sum->real) y * (theta:num->real^(N,1)finite_sum->real) j y`; `1..J`;
                   `pastecart (basis b:real^N) (vec 0:real^1)`; `x:real^(N,1)finite_sum`]
                  P2AW_D1_SUM) THEN
    REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN ANTS_TAC THENL
     [X_GEN_TAC `j:num` THEN STRIP_TAC THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
      EXISTS_TAC `(:real^(N,1)finite_sum)` THEN REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN
      USE_THEN "SMJ" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      DISCH_THEN ACCEPT_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. sum(1..dimindex(:N)) (\a. sum(1..dimindex(:N))
          (\b. (A:real^(N,1)finite_sum->real^N^N) x$a$b * wan_xder a u x * wan_xder b phi x)) =
        sum(1..J) (\j. sum(1..dimindex(:N)) (\a. sum(1..dimindex(:N))
          (\b. A x$a$b * wan_xder a u x * wan_xder b (\y. phi y * theta j y) x)))`
  (LABEL_TAC "BS") THENL
   [GEN_TAC THEN USE_THEN "DX" (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[GSYM SUM_LMUL] THEN
    ACCEPT_TAC(REWRITE_RULE[FINITE_NUMSEG]
     (ISPECL [`\a b j. (A:real^(N,1)finite_sum->real^N^N) x$a$b * wan_xder a u x *
                       wan_xder b (\y. (phi:real^(N,1)finite_sum->real) y *
                                       (theta:num->real^(N,1)finite_sum->real) j y) x`;
              `1..J`; `dimindex(:N)`] P2AW_SUM_SWAP3));
    ALL_TAC] THEN
  (* rewrite both integrands as finite sums of the pieces *)
  SUBGOAL_THEN
   `(\x. lift((phi:real^(N,1)finite_sum->real) x * Fb x)) =
    (\x. vsum(1..J) (\j. lift((phi x * theta j x) * Fb x)))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `x:real^(N,1)finite_sum` THEN
    SUBGOAL_THEN
     `(phi:real^(N,1)finite_sum->real) x * Fb x = sum(1..J) (\j. (phi x * theta j x) * Fb x)`
    SUBST1_TAC THENL
     [REWRITE_TAC[SUM_RMUL] THEN USE_THEN "PU" (fun th -> REWRITE_TAC[th]);
      GEN_REWRITE_TAC LAND_CONV [LIFT_SUM] THEN REWRITE_TAC[o_DEF]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\x. lift(sum(1..dimindex(:N)) (\a. sum(1..dimindex(:N))
          (\b. (A:real^(N,1)finite_sum->real^N^N) x$a$b * wan_xder a u x * wan_xder b phi x)))) =
    (\x. vsum(1..J) (\j. lift(sum(1..dimindex(:N)) (\a. sum(1..dimindex(:N))
          (\b. A x$a$b * wan_xder a u x * wan_xder b (\y. phi y * theta j y) x)))))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `x:real^(N,1)finite_sum` THEN
    USE_THEN "BS" (fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THEN
    GEN_REWRITE_TAC LAND_CONV [LIFT_SUM] THEN REWRITE_TAC[o_DEF];
    ALL_TAC] THEN
  (* integrability and the integrals of the sums *)
  SUBGOAL_THEN
   `(\x. vsum(1..J) (\j. lift(((phi:real^(N,1)finite_sum->real) x * theta j x) * Fb x)))
      integrable_on s /\
    integral s (\x. vsum(1..J) (\j. lift((phi x * theta j x) * Fb x))) =
    vsum(1..J) (\j. integral s (\x. lift((phi x * theta j x) * Fb x)))`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\j x. lift(((phi:real^(N,1)finite_sum->real) x *
                              (theta:num->real^(N,1)finite_sum->real) j x) * Fb x)`;
                   `s:real^(N,1)finite_sum->bool`; `1..J`] INTEGRAL_VSUM) THEN
    MP_TAC(ISPECL [`\j x. lift(((phi:real^(N,1)finite_sum->real) x *
                              (theta:num->real^(N,1)finite_sum->real) j x) * Fb x)`;
                   `s:real^(N,1)finite_sum->bool`; `1..J`] INTEGRABLE_VSUM) THEN
    REWRITE_TAC[FINITE_NUMSEG] THEN
    SUBGOAL_THEN
     `!j. j IN 1..J
          ==> (\x. lift(((phi:real^(N,1)finite_sum->real) x * theta j x) * Fb x)) integrable_on s`
    (fun th -> REWRITE_TAC[th]) THENL
     [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
      USE_THEN "PC" (MP_TAC o SPEC `j:num`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(ACCEPT_TAC o CONJUNCT1);
      ALL_TAC] THEN
    DISCH_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\x. vsum(1..J) (\j. lift(sum(1..dimindex(:N)) (\a. sum(1..dimindex(:N))
          (\b. (A:real^(N,1)finite_sum->real^N^N) x$a$b * wan_xder a u x *
               wan_xder b (\y. (phi:real^(N,1)finite_sum->real) y * theta j y) x)))))
      integrable_on s /\
    integral s (\x. vsum(1..J) (\j. lift(sum(1..dimindex(:N)) (\a. sum(1..dimindex(:N))
          (\b. A x$a$b * wan_xder a u x * wan_xder b (\y. phi y * theta j y) x))))) =
    vsum(1..J) (\j. integral s (\x. lift(sum(1..dimindex(:N)) (\a. sum(1..dimindex(:N))
          (\b. A x$a$b * wan_xder a u x * wan_xder b (\y. phi y * theta j y) x)))))`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\j x. lift(sum(1..dimindex(:N)) (\a. sum(1..dimindex(:N))
          (\b. (A:real^(N,1)finite_sum->real^N^N) x$a$b * wan_xder a u x *
               wan_xder b (\y. (phi:real^(N,1)finite_sum->real) y *
                                (theta:num->real^(N,1)finite_sum->real) j y) x)))`;
                   `s:real^(N,1)finite_sum->bool`; `1..J`] INTEGRAL_VSUM) THEN
    MP_TAC(ISPECL [`\j x. lift(sum(1..dimindex(:N)) (\a. sum(1..dimindex(:N))
          (\b. (A:real^(N,1)finite_sum->real^N^N) x$a$b * wan_xder a u x *
               wan_xder b (\y. (phi:real^(N,1)finite_sum->real) y *
                                (theta:num->real^(N,1)finite_sum->real) j y) x)))`;
                   `s:real^(N,1)finite_sum->bool`; `1..J`] INTEGRABLE_VSUM) THEN
    REWRITE_TAC[FINITE_NUMSEG] THEN
    SUBGOAL_THEN
     `!j. j IN 1..J
          ==> (\x. lift(sum(1..dimindex(:N)) (\a. sum(1..dimindex(:N))
                (\b. (A:real^(N,1)finite_sum->real^N^N) x$a$b * wan_xder a u x *
                     wan_xder b (\y. (phi:real^(N,1)finite_sum->real) y * theta j y) x))))
                integrable_on s`
    (fun th -> REWRITE_TAC[th]) THENL
     [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
      USE_THEN "PC" (MP_TAC o SPEC `j:num`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(ACCEPT_TAC o CONJUNCT1 o CONJUNCT2);
      ALL_TAC] THEN
    DISCH_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[DROP_VSUM; o_DEF] THEN
  REWRITE_TAC[GSYM SUM_ADD_NUMSEG] THEN MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN
  X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  USE_THEN "PC" (MP_TAC o SPEC `j:num`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[IN_NUMSEG]; SIMP_TAC[]]);;

