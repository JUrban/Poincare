(* ========================================================================= *)
(* Unit pc_p2b_slice (Part 2B, MT Prop 9.79): the uniform slice form         *)
(* P2B_PROP_9_79_SLICE_FIX (= P2_PROP_9_79_SLICE) and the uniform cap form   *)
(* P2B_PROP_9_79_CAP_FIX.                                                    *)
(*                                                                           *)
(* 6a <= R <= 6b from a <= sec <= b (frame computation);                     *)
(* the C-component case with delta depending on C, C', Kr only;              *)
(* the neck case (eps-neck to eps'-neck, eps < eps') and the round case;     *)
(* monotonicity of rfs_mclose in delta; SLICE_FIX from CAP_FIX.              *)
(* ========================================================================= *)

needs "src/pc_p2b_cap.ml";;

prioritize_real();;

type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Scalar curvature against sectional curvature bounds at a point: with an  *)
(* orthonormal frame f_i, R = sum over i <> j of sec(f_i,f_j).               *)
(* ------------------------------------------------------------------------- *)

let P2BS_FRAME_TERM_SECT = prove
 (`!U (G:real^N->real^N^N) y (M:real^N^N) i j.
     metric_field U G /\ y IN U /\ G y = transp M ** M /\ invertible M /\
     1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
     ==> (i = j
          ==> (matrix_inv M ** basis i) dot
              (G y ** lriemann G y (matrix_inv M ** basis i)
                                   (matrix_inv M ** basis j) (matrix_inv M ** basis j)) = &0) /\
         (~(i = j)
          ==> ~collinear {vec 0, matrix_inv M ** basis i, matrix_inv M ** basis j} /\
              (matrix_inv M ** basis i) dot
              (G y ** lriemann G y (matrix_inv M ** basis i)
                                   (matrix_inv M ** basis j) (matrix_inv M ** basis j)) =
              lsectional G y (matrix_inv M ** basis i) (matrix_inv M ** basis j))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `fi = matrix_inv(M:real^N^N) ** basis i` THEN
  ABBREV_TAC `fj = matrix_inv(M:real^N^N) ** basis j` THEN
  SUBGOAL_THEN `(fi:real^N) dot ((G:real^N->real^N^N) y ** fi) = &1 /\
                (fj:real^N) dot (G y ** fj) = &1 /\
                (fi:real^N) dot (G y ** fj) = (if (i:num) = j then &1 else &0)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["fi"; "fj"] THEN REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL [`(G:real^N->real^N^N) y`; `M:real^N^N`; `i:num`; `i:num`]
                    P2B_FRAME_ORTHO);
      MP_TAC(ISPECL [`(G:real^N->real^N^N) y`; `M:real^N^N`; `j:num`; `j:num`]
                    P2B_FRAME_ORTHO);
      MP_TAC(ISPECL [`(G:real^N->real^N^N) y`; `M:real^N^N`; `i:num`; `j:num`]
                    P2B_FRAME_ORTHO)] THEN
    ANTS_TAC THEN ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `(G:real^N->real^N^N) y = transp(M:real^N^N) ** M` THEN DISCH_THEN(K ALL_TAC) THEN
  CONJ_TAC THENL
   [DISCH_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
    SUBGOAL_THEN `(fi:real^N) = fj` SUBST_ALL_TAC THENL
     [MAP_EVERY EXPAND_TAC ["fi"; "fj"] THEN REFL_TAC; ALL_TAC] THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `fj:real^N`;
                   `fj:real^N`; `fj:real^N`] LRIEMANN_ANTISYM) THEN
    ASM_REWRITE_TAC[VECTOR_ARITH `(x:real^N) = --x <=> x = vec 0`] THEN
    SIMP_TAC[MATRIX_VECTOR_MUL_RZERO; DOT_RZERO];
    ALL_TAC] THEN
  DISCH_TAC THEN
  UNDISCH_TAC `(fi:real^N) dot ((G:real^N->real^N^N) y ** fj) =
               (if (i:num) = j then &1 else &0)` THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  CONJ_TAC THENL
   [REWRITE_TAC[COLLINEAR_LEMMA] THEN STRIP_TAC THENL
     [UNDISCH_TAC `(fi:real^N) dot ((G:real^N->real^N^N) y ** fi) = &1` THEN
      ASM_REWRITE_TAC[DOT_LZERO] THEN REAL_ARITH_TAC;
      UNDISCH_TAC `(fj:real^N) dot ((G:real^N->real^N^N) y ** fj) = &1` THEN
      ASM_REWRITE_TAC[DOT_LZERO] THEN REAL_ARITH_TAC;
      UNDISCH_TAC `(fi:real^N) dot ((G:real^N->real^N^N) y ** fj) = &0` THEN
      UNDISCH_TAC `(fj:real^N) dot ((G:real^N->real^N^N) y ** fj) = &1` THEN
      ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_RMUL; DOT_RMUL; DOT_LMUL] THEN
      UNDISCH_TAC `(fi:real^N) dot ((G:real^N->real^N^N) y ** fi) = &1` THEN
      ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_RMUL; DOT_RMUL; DOT_LMUL] THEN
      REWRITE_TAC[REAL_MUL_RID] THEN DISCH_TAC THEN DISCH_TAC THEN DISCH_TAC THEN
      UNDISCH_TAC `c * c = &1` THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
    REWRITE_TAC[lsectional] THEN ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC[REAL_DIV_1]]);;

let P2BS_DOUBLE_SUM_OFFDIAG = prove
 (`!n (t:num->num->real) a.
     (!i. 1 <= i /\ i <= n ==> t i i = &0)
     ==> ((!i j. 1 <= i /\ i <= n /\ 1 <= j /\ j <= n /\ ~(i = j) ==> a <= t i j)
          ==> &(n * (n - 1)) * a <= sum(1..n) (\j. sum(1..n) (\i. t i j))) /\
         ((!i j. 1 <= i /\ i <= n /\ 1 <= j /\ j <= n /\ ~(i = j) ==> t i j <= a)
          ==> sum(1..n) (\j. sum(1..n) (\i. t i j)) <= &(n * (n - 1)) * a)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `sum(1..n) (\j. sum(1..n) (\i. if i = j then &0 else a)) = &(n * (n - 1)) * a`
  (SUBST1_TAC o SYM) THENL
   [MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `sum(1..n) (\j. &(n - 1) * a)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `jj:num` THEN STRIP_TAC THEN
      REWRITE_TAC[] THEN
      SUBGOAL_THEN `(\i. if (i:num) = jj then &0 else a) =
                    (\i. a - (if (i:num) = jj then a else &0))`
      SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN COND_CASES_TAC THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      REWRITE_TAC[SUM_SUB_NUMSEG; SUM_CONST_NUMSEG; SUM_DELTA; IN_NUMSEG] THEN
      ASM_REWRITE_TAC[ADD_SUB] THEN
      SUBGOAL_THEN `1 <= n` MP_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      SIMP_TAC[GSYM REAL_OF_NUM_SUB] THEN REAL_ARITH_TAC;
      REWRITE_TAC[SUM_CONST_NUMSEG; ADD_SUB; GSYM REAL_OF_NUM_MUL] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  CONJ_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  ASM_CASES_TAC `i:num = j` THEN ASM_SIMP_TAC[REAL_LE_REFL]);;

let P2BS_LSCALAR_SECT = prove
 (`!U (G:real^N->real^N^N) y a.
     metric_field U G /\ y IN U
     ==> ((!u v. ~collinear {vec 0,u,v} ==> a <= lsectional G y u v)
          ==> &(dimindex(:N) * (dimindex(:N) - 1)) * a <= lscalar G y) /\
         ((!u v. ~collinear {vec 0,u,v} ==> lsectional G y u v <= a)
          ==> lscalar G y <= &(dimindex(:N) * (dimindex(:N) - 1)) * a)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`] LRG_FRAME) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `M:real^N^N` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `M:real^N^N`]
                P2B_LSCALAR_FRAME) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  ABBREV_TAC `Tm = \i j. (matrix_inv(M:real^N^N) ** basis i) dot
                         ((G:real^N->real^N^N) y ** lriemann G y (matrix_inv M ** basis i)
                              (matrix_inv M ** basis j) (matrix_inv M ** basis j))` THEN
  SUBGOAL_THEN
   `sum(1..dimindex(:N))
      (\j. lricci (G:real^N->real^N^N) y (matrix_inv(M:real^N^N) ** basis j)
                  (matrix_inv M ** basis j)) =
    sum(1..dimindex(:N)) (\j. sum(1..dimindex(:N)) (\i. (Tm:num->num->real) i j))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN EXPAND_TAC "Tm" THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC P2B_LRICCI_FRAME THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
          ==> (i = j ==> (Tm:num->num->real) i j = &0) /\
              (~(i = j)
               ==> ~collinear {vec 0, matrix_inv(M:real^N^N) ** basis i,
                               matrix_inv M ** basis j} /\
                   Tm i j = lsectional (G:real^N->real^N^N) y (matrix_inv M ** basis i)
                                       (matrix_inv M ** basis j))`
  (LABEL_TAC "term") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN EXPAND_TAC "Tm" THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC P2BS_FRAME_TERM_SECT THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`dimindex(:N)`; `Tm:num->num->real`; `a:real`] P2BS_DOUBLE_SUM_OFFDIAG) THEN
  ANTS_TAC THENL
   [X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    USE_THEN "term" (MP_TAC o SPECL [`i:num`; `i:num`]) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THEN CONJ_TAC THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  REPEAT STRIP_TAC THEN USE_THEN "term" (MP_TAC o SPECL [`i:num`; `j:num`]) THEN
  (ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let P2BS_MFD_SCALAR_SECT = prove
 (`!top atlas (g:A->real^3^3) x a.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\ x IN topspace top
     ==> ((!u v. ~collinear {vec 0,u,v} ==> a <= mfd_sectional atlas g x u v)
          ==> &6 * a <= mfd_scalar atlas g x) /\
         ((!u v. ~collinear {vec 0,u,v} ==> mfd_sectional atlas g x u v <= a)
          ==> mfd_scalar atlas g x <= &6 * a)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[mfd_scalar; mfd_sectional] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)))
                        (FST(chart_at atlas x))`;
                 `metric_local atlas (chart_at atlas (x:A)) (g:A->real^3^3)`;
                 `SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)) x`;
                 `a:real`] P2BS_LSCALAR_SECT) THEN
  REWRITE_TAC[DIMINDEX_3] THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
   [UNDISCH_TAC `riemannian_metric atlas (g:A->real^3^3)` THEN
    REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[FUN_IN_IMAGE]]);;

(* ========================================================================= *)
(* The C-component case, uniform.  The sectional bound gives                 *)
(* R >= 6 d6 > 6 Rm / C, so m = Rn / R0 lies in [6/C, 1]; alpha depends on C *)
(* only (P2BS_CCOMP_ALPHA); the margins of the conclusion use d = C and      *)
(* E = 3C/2 < 2C <= C' (P2BS_CCOMP_ARITH); K0 is Kr.                         *)
(* ========================================================================= *)

let P2BS_CCOMP_ALPHA = prove
 (`!C. &1 < C
       ==> ?alpha. &0 < alpha /\ &4 * C * alpha <= &1 /\
                   !m. &6 / C <= m /\ m <= &1
                       ==> &3 * alpha <= m /\
                           alpha * (&1 + &3 * (&3 / &2 * C) pow 2 * m pow 2) <=
                           ((&3 / &2 * C) pow 2 - C pow 2) * m pow 3 /\
                           alpha * (&3 + &2 * (&3 / &2 * C) * m) <=
                           (&3 / &2 * C - C) * m pow 2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < C /\ &0 < &6 / C` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `E = &3 / &2 * C` THEN ABBREV_TAC `m0 = &6 / C` THEN
  SUBGOAL_THEN `&0 < E pow 2 - C pow 2 /\ &0 < E - C /\ &0 <= E` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "E" THEN
    REWRITE_TAC[REAL_ARITH `(&3 / &2 * C) pow 2 - C pow 2 = &5 / &4 * C pow 2`] THEN
    ASM_SIMP_TAC[REAL_LT_MUL; REAL_POW_LT; REAL_ARITH `&0 < &5 / &4`] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPEC `[&3, m0; &1 + &3 * E pow 2, (E pow 2 - C pow 2) * m0 pow 3;
                 &3 + &2 * E, (E - C) * m0 pow 2; &4 * C, &1]` P2BC_EXISTS_SMALL) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[MEM; PAIR_EQ] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[REAL_LT_MUL; REAL_POW_LT; REAL_LE_POW_2;
                 REAL_ARITH `&0 <= x ==> &0 < &1 + &3 * x`;
                 REAL_ARITH `&0 <= x ==> &0 < &3 + &2 * x`] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `alpha:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "AL"))) THEN
  EXISTS_TAC `alpha:real` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `alpha * &3 <= m0 /\
                alpha * (&1 + &3 * E pow 2) <= (E pow 2 - C pow 2) * m0 pow 3 /\
                alpha * (&3 + &2 * E) <= (E - C) * m0 pow 2 /\ alpha * (&4 * C) <= &1`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN USE_THEN "AL" MATCH_MP_TAC THEN REWRITE_TAC[MEM; PAIR_EQ];
    ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `m:real` THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < m` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `m pow 2 <= &1 /\ m0 pow 2 <= m pow 2 /\ m0 pow 3 <= m pow 3`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_1_LE THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `alpha * (&1 + &3 * E pow 2)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC(REAL_ARITH `x * y <= x * &1 ==> &1 + &3 * x * y <= &1 + &3 * x`) THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2];
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(E pow 2 - C pow 2) * m0 pow 3` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC];
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `alpha * (&3 + &2 * E)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC(REAL_ARITH `x * y <= x * &1 ==> &3 + &2 * x * y <= &3 + &2 * x`) THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(E - C) * m0 pow 2` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC]]);;

let P2BS_CCOMP_ARITH = prove
 (`!C C' R0 Rn Rm D d6 dl alpha a.
     &1 < C /\ &2 * C <= C' /\ &0 < R0 /\ &0 < Rn /\ R0 <= Rm /\ &6 * Rm <= C * Rn /\
     &0 <= D /\ D pow 2 * Rn < C pow 2 /\ &1 < C pow 2 * Rm * D pow 2 /\
     inv C * Rm < d6 /\ &0 <= dl /\ dl <= &1 / &4 /\ &0 < alpha /\ &4 * C * alpha <= &1 /\
     a = alpha * R0
     ==> inv C' * (Rm + a) < d6 - a /\
         D pow 2 * (dl * Rn + &2 * a) < C' pow 2 - D pow 2 * Rn /\
         C' pow 2 * D pow 2 * (a + dl * Rm) < C' pow 2 * Rm * D pow 2 - &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < C /\ &0 < C' /\ &0 < inv C /\ &0 < inv C' /\
                inv C' <= inv C / &2 /\ inv C' <= &1 / &2 /\ alpha <= inv C / &4 /\
                alpha * C <= &1 / &4 /\ inv C < &1`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < C /\ &0 < C'` STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_INV_EQ] THEN
    SUBGOAL_THEN `inv C' <= inv(&2 * C)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `inv(&2 * C) = inv C / &2` (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))
    THENL [REWRITE_TAC[REAL_INV_MUL] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `inv C < &1` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_INV_LT_1 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      ASM_REAL_ARITH_TAC;
      SUBGOAL_THEN `alpha = (&4 * C * alpha) * inv C / &4` SUBST1_TAC THENL
       [UNDISCH_TAC `&0 < C` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= y /\ x * y <= &1 * y ==> x * y / &4 <= y / &4`) THEN
      CONJ_TAC THENL [ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE]; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE];
      ASM_REAL_ARITH_TAC;
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `a <= inv C * Rm / &4 /\ &24 * a <= Rn /\ &0 <= a /\ a <= Rm / &4`
  STRIP_ASSUME_TAC THENL
   [SUBST1_TAC(ASSUME `a = alpha * R0`) THEN
    SUBGOAL_THEN `alpha * R0 <= alpha * Rm` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `alpha * Rm <= (inv C / &4) * Rm` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&6 * (alpha * R0) <= alpha * (C * Rn)` ASSUME_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `alpha * (&6 * R0) <= alpha * (C * Rn)
                               ==> &6 * (alpha * R0) <= alpha * (C * Rn)`) THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(alpha * C) * Rn <= (&1 / &4) * Rn` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= alpha * R0 /\ inv C * Rm <= Rm` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC(REAL_ARITH `inv C * Rm <= &1 * Rm ==> inv C * Rm <= Rm`) THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&4 * C pow 2 <= C' pow 2` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_ARITH `&4 * C pow 2 = (&2 * C) pow 2`] THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN `inv C' * Rm <= (inv C / &2) * Rm /\ inv C' * a <= (&1 / &2) * a`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    SUBGOAL_THEN `&0 <= D pow 2 * Rn /\ dl * (D pow 2 * Rn) <= (&1 / &4) * (D pow 2 * Rn) /\
                  D pow 2 * (&24 * a) <= D pow 2 * Rn`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2]];
      ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    SUBGOAL_THEN `&0 <= D pow 2 * Rm /\ &0 <= C' pow 2 * D pow 2` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(&4 * C pow 2) * (D pow 2 * Rm) <= C' pow 2 * (D pow 2 * Rm) /\
                  (C' pow 2 * D pow 2) * (a + dl * Rm) <= (C' pow 2 * D pow 2) * (Rm / &2)`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
        SUBGOAL_THEN `dl * Rm <= (&1 / &4) * Rm` MP_TAC THENL
         [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]];
      ALL_TAC] THEN
    ASM_REAL_ARITH_TAC]);;

let P2BS_CCOMP_UNIF = prove
 (`P2B_REQ_LRG_DERIV_STATEMENT
   ==> !C C' Kr. &1 < C /\ &2 * C <= C'
         ==> ?delta. &0 < delta /\
               !top atlas (g:A->real^3^3) x U top' atlas' (g':B->real^3^3) psi psi'.
                  smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
                  rfs_c_component (top,atlas) g C U /\ x IN U /\
                  (!y l. y IN U /\ l <= 2
                         ==> lrm_deriv_norm2 l
                               (metric_local atlas (chart_at atlas y)
                                  (\z. mfd_scalar atlas g x %% g z))
                               (SND(chart_at atlas y) y) <= Kr) /\
                  smooth_manifold_atlas top' atlas' /\ riemannian_metric atlas' g' /\
                  mfd_diffeo top atlas U top' atlas' (IMAGE psi U) psi psi' /\
                  IMAGE psi U IN connected_components_of top' /\
                  rfs_mclose (rfs_kreg delta) delta atlas U
                    (\y. mfd_scalar atlas g x %% g y)
                    (\y. mfd_scalar atlas g x %% mfd_pullback_metric atlas atlas' psi g' y)
                  ==> rfs_c_component (top',atlas') g' C' (IMAGE psi U)`,
  DISCH_THEN(LABEL_TAC "LRGD" o MATCH_MP P2B9S_LRG_D) THEN
  MAP_EVERY X_GEN_TAC [`C:real`; `C':real`; `Kr:real`] THEN STRIP_TAC THEN
  MP_TAC(SPEC `C:real` P2BS_CCOMP_ALPHA) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `alpha:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "AM")))) THEN
  USE_THEN "LRGD" (fun th -> MP_TAC(MATCH_MP (SPECL [`Kr:real`; `alpha:real`] th)
                                            (ASSUME `&0 < alpha`))) THEN
  DISCH_THEN(X_CHOOSE_THEN `eta:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "Dform"))) THEN
  EXISTS_TAC `min (&1 / &4) eta` THEN
  ABBREV_TAC `delta = min (&1 / &4) eta` THEN
  SUBGOAL_THEN `&0 < delta /\ delta <= &1 / &4 /\ delta <= eta` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "delta" THEN REWRITE_TAC[REAL_LT_MIN; REAL_MIN_LE; REAL_LE_REFL] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                       `g:A->real^3^3`; `x:A`; `U:A->bool`;
                       `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                       `g':B->real^3^3`; `psi:A->B`; `psi':B->A`] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`C:real`; `top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `x:A`; `U:A->bool`] P2B9S_CCOMP_SOURCE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `Rn:real` (X_CHOOSE_THEN `Rm:real` (X_CHOOSE_THEN `D:real`
    (X_CHOOSE_THEN `d6:real` (X_CHOOSE_THEN `d9:real` (X_CHOOSE_THEN `d10:real`
      (X_CHOOSE_THEN `K0:real` (X_CHOOSE_THEN `y0:A` (X_CHOOSE_THEN `y1:A`
        STRIP_ASSUME_TAC))))))))) THEN
  SUBGOAL_THEN `U IN connected_components_of (top:A topology) /\ compact_in top U /\
                (mfd_diffeomorphic (subtopology top U)
                   (restrict_atlas (atlas:((A->bool)#(A->real^3))->bool) U)
                   (subtopology euclidean (sphere(vec 0:real^4,&1))) sphere3_atlas \/
                 rfs_has_twisted (subtopology top U) (restrict_atlas atlas U))`
  (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "type"))) THENL
   [UNDISCH_TAC `rfs_c_component (top,atlas) (g:A->real^3^3) C U` THEN
    REWRITE_TAC[rfs_c_component] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y0:A) IN topspace top` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `U:A->bool`] CONNECTED_COMPONENTS_OF_SUBSET) THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(y0:A) IN U` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < C /\ &6 * Rm <= C * Rn` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < C` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&6 * d6 <= mfd_scalar atlas (g:A->real^3^3) y0` MP_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                     `g:A->real^3^3`; `y0:A`; `d6:real`] P2BS_MFD_SCALAR_SECT) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN
      REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `d6:real`)) (concl th))) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `C * (inv C * Rm) = Rm /\ C * (inv C * Rm) < C * d6 /\
                  C * (&6 * d6) <= C * Rn`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THENL
       [UNDISCH_TAC `&0 < C` THEN CONV_TAC REAL_FIELD;
        MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `R0 = mfd_scalar atlas (g:A->real^3^3) x` THEN
  SUBGOAL_THEN `&0 < R0` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `m = Rn / R0` THEN
  SUBGOAL_THEN `&0 < m /\ m * R0 = Rn` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "m" THEN ASM_SIMP_TAC[REAL_LT_DIV; REAL_DIV_RMUL; REAL_LT_IMP_NZ];
    ALL_TAC] THEN
  SUBGOAL_THEN `m <= &1 /\ &6 / C <= m` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [SUBGOAL_THEN `m * R0 <= &1 * R0` MP_TAC THENL
       [ASM_REAL_ARITH_TAC; ASM_SIMP_TAC[REAL_LE_RMUL_EQ]];
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
      SUBGOAL_THEN `&6 * R0 <= (m * C) * R0` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `C * Rn` THEN CONJ_TAC THENL
         [ASM_REAL_ARITH_TAC;
          UNDISCH_TAC `m * R0 = Rn` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN REAL_ARITH_TAC];
        ASM_SIMP_TAC[REAL_LE_RMUL_EQ]]];
    ALL_TAC] THEN
  USE_THEN "AM" (fun th -> MP_TAC(MATCH_MP (SPEC `m:real` th)
    (CONJ (ASSUME `&6 / C <= m`) (ASSUME `m <= &1`)))) THEN STRIP_TAC THEN
  MP_TAC(SPECL [`C:real`; `C':real`; `R0:real`; `Rn:real`; `Rm:real`; `D:real`; `d6:real`;
                `delta:real`; `alpha:real`; `alpha * R0`] P2BS_CCOMP_ARITH) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN
   `!y. y IN U
        ==> rfa_rmd2 0 atlas (\z. R0 %% (g:A->real^3^3) z) y <= Kr /\
            rfa_rmd2 1 atlas (\z. R0 %% g z) y <= Kr /\
            rfa_rmd2 2 atlas (\z. R0 %% g z) y <= Kr`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[rfa_rmd2] THEN
    FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `Kr:real`)) (concl th))) THEN
    ASM_REWRITE_TAC[ARITH];
    ALL_TAC] THEN
  UNDISCH_TAC `rfs_mclose (rfs_kreg delta) delta atlas U (\y. R0 %% (g:A->real^3^3) y)
                 (\y. R0 %% mfd_pullback_metric atlas atlas' (psi:A->B) (g':B->real^3^3) y)` THEN
  REWRITE_TAC[rfs_mclose] THEN DISCH_THEN(X_CHOOSE_THEN `d2:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!y. y IN U
        ==> abs(mfd_scalar atlas' (g':B->real^3^3) ((psi:A->B) y) -
                mfd_scalar atlas (g:A->real^3^3) y) <= alpha * R0 /\
            (!u v. ~collinear {vec 0,u,v}
                   ==> abs(mfd_sectional atlas (mfd_pullback_metric atlas atlas' psi g') y u v -
                           mfd_sectional atlas g y u v) <= alpha * R0) /\
            abs(rfs_scalar_grad2 atlas' g' (psi y) - rfs_scalar_grad2 atlas g y) <=
            alpha * R0 pow 3 /\
            abs(rfs_scalar_lap atlas' g' (psi y) - rfs_scalar_lap atlas g y) <= alpha * R0 pow 2 /\
            abs(rfs_ric_norm2 atlas' g' (psi y) - rfs_ric_norm2 atlas g y) <= alpha * R0 pow 2 /\
            (!v. v dot (mfd_pullback_metric atlas atlas' psi g' y ** v) <=
                 (&1 + delta) * (v dot (g y ** v))) /\
            (!v. (&1 - delta) * (v dot (g y ** v)) <=
                 v dot (mfd_pullback_metric atlas atlas' psi g' y ** v))`
  (LABEL_TAC "PT") THENL
   [X_GEN_TAC `y:A` THEN DISCH_TAC THEN MATCH_MP_TAC P2B9S_CCOMP_TARGET_POINT THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `top':B topology`; `U:A->bool`;
                          `IMAGE (psi:A->B) U`; `psi':B->A`; `Kr:real`; `eta:real`; `d2:real`] THEN
    ASM_SIMP_TAC[] THEN USE_THEN "Dform" ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `alpha * R0 <= Rn / &3 /\ &0 <= alpha * R0` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `m * R0 = Rn` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      UNDISCH_TAC `&3 * alpha <= m` THEN UNDISCH_TAC `&0 < R0` THEN
      SPEC_TAC(`R0:real`,`r:real`) THEN GEN_TAC THEN REPEAT DISCH_TAC THEN
      MATCH_MP_TAC(REAL_ARITH `&3 * (alpha * r) <= m * r ==> alpha * r <= (m * r) / &3`) THEN
      REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE];
      ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`mfd_scalar atlas (g:A->real^3^3)`; `mfd_scalar atlas' (g':B->real^3^3)`;
                 `psi:A->B`; `U:A->bool`; `Rn:real`; `Rm:real`; `alpha * R0`;
                 `y0:A`; `y1:A`] P2B9S_RANGE_TRANSFER) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[] THEN REPEAT STRIP_TAC THEN USE_THEN "PT" (MP_TAC o SPEC `y:A`) THEN
    ASM_SIMP_TAC[];
    STRIP_TAC] THEN
  SUBGOAL_THEN
   `!a b. a IN U /\ b IN U
          ==> mfd_dist (top',atlas') (g':B->real^3^3) ((psi:A->B) a) (psi b) <=
              sqrt(&1 + delta) * mfd_dist (top,atlas) (g:A->real^3^3) a b /\
              sqrt(&1 - delta) * mfd_dist (top,atlas) g a b <=
              mfd_dist (top',atlas') g' (psi a) (psi b)`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC P2B9S_CCOMP_DIST THEN
    MAP_EVERY EXISTS_TAC [`U:A->bool`; `psi':B->A`] THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THEN REPEAT STRIP_TAC THEN USE_THEN "PT" (MP_TAC o SPEC `y:A`) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`mfd_dist (top,atlas) (g:A->real^3^3)`;
                 `mfd_dist (top',atlas') (g':B->real^3^3)`; `psi:A->B`; `U:A->bool`; `D:real`;
                 `sqrt(&1 + delta)`; `sqrt(&1 - delta)`] P2B9S_DIST_SUP_TRANSFER) THEN
  SUBGOAL_THEN `~(U:A->bool = {}) /\ &0 <= &1 + delta /\ &0 < &1 - delta`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    CONJ_TAC THENL [EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LE; SQRT_POS_LT];
    STRIP_TAC] THEN
  SUBGOAL_THEN `!y u v. y IN U /\ ~collinear {vec 0,u,v}
                       ==> d6 - alpha * R0 <=
                           mfd_sectional atlas' (g':B->real^3^3) ((psi:A->B) y) u v`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                   `U:A->bool`; `IMAGE (psi:A->B) U`; `psi:A->B`; `psi':B->A`;
                   `g':B->real^3^3`; `y:A`] P2B9S_PB_SECTIONAL) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL [`u:real^3`; `v:real^3`] o CONJUNCT2) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `u1:real^3` (X_CHOOSE_THEN `v1:real^3` STRIP_ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[] THEN
    USE_THEN "PT" (fun th -> MP_TAC(SPECL [`u1:real^3`; `v1:real^3`]
      (CONJUNCT1(CONJUNCT2(MATCH_MP th (ASSUME `(y:A) IN U`)))))) THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`y:A`; `u1:real^3`; `v1:real^3`] o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `d6:real`)) (concl th) &&
      not(can (find_term ((=) `alpha:real`)) (concl th)))) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < inv C /\ &0 < inv C' /\ &0 < C' /\ &0 < Rm /\ D pow 2 * Rn < C' pow 2`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < C'` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_INV] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `C pow 2` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < d6 - alpha * R0` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `inv C' * (Rm + alpha * R0)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[rfs_c_component; rfs_inf_gt; rfs_sup_lt] THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC IMAGE_COMPACT_IN THEN EXISTS_TAC `subtopology top (U:A->bool)` THEN
    ASM_REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY; SUBSET_REFL] THEN
    FIRST_ASSUM(ACCEPT_TAC o CONJUNCT1 o MATCH_MP MFD_DIFFEO_MAPS);
    MATCH_MP_TAC P2B9S_CCOMP_TYPE THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                          `U:A->bool`; `psi:A->B`; `psi':B->A`] THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "type" ACCEPT_TAC;
    REWRITE_TAC[IN_IMAGE] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `d6 - alpha * R0` THEN ASM_SIMP_TAC[];
    EXISTS_TAC `d6 - alpha * R0` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `inv C' * (Rm + alpha * R0)` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      REWRITE_TAC[IN_ELIM_THM; LEFT_IMP_EXISTS_THM; IN_IMAGE] THEN
      REPEAT STRIP_TAC THEN ASM_SIMP_TAC[]];
    MATCH_MP_TAC P2B9S_DIAM_LOWER THEN
    MAP_EVERY EXISTS_TAC [`D:real`; `Rm:real`; `delta:real`; `alpha * R0`] THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC P2B9S_DIAM_UPPER THEN
    MAP_EVERY EXISTS_TAC [`D:real`; `Rn:real`; `delta:real`; `alpha * R0`] THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    SUBGOAL_THEN `&0 <= sqrt(&1 - delta) * D` ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_MUL; SQRT_POS_LE; REAL_LT_IMP_LE]; ALL_TAC] THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN TRY ASM_REAL_ARITH_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt(&1 - delta) * D` THEN
    ASM_REWRITE_TAC[];
    EXISTS_TAC `&3 / &2 * C` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[IN_ELIM_THM; LEFT_IMP_EXISTS_THM; IN_IMAGE] THEN
    X_GEN_TAC `w:real` THEN X_GEN_TAC `z:B` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `y:A` STRIP_ASSUME_TAC) SUBST1_TAC) THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    USE_THEN "PT" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th (ASSUME `(y:A) IN U`))) THEN
    SUBGOAL_THEN `(y:A) IN topspace top /\ (psi:A->B) y IN topspace top'`
    STRIP_ASSUME_TAC THENL
     [FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [mfd_diffeo] o check (fun th ->
        can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_diffeo")) (concl th) &&
        not (is_forall (concl th)))) THEN
      CONJ_TAC THENL
       [MP_TAC(MATCH_MP OPEN_IN_SUBSET (ASSUME `open_in top (U:A->bool)`));
        MP_TAC(MATCH_MP OPEN_IN_SUBSET (ASSUME `open_in top' (IMAGE (psi:A->B) U)`))] THEN
      REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[FUN_IN_IMAGE];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < mfd_scalar atlas (g:A->real^3^3) y /\ m * R0 <= mfd_scalar atlas g y`
    STRIP_ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `y:A` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `Rm:real`)) (concl th) &&
        not(can (find_term ((=) `alpha:real`)) (concl th)))) THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(SPECL [`mfd_scalar atlas (g:A->real^3^3) y`;
                  `rfs_scalar_grad2 atlas (g:A->real^3^3) y`; `C:real`]
                 P2B9S_GRAD_RATIO_IMP) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN CONJ_TAC THENL
       [MATCH_MP_TAC P2B9S_GRAD2_POS THEN EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `d9:real` THEN
        ASM_SIMP_TAC[REAL_LT_IMP_LE]];
      DISCH_TAC] THEN
    MP_TAC(SPECL [`m:real`; `R0:real`; `C:real`; `&3 / &2 * C`;
                  `mfd_scalar atlas (g:A->real^3^3) y`;
                  `mfd_scalar atlas' (g':B->real^3^3) ((psi:A->B) y)`;
                  `rfs_scalar_grad2 atlas (g:A->real^3^3) y`;
                  `rfs_scalar_grad2 atlas' (g':B->real^3^3) ((psi:A->B) y)`; `alpha:real`]
                 P2B9S_MARGIN_GRAD_POLY) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC;
      STRIP_TAC] THEN
    MATCH_MP_TAC P2B9S_GRAD_RATIO_BACK THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC P2B9S_GRAD2_POS THEN EXISTS_TAC `top':B topology` THEN ASM_REWRITE_TAC[];
      ASM_REAL_ARITH_TAC];
    EXISTS_TAC `&3 / &2 * C` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[IN_ELIM_THM; LEFT_IMP_EXISTS_THM; IN_IMAGE] THEN
    X_GEN_TAC `w:real` THEN X_GEN_TAC `z:B` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `y:A` STRIP_ASSUME_TAC) SUBST1_TAC) THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    USE_THEN "PT" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th (ASSUME `(y:A) IN U`))) THEN
    SUBGOAL_THEN `&0 < mfd_scalar atlas (g:A->real^3^3) y /\ m * R0 <= mfd_scalar atlas g y`
    STRIP_ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `y:A` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `Rm:real`)) (concl th) &&
        not(can (find_term ((=) `alpha:real`)) (concl th)))) THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(SPECL [`mfd_scalar atlas (g:A->real^3^3) y`;
                  `rfs_scalar_lap atlas (g:A->real^3^3) y + &2 * rfs_ric_norm2 atlas g y`;
                  `C:real`] P2B9S_LAP_RATIO_IMP) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `d10:real` THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE];
      DISCH_TAC] THEN
    MP_TAC(SPECL [`m:real`; `R0:real`; `C:real`; `&3 / &2 * C`;
                  `mfd_scalar atlas (g:A->real^3^3) y`;
                  `mfd_scalar atlas' (g':B->real^3^3) ((psi:A->B) y)`;
                  `rfs_scalar_lap atlas (g:A->real^3^3) y + &2 * rfs_ric_norm2 atlas g y`;
                  `rfs_scalar_lap atlas' (g':B->real^3^3) ((psi:A->B) y) +
                   &2 * rfs_ric_norm2 atlas' g' (psi y)`; `alpha:real`]
                 P2B9S_MARGIN_LAP_POLY) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC;
      STRIP_TAC] THEN
    MATCH_MP_TAC P2B9S_LAP_RATIO_BACK THEN ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* The neck case (an eps-neck is an eps'-neck with closeness eps^2 on the    *)
(* smaller domain, P2BS_NECK_SHRINK; P2B9_SNECK_CORE at eps' with the        *)
(* uniform centre bound from P2B_REQ_LRG_RM_NEAR_STATEMENT) and the round    *)
(* case (R(x)/q <= 8 from the sectional curvatures, so the rescaling factor  *)
(* is bounded by 9^k).                                                       *)
(* ========================================================================= *)

let P2BS_NECK_SHRINK = prove
 (`!top atlas (g:A->real^3^3) dl eps x (e:real^3->A).
     &0 < dl /\ dl <= eps /\ riemannian_metric atlas g /\
     rfs_neck (top,atlas) g dl x e
     ==> rfs_neck (top,atlas) g eps x e /\
         IMAGE e (rfs_neck_dom eps) SUBSET IMAGE e (rfs_neck_dom dl) /\
         open_in top (IMAGE e (rfs_neck_dom eps)) /\
         (!y. y IN rfs_neck_dom eps
              ==> lck_dist2 (rfs_kreg eps) (cylinder_flow (&0))
                    (\z. mfd_scalar atlas g x %% rfs_pullback atlas e g z) y <= dl pow 2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `rfs_neck_dom eps SUBSET rfs_neck_dom dl` ASSUME_TAC THENL
   [MATCH_MP_TAC APX_NECK_DOM_MONO THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC APX_NECK_MONO_GEN THEN EXISTS_TAC `dl:real` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[];
    UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) dl x e` THEN
    REWRITE_TAC[rfs_neck] THEN STRIP_TAC THEN
    MATCH_MP_TAC MFD_PARAM_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `rfs_neck_dom dl`] THEN
    ASM_REWRITE_TAC[rfs_neck_dom; OPEN_ANNULUS] THEN
    ASM_REWRITE_TAC[GSYM rfs_neck_dom];
    ALL_TAC] THEN
  UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) dl x e` THEN
  REWRITE_TAC[rfs_neck; rfs_close_on] THEN STRIP_TAC THEN
  X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `lck_dist2 (rfs_kreg dl) (cylinder_flow (&0))
      (\y. mfd_scalar atlas (g:A->real^3^3) x %% rfs_pullback atlas (e:real^3->A) g y) y` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LCK_DIST_MONO THEN EXISTS_TAC `rfs_neck_dom dl` THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[APX_NECK_CYL_FIELD];
      MATCH_MP_TAC RFB_METRIC_FIELD_CMUL THEN ASM_REWRITE_TAC[ETA_AX] THEN
      MATCH_MP_TAC APX_RFS_PULLBACK_FIELD THEN
      EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `(y:real^3) IN rfs_neck_dom eps` THEN
      UNDISCH_TAC `rfs_neck_dom eps SUBSET rfs_neck_dom dl` THEN SET_TAC[];
      MATCH_MP_TAC APX_KREG_MONO THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `d:real` THEN CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `(y:real^3) IN rfs_neck_dom eps` THEN
    UNDISCH_TAC `rfs_neck_dom eps SUBSET rfs_neck_dom dl` THEN SET_TAC[];
    ASM_SIMP_TAC[REAL_LT_IMP_LE]]);;

let P2BS_MCLOSE_SUBSET = prove
 (`!k eps (atlas:((A->bool)#(A->real^N))->bool) W V g0 g.
     rfs_mclose k eps atlas W g0 g /\ V SUBSET W ==> rfs_mclose k eps atlas V g0 g`,
  REWRITE_TAC[rfs_mclose] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) ASSUME_TAC) THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]);;

let P2BS_SNECK_CENTRE_UNIFORM = prove
 (`P2B_REQ_LRG_RM_NEAR_STATEMENT
   ==> ?K0. !top atlas (g:A->real^3^3) eps x e.
              riemannian_metric atlas g /\ rfs_neck (top,atlas) g eps x e /\ eps < &1 / &4
              ==> !y0. y0 IN sphere(vec 0,&1) /\ e y0 = x
                       ==> lrm_deriv_norm2 0
                             (\z. mfd_scalar atlas g x %% rfs_pullback atlas e g z) y0
                           <= K0 pow 2`,
  REWRITE_TAC[P2B_REQ_LRG_RM_NEAR_STATEMENT] THEN DISCH_TAC THEN
  X_CHOOSE_TAC `Kc:real` APX_CYL0_RM_BOUND THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `K:real` o SPEC `Kc pow 2`) THEN
  EXISTS_TAC `&1 + abs K` THEN
  MAP_EVERY X_GEN_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                       `g:A->real^3^3`; `eps:real`; `x:A`; `e:real^3->A`] THEN
  STRIP_TAC THEN X_GEN_TAC `y0:real^3` THEN STRIP_TAC THEN
  UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) eps x e` THEN
  REWRITE_TAC[rfs_neck; rfs_close_on] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(y0:real^3) IN rfs_neck_dom eps` ASSUME_TAC THENL
   [MP_TAC(SPEC `eps:real` APX_UNIT_SPHERE_NECK_DOM) THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(y0:real^3) IN sphere(vec 0,&1)` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(y0:real^3 = vec 0)` ASSUME_TAC THENL
   [UNDISCH_TAC `(y0:real^3) IN sphere(vec 0,&1)` THEN
    REWRITE_TAC[IN_SPHERE_0] THEN DISCH_TAC THEN DISCH_TAC THEN
    UNDISCH_TAC `norm(y0:real^3) = &1` THEN ASM_REWRITE_TAC[NORM_0] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `K:real` THEN CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC(REAL_ARITH `&0 <= (&1 + abs x) * abs x ==> x <= (&1 + abs x) pow 2`) THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REAL_ARITH_TAC] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
    length(fst(strip_forall(concl th))) = 4)) THEN
  MAP_EVERY EXISTS_TAC [`rfs_neck_dom eps`; `cylinder_flow (&0)`] THEN
  ASM_SIMP_TAC[APX_NECK_CYL_FIELD] THEN CONJ_TAC THENL
   [MATCH_MP_TAC LRG_METRIC_FIELD_SCALE THEN ASM_REWRITE_TAC[ETA_AX] THEN
    MATCH_MP_TAC APX_RFS_PULLBACK_FIELD THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `lck_dist2 (rfs_kreg eps) (cylinder_flow (&0))
                (\y. mfd_scalar atlas (g:A->real^3^3) x %%
                     rfs_pullback atlas (e:real^3->A) g y) y0` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LCK_DIST_MONO THEN EXISTS_TAC `rfs_neck_dom eps` THEN
    ASM_REWRITE_TAC[APX_NECK_CYL_FIELD] THEN CONJ_TAC THENL
     [MATCH_MP_TAC LRG_METRIC_FIELD_SCALE THEN ASM_REWRITE_TAC[ETA_AX] THEN
      MATCH_MP_TAC APX_RFS_PULLBACK_FIELD THEN ASM_MESON_TAC[];
      MATCH_MP_TAC APX_KREG_TWO THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `d:real` THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      length(fst(strip_forall(concl th))) = 1 &&
      can (find_term (fun t -> t = `d:real`)) (concl th))) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LT_IMP_LE THEN MATCH_MP_TAC REAL_LTE_TRANS THEN
  EXISTS_TAC `eps pow 2` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `eps pow 2 <= (&1 / &4) pow 2` MP_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC; CONV_TAC REAL_RAT_REDUCE_CONV] THEN
  REAL_ARITH_TAC);;

let P2BS_NECK_UNIF = prove
 (`P2B_REQ_LRG_BASE_STATEMENT /\ P2B_REQ_LRG_RM_NEAR_STATEMENT
   ==> !eps eps'. &0 < eps /\ eps < eps' /\ eps' < &1 / &4
         ==> ?delta. &0 < delta /\
               !top atlas (g:A->real^3^3) x e top' atlas' (g':B->real^3^3) psi psi'.
                  riemannian_metric atlas g /\ rfs_neck (top,atlas) g eps x e /\
                  smooth_manifold_atlas top' atlas' /\ riemannian_metric atlas' g' /\
                  mfd_diffeo top atlas (IMAGE e (rfs_neck_dom eps)) top' atlas'
                             (IMAGE psi (IMAGE e (rfs_neck_dom eps))) psi psi' /\
                  rfs_mclose (rfs_kreg delta) delta atlas (IMAGE e (rfs_neck_dom eps))
                    (\y. mfd_scalar atlas g x %% g y)
                    (\y. mfd_scalar atlas g x %% mfd_pullback_metric atlas atlas' psi g' y)
                  ==> rfs_neck (top',atlas') g' eps' (psi x) (psi o e)`,
  REWRITE_TAC[P2B_REQ_LRG_BASE_STATEMENT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "req") (MP_TAC o MATCH_MP P2BS_SNECK_CENTRE_UNIFORM)) THEN
  DISCH_THEN(X_CHOOSE_THEN `K0:real` (LABEL_TAC "cu" o INST_TYPE [`:A`,`:A`])) THEN
  MAP_EVERY X_GEN_TAC [`eps:real`; `eps':real`] THEN STRIP_TAC THEN
  USE_THEN "req" (MP_TAC o SPEC `rfs_kreg eps'`) THEN
  DISCH_THEN(X_CHOOSE_THEN `M:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "base"))) THEN
  MP_TAC(ISPECL [`eps:real`; `eps':real`; `M:real`; `K0:real`; `&1`; `&2`;
                 `rfs_kreg eps' + 2`] P2B9_DELTA_EXISTS) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `delta:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `delta:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                       `g:A->real^3^3`; `x:A`; `e:real^3->A`;
                       `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                       `g':B->real^3^3`; `psi:A->B`; `psi':B->A`] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `eps':real`; `x:A`; `e:real^3->A`] P2BS_NECK_SHRINK) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `&0 <= eps pow 2 /\ eps pow 2 <= &1 / &4`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_LE_POW_2] THEN
    SUBGOAL_THEN `eps pow 2 <= (&1 / &4) pow 2` MP_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC; CONV_TAC REAL_RAT_REDUCE_CONV] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y0. y0 IN sphere(vec 0,&1) /\ (e:real^3->A) y0 = x
         ==> lrm_deriv_norm2 0
               (\z. mfd_scalar atlas (g:A->real^3^3) x %% rfs_pullback atlas e g z) y0
             <= K0 pow 2`
  ASSUME_TAC THENL
   [USE_THEN "cu" MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `eps:real`] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_diffeo top (atlas:((A->bool)#(A->real^3))->bool)
      (IMAGE (e:real^3->A) (rfs_neck_dom eps')) top'
      (atlas':((B->bool)#(B->real^3))->bool)
      (IMAGE (psi:A->B) (IMAGE e (rfs_neck_dom eps'))) psi psi'`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_DIFFEO_RESTRICT THEN
    MAP_EVERY EXISTS_TAC [`IMAGE (e:real^3->A) (rfs_neck_dom eps)`;
                          `IMAGE (psi:A->B) (IMAGE (e:real^3->A) (rfs_neck_dom eps))`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `rfs_mclose (rfs_kreg delta) delta atlas (IMAGE (e:real^3->A) (rfs_neck_dom eps'))
      (\y. mfd_scalar atlas (g:A->real^3^3) x %% g y)
      (\y. mfd_scalar atlas g x %%
           mfd_pullback_metric atlas (atlas':((B->bool)#(B->real^3))->bool) (psi:A->B)
             (g':B->real^3^3) y)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P2BS_MCLOSE_SUBSET THEN
    EXISTS_TAC `IMAGE (e:real^3->A) (rfs_neck_dom eps)` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &72 * (&1 + abs K0) * delta` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(&1 + &72 * (&1 + abs K0) * delta) * (sqrt(eps pow 2) + sqrt M * delta) +
    &2 * (&72 * (&1 + abs K0) * delta) < eps'`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[POW_2_SQRT; REAL_LT_IMP_LE] THEN MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `(&1 + &2 * &1 * (&72 * (&1 + abs K0) * delta)) pow (rfs_kreg eps' + 2) *
                ((&1 + &72 * (&1 + abs K0) * delta) * (eps + sqrt M * delta) +
                 (&2 + &4 * &1) * (&72 * (&1 + abs K0) * delta))` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P2B9_STATIC_BND THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= a /\ &0 <= b ==> &0 <= a + b`) THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_SIMP_TAC[SQRT_POS_LE; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  MATCH_MP_TAC P2B9_SNECK_CORE THEN
  MAP_EVERY EXISTS_TAC [`rfs_kreg eps'`; `M:real`; `K0:real`; `delta:real`; `eps pow 2`;
                        `top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                        `g:A->real^3^3`; `psi':B->A`] THEN
  ASM_REWRITE_TAC[]);;

let P2BS_ROUND_SECT_Q = prove
 (`!top atlas (g:A->real^3^3) eps W x q g1.
        &0 < eps /\ eps <= &1 / &40 /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ W IN connected_components_of top /\
        &0 < q /\ riemannian_metric atlas g1 /\
        (!x u v. x IN W /\ ~collinear {vec 0,u,v} ==> mfd_sectional atlas g1 x u v = &1) /\
        rfs_mclose (rfs_kreg eps) eps atlas W g1 (\x. q %% g x) /\ x IN W
        ==> !u v. ~collinear {vec 0,u,v}
                  ==> abs(mfd_sectional atlas g x u v / q - &1) <= &24 * eps`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rfs_mclose] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[CONNECTED_COMPONENTS_OF_SUBSET; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `x:A`]
                CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:A` o check (fun th ->
    is_forall (concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "lck_dist2")) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)` THEN
  ABBREV_TAC `yc = SND (c:(A->bool)#(A->real^3)) x` THEN
  ABBREV_TAC `S = IMAGE (SND (c:(A->bool)#(A->real^3))) (FST c)` THEN
  SUBGOAL_THEN `(yc:real^3) IN S` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["yc"; "S"] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `metric_field S (metric_local atlas c (g1:A->real^3^3)) /\
                metric_field S (metric_local atlas c (g:A->real^3^3))`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN CONJ_TAC THENL
     [UNDISCH_TAC `riemannian_metric atlas (g1:A->real^3^3)`;
      UNDISCH_TAC `riemannian_metric atlas (g:A->real^3^3)`] THEN
    REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `metric_local atlas c (\x. q %% (g:A->real^3^3) x) =
                (\z. q %% metric_local atlas c g z)`
  SUBST_ALL_TAC THENL
   [REWRITE_TAC[metric_local; FUN_EQ_THM; MATRIX_MUL_LMUL; MATRIX_MUL_RMUL]; ALL_TAC] THEN
  ABBREV_TAC `G1 = metric_local atlas c (g1:A->real^3^3)` THEN
  ABBREV_TAC `Gg = metric_local atlas c (g:A->real^3^3)` THEN
  SUBGOAL_THEN `metric_field S (\z. q %% (Gg:real^3->real^3^3) z)` ASSUME_TAC THENL
   [MATCH_MP_TAC RFB_METRIC_FIELD_CMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!u v. ~collinear {vec 0,u,v} ==> lsectional (G1:real^3->real^3^3) yc u v = &1`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`x:A`; `u:real^3`; `v:real^3`] o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_sectional"))
          (concl th))) THEN
    ASM_REWRITE_TAC[mfd_sectional];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^3->bool`; `G1:real^3->real^3^3`; `yc:real^3`; `&1`]
                APX_CONST_CURV_RIEMANN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`S:real^3->bool`; `G1:real^3->real^3^3`; `yc:real^3`] LRG_FRAME) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `M:real^3^3` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`G1:real^3->real^3^3`; `yc:real^3`; `M:real^3^3`]
                APX_CONST1_FRAME_BOUND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `sqrt(lck_dist2 2 (G1:real^3->real^3^3) (\z. q %% Gg z) yc) < eps`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `sqrt d` THEN CONJ_TAC THENL
     [REWRITE_TAC[SQRT_MONO_LE_EQ] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `lck_dist2 (rfs_kreg eps) (G1:real^3->real^3^3) (\z. q %% Gg z) yc` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LCK_DIST_MONO THEN
      EXISTS_TAC `S:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC APX_KREG_TWO THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `sqrt(eps pow 2)` THEN
      ASM_SIMP_TAC[SQRT_MONO_LT_EQ; POW_2_SQRT; REAL_LT_IMP_LE; REAL_LE_REFL]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^3->bool`; `G1:real^3->real^3^3`; `\z. q %% (Gg:real^3->real^3^3) z`;
                 `yc:real^3`; `M:real^3^3`; `&2`] APX_SECTIONAL_STABILITY_LIP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_TAC THEN X_GEN_TAC `u:real^3` THEN X_GEN_TAC `v:real^3` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`u:real^3`; `v:real^3`] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "lsectional")) (concl th) &&
    can (find_term (fun t -> t = `&8`)) (concl th))) THEN
  MP_TAC(ISPECL [`S:real^3->bool`; `Gg:real^3->real^3^3`; `q:real`; `yc:real^3`;
                 `u:real^3`; `v:real^3`] APX_LSECTIONAL_SCALE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC[] THEN
  SUBGOAL_THEN `lsectional (Gg:real^3->real^3^3) yc u v =
                mfd_sectional (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) (x:A) u v`
  SUBST1_TAC THENL
   [MAP_EVERY EXPAND_TAC ["Gg"; "yc"; "c"] THEN REWRITE_TAC[mfd_sectional]; ALL_TAC] THEN
  UNDISCH_TAC `sqrt(lck_dist2 2 (G1:real^3->real^3^3) (\z. q %% Gg z) yc) < eps` THEN
  REAL_ARITH_TAC);;

let P2BS_ROUND_UNIF = prove
 (`!eps eps'. &0 < eps /\ &2 * eps <= eps' /\ eps' <= &1 / &40
     ==> ?delta. &0 < delta /\
           !top atlas (g:A->real^3^3) x U top' atlas' (g':B->real^3^3) psi psi'.
              smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
              rfs_round_component (top,atlas) g eps U /\ x IN U /\
              smooth_manifold_atlas top' atlas' /\ riemannian_metric atlas' g' /\
              mfd_diffeo top atlas U top' atlas' (IMAGE psi U) psi psi' /\
              IMAGE psi U IN connected_components_of top' /\
              rfs_mclose (rfs_kreg delta) delta atlas U
                (\y. mfd_scalar atlas g x %% g y)
                (\y. mfd_scalar atlas g x %% mfd_pullback_metric atlas atlas' psi g' y)
              ==> rfs_round_component (top',atlas') g' eps' (IMAGE psi U)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `k = rfs_kreg eps'` THEN
  MP_TAC(SPEC `k:num` (REWRITE_RULE[P2B_REQ_LRG_BASE_STATEMENT] P2B_REQ_LRG_BASE)) THEN
  DISCH_THEN(X_CHOOSE_THEN `M:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "B"))) THEN
  ABBREV_TAC `A1 = M * &9 pow k` THEN
  SUBGOAL_THEN `&0 <= A1` ASSUME_TAC THENL
   [EXPAND_TAC "A1" THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_POW_LE THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `min eps' ((eps' - eps) / (sqrt A1 + &1))` THEN
  ABBREV_TAC `delta = min eps' ((eps' - eps) / (sqrt A1 + &1))` THEN
  SUBGOAL_THEN `&0 < delta /\ delta <= eps' /\ delta <= (eps' - eps) / (sqrt A1 + &1)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "delta" THEN REWRITE_TAC[REAL_MIN_LE; REAL_LT_MIN; REAL_LE_REFL] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN MATCH_MP_TAC REAL_LT_DIV THEN
    SUBGOAL_THEN `&0 <= sqrt A1` MP_TAC THENL [ASM_SIMP_TAC[SQRT_POS_LE]; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                       `g:A->real^3^3`; `x:A`; `U:A->bool`;
                       `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                       `g':B->real^3^3`; `psi:A->B`; `psi':B->A`] THEN
  STRIP_TAC THEN
  UNDISCH_TAC `rfs_round_component (top,atlas) (g:A->real^3^3) eps U` THEN
  REWRITE_TAC[rfs_round_component] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `q:real` (X_CHOOSE_THEN `g1:A->real^3^3` STRIP_ASSUME_TAC))))) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `U:A->bool`; `x:A`; `q:real`; `g1:A->real^3^3`]
                P2BS_ROUND_SECT_Q) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  UNDISCH_TAC `rfs_mclose (rfs_kreg eps) eps atlas U (g1:A->real^3^3)
                 (\x. q %% (g:A->real^3^3) x)` THEN
  REWRITE_TAC[rfs_mclose] THEN DISCH_THEN(X_CHOOSE_THEN `d1:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[CONNECTED_COMPONENTS_OF_SUBSET; SUBSET]; ALL_TAC] THEN
  ABBREV_TAC `R = mfd_scalar atlas (g:A->real^3^3) x` THEN
  SUBGOAL_THEN `&0 < R /\ R / q <= &8` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `g:A->real^3^3`; `x:A`; `q * (&1 - &24 * eps)`] P2BS_MFD_SCALAR_SECT) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `g:A->real^3^3`; `x:A`; `q * (&1 + &24 * eps)`] P2BS_MFD_SCALAR_SECT) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `!u v. ~collinear {vec 0,u,v}
                        ==> q * (&1 - &24 * eps) <= mfd_sectional atlas (g:A->real^3^3) x u v /\
                            mfd_sectional atlas g x u v <= q * (&1 + &24 * eps)`
    ASSUME_TAC THENL
     [REPEAT GEN_TAC THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`u:real^3`; `v:real^3`] o check (fun th ->
        is_forall(concl th) && can (find_term ((=) `&24 * eps`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN
      ABBREV_TAC `s = mfd_sectional atlas (g:A->real^3^3) x u v` THEN DISCH_TAC THEN
      SUBGOAL_THEN `s = q * (s / q)` SUBST1_TAC THENL
       [UNDISCH_TAC `&0 < q` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
      CONJ_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN REPEAT STRIP_TAC THENL
     [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `&6 * q * (&1 - &24 * eps)` THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LT_MUL THEN
      ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&6 * q * (&1 + &24 * eps)` THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `q * (&1 + &24 * eps) <= q * (&4 / &3)` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= d1` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `lck_dist2 (rfs_kreg eps)
                  (metric_local atlas (chart_at atlas (x:A)) (g1:A->real^3^3))
                  (metric_local atlas (chart_at atlas x) (\x. q %% (g:A->real^3^3) x))
                  (SND(chart_at atlas x) x)` THEN
    CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
    MATCH_MP_TAC APX_LCK_DIST2_POS THEN
    EXISTS_TAC `IMAGE (SND (chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)))
                      (FST (chart_at atlas x))` THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `x:A`] CHART_AT) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[FUN_IN_IMAGE; METRIC_LOCAL_CMUL] THEN CONJ_TAC THENL
     [UNDISCH_TAC `riemannian_metric atlas (g1:A->real^3^3)`;
      MATCH_MP_TAC LRG_METRIC_FIELD_SCALE THEN ASM_REWRITE_TAC[ETA_AX] THEN
      UNDISCH_TAC `riemannian_metric atlas (g:A->real^3^3)`] THEN
    REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt d1 < eps` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_LSQRT THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  ABBREV_TAC `A0 = M * (&1 + R / q) pow k` THEN
  SUBGOAL_THEN `&0 <= A0 /\ A0 <= A1` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["A0"; "A1"] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_POW_LE THEN MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 <= &1 + x`) THEN
      ASM_SIMP_TAC[REAL_LE_DIV; REAL_LT_IMP_LE];
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_POW_LE2 THEN
      CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 <= &1 + x`) THEN
      ASM_SIMP_TAC[REAL_LE_DIV; REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  SUBGOAL_THEN `delta <= (eps' - sqrt d1) / (sqrt A0 + &1)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(eps' - eps) / (sqrt A1 + &1)` THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&0 <= sqrt A0 /\ sqrt A0 <= sqrt A1` STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[SQRT_POS_LE; SQRT_MONO_LE]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(eps' - eps) / (sqrt A0 + &1)` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_INV THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  UNDISCH_TAC `rfs_mclose (rfs_kreg delta) delta atlas U (\y. R %% (g:A->real^3^3) y)
                 (\y. R %% mfd_pullback_metric atlas (atlas':((B->bool)#(B->real^3))->bool)
                                (psi:A->B) (g':B->real^3^3) y)` THEN
  REWRITE_TAC[rfs_mclose] THEN DISCH_THEN(X_CHOOSE_THEN `d2:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `&0 <= d2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `lck_dist2 (rfs_kreg delta)
                  (metric_local atlas (chart_at atlas (x:A)) (\y. R %% (g:A->real^3^3) y))
                  (metric_local atlas (chart_at atlas x)
                     (\y. R %% mfd_pullback_metric atlas atlas' (psi:A->B) (g':B->real^3^3) y))
                  (SND(chart_at atlas x) x)` THEN
    ASM_SIMP_TAC[] THEN MATCH_MP_TAC P2B9S_PB_LCK_POS THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `top':B topology`; `U:A->bool`;
                          `IMAGE (psi:A->B) U`; `psi':B->A`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < eps' /\ d1 < eps' pow 2 /\ d1 <= &1 / &4 /\ k <= rfs_kreg delta`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `eps pow 2 <= eps' pow 2 /\ eps pow 2 <= (&1 / &40) pow 2`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      UNDISCH_TAC `eps pow 2 <= (&1 / &40) pow 2` THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      ASM_REAL_ARITH_TAC;
      EXPAND_TAC "k" THEN MATCH_MP_TAC APX_KREG_MONO THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y. y IN U
        ==> lck_dist2 k (metric_local atlas (chart_at atlas y) (g1:A->real^3^3))
                        (metric_local atlas (chart_at atlas y) (\x. q %% (g:A->real^3^3) x))
                        (SND(chart_at atlas y) y) <= d1`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:A` THEN DISCH_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `lck_dist2 (rfs_kreg eps)
                  (metric_local atlas (chart_at atlas (y:A)) (g1:A->real^3^3))
                  (metric_local atlas (chart_at atlas y) (\x. q %% (g:A->real^3^3) x))
                  (SND(chart_at atlas y) y)` THEN
    ASM_SIMP_TAC[] THEN MATCH_MP_TAC LCK_DIST_MONO THEN
    EXISTS_TAC `IMAGE (SND (chart_at (atlas:((A->bool)#(A->real^3))->bool) (y:A)))
                      (FST (chart_at atlas y))` THEN
    SUBGOAL_THEN `(y:A) IN topspace top` ASSUME_TAC THENL
     [ASM_MESON_TAC[CONNECTED_COMPONENTS_OF_SUBSET; SUBSET]; ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `y:A`] CHART_AT) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[FUN_IN_IMAGE; METRIC_LOCAL_CMUL] THEN REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `riemannian_metric atlas (g1:A->real^3^3)` THEN
      REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC LRG_METRIC_FIELD_SCALE THEN ASM_REWRITE_TAC[ETA_AX] THEN
      UNDISCH_TAC `riemannian_metric atlas (g:A->real^3^3)` THEN
      REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      EXPAND_TAC "k" THEN MATCH_MP_TAC APX_KREG_MONO THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[rfs_round_component] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC IMAGE_COMPACT_IN THEN EXISTS_TAC `subtopology top (U:A->bool)` THEN
    ASM_REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY; SUBSET_REFL] THEN
    FIRST_ASSUM(ACCEPT_TAC o CONJUNCT1 o MATCH_MP MFD_DIFFEO_MAPS);
    ALL_TAC] THEN
  EXISTS_TAC `q:real` THEN
  EXISTS_TAC `\z. if z IN IMAGE (psi:A->B) U
                  then mfd_pullback_metric atlas' atlas (psi':B->A) (g1:A->real^3^3) z
                  else (g':B->real^3^3) z` THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g1:A->real^3^3`;
                 `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`; `g':B->real^3^3`;
                 `U:A->bool`; `IMAGE (psi:A->B) U`; `psi:A->B`; `psi':B->A`]
                P2B9S_ROUND_TARGET_METRIC) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CLOSED_IN_CONNECTED_COMPONENTS_OF THEN
    ASM_REWRITE_TAC[];
    STRIP_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `(sqrt d1 + sqrt(M * (&1 + R / q) pow k * d2)) pow 2` THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_MUL_ASSOC] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC P2B9S_DELTA_ARITH THEN EXISTS_TAC `delta:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `y:A` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `g1:A->real^3^3`;
                 `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`; `g':B->real^3^3`;
                 `U:A->bool`; `IMAGE (psi:A->B) U`; `psi:A->B`; `psi':B->A`;
                 `q:real`; `R:real`; `M:real`; `k:num`; `rfs_kreg delta`;
                 `d1:real`; `d2:real`; `y:A`] P2B9S_ROUND_POINT) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[] THEN USE_THEN "B" ACCEPT_TAC;
    SIMP_TAC[]]);;

(* ========================================================================= *)
(* rfs_mclose is monotone in delta; the slice form follows from the cap form *)
(* and the three cases above, with K = max 2 Kc and eps0 = min (1/40) epc.   *)
(* ========================================================================= *)

let P2BS_MCLOSE_MONO = prove
 (`!top atlas (g:A->real^N^N) top' atlas' (g':B->real^N^N) U U' psi psi' R delta delta'.
     smooth_manifold_atlas top atlas /\ smooth_manifold_atlas top' atlas' /\
     riemannian_metric atlas g /\ riemannian_metric atlas' g' /\
     mfd_diffeo top atlas U top' atlas' U' psi psi' /\ &0 < R /\ &0 < delta /\
     delta <= delta' /\
     rfs_mclose (rfs_kreg delta) delta atlas U (\y. R %% g y)
       (\y. R %% mfd_pullback_metric atlas atlas' psi g' y)
     ==> rfs_mclose (rfs_kreg delta') delta' atlas U (\y. R %% g y)
           (\y. R %% mfd_pullback_metric atlas atlas' psi g' y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rfs_mclose] THEN STRIP_TAC THEN
  EXISTS_TAC `d:real` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `delta pow 2` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `y:A` THEN DISCH_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `lck_dist2 (rfs_kreg delta)
                (metric_local atlas (chart_at atlas (y:A)) (\z. R %% (g:A->real^N^N) z))
                (metric_local atlas (chart_at atlas y)
                   (\z. R %% mfd_pullback_metric atlas atlas' (psi:A->B) (g':B->real^N^N) z))
                (SND(chart_at atlas y) y)` THEN
  ASM_SIMP_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`; `g':B->real^N^N`;
                 `U:A->bool`; `U':B->bool`; `psi:A->B`; `psi':B->A`; `y:A`] P2B9S_PB_FIELDS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC)) THEN
  MATCH_MP_TAC LCK_DIST_MONO THEN EXISTS_TAC `s:real^N->bool` THEN
  ASM_REWRITE_TAC[METRIC_LOCAL_CMUL] THEN REPEAT CONJ_TAC THEN
  TRY(MATCH_MP_TAC LRG_METRIC_FIELD_SCALE THEN ASM_REWRITE_TAC[ETA_AX] THEN NO_TAC) THEN
  MATCH_MP_TAC APX_KREG_MONO THEN ASM_REWRITE_TAC[]);;

let P2BS_SLICE_FROM_CAP = prove
 (`!(u:A->bool) (w:B->bool).
     P2B_PROP_9_79_CAP_FIX_STATEMENT u w ==> P2B_PROP_9_79_SLICE_FIX_STATEMENT u w`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[P2B_PROP_9_79_CAP_FIX_STATEMENT; P2B_PROP_9_79_SLICE_FIX_STATEMENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `Kc:real` (X_CHOOSE_THEN `epc:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "CAP"))))) THEN
  MAP_EVERY EXISTS_TAC [`max (&2) Kc`; `min (&1 / &40) epc`] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[REAL_LT_MIN] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`C:real`; `eps:real`; `C':real`; `eps':real`; `Kr:real`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `&2 * eps <= eps' /\ Kc * eps <= eps' /\ eps' <= &1 / &40 /\ eps' <= epc /\
                eps < eps' /\ eps' < &1 / &4`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&2 * eps <= max (&2) Kc * eps /\ Kc * eps <= max (&2) Kc * eps`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `eps' <= min (&1 / &40) epc` THEN REWRITE_TAC[REAL_LE_MIN] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "CAP" (MP_TAC o SPECL [`C:real`; `eps:real`; `C':real`; `eps':real`; `Kr:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "D1"))) THEN
  MP_TAC(SPECL [`eps:real`; `eps':real`]
    (MATCH_MP P2BS_NECK_UNIF (CONJ P2B_REQ_LRG_BASE P2B_REQ_LRG_RM_NEAR))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "D2"))) THEN
  MP_TAC(SPECL [`C:real`; `C':real`; `Kr:real`]
    (MATCH_MP P2BS_CCOMP_UNIF P2B_REQ_LRG_DERIV)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d3:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "D3"))) THEN
  MP_TAC(SPECL [`eps:real`; `eps':real`] P2BS_ROUND_UNIF) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d4:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "D4"))) THEN
  EXISTS_TAC `min (min d1 d2) (min d3 d4)` THEN
  ABBREV_TAC `delta = min (min d1 d2) (min d3 d4)` THEN
  SUBGOAL_THEN `&0 < delta /\ delta <= d1 /\ delta <= d2 /\ delta <= d3 /\ delta <= d4`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "delta" THEN REWRITE_TAC[REAL_LT_MIN; REAL_MIN_LE; REAL_LE_REFL] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                       `g:A->real^3^3`; `top':B topology`;
                       `atlas':((B->bool)#(B->real^3))->bool`; `g':B->real^3^3`;
                       `x:A`; `U:A->bool`; `psi:A->B`; `psi':B->A`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `!d. &0 < mfd_scalar atlas (g:A->real^3^3) x /\ delta <= d
        ==> rfs_mclose (rfs_kreg d) d atlas U
              (\y. mfd_scalar atlas (g:A->real^3^3) x %% g y)
              (\y. mfd_scalar atlas g x %%
                   mfd_pullback_metric atlas atlas' (psi:A->B) (g':B->real^3^3) y)`
  (LABEL_TAC "MC") THENL
   [X_GEN_TAC `d:real` THEN STRIP_TAC THEN MATCH_MP_TAC P2BS_MCLOSE_MONO THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `top':B topology`; `IMAGE (psi:A->B) U`;
                          `psi':B->A`; `delta:real`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(DISJ_CASES_THEN2 (X_CHOOSE_THEN `e:real^3->A` STRIP_ASSUME_TAC)
    (DISJ_CASES_THEN2 (X_CHOOSE_THEN `Y:A->bool` STRIP_ASSUME_TAC)
      (DISJ_CASES_THEN2 STRIP_ASSUME_TAC STRIP_ASSUME_TAC)) o
    GEN_REWRITE_RULE I [rfs_canonical_nbhd] o
    check (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) = "rfs_canonical_nbhd"
                     with Failure _ -> false)) THENL
   [SUBGOAL_THEN `&0 < mfd_scalar atlas (g:A->real^3^3) x` ASSUME_TAC THENL
     [UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) eps x e` THEN SIMP_TAC[rfs_neck];
      ALL_TAC] THEN
    USE_THEN "MC" (fun th -> MP_TAC(MATCH_MP (SPEC `d2:real` th)
      (CONJ (ASSUME `&0 < mfd_scalar atlas (g:A->real^3^3) x`) (ASSUME `delta <= d2`)))) THEN
    DISCH_TAC THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `U:A->bool`)) THEN
    EXISTS_TAC `IMAGE ((psi:A->B) o (e:real^3->A)) (rfs_neck_dom eps')` THEN CONJ_TAC THENL
     [REWRITE_TAC[IMAGE_o] THEN MATCH_MP_TAC IMAGE_SUBSET THEN MATCH_MP_TAC IMAGE_SUBSET THEN
      MATCH_MP_TAC APX_NECK_DOM_MONO THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[rfs_canonical_nbhd] THEN DISJ1_TAC THEN
    EXISTS_TAC `(psi:A->B) o (e:real^3->A)` THEN REWRITE_TAC[] THEN
    USE_THEN "D2" MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                          `g:A->real^3^3`; `psi':B->A`] THEN
    ASM_REWRITE_TAC[];
    SUBGOAL_THEN `&0 < mfd_scalar atlas (g:A->real^3^3) x` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                     `g:A->real^3^3`; `C:real`; `eps:real`; `U:A->bool`; `Y:A->bool`]
                    APX_CAP_CORE) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      SUBGOAL_THEN `(x:A) IN U` ASSUME_TAC THENL
       [SUBGOAL_THEN `(Y:A->bool) SUBSET top closure_of Y` MP_TAC THENL
         [MATCH_MP_TAC CLOSURE_OF_SUBSET THEN ASM_SIMP_TAC[OPEN_IN_SUBSET]; ALL_TAC] THEN
        UNDISCH_TAC `top closure_of (Y:A->bool) SUBSET U` THEN
        UNDISCH_TAC `(x:A) IN Y` THEN SET_TAC[];
        ALL_TAC] THEN
      UNDISCH_TAC `rfs_cap (top,atlas) (g:A->real^3^3) C eps U Y` THEN
      REWRITE_TAC[rfs_cap] THEN STRIP_TAC THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    USE_THEN "MC" (fun th -> MP_TAC(MATCH_MP (SPEC `d1:real` th)
      (CONJ (ASSUME `&0 < mfd_scalar atlas (g:A->real^3^3) x`) (ASSUME `delta <= d1`)))) THEN
    DISCH_TAC THEN
    USE_THEN "D1" (MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                                   `g:A->real^3^3`; `top':B topology`;
                                   `atlas':((B->bool)#(B->real^3))->bool`; `g':B->real^3^3`;
                                   `x:A`; `U:A->bool`; `Y:A->bool`; `psi:A->B`;
                                   `psi':B->A`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[];
      DISCH_THEN(X_CHOOSE_THEN `U':B->bool` (X_CHOOSE_THEN `Y':B->bool` STRIP_ASSUME_TAC))] THEN
    EXISTS_TAC `U':B->bool` THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      REWRITE_TAC[rfs_canonical_nbhd] THEN DISJ2_TAC THEN DISJ1_TAC THEN
      EXISTS_TAC `Y':B->bool` THEN ASM_REWRITE_TAC[]];
    SUBGOAL_THEN `U IN connected_components_of (top:A topology)` ASSUME_TAC THENL
     [UNDISCH_TAC `rfs_c_component (top,atlas) (g:A->real^3^3) C U` THEN
      SIMP_TAC[rfs_c_component];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < mfd_scalar atlas (g:A->real^3^3) x` ASSUME_TAC THENL
     [MATCH_MP_TAC P2B_MFD_SCALAR_POS THEN EXISTS_TAC `top:A topology` THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MP_TAC(ISPECL [`top:A topology`; `U:A->bool`] CONNECTED_COMPONENTS_OF_SUBSET) THEN
        ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(x:A) IN U` THEN SET_TAC[];
        REPEAT STRIP_TAC THEN
        UNDISCH_TAC `rfs_c_component (top,atlas) (g:A->real^3^3) C U` THEN
        REWRITE_TAC[rfs_c_component] THEN STRIP_TAC THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    USE_THEN "MC" (fun th -> MP_TAC(MATCH_MP (SPEC `d3:real` th)
      (CONJ (ASSUME `&0 < mfd_scalar atlas (g:A->real^3^3) x`) (ASSUME `delta <= d3`)))) THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `IMAGE (psi:A->B) U IN connected_components_of top'` ASSUME_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    EXISTS_TAC `IMAGE (psi:A->B) U` THEN REWRITE_TAC[SUBSET_REFL; rfs_canonical_nbhd] THEN
    DISJ2_TAC THEN DISJ2_TAC THEN DISJ1_TAC THEN
    CONJ_TAC THENL [ASM_SIMP_TAC[FUN_IN_IMAGE]; ALL_TAC] THEN
    USE_THEN "D3" MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                          `g:A->real^3^3`; `x:A`; `psi':B->A`] THEN
    ASM_REWRITE_TAC[];
    SUBGOAL_THEN `U IN connected_components_of (top:A topology)` ASSUME_TAC THENL
     [UNDISCH_TAC `rfs_round_component (top,atlas) (g:A->real^3^3) eps U` THEN
      SIMP_TAC[rfs_round_component];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < mfd_scalar atlas (g:A->real^3^3) x` ASSUME_TAC THENL
     [MATCH_MP_TAC P2B_MFD_SCALAR_POS THEN EXISTS_TAC `top:A topology` THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MP_TAC(ISPECL [`top:A topology`; `U:A->bool`] CONNECTED_COMPONENTS_OF_SUBSET) THEN
        ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(x:A) IN U` THEN SET_TAC[];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                     `g:A->real^3^3`; `eps:real`; `U:A->bool`; `x:A`] APX_ROUND_SECTIONAL) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `q:real` STRIP_ASSUME_TAC) THEN
      MAP_EVERY X_GEN_TAC [`u1:real^3`; `v1:real^3`] THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`u1:real^3`; `v1:real^3`]) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      SUBGOAL_THEN `&0 < mfd_sectional atlas (g:A->real^3^3) x u1 v1 / q` MP_TAC THENL
       [ASM_REAL_ARITH_TAC; ASM_SIMP_TAC[REAL_LT_RDIV_EQ; REAL_MUL_LZERO]];
      ALL_TAC] THEN
    USE_THEN "MC" (fun th -> MP_TAC(MATCH_MP (SPEC `d4:real` th)
      (CONJ (ASSUME `&0 < mfd_scalar atlas (g:A->real^3^3) x`) (ASSUME `delta <= d4`)))) THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `IMAGE (psi:A->B) U IN connected_components_of top'` ASSUME_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    EXISTS_TAC `IMAGE (psi:A->B) U` THEN REWRITE_TAC[SUBSET_REFL; rfs_canonical_nbhd] THEN
    DISJ2_TAC THEN DISJ2_TAC THEN DISJ2_TAC THEN
    CONJ_TAC THENL [ASM_SIMP_TAC[FUN_IN_IMAGE]; ALL_TAC] THEN
    USE_THEN "D4" MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                          `g:A->real^3^3`; `x:A`; `psi':B->A`] THEN
    ASM_REWRITE_TAC[]]);;

