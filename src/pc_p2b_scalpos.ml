(* ========================================================================= *)
(* Unit pc_p2b_scalpos (Part 2B): positive sectional curvature gives        *)
(* positive scalar curvature.  In a G-orthonormal frame f_i = M^-1 e_i       *)
(* (G y = M^T M, LRG_FRAME) the scalar curvature is the sum over i, j of     *)
(* the curvature terms of the coordinate planes, nonnegative and positive   *)
(* for i <> j (P2B_FRAME_TERM), so R > 0 in dimension at least 2            *)
(* (P2B_LSCALAR_POS_SECT); on a 3-manifold in the preferred charts           *)
(* (P2B_MFD_SCALAR_POS).  A small separate unit, since pc_p2c_cderiv needs   *)
(* only these.                                                               *)
(* ========================================================================= *)

needs "src/pc_lrg_stab.ml";;

prioritize_real();;
type_invention_error := true;;

let P2B_FRAME_ORTHO = prove
 (`!(G:real^N^N) (M:real^N^N) i j.
     G = transp M ** M /\ invertible M /\
     1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
     ==> (matrix_inv M ** basis i) dot (G ** (matrix_inv M ** basis j)) =
         if i = j then &1 else &0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`G:real^N^N`; `M:real^N^N`; `matrix_inv(M:real^N^N) ** basis i:real^N`;
                 `matrix_inv(M:real^N^N) ** basis j:real^N`] LRG_FRAME_DOT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_ASSOC] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[CONJUNCT1(MATCH_MP MATRIX_INV th)]) THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_LID] THEN ASM_SIMP_TAC[DOT_BASIS_BASIS]);;

let P2B_LSCALAR_FRAME = prove
 (`!U (G:real^N->real^N^N) y (M:real^N^N).
     metric_field U G /\ y IN U /\ G y = transp M ** M /\ invertible M
     ==> lscalar G y =
         sum(1..dimindex(:N))
            (\j. lricci G y (matrix_inv M ** basis j) (matrix_inv M ** basis j))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`] LRG_LSCALAR_TRACE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN `matrix_inv((G:real^N->real^N^N) y) = matrix_inv(M:real^N^N) ** transp(matrix_inv M)`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[MATRIX_INV_MUL; INVERTIBLE_TRANSP; MATRIX_INV_TRANSP]; ALL_TAC] THEN
  ONCE_REWRITE_TAC[GSYM MATRIX_MUL_ASSOC] THEN ONCE_REWRITE_TAC[TRACE_MUL_SYM] THEN
  REWRITE_TAC[LRG_TRACE_BASIS] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
  X_GEN_TAC `j:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`;
                 `matrix_inv(M:real^N^N) ** basis j:real^N`; `matrix_inv(M:real^N^N) ** basis j:real^N`]
                LRG_LRICCI_DOT_FORM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_SIMP_TAC[GSYM DOT_BASIS] THEN
  REWRITE_TAC[GSYM MATRIX_VECTOR_MUL_ASSOC; DOT_MATRIX_TRANSP_LMUL] THEN
  MATCH_ACCEPT_TAC DOT_SYM);;

let P2B_LRICCI_FRAME = prove
 (`!U (G:real^N->real^N^N) y (M:real^N^N) v.
     metric_field U G /\ y IN U /\ G y = transp M ** M /\ invertible M
     ==> lricci G y v v =
         sum(1..dimindex(:N))
            (\i. (matrix_inv M ** basis i) dot
                 (G y ** lriemann G y (matrix_inv M ** basis i) v v))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[lricci] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `sum(1..dimindex(:N))
                (\i. ((M:real^N^N) ** lriemann (G:real^N->real^N^N) y
                                        (matrix_inv M ** basis i) v v)$i)` THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`\z:real^N. lriemann (G:real^N->real^N^N) y z v v`; `M:real^N^N`]
                  LRG_TRACE_FRAME) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`] LRIEMANN_TRILINEAR) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`(G:real^N->real^N^N) y`; `M:real^N^N`; `matrix_inv(M:real^N^N) ** basis i`;
                 `lriemann (G:real^N->real^N^N) y (matrix_inv(M:real^N^N) ** basis i) v v`]
                LRG_FRAME_DOT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_ASSOC] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[CONJUNCT1(MATCH_MP MATRIX_INV th)]) THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_LID] THEN ASM_SIMP_TAC[DOT_BASIS]);;

let P2B_FRAME_TERM = prove
 (`!U (G:real^N->real^N^N) y (M:real^N^N) i j.
     metric_field U G /\ y IN U /\ G y = transp M ** M /\ invertible M /\
     (!u v. ~collinear {vec 0,u,v} ==> &0 < lsectional G y u v) /\
     1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
     ==> &0 <= (matrix_inv M ** basis i) dot
               (G y ** lriemann G y (matrix_inv M ** basis i)
                                    (matrix_inv M ** basis j) (matrix_inv M ** basis j)) /\
         (~(i = j)
          ==> &0 < (matrix_inv M ** basis i) dot
                   (G y ** lriemann G y (matrix_inv M ** basis i)
                                        (matrix_inv M ** basis j) (matrix_inv M ** basis j)))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "sect") STRIP_ASSUME_TAC))))) THEN
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
  ASM_CASES_TAC `i:num = j` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(fi:real^N) = fj` SUBST_ALL_TAC THENL
     [MAP_EVERY EXPAND_TAC ["fi"; "fj"] THEN REFL_TAC; ALL_TAC] THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `fj:real^N`;
                   `fj:real^N`; `fj:real^N`] LRIEMANN_ANTISYM) THEN
    ASM_REWRITE_TAC[VECTOR_ARITH `(x:real^N) = --x <=> x = vec 0`] THEN
    SIMP_TAC[MATRIX_VECTOR_MUL_RZERO; DOT_RZERO; REAL_LE_REFL];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `(fi:real^N) dot ((G:real^N->real^N^N) y ** fj) =
               (if (i:num) = j then &1 else &0)` THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `~collinear {vec 0,fi:real^N,fj}` ASSUME_TAC THENL
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
    ALL_TAC] THEN
  USE_THEN "sect" (fun th -> MP_TAC(MATCH_MP (SPECL [`fi:real^N`; `fj:real^N`] th)
                                        (ASSUME `~collinear {vec 0,fi:real^N,fj}`))) THEN
  REWRITE_TAC[lsectional] THEN ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REWRITE_TAC[REAL_DIV_1] THEN SIMP_TAC[REAL_LT_IMP_LE]);;

let P2B_LSCALAR_POS_SECT = prove
 (`!U (G:real^N->real^N^N) y.
     metric_field U G /\ y IN U /\ 2 <= dimindex(:N) /\
     (!u v. ~collinear {vec 0,u,v} ==> &0 < lsectional G y u v)
     ==> &0 < lscalar G y`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`] LRG_FRAME) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `M:real^N^N` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `M:real^N^N`]
                P2B_LSCALAR_FRAME) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN
   `!j. 1 <= j /\ j <= dimindex(:N)
        ==> lricci (G:real^N->real^N^N) y (matrix_inv(M:real^N^N) ** basis j)
                   (matrix_inv M ** basis j) =
            sum(1..dimindex(:N))
              (\i. (matrix_inv M ** basis i) dot
                   (G y ** lriemann G y (matrix_inv M ** basis i)
                                        (matrix_inv M ** basis j) (matrix_inv M ** basis j)))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC P2B_LRICCI_FRAME THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
          ==> &0 <= (matrix_inv(M:real^N^N) ** basis i) dot
                    ((G:real^N->real^N^N) y ** lriemann G y (matrix_inv M ** basis i)
                         (matrix_inv M ** basis j) (matrix_inv M ** basis j)) /\
              (~(i = j)
               ==> &0 < (matrix_inv M ** basis i) dot
                        (G y ** lriemann G y (matrix_inv M ** basis i)
                             (matrix_inv M ** basis j) (matrix_inv M ** basis j)))`
  (LABEL_TAC "term") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC P2B_FRAME_TERM THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `(G:real^N->real^N^N) y = transp(M:real^N^N) ** M` THEN
  DISCH_THEN(K ALL_TAC) THEN
  MATCH_MP_TAC SUM_POS_LT THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN CONJ_TAC THENL
   [X_GEN_TAC `j:num` THEN STRIP_TAC THEN ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN USE_THEN "term" (MP_TAC o SPECL [`i:num`; `j:num`]) THEN
    ASM_SIMP_TAC[];
    EXISTS_TAC `1` THEN CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `1 <= 1 /\ 1 <= dimindex(:N)` STRIP_ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN MATCH_MP_TAC SUM_POS_LT THEN
    REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN CONJ_TAC THENL
     [X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
      USE_THEN "term" (MP_TAC o SPECL [`i:num`; `1`]) THEN ASM_SIMP_TAC[];
      EXISTS_TAC `2` THEN REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      USE_THEN "term" (MP_TAC o SPECL [`2`; `1`]) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o CONJUNCT2) THEN REWRITE_TAC[ARITH]]]);;

let P2B_MFD_SCALAR_POS = prove
 (`!top atlas (g:A->real^3^3) x.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\ x IN topspace top /\
     (!u v. ~collinear {vec 0,u,v} ==> &0 < mfd_sectional atlas g x u v)
     ==> &0 < mfd_scalar atlas g x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_scalar] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN MATCH_MP_TAC P2B_LSCALAR_POS_SECT THEN
  EXISTS_TAC `IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A))) (FST(chart_at atlas x))` THEN
  REWRITE_TAC[DIMINDEX_3; ARITH] THEN CONJ_TAC THENL
   [UNDISCH_TAC `riemannian_metric atlas (g:A->real^3^3)` THEN
    REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL [ASM_SIMP_TAC[FUN_IN_IMAGE]; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL [`u:real^3`; `v:real^3`]) THEN
  ASM_REWRITE_TAC[mfd_sectional]);;

