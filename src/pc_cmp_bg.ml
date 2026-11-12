(* ========================================================================= *)
(* Unit pc_cmp_bg (comparison-geometry layer CMP): the global Bishop-Gromov  *)
(* inequality on a complete 3-manifold with sec >= 0 (MT Thm 1.34),          *)
(* CMP_T1_BISHOP_GROMOV and CMP_T3_BISHOP_GROMOV_P2B, in the forms of the    *)
(* statements P2C_REQ_BISHOP_GROMOV and P2B_REQ_CMP_BISHOP_GROMOV.  sec >= k *)
(* at a point gives Ric >= (n-1) k there (a G-orthonormal frame whose first  *)
(* vector is w / |w|); completeness gives compact closures of balls; S1      *)
(* (CMP_RELVOL) with K = 0 and V_0(r) = 4/3 pi r^3 finish.                   *)
(* ========================================================================= *)

needs "src/pc_cmp_relvol.ml";;
needs "src/pc_p2b_scalpos.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* The statement constants CMP_T1_BISHOP_GROMOV_STATEMENT and                *)
(* CMP_T3_BISHOP_GROMOV_P2B_STATEMENT; their bodies equal those of           *)
(* P2C_REQ_BISHOP_GROMOV_STATEMENT (pc_p2c_iface) and                        *)
(* P2B_REQ_CMP_BISHOP_GROMOV_STATEMENT (pc_p2b_defs).                        *)
(* ========================================================================= *)

let CMP_T1_BISHOP_GROMOV_STATEMENT = new_definition
 `CMP_T1_BISHOP_GROMOV_STATEMENT (u:A->bool) <=>
    !top atlas g x r1 r2 v1 v2.
       hausdorff_space (top:A topology) /\
       smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool) /\
       riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\
       (!y u v. y IN topspace top /\ ~collinear {vec 0,u,v}
                ==> &0 <= mfd_sectional atlas g y u v) /\
       x IN topspace top /\ &0 < r1 /\ r1 <= r2 /\
       mfd_has_volume (top,atlas) g (mfd_ball (top,atlas) g x r1) v1 /\
       mfd_has_volume (top,atlas) g (mfd_ball (top,atlas) g x r2) v2
       ==> v2 / r2 pow 3 <= v1 / r1 pow 3`;;

let CMP_T3_BISHOP_GROMOV_P2B_STATEMENT = new_definition
 `CMP_T3_BISHOP_GROMOV_P2B_STATEMENT (w:B->bool) <=>
    !top atlas g p r1 r2 v1 v2.
       hausdorff_space top /\ smooth_manifold_atlas top (atlas:((B->bool)#(B->real^3))->bool) /\
       riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\
       (!x u v. x IN topspace top /\ ~collinear {vec 0,u,v}
                ==> &0 <= mfd_sectional atlas g x u v) /\
       p IN topspace top /\ &0 < r1 /\ r1 <= r2 /\
       mfd_has_volume (top,atlas) g (mfd_ball (top,atlas) g p r1) v1 /\
       mfd_has_volume (top,atlas) g (mfd_ball (top,atlas) g p r2) v2
       ==> v2 / r2 pow 3 <= v1 / r1 pow 3 /\ v1 <= &4 / &3 * pi * r1 pow 3`;;

(* ========================================================================= *)
(* Sec >= k at a point gives Ric(w,w) >= (n-1) k <w,w>.  Take a              *)
(* G-orthonormal frame f_i = M^-1 e_i whose first vector is w / c; the term  *)
(* of f_1 in the frame trace of Ric vanishes (R(f,f) = 0) and each other     *)
(* term is sec(f_i,w) c^2 >= k <w,w> (P2B_LRICCI_FRAME, P2B_FRAME_ORTHO).    *)
(* ========================================================================= *)

let CMPZ_FRAME_FIRST = prove
 (`!U (G:real^N->real^N^N) y w.
        metric_field U G /\ y IN U /\ ~(w = vec 0)
        ==> ?(M:real^N^N) c. invertible M /\ G y = transp M ** M /\ &0 < c /\
                             matrix_inv M ** basis 1 = inv c % w`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`] LRG_FRAME) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `M0:real^N^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `~((M0:real^N^N) ** w = vec 0)` ASSUME_TAC THENL
   [DISCH_THEN(MP_TAC o AP_TERM `\z:real^N. matrix_inv(M0:real^N^N) ** z`) THEN
    ASM_SIMP_TAC[MATRIX_VECTOR_MUL_ASSOC; MATRIX_INV; MATRIX_VECTOR_MUL_LID;
                 MATRIX_VECTOR_MUL_RZERO];
    ALL_TAC] THEN
  ABBREV_TAC `c = norm((M0:real^N^N) ** w)` THEN
  SUBGOAL_THEN `&0 < c` ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `norm(inv c % ((M0:real^N^N) ** w)) = &1` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_MUL; REAL_ABS_INV] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < c ==> abs c = c`; REAL_MUL_LINV; REAL_LT_IMP_NZ];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?P:real^N^N. orthogonal_matrix P /\ P ** basis 1 = inv c % ((M0:real^N^N) ** w)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`basis 1:real^N`; `inv c % ((M0:real^N^N) ** w)`]
      ORTHOGONAL_TRANSFORMATION_EXISTS_1) THEN
    ASM_SIMP_TAC[NORM_BASIS; DIMINDEX_GE_1; LE_REFL] THEN
    DISCH_THEN(X_CHOOSE_THEN `f:real^N->real^N` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `matrix(f:real^N->real^N)` THEN
    FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [ORTHOGONAL_TRANSFORMATION]) THEN
    ASM_SIMP_TAC[MATRIX_WORKS] THEN ASM_MESON_TAC[ORTHOGONAL_TRANSFORMATION_MATRIX];
    ALL_TAC] THEN
  SUBGOAL_THEN `transp(P:real^N^N) ** P = mat 1 /\ P ** transp P = mat 1`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `orthogonal_matrix(P:real^N^N)` THEN REWRITE_TAC[orthogonal_matrix];
    ALL_TAC] THEN
  SUBGOAL_THEN `invertible(transp(P:real^N^N) ** (M0:real^N^N))` ASSUME_TAC THENL
   [REWRITE_TAC[INVERTIBLE_MATRIX_MUL] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[INVERTIBLE_LEFT_INVERSE] THEN EXISTS_TAC `P:real^N^N` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(transp(P:real^N^N) ** (M0:real^N^N)) ** (inv c % w) = basis 1` ASSUME_TAC THENL
   [SUBGOAL_THEN
     `(transp(P:real^N^N) ** (M0:real^N^N)) ** (inv c % w) =
      transp P ** (inv c % (M0 ** w))` SUBST1_TAC THENL
     [REWRITE_TAC[MATRIX_VECTOR_MUL_RMUL; MATRIX_VECTOR_MUL_ASSOC]; ALL_TAC] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      lhand(concl th) = `(P:real^N^N) ** basis 1`)) THEN
    ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_ASSOC; MATRIX_VECTOR_MUL_LID];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`transp(P:real^N^N) ** (M0:real^N^N)`; `c:real`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[MATRIX_TRANSP_MUL; TRANSP_TRANSP] THEN
    SUBGOAL_THEN
     `(transp(M0:real^N^N) ** (P:real^N^N)) ** (transp P ** M0) =
      transp M0 ** (P ** transp P) ** M0` SUBST1_TAC THENL
     [REWRITE_TAC[MATRIX_MUL_ASSOC]; ASM_REWRITE_TAC[MATRIX_MUL_LID]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o AP_TERM
    `\z:real^N. matrix_inv(transp(P:real^N^N) ** (M0:real^N^N)) ** z` o
    check (fun th -> is_eq(concl th) && rand(concl th) = `basis 1:real^N`)) THEN
  ASM_SIMP_TAC[MATRIX_VECTOR_MUL_ASSOC; MATRIX_INV; MATRIX_VECTOR_MUL_LID] THEN
  MESON_TAC[]);;

let CMPZ_FIRST_TERM_ZERO = prove
 (`!U (G:real^N->real^N^N) y (f:real^N) c w.
        metric_field U G /\ y IN U /\ ~(c = &0) /\ f = inv c % w
        ==> lriemann G y f w w = vec 0`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `w = c % (f:real^N)` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[VECTOR_MUL_ASSOC] THEN ASM_SIMP_TAC[REAL_MUL_RINV; VECTOR_MUL_LID];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`] LRIEMANN_TRILINEAR) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!z. lriemann (G:real^N->real^N^N) y f f z = vec 0` ASSUME_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `f:real^N`;
                   `f:real^N`; `z:real^N`] LRIEMANN_ANTISYM) THEN
    ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `linear (\v. lriemann (G:real^N->real^N^N) y f v (c % f))` MP_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`c:real`; `f:real^N`] o MATCH_MP LINEAR_CMUL) THEN
  ASM_REWRITE_TAC[VECTOR_MUL_RZERO]);;

let CMPZ_TERM_LOWER = prove
 (`!(G:real^N->real^N^N) y kappa (f1:real^N) fi c w.
        (!u v. ~collinear {vec 0,u,v} ==> kappa <= lsectional G y u v) /\
        fi dot (G y ** fi) = &1 /\ fi dot (G y ** f1) = &0 /\
        f1 dot (G y ** f1) = &1 /\ &0 < c /\ f1 = inv c % w
        ==> kappa * (w dot (G y ** w)) <= fi dot (G y ** lriemann G y fi w w)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "sec") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "f1")))))) THEN
  SUBGOAL_THEN `w = c % (f1:real^N)` SUBST1_TAC THENL
   [REMOVE_THEN "f1" SUBST1_TAC THEN REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
    ASM_SIMP_TAC[REAL_MUL_RINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID];
    REMOVE_THEN "f1" (K ALL_TAC)] THEN
  SUBGOAL_THEN
   `(fi:real^N) dot ((G:real^N->real^N^N) y ** (c % f1)) = &0 /\
    (c % f1) dot (G y ** (c % f1)) = c pow 2`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_RMUL; DOT_RMUL; DOT_LMUL; REAL_MUL_RZERO] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < c pow 2` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `~((c % f1:real^N) = vec 0)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    UNDISCH_TAC `(c % f1:real^N) dot ((G:real^N->real^N^N) y ** (c % f1)) = c pow 2` THEN
    ASM_REWRITE_TAC[DOT_LZERO] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~collinear {vec 0,fi:real^N,c % f1}` ASSUME_TAC THENL
   [REWRITE_TAC[COLLINEAR_LEMMA; DE_MORGAN_THM; NOT_EXISTS_THM] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [DISCH_TAC THEN
      UNDISCH_TAC `(fi:real^N) dot ((G:real^N->real^N^N) y ** fi) = &1` THEN
      ASM_REWRITE_TAC[DOT_LZERO] THEN REAL_ARITH_TAC;
      X_GEN_TAC `t:real` THEN DISCH_TAC THEN
      UNDISCH_TAC `(fi:real^N) dot ((G:real^N->real^N^N) y ** (c % f1)) = &0` THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[MATRIX_VECTOR_MUL_RMUL; DOT_RMUL] THEN
      ASM_REWRITE_TAC[REAL_MUL_RID] THEN
      DISCH_TAC THEN UNDISCH_TAC `~((c % f1:real^N) = vec 0)` THEN
      ASM_REWRITE_TAC[VECTOR_MUL_LZERO]];
    ALL_TAC] THEN
  USE_THEN "sec" (fun th -> MP_TAC(MATCH_MP th
    (ASSUME `~collinear {vec 0,fi:real^N,c % f1}`))) THEN
  REWRITE_TAC[lsectional] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[REAL_ARITH `&1 * x - &0 pow 2 = x`] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ]);;

let CMPZ_LRICCI_SEC_LOWER = prove
 (`!U (G:real^N->real^N^N) y kappa w.
        metric_field U G /\ y IN U /\
        (!u v. ~collinear {vec 0,u,v} ==> kappa <= lsectional G y u v)
        ==> &(dimindex(:N) - 1) * kappa * (w dot (G y ** w)) <= lricci G y w w`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "sec"))) THEN
  ASM_CASES_TAC `w:real^N = vec 0` THENL
   [MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`]
      LRIEMANN_TRILINEAR) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[DOT_LZERO; REAL_MUL_RZERO; lricci] THEN
    SUBGOAL_THEN `!u. lriemann (G:real^N->real^N^N) y u (vec 0) (vec 0) = vec 0`
      (fun th -> REWRITE_TAC[th; VEC_COMPONENT; SUM_0; REAL_LE_REFL]) THEN
    X_GEN_TAC `u:real^N` THEN
    SUBGOAL_THEN `linear (\z. lriemann (G:real^N->real^N^N) y u (vec 0) z)` MP_TAC THENL
     [ASM_REWRITE_TAC[]; DISCH_THEN(MP_TAC o MATCH_MP LINEAR_0) THEN REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `w:real^N`]
    CMPZ_FRAME_FIRST) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `M:real^N^N` (X_CHOOSE_THEN `c:real` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `M:real^N^N`;
                 `w:real^N`] P2B_LRICCI_FRAME) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN `1 <= dimindex(:N)` ASSUME_TAC THENL
   [REWRITE_TAC[DIMINDEX_GE_1]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. 2 <= i /\ i <= dimindex(:N)
        ==> kappa * (w dot ((G:real^N->real^N^N) y ** w)) <=
            (matrix_inv(M:real^N^N) ** basis i) dot
            (G y ** lriemann G y (matrix_inv M ** basis i) w w)`
  (LABEL_TAC "terms") THENL
   [X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `1 <= i /\ ~(i = 1)` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `2 <= i` THEN ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN
     `(matrix_inv(M:real^N^N) ** basis i) dot
      ((G:real^N->real^N^N) y ** (matrix_inv M ** basis i)) = &1 /\
      (matrix_inv M ** basis i) dot (G y ** (matrix_inv M ** basis 1)) = &0 /\
      (matrix_inv M ** basis 1) dot (G y ** (matrix_inv M ** basis 1)) = &1`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THENL
       [MP_TAC(ISPECL [`(G:real^N->real^N^N) y`; `M:real^N^N`; `i:num`; `i:num`]
          P2B_FRAME_ORTHO);
        MP_TAC(ISPECL [`(G:real^N->real^N^N) y`; `M:real^N^N`; `i:num`; `1`]
          P2B_FRAME_ORTHO);
        MP_TAC(ISPECL [`(G:real^N->real^N^N) y`; `M:real^N^N`; `1`; `1`]
          P2B_FRAME_ORTHO)] THEN
      ASM_REWRITE_TAC[LE_REFL];
      ALL_TAC] THEN
    MATCH_MP_TAC CMPZ_TERM_LOWER THEN
    MAP_EVERY EXISTS_TAC [`matrix_inv(M:real^N^N) ** basis 1`; `c:real`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SIMP_TAC[SUM_CLAUSES_LEFT; DIMINDEX_GE_1] THEN
  SUBGOAL_THEN
   `lriemann (G:real^N->real^N^N) y (matrix_inv(M:real^N^N) ** basis 1) w w = vec 0`
  SUBST1_TAC THENL
   [MATCH_MP_TAC CMPZ_FIRST_TERM_ZERO THEN
    MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `c:real`] THEN
    ASM_SIMP_TAC[REAL_LT_IMP_NZ];
    REWRITE_TAC[MATRIX_VECTOR_MUL_RZERO; DOT_RZERO; REAL_ADD_LID]] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(1 + 1..dimindex(:N))
                (\i. kappa * (w dot ((G:real^N->real^N^N) y ** w)))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[SUM_CONST_NUMSEG] THEN
    SUBGOAL_THEN `(dimindex(:N) + 1) - (1 + 1) = dimindex(:N) - 1` SUBST1_TAC THENL
     [ARITH_TAC; REWRITE_TAC[REAL_LE_REFL]];
    MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN USE_THEN "terms" MATCH_MP_TAC THEN
    MAP_EVERY UNDISCH_TAC [`1 + 1 <= i`; `i <= dimindex(:N)`] THEN ARITH_TAC]);;

let CMPZ_MFD_RICCI_SEC_LOWER = prove
 (`!top atlas (g:A->real^N^N) y kappa w.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        y IN topspace top /\
        (!u v. ~collinear {vec 0,u,v} ==> kappa <= mfd_sectional atlas g y u v)
        ==> &(dimindex(:N) - 1) * kappa * (w dot (g y ** w)) <= mfd_ricci atlas g y w w`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `y:A`] CMPF_LOCAL_METRIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[mfd_ricci] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
    rand(concl th) = `(g:A->real^N^N) y`)) THEN
  MATCH_MP_TAC CMPZ_LRICCI_SEC_LOWER THEN
  EXISTS_TAC `IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (y:A)))
                    (FST(chart_at atlas y))` THEN
  ASM_REWRITE_TAC[GSYM mfd_sectional]);;

(* ========================================================================= *)
(* T1 and T3.  Completeness gives compact closures of balls, sec >= 0 gives  *)
(* Ric >= 0, and S1 at K = 0 with V_0(r) = 4/3 pi r^3 gives v2 / r2^3 <= v1  *)
(* / r1^3 and v1 <= 4/3 pi r1^3.                                             *)
(* ========================================================================= *)

let CMPZ_COMPLETE_CLOSURE_COMPACT = prove
 (`!top atlas (g:A->real^N^N) x R.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        mfd_complete (top,atlas) g /\ x IN topspace top
        ==> compact_in top (top closure_of mfd_ball (top,atlas) g x R)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC CLOSED_COMPACT_IN THEN
  EXISTS_TAC `mfd_cball (top,atlas) (g:A->real^N^N) x R` THEN
  REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[mfd_complete];
    MATCH_MP_TAC CLOSURE_OF_MINIMAL THEN ASM_SIMP_TAC[MFD_CBALL_CLOSED] THEN
    REWRITE_TAC[mfd_ball; mfd_cball; SUBSET; IN_ELIM_THM] THEN MESON_TAC[REAL_LT_IMP_LE];
    REWRITE_TAC[CLOSED_IN_CLOSURE_OF]]);;

let CMPZ_BG3_MAIN = prove
 (`!top atlas (g:A->real^3^3) x r1 r2 v1 v2.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\
        (!y u v. y IN topspace top /\ ~collinear {vec 0,u,v}
                 ==> &0 <= mfd_sectional atlas g y u v) /\
        x IN topspace top /\ &0 < r1 /\ r1 <= r2 /\
        mfd_has_volume (top,atlas) g (mfd_ball (top,atlas) g x r1) v1 /\
        mfd_has_volume (top,atlas) g (mfd_ball (top,atlas) g x r2) v2
        ==> v2 / r2 pow 3 <= v1 / r1 pow 3 /\ v1 <= &4 / &3 * pi * r1 pow 3`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < r2` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`(:A)`; `(:3)`] CMP_RELVOL) THEN REWRITE_TAC[CMP_RELVOL_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                             `g:A->real^3^3`; `x:A`; `&0`; `r2:real`; `r1:real`;
                             `r2:real`; `v1:real`; `v2:real`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_LE_REFL] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CMPZ_COMPLETE_CLOSURE_COMPACT THEN ASM_REWRITE_TAC[];
      MAP_EVERY X_GEN_TAC [`y:A`; `w:real^3`] THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                     `g:A->real^3^3`; `y:A`; `&0`; `w:real^3`] CMPZ_MFD_RICCI_SEC_LOWER) THEN
      ANTS_TAC THENL
       [SUBGOAL_THEN `(y:A) IN topspace top` ASSUME_TAC THENL
         [UNDISCH_TAC `(y:A) IN mfd_ball (top,atlas) (g:A->real^3^3) x r2` THEN
          REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN MESON_TAC[MFD_JOINABLE_IN_TOPSPACE];
          ALL_TAC] THEN
        ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
          is_forall(concl th) && length(fst(strip_forall(concl th))) = 3)) THEN
        ASM_REWRITE_TAC[];
        REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_RZERO; REAL_NEG_0]]];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_NEG_0] THEN
  ASM_SIMP_TAC[CMP_VMODEL_FLAT; VOLUME_BALL; REAL_LT_IMP_LE] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 < &4 / &3 * pi` ASSUME_TAC THENL
   [MP_TAC PI_POS THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < r1 pow 3 /\ &0 < r2 pow 3` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  MATCH_MP_TAC CMPB_DIV_LE THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_LCANCEL_IMP THEN EXISTS_TAC `&4 / &3 * pi` THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `v2 * &4 / &3 * pi * r1 pow 3 <= v1 * &4 / &3 * pi * r2 pow 3` THEN
  REAL_ARITH_TAC);;

(* CMP_T1_BISHOP_GROMOV and CMP_T3_BISHOP_GROMOV_P2B: the statement constants hold. *)

let CMP_T1_BISHOP_GROMOV = prove
 (`!(u:A->bool). CMP_T1_BISHOP_GROMOV_STATEMENT u`,
  REWRITE_TAC[CMP_T1_BISHOP_GROMOV_STATEMENT] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP CMPZ_BG3_MAIN) THEN SIMP_TAC[]);;

let CMP_T3_BISHOP_GROMOV_P2B = prove
 (`!(w:B->bool). CMP_T3_BISHOP_GROMOV_P2B_STATEMENT w`,
  REWRITE_TAC[CMP_T3_BISHOP_GROMOV_P2B_STATEMENT] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP CMPZ_BG3_MAIN) THEN SIMP_TAC[]);;

