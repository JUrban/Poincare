(* ========================================================================= *)
(* Unit pc_cmp_hess (comparison-geometry layer CMP): Laplacian comparison    *)
(* barriers S7 (CMP_LAPLACIAN_BARRIER, Calabi) and S8                        *)
(* (CMP_LAPLACIAN_BARRIER_SQ).  The Laplacian of r = |w| in Gauss-lemma      *)
(* coordinates is (n-1)/r + tr(G^-1 D_w G)/(2r); along a ray of the exp      *)
(* pullback this is tr(B A^-1) - 1/r, bounded by (n-1) ct_{-K}(r) under      *)
(* Ric >= -(n-1) K (CMPJ_TRACE_UPPER); the barrier delta + |psi(y)|_q at a   *)
(* point q of a minimizing geodesic near p (CMPN_NO_CONJ) transfers to the   *)
(* chart at x by LLAP_PULLBACK.                                              *)
(* ========================================================================= *)

needs "src/pc_cmp_nconj.ml";;
needs "src/pc_mfd_restrict.ml";;
needs "src/pc_cmp_conj.ml";;
needs "src/pc_rfa_slcalc.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* The Laplacian and gradient of r = |w| for a metric field G                *)
(* with the Gauss property G(w) w = w: llap = (n-1)/r + tr(G^-1 D_w G)/(2r)  *)
(* and lgrad2 = 1.                                                           *)
(* ========================================================================= *)

let CMPH_BASIS_ENTRY = prove
 (`!(A:real^N^N) i j.
        1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
        ==> basis i dot (A ** basis j) = A$i$j`,
  SIMP_TAC[MATRIX_VECTOR_MUL_BASIS; DOT_BASIS; column; LAMBDA_BETA]);;

let CMPH_SUM_PAIR_TRACE = prove
 (`!(M:real^N^N) X.
        sum(1..dimindex(:N)) (\i. sum(1..dimindex(:N)) (\j. M$i$j * X$i$j)) =
        trace(M ** transp X)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[trace] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN ASM_SIMP_TAC[matrix_mul; LAMBDA_BETA] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  ASM_SIMP_TAC[transp; LAMBDA_BETA]);;

let CMPH_QUAD_SUM = prove
 (`!(M:real^N^N) (y:real^N).
        sum(1..dimindex(:N)) (\i. sum(1..dimindex(:N)) (\j. M$i$j * y$i * y$j)) =
        y dot (M ** y)`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`M:real^N^N`; `\i. (y:real^N)$i`] LRG_QUADFORM_SUM) THEN
  REWRITE_TAC[LAMBDA_ETA]);;

let CMPH_CHRISTOFFEL_RADIAL2 = prove
 (`!U (G:real^N->real^N^N) y a b.
        metric_field U G /\ y IN U /\ (!z. z IN U ==> G z ** z = z)
        ==> y dot christoffel G y a b =
            a dot b - a dot (G y ** b) - inv(&2) * (a dot (mderiv G y y ** b))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(G:real^N->real^N^N) y ** y = y` ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^N) dot christoffel G y a b = y dot (G y ** christoffel G y a b)`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `y:real^N`;
                   `christoffel (G:real^N->real^N^N) y a b`] LRG_METRIC_SYM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN MATCH_ACCEPT_TAC DOT_SYM;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `a:real^N`;
                 `b:real^N`; `y:real^N`] LRG_CHRISTOFFEL_DOT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `a:real^N`;
                 `y:real^N`; `b:real^N`] LRG_MDERIV_SYM) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `b:real^N`;
                 `y:real^N`; `a:real^N`] LRG_MDERIV_SYM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `a:real^N`]
    CMPP_GAUSS_DERIV) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o AP_TERM `\v:real^N. (b:real^N) dot v`) THEN
  REWRITE_TAC[DOT_RADD] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `b:real^N`]
    CMPP_GAUSS_DERIV) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o AP_TERM `\v:real^N. (a:real^N) dot v`) THEN
  REWRITE_TAC[DOT_RADD] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `b:real^N`;
                 `a:real^N`] LRG_METRIC_SYM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`a:real^N`; `b:real^N`] DOT_SYM) THEN
  ASM_REAL_ARITH_TAC);;

let CMPH_MDERIV_TRANSP = prove
 (`!U (G:real^N->real^N^N) y w.
        metric_field U G /\ y IN U ==> transp(mderiv G y w) = mderiv G y w`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CMPP_MATRIX_EQ_DOT THEN
  MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real^N`] THEN
  ONCE_REWRITE_TAC[DOT_SYM] THEN REWRITE_TAC[DOT_MATRIX_TRANSP_LMUL] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `w:real^N`;
                 `a:real^N`; `b:real^N`] LRG_MDERIV_SYM) THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[DOT_SYM]);;

let CMPH_LLAP_NORM = prove
 (`!U (G:real^N->real^N^N) y.
        metric_field U G /\ y IN U /\ ~(y = vec 0) /\ (!z. z IN U ==> G z ** z = z)
        ==> llap G (\z. norm z) y =
            (&(dimindex(:N)) - &1) / norm y +
            trace(matrix_inv(G y) ** mderiv G y y) / (&2 * norm y)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < norm(y:real^N)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  ABBREV_TAC `t = norm(y:real^N)` THEN
  SUBGOAL_THEN
   `!z b:real^N. ~(z = vec 0)
                 ==> drop(frechet_derivative (\x. lift(norm x)) (at z) b) =
                     (z dot b) / norm z`
  (LABEL_TAC "d1") THENL
   [REPEAT STRIP_TAC THEN
    FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT o
                MATCH_MP CMPP_NORM_DERIV) THEN
    REWRITE_TAC[LIFT_DROP];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!a b:real^N.
      drop(frechet_derivative
             (\z. frechet_derivative (\w. lift(norm w)) (at z) a) (at y) b) =
      (b dot a) / t - (y dot a) * (y dot b) / t pow 3`
  (LABEL_TAC "d2") THENL
   [REPEAT GEN_TAC THEN
    SUBGOAL_THEN
     `frechet_derivative (\z. frechet_derivative (\w. lift(norm w)) (at z) (a:real^N))
        (at y) =
      (\h. lift((h dot a) / norm y - (y dot a) * (y dot h) / norm y pow 3))`
    (fun th -> REWRITE_TAC[th; LIFT_DROP] THEN ASM_REWRITE_TAC[]) THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `frechet_derivative (\z:real^N. lift((z dot a) / norm z)) (at y)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LRG_FRECHET_DERIVATIVE_EQ_OPEN THEN
      EXISTS_TAC `(:real^N) DELETE (vec 0)` THEN
      SIMP_TAC[OPEN_DELETE; OPEN_UNIV; IN_DELETE; IN_UNIV] THEN ASM_REWRITE_TAC[] THEN
      REPEAT STRIP_TAC THEN
      USE_THEN "d1" (fun th -> REWRITE_TAC[GSYM(MATCH_MP th (ASSUME `~(z:real^N = vec 0)`))]) THEN
      REWRITE_TAC[LIFT_DROP];
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
      ASM_SIMP_TAC[CMPP_NORM_DIR_DERIV]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!k. 1 <= k /\ k <= dimindex(:N)
        ==> drop(frechet_derivative (\z. lift(norm(z:real^N))) (at y) (basis k)) =
            y$k / t`
  (LABEL_TAC "d1k") THENL
   [REPEAT STRIP_TAC THEN
    USE_THEN "d1" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `~(y:real^N = vec 0)`)]) THEN
    ASM_SIMP_TAC[DOT_BASIS];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
          ==> drop(frechet_derivative
                     (\z. frechet_derivative (\w. lift(norm w)) (at z) (basis j))
                     (at y) (basis i)) -
              sum(1..dimindex(:N))
               (\k. (christoffel (G:real^N->real^N^N) y (basis i) (basis j))$k *
                    drop(frechet_derivative (\z. lift(norm z)) (at y) (basis k))) =
              ((G y)$i$j * inv t + (mderiv G y y)$i$j * inv(&2 * t)) -
              ((y:real^N)$i * y$j) * inv(t pow 3)`
  (LABEL_TAC "summand") THENL
   [REPEAT STRIP_TAC THEN USE_THEN "d2" (fun th -> REWRITE_TAC[th]) THEN
    SUBGOAL_THEN
     `sum(1..dimindex(:N))
       (\k. (christoffel (G:real^N->real^N^N) y (basis i) (basis j))$k *
            drop(frechet_derivative (\z. lift(norm z)) (at y) (basis k))) =
      (y dot christoffel G y (basis i) (basis j)) / t`
    SUBST1_TAC THENL
     [MATCH_MP_TAC EQ_TRANS THEN
      EXISTS_TAC `sum(1..dimindex(:N))
                    (\k. ((christoffel (G:real^N->real^N^N) y (basis i) (basis j))$k *
                          (y:real^N)$k) * inv t)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
        ASM_SIMP_TAC[] THEN REWRITE_TAC[real_div] THEN REAL_ARITH_TAC;
        REWRITE_TAC[SUM_RMUL; GSYM dot; real_div] THEN
        AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_ACCEPT_TAC DOT_SYM];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`;
                   `basis i:real^N`; `basis j:real^N`] CMPH_CHRISTOFFEL_RADIAL2) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    ASM_SIMP_TAC[CMPH_BASIS_ENTRY; DOT_BASIS] THEN
    UNDISCH_TAC `&0 < t` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  REWRITE_TAC[llap] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `sum(1..dimindex(:N)) (\i. sum(1..dimindex(:N)) (\j.
      (matrix_inv((G:real^N->real^N^N) y)$i$j * (G y)$i$j) * inv t +
      (matrix_inv(G y)$i$j * (mderiv G y y)$i$j) * inv(&2 * t) -
      (matrix_inv(G y)$i$j * (y:real^N)$i * y$j) * inv(t pow 3)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN USE_THEN "summand" (fun th -> ASM_SIMP_TAC[th]) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[SUM_ADD_NUMSEG; SUM_SUB_NUMSEG; SUM_RMUL] THEN
  REWRITE_TAC[CMPH_SUM_PAIR_TRACE; CMPH_QUAD_SUM] THEN
  SUBGOAL_THEN `transp((G:real^N->real^N^N) y) = G y /\
                transp(mderiv G y y) = mderiv G y y`
  (fun th -> REWRITE_TAC[th]) THENL
   [CONJ_TAC THENL
     [ASM_MESON_TAC[metric_field]; MATCH_MP_TAC CMPH_MDERIV_TRANSP THEN
      EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`]
    LRG_METRIC_INVERTIBLE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `matrix_inv((G:real^N->real^N^N) y) ** G y = mat 1` SUBST1_TAC THENL
   [ASM_SIMP_TAC[MATRIX_INV]; ALL_TAC] THEN
  SUBGOAL_THEN `matrix_inv((G:real^N->real^N^N) y) ** y = y` SUBST1_TAC THENL
   [SUBGOAL_THEN `y = (G:real^N->real^N^N) y ** y` (fun th ->
      GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[MATRIX_VECTOR_MUL_ASSOC; MATRIX_INV; MATRIX_VECTOR_MUL_LID];
    ALL_TAC] THEN
  REWRITE_TAC[TRACE_I; DOT_SQUARE_NORM] THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `&0 < t` THEN CONV_TAC REAL_FIELD);;

let CMPH_LGRAD2_NORM = prove
 (`!U (G:real^N->real^N^N) y.
        metric_field U G /\ y IN U /\ ~(y = vec 0) /\ (!z. z IN U ==> G z ** z = z)
        ==> lgrad2 G (\z. norm z) y = &1`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < norm(y:real^N)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  ABBREV_TAC `t = norm(y:real^N)` THEN
  SUBGOAL_THEN
   `!k. 1 <= k /\ k <= dimindex(:N)
        ==> drop(frechet_derivative (\z. lift(norm(z:real^N))) (at y) (basis k)) =
            y$k / t`
  (LABEL_TAC "d1k") THENL
   [REPEAT STRIP_TAC THEN
    FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT o
                MATCH_MP CMPP_NORM_DERIV) THEN
    ASM_SIMP_TAC[LIFT_DROP; DOT_BASIS];
    ALL_TAC] THEN
  REWRITE_TAC[lgrad2] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `sum(1..dimindex(:N)) (\i. sum(1..dimindex(:N)) (\j.
      (matrix_inv((G:real^N->real^N^N) y)$i$j * (y:real^N)$i * y$j) * inv(t pow 2)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN USE_THEN "d1k" (fun th -> ASM_SIMP_TAC[th]) THEN
    UNDISCH_TAC `&0 < t` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  REWRITE_TAC[SUM_RMUL; CMPH_QUAD_SUM] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`]
    LRG_METRIC_INVERTIBLE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `matrix_inv((G:real^N->real^N^N) y) ** y = y` SUBST1_TAC THENL
   [SUBGOAL_THEN `y = (G:real^N->real^N^N) y ** y` (fun th ->
      GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[MATRIX_VECTOR_MUL_ASSOC; MATRIX_INV; MATRIX_VECTOR_MUL_LID];
    ALL_TAC] THEN
  REWRITE_TAC[DOT_SQUARE_NORM] THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `&0 < t` THEN CONV_TAC REAL_FIELD);;

(* ========================================================================= *)
(* Along a ray of the exp pullback, with the Jacobi system                   *)
(* A, B of the ray, tr(G^-1 D_w G) = 2 |w| tr(B A^-1) - 2n, so the           *)
(* Laplacian of r = |w| is tr(B A^-1) - 1/|w|.                               *)
(* ========================================================================= *)

let CMPH_SYM_QUAD_EQ = prove
 (`!X Y:real^N^N.
        transp X = X /\ transp Y = Y /\ (!a. a dot (X ** a) = a dot (Y ** a))
        ==> X = Y`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CMPP_MATRIX_EQ_DOT THEN
  MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real^N`] THEN
  SUBGOAL_THEN
   `!M:real^N^N. transp M = M
                 ==> a dot (M ** b) =
                     ((a + b) dot (M ** (a + b)) - (a - b) dot (M ** (a - b))) / &4`
  (fun th -> ASM_SIMP_TAC[th]) THEN
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_ADD_LDISTRIB; MATRIX_VECTOR_MUL_SUB_LDISTRIB;
              DOT_LADD; DOT_RADD; DOT_LSUB; DOT_RSUB] THEN
  SUBGOAL_THEN `(b:real^N) dot ((M:real^N^N) ** a) = a dot (M ** b)` SUBST1_TAC THENL
   [MP_TAC(ISPECL [`M:real^N^N`; `a:real^N`; `b:real^N`] DOT_MATRIX_TRANSP_LMUL) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[DOT_SYM];
    REAL_ARITH_TAC]);;

let CMPH_TRACE_CONGRUENCE = prove
 (`!(Tm:real^N^N) (b:real^N^N).
        invertible Tm
        ==> trace(matrix_inv(transp Tm ** Tm) ** (transp Tm ** b ** Tm)) = trace b`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[MATRIX_INV_MUL; INVERTIBLE_TRANSP] THEN
  REWRITE_TAC[GSYM MATRIX_MUL_ASSOC] THEN
  SUBGOAL_THEN `matrix_inv(transp(Tm:real^N^N)) ** transp Tm ** (b:real^N^N) ** Tm = b ** Tm`
  SUBST1_TAC THENL
   [REWRITE_TAC[MATRIX_MUL_ASSOC] THEN
    ASM_SIMP_TAC[MATRIX_INV; INVERTIBLE_TRANSP; MATRIX_MUL_LID];
    ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [TRACE_MUL_SYM] THEN
  REWRITE_TAC[GSYM MATRIX_MUL_ASSOC] THEN
  ASM_SIMP_TAC[MATRIX_INV; MATRIX_MUL_RID]);;

let CMPH_RAY_MDERIV = prove
 (`!U (G:real^N->real^N^N) w (P:real^N^N) (A:real->real^N^N) B R L eta a.
        metric_field U G /\ w IN U /\ &0 < norm w /\ norm w < L /\ &0 < eta /\
        cmp_jsys A B R L /\
        (!s a. abs(s - norm w) < eta /\ &0 < s
               ==> a dot (G(s % inv(norm w) % w) ** a) =
                   ((A s ** (transp P ** a)) dot (A s ** (transp P ** a))) / s pow 2)
        ==> a dot (mderiv G w w ** a) =
            norm w * (&2 * ((B(norm w) ** (transp P ** a)) dot
                            (A(norm w) ** (transp P ** a))) / norm w pow 2 -
                      &2 * ((A(norm w) ** (transp P ** a)) dot
                            (A(norm w) ** (transp P ** a))) / norm w pow 3)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(LABEL_TAC "ray") THEN
  ABBREV_TAC `t = norm(w:real^N)` THEN
  ABBREV_TAC `c:real^N = transp(P:real^N^N) ** a` THEN
  SUBGOAL_THEN `t % inv t % (w:real^N) = w` ASSUME_TAC THENL
   [REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
    ASM_SIMP_TAC[REAL_MUL_RINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID];
    ALL_TAC] THEN
  SUBGOAL_THEN `(vectorize o (G:real^N->real^N^N)) differentiable at w` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `w:real^N`]
      LRG_METRIC_FIELD_DIFF) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `mderiv (G:real^N->real^N^N) w w = t %% mderiv G w (inv t % w)`
  SUBST1_TAC THENL
   [FIRST_ASSUM(fun th -> REWRITE_TAC[GSYM(CONJUNCT2(MATCH_MP LRG_MDERIV_LINEAR th))]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[MATRIX_VECTOR_LMUL; DOT_RMUL] THEN AP_TERM_TAC THEN
  MATCH_MP_TAC REAL_DERIVATIVE_UNIQUE_ATREAL THEN
  EXISTS_TAC `\s. (((A:real->real^N^N) s ** c) dot (A s ** (c:real^N))) / s pow 2` THEN
  EXISTS_TAC `t:real` THEN CONJ_TAC THENL
   [MATCH_MP_TAC HAS_REAL_DERIVATIVE_TRANSFORM_ATREAL THEN
    EXISTS_TAC `\s. (a:real^N) dot ((G:real^N->real^N^N)(s % inv t % w) ** a)` THEN
    EXISTS_TAC `min t eta` THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      X_GEN_TAC `s:real` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
      USE_THEN "ray" (MP_TAC o SPECL [`s:real`; `a:real^N`]) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]];
      SUBGOAL_THEN
       `mderiv (G:real^N->real^N^N) w (inv t % w) =
        mderiv G (t % inv t % w) (inv t % w)`
      SUBST1_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC CMPP_GDOT_RAY_DERIV THEN ASM_REWRITE_TAC[]];
    MATCH_MP_TAC CMPP_GRAM_RAY_DERIV THEN
    MAP_EVERY EXISTS_TAC [`R:real->real^N^N`; `L:real`] THEN ASM_REWRITE_TAC[]]);;

let CMPH_RAY_TRACE = prove
 (`!U (G:real^N->real^N^N) w (P:real^N^N) (A:real->real^N^N) B R L eta.
        metric_field U G /\ w IN U /\ &0 < norm w /\ norm w < L /\ &0 < eta /\
        orthogonal_matrix P /\ cmp_jsys A B R L /\ invertible(A(norm w)) /\
        (!s a. abs(s - norm w) < eta /\ &0 < s
               ==> a dot (G(s % inv(norm w) % w) ** a) =
                   ((A s ** (transp P ** a)) dot (A s ** (transp P ** a))) / s pow 2)
        ==> trace(matrix_inv(G w) ** mderiv G w w) =
            &2 * norm w * trace(B(norm w) ** matrix_inv(A(norm w))) -
            &2 * &(dimindex(:N))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(LABEL_TAC "ray") THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `w:real^N`; `P:real^N^N`;
                 `A:real->real^N^N`; `B:real->real^N^N`; `R:real->real^N^N`; `L:real`;
                 `eta:real`] CMPH_RAY_MDERIV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "md") THEN
  ABBREV_TAC `t = norm(w:real^N)` THEN
  SUBGOAL_THEN `t % inv t % (w:real^N) = w` ASSUME_TAC THENL
   [REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
    ASM_SIMP_TAC[REAL_MUL_RINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID];
    ALL_TAC] THEN
  ABBREV_TAC `Tm = inv t %% ((A:real->real^N^N) t ** transp(P:real^N^N))` THEN
  ABBREV_TAC `X = (B:real->real^N^N) t ** matrix_inv((A:real->real^N^N) t)` THEN
  ABBREV_TAC `bs = t %% ((X:real^N^N) + transp X) - &2 %% mat 1:real^N^N` THEN
  SUBGOAL_THEN `!a:real^N. (Tm:real^N^N) ** a =
                inv t % ((A:real->real^N^N) t ** (transp(P:real^N^N) ** a))`
  (LABEL_TAC "Ta") THENL
   [GEN_TAC THEN EXPAND_TAC "Tm" THEN REWRITE_TAC[MATRIX_VECTOR_LMUL] THEN
    REWRITE_TAC[MATRIX_VECTOR_MUL_ASSOC];
    ALL_TAC] THEN
  SUBGOAL_THEN `invertible(Tm:real^N^N)` ASSUME_TAC THENL
   [EXPAND_TAC "Tm" THEN
    ASM_SIMP_TAC[INVERTIBLE_CMUL; REAL_INV_EQ_0; REAL_LT_IMP_NZ; INVERTIBLE_MATRIX_MUL;
                 INVERTIBLE_TRANSP; ORTHOGONAL_MATRIX_IMP_INVERTIBLE];
    ALL_TAC] THEN
  SUBGOAL_THEN `(G:real^N->real^N^N) w = transp (Tm:real^N^N) ** Tm` ASSUME_TAC THENL
   [MATCH_MP_TAC CMPH_SYM_QUAD_EQ THEN REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[metric_field];
      REWRITE_TAC[MATRIX_TRANSP_MUL; TRANSP_TRANSP];
      X_GEN_TAC `a:real^N` THEN
      USE_THEN "ray" (MP_TAC o SPECL [`t:real`; `a:real^N`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_ABS_0]; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      ONCE_REWRITE_TAC[DOT_SYM] THEN
      REWRITE_TAC[GSYM MATRIX_VECTOR_MUL_ASSOC; DOT_MATRIX_TRANSP_LMUL] THEN
      USE_THEN "Ta" (fun th -> REWRITE_TAC[th]) THEN
      REWRITE_TAC[DOT_LMUL; DOT_RMUL] THEN
      UNDISCH_TAC `&0 < t` THEN CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  SUBGOAL_THEN `transp(bs:real^N^N) = bs` ASSUME_TAC THENL
   [EXPAND_TAC "bs" THEN
    REWRITE_TAC[TRANSP_MATRIX_SUB; TRANSP_MATRIX_CMUL; TRANSP_MATRIX_ADD; TRANSP_MAT;
                TRANSP_TRANSP] THEN
    REWRITE_TAC[MATRIX_ADD_SYM];
    ALL_TAC] THEN
  SUBGOAL_THEN `mderiv (G:real^N->real^N^N) w w = transp (Tm:real^N^N) ** bs ** Tm`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CMPH_SYM_QUAD_EQ THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CMPH_MDERIV_TRANSP THEN EXISTS_TAC `U:real^N->bool` THEN
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[MATRIX_TRANSP_MUL; TRANSP_TRANSP; MATRIX_MUL_ASSOC];
      X_GEN_TAC `a:real^N` THEN USE_THEN "md" (fun th -> REWRITE_TAC[th]) THEN
      ABBREV_TAC `c:real^N = transp(P:real^N^N) ** a` THEN
      ABBREV_TAC `v:real^N = (Tm:real^N^N) ** a` THEN
      SUBGOAL_THEN `v = inv t % ((A:real->real^N^N) t ** (c:real^N))` ASSUME_TAC THENL
       [MAP_EVERY EXPAND_TAC ["v"; "c"] THEN USE_THEN "Ta" (fun th -> REWRITE_TAC[th]);
        ALL_TAC] THEN
      REWRITE_TAC[GSYM MATRIX_VECTOR_MUL_ASSOC] THEN
      SUBGOAL_THEN `(a:real^N) dot (transp(Tm:real^N^N) ** bs ** Tm ** a) =
                    v dot ((bs:real^N^N) ** v)` SUBST1_TAC THENL
       [EXPAND_TAC "v" THEN ONCE_REWRITE_TAC[DOT_SYM] THEN
        REWRITE_TAC[DOT_MATRIX_TRANSP_LMUL];
        ALL_TAC] THEN
      SUBGOAL_THEN `(X:real^N^N) ** (A:real->real^N^N) t ** (c:real^N) = (B:real->real^N^N) t ** c`
      ASSUME_TAC THENL
       [EXPAND_TAC "X" THEN REWRITE_TAC[GSYM MATRIX_MUL_ASSOC; MATRIX_VECTOR_MUL_ASSOC] THEN
        ASM_SIMP_TAC[MATRIX_INV; MATRIX_MUL_RID];
        ALL_TAC] THEN
      SUBGOAL_THEN `(v:real^N) dot (transp(X:real^N^N) ** v) = v dot (X ** v)` ASSUME_TAC THENL
       [ONCE_REWRITE_TAC[DOT_SYM] THEN REWRITE_TAC[DOT_MATRIX_TRANSP_LMUL]; ALL_TAC] THEN
      SUBST1_TAC(SYM(ASSUME `t %% ((X:real^N^N) + transp X) - &2 %% mat 1:real^N^N = bs`)) THEN
      REWRITE_TAC[MATRIX_VECTOR_MUL_SUB_RDISTRIB; MATRIX_VECTOR_LMUL;
                  MATRIX_VECTOR_MUL_ADD_RDISTRIB; MATRIX_VECTOR_MUL_LID] THEN
      REWRITE_TAC[DOT_RSUB; DOT_RMUL; DOT_RADD] THEN
      REWRITE_TAC[ASSUME `(v:real^N) dot (transp(X:real^N^N) ** v) = v dot (X ** v)`] THEN
      REWRITE_TAC[ASSUME `v = inv t % ((A:real->real^N^N) t ** (c:real^N))`] THEN
      REWRITE_TAC[MATRIX_VECTOR_MUL_RMUL; DOT_LMUL; DOT_RMUL] THEN
      REWRITE_TAC[ASSUME `(X:real^N^N) ** (A:real->real^N^N) t ** (c:real^N) =
                          (B:real->real^N^N) t ** c`] THEN
      MP_TAC(ISPECL [`(B:real->real^N^N) t ** c`; `(A:real->real^N^N) t ** (c:real^N)`]
        DOT_SYM) THEN
      DISCH_THEN SUBST1_TAC THEN
      UNDISCH_TAC `&0 < t` THEN CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[CMPH_TRACE_CONGRUENCE] THEN
  SUBST1_TAC(SYM(ASSUME `t %% ((X:real^N^N) + transp X) - &2 %% mat 1:real^N^N = bs`)) THEN
  REWRITE_TAC[TRACE_SUB; TRACE_CMUL; TRACE_ADD; TRACE_TRANSP; TRACE_I] THEN
  REAL_ARITH_TAC);;

let CMPH_LLAP_RAY = prove
 (`!U (G:real^N->real^N^N) w (P:real^N^N) (A:real->real^N^N) B R L eta.
        metric_field U G /\ w IN U /\ (!z. z IN U ==> G z ** z = z) /\
        &0 < norm w /\ norm w < L /\ &0 < eta /\
        orthogonal_matrix P /\ cmp_jsys A B R L /\ invertible(A(norm w)) /\
        (!s a. abs(s - norm w) < eta /\ &0 < s
               ==> a dot (G(s % inv(norm w) % w) ** a) =
                   ((A s ** (transp P ** a)) dot (A s ** (transp P ** a))) / s pow 2)
        ==> llap G (\z. norm z) w =
            trace(B(norm w) ** matrix_inv(A(norm w))) - inv(norm w)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `w:real^N`] CMPH_LLAP_NORM) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[GSYM NORM_POS_LT]; DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `w:real^N`; `P:real^N^N`;
                 `A:real->real^N^N`; `B:real->real^N^N`; `R:real->real^N^N`; `L:real`;
                 `eta:real`] CMPH_RAY_TRACE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  UNDISCH_TAC `&0 < norm(w:real^N)` THEN CONV_TAC REAL_FIELD);;

(* ========================================================================= *)
(* Jacobi data along a ray of the exp pullback with the Ricci                *)
(* trace bound (CMPR_RAY_DATA_SEC with Ric >= -(n-1) K in place of sec <=  *)
(* K).                                                                       *)
(* ========================================================================= *)

let CMPH_RAY_DATA_RIC = prove
 (`!top atlas (g:A->real^N^N) (x:A) (E:real^N^N) K rho w.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ x IN topspace top /\
        mfd_orthonormal_frame g x E /\ &0 < rho /\
        mfd_tball g x rho SUBSET mfd_exp_dom (top,atlas) g x /\
        (!y v. y IN topspace top
               ==> --(&(dimindex(:N) - 1) * K) * (v dot (g y ** v)) <=
                   mfd_ricci atlas g y v v) /\
        &0 < norm w
        ==> ?P A B R.
              orthogonal_matrix P /\ P ** basis 1 = inv(norm w) % w /\
              cmp_jsys A B R rho /\
              (!t. &0 <= t /\ t < rho
                   ==> --(&(dimindex(:N) - 1) * K) <= trace(R t)) /\
              (!s a. &0 < s /\ s < rho
                     ==> a dot (cmp_expmetric (top,atlas) g x E (s % inv(norm w) % w) ** a) =
                         ((A s ** (transp P ** a)) dot (A s ** (transp P ** a))) / s pow 2)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `u:real^N = inv(norm w) % w` THEN
  SUBGOAL_THEN `norm(u:real^N) = &1` ASSUME_TAC THENL
   [EXPAND_TAC "u" THEN REWRITE_TAC[NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM] THEN
    ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ];
    ALL_TAC] THEN
  SUBGOAL_THEN `?P:real^N^N. orthogonal_matrix P /\ P ** basis 1 = u` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`basis 1:real^N`; `u:real^N`] ORTHOGONAL_TRANSFORMATION_EXISTS_1) THEN
    ASM_SIMP_TAC[NORM_BASIS; DIMINDEX_GE_1; LE_REFL] THEN
    DISCH_THEN(X_CHOOSE_THEN `f:real^N->real^N` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `matrix(f:real^N->real^N)` THEN
    FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [ORTHOGONAL_TRANSFORMATION]) THEN
    ASM_SIMP_TAC[MATRIX_WORKS] THEN ASM_MESON_TAC[ORTHOGONAL_TRANSFORMATION_MATRIX];
    ALL_TAC] THEN
  EXISTS_TAC `P:real^N^N` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `(E:real^N^N) ** u`] MFD_GEO_MAXIMAL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `E:real^N^N`; `P:real^N^N`; `u:real^N`]
    CMPP_FRAME_ALONG) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `Fr:num->real->real^N` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `mfd_geo (top,atlas) (g:A->real^N^N) x ((E:real^N^N) ** u)`;
                 `mfd_geo_maxint (top,atlas) (g:A->real^N^N) x ((E:real^N^N) ** u)`;
                 `Fr:num->real->real^N`] CMPP_JACOBI_ALONG) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `Y:num->real->real^N` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `E:real^N^N`; `u:real^N`; `rho:real`]
    CMPP_RADIAL) THEN
  ASM_REWRITE_TAC[REAL_MUL_RID] THEN DISCH_THEN(LABEL_TAC "rad") THEN
  EXISTS_TAC `cmp_fmat (\j. cmp_fcoord (g:A->real^N^N)
                (mfd_geo (top,atlas) g x ((E:real^N^N) ** u)) (Fr:num->real->real^N)
                ((Y:num->real->real^N) j))` THEN
  EXISTS_TAC `cmp_fmat (\j. cmp_fcoord (g:A->real^N^N)
                (mfd_geo (top,atlas) g x ((E:real^N^N) ** u)) (Fr:num->real->real^N)
                (mfd_covd atlas g (mfd_geo (top,atlas) g x (E ** u))
                   ((Y:num->real->real^N) j)))` THEN
  EXISTS_TAC `cmp_rmat atlas (g:A->real^N^N)
                (mfd_geo (top,atlas) g x ((E:real^N^N) ** u)) (Fr:num->real->real^N)` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CMPJ_FRAME_JSYS THEN
    MAP_EVERY EXISTS_TAC
     [`top:A topology`;
      `mfd_geo_maxint (top,atlas) (g:A->real^N^N) x ((E:real^N^N) ** u)`] THEN
    ASM_SIMP_TAC[] THEN X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    USE_THEN "rad" (MP_TAC o SPEC `t:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    USE_THEN "rad" (MP_TAC o SPEC `t:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    SUBGOAL_THEN `mfd_geo (top,atlas) (g:A->real^N^N) x ((E:real^N^N) ** u) t IN topspace top`
    ASSUME_TAC THENL
     [MATCH_MP_TAC GEOL_GEODESIC_IN_TOPSPACE THEN
      MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                            `mfd_geo_maxint (top,atlas) (g:A->real^N^N) x ((E:real^N^N) ** u)`] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`;
                   `mfd_geo (top,atlas) (g:A->real^N^N) x ((E:real^N^N) ** u)`;
                   `mfd_geo_maxint (top,atlas) (g:A->real^N^N) x ((E:real^N^N) ** u)`;
                   `Fr:num->real->real^N`; `t:real`] CMPJ_FRAME_RICCI) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `--k * &1 <= r ==> --k <= r`) THEN
    SUBGOAL_THEN
     `mfd_vel atlas (mfd_geo (top,atlas) (g:A->real^N^N) x ((E:real^N^N) ** u)) t dot
      (g(mfd_geo (top,atlas) g x (E ** u) t) **
       mfd_vel atlas (mfd_geo (top,atlas) g x (E ** u)) t) = &1`
    (fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [SYM th]) THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `g:A->real^N^N`;
                     `mfd_geo (top,atlas) (g:A->real^N^N) x ((E:real^N^N) ** u) t`]
        GEOD_TNORM_BASIC) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o SPEC `mfd_vel (atlas:((A->bool)#(A->real^N))->bool)
                   (mfd_geo (top,atlas) (g:A->real^N^N) x ((E:real^N^N) ** u)) t` o
                 CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `g:A->real^N^N`;
                     `mfd_geo (top,atlas) (g:A->real^N^N) x ((E:real^N^N) ** u)`;
                     `mfd_geo_maxint (top,atlas) (g:A->real^N^N) x ((E:real^N^N) ** u)`;
                     `t:real`; `&0`] MFD_GEODESIC_SPEED) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      ASM_SIMP_TAC[CMPP_TNORM_FRAME] THEN REAL_ARITH_TAC;
      ASM_SIMP_TAC[]];
    MAP_EVERY X_GEN_TAC [`s:real`; `a:real^N`] THEN STRIP_TAC THEN
    MATCH_MP_TAC CMPP_RAY_IDENTITY THEN EXISTS_TAC `rho:real` THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    MATCH_MP_TAC MFD_EXP_DIFFERENTIAL_JACOBI_RAY THEN
    REWRITE_TAC[ETA_AX] THEN ASM_SIMP_TAC[] THEN
    USE_THEN "rad" (MP_TAC o SPEC `s:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]]]);;

let CMPH_TRACE_BOUND = prove
 (`!(A:real->real^N^N) B R L K t.
        cmp_jsys A B R L /\ &0 <= K /\
        (!s. &0 <= s /\ s < L ==> --(&(dimindex(:N) - 1) * K) <= trace(R s)) /\
        (!s. &0 < s /\ s < L ==> invertible(A s)) /\ &0 < t /\ t < L
        ==> trace(B t ** matrix_inv(A t)) - inv t <=
            &(dimindex(:N) - 1) * (inv t + sqrt K)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!s. &0 < s ==> &0 < cmp_sn (--K) s` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC CMP_SN_POS THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`A:real->real^N^N`; `B:real->real^N^N`; `R:real->real^N^N`;
                 `L:real`; `K:real`] CMPJ_TRACE_UPPER) THEN
  ASM_SIMP_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `t:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  MP_TAC(SPECL [`K:real`; `t:real`] CMP_CT_UPPER_NEG_SQRT) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  MATCH_MP_TAC REAL_LE_RCANCEL_IMP THEN EXISTS_TAC `cmp_sn (--K) t` THEN
  ASM_SIMP_TAC[] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&(dimindex(:N) - 1) * cmp_cs (--K) t` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
  ASM_REWRITE_TAC[REAL_POS]);;

(* ========================================================================= *)
(* exp_q in the chart at exp_q(E w0), composed with a frame E,               *)
(* is a diffeomorphism near w0 when d exp_q is injective at E w0 (the        *)
(* smooth inverse function theorem SMOOTH_INVERSE_FUNCTION_THEOREM).         *)
(* ========================================================================= *)

let CMPH_EXP_CHART_SMOOTH = prove
 (`!top atlas (g:A->real^N^N) (q:A) (c:(A->bool)#(A->real^N)).
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ q IN topspace top /\ c IN atlas
        ==> open {v | v IN mfd_exp_dom (top,atlas) g q /\
                      mfd_exp (top,atlas) g q v IN FST c} /\
            smooth_map_on {v | v IN mfd_exp_dom (top,atlas) g q /\
                               mfd_exp (top,atlas) g q v IN FST c}
              (\v. SND c (mfd_exp (top,atlas) g q v))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `q:A`; `c:(A->bool)#(A->real^N)`] CMPP_EXP_CHART_OPEN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `q:A`] MFD_EXP_SMOOTH) THEN
  ASM_REWRITE_TAC[mfd_smooth_map; open_set_atlas; IN_SING] THEN
  DISCH_THEN(MP_TAC o SPECL [`(:real^N),(\x:real^N. x)`; `c:(A->bool)#(A->real^N)`] o
             CONJUNCT2) THEN
  ASM_REWRITE_TAC[IMAGE_ID; INTER_UNIV; IN_UNIV] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] SMOOTH_MAP_ON_EQ) THEN
  REWRITE_TAC[IN_ELIM_THM; o_THM] THEN
  SIMP_TAC[MFDM_CHART_INV_ID; IN_UNIV]);;

let CMPH_EXP_FRAME_DIFFEO = prove
 (`!top atlas (g:A->real^N^N) (q:A) (E:real^N^N) w0.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ q IN topspace top /\ invertible E /\
        E ** w0 IN mfd_exp_dom (top,atlas) g q /\
        (!h. mfd_differential (open_set_atlas (:real^N)) atlas
               (mfd_exp (top,atlas) g q) (E ** w0) h = vec 0 ==> h = vec 0)
        ==> ?t u Fi.
              open t /\ w0 IN t /\ open u /\
              (!w. w IN t
                   ==> E ** w IN mfd_exp_dom (top,atlas) g q /\
                       mfd_exp (top,atlas) g q (E ** w) IN
                       FST(chart_at atlas (mfd_exp (top,atlas) g q (E ** w0)))) /\
              diffeomorphism_on t u
                (\w. SND(chart_at atlas (mfd_exp (top,atlas) g q (E ** w0)))
                        (mfd_exp (top,atlas) g q (E ** w))) Fi`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `c = chart_at atlas (mfd_exp (top,atlas) (g:A->real^N^N) (q:A) ((E:real^N^N) ** (w0:real^N)))` THEN
  SUBGOAL_THEN `mfd_exp (top,atlas) (g:A->real^N^N) (q:A) ((E:real^N^N) ** (w0:real^N)) IN topspace top`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CMPP_EXP_IN_TOPSPACE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `mfd_exp (top,atlas) (g:A->real^N^N) (q:A) ((E:real^N^N) ** (w0:real^N))`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `q:A`; `c:(A->bool)#(A->real^N)`] CMPH_EXP_CHART_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `S = {w | (E:real^N^N) ** w IN
                       {v | v IN mfd_exp_dom (top,atlas) (g:A->real^N^N) (q:A) /\
                            mfd_exp (top,atlas) g q v IN FST (c:(A->bool)#(A->real^N))}}` THEN
  SUBGOAL_THEN `open (S:real^N->bool) /\ (w0:real^N) IN S` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE_UNIV THEN ASM_REWRITE_TAC[] THEN
      GEN_TAC THEN MATCH_MP_TAC LINEAR_CONTINUOUS_AT THEN
      REWRITE_TAC[MATRIX_VECTOR_MUL_LINEAR];
      ASM_REWRITE_TAC[IN_ELIM_THM]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on S (\w. SND (c:(A->bool)#(A->real^N))
                       (mfd_exp (top,atlas) (g:A->real^N^N) (q:A) ((E:real^N^N) ** w)))`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `(\w. SND (c:(A->bool)#(A->real^N))
             (mfd_exp (top,atlas) (g:A->real^N^N) (q:A) ((E:real^N^N) ** w))) =
      (\v. SND c (mfd_exp (top,atlas) g q v)) o (\w. E ** w)`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
    EXISTS_TAC `{v | v IN mfd_exp_dom (top,atlas) (g:A->real^N^N) (q:A) /\
                     mfd_exp (top,atlas) g q v IN FST (c:(A->bool)#(A->real^N))}` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [EXPAND_TAC "S" THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
      SIMP_TAC[];
      SUBGOAL_THEN `(\w:real^N. (E:real^N^N) ** w) = (\w. E ** w) o (\w. w)` SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_LINEAR_O THEN
      ASM_REWRITE_TAC[SMOOTH_MAP_ON_ID; MATRIX_VECTOR_MUL_LINEAR]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\w. SND (c:(A->bool)#(A->real^N))
            (mfd_exp (top,atlas) (g:A->real^N^N) (q:A) ((E:real^N^N) ** w))) has_derivative
     (\h. mfd_differential (open_set_atlas (:real^N)) atlas (mfd_exp (top,atlas) g q)
            (E ** w0) (E ** h))) (at w0)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `q:A`; `(E:real^N^N) ** (w0:real^N)`;
                   `c:(A->bool)#(A->real^N)`] CMPP_EXP_CHART_DERIV) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`;
                   `mfd_exp (top,atlas) (g:A->real^N^N) (q:A) ((E:real^N^N) ** (w0:real^N))`]
      CHART_JAC_SELF) THEN
    REWRITE_TAC[PAIR] THEN ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[ETA_AX] THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `(\w. SND (c:(A->bool)#(A->real^N))
             (mfd_exp (top,atlas) (g:A->real^N^N) (q:A) ((E:real^N^N) ** w))) =
      (\v. SND c (mfd_exp (top,atlas) g q v)) o (\w. E ** w)`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    SUBGOAL_THEN
     `(\h. mfd_differential (open_set_atlas (:real^N)) atlas
             (mfd_exp (top,atlas) (g:A->real^N^N) (q:A)) ((E:real^N^N) ** w0) (E ** h)) =
      mfd_differential (open_set_atlas (:real^N)) atlas (mfd_exp (top,atlas) g q)
        (E ** w0) o (\h. E ** h)`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC DIFF_CHAIN_AT THEN CONJ_TAC THENL
     [MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN REWRITE_TAC[MATRIX_VECTOR_MUL_LINEAR];
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\w. SND (c:(A->bool)#(A->real^N))
                        (mfd_exp (top,atlas) (g:A->real^N^N) (q:A) ((E:real^N^N) ** w))`;
                 `S:real^N->bool`; `w0:real^N`] SMOOTH_INVERSE_FUNCTION_THEOREM) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
    SUBGOAL_THEN
     `linear (\h. mfd_differential (open_set_atlas (:real^N)) atlas
                    (mfd_exp (top,atlas) (g:A->real^N^N) (q:A)) ((E:real^N^N) ** w0) (E ** h))`
    ASSUME_TAC THENL
     [SUBGOAL_THEN
       `(\h. mfd_differential (open_set_atlas (:real^N)) atlas
               (mfd_exp (top,atlas) (g:A->real^N^N) (q:A)) ((E:real^N^N) ** w0) (E ** h)) =
        mfd_differential (open_set_atlas (:real^N)) atlas (mfd_exp (top,atlas) g q)
          (E ** w0) o (\h. E ** h)`
      SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC LINEAR_COMPOSE THEN REWRITE_TAC[MATRIX_VECTOR_MUL_LINEAR] THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `g:A->real^N^N`; `q:A`; `(E:real^N^N) ** (w0:real^N)`] CMPP_EXP_DIFF) THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    ASM_SIMP_TAC[DET_MATRIX_EQ_0_LEFT] THEN
    MATCH_MP_TAC LINEAR_INJECTIVE_LEFT_INVERSE THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real^N`] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `q:A`; `(E:real^N^N) ** (w0:real^N)`] CMPP_EXP_DIFF) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(E:real^N^N) ** (a - b) = vec 0` MP_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        is_forall(concl th) && can (find_term ((=) `vec 0:real^N`)) (concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_differential"))
            (concl th))) THEN
      REWRITE_TAC[MATRIX_VECTOR_MUL_SUB_LDISTRIB] THEN
      FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LINEAR_SUB th]) THEN
      ASM_REWRITE_TAC[VECTOR_SUB_REFL];
      ALL_TAC] THEN
    DISCH_TAC THEN
    MATCH_MP_TAC(VECTOR_ARITH `a - b:real^N = vec 0 ==> a = b`) THEN
    MATCH_MP_TAC CMPR_INVERTIBLE_KER THEN EXISTS_TAC `E:real^N^N` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` (X_CHOOSE_THEN `u:real^N->bool`
    (X_CHOOSE_THEN `Fi:real^N->real^N` STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`t:real^N->bool`; `u:real^N->bool`; `Fi:real^N->real^N`] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `w:real^N` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(w:real^N) IN S` MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  EXPAND_TAC "S" THEN REWRITE_TAC[IN_ELIM_THM]);;

(* ========================================================================= *)
(* Helpers for the barrier.  Restricting a diffeomorphism,                   *)
(* monotonicity of cmp_jsys, invertibility of A(s) is open in s, A(s) is     *)
(* invertible where d exp is injective along the ray, dist(x,exp_x v) is at  *)
(* most |v|_x, and functions of the chart coordinates are mfd_smooth_on.     *)
(* ========================================================================= *)

let CMPH_DIFFEO_RESTRICT = prove
 (`!s t s' (f:real^N->real^N) g.
        diffeomorphism_on s t f g /\ open s' /\ s' SUBSET s
        ==> diffeomorphism_on s' (IMAGE f s') f g`,
  REPEAT GEN_TAC THEN REWRITE_TAC[diffeomorphism_on] THEN STRIP_TAC THEN
  SUBGOAL_THEN `open (IMAGE (f:real^N->real^N) s')` ASSUME_TAC THENL
   [SUBGOAL_THEN `IMAGE (f:real^N->real^N) s' = {y | y IN t /\ (g:real^N->real^N) y IN s'}`
    SUBST1_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on s' (f:real^N->real^N) /\
                smooth_map_on (IMAGE f s') (g:real^N->real^N)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THENL
     [EXISTS_TAC `s:real^N->bool`; EXISTS_TAC `t:real^N->bool`] THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

let CMPH_JSYS_MONO = prove
 (`!(A:real->real^N^N) B R L L'.
        cmp_jsys A B R L /\ &0 < L' /\ L' <= L ==> cmp_jsys A B R L'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cmp_jsys] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `t:real` THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REAL_ARITH_TAC);;

let CMPH_JSYS_INV_NEAR = prove
 (`!(A:real->real^N^N) B R L t.
        cmp_jsys A B R L /\ &0 <= t /\ t < L /\ invertible(A t)
        ==> ?eps. &0 < eps /\ !s. abs(s - t) < eps ==> invertible(A s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cmp_jsys] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `t:real`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(\s. vectorize((A:real->real^N^N)(drop s))) continuous (at (lift t))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN REWRITE_TAC[differentiable] THEN
    EXISTS_TAC `\x:real^1. drop x % vectorize((B:real->real^N^N) t)` THEN
    ASM_REWRITE_TAC[GSYM has_vector_derivative];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`at (lift t)`; `\s:real^1. (A:real->real^N^N)(drop s)`]
    CONTINUOUS_DET_VECTORIZE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `vec 0:real^1` o
    MATCH_MP (REWRITE_RULE[IMP_CONJ] CONTINUOUS_AT_AVOID)) THEN
  ASM_REWRITE_TAC[LIFT_DROP; GSYM LIFT_NUM; LIFT_EQ; GSYM INVERTIBLE_DET_NZ] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `e:real` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `s:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `lift s`) THEN
  REWRITE_TAC[LIFT_DROP; DIST_LIFT] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC);;

let CMPH_RAY_INVERTIBLE = prove
 (`!top atlas (g:A->real^N^N) (q:A) (E:real^N^N) (P:real^N^N) (A:real^N^N) s w.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ q IN topspace top /\ invertible E /\
        E ** w IN mfd_exp_dom (top,atlas) g q /\ orthogonal_matrix P /\ &0 < s /\
        (!a. a dot (cmp_expmetric (top,atlas) g q E w ** a) =
             ((A ** (transp P ** a)) dot (A ** (transp P ** a))) / s pow 2) /\
        (!h. mfd_differential (open_set_atlas (:real^N)) atlas
               (mfd_exp (top,atlas) g q) (E ** w) h = vec 0 ==> h = vec 0)
        ==> invertible A`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [orthogonal_matrix]) THEN
  REWRITE_TAC[INVERTIBLE_LEFT_INVERSE; MATRIX_LEFT_INVERTIBLE_KER] THEN
  X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
  SUBGOAL_THEN `transp(P:real^N^N) ** (P ** (y:real^N)) = y` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_ASSOC; MATRIX_VECTOR_MUL_LID]; ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_differential (open_set_atlas (:real^N)) atlas
      (mfd_exp (top,atlas) (g:A->real^N^N) q) ((E:real^N^N) ** w)
      (E ** ((P:real^N^N) ** (y:real^N))) dot
    (g(mfd_exp (top,atlas) g q (E ** w)) **
     mfd_differential (open_set_atlas (:real^N)) atlas
       (mfd_exp (top,atlas) g q) (E ** w) (E ** (P ** y))) = &0`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `q:A`; `E:real^N^N`; `w:real^N`;
                   `(P:real^N^N) ** (y:real^N)`; `(P:real^N^N) ** (y:real^N)`]
      CMPP_EXPMETRIC_DOT) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
    ASM_REWRITE_TAC[DOT_LZERO; real_div; REAL_MUL_LZERO];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`;
                 `mfd_exp (top,atlas) (g:A->real^N^N) q ((E:real^N^N) ** w)`]
    RIEMANNIAN_METRIC_POS) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[CMPP_EXP_IN_TOPSPACE]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC
    `mfd_differential (open_set_atlas (:real^N)) atlas
       (mfd_exp (top,atlas) (g:A->real^N^N) q) ((E:real^N^N) ** w)
       (E ** ((P:real^N^N) ** (y:real^N)))` o
    CONJUNCT2) THEN
  ASM_REWRITE_TAC[REAL_LT_REFL] THEN
  REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `(E:real^N^N) ** ((P:real^N^N) ** y) = vec 0` ASSUME_TAC THENL
   [UNDISCH_TAC
     `!h. mfd_differential (open_set_atlas (:real^N)) atlas
            (mfd_exp (top,atlas) (g:A->real^N^N) q) ((E:real^N^N) ** w) h = vec 0
          ==> h = vec 0` THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(P:real^N^N) ** (y:real^N) = vec 0` ASSUME_TAC THENL
   [MATCH_MP_TAC CMPR_INVERTIBLE_KER THEN EXISTS_TAC `E:real^N^N` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `transp(P:real^N^N) ** (P ** (y:real^N)) = y` THEN
  ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_RZERO] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REFL_TAC);;

let CMPH_EXP_DIST_LE = prove
 (`!top atlas (g:A->real^N^N) (x:A) v.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ x IN topspace top /\
        v IN mfd_exp_dom (top,atlas) g x
        ==> mfd_joinable (top,atlas) x (mfd_exp (top,atlas) g x v) /\
            mfd_dist (top,atlas) g x (mfd_exp (top,atlas) g x v) <= mfd_tnorm g x v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `v:real^N`] CMPS_RAY_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 IN mfd_geo_maxint (top,atlas) (g:A->real^N^N) x v /\
                &1 IN mfd_geo_maxint (top,atlas) g x v` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN
    UNDISCH_TAC `real_interval[&0,&1] SUBSET mfd_geo_maxint (top,atlas) (g:A->real^N^N) x v` THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[IN_REAL_INTERVAL] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_exp (top,atlas) (g:A->real^N^N) x v = mfd_geo (top,atlas) g x v (&1)`
  SUBST1_TAC THENL
   [UNDISCH_TAC
     `!s. &0 <= s /\ s <= &1
          ==> s % v IN mfd_exp_dom (top,atlas) (g:A->real^N^N) x /\
              mfd_exp (top,atlas) g x (s % v) = mfd_geo (top,atlas) g x v s` THEN
    DISCH_THEN(MP_TAC o SPEC `&1`) THEN
    REWRITE_TAC[REAL_POS; REAL_LE_REFL; VECTOR_MUL_LID] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `mfd_geo (top,atlas) (g:A->real^N^N) x v`;
                 `mfd_geo_maxint (top,atlas) (g:A->real^N^N) x v`; `&0`; `&1`]
    GEOH_GEO_SEG_DIST) THEN
  ASM_REWRITE_TAC[REAL_SUB_RZERO; REAL_ABS_NUM; REAL_MUL_LID] THEN MESON_TAC[]);;

let CMPH_MFD_SMOOTH_ON_CHART = prove
 (`!top atlas (c:(A->bool)#(A->real^N)) V (h:real^N->real^K).
        smooth_manifold_atlas top atlas /\ c IN atlas /\ open V /\
        V SUBSET IMAGE (SND c) (FST c) /\ smooth_map_on V h
        ==> mfd_smooth_on atlas {y | y IN FST c /\ SND c y IN V} (\y. h(SND c y))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[mfd_smooth_on] THEN
  X_GEN_TAC `c':(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(\y. (h:real^N->real^K)(SND (c:(A->bool)#(A->real^N)) y)) o
                chart_inv (c':(A->bool)#(A->real^N)) = h o chart_trans c' c`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM; chart_trans]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c':(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `open_in top {y:A | y IN FST (c:(A->bool)#(A->real^N)) /\ SND c y IN V}`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`;
                   `V:real^N->bool`] GRGD_CHART_PREIMAGE_OPEN) THEN
    ASM_REWRITE_TAC[PAIR];
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `V:real^N->bool` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MFDM_CHART_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
    ASM_REWRITE_TAC[INTER_SUBSET] THEN MATCH_MP_TAC OPEN_IN_INTER THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTER; IN_ELIM_THM; chart_trans] THEN
    ASM_SIMP_TAC[];
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
    EXISTS_TAC `IMAGE (SND(c':(A->bool)#(A->real^N))) (FST c' INTER FST(c:(A->bool)#(A->real^N)))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC IMAGE_SUBSET THEN SET_TAC[];
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `FST(c':(A->bool)#(A->real^N))`; `SND(c':(A->bool)#(A->real^N))`;
                     `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`]
        CHART_TRANS_SMOOTH) THEN
      ASM_REWRITE_TAC[PAIR]]]);;

(* ========================================================================= *)
(* Transfer of the Laplacian and of |grad|^2 of y -> h(Fi(SND c              *)
(* y)) from the chart c to the exp pullback metric, where Fi inverts         *)
(* w -> SND c (exp_q(E w)) on an open set t and h is smooth on t; the case   *)
(* h(w) = c0 + |w| on a set t avoiding 0 (used for S7).                      *)
(* ========================================================================= *)

let CMPH_CHART_TRANSFER_GEN = prove
 (`!top atlas (g:A->real^N^N) (q:A) (E:real^N^N) (c:(A->bool)#(A->real^N))
    t u (Fi:real^N->real^N) (h:real^N->real) w0.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ q IN topspace top /\ c IN atlas /\
        (!w. w IN t ==> E ** w IN mfd_exp_dom (top,atlas) g q /\
                        mfd_exp (top,atlas) g q (E ** w) IN FST c) /\
        diffeomorphism_on t u (\w. SND c (mfd_exp (top,atlas) g q (E ** w))) Fi /\
        smooth_map_on t (\z. lift(h z)) /\ w0 IN t
        ==> u SUBSET IMAGE (SND c) (FST c) /\
            smooth_map_on u (\z. lift(h(Fi z))) /\
            metric_field t (cmp_expmetric (top,atlas) g q E) /\
            llap (metric_local atlas c g) ((\y. h(Fi(SND c y))) o chart_inv c)
                 (SND c (mfd_exp (top,atlas) g q (E ** w0))) =
            llap (cmp_expmetric (top,atlas) g q E) h w0 /\
            lgrad2 (metric_local atlas c g) ((\y. h(Fi(SND c y))) o chart_inv c)
                 (SND c (mfd_exp (top,atlas) g q (E ** w0))) =
            lgrad2 (cmp_expmetric (top,atlas) g q E) h w0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `Fm = \w. SND (c:(A->bool)#(A->real^N))
                       (mfd_exp (top,atlas) (g:A->real^N^N) (q:A) ((E:real^N^N) ** w))` THEN
  SUBGOAL_THEN `!w. (Fm:real^N->real^N) w =
                    SND (c:(A->bool)#(A->real^N))
                      (mfd_exp (top,atlas) (g:A->real^N^N) (q:A) ((E:real^N^N) ** w))`
  ASSUME_TAC THENL [EXPAND_TAC "Fm" THEN REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [diffeomorphism_on]) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `u SUBSET IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)` ASSUME_TAC THENL
   [UNDISCH_TAC `IMAGE (Fm:real^N->real^N) t = u` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `w:real^N` THEN DISCH_TAC THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on u (\z. lift((h:real^N->real)((Fi:real^N->real^N) z)))`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `(\z. lift((h:real^N->real)((Fi:real^N->real^N) z))) =
                  (\z. lift(h z)) o Fi`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `t:real^N->bool` THEN
    ASM_REWRITE_TAC[SUBSET_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `metric_field u (metric_local atlas (c:(A->bool)#(A->real^N)) (g:A->real^N^N))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN
    EXISTS_TAC `IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)` THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `riemannian_metric atlas (g:A->real^N^N)` THEN
    REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!w. w IN t
        ==> mpullback (Fm:real^N->real^N)
              (metric_local atlas (c:(A->bool)#(A->real^N)) (g:A->real^N^N)) w =
            cmp_expmetric (top,atlas) g (q:A) (E:real^N^N) w`
  ASSUME_TAC THENL
   [X_GEN_TAC `w:real^N` THEN DISCH_TAC THEN EXPAND_TAC "Fm" THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC CMPP_EXPMETRIC_LOCAL THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `metric_field t (cmp_expmetric (top,atlas) (g:A->real^N^N) (q:A) (E:real^N^N))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MFDR_METRIC_FIELD_EQ THEN
    EXISTS_TAC `mpullback (Fm:real^N->real^N)
                  (metric_local atlas (c:(A->bool)#(A->real^N)) (g:A->real^N^N))` THEN
    ASM_SIMP_TAC[] THEN MATCH_MP_TAC METRIC_FIELD_PULLBACK THEN
    MAP_EVERY EXISTS_TAC [`u:real^N->bool`; `Fi:real^N->real^N`] THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "Fm" THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `SND (c:(A->bool)#(A->real^N))
      (mfd_exp (top,atlas) (g:A->real^N^N) (q:A) ((E:real^N^N) ** w0)) =
    (Fm:real^N->real^N) w0`
  SUBST1_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(Fm:real^N->real^N) w0 IN u` ASSUME_TAC THENL
   [UNDISCH_TAC `IMAGE (Fm:real^N->real^N) t = u` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z. z IN u
        ==> (metric_local atlas (c:(A->bool)#(A->real^N)) (g:A->real^N^N)) z =
            metric_local atlas c g z /\
            ((\y. (h:real^N->real)((Fi:real^N->real^N)(SND c y))) o chart_inv c) z =
            (\z. h(Fi z)) z`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN
    SUBGOAL_THEN `(z:real^N) IN IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)` MP_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!w. w IN t
        ==> mpullback (Fm:real^N->real^N)
              (metric_local atlas (c:(A->bool)#(A->real^N)) (g:A->real^N^N)) w =
            cmp_expmetric (top,atlas) g (q:A) (E:real^N^N) w /\
            ((\z. (h:real^N->real)((Fi:real^N->real^N) z)) o Fm) w = h w`
  ASSUME_TAC THENL
   [X_GEN_TAC `w:real^N` THEN DISCH_TAC THEN ASM_SIMP_TAC[o_THM];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `llap (metric_local atlas (c:(A->bool)#(A->real^N)) (g:A->real^N^N))
                     (\z. (h:real^N->real)((Fi:real^N->real^N) z))
                     ((Fm:real^N->real^N) w0)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LLAP_LOCAL THEN EXISTS_TAC `u:real^N->bool` THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`u:real^N->bool`; `t:real^N->bool`; `Fm:real^N->real^N`;
                   `Fi:real^N->real^N`;
                   `metric_local atlas (c:(A->bool)#(A->real^N)) (g:A->real^N^N)`;
                   `\z. (h:real^N->real)((Fi:real^N->real^N) z)`; `w0:real^N`]
      LLAP_PULLBACK) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
    MATCH_MP_TAC LLAP_LOCAL THEN EXISTS_TAC `t:real^N->bool` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `lgrad2 (metric_local atlas (c:(A->bool)#(A->real^N)) (g:A->real^N^N))
                     (\z. (h:real^N->real)((Fi:real^N->real^N) z))
                     ((Fm:real^N->real^N) w0)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LGRAD2_LOCAL THEN EXISTS_TAC `u:real^N->bool` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`u:real^N->bool`; `t:real^N->bool`; `Fm:real^N->real^N`;
                 `Fi:real^N->real^N`;
                 `metric_local atlas (c:(A->bool)#(A->real^N)) (g:A->real^N^N)`;
                 `\z. (h:real^N->real)((Fi:real^N->real^N) z)`; `w0:real^N`]
    LGRAD2_PULLBACK) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
  MATCH_MP_TAC LGRAD2_LOCAL THEN EXISTS_TAC `t:real^N->bool` THEN ASM_SIMP_TAC[]);;

let CMPH_CHART_TRANSFER = prove
 (`!top atlas (g:A->real^N^N) (q:A) (E:real^N^N) (c:(A->bool)#(A->real^N))
    t u (Fi:real^N->real^N) c0 w0.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ q IN topspace top /\ c IN atlas /\
        (!w. w IN t ==> E ** w IN mfd_exp_dom (top,atlas) g q /\
                        mfd_exp (top,atlas) g q (E ** w) IN FST c) /\
        (!w. w IN t ==> ~(w = vec 0)) /\
        diffeomorphism_on t u (\w. SND c (mfd_exp (top,atlas) g q (E ** w))) Fi /\
        w0 IN t
        ==> u SUBSET IMAGE (SND c) (FST c) /\
            smooth_map_on u (\z. lift(c0 + norm(Fi z))) /\
            metric_field t (cmp_expmetric (top,atlas) g q E) /\
            llap (metric_local atlas c g)
                 ((\y. c0 + norm(Fi(SND c y))) o chart_inv c)
                 (SND c (mfd_exp (top,atlas) g q (E ** w0))) =
            llap (cmp_expmetric (top,atlas) g q E) (\z. norm z) w0 /\
            lgrad2 (metric_local atlas c g)
                 ((\y. c0 + norm(Fi(SND c y))) o chart_inv c)
                 (SND c (mfd_exp (top,atlas) g q (E ** w0))) =
            lgrad2 (cmp_expmetric (top,atlas) g q E) (\z. norm z) w0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [diffeomorphism_on]) THEN
  SUBGOAL_THEN `smooth_map_on t (\z:real^N. lift(norm z))` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`t:real^N->bool`; `\z:real^N. z`] SMOOTH_MAP_ON_LIFT_NORM) THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_ID];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on t (\z:real^N. lift((c0:real) + norm z))` ASSUME_TAC THENL
   [REWRITE_TAC[LIFT_ADD] THEN MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN
    ASM_REWRITE_TAC[SMOOTH_MAP_ON_CONST];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `q:A`; `E:real^N^N`; `c:(A->bool)#(A->real^N)`;
                 `t:real^N->bool`; `u:real^N->bool`; `Fi:real^N->real^N`;
                 `\z:real^N. (c0:real) + norm z`; `w0:real^N`] CMPH_CHART_TRANSFER_GEN) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!x. ((\r. (c0:real) + r) has_real_derivative &1) (atreal x) /\
                    ((\r:real. &1) has_real_derivative &0) (atreal x)`
  ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[HAS_REAL_DERIVATIVE_CONST] THEN
    MP_TAC(ISPECL [`\r:real. (c0:real)`; `&0`; `\r:real. r`; `&1`; `atreal x`]
      HAS_REAL_DERIVATIVE_ADD) THEN
    REWRITE_TAC[HAS_REAL_DERIVATIVE_CONST; HAS_REAL_DERIVATIVE_ID; REAL_ADD_LID];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`t:real^N->bool`; `(:real)`;
                   `cmp_expmetric (top,atlas) (g:A->real^N^N) (q:A) (E:real^N^N)`;
                   `\z:real^N. norm z`; `\r. (c0:real) + r`; `\r:real. &1`; `\r:real. &0`;
                   `w0:real^N`] RFA_LLAP_COMPOSE) THEN
    ASM_REWRITE_TAC[IN_UNIV] THEN
    REWRITE_TAC[REAL_MUL_LID; REAL_MUL_LZERO; REAL_ADD_RID];
    MP_TAC(ISPECL [`t:real^N->bool`;
                   `cmp_expmetric (top,atlas) (g:A->real^N^N) (q:A) (E:real^N^N)`;
                   `\z:real^N. norm z`; `\r. (c0:real) + r`; `&1`; `w0:real^N`]
      RFA_LGRAD2_COMPOSE) THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[REAL_POW_ONE; REAL_MUL_LID]]);;

(* ========================================================================= *)
(* The Laplacian of |w| for the exp pullback metric at a point               *)
(* w0 such that d exp_q is injective along the segment from 0 to E w0:       *)
(* llap <= (n-1)(1/|w0| + sqrt K) under Ric >= -(n-1)K, and lgrad2 = 1.      *)
(* ========================================================================= *)

let CMPH_RAY_LAP_BOUND = prove
 (`!top atlas (g:A->real^N^N) (q:A) (E:real^N^N) K t w0.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ q IN topspace top /\
        mfd_orthonormal_frame g q E /\ &0 <= K /\
        mfd_exp_dom (top,atlas) g q = (:real^N) /\
        (!y v. y IN topspace top
               ==> --(&(dimindex(:N) - 1) * K) * (v dot (g y ** v)) <=
                   mfd_ricci atlas g y v v) /\
        metric_field t (cmp_expmetric (top,atlas) g q E) /\ w0 IN t /\
        (!w. w IN t ==> ~(w = vec 0)) /\
        (!s h. &0 < s /\ s <= &1 /\
               mfd_differential (open_set_atlas (:real^N)) atlas
                 (mfd_exp (top,atlas) g q) (E ** (s % w0)) h = vec 0
               ==> h = vec 0)
        ==> llap (cmp_expmetric (top,atlas) g q E) (\z. norm z) w0 <=
            &(dimindex(:N) - 1) * (inv(norm w0) + sqrt K) /\
            lgrad2 (cmp_expmetric (top,atlas) g q E) (\z. norm z) w0 = &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(w0:real^N = vec 0)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < norm(w0:real^N)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `invertible(E:real^N^N)` ASSUME_TAC THENL
   [REWRITE_TAC[INVERTIBLE_LEFT_INVERSE] THEN
    EXISTS_TAC `transp(E:real^N^N) ** (g:A->real^N^N) q` THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [mfd_orthonormal_frame]) THEN
    REWRITE_TAC[GSYM MATRIX_MUL_ASSOC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z. z IN t ==> cmp_expmetric (top,atlas) (g:A->real^N^N) q E z ** z = z`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC CMPP_EXPMETRIC_GAUSS THEN
    ASM_REWRITE_TAC[IN_UNIV];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `q:A`; `E:real^N^N`; `K:real`; `norm(w0:real^N) + &1`; `w0:real^N`]
    CMPH_RAY_DATA_RIC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[SUBSET_UNIV] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`P:real^N^N`; `A:real->real^N^N`; `B:real->real^N^N`;
                       `R:real->real^N^N`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `!s. &0 < s /\ s <= norm(w0:real^N) ==> invertible((A:real->real^N^N) s)`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    MATCH_MP_TAC CMPH_RAY_INVERTIBLE THEN
    MAP_EVERY EXISTS_TAC
     [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
      `q:A`; `E:real^N^N`; `P:real^N^N`; `s:real`;
      `s % inv(norm(w0:real^N)) % w0`] THEN
    ASM_REWRITE_TAC[IN_UNIV] THEN CONJ_TAC THENL
     [X_GEN_TAC `a:real^N` THEN
      UNDISCH_TAC
       `!s a. &0 < s /\ s < norm(w0:real^N) + &1
              ==> a dot (cmp_expmetric (top,atlas) (g:A->real^N^N) q E
                           (s % inv(norm w0) % w0) ** a) =
                  (((A:real->real^N^N) s ** (transp (P:real^N^N) ** a)) dot
                   (A s ** (transp P ** a))) / s pow 2` THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[VECTOR_MUL_ASSOC] THEN X_GEN_TAC `h:real^N` THEN DISCH_TAC THEN
    UNDISCH_TAC
     `!s h. &0 < s /\ s <= &1 /\
            mfd_differential (open_set_atlas (:real^N)) atlas
              (mfd_exp (top,atlas) (g:A->real^N^N) q) ((E:real^N^N) ** (s % w0)) h = vec 0
            ==> h = vec 0` THEN
    DISCH_THEN MATCH_MP_TAC THEN EXISTS_TAC `s * inv(norm(w0:real^N))` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[REAL_LT_INV_EQ];
      ASM_SIMP_TAC[GSYM real_div; REAL_LE_LDIV_EQ; REAL_MUL_LID]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`A:real->real^N^N`; `B:real->real^N^N`; `R:real->real^N^N`;
                 `norm(w0:real^N) + &1`; `norm(w0:real^N)`] CMPH_JSYS_INV_NEAR) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[NORM_POS_LE; REAL_LE_REFL; REAL_ARITH `x < x + &1`]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `eps:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `L' = norm(w0:real^N) + min eps (&1) / &2` THEN
  SUBGOAL_THEN `norm(w0:real^N) < L' /\ L' <= norm w0 + &1 /\ L' - norm w0 < eps`
  STRIP_ASSUME_TAC THENL [EXPAND_TAC "L'" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!s. &0 < s /\ s < L' ==> invertible((A:real->real^N^N) s)` ASSUME_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    ASM_CASES_TAC `s <= norm(w0:real^N)` THENL
     [ASM_SIMP_TAC[];
      UNDISCH_TAC `!s. abs(s - norm(w0:real^N)) < eps ==> invertible((A:real->real^N^N) s)` THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `cmp_jsys (A:real->real^N^N) B R L'` ASSUME_TAC THENL
   [MATCH_MP_TAC CMPH_JSYS_MONO THEN EXISTS_TAC `norm(w0:real^N) + &1` THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!s. &0 <= s /\ s < L'
                    ==> --(&(dimindex(:N) - 1) * K) <= trace((R:real->real^N^N) s)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "trace")) (concl th))) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`A:real->real^N^N`; `B:real->real^N^N`; `R:real->real^N^N`;
                 `L':real`; `K:real`; `norm(w0:real^N)`] CMPH_TRACE_BOUND) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(ISPECL [`t:real^N->bool`; `cmp_expmetric (top,atlas) (g:A->real^N^N) q E`;
                 `w0:real^N`; `P:real^N^N`; `A:real->real^N^N`; `B:real->real^N^N`;
                 `R:real->real^N^N`; `norm(w0:real^N) + &1`; `&1`] CMPH_LLAP_RAY) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_LT_01; REAL_ARITH `x < x + &1`] THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_REFL]; ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`s:real`; `a:real^N`] THEN STRIP_TAC THEN
    UNDISCH_TAC
     `!s a. &0 < s /\ s < norm(w0:real^N) + &1
            ==> a dot (cmp_expmetric (top,atlas) (g:A->real^N^N) q E
                         (s % inv(norm w0) % w0) ** a) =
                (((A:real->real^N^N) s ** (transp (P:real^N^N) ** a)) dot
                 (A s ** (transp P ** a))) / s pow 2` THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC CMPH_LGRAD2_NORM THEN EXISTS_TAC `t:real^N->bool` THEN
  ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* The barrier core.  CMPH_EXP_CHART_NBHD: near a point                      *)
(* x = exp_q(E w0) where d exp_q is injective, the local inverse Fi of       *)
(* w -> SND c (exp_q(E w)) (c the chart at x) on an open t inside a given    *)
(* open O, with d(q,y) <= |Fi(SND c y)| on the chart neighbourhood.  Then    *)
(* CMPH_BARRIER_CORE: if d exp_q is injective at s uq for 0 < s <= L         *)
(* (|uq|_q = 1, exp_q total) and x = exp_q(L uq), then phi = c0 + |psi|      *)
(* (psi the local inverse of exp_q in a frame) is a smooth upper barrier for *)
(* c0 + d(q,.) near x, equal to c0 + L at x, with |grad phi|^2 = 1 and       *)
(* Laplacian at most (n-1)(1/L + sqrt K) at x.                               *)
(* ========================================================================= *)

let CMPH_EXP_CHART_NBHD = prove
 (`!top atlas (g:A->real^N^N) (q:A) (E:real^N^N) w0 O x.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ q IN topspace top /\
        mfd_orthonormal_frame g q E /\
        mfd_exp_dom (top,atlas) g q = (:real^N) /\
        (!h. mfd_differential (open_set_atlas (:real^N)) atlas
               (mfd_exp (top,atlas) g q) (E ** w0) h = vec 0 ==> h = vec 0) /\
        open O /\ w0 IN O /\ mfd_exp (top,atlas) g q (E ** w0) = x
        ==> ?t u Fi.
              open t /\ w0 IN t /\ t SUBSET O /\ open u /\
              (!w. w IN t ==> mfd_exp (top,atlas) g q (E ** w) IN FST(chart_at atlas x)) /\
              diffeomorphism_on t u
                (\w. SND(chart_at atlas x) (mfd_exp (top,atlas) g q (E ** w))) Fi /\
              open_in top {y | y IN FST(chart_at atlas x) /\
                               SND(chart_at atlas x) y IN u} /\
              x IN FST(chart_at atlas x) /\ SND(chart_at atlas x) x IN u /\
              Fi(SND(chart_at atlas x) x) = w0 /\
              (!y. y IN FST(chart_at atlas x) /\ SND(chart_at atlas x) y IN u
                   ==> Fi(SND(chart_at atlas x) y) IN t /\
                       mfd_exp (top,atlas) g q (E ** Fi(SND(chart_at atlas x) y)) = y /\
                       mfd_joinable (top,atlas) q y /\
                       mfd_dist (top,atlas) g q y <= norm(Fi(SND(chart_at atlas x) y)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `invertible(E:real^N^N)` ASSUME_TAC THENL
   [REWRITE_TAC[INVERTIBLE_LEFT_INVERSE] THEN
    EXISTS_TAC `transp(E:real^N^N) ** (g:A->real^N^N) q` THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [mfd_orthonormal_frame]) THEN
    REWRITE_TAC[GSYM MATRIX_MUL_ASSOC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL
   [SUBST1_TAC(SYM(ASSUME
      `mfd_exp (top,atlas) (g:A->real^N^N) q ((E:real^N^N) ** w0) = x`)) THEN
    MATCH_MP_TAC CMPP_EXP_IN_TOPSPACE THEN ASM_REWRITE_TAC[IN_UNIV];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `q:A`; `E:real^N^N`; `w0:real^N`] CMPH_EXP_FRAME_DIFFEO) THEN
  ASM_REWRITE_TAC[IN_UNIV] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`t0:real^N->bool`; `u0:real^N->bool`; `Fi:real^N->real^N`] THEN
  STRIP_TAC THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)` THEN
  ABBREV_TAC `t = t0 INTER (O:real^N->bool)` THEN
  SUBGOAL_THEN `open (t:real^N->bool) /\ t SUBSET t0 /\ t SUBSET O /\ (w0:real^N) IN t`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "t" THEN ASM_SIMP_TAC[OPEN_INTER; INTER_SUBSET; IN_INTER];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t0:real^N->bool`; `u0:real^N->bool`; `t:real^N->bool`;
                 `\w. SND (c:(A->bool)#(A->real^N))
                        (mfd_exp (top,atlas) (g:A->real^N^N) q ((E:real^N^N) ** w))`;
                 `Fi:real^N->real^N`] CMPH_DIFFEO_RESTRICT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `u = IMAGE (\w. SND (c:(A->bool)#(A->real^N))
                     (mfd_exp (top,atlas) (g:A->real^N^N) q ((E:real^N^N) ** w))) t` THEN
  MP_TAC(REWRITE_RULE[diffeomorphism_on] (ASSUME
   `diffeomorphism_on t u
      (\w. SND (c:(A->bool)#(A->real^N))
             (mfd_exp (top,atlas) (g:A->real^N^N) q ((E:real^N^N) ** w))) Fi`)) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `(Fi:real^N->real^N)(SND (c:(A->bool)#(A->real^N)) x) = w0` ASSUME_TAC THENL
   [UNDISCH_TAC
     `!x. x IN t
          ==> (Fi:real^N->real^N)
                (SND (c:(A->bool)#(A->real^N))
                  (mfd_exp (top,atlas) (g:A->real^N^N) q ((E:real^N^N) ** x))) = x` THEN
    DISCH_THEN(MP_TAC o SPEC `w0:real^N`) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `SND (c:(A->bool)#(A->real^N)) x IN u` ASSUME_TAC THENL
   [EXPAND_TAC "u" THEN REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `w0:real^N` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z:A. z IN FST (c:(A->bool)#(A->real^N)) ==> chart_inv c (SND c z) = z`
  ASSUME_TAC THENL [ASM_MESON_TAC[MFDM_CHART]; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`t:real^N->bool`; `u:real^N->bool`; `Fi:real^N->real^N`] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    ASM_MESON_TAC[SUBSET];
    ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`;
                   `u:real^N->bool`] GRGD_CHART_PREIMAGE_OPEN) THEN
    ASM_REWRITE_TAC[PAIR];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `y:A` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(Fi:real^N->real^N)(SND (c:(A->bool)#(A->real^N)) y) IN t` ASSUME_TAC THENL
   [UNDISCH_TAC `IMAGE (Fi:real^N->real^N) u = t` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_exp (top,atlas) (g:A->real^N^N) q
      ((E:real^N^N) ** (Fi:real^N->real^N)(SND (c:(A->bool)#(A->real^N)) y)) IN FST c`
  ASSUME_TAC THENL [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN
   `SND (c:(A->bool)#(A->real^N))
      (mfd_exp (top,atlas) (g:A->real^N^N) q
        ((E:real^N^N) ** (Fi:real^N->real^N)(SND c y))) = SND c y`
  ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_exp (top,atlas) (g:A->real^N^N) q
      ((E:real^N^N) ** (Fi:real^N->real^N)(SND (c:(A->bool)#(A->real^N)) y)) = y`
  ASSUME_TAC THENL
   [UNDISCH_TAC `!z:A. z IN FST (c:(A->bool)#(A->real^N)) ==> chart_inv c (SND c z) = z` THEN
    DISCH_THEN(fun th ->
      MP_TAC(SPEC `y:A` th) THEN
      MP_TAC(SPEC `mfd_exp (top,atlas) (g:A->real^N^N) q
                     ((E:real^N^N) ** (Fi:real^N->real^N)
                        (SND (c:(A->bool)#(A->real^N)) y))` th)) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `q:A`;
                 `(E:real^N^N) ** (Fi:real^N->real^N)(SND (c:(A->bool)#(A->real^N)) y)`]
    CMPH_EXP_DIST_LE) THEN
  ASM_REWRITE_TAC[IN_UNIV] THEN
  MP_TAC(ISPECL [`g:A->real^N^N`; `q:A`; `E:real^N^N`;
                 `(Fi:real^N->real^N)(SND (c:(A->bool)#(A->real^N)) y)`] CMPP_TNORM_FRAME) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN SIMP_TAC[]);;

let CMPH_BARRIER_CORE = prove
 (`!top atlas (g:A->real^N^N) (q:A) (uq:real^N) K L c0 x.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ q IN topspace top /\ &0 <= K /\
        mfd_exp_dom (top,atlas) g q = (:real^N) /\
        (!y v. y IN topspace top
               ==> --(&(dimindex(:N) - 1) * K) * (v dot (g y ** v)) <=
                   mfd_ricci atlas g y v v) /\
        mfd_tnorm g q uq = &1 /\ &0 < L /\
        (!s h. &0 < s /\ s <= L /\
               mfd_differential (open_set_atlas (:real^N)) atlas
                 (mfd_exp (top,atlas) g q) (s % uq) h = vec 0
               ==> h = vec 0) /\
        mfd_exp (top,atlas) g q (L % uq) = x
        ==> ?W phi.
              open_in top W /\ x IN W /\ mfd_smooth_on atlas W (lift o phi) /\
              (!y. y IN W
                   ==> mfd_joinable (top,atlas) q y /\
                       c0 + mfd_dist (top,atlas) g q y <= phi y) /\
              phi x = c0 + L /\
              lgrad2 (metric_local atlas (chart_at atlas x) g)
                     (phi o chart_inv (chart_at atlas x))
                     (SND(chart_at atlas x) x) = &1 /\
              llap (metric_local atlas (chart_at atlas x) g)
                   (phi o chart_inv (chart_at atlas x))
                   (SND(chart_at atlas x) x) <=
              &(dimindex(:N) - 1) * (inv L + sqrt K)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `q:A`] GEOJ_ONB) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `E:real^N^N`) THEN
  SUBGOAL_THEN `mfd_orthonormal_frame (g:A->real^N^N) q E` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[mfd_orthonormal_frame]; ALL_TAC] THEN
  SUBGOAL_THEN `invertible(E:real^N^N)` ASSUME_TAC THENL
   [REWRITE_TAC[INVERTIBLE_LEFT_INVERSE] THEN
    EXISTS_TAC `transp(E:real^N^N) ** (g:A->real^N^N) q` THEN
    ASM_REWRITE_TAC[GSYM MATRIX_MUL_ASSOC];
    ALL_TAC] THEN
  ABBREV_TAC `w0 = L % (matrix_inv(E:real^N^N) ** (uq:real^N))` THEN
  SUBGOAL_THEN `(E:real^N^N) ** w0 = L % uq` ASSUME_TAC THENL
   [EXPAND_TAC "w0" THEN REWRITE_TAC[MATRIX_VECTOR_MUL_RMUL; MATRIX_VECTOR_MUL_ASSOC] THEN
    ASM_SIMP_TAC[MATRIX_INV; MATRIX_VECTOR_MUL_LID];
    ALL_TAC] THEN
  SUBGOAL_THEN `norm(w0:real^N) = L` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`g:A->real^N^N`; `q:A`; `E:real^N^N`; `w0:real^N`] CMPP_TNORM_FRAME) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `q:A`] GEOD_TNORM_BASIC) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[REAL_MUL_RID] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `q:A`; `E:real^N^N`; `w0:real^N`;
                 `(:real^N) DELETE vec 0`; `x:A`] CMPH_EXP_CHART_NBHD) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[OPEN_DELETE; OPEN_UNIV; IN_DELETE; IN_UNIV] THEN CONJ_TAC THENL
     [X_GEN_TAC `h:real^N` THEN DISCH_TAC THEN
      UNDISCH_TAC
       `!s h. &0 < s /\ s <= L /\
              mfd_differential (open_set_atlas (:real^N)) atlas
                (mfd_exp (top,atlas) (g:A->real^N^N) q) (s % uq) h = vec 0
              ==> h = vec 0` THEN
      DISCH_THEN MATCH_MP_TAC THEN EXISTS_TAC `L:real` THEN
      ASM_REWRITE_TAC[REAL_LE_REFL];
      REWRITE_TAC[GSYM NORM_POS_LT] THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`t:real^N->bool`; `u:real^N->bool`; `Fi:real^N->real^N`] THEN
  STRIP_TAC THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`] CHART_AT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    SUBST1_TAC(SYM(ASSUME `mfd_exp (top,atlas) (g:A->real^N^N) q (L % uq) = x`)) THEN
    MATCH_MP_TAC CMPP_EXP_IN_TOPSPACE THEN ASM_REWRITE_TAC[IN_UNIV];
    ASM_REWRITE_TAC[] THEN STRIP_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `q:A`; `E:real^N^N`; `c:(A->bool)#(A->real^N)`;
                 `t:real^N->bool`; `u:real^N->bool`; `Fi:real^N->real^N`; `c0:real`;
                 `w0:real^N`] CMPH_CHART_TRANSFER) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_UNIV] THEN
    UNDISCH_TAC `t SUBSET (:real^N) DELETE vec 0` THEN
    REWRITE_TAC[SUBSET; IN_DELETE; IN_UNIV] THEN SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[ASSUME `(E:real^N^N) ** w0 = L % uq`;
              ASSUME `mfd_exp (top,atlas) (g:A->real^N^N) q (L % uq) = x`] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `q:A`; `E:real^N^N`; `K:real`; `t:real^N->bool`;
                 `w0:real^N`] CMPH_RAY_LAP_BOUND) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [UNDISCH_TAC `t SUBSET (:real^N) DELETE vec 0` THEN
      REWRITE_TAC[SUBSET; IN_DELETE; IN_UNIV] THEN SIMP_TAC[];
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`s:real`; `h:real^N`] THEN STRIP_TAC THEN
    UNDISCH_TAC
     `!s h. &0 < s /\ s <= L /\
            mfd_differential (open_set_atlas (:real^N)) atlas
              (mfd_exp (top,atlas) (g:A->real^N^N) q) (s % uq) h = vec 0
            ==> h = vec 0` THEN
    DISCH_THEN MATCH_MP_TAC THEN EXISTS_TAC `s * L` THEN
    UNDISCH_TAC
     `mfd_differential (open_set_atlas (:real^N)) atlas
        (mfd_exp (top,atlas) (g:A->real^N^N) q) ((E:real^N^N) ** (s % w0)) h = vec 0` THEN
    ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_RMUL; VECTOR_MUL_ASSOC] THEN
    DISCH_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC(REAL_ARITH `s * L <= &1 * L ==> s * L <= L`) THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]];
    ASM_REWRITE_TAC[] THEN STRIP_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`{y:A | y IN FST (c:(A->bool)#(A->real^N)) /\ SND c y IN u}`;
    `\y:A. c0 + norm((Fi:real^N->real^N)(SND (c:(A->bool)#(A->real^N)) y))`] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[IN_ELIM_THM];
    SUBGOAL_THEN
     `lift o (\y:A. c0 + norm((Fi:real^N->real^N)(SND (c:(A->bool)#(A->real^N)) y))) =
      (\y. (\z. lift(c0 + norm(Fi z))) (SND c y))`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CMPH_MFD_SMOOTH_ON_CHART THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `y:A` THEN STRIP_TAC THEN
    UNDISCH_TAC
     `!y. y IN FST (c:(A->bool)#(A->real^N)) /\ SND c y IN u
          ==> (Fi:real^N->real^N)(SND c y) IN t /\
              mfd_exp (top,atlas) (g:A->real^N^N) q ((E:real^N^N) ** Fi(SND c y)) = y /\
              mfd_joinable (top,atlas) q y /\
              mfd_dist (top,atlas) g q y <= norm(Fi(SND c y))` THEN
    DISCH_THEN(MP_TAC o SPEC `y:A`) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* S7, CMP_LAPLACIAN_BARRIER (Calabi).  Take a minimizing                    *)
(* geodesic gamma from p to x (Hopf-Rinow), with d = d(p,x), and the point   *)
(* q = gamma(delta) with 1/(d - delta) = 1/d + e/n.  Then x is not          *)
(* conjugate to q along gamma (CMPN_NO_CONJ), the barrier core at q gives    *)
(* phi = delta + |psi| >= delta + d(q,.) >= d(p,.) near x, phi(x) = d, and   *)
(* the Laplacian bound (n-1)(1/(d - delta) + sqrt K) <= (n-1)(1/d + sqrt K)  *)
(* + e.                                                                      *)
(* ========================================================================= *)

let CMPH_INV_ARITH = prove
 (`!d e K. &0 < d /\ &0 < e /\ &0 <= K
           ==> &0 < inv(inv d + e / &(dimindex(:N))) /\
               inv(inv d + e / &(dimindex(:N))) < d /\
               &(dimindex(:N) - 1) * (inv(inv(inv d + e / &(dimindex(:N)))) + sqrt K) <=
               &(dimindex(:N) - 1) * (inv d + sqrt K) + e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &(dimindex(:N))` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT; ARITH_RULE `0 < n <=> 1 <= n`; DIMINDEX_GE_1]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < e / &(dimindex(:N))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_DIV]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < inv d` ASSUME_TAC THENL [ASM_REWRITE_TAC[REAL_LT_INV_EQ]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < inv d + e / &(dimindex(:N))` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[REAL_LT_INV_EQ; REAL_INV_INV] THEN CONJ_TAC THENL
   [GEN_REWRITE_TAC RAND_CONV [GSYM REAL_INV_INV] THEN MATCH_MP_TAC REAL_LT_INV2 THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&(dimindex(:N) - 1) <= &(dimindex(:N))` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LE] THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&(dimindex(:N) - 1) * (e / &(dimindex(:N))) <= e` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&(dimindex(:N)) * (e / &(dimindex(:N)))` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      ASM_SIMP_TAC[REAL_DIV_LMUL; REAL_LT_IMP_NZ; REAL_LE_REFL]];
    REAL_ARITH_TAC]);;

let CMP_LAPLACIAN_BARRIER = prove
 (`!(u:A->bool) (n:N->bool). CMP_LAPLACIAN_BARRIER_STATEMENT u n`,
  REWRITE_TAC[CMP_LAPLACIAN_BARRIER_STATEMENT] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`x:A`; `e:real`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `p:A`; `x:A`] MFD_COMPLETE_MINIMIZING_GEODESIC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `v:real^N` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `d = mfd_dist (top,atlas) (g:A->real^N^N) p x` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `p:A`] GEOD_TNORM_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < d` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 <= d /\ ~(d = &0) ==> &0 < d`) THEN CONJ_TAC THENL
     [ASM_MESON_TAC[]; DISCH_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `p:A`; `v:real^N`] GEOD_TNORM_EQ_0) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `p:A`] MFD_EXP_DOM) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `ud = inv d % (v:real^N)` THEN
  SUBGOAL_THEN `mfd_tnorm (g:A->real^N^N) p ud = &1` ASSUME_TAC THENL
   [EXPAND_TAC "ud" THEN
    ASM_SIMP_TAC[REAL_ABS_INV; REAL_ARITH `&0 < d ==> abs d = d`; REAL_MUL_LINV;
                 REAL_LT_IMP_NZ];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s. s IN mfd_geo_maxint (top,atlas) (g:A->real^N^N) p ud` ASSUME_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `p:A`; `ud:real^N`; `s:real`] MFD_EXP_RADIAL) THEN
    ASM_REWRITE_TAC[IN_UNIV] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_geo (top,atlas) (g:A->real^N^N) p ud d = x` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `p:A`; `ud:real^N`; `d:real`] MFD_EXP_RADIAL) THEN
    ASM_REWRITE_TAC[IN_UNIV] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN EXPAND_TAC "ud" THEN
    ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_RINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `p:A`; `ud:real^N`] CMPS_RAY_FACTS) THEN
  ASM_REWRITE_TAC[IN_UNIV] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`d:real`; `e:real`; `K:real`] CMPH_INV_ARITH) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `L = inv(inv d + e / &(dimindex(:N)))` THEN STRIP_TAC THEN
  ABBREV_TAC `delta = d - L` THEN
  SUBGOAL_THEN `&0 < delta /\ delta + L = d` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "delta" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `p:A`; `ud:real^N`; `delta:real`] CMPN_SHIFT_SETUP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `mfd_geo (top,atlas) (g:A->real^N^N) p ud`;
                 `mfd_geo_maxint (top,atlas) (g:A->real^N^N) p ud`; `&0`; `delta:real`]
    GEOH_GEO_SEG_DIST) THEN
  ASM_REWRITE_TAC[REAL_SUB_RZERO; REAL_MUL_RID] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `mfd_geo (top,atlas) (g:A->real^N^N) p ud`;
                 `mfd_geo_maxint (top,atlas) (g:A->real^N^N) p ud`; `delta:real`; `d:real`]
    GEOH_GEO_SEG_DIST) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!s h. &0 < s /\ s <= L /\
          mfd_differential (open_set_atlas (:real^N)) atlas
            (mfd_exp (top,atlas) (g:A->real^N^N) (mfd_geo (top,atlas) g p ud delta))
            (s % mfd_vel atlas (mfd_geo (top,atlas) g p ud) delta) h = vec 0
          ==> h = vec 0`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC CMPN_NO_CONJ THEN
    MAP_EVERY EXISTS_TAC
     [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
      `p:A`; `ud:real^N`; `d:real`; `delta:real`; `s:real`] THEN
    ASM_REWRITE_TAC[SUBSET] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_tnorm (g:A->real^N^N) (mfd_geo (top,atlas) g p ud delta)
      (mfd_vel atlas (mfd_geo (top,atlas) g p ud) delta) = &1`
  ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `q = mfd_geo (top,atlas) (g:A->real^N^N) p ud delta` THEN
  ABBREV_TAC `uq = mfd_vel (atlas:((A->bool)#(A->real^N))->bool)
                     (mfd_geo (top,atlas) (g:A->real^N^N) p ud) delta` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `q:A`; `x:A`] MFD_COMPLETE_MINIMIZING_GEODESIC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `mfd_exp (top,atlas) (g:A->real^N^N) q (L % uq) = x` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `q:A`; `uq:real^N`; `L:real`] MFD_EXP_RADIAL) THEN
    ASM_REWRITE_TAC[IN_UNIV] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `q:A`; `uq:real^N`; `K:real`; `L:real`; `delta:real`;
                 `x:A`] CMPH_BARRIER_CORE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`W:A->bool`; `phi:A->real`] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`W:A->bool`; `phi:A->real`] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    X_GEN_TAC `y:A` THEN DISCH_TAC THEN
    UNDISCH_TAC
     `!y. y IN W
          ==> mfd_joinable (top,atlas) q y /\
              delta + mfd_dist (top,atlas) (g:A->real^N^N) q y <= (phi:A->real) y` THEN
    DISCH_THEN(MP_TAC o SPEC `y:A`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MFD_JOINABLE_TRANS THEN EXISTS_TAC `q:A` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `mfd_dist (top,atlas) (g:A->real^N^N) p q +
                mfd_dist (top,atlas) g q y` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MFD_DIST_TRIANGLE THEN ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC];
    ASM_REAL_ARITH_TAC;
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&(dimindex(:N) - 1) * (inv L + sqrt K)` THEN ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* S8, CMP_LAPLACIAN_BARRIER_SQ.  Away from p: the square of                 *)
(* the S7 barrier (llap(f^2) = 2 f llap f + 2 |grad f|^2).  At p: |psi|^2    *)
(* for the local inverse psi of exp_p in an orthonormal frame, whose         *)
(* Laplacian at p is 2n (the pullback metric is the identity at 0).          *)
(* ========================================================================= *)

let CMPH_LLAP_SQNORM0 = prove
 (`!(G:real^N->real^N^N).
        G(vec 0) = mat 1
        ==> llap G (\z. norm z pow 2) (vec 0) = &2 * &(dimindex(:N)) /\
            lgrad2 G (\z. norm z pow 2) (vec 0) = &0`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `!z:real^N. frechet_derivative (\w. lift(norm w pow 2)) (at z) =
                           (\x. &2 % lift(z dot x))`
  ASSUME_TAC THENL
   [GEN_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
    REWRITE_TAC[HAS_DERIVATIVE_SQNORM_AT];
    ALL_TAC] THEN
  SUBGOAL_THEN `!h:real^N. rfa_d1 (\z. norm z pow 2) (vec 0) h = &0` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[rfa_d1; DOT_LZERO; LIFT_NUM; VECTOR_MUL_RZERO; DROP_VEC]; ALL_TAC] THEN
  SUBGOAL_THEN `!a b:real^N. rfa_d2 (\z. norm z pow 2) (vec 0) a b = &2 * (a dot b)`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN ASM_REWRITE_TAC[rfa_d2] THEN
    SUBGOAL_THEN `frechet_derivative (\z:real^N. &2 % lift(z dot b)) (at (vec 0)) =
                  (\z. &2 % lift(z dot b))`
    SUBST1_TAC THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
      MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN MATCH_MP_TAC LINEAR_COMPOSE_CMUL THEN
      ONCE_REWRITE_TAC[DOT_SYM] THEN REWRITE_TAC[LINEAR_LIFT_DOT];
      REWRITE_TAC[DROP_CMUL; LIFT_DROP]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [ASM_REWRITE_TAC[RFA_LLAP_D2; MATRIX_INV_I; REAL_MUL_RZERO; SUM_0; REAL_SUB_RZERO] THEN
    MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `sum(1..dimindex(:N)) (\i. &2)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      REWRITE_TAC[] THEN
      MATCH_MP_TAC EQ_TRANS THEN
      EXISTS_TAC `sum(1..dimindex(:N)) (\j. if j = i then &2 else &0)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
        ASM_SIMP_TAC[MAT_COMPONENT; DOT_BASIS_BASIS] THEN
        ASM_CASES_TAC `j:num = i` THEN ASM_REWRITE_TAC[] THENL
         [REAL_ARITH_TAC;
          SUBGOAL_THEN `~(i:num = j)` (fun th -> REWRITE_TAC[th]) THENL
           [ASM_MESON_TAC[]; REAL_ARITH_TAC]];
        ASM_REWRITE_TAC[SUM_DELTA; IN_NUMSEG]];
      REWRITE_TAC[SUM_CONST_NUMSEG; ADD_SUB] THEN REAL_ARITH_TAC];
    ASM_REWRITE_TAC[RFA_LGRAD2_D1; rfa_lginner; REAL_MUL_LZERO; REAL_MUL_RZERO; SUM_0]]);;

let CMPH_LAP_SQ = prove
 (`!U (G:real^N->real^N^N) f y.
        open U /\ smooth_map_on U (\z. lift(f z)) /\ y IN U
        ==> llap G (\z. f z pow 2) y = &2 * f y * llap G f y + &2 * lgrad2 G f y /\
            lgrad2 G (\z. f z pow 2) y = &4 * f y pow 2 * lgrad2 G f y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`U:real^N->bool`; `(:real)`; `G:real^N->real^N^N`; `f:real^N->real`;
                   `\t:real. t pow 2`; `\t:real. &2 * t`; `\t:real. &2`; `y:real^N`]
      RFA_LLAP_COMPOSE) THEN
    ASM_REWRITE_TAC[IN_UNIV] THEN ANTS_TAC THENL
     [X_GEN_TAC `t:real` THEN CONJ_TAC THEN REAL_DIFF_TAC THEN
      CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[REAL_POW_1] THEN REAL_ARITH_TAC;
      DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC];
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `f:real^N->real`;
                   `\t:real. t pow 2`; `&2 * (f:real^N->real) y`; `y:real^N`]
      RFA_LGRAD2_COMPOSE) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [REAL_DIFF_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[REAL_POW_1] THEN
      REAL_ARITH_TAC;
      DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC]]);;

let CMPH_MFD_SMOOTH_ON_SQ = prove
 (`!top atlas W (phi:A->real).
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
        open_in top W /\ mfd_smooth_on atlas W (lift o phi)
        ==> mfd_smooth_on atlas W (lift o (\y. phi y pow 2))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mfd_smooth_on] THEN STRIP_TAC THEN
  X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `c:(A->bool)#(A->real^N)`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN
   `(lift o (\y:A. (phi:A->real) y pow 2)) o chart_inv (c:(A->bool)#(A->real^N)) =
    (\z. lift(drop(((lift o phi) o chart_inv c) z) pow 2))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_DROP]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_LIFT_POW THEN ASM_REWRITE_TAC[ETA_AX] THEN
  MATCH_MP_TAC MFDM_CHART_IMAGE_OPEN THEN
  MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
  ASM_REWRITE_TAC[INTER_SUBSET] THEN MATCH_MP_TAC OPEN_IN_INTER THEN
  ASM_MESON_TAC[MFDM_CHART]);;

let CMPH_SQ_BARRIER_P = prove
 (`!top atlas (g:A->real^N^N) (p:A).
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ p IN topspace top /\
        mfd_exp_dom (top,atlas) g p = (:real^N)
        ==> ?W phi.
              open_in top W /\ p IN W /\ mfd_smooth_on atlas W (lift o phi) /\
              (!y. y IN W
                   ==> mfd_joinable (top,atlas) p y /\
                       mfd_dist (top,atlas) g p y pow 2 <= phi y) /\
              phi p = &0 /\
              lgrad2 (metric_local atlas (chart_at atlas p) g)
                     (phi o chart_inv (chart_at atlas p))
                     (SND(chart_at atlas p) p) = &0 /\
              llap (metric_local atlas (chart_at atlas p) g)
                   (phi o chart_inv (chart_at atlas p))
                   (SND(chart_at atlas p) p) = &2 * &(dimindex(:N))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `p:A`] GEOJ_ONB) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `E:real^N^N`) THEN
  SUBGOAL_THEN `mfd_orthonormal_frame (g:A->real^N^N) p E` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[mfd_orthonormal_frame]; ALL_TAC] THEN
  SUBGOAL_THEN `mfd_exp (top,atlas) (g:A->real^N^N) p (vec 0) = p` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `p:A`] MFD_EXP_DOM) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `p:A`; `E:real^N^N`; `vec 0:real^N`; `(:real^N)`;
                 `p:A`] CMPH_EXP_CHART_NBHD) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV; MATRIX_VECTOR_MUL_RZERO] THEN
    ASM_SIMP_TAC[MFD_EXP_DIFFERENTIAL_ZERO];
    ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`t:real^N->bool`; `u:real^N->bool`; `Fi:real^N->real^N`] THEN
  STRIP_TAC THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^N))->bool) (p:A)` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `p:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `p:A`; `E:real^N^N`; `c:(A->bool)#(A->real^N)`;
                 `t:real^N->bool`; `u:real^N->bool`; `Fi:real^N->real^N`;
                 `\w:real^N. norm w pow 2`; `vec 0:real^N`] CMPH_CHART_TRANSFER_GEN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_UNIV] THEN
    MP_TAC(ISPECL [`t:real^N->bool`; `\z:real^N. z`] SMOOTH_MAP_ON_NORM_POW2_OPEN) THEN
    ASM_REWRITE_TAC[SMOOTH_MAP_ON_ID];
    ALL_TAC] THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_RZERO;
              ASSUME `mfd_exp (top,atlas) (g:A->real^N^N) p (vec 0) = p`] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `p:A`; `E:real^N^N`] CMPP_EXPMETRIC_ZERO) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPEC `cmp_expmetric (top,atlas) (g:A->real^N^N) p E` CMPH_LLAP_SQNORM0) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC
   [`{y:A | y IN FST (c:(A->bool)#(A->real^N)) /\ SND c y IN u}`;
    `\y:A. norm((Fi:real^N->real^N)(SND (c:(A->bool)#(A->real^N)) y)) pow 2`] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[IN_ELIM_THM];
    SUBGOAL_THEN
     `lift o (\y:A. norm((Fi:real^N->real^N)(SND (c:(A->bool)#(A->real^N)) y)) pow 2) =
      (\y. (\z. lift(norm(Fi z) pow 2)) (SND c y))`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CMPH_MFD_SMOOTH_ON_CHART THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `y:A` THEN STRIP_TAC THEN
    UNDISCH_TAC
     `!y. y IN FST (c:(A->bool)#(A->real^N)) /\ SND c y IN u
          ==> (Fi:real^N->real^N)(SND c y) IN t /\
              mfd_exp (top,atlas) (g:A->real^N^N) p ((E:real^N^N) ** Fi(SND c y)) = y /\
              mfd_joinable (top,atlas) p y /\
              mfd_dist (top,atlas) g p y <= norm(Fi(SND c y))` THEN
    DISCH_THEN(MP_TAC o SPEC `y:A`) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MFD_DIST_POS_LE THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[NORM_0] THEN CONV_TAC REAL_RAT_REDUCE_CONV;
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[]]);;

let CMP_LAPLACIAN_BARRIER_SQ = prove
 (`!(u:A->bool) (n:N->bool). CMP_LAPLACIAN_BARRIER_SQ_STATEMENT u n`,
  REWRITE_TAC[CMP_LAPLACIAN_BARRIER_SQ_STATEMENT] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`x:A`; `e:real`] THEN STRIP_TAC THEN
  ASM_CASES_TAC `x:A = p` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `p:A`; `p:A`] MFD_COMPLETE_MINIMIZING_GEODESIC) THEN
    ASM_REWRITE_TAC[MFD_JOINABLE_REFL] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `p:A`] CMPH_SQ_BARRIER_P) THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`W:A->bool`; `phi:A->real`] THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`W:A->bool`; `phi:A->real`] THEN
    ASM_SIMP_TAC[MFD_DIST_REFL] THEN
    REWRITE_TAC[REAL_POW_2; REAL_MUL_LZERO; REAL_MUL_RZERO; REAL_ADD_RID] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < mfd_dist (top,atlas) (g:A->real^N^N) p x` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 <= d /\ ~(d = &0) ==> &0 < d`) THEN CONJ_TAC THENL
     [MATCH_MP_TAC MFD_DIST_POS_LE THEN ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[MFD_DIST_EQ_0] THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `d = mfd_dist (top,atlas) (g:A->real^N^N) p x` THEN
  MP_TAC(ISPECL [`u:A->bool`; `n:N->bool`] CMP_LAPLACIAN_BARRIER) THEN
  REWRITE_TAC[CMP_LAPLACIAN_BARRIER_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                             `g:A->real^N^N`; `p:A`; `K:real`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPECL [`x:A`; `e / (&2 * d)`]) THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_LT_MUL; REAL_OF_NUM_LT; ARITH] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`W:A->bool`; `psi:A->real`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `open (IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c INTER W)) /\
    SND c x IN IMAGE (SND c) (FST c INTER W) /\
    smooth_map_on (IMAGE (SND c) (FST c INTER W))
      (\z. lift(((psi:A->real) o chart_inv c) z))`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MFDM_CHART_IMAGE_OPEN THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
      ASM_SIMP_TAC[INTER_SUBSET; OPEN_IN_INTER];
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_INTER];
      UNDISCH_TAC `mfd_smooth_on (atlas:((A->bool)#(A->real^N))->bool) W (lift o (psi:A->real))` THEN
      REWRITE_TAC[mfd_smooth_on] THEN
      DISCH_THEN(MP_TAC o SPEC `c:(A->bool)#(A->real^N)`) THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM; o_THM]];
    ALL_TAC] THEN
  SUBGOAL_THEN `((psi:A->real) o chart_inv (c:(A->bool)#(A->real^N))) (SND c x) = d`
  ASSUME_TAC THENL [ASM_SIMP_TAC[o_THM]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(\y:A. (psi:A->real) y pow 2) o chart_inv (c:(A->bool)#(A->real^N)) =
    (\z. (psi o chart_inv c) z pow 2)`
  ASSUME_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c INTER W)`;
                 `metric_local atlas (c:(A->bool)#(A->real^N)) (g:A->real^N^N)`;
                 `(psi:A->real) o chart_inv (c:(A->bool)#(A->real^N))`;
                 `SND (c:(A->bool)#(A->real^N)) x`] CMPH_LAP_SQ) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  EXISTS_TAC `W:A->bool` THEN EXISTS_TAC `\y:A. (psi:A->real) y pow 2` THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC CMPH_MFD_SMOOTH_ON_SQ THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `y:A` THEN DISCH_TAC THEN
    UNDISCH_TAC
     `!y. y IN W
          ==> mfd_joinable (top,atlas) p y /\
              mfd_dist (top,atlas) (g:A->real^N^N) p y <= (psi:A->real) y` THEN
    DISCH_THEN(MP_TAC o SPEC `y:A`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MFD_DIST_POS_LE THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[REAL_MUL_RID];
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&(dimindex(:N) - 1) + &1 = &(dimindex(:N))` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_ADD] THEN AP_TERM_TAC THEN MATCH_MP_TAC SUB_ADD THEN
      REWRITE_TAC[DIMINDEX_GE_1];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `d * (&(dimindex(:N) - 1) * (inv d + sqrt K) + e / (&2 * d)) =
      &(dimindex(:N) - 1) + &(dimindex(:N) - 1) * sqrt K * d + e / &2`
    ASSUME_TAC THENL [UNDISCH_TAC `&0 < d` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    SUBGOAL_THEN
     `d * llap (metric_local atlas (c:(A->bool)#(A->real^N)) (g:A->real^N^N))
              ((psi:A->real) o chart_inv c) (SND c x) <=
      d * (&(dimindex(:N) - 1) * (inv d + sqrt K) + e / (&2 * d))`
    MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `&(dimindex(:N) - 1) + &1 = &(dimindex(:N))` THEN REAL_ARITH_TAC]);;

