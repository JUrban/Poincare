(* ========================================================================= *)
(* Unit pc_rf_unique_a14: A14, the uniqueness of complete Ricci flows of     *)
(* bounded curvature with the same initial metric (the statement             *)
(* P2C_REQ_UNIQ_COMPLETE_STATEMENT), at (:real^3), conditional on            *)
(* P2_THM_3_29_STATEMENT (:real^3) (Shi with initial bounds; the hypothesis  *)
(* is discharged in pc_rf_unique_a14u).  The uniform bounds required by      *)
(* RFU_ENERGY_ZERO are derived from the hypotheses of A14: metric            *)
(* equivalence from the curvature bound (RFA_METRIC_EQUIV), Shi bounds for   *)
(* both flows, the scalar curvature bound, the Kotschwar density bound       *)
(* (Christoffel differences integrated in time), and |dphi|^2 and the volume *)
(* growth of phi-sublevel sets for g(t).                                     *)
(* ========================================================================= *)

needs "src/pc_rf_unique_complete.ml";;
needs "src/pc_grg_area.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* Bounds from the curvature bound: Ricci and scalar curvature               *)
(* (RFU_RIC_FROM_RMNORM, RFU_SCALAR_FROM_RMNORM), metric equivalence along  *)
(* the flow (RFU_FLOW_EQUIV), and monotonicity of |df|^2 in the metric       *)
(* (RFU_LGRAD2_MONO).                                                        *)
(* ========================================================================= *)

let RFU_RIC_FROM_RMNORM = prove
 (`?C. &0 <= C /\
       !(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) x K v.
          smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
          x IN topspace top /\ &0 <= K /\ mfd_rm_norm atlas g x <= K
          ==> abs(mfd_ricci atlas g x v v) <= (C * K) * (v dot (g x ** v))`,
  X_CHOOSE_THEN `C0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "R0"))
    (INST_TYPE [`:A`,`:A`; `:N`,`:N`] RFA_R1_RMD0) THEN
  EXISTS_TAC `&(dimindex(:N)) * sqrt C0` THEN
  CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_POS; SQRT_POS_LE]; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `C0 * K pow 2`; `v:real^N`] RFA_R1_RIC_BOUND) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_MUL; REAL_LE_POW_2] THEN USE_THEN "R0" MATCH_MP_TAC THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[SQRT_MUL; REAL_LE_POW_2; POW_2_SQRT] THEN
  REWRITE_TAC[REAL_MUL_ASSOC]);;

(* The scalar curvature in terms of a Ricci bound, via normalisation. *)

let RFU_LSCALAR_BOUND = prove
 (`!U (G:real^N->real^N^N) y K.
        metric_field U G /\ y IN U /\
        (!v. abs(lricci G y v v) <= K * (v dot (G y ** v)))
        ==> abs(lscalar G y) <= &(dimindex(:N)) * K`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`] RFU_NORMALIZE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `M:real^N^N` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `h = \z:real^N. matrix_inv(M:real^N^N) ** z` THEN
  ABBREV_TAC `U' = IMAGE (\y:real^N. (M:real^N^N) ** y) U` THEN
  ABBREV_TAC `z0 = (M:real^N^N) ** y` THEN
  SUBGOAL_THEN `(h:real^N->real^N) z0 = y` (LABEL_TAC "HZ") THENL
   [MAP_EVERY EXPAND_TAC ["h"; "z0"] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `U':real^N->bool`; `h:real^N->real^N`;
                 `\y:real^N. (M:real^N^N) ** y`; `z0:real^N`] LRG_DIFFEO_DERIV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `U':real^N->bool`; `h:real^N->real^N`;
                 `\y:real^N. (M:real^N^N) ** y`; `G:real^N->real^N^N`; `z0:real^N`]
                LSCALAR_PULLBACK) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[lscalar] THEN ASM_REWRITE_TAC[MATRIX_INV_I] THEN
  SIMP_TAC[MAT_COMPONENT; COND_RAND; COND_RATOR; REAL_MUL_LZERO; REAL_MUL_LID] THEN
  MATCH_MP_TAC RFU_SUM_ABS_BOUND_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  BETA_TAC THEN
  SUBGOAL_THEN `!j. (i:num = j) <=> (j = i)` (fun th -> REWRITE_TAC[th]) THENL
   [MESON_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[SUM_DELTA; IN_NUMSEG] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `U':real^N->bool`; `h:real^N->real^N`;
                 `\y:real^N. (M:real^N^N) ** y`; `G:real^N->real^N^N`; `z0:real^N`;
                 `basis i:real^N`; `basis i:real^N`] LRICCI_PULLBACK) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `K * ((frechet_derivative (h:real^N->real^N) (at z0) (basis i)) dot
                   ((G:real^N->real^N^N) y ** frechet_derivative h (at z0) (basis i)))` THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`h:real^N->real^N`; `G:real^N->real^N^N`; `z0:real^N`; `basis i:real^N`]
                RFU_MPULLBACK_QFORM) THEN
  ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_LID] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  ASM_SIMP_TAC[DOT_BASIS_BASIS; REAL_MUL_RID; REAL_LE_REFL]);;

let RFU_SCALAR_FROM_RMNORM = prove
 (`?C. &0 <= C /\
       !(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) x K.
          smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
          x IN topspace top /\ &0 <= K /\ mfd_rm_norm atlas g x <= K
          ==> abs(mfd_scalar atlas g x) <= C * K`,
  X_CHOOSE_THEN `C:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "RC"))
    (INST_TYPE [`:A`,`:A`; `:N`,`:N`] RFU_RIC_FROM_RMNORM) THEN
  EXISTS_TAC `&(dimindex(:N)) * C` THEN
  CONJ_TAC THENL [ASM_SIMP_TAC[REAL_LE_MUL; REAL_POS]; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`]
         CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[mfd_scalar; GSYM REAL_MUL_ASSOC] THEN
  MATCH_MP_TAC RFU_LSCALAR_BOUND THEN
  EXISTS_TAC `IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)))
                    (FST(chart_at atlas x))` THEN
  REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[riemannian_metric];
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `v:real^N` THEN
    USE_THEN "RC" (MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                                   `g:A->real^N^N`; `x:A`; `K:real`; `v:real^N`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN REWRITE_TAC[mfd_ricci] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x:A`] METRIC_LOCAL_AT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[REAL_MUL_ASSOC]]);;

(* Metric equivalence along a flow of bounded curvature. *)

let RFU_FLOW_EQUIV = prove
 (`?C. &0 <= C /\
     !(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) a b (g:real->A->real^N^N) b1 K.
       ricci_flow_from (top,atlas) a b g /\ a < b1 /\ b1 <= b /\ &0 <= K /\
       (!t x. a <= t /\ t < b1 /\ x IN topspace top ==> mfd_rm_norm atlas (g t) x <= K)
       ==> !t x v. a <= t /\ t < b1 /\ x IN topspace top
                   ==> exp(--(&2 * (C * K) * (b1 - a))) * (v dot (g a x ** v))
                       <= v dot (g t x ** v) /\
                       v dot (g t x ** v) <= exp(&2 * (C * K) * (b1 - a)) * (v dot (g a x ** v))`,
  X_CHOOSE_THEN `C:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "RC"))
    (INST_TYPE [`:A`,`:A`; `:N`,`:N`] RFU_RIC_FROM_RMNORM) THEN
  EXISTS_TAC `C:real` THEN ASM_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `ricci_flow_from (top,atlas) a b1 (g:real->A->real^N^N)` ASSUME_TAC THENL
   [MATCH_MP_TAC PDE_RFF_RESTRICT THEN MAP_EVERY EXISTS_TAC [`a:real`; `b:real`] THEN
    ASM_REWRITE_TAC[REAL_LE_REFL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `a:real`; `b1:real`; `g:real->A->real^N^N`] GRGT_RF_METRIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `a:real`; `b1:real`; `g:real->A->real^N^N`; `C * K:real`] RFA_METRIC_EQUIV) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    USE_THEN "RC" MATCH_MP_TAC THEN EXISTS_TAC `top:A topology` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_TAC THEN MAP_EVERY X_GEN_TAC [`t:real`; `x:A`; `v:real^N`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`t:real`; `x:A`; `v:real^N`]) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 <= v dot ((g:real->A->real^N^N) a x ** v)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `(g:real->A->real^N^N) a`; `x:A`] RIEMANNIAN_METRIC_POS) THEN
    ASM_SIMP_TAC[REAL_LE_REFL] THEN STRIP_TAC THEN
    ASM_CASES_TAC `v:real^N = vec 0` THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE; MATRIX_VECTOR_MUL_RZERO; DOT_RZERO; REAL_LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= C * K` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_LE_MUL]; ALL_TAC] THEN
  SUBGOAL_THEN
   `exp(--(&2 * (C * K) * (b1 - a))) <= exp(--(&2 * (C * K) * (t - a))) /\
    exp(&2 * (C * K) * (t - a)) <= exp(&2 * (C * K) * (b1 - a))`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_EXP_MONO_LE] THEN CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `x <= y ==> --y <= --x`); ALL_TAC] THEN
    REPEAT(MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  STRIP_TAC THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THENL
   [EXISTS_TAC `exp(--(&2 * (C * K) * (t - a))) * (v dot ((g:real->A->real^N^N) a x ** v))`;
    EXISTS_TAC `exp(&2 * (C * K) * (t - a)) * (v dot ((g:real->A->real^N^N) a x ** v))`] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* |df|^2 decreases when the metric increases (RFU_LGRAD2_MONO), and the     *)
(* transfer of the bounds on phi from g(a) to g(t): |dphi|^2                 *)
(* (RFU_MGRAD2_TRANSFER) and the volume growth of sublevel sets              *)
(* (RFU_VOLUME_TRANSFER, dimension 3).                                       *)
(* ========================================================================= *)

let RFU_ALG_MONO = prove
 (`!L p q c. &0 < c /\ &0 <= p /\ &0 <= q /\ c * q pow 2 <= L /\ L <= p * q
             ==> L <= p pow 2 / c`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
  ASM_CASES_TAC `q = &0` THENL
   [UNDISCH_TAC `L <= p * q` THEN ASM_REWRITE_TAC[REAL_MUL_RZERO] THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&0` THEN CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&0 <= --L * c ==> L * c <= &0`) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_LE_POW_2]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < q` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `c * q <= p` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_RCANCEL_IMP THEN EXISTS_TAC `q:real` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `L:real` THEN CONJ_TAC THENL
     [UNDISCH_TAC `c * q pow 2 <= L` THEN REWRITE_TAC[REAL_POW_2; REAL_MUL_ASSOC];
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(p * q) * c` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_POW_2; GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
  ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN ASM_REWRITE_TAC[]);;

let RFU_LGRAD2_MONO = prove
 (`!U (G:real^N->real^N^N) G' f y c.
        metric_field U G /\ metric_field U G' /\ y IN U /\ &0 < c /\
        (!v. c * (v dot (G' y ** v)) <= v dot (G y ** v))
        ==> lgrad2 G f y <= lgrad2 G' f y / c`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[RFU_LGRAD2_DOT] THEN
  ABBREV_TAC `d = (lambda i. rfa_d1 (f:real^N->real) (y:real^N) (basis i)):real^N` THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G':real^N->real^N^N`; `y:real^N`] LRG_FRAME) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `M:real^N^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `invertible((G:real^N->real^N^N) y)` ASSUME_TAC THENL
   [ASM_MESON_TAC[LRG_METRIC_INVERTIBLE]; ALL_TAC] THEN
  SUBGOAL_THEN `transp((G:real^N->real^N^N) y) = G y` ASSUME_TAC THENL
   [ASM_MESON_TAC[RFU_METRIC_PROPS]; ALL_TAC] THEN
  ABBREV_TAC `w = matrix_inv((G:real^N->real^N^N) y) ** (d:real^N)` THEN
  SUBGOAL_THEN `(G:real^N->real^N^N) y ** w = d` ASSUME_TAC THENL
   [EXPAND_TAC "w" THEN REWRITE_TAC[MATRIX_VECTOR_MUL_ASSOC] THEN
    ASM_SIMP_TAC[MATRIX_INV; MATRIX_VECTOR_MUL_LID];
    ALL_TAC] THEN
  SUBGOAL_THEN `(M:real^N^N) ** matrix_inv M = mat 1 /\ matrix_inv M ** M = mat 1`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[MATRIX_INV]; ALL_TAC] THEN
  SUBGOAL_THEN
   `matrix_inv((G':real^N->real^N^N) y) = matrix_inv(M:real^N^N) ** transp(matrix_inv M)`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MATRIX_INV_UNIQUE THEN
    REWRITE_TAC[MATRIX_MUL_ASSOC] THEN
    SUBGOAL_THEN `transp(matrix_inv(M:real^N^N)) ** transp M = mat 1 /\
                  transp M ** transp(matrix_inv(M:real^N^N)) = mat 1`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[GSYM MATRIX_TRANSP_MUL] THEN ASM_REWRITE_TAC[TRANSP_MAT]; ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[GSYM MATRIX_MUL_ASSOC] THEN
      GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [MATRIX_MUL_ASSOC] THEN
      ASM_REWRITE_TAC[MATRIX_MUL_LID];
      GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [GSYM MATRIX_MUL_ASSOC] THEN
      ASM_REWRITE_TAC[MATRIX_MUL_RID]];
    ALL_TAC] THEN
  ABBREV_TAC `d' = transp(matrix_inv(M:real^N^N)) ** (d:real^N)` THEN
  ABBREV_TAC `w' = (M:real^N^N) ** (w:real^N)` THEN
  SUBGOAL_THEN `(d:real^N) dot (matrix_inv((G':real^N->real^N^N) y) ** d) = (d':real^N) dot d'`
  SUBST1_TAC THENL
   [ASM_REWRITE_TAC[GSYM MATRIX_VECTOR_MUL_ASSOC] THEN
    EXPAND_TAC "d'" THEN REWRITE_TAC[DOT_MATRIX_TRANSP_RMUL] THEN
    REWRITE_TAC[GSYM DOT_MATRIX_TRANSP_LMUL; TRANSP_TRANSP];
    ALL_TAC] THEN
  SUBGOAL_THEN `(w:real^N) dot ((G':real^N->real^N^N) y ** w) = (w':real^N) dot w'` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[GSYM MATRIX_VECTOR_MUL_ASSOC] THEN EXPAND_TAC "w'" THEN
    REWRITE_TAC[DOT_MATRIX_TRANSP_RMUL];
    ALL_TAC] THEN
  SUBGOAL_THEN `(d:real^N) dot (matrix_inv((G:real^N->real^N^N) y) ** d) = d dot w`
  SUBST1_TAC THENL [EXPAND_TAC "w" THEN REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(d:real^N) dot w = (d':real^N) dot w'` ASSUME_TAC THENL
   [SUBGOAL_THEN `(d:real^N) = transp(M:real^N^N) ** d'` SUBST1_TAC THENL
     [EXPAND_TAC "d'" THEN REWRITE_TAC[MATRIX_VECTOR_MUL_ASSOC; GSYM MATRIX_TRANSP_MUL] THEN
      ASM_REWRITE_TAC[TRANSP_MAT; MATRIX_VECTOR_MUL_LID];
      ALL_TAC] THEN
    EXPAND_TAC "w'" THEN REWRITE_TAC[DOT_MATRIX_TRANSP_LMUL];
    ALL_TAC] THEN
  SUBGOAL_THEN `c * ((w':real^N) dot w') <= (d:real^N) dot w` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(w:real^N) dot ((G:real^N->real^N^N) y ** w)` THEN CONJ_TAC THENL
     [UNDISCH_TAC `(w:real^N) dot ((G':real^N->real^N^N) y ** w) = (w':real^N) dot w'` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[ASSUME `(G:real^N->real^N^N) y ** w = d`] THEN
      SIMP_TAC[DOT_SYM; REAL_LE_REFL]];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM NORM_POW_2] THEN
  MATCH_MP_TAC RFU_ALG_MONO THEN EXISTS_TAC `norm(w':real^N)` THEN
  ASM_REWRITE_TAC[NORM_POS_LE; GSYM NORM_POW_2] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[NORM_POW_2]; ALL_TAC] THEN
  REWRITE_TAC[NORM_CAUCHY_SCHWARZ]);;

let RFU_MGRAD2_TRANSFER = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (g0:A->real^N^N) g f x c.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g0 /\
        riemannian_metric atlas g /\ x IN topspace top /\ &0 < c /\
        (!v. c * (v dot (g0 x ** v)) <= v dot (g x ** v))
        ==> rfu_mgrad2 atlas g f x <= rfu_mgrad2 atlas g0 f x / c`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`]
         CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN REWRITE_TAC[rfu_mgrad2] THEN
  MATCH_MP_TAC RFU_LGRAD2_MONO THEN
  EXISTS_TAC `IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)))
                    (FST(chart_at atlas x))` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[riemannian_metric];
    ASM_MESON_TAC[riemannian_metric];
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x:A`] METRIC_LOCAL_AT) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g0:A->real^N^N`; `x:A`] METRIC_LOCAL_AT) THEN
    ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN ASM_REWRITE_TAC[]]);;

let RFU_VOLUME_TRANSFER = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g0:A->real^3^3) g S v E.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g0 /\ riemannian_metric atlas g /\
        compact_in top S /\ &0 <= E /\
        (!x w. x IN S ==> w dot (g x ** w) <= E * (w dot (g0 x ** w))) /\
        mfd_has_volume (top,atlas) g S v
        ==> ?v0. mfd_has_volume (top,atlas) g0 S v0 /\ v <= E * sqrt E * v0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g0:A->real^3^3`; `S:A->bool`] MFD_HAS_VOLUME_COMPACT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `v0:real`) THEN
  EXISTS_TAC `v0:real` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MFD_HAS_VOLUME_COMPARE_QF THEN
  MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                        `g:A->real^3^3`; `g0:A->real^3^3`; `S:A->bool`] THEN
  ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* The closure of a ball of a complete metric is compact, and                *)
(* uniform bounds of |nabla^j Rm|^2, j <= 2, along a flow of bounded         *)
(* curvature with bounded initial derivatives, from MT Thm 3.29 (Shi with    *)
(* initial bounds) applied on unit balls (RFU_SHI_FLOW).                     *)
(* ========================================================================= *)

let RFU_BALL_CLOSURE_COMPACT = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) x r.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        mfd_complete (top,atlas) g /\ x IN topspace top
        ==> compact_in top (top closure_of mfd_ball (top,atlas) g x r)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `compact_in top (mfd_cball (top,atlas) (g:A->real^N^N) x r)` ASSUME_TAC THENL
   [ASM_MESON_TAC[mfd_complete]; ALL_TAC] THEN
  SUBGOAL_THEN
   `top closure_of mfd_ball (top,atlas) (g:A->real^N^N) x r SUBSET mfd_cball (top,atlas) g x r`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CLOSURE_OF_MINIMAL THEN ASM_SIMP_TAC[MFD_CBALL_CLOSED] THEN
    REWRITE_TAC[mfd_ball; mfd_cball; SUBSET; IN_ELIM_THM] THEN MESON_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `top closure_of mfd_ball (top,atlas) (g:A->real^N^N) x r =
    mfd_cball (top,atlas) g x r INTER top closure_of mfd_ball (top,atlas) g x r`
  SUBST1_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC COMPACT_INTER_CLOSED_IN THEN ASM_REWRITE_TAC[CLOSED_IN_CLOSURE_OF]);;

let RFU_SHI_FLOW = prove
 (`!top (atlas:((real^3->bool)#(real^3->real^3))->bool) a b g b1 K K0.
     P2_THM_3_29_STATEMENT (:real^3) /\
     hausdorff_space top /\ ricci_flow_from (top,atlas) a b g /\ a < b1 /\ b1 <= b /\
     mfd_complete (top,atlas) (g a) /\
     (!t x. a <= t /\ t < b1 /\ x IN topspace top ==> mfd_rm_norm atlas (g t) x <= K) /\
     (!j x. j <= 2 /\ x IN topspace top
            ==> lrm_deriv_norm2 j (metric_local atlas (chart_at atlas x) (g a))
                                (SND(chart_at atlas x) x) <= K0)
     ==> ?B. !j t x. j <= 2 /\ a <= t /\ t < b1 /\ x IN topspace top
                     ==> rfa_rmd2 j atlas (g t) x <= B`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o REWRITE_RULE[P2_THM_3_29_STATEMENT]) STRIP_ASSUME_TAC) THEN
  DISCH_THEN(MP_TAC o SPECL [`2`; `max (max K K0) (&1)`; `&1`; `b1 - a:real`]) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Cl:real` (LABEL_TAC "SHI")) THEN
  EXISTS_TAC `Cl:real` THEN MAP_EVERY X_GEN_TAC [`j:num`; `t:real`; `x:real^3`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `ricci_flow_from (top,atlas) a b1 (g:real->real^3->real^3^3)` ASSUME_TAC THENL
   [MATCH_MP_TAC PDE_RFF_RESTRICT THEN MAP_EVERY EXISTS_TAC [`a:real`; `b:real`] THEN
    ASM_REWRITE_TAC[REAL_LE_REFL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:(real^3)topology`; `atlas:((real^3->bool)#(real^3->real^3))->bool`;
                 `a:real`; `b1:real`; `g:real->real^3->real^3^3`] GRGT_RF_METRIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `riemannian_metric atlas ((g:real->real^3->real^3^3) a)` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "SHI" (MP_TAC o SPECL
   [`top:(real^3)topology`; `atlas:((real^3->bool)#(real^3->real^3))->bool`;
    `a:real`; `b1:real`; `g:real->real^3->real^3^3`; `x:real^3`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_LE_REFL] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC RFU_BALL_CLOSURE_COMPACT THEN ASM_REWRITE_TAC[];
      REPEAT STRIP_TAC THEN MATCH_MP_TAC(REAL_ARITH `x <= K ==> x <= max (max K K0) (&1)`) THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(y:real^3) IN mfd_ball (top,atlas) ((g:real->real^3->real^3^3) a) x (&1)` THEN
      REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN MESON_TAC[MFD_JOINABLE_IN_TOPSPACE];
      REPEAT STRIP_TAC THEN MATCH_MP_TAC(REAL_ARITH `x <= K0 ==> x <= max (max K K0) (&1)`) THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(y:real^3) IN mfd_ball (top,atlas) ((g:real->real^3->real^3^3) a) x (&1)` THEN
      REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN MESON_TAC[MFD_JOINABLE_IN_TOPSPACE]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`j:num`; `t:real`; `x:real^3`]) THEN
  REWRITE_TAC[rfa_rmd2] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:(real^3)topology`; `atlas:((real^3->bool)#(real^3->real^3))->bool`;
                 `(g:real->real^3->real^3^3) a`; `x:real^3`; `&1 / &2`] MFD_CENTRE_IN_BALL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN CONV_TAC REAL_RAT_REDUCE_CONV);;

(* ========================================================================= *)
(* Component bounds of the three parts of the Kotschwar density              *)
(* at a point where the metrics are L-equivalent to the Euclidean one        *)
(* (RFU_HH_CB, RFU_AA_CB, RFU_Q_CB, RFU_DENS_CB), and conversely the bound  *)
(* of the Christoffel difference by the density (RFU_AA_SMALL).              *)
(* ========================================================================= *)

let RFU_EQUIV_ENTRIES = prove
 (`!U (G:real^N->real^N^N) y L.
        metric_field U G /\ y IN U /\ &0 <= L /\
        (!v. v dot (G y ** v) <= L * (v dot v) /\ v dot v <= L * (v dot (G y ** v)))
        ==> (!p q. 1 <= p /\ p <= dimindex(:N) /\ 1 <= q /\ q <= dimindex(:N)
                   ==> abs(G y$p$q) <= L /\ abs(matrix_inv(G y)$p$q) <= L) /\
            (!p. 1 <= p /\ p <= dimindex(:N) ==> G y$p$p <= L)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `transp((G:real^N->real^N^N) y) = G y /\ invertible(G y) /\
                (!v. &0 <= v dot (G y ** v))` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[RFU_METRIC_PROPS];
      ASM_MESON_TAC[LRG_METRIC_INVERTIBLE];
      GEN_TAC THEN MATCH_MP_TAC LRG_METRIC_NONNEG THEN
      EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!p q. 1 <= p /\ p <= dimindex(:N) /\ 1 <= q /\ q <= dimindex(:N)
          ==> abs((G:real^N->real^N^N) y$p$q) <= L /\ abs(matrix_inv(G y)$p$q) <= L`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC RFA_QFORM_ENTRY_BOUND THEN ASM_REWRITE_TAC[NORM_POW_2] THEN
      ASM_MESON_TAC[];
      MP_TAC(ISPECL [`(G:real^N->real^N^N) y`; `L:real`] RFA_GINV_ENTRY_BOUND) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[NORM_POW_2] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`p:num`; `p:num`]) THEN ASM_REWRITE_TAC[] THEN
  REAL_ARITH_TAC);;

let RFU_HH_CB = prove
 (`!(G1:real^N->real^N^N) G2 y L.
        (!p q. 1 <= p /\ p <= dimindex(:N) /\ 1 <= q /\ q <= dimindex(:N)
               ==> abs(G1 y$p$q) <= L /\ abs(G2 y$p$q) <= L)
        ==> rfu_cb 2 (rfu_hh G1 G2) y (&2 * L)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC RFU_CB_OF_BTUP THEN
  X_GEN_TAC `u:num->real^N` THEN REWRITE_TAC[rfu_btup] THEN DISCH_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC o
    C MP (ARITH_RULE `1 <= 1 /\ 1 <= 2`) o SPEC `1`) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC o
    C MP (ARITH_RULE `1 <= 2 /\ 2 <= 2`) o SPEC `2`) THEN
  ASM_REWRITE_TAC[rfu_hh; lmetric2] THEN ASM_SIMP_TAC[LRG_BASIS_DOT_MATRIX] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`i:num`; `j:num`]) THEN ASM_REWRITE_TAC[] THEN
  REAL_ARITH_TAC);;

let RFU_AA_CB = prove
 (`!(G1:real^N->real^N^N) G2 y L d.
        (!p q. 1 <= p /\ p <= dimindex(:N) /\ 1 <= q /\ q <= dimindex(:N)
               ==> abs(G1 y$p$q) <= L) /\
        (!i j l. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N) /\
                 1 <= l /\ l <= dimindex(:N)
                 ==> abs((christoffel G1 y (basis i) (basis j) -
                          christoffel G2 y (basis i) (basis j))$l) <= d)
        ==> rfu_cb 3 (rfu_aa G1 G2) y (&(dimindex(:N)) * L * d)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC RFU_CB_OF_BTUP THEN
  X_GEN_TAC `u:num->real^N` THEN REWRITE_TAC[rfu_btup] THEN DISCH_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC o
    C MP (ARITH_RULE `1 <= 1 /\ 1 <= 3`) o SPEC `1`) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC o
    C MP (ARITH_RULE `1 <= 2 /\ 2 <= 3`) o SPEC `2`) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC o
    C MP (ARITH_RULE `1 <= 3 /\ 3 <= 3`) o SPEC `3`) THEN
  ASM_REWRITE_TAC[rfu_aa; rfu_low3; rfu_dgam] THEN
  ASM_SIMP_TAC[DOT_BASIS; MATRIX_VECTOR_MUL_COMPONENT] THEN REWRITE_TAC[dot] THEN
  MATCH_MP_TAC RFU_SUM_ABS_BOUND_NUMSEG THEN X_GEN_TAC `l:num` THEN STRIP_TAC THEN
  REWRITE_TAC[REAL_ABS_MUL] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
  REWRITE_TAC[REAL_ABS_POS] THEN CONJ_TAC THENL
   [SUBGOAL_THEN `((G1:real^N->real^N^N) y$k)$l = G1 y$k$l` SUBST1_TAC THENL
     [REWRITE_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`k:num`; `l:num`] o
      check (fun th -> length(fst(strip_forall(concl th))) = 2)) THEN
    ASM_REWRITE_TAC[];
    FIRST_X_ASSUM(MP_TAC o SPECL [`i:num`; `j:num`; `l:num`] o
      check (fun th -> length(fst(strip_forall(concl th))) = 3)) THEN
    ASM_REWRITE_TAC[]]);;

(* x.(A y) = (B^-1 A x).(B y) for symmetric A, B with B invertible. *)

let RFU_DOT_REBASE = prove
 (`!(A:real^N^N) B x y.
        transp A = A /\ transp B = B /\ invertible B
        ==> x dot (A ** y) = (matrix_inv B ** (A ** x)) dot (B ** y)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM DOT_MATRIX_TRANSP_LMUL] THEN
  ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_ASSOC] THEN
  ASM_SIMP_TAC[MATRIX_INV; MATRIX_MUL_LID]);;

let RFU_Q_CB = prove
 (`!U (G1:real^N->real^N^N) G2 y L c1 c2.
        metric_field U G1 /\ metric_field U G2 /\ y IN U /\
        (!p q. 1 <= p /\ p <= dimindex(:N) /\ 1 <= q /\ q <= dimindex(:N)
               ==> abs(G1 y$p$q) <= L /\ abs(matrix_inv(G2 y)$p$q) <= L) /\
        rfu_cb 4 (lrm4 G1) y c1 /\ rfu_cb 4 (lrm4 G2) y c2
        ==> rfu_cb 4 (rfu_q G1 G2) y
                   (c1 + &(dimindex(:N)) * (&(dimindex(:N)) * L * L) * c2)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G1:real^N->real^N^N`] LRM4_TENSOR_FIELD) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G2:real^N->real^N^N`] LRM4_TENSOR_FIELD) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `transp((G1:real^N->real^N^N) y) = G1 y /\ transp((G2:real^N->real^N^N) y) = G2 y /\
                invertible((G2:real^N->real^N^N) y)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[RFU_METRIC_PROPS; LRG_METRIC_INVERTIBLE]; ALL_TAC] THEN
  MATCH_MP_TAC RFU_CB_OF_BTUP THEN X_GEN_TAC `u:num->real^N` THEN DISCH_TAC THEN
  SUBGOAL_THEN `?k. 1 <= k /\ k <= dimindex(:N) /\ (u:num->real^N) 3 = basis k`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `rfu_btup 4 (u:num->real^N)` THEN REWRITE_TAC[rfu_btup] THEN
    DISCH_THEN MATCH_MP_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC
   `w = matrix_inv((G2:real^N->real^N^N) y) ** ((G1:real^N->real^N^N) y ** basis k)` THEN
  SUBGOAL_THEN
   `rfu_q (G1:real^N->real^N^N) G2 y u =
    lrm4 G1 y u - lrm4 G2 y (\j. if j = 3 then w else u j)`
  SUBST1_TAC THENL
   [REWRITE_TAC[rfu_q; rfu_low4; rfu_drm; lrm4] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[MATRIX_VECTOR_MUL_SUB_LDISTRIB; DOT_RSUB] THEN AP_TERM_TAC THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "w" THEN MATCH_MP_TAC RFU_DOT_REBASE THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `abs a <= c1 /\ abs b <= c2 ==> abs(a - b) <= c1 + c2`) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC RFU_CB_BTUP THEN MAP_EVERY EXISTS_TAC [`4`; `U:real^N->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC RFU_SLOT_VEC_BOUND THEN MAP_EVERY EXISTS_TAC [`4`; `U:real^N->bool`] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
  X_GEN_TAC `q:num` THEN STRIP_TAC THEN EXPAND_TAC "w" THEN
  ASM_SIMP_TAC[MATRIX_VECTOR_MUL_BASIS; MATRIX_VECTOR_MUL_COMPONENT] THEN REWRITE_TAC[dot] THEN
  MATCH_MP_TAC RFU_SUM_ABS_BOUND_NUMSEG THEN X_GEN_TAC `p:num` THEN STRIP_TAC THEN
  ASM_SIMP_TAC[column; LAMBDA_BETA] THEN
  REWRITE_TAC[REAL_ABS_MUL] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
  REWRITE_TAC[REAL_ABS_POS] THEN CONJ_TAC THEN ASM_MESON_TAC[]);;

let RFU_DENS_CB = prove
 (`!U (G1:real^N->real^N^N) G2 y L c.
        metric_field U G1 /\ metric_field U G2 /\ y IN U /\
        (!p q. 1 <= p /\ p <= dimindex(:N) /\ 1 <= q /\ q <= dimindex(:N)
               ==> abs(matrix_inv(G1 y)$p$q) <= L) /\
        rfu_cb 2 (rfu_hh G1 G2) y c /\ rfu_cb 3 (rfu_aa G1 G2) y c /\
        rfu_cb 4 (rfu_q G1 G2) y c
        ==> pde_kot_density G1 G2 y <=
            &(CARD(index_tuples 2 (:N))) pow 2 * L pow 2 * c pow 2 +
            &(CARD(index_tuples 3 (:N))) pow 2 * L pow 3 * c pow 2 +
            &(CARD(index_tuples 4 (:N))) pow 2 * L pow 4 * c pow 2`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G1:real^N->real^N^N`; `G2:real^N->real^N^N`; `y:real^N`]
                RFU_DENS_TERMS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN
  MATCH_MP_TAC(REAL_ARITH `a <= a' /\ b <= b' /\ c <= c' ==> a + b + c <= a' + b' + c'`) THEN
  REPEAT CONJ_TAC THEN MATCH_MP_TAC RFU_LTNORM2_CB THEN ASM_REWRITE_TAC[]);;

(* Conversely the density bounds the Christoffel difference. *)

let RFU_AA_SMALL = prove
 (`!U (G1:real^N->real^N^N) G2 y L i j l.
        metric_field U G1 /\ metric_field U G2 /\ y IN U /\ &0 <= L /\
        (!p. 1 <= p /\ p <= dimindex(:N) ==> G1 y$p$p <= L) /\
        (!p q. 1 <= p /\ p <= dimindex(:N) /\ 1 <= q /\ q <= dimindex(:N)
               ==> abs(matrix_inv(G1 y)$p$q) <= L) /\
        1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N) /\
        1 <= l /\ l <= dimindex(:N)
        ==> ((christoffel G1 y (basis i) (basis j) -
              christoffel G2 y (basis i) (basis j))$l) pow 2
            <= ((&(dimindex(:N)) * L) pow 2 * L pow 3) * pde_kot_density G1 G2 y`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `X = christoffel (G1:real^N->real^N^N) y (basis i) (basis j) -
                  christoffel G2 y (basis i) (basis j)` THEN
  SUBGOAL_THEN
   `&0 <= pde_kot_density (G1:real^N->real^N^N) G2 y /\
    ltnorm2 3 G1 (rfu_aa G1 G2) y <= pde_kot_density G1 G2 y`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`U:real^N->bool`; `G1:real^N->real^N^N`; `G2:real^N->real^N^N`;
                   `y:real^N`] RFU_DENS_TERMS) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G1:real^N->real^N^N`; `G2:real^N->real^N^N`]
                RFU_DENS_FIELDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `invertible((G1:real^N->real^N^N) y)` ASSUME_TAC THENL
   [ASM_MESON_TAC[LRG_METRIC_INVERTIBLE]; ALL_TAC] THEN
  ABBREV_TAC `e = pde_kot_density (G1:real^N->real^N^N) G2 y` THEN
  SUBGOAL_THEN
   `!k. 1 <= k /\ k <= dimindex(:N)
        ==> abs(((G1:real^N->real^N^N) y ** (X:real^N))$k) <= sqrt(e * L pow 3)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`3`; `U:real^N->bool`; `G1:real^N->real^N^N`;
                   `rfu_aa (G1:real^N->real^N^N) G2`; `y:real^N`; `L:real`] RFU_CB_LTNORM2) THEN
    ASM_REWRITE_TAC[rfu_cb] THEN
    DISCH_THEN(MP_TAC o SPEC `rfa_tup3 i j k`) THEN ASM_SIMP_TAC[RFA_TUP3_IN] THEN
    MATCH_MP_TAC(REAL_ARITH `x = y /\ c <= d ==> abs y <= c ==> abs x <= d`) THEN
    CONJ_TAC THENL
     [REWRITE_TAC[rfu_aa; rfu_low3; rfu_dgam; rfa_tup3] THEN CONV_TAC NUM_REDUCE_CONV THEN
      ASM_SIMP_TAC[DOT_BASIS];
      MATCH_MP_TAC SQRT_MONO_LE THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      ASM_SIMP_TAC[REAL_POW_LE] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(X:real^N) = matrix_inv((G1:real^N->real^N^N) y) ** (G1 y ** X)`
  SUBST1_TAC THENL
   [REWRITE_TAC[MATRIX_VECTOR_MUL_ASSOC] THEN
    ASM_SIMP_TAC[MATRIX_INV; MATRIX_VECTOR_MUL_LID];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= e * L pow 3` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_POW_LE] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `abs((matrix_inv((G1:real^N->real^N^N) y) ** (G1 y ** (X:real^N)))$l) <=
    &(dimindex(:N)) * L * sqrt(e * L pow 3)`
  MP_TAC THENL
   [ASM_SIMP_TAC[MATRIX_VECTOR_MUL_COMPONENT] THEN REWRITE_TAC[dot] THEN
    MATCH_MP_TAC RFU_SUM_ABS_BOUND_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    REWRITE_TAC[REAL_ABS_MUL] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
    ASM_SIMP_TAC[REAL_ABS_POS];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (REAL_ARITH `abs x <= y ==> abs x <= abs y`)) THEN
  REWRITE_TAC[REAL_LE_SQUARE_ABS] THEN
  MATCH_MP_TAC(REAL_ARITH `y = z ==> x <= y ==> x <= z`) THEN
  REWRITE_TAC[REAL_POW_MUL] THEN ASM_SIMP_TAC[SQRT_POW_2] THEN REAL_ARITH_TAC);;

(* ========================================================================= *)
(* The Christoffel difference of two flows grows at most linearly in time.   *)
(* The time derivative of the Christoffel symbols is bounded by nabla Rm     *)
(* (RFU_LDGAMMA_BOUND); hence the difference is Lipschitz in time            *)
(* (RFU_GAMMA_DIFF_LIP), and it vanishes at the initial time because the     *)
(* density does (RFU_GAMMA_DIFF_BOUND).                                      *)
(* ========================================================================= *)

let RFU_GAMMA_COMP_DERIV = prove
 (`!U a b (G:real->real^N->real^N^N) t y u v l.
        lricci_flow U a b G /\ a < t /\ t < b /\ y IN U /\ 1 <= l /\ l <= dimindex(:N)
        ==> ((\r. (christoffel (G r) y u v)$l) has_real_derivative
             (ldgamma G t y u v)$l) (atreal t)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `a:real`; `b:real`; `G:real->real^N->real^N^N`;
                 `t:real`; `y:real^N`; `u:real^N`; `v:real^N`] LRG_FLOW_GAMMA_VDERIV) THEN
  ASM_REWRITE_TAC[GSYM ldgamma] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`\r. christoffel ((G:real->real^N->real^N^N) r) y u v`;
                 `ldgamma (G:real->real^N->real^N^N) t y u v`; `t:real`; `l:num`]
                LRG_VDERIV_COMPONENT_REAL) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let RFU_LDGAMMA_BOUND = prove
 (`!L B. ?D. &0 <= D /\
       !U a b (G:real->real^N->real^N^N) t y.
         lricci_flow U a b G /\ a < t /\ t < b /\ y IN U /\ &0 <= L /\
         (!p. 1 <= p /\ p <= dimindex(:N) ==> G t y$p$p <= L) /\
         (!p q. 1 <= p /\ p <= dimindex(:N) /\ 1 <= q /\ q <= dimindex(:N)
                ==> abs(matrix_inv(G t y)$p$q) <= L) /\
         lrm_deriv_norm2 1 (G t) y <= B
         ==> !i j l. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N) /\
                     1 <= l /\ l <= dimindex(:N)
                     ==> abs((ldgamma G t y (basis i) (basis j))$l) <= D`,
  REPEAT GEN_TAC THEN
  ABBREV_TAC `c5 = sqrt(abs B * abs L pow 5)` THEN
  SUBGOAL_THEN `&0 <= c5` ASSUME_TAC THENL
   [EXPAND_TAC "c5" THEN MATCH_MP_TAC SQRT_POS_LE THEN MATCH_MP_TAC REAL_LE_MUL THEN
    SIMP_TAC[REAL_ABS_POS; REAL_POW_LE];
    ALL_TAC] THEN
  EXISTS_TAC `&(dimindex(:N)) * abs L *
              (&3 * (&(dimindex(:N)) * &(dimindex(:N)) * abs L * c5))` THEN
  CONJ_TAC THENL
   [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_REWRITE_TAC[REAL_POS; REAL_ABS_POS];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `abs L = L` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `metric_field U ((G:real->real^N->real^N^N) t)` ASSUME_TAC THENL
   [ASM_MESON_TAC[RFU_FLOW_METRIC]; ALL_TAC] THEN
  (* components of nabla Rm *)
  SUBGOAL_THEN
   `!al. al IN index_tuples 5 (:N)
         ==> abs(lnabla 4 ((G:real->real^N->real^N^N) t) (lrm4 (G t)) y
                   (\r. basis(al r))) <= c5`
  (LABEL_TAC "R5") THENL
   [MP_TAC(ISPECL [`U:real^N->bool`; `(G:real->real^N->real^N^N) t`] LRM4_TENSOR_FIELD) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`4`; `U:real^N->bool`; `(G:real->real^N->real^N^N) t`;
                   `lrm4 ((G:real->real^N->real^N^N) t)`] LRG_LNABLA_ITER_FIELD) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `1`) THEN
    REWRITE_TAC[RFA_LNABLA_ITER_1] THEN CONV_TAC NUM_REDUCE_CONV THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`5`; `U:real^N->bool`; `(G:real->real^N->real^N^N) t`;
                   `lnabla 4 ((G:real->real^N->real^N^N) t) (lrm4 (G t))`;
                   `y:real^N`; `L:real`] RFU_CB_LTNORM2) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `rfu_cb 5 (lnabla 4 ((G:real->real^N->real^N^N) t) (lrm4 (G t))) y c5`
    MP_TAC THENL [ALL_TAC; REWRITE_TAC[rfu_cb]] THEN
    MATCH_MP_TAC RFU_CB_MONO THEN
    EXISTS_TAC `sqrt(ltnorm2 5 ((G:real->real^N->real^N^N) t)
                       (lnabla 4 (G t) (lrm4 (G t))) y * L pow 5)` THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "c5" THEN MATCH_MP_TAC SQRT_MONO_LE THEN
    SUBGOAL_THEN `abs L = L` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_POW_LE] THEN
    UNDISCH_TAC `lrm_deriv_norm2 1 ((G:real->real^N->real^N^N) t) y <= B` THEN
    REWRITE_TAC[lrm_deriv_norm2; RFA_LNABLA_ITER_1] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* components of nabla Ric *)
  SUBGOAL_THEN
   `!x1 x2 x3. 1 <= x1 /\ x1 <= dimindex(:N) /\ 1 <= x2 /\ x2 <= dimindex(:N) /\
               1 <= x3 /\ x3 <= dimindex(:N)
               ==> abs(lnabla 2 ((G:real->real^N->real^N^N) t) (lric2 (G t)) y
                         (\r. basis(rfa_tup3 x1 x2 x3 r)))
                   <= &(dimindex(:N)) * &(dimindex(:N)) * L * c5`
  (LABEL_TAC "R3") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `(G:real->real^N->real^N^N) t`; `y:real^N`;
                   `x1:num`; `x2:num`; `x3:num`] RFA_N3_R5) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC RFU_SUM_ABS_BOUND_NUMSEG THEN X_GEN_TAC `p:num` THEN STRIP_TAC THEN
    BETA_TAC THEN
    MATCH_MP_TAC RFU_SUM_ABS_BOUND_NUMSEG THEN X_GEN_TAC `q:num` THEN STRIP_TAC THEN
    BETA_TAC THEN
    REWRITE_TAC[REAL_ABS_MUL] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
    ASM_SIMP_TAC[REAL_ABS_POS] THEN USE_THEN "R5" MATCH_MP_TAC THEN
    REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC RFA_TUP5_IN THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `a:real`; `b:real`; `G:real->real^N->real^N^N`;
                 `t:real`; `y:real^N`; `i:num`; `j:num`; `l:num`] RFA_LDGAMMA_N3) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[REAL_ABS_NEG] THEN
  MATCH_MP_TAC RFU_SUM_ABS_BOUND_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
  REWRITE_TAC[REAL_ABS_MUL] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
  ASM_SIMP_TAC[REAL_ABS_POS] THEN
  MATCH_MP_TAC(REAL_ARITH
   `abs x <= c /\ abs y <= c /\ abs z <= c ==> abs(x + y - z) <= &3 * c`) THEN
  REPEAT CONJ_TAC THEN USE_THEN "R3" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let RFU_GAMMA_DIFF_LIP = prove
 (`!U a b (F1:real->real^N->real^N^N) F2 z D r t i j l.
        lricci_flow U a b F1 /\ lricci_flow U a b F2 /\ z IN U /\
        a < r /\ r <= t /\ t < b /\ 1 <= l /\ l <= dimindex(:N) /\
        (!s. r <= s /\ s <= t
             ==> abs((ldgamma F1 s z (basis i) (basis j))$l) <= D /\
                 abs((ldgamma F2 s z (basis i) (basis j))$l) <= D)
        ==> abs((christoffel (F1 t) z (basis i) (basis j) -
                 christoffel (F2 t) z (basis i) (basis j))$l -
                (christoffel (F1 r) z (basis i) (basis j) -
                 christoffel (F2 r) z (basis i) (basis j))$l) <= (&2 * D) * (t - r)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`\s. (christoffel ((F1:real->real^N->real^N^N) s) z (basis i) (basis j) -
          christoffel (F2 s) z (basis i) (basis j))$l`;
    `\s. (ldgamma (F1:real->real^N->real^N^N) s z (basis i) (basis j))$l -
         (ldgamma F2 s z (basis i) (basis j))$l`;
    `real_interval[r,t]`; `&2 * D`] REAL_DIFFERENTIABLE_BOUND) THEN
  REWRITE_TAC[IS_REALINTERVAL_INTERVAL; IN_REAL_INTERVAL] THEN ANTS_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
      REWRITE_TAC[VECTOR_SUB_COMPONENT] THEN
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUB THEN CONJ_TAC THEN
      MATCH_MP_TAC RFU_GAMMA_COMP_DERIV THEN
      MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `a:real`; `b:real`] THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      FIRST_X_ASSUM(MP_TAC o SPEC `s:real`) THEN ASM_REWRITE_TAC[] THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`t:real`; `r:real`]) THEN
  ASM_REWRITE_TAC[REAL_LE_REFL] THEN
  MATCH_MP_TAC(REAL_ARITH `y = z ==> x <= y ==> x <= z`) THEN
  AP_TERM_TAC THEN ASM_REAL_ARITH_TAC);;

let RFU_ALG_EPS = prove
 (`!K g. &0 <= K /\ &0 < g ==> K * (g / (K + &1)) < g`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `x = g / (K + &1)` THEN
  SUBGOAL_THEN `&0 < x` ASSUME_TAC THENL
   [EXPAND_TAC "x" THEN MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `g = x * (K + &1)` SUBST1_TAC THENL
   [EXPAND_TAC "x" THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_DIV_RMUL THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let RFU_GAMMA_DIFF_BOUND = prove
 (`!U a b (F1:real->real^N->real^N^N) F2 z b1 L D t i j l.
        lricci_flow U a b F1 /\ lricci_flow U a b F2 /\ z IN U /\ b1 < b /\
        a <= t /\ t <= b1 /\ &0 <= L /\ &0 <= D /\
        1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N) /\
        1 <= l /\ l <= dimindex(:N) /\
        (!s. a <= s /\ s <= b1
             ==> metric_field U (F1 s) /\ metric_field U (F2 s) /\
                 (!p. 1 <= p /\ p <= dimindex(:N) ==> F1 s z$p$p <= L) /\
                 (!p q. 1 <= p /\ p <= dimindex(:N) /\ 1 <= q /\ q <= dimindex(:N)
                        ==> abs(matrix_inv(F1 s z)$p$q) <= L)) /\
        (!s. a < s /\ s <= b1
             ==> abs((ldgamma F1 s z (basis i) (basis j))$l) <= D /\
                 abs((ldgamma F2 s z (basis i) (basis j))$l) <= D) /\
        (!eps. &0 < eps
               ==> ?d. &0 < d /\
                       !r. a <= r /\ r < a + d /\ r <= b1
                           ==> pde_kot_density (F1 r) (F2 r) z < eps)
        ==> abs((christoffel (F1 t) z (basis i) (basis j) -
                 christoffel (F2 t) z (basis i) (basis j))$l) <= (&2 * D) * (t - a)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(LABEL_TAC "CT" o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "pde_kot_density")) (concl th))) THEN
  FIRST_X_ASSUM(LABEL_TAC "LD" o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "ldgamma")) (concl th))) THEN
  FIRST_X_ASSUM(LABEL_TAC "MF" o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "metric_field")) (concl th))) THEN
  ABBREV_TAC `K = (&(dimindex(:N)) * L) pow 2 * L pow 3` THEN
  SUBGOAL_THEN `&0 <= K` ASSUME_TAC THENL
   [EXPAND_TAC "K" THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_SIMP_TAC[REAL_POW_LE; REAL_LE_POW_2];
    ALL_TAC] THEN
  (* the component at time r is controlled by the density *)
  SUBGOAL_THEN
   `!r. a <= r /\ r <= b1
        ==> ((christoffel ((F1:real->real^N->real^N^N) r) z (basis i) (basis j) -
              christoffel (F2 r) z (basis i) (basis j))$l) pow 2
            <= K * pde_kot_density (F1 r) (F2 r) z`
  (LABEL_TAC "SM") THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "K" THEN
    USE_THEN "MF" (MP_TAC o SPEC `r:real`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    MATCH_MP_TAC RFU_AA_SMALL THEN EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  ABBREV_TAC `gap = abs((christoffel ((F1:real->real^N->real^N^N) t) z (basis i) (basis j) -
                         christoffel (F2 t) z (basis i) (basis j))$l) - (&2 * D) * (t - a)` THEN
  SUBGOAL_THEN `&0 < gap` ASSUME_TAC THENL
   [EXPAND_TAC "gap" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "CT" (MP_TAC o SPEC `gap pow 2 / (K + &1)`) THEN ANTS_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN ASM_SIMP_TAC[REAL_POW_LT] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!r. a <= r /\ r < a + d /\ r <= b1
        ==> abs((christoffel ((F1:real->real^N->real^N^N) r) z (basis i) (basis j) -
                 christoffel (F2 r) z (basis i) (basis j))$l) < gap`
  (LABEL_TAC "SMALL") THENL
   [REPEAT STRIP_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `abs x < abs g /\ &0 < g ==> abs x < g`) THEN
    ASM_REWRITE_TAC[REAL_LT_SQUARE_ABS] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `K * pde_kot_density ((F1:real->real^N->real^N^N) r) (F2 r) z` THEN
    CONJ_TAC THENL
     [USE_THEN "SM" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `K * (gap pow 2 / (K + &1))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LT_IMP_LE THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC RFU_ALG_EPS THEN ASM_SIMP_TAC[REAL_POW_LT]];
    ALL_TAC] THEN
  ASM_CASES_TAC `t:real = a` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    USE_THEN "SMALL" (MP_TAC o SPEC `a:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC
     `abs((christoffel ((F1:real->real^N->real^N^N) a) z (basis i) (basis j) -
           christoffel (F2 a) z (basis i) (basis j))$l) - (&2 * D) * (a - a) = gap` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `r = a + min d (t - a) / &2` THEN
  SUBGOAL_THEN `a < r /\ r < a + d /\ r <= t` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "r" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "SMALL" (MP_TAC o SPEC `r:real`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `a:real`; `b:real`; `F1:real->real^N->real^N^N`;
                 `F2:real->real^N->real^N^N`; `z:real^N`; `D:real`; `r:real`; `t:real`;
                 `i:num`; `j:num`; `l:num`] RFU_GAMMA_DIFF_LIP) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN USE_THEN "LD" MATCH_MP_TAC THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(&2 * D) * (t - r) <= (&2 * D) * (t - a)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC
   `abs((christoffel ((F1:real->real^N->real^N^N) t) z (basis i) (basis j) -
         christoffel (F2 t) z (basis i) (basis j))$l) - (&2 * D) * (t - a) = gap` THEN
  REAL_ARITH_TAC);;

(* ========================================================================= *)
(* The uniform bound of the Kotschwar density.  Locally, in a                *)
(* chart where both flows stay L-equivalent to the Euclidean metric at z,   *)
(* with |Rm|^2, |nabla Rm|^2 <= B and the density tending to 0 at the       *)
(* initial time, the density is bounded in terms of L, B and the length of  *)
(* the time interval (RFU_LOCAL_DENS_BOUND).                                 *)
(* ========================================================================= *)

let RFU_LRM4_CB = prove
 (`!U (G:real^N->real^N^N) y L B.
        metric_field U G /\ y IN U /\ &0 <= L /\
        (!p. 1 <= p /\ p <= dimindex(:N) ==> G y$p$p <= L) /\
        lrm_deriv_norm2 0 G y <= B
        ==> rfu_cb 4 (lrm4 G) y (sqrt(abs B * L pow 4))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`] LRM4_TENSOR_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC RFU_CB_MONO THEN
  EXISTS_TAC `sqrt(ltnorm2 4 (G:real^N->real^N^N) (lrm4 G) y * L pow 4)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC RFU_CB_LTNORM2 THEN EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC SQRT_MONO_LE THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_SIMP_TAC[REAL_POW_LE] THEN
    UNDISCH_TAC `lrm_deriv_norm2 0 (G:real^N->real^N^N) y <= B` THEN
    REWRITE_TAC[lrm_deriv_norm2; lnabla_iter; ADD_CLAUSES] THEN REAL_ARITH_TAC]);;

let RFU_LOCAL_DENS_BOUND = prove
 (`!L B Tl. &0 <= L
     ==> ?Md. !U a b (F1:real->real^N->real^N^N) F2 z b1 t.
       lricci_flow U a b F1 /\ lricci_flow U a b F2 /\ z IN U /\ b1 < b /\
       b1 - a <= Tl /\ a <= t /\ t <= b1 /\
       (!s. a <= s /\ s <= b1
            ==> metric_field U (F1 s) /\ metric_field U (F2 s) /\
                (!v. v dot (F1 s z ** v) <= L * (v dot v) /\
                     v dot v <= L * (v dot (F1 s z ** v)) /\
                     v dot (F2 s z ** v) <= L * (v dot v) /\
                     v dot v <= L * (v dot (F2 s z ** v))) /\
                lrm_deriv_norm2 0 (F1 s) z <= B /\ lrm_deriv_norm2 0 (F2 s) z <= B /\
                lrm_deriv_norm2 1 (F1 s) z <= B /\ lrm_deriv_norm2 1 (F2 s) z <= B) /\
       (!eps. &0 < eps
              ==> ?d. &0 < d /\
                      !r. a <= r /\ r < a + d /\ r <= b1
                          ==> pde_kot_density (F1 r) (F2 r) z < eps)
       ==> pde_kot_density (F1 t) (F2 t) z <= Md`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL [`L:real`; `B:real`] (INST_TYPE [`:N`,`:N`] RFU_LDGAMMA_BOUND)) THEN
  DISCH_THEN(X_CHOOSE_THEN `D:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "D"))) THEN
  ABBREV_TAC `c4 = sqrt(abs B * L pow 4)` THEN
  SUBGOAL_THEN `&0 <= c4` ASSUME_TAC THENL
   [EXPAND_TAC "c4" THEN MATCH_MP_TAC SQRT_POS_LE THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_SIMP_TAC[REAL_ABS_POS; REAL_POW_LE];
    ALL_TAC] THEN
  ABBREV_TAC `ca = &(dimindex(:N)) * L * ((&2 * D) * abs Tl)` THEN
  ABBREV_TAC `cq = c4 + &(dimindex(:N)) * (&(dimindex(:N)) * L * L) * c4` THEN
  SUBGOAL_THEN `&0 <= &2 * L /\ &0 <= ca /\ &0 <= cq` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["ca"; "cq"] THEN REPEAT CONJ_TAC THEN
    TRY(MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC) THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_REWRITE_TAC[REAL_POS; REAL_ABS_POS] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `c = &2 * L + ca + cq` THEN
  EXISTS_TAC `&(CARD(index_tuples 2 (:N))) pow 2 * L pow 2 * c pow 2 +
              &(CARD(index_tuples 3 (:N))) pow 2 * L pow 3 * c pow 2 +
              &(CARD(index_tuples 4 (:N))) pow 2 * L pow 4 * c pow 2` THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(LABEL_TAC "CT" o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "pde_kot_density")) (concl th))) THEN
  FIRST_X_ASSUM(LABEL_TAC "BD" o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "metric_field")) (concl th))) THEN
  (* entries at every time *)
  SUBGOAL_THEN
   `!s. a <= s /\ s <= b1
        ==> metric_field U ((F1:real->real^N->real^N^N) s) /\ metric_field U (F2 s) /\
            (!p q. 1 <= p /\ p <= dimindex(:N) /\ 1 <= q /\ q <= dimindex(:N)
                   ==> abs(F1 s z$p$q) <= L /\ abs(matrix_inv(F1 s z)$p$q) <= L /\
                       abs(F2 s z$p$q) <= L /\ abs(matrix_inv(F2 s z)$p$q) <= L) /\
            (!p. 1 <= p /\ p <= dimindex(:N) ==> F1 s z$p$p <= L /\ F2 s z$p$p <= L)`
  (LABEL_TAC "EN") THENL
   [X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    USE_THEN "BD" (MP_TAC o SPEC `s:real`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `(F1:real->real^N->real^N^N) s`; `z:real^N`; `L:real`]
                  RFU_EQUIV_ENTRIES) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; STRIP_TAC] THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `(F2:real->real^N->real^N^N) s`; `z:real^N`; `L:real`]
                  RFU_EQUIV_ENTRIES) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; STRIP_TAC] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  USE_THEN "EN" (MP_TAC o SPEC `t:real`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  USE_THEN "BD" (MP_TAC o SPEC `t:real`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MATCH_MP_TAC RFU_DENS_CB THEN EXISTS_TAC `U:real^N->bool` THEN ASM_SIMP_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [(* the metric difference *)
    MATCH_MP_TAC RFU_CB_MONO THEN EXISTS_TAC `&2 * L` THEN CONJ_TAC THENL
     [MATCH_MP_TAC RFU_HH_CB THEN ASM_SIMP_TAC[];
      EXPAND_TAC "c" THEN
      MAP_EVERY UNDISCH_TAC [`&0 <= ca`; `&0 <= cq`] THEN REAL_ARITH_TAC];
    (* the Christoffel difference *)
    MATCH_MP_TAC RFU_CB_MONO THEN EXISTS_TAC `ca:real` THEN CONJ_TAC THENL
     [EXPAND_TAC "ca" THEN MATCH_MP_TAC RFU_AA_CB THEN ASM_SIMP_TAC[] THEN
      MAP_EVERY X_GEN_TAC [`i:num`; `j:num`; `l:num`] THEN STRIP_TAC THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&2 * D) * (t - a)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC RFU_GAMMA_DIFF_BOUND THEN
        MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `b:real`; `b1:real`; `L:real`] THEN
        ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
         [X_GEN_TAC `s:real` THEN DISCH_TAC THEN
          USE_THEN "EN" (MP_TAC o SPEC `s:real`) THEN
          ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN SIMP_TAC[];
          X_GEN_TAC `s:real` THEN STRIP_TAC THEN
          USE_THEN "EN" (MP_TAC o SPEC `s:real`) THEN
          ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
          USE_THEN "BD" (MP_TAC o SPEC `s:real`) THEN
          ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
          CONJ_TAC THENL
           [USE_THEN "D" (MP_TAC o SPECL [`U:real^N->bool`; `a:real`; `b:real`;
                                          `F1:real->real^N->real^N^N`; `s:real`; `z:real^N`]);
            USE_THEN "D" (MP_TAC o SPECL [`U:real^N->bool`; `a:real`; `b:real`;
                                          `F2:real->real^N->real^N^N`; `s:real`; `z:real^N`])] THEN
          (ANTS_TAC THENL
            [ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC;
             DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]])];
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC];
      EXPAND_TAC "c" THEN
      MAP_EVERY UNDISCH_TAC [`&0 <= &2 * L`; `&0 <= cq`] THEN REAL_ARITH_TAC];
    (* the curvature difference *)
    MATCH_MP_TAC RFU_CB_MONO THEN EXISTS_TAC `cq:real` THEN CONJ_TAC THENL
     [EXPAND_TAC "cq" THEN MATCH_MP_TAC RFU_Q_CB THEN EXISTS_TAC `U:real^N->bool` THEN
      ASM_SIMP_TAC[] THEN EXPAND_TAC "c4" THEN CONJ_TAC THEN
      MATCH_MP_TAC RFU_LRM4_CB THEN EXISTS_TAC `U:real^N->bool` THEN ASM_SIMP_TAC[];
      EXPAND_TAC "c" THEN
      MAP_EVERY UNDISCH_TAC [`&0 <= &2 * L`; `&0 <= ca`] THEN REAL_ARITH_TAC]]);;

(* A function from a in the sense of pde_sfun_from is right-continuous in    *)
(* time at a, at each point.                                                 *)

let RFU_SFUN_TIME_CONT = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) a b (e:real->A->real) x eps.
     smooth_manifold_atlas top atlas /\ pde_sfun_from atlas a b e /\
     x IN topspace top /\ a < b /\ &0 < eps
     ==> ?d. &0 < d /\ !r. a <= r /\ r < b /\ r < a + d ==> abs(e r x - e a x) < eps`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`]
         CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  SPEC_TAC(`chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)`,
           `c:(A->bool)#(A->real^N)`) THEN
  GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `pde_sfun_from (atlas:((A->bool)#(A->real^N))->bool) a b e` THEN
  REWRITE_TAC[pde_sfun_from] THEN DISCH_THEN(MP_TAC o SPEC `c:(A->bool)#(A->real^N)`) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d0:real` (X_CHOOSE_THEN `FF:real^(1,N)finite_sum->real^1`
    STRIP_ASSUME_TAC)) THEN
  ABBREV_TAC `y0 = SND(c:(A->bool)#(A->real^N)) x` THEN
  SUBGOAL_THEN `(y0:real^N) IN IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c) /\
                chart_inv c y0 = (x:A)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "y0" THEN ASM_SIMP_TAC[FUN_IN_IMAGE]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(FF:real^(1,N)finite_sum->real^1) continuous at (pastecart (lift a) y0)`
  MP_TAC THENL
   [MP_TAC(ISPECL [`FF:real^(1,N)finite_sum->real^1`;
                   `interval(lift(a - d0),lift b) PCROSS
                    IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)`]
                  CONTINUOUS_ON_EQ_CONTINUOUS_AT) THEN
    ANTS_TAC THENL [MATCH_MP_TAC OPEN_PCROSS THEN ASM_REWRITE_TAC[OPEN_INTERVAL]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o fst o EQ_IMP_RULE) THEN
    ANTS_TAC THENL [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[continuous_at] THEN DISCH_THEN(MP_TAC o SPEC `eps:real`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `r:real` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `pastecart (lift r) (y0:real^N)`) THEN
  REWRITE_TAC[DIST_PASTECART_CANCEL; DIST_LIFT] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `(FF:real^(1,N)finite_sum->real^1) (pastecart (lift r) y0) = lift(e r (x:A)) /\
    FF (pastecart (lift a) y0) = lift(e a x)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN ASM_SIMP_TAC[REAL_LE_REFL]; ALL_TAC] THEN
  ASM_REWRITE_TAC[DIST_LIFT]);;

(* The uniform density bound on a manifold: normalise the preferred chart at *)
(* x by a linear map so that g1(a) is Euclidean at x, then apply the local   *)
(* bound.                                                                     *)

let RFU_DENS_UNIFORM = prove
 (`!Lam B Tl. &0 <= Lam
     ==> ?M. !(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) a b g1 g2 b1 x t.
       ricci_flow_from (top,atlas) a b g1 /\ ricci_flow_from (top,atlas) a b g2 /\
       (!x. x IN topspace top ==> g1 a x = g2 a x) /\
       b1 < b /\ b1 - a <= Tl /\ a <= t /\ t <= b1 /\ x IN topspace top /\
       (!s v. a <= s /\ s <= b1
              ==> v dot (g1 s x ** v) <= Lam * (v dot (g1 a x ** v)) /\
                  v dot (g1 a x ** v) <= Lam * (v dot (g1 s x ** v)) /\
                  v dot (g2 s x ** v) <= Lam * (v dot (g1 a x ** v)) /\
                  v dot (g1 a x ** v) <= Lam * (v dot (g2 s x ** v))) /\
       (!s. a <= s /\ s <= b1
            ==> rfa_rmd2 0 atlas (g1 s) x <= B /\ rfa_rmd2 0 atlas (g2 s) x <= B /\
                rfa_rmd2 1 atlas (g1 s) x <= B /\ rfa_rmd2 1 atlas (g2 s) x <= B)
       ==> pde_mkot_density atlas (g1 t) (g2 t) x <= M`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL [`Lam:real`; `B:real`; `Tl:real`]
               (INST_TYPE [`:N`,`:N`] RFU_LOCAL_DENS_BOUND)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `Md:real` (LABEL_TAC "LB")) THEN
  EXISTS_TAC `Md:real` THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(LABEL_TAC "RB" o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "rfa_rmd2")) (concl th))) THEN
  FIRST_X_ASSUM(LABEL_TAC "EQ" o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "dot")) (concl th))) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `a:real`; `b:real`; `g1:real->A->real^N^N`] GRGT_RF_METRIC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `a:real`; `b:real`; `g2:real->A->real^N^N`] GRGT_RF_METRIC) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`]
         CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)` THEN
  ABBREV_TAC `U = IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)` THEN
  ABBREV_TAC `y0 = SND(c:(A->bool)#(A->real^N)) x` THEN
  SUBGOAL_THEN `(y0:real^N) IN U` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["y0"; "U"] THEN ASM_SIMP_TAC[FUN_IN_IMAGE]; ALL_TAC] THEN
  ABBREV_TAC `G1 = \s. metric_local atlas (c:(A->bool)#(A->real^N)) ((g1:real->A->real^N^N) s)` THEN
  ABBREV_TAC `G2 = \s. metric_local atlas (c:(A->bool)#(A->real^N)) ((g2:real->A->real^N^N) s)` THEN
  (* the local flows *)
  SUBGOAL_THEN `lricci_flow U a b (G1:real->real^N->real^N^N) /\
                lricci_flow U a b (G2:real->real^N->real^N^N)` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["U"; "G1"; "G2"] THEN CONJ_TAC THEN
    MATCH_MP_TAC LRG_RICCI_FLOW_ON_CHART THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. a <= s /\ s < b
        ==> metric_field U ((G1:real->real^N->real^N^N) s) /\
            metric_field U ((G2:real->real^N->real^N^N) s)`
  (LABEL_TAC "MFG") THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN MAP_EVERY EXPAND_TAC ["U"; "G1"; "G2"] THEN
    CONJ_TAC THENL
     [SUBGOAL_THEN `riemannian_metric atlas ((g1:real->A->real^N^N) s)` MP_TAC THENL
       [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC];
      SUBGOAL_THEN `riemannian_metric atlas ((g2:real->A->real^N^N) s)` MP_TAC THENL
       [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC]] THEN
    REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. (G1:real->real^N->real^N^N) s y0 = g1 s (x:A) /\
        (G2:real->real^N->real^N^N) s y0 = g2 s x`
  (LABEL_TAC "GX") THENL
   [GEN_TAC THEN MAP_EVERY EXPAND_TAC ["G1"; "G2"; "y0"; "c"] THEN
    CONJ_TAC THEN MATCH_MP_TAC METRIC_LOCAL_AT THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the normalising linear chart *)
  MP_TAC(ISPECL [`U:real^N->bool`; `(G1:real->real^N->real^N^N) a`; `y0:real^N`]
                RFU_NORMALIZE) THEN
  ANTS_TAC THENL
   [USE_THEN "MFG" (MP_TAC o SPEC `a:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `M:real^N^N` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `h = \z:real^N. matrix_inv(M:real^N^N) ** z` THEN
  ABBREV_TAC `U' = IMAGE (\y:real^N. (M:real^N^N) ** y) U` THEN
  ABBREV_TAC `z0 = (M:real^N^N) ** y0` THEN
  SUBGOAL_THEN `(h:real^N->real^N) z0 = y0` (LABEL_TAC "HZ") THENL
   [MAP_EVERY EXPAND_TAC ["h"; "z0"] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `U':real^N->bool`; `h:real^N->real^N`;
                 `\y:real^N. (M:real^N^N) ** y`; `z0:real^N`] LRG_DIFFEO_DERIV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `F1 = \s. mpullback (h:real^N->real^N) ((G1:real->real^N->real^N^N) s)` THEN
  ABBREV_TAC `F2 = \s. mpullback (h:real^N->real^N) ((G2:real->real^N->real^N^N) s)` THEN
  SUBGOAL_THEN `lricci_flow U' a b (F1:real->real^N->real^N^N) /\
                lricci_flow U' a b (F2:real->real^N->real^N^N)` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["F1"; "F2"] THEN CONJ_TAC THEN
    MATCH_MP_TAC LRICCI_FLOW_PULLBACK THEN
    MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `\y:real^N. (M:real^N^N) ** y`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. a <= s /\ s < b
        ==> metric_field U' ((F1:real->real^N->real^N^N) s) /\
            metric_field U' ((F2:real->real^N->real^N^N) s)`
  (LABEL_TAC "MFF") THENL
   [X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    USE_THEN "MFG" (MP_TAC o SPEC `s:real`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    MAP_EVERY EXPAND_TAC ["F1"; "F2"] THEN CONJ_TAC THEN
    MATCH_MP_TAC METRIC_FIELD_PULLBACK THEN
    MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `\y:real^N. (M:real^N^N) ** y`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* quadratic forms at z0 *)
  SUBGOAL_THEN
   `!s v. (v:real^N) dot ((F1:real->real^N->real^N^N) s z0 ** v) =
          (frechet_derivative (h:real^N->real^N) (at z0) v) dot
          ((g1:real->A->real^N^N) s x ** frechet_derivative h (at z0) v) /\
          v dot ((F2:real->real^N->real^N^N) s z0 ** v) =
          (frechet_derivative h (at z0) v) dot
          ((g2:real->A->real^N^N) s x ** frechet_derivative h (at z0) v)`
  (LABEL_TAC "QF") THENL
   [REPEAT GEN_TAC THEN MAP_EVERY EXPAND_TAC ["F1"; "F2"] THEN
    MP_TAC(ISPECL [`h:real^N->real^N`; `(G1:real->real^N->real^N^N) s`; `z0:real^N`;
                   `v:real^N`] RFU_MPULLBACK_QFORM) THEN
    MP_TAC(ISPECL [`h:real^N->real^N`; `(G2:real->real^N->real^N^N) s`; `z0:real^N`;
                   `v:real^N`] RFU_MPULLBACK_QFORM) THEN
    ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!v. (v:real^N) dot v =
                    (frechet_derivative (h:real^N->real^N) (at z0) v) dot
                    ((g1:real->A->real^N^N) a x ** frechet_derivative h (at z0) v)`
  (LABEL_TAC "Q0") THENL
   [GEN_TAC THEN USE_THEN "QF" (fun th -> REWRITE_TAC[GSYM th]) THEN
    SUBGOAL_THEN `(F1:real->real^N->real^N^N) a z0 = mat 1` SUBST1_TAC THENL
     [EXPAND_TAC "F1" THEN ASM_REWRITE_TAC[]; REWRITE_TAC[MATRIX_VECTOR_MUL_LID]];
    ALL_TAC] THEN
  (* the density and the curvature norms in the normalised chart *)
  SUBGOAL_THEN
   `!s. metric_local atlas (c:(A->bool)#(A->real^N)) ((g1:real->A->real^N^N) s) = G1 s /\
        metric_local atlas c ((g2:real->A->real^N^N) s) = G2 s`
  (LABEL_TAC "GL") THENL
   [GEN_TAC THEN MAP_EVERY EXPAND_TAC ["G1"; "G2"] THEN REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. a <= s /\ s < b
        ==> pde_kot_density ((F1:real->real^N->real^N^N) s) (F2 s) z0 =
            pde_mkot_density atlas ((g1:real->A->real^N^N) s) (g2 s) x /\
            (!j. lrm_deriv_norm2 j ((F1:real->real^N->real^N^N) s) z0 =
                 rfa_rmd2 j atlas ((g1:real->A->real^N^N) s) x /\
                 lrm_deriv_norm2 j ((F2:real->real^N->real^N^N) s) z0 =
                 rfa_rmd2 j atlas ((g2:real->A->real^N^N) s) x)`
  (LABEL_TAC "TR") THENL
   [X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    USE_THEN "MFG" (MP_TAC o SPEC `s:real`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    REWRITE_TAC[pde_mkot_density; rfa_rmd2] THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY EXPAND_TAC ["F1"; "F2"] THEN
    USE_THEN "HZ" (fun th -> GEN_REWRITE_TAC DEPTH_CONV [SYM th]) THEN
    CONJ_TAC THENL [ALL_TAC; GEN_TAC THEN CONJ_TAC] THENL
     [MATCH_MP_TAC RFU_DENS_PULLBACK;
      MATCH_MP_TAC LRM_DERIV_NORM2_PULLBACK;
      MATCH_MP_TAC LRM_DERIV_NORM2_PULLBACK] THEN
    MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `U':real^N->bool`;
                          `\y:real^N. (M:real^N^N) ** y`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  USE_THEN "LB" (MP_TAC o SPECL
   [`U':real^N->bool`; `a:real`; `b:real`; `F1:real->real^N->real^N^N`;
    `F2:real->real^N->real^N^N`; `z0:real^N`; `b1:real`; `t:real`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `s:real` THEN DISCH_TAC THEN
      USE_THEN "MFF" (MP_TAC o SPEC `s:real`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
      USE_THEN "TR" (MP_TAC o SPEC `s:real`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
      USE_THEN "RB" (MP_TAC o SPEC `s:real`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
      ASM_REWRITE_TAC[] THEN X_GEN_TAC `v:real^N` THEN
      USE_THEN "QF" (fun th -> REWRITE_TAC[th]) THEN
      USE_THEN "Q0" (fun th -> REWRITE_TAC[th]) THEN
      USE_THEN "EQ" (MP_TAC o SPECL
        [`s:real`; `frechet_derivative (h:real^N->real^N) (at z0) v`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
      X_GEN_TAC `eps:real` THEN DISCH_TAC THEN
      MP_TAC(BETA_RULE(ISPECL
       [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b:real`;
        `\s. pde_mkot_density atlas ((g1:real->A->real^N^N) s) (g2 s)`; `x:A`;
        `eps:real`] RFU_SFUN_TIME_CONT)) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC RFU_MKOT_SFUN THEN
        EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "DC"))) THEN
      EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `r:real` THEN STRIP_TAC THEN
      USE_THEN "TR" (MP_TAC o SPEC `r:real`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN
      USE_THEN "DC" (MP_TAC o SPEC `r:real`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `pde_mkot_density atlas ((g1:real->A->real^N^N) a) (g2 a) x = &0`
      SUBST1_TAC THENL
       [MATCH_MP_TAC RFU_MKOT_SAME THEN EXISTS_TAC `top:A topology` THEN
        ASM_REWRITE_TAC[];
        REAL_ARITH_TAC]];
    USE_THEN "TR" (MP_TAC o SPEC `t:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN SIMP_TAC[]]);;

(* ========================================================================= *)
(* A14 at (:real^3), conditional on P2_THM_3_29_STATEMENT (:real^3):         *)
(* RFU_A14_COND.                                                             *)
(* For t0 < b put b2 = (t0 + b) / 2; the curvature bound on [a,b2] gives     *)
(* metric equivalence with g(a) (RFU_FLOW_EQUIV), Shi bounds for both flows  *)
(* (RFU_SHI_FLOW), the scalar curvature bound, the density bound            *)
(* (RFU_DENS_UNIFORM) and the transfer of |dphi|^2 and of the volume growth  *)
(* to g(s); then RFU_ENERGY_ZERO with b1 = t0 and PDE_KOT_DENSITY_ZERO.       *)
(* ========================================================================= *)

let RFU_RMD2_SAME = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (g1:A->real^N^N) g2 x l.
     smooth_manifold_atlas top atlas /\ x IN topspace top /\
     (!z. z IN topspace top ==> g1 z = g2 z)
     ==> lrm_deriv_norm2 l (metric_local atlas (chart_at atlas x) g1)
                         (SND(chart_at atlas x) x) =
         lrm_deriv_norm2 l (metric_local atlas (chart_at atlas x) g2)
                         (SND(chart_at atlas x) x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`]
                CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  SPEC_TAC(`chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)`,
           `c:(A->bool)#(A->real^N)`) THEN
  GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC LRM_DERIV_NORM2_LOCAL THEN
  EXISTS_TAC `IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)` THEN
  ASM_SIMP_TAC[FUN_IN_IMAGE] THEN X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
  REWRITE_TAC[metric_local] THEN
  SUBGOAL_THEN `chart_inv (c:(A->bool)#(A->real^N)) z IN topspace top` ASSUME_TAC THENL
   [MP_TAC(MATCH_MP OPEN_IN_SUBSET (ASSUME `open_in top (FST (c:(A->bool)#(A->real^N)))`)) THEN
    ASM SET_TAC[];
    ASM_SIMP_TAC[]]);;

let RFU_EI_FLIP = prove
 (`!E Ei qa qs. &0 < E /\ E * Ei = &1 /\ Ei * qa <= qs ==> qa <= E * qs`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `qa = E * (Ei * qa)` SUBST1_TAC THENL
   [REWRITE_TAC[REAL_MUL_ASSOC] THEN ASM_REWRITE_TAC[REAL_MUL_LID]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC);;

let RFU_VOL_ARITH = prove
 (`!e C r v v0. &0 <= e /\ &0 <= r /\ v <= e * v0 /\ v0 <= C * exp(C * r)
                ==> v <= (e * abs C + abs C) * exp((e * abs C + abs C) * r)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `e * abs C * exp(abs C * r)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `e * v0` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `C * exp(C * r)` THEN
    ASM_REWRITE_TAC[RFU_CV_EXP_ABS];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= e * abs C` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_ABS_POS]; ALL_TAC] THEN
  REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
  REWRITE_TAC[REAL_EXP_POS_LE; REAL_EXP_MONO_LE] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MP_TAC(SPEC `C:real` REAL_ABS_POS) THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

let RFU_A14_COND = prove
 (`P2_THM_3_29_STATEMENT (:real^3)
   ==> !top atlas a b g g' phi C.
       hausdorff_space (top:(real^3)topology) /\
       ricci_flow_from (top,atlas:((real^3->bool)#(real^3->real^3))->bool) a b g /\
       ricci_flow_from (top,atlas) a b g' /\
       (!x. x IN topspace top ==> g' a x = g a x) /\
       (!t. a <= t /\ t < b ==> mfd_complete (top,atlas) (g t) /\
                                mfd_complete (top,atlas) (g' t)) /\
       (!b1. b1 < b
             ==> ?K. !t x. a <= t /\ t <= b1 /\ x IN topspace top
                           ==> mfd_rm_norm atlas (g t) x <= K /\
                               mfd_rm_norm atlas (g' t) x <= K) /\
       (!l. ?Cl. !x. x IN topspace top
                     ==> lrm_deriv_norm2 l (metric_local atlas (chart_at atlas x) (g a))
                                         (SND(chart_at atlas x) x) <= Cl) /\
       mfd_smooth atlas (lift o phi) /\
       (!c. compact_in top {x | x IN topspace top /\ phi x <= c}) /\
       (!x. x IN topspace top
            ==> p2c_fgrad2 atlas (g a) phi x <= C /\ abs(p2c_flap atlas (g a) phi x) <= C) /\
       (!s v. mfd_has_volume (top,atlas) (g a) {x | x IN topspace top /\ phi x <= s} v
              ==> v <= C * exp(C * s))
       ==> !t x. a <= t /\ t < b /\ x IN topspace top ==> g' t x = g t x`,
  DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`t0:real`; `x0:real^3`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(LABEL_TAC "VOL" o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_has_volume")) (concl th))) THEN
  FIRST_X_ASSUM(LABEL_TAC "GR" o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p2c_fgrad2")) (concl th))) THEN
  FIRST_X_ASSUM(LABEL_TAC "CMP" o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "compact_in")) (concl th))) THEN
  FIRST_X_ASSUM(LABEL_TAC "IN" o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "lrm_deriv_norm2")) (concl th))) THEN
  FIRST_X_ASSUM(LABEL_TAC "RM" o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_rm_norm")) (concl th))) THEN
  FIRST_X_ASSUM(LABEL_TAC "CPL" o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_complete")) (concl th))) THEN
  MP_TAC(ISPECL [`top:(real^3)topology`; `atlas:((real^3->bool)#(real^3->real^3))->bool`;
                 `a:real`; `b:real`; `g:real->real^3->real^3^3`] GRGT_RF_METRIC) THEN
  MP_TAC(ISPECL [`top:(real^3)topology`; `atlas:((real^3->bool)#(real^3->real^3))->bool`;
                 `a:real`; `b:real`; `g':real->real^3->real^3^3`] GRGT_RF_METRIC) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "RG'")))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "RG")))) THEN
  ABBREV_TAC `b2 = (t0 + b) / &2` THEN
  SUBGOAL_THEN `t0 < b2 /\ b2 < b /\ a < b2` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "b2" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  (* the curvature bound on [a,b2] *)
  USE_THEN "RM" (MP_TAC o SPEC `b2:real`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `K0:real` (LABEL_TAC "K0")) THEN
  ABBREV_TAC `K = abs K0` THEN
  SUBGOAL_THEN `&0 <= K` ASSUME_TAC THENL [EXPAND_TAC "K" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!t x. a <= t /\ t < b2 /\ x IN topspace top
          ==> mfd_rm_norm atlas ((g:real->real^3->real^3^3) t) x <= K /\
              mfd_rm_norm atlas ((g':real->real^3->real^3^3) t) x <= K`
  (LABEL_TAC "KB") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    USE_THEN "K0" (MP_TAC o SPECL [`t:real`; `x:real^3`]) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
    EXPAND_TAC "K" THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* metric equivalence with g(a) on [a,b2) *)
  X_CHOOSE_THEN `Cf:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "FE"))
    (INST_TYPE [`:real^3`,`:A`; `:3`,`:N`] RFU_FLOW_EQUIV) THEN
  ABBREV_TAC `E = exp(&2 * (Cf * K) * (b2 - a))` THEN
  ABBREV_TAC `Ei = exp(--(&2 * (Cf * K) * (b2 - a)))` THEN
  SUBGOAL_THEN `&0 < E /\ &0 < Ei /\ E * Ei = &1 /\ &1 <= E` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["E"; "Ei"] THEN REWRITE_TAC[REAL_EXP_POS_LT; REAL_EXP_NEG_MUL] THEN
    ONCE_REWRITE_TAC[GSYM REAL_EXP_0] THEN REWRITE_TAC[REAL_EXP_MONO_LE] THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s x v. a <= s /\ s < b2 /\ x IN topspace top
            ==> Ei * (v dot ((g:real->real^3->real^3^3) a x ** v)) <= v dot (g s x ** v) /\
                v dot (g s x ** v) <= E * (v dot (g a x ** v)) /\
                Ei * (v dot (g a x ** v)) <= v dot ((g':real->real^3->real^3^3) s x ** v) /\
                v dot (g' s x ** v) <= E * (v dot (g a x ** v))`
  (LABEL_TAC "EQV") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    USE_THEN "FE" (MP_TAC o SPECL
     [`top:(real^3)topology`; `atlas:((real^3->bool)#(real^3->real^3))->bool`;
      `a:real`; `b:real`; `g:real->real^3->real^3^3`; `b2:real`; `K:real`]) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN REPEAT STRIP_TAC THEN
      USE_THEN "KB" (MP_TAC o SPECL [`t:real`; `x':real^3`]) THEN
      ASM_SIMP_TAC[];
      DISCH_THEN(MP_TAC o SPECL [`s:real`; `x:real^3`; `v:real^3`])] THEN
    USE_THEN "FE" (MP_TAC o SPECL
     [`top:(real^3)topology`; `atlas:((real^3->bool)#(real^3->real^3))->bool`;
      `a:real`; `b:real`; `g':real->real^3->real^3^3`; `b2:real`; `K:real`]) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN REPEAT STRIP_TAC THEN
      USE_THEN "KB" (MP_TAC o SPECL [`t:real`; `x':real^3`]) THEN
      ASM_SIMP_TAC[];
      DISCH_THEN(MP_TAC o SPECL [`s:real`; `x:real^3`; `v:real^3`])] THEN
    ASM_SIMP_TAC[] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* initial derivative bounds and Shi bounds for both flows *)
  SUBGOAL_THEN
   `?K1. !j x. j <= 2 /\ x IN topspace top
               ==> lrm_deriv_norm2 j
                     (metric_local atlas (chart_at atlas x) ((g:real->real^3->real^3^3) a))
                     (SND(chart_at atlas x) x) <= K1`
  (X_CHOOSE_THEN `K1:real` (LABEL_TAC "K1")) THENL
   [USE_THEN "IN" (fun th -> MP_TAC(SPEC `0` th) THEN MP_TAC(SPEC `1` th) THEN
                             MP_TAC(SPEC `2` th)) THEN
    DISCH_THEN(X_CHOOSE_TAC `c2:real`) THEN DISCH_THEN(X_CHOOSE_TAC `c1:real`) THEN
    DISCH_THEN(X_CHOOSE_TAC `c0:real`) THEN
    EXISTS_TAC `max c0 (max c1 c2)` THEN
    REWRITE_TAC[ARITH_RULE `j <= 2 <=> j = 0 \/ j = 1 \/ j = 2`] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
     [MATCH_MP_TAC(REAL_ARITH `y <= c0 ==> y <= max c0 (max c1 c2)`);
      MATCH_MP_TAC(REAL_ARITH `y <= c1 ==> y <= max c0 (max c1 c2)`);
      MATCH_MP_TAC(REAL_ARITH `y <= c2 ==> y <= max c0 (max c1 c2)`)] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_complete (top,atlas) ((g:real->real^3->real^3^3) a) /\
                mfd_complete (top,atlas) ((g':real->real^3->real^3^3) a)`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "CPL" (MP_TAC o SPEC `a:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t x. a <= t /\ t < b2 /\ x IN topspace top
          ==> mfd_rm_norm atlas ((g:real->real^3->real^3^3) t) x <= K`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN USE_THEN "KB" (MP_TAC o SPECL [`t:real`; `x:real^3`]) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t x. a <= t /\ t < b2 /\ x IN topspace top
          ==> mfd_rm_norm atlas ((g':real->real^3->real^3^3) t) x <= K`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN USE_THEN "KB" (MP_TAC o SPECL [`t:real`; `x:real^3`]) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!j x. j <= 2 /\ x IN topspace top
          ==> lrm_deriv_norm2 j
                (metric_local atlas (chart_at atlas x) ((g':real->real^3->real^3^3) a))
                (SND(chart_at atlas x) x) <= K1`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`top:(real^3)topology`; `atlas:((real^3->bool)#(real^3->real^3))->bool`;
                   `(g':real->real^3->real^3^3) a`; `(g:real->real^3->real^3^3) a`;
                   `x:real^3`; `j:num`] RFU_RMD2_SAME) THEN
    ASM_SIMP_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    USE_THEN "K1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:(real^3)topology`; `atlas:((real^3->bool)#(real^3->real^3))->bool`;
                 `a:real`; `b:real`; `g:real->real^3->real^3^3`; `b2:real`; `K:real`;
                 `K1:real`] RFU_SHI_FLOW) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_IMP_LE];
    DISCH_THEN(X_CHOOSE_THEN `B1:real` (LABEL_TAC "S1"))] THEN
  MP_TAC(ISPECL [`top:(real^3)topology`; `atlas:((real^3->bool)#(real^3->real^3))->bool`;
                 `a:real`; `b:real`; `g':real->real^3->real^3^3`; `b2:real`; `K:real`;
                 `K1:real`] RFU_SHI_FLOW) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_IMP_LE];
    DISCH_THEN(X_CHOOSE_THEN `B2:real` (LABEL_TAC "S2"))] THEN
  ABBREV_TAC `B = max B1 B2` THEN
  SUBGOAL_THEN
   `!j s x. j <= 2 /\ a <= s /\ s < b2 /\ x IN topspace top
            ==> rfa_rmd2 j atlas ((g:real->real^3->real^3^3) s) x <= B /\
                rfa_rmd2 j atlas ((g':real->real^3->real^3^3) s) x <= B`
  (LABEL_TAC "SB") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN EXPAND_TAC "B" THEN
    MATCH_MP_TAC(REAL_ARITH `x <= B1 /\ y <= B2 ==> x <= max B1 B2 /\ y <= max B1 B2`) THEN
    CONJ_TAC THENL
     [USE_THEN "S1" MATCH_MP_TAC; USE_THEN "S2" MATCH_MP_TAC] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the scalar curvature *)
  X_CHOOSE_THEN `Cs:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "SC"))
    (INST_TYPE [`:real^3`,`:A`; `:3`,`:N`] RFU_SCALAR_FROM_RMNORM) THEN
  (* the density *)
  MP_TAC(SPECL [`E:real`; `B:real`; `b2 - a`]
               (INST_TYPE [`:real^3`,`:A`; `:3`,`:N`] RFU_DENS_UNIFORM)) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `M:real` (LABEL_TAC "DU")) THEN
  (* the energy argument *)
  MP_TAC(ISPECL
   [`top:(real^3)topology`; `atlas:((real^3->bool)#(real^3->real^3))->bool`;
    `a:real`; `b:real`; `t0:real`; `g:real->real^3->real^3^3`;
    `g':real->real^3->real^3^3`; `phi:real^3->real`; `E * E:real`; `B:real`;
    `C / Ei`; `(E * sqrt E) * abs C + abs C`; `Cs * K:real`; `M:real`] RFU_ENERGY_ZERO) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_SIMP_TAC[];
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[];
      (* the pointwise bounds on [a,t0] *)
      X_GEN_TAC `s:real` THEN X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
      SUBGOAL_THEN `s < b2 /\ s < b` STRIP_ASSUME_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      USE_THEN "SB" (MP_TAC o SPECL [`0`; `s:real`; `x:real^3`]) THEN
      ANTS_TAC THENL [CONJ_TAC THENL [ARITH_TAC; ASM_REWRITE_TAC[]]; STRIP_TAC] THEN
      USE_THEN "SB" (MP_TAC o SPECL [`1`; `s:real`; `x:real^3`]) THEN
      ANTS_TAC THENL [CONJ_TAC THENL [ARITH_TAC; ASM_REWRITE_TAC[]]; STRIP_TAC] THEN
      USE_THEN "SB" (MP_TAC o SPECL [`2`; `s:real`; `x:real^3`]) THEN
      ANTS_TAC THENL [CONJ_TAC THENL [ARITH_TAC; ASM_REWRITE_TAC[]]; STRIP_TAC] THEN
      SUBGOAL_THEN `riemannian_metric atlas ((g:real->real^3->real^3^3) a) /\
                    riemannian_metric atlas ((g:real->real^3->real^3^3) s)`
      STRIP_ASSUME_TAC THENL
       [CONJ_TAC THEN USE_THEN "RG" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [(* mutual equivalence *)
        X_GEN_TAC `v:real^3` THEN
        USE_THEN "EQV" (MP_TAC o SPECL [`s:real`; `x:real^3`; `v:real^3`]) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
        MP_TAC(SPECL [`E:real`; `Ei:real`; `v dot ((g:real->real^3->real^3^3) a x ** v)`;
                      `v dot ((g:real->real^3->real^3^3) s x ** v)`] RFU_EI_FLIP) THEN
        MP_TAC(SPECL [`E:real`; `Ei:real`; `v dot ((g:real->real^3->real^3^3) a x ** v)`;
                      `v dot ((g':real->real^3->real^3^3) s x ** v)`] RFU_EI_FLIP) THEN
        ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
        CONJ_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `E * (v dot ((g:real->real^3->real^3^3) a x ** v))` THEN
        ASM_REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
        ASM_SIMP_TAC[REAL_LT_IMP_LE];
        (* the gradient of phi *)
        MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `rfu_mgrad2 atlas ((g:real->real^3->real^3^3) a) phi x / Ei` THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC RFU_MGRAD2_TRANSFER THEN EXISTS_TAC `top:(real^3)topology` THEN
          ASM_REWRITE_TAC[] THEN X_GEN_TAC `v:real^3` THEN
          USE_THEN "EQV" (MP_TAC o SPECL [`s:real`; `x:real^3`; `v:real^3`]) THEN
          ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
          ASM_SIMP_TAC[REAL_LE_DIV2_EQ] THEN REWRITE_TAC[GSYM RFU_P2C_FGRAD2] THEN
          USE_THEN "GR" (MP_TAC o SPEC `x:real^3`) THEN ASM_SIMP_TAC[]];
        (* the scalar curvature *)
        USE_THEN "SC" (MP_TAC o SPECL
         [`top:(real^3)topology`; `atlas:((real^3->bool)#(real^3->real^3))->bool`;
          `(g:real->real^3->real^3^3) s`; `x:real^3`; `K:real`]) THEN
        ANTS_TAC THENL
         [ASM_REWRITE_TAC[] THEN USE_THEN "KB" (MP_TAC o SPECL [`s:real`; `x:real^3`]) THEN
          ASM_SIMP_TAC[];
          REAL_ARITH_TAC];
        (* the density *)
        USE_THEN "DU" (MP_TAC o SPECL
         [`top:(real^3)topology`; `atlas:((real^3->bool)#(real^3->real^3))->bool`;
          `a:real`; `b:real`; `g:real->real^3->real^3^3`; `g':real->real^3->real^3^3`;
          `t0:real`; `x:real^3`; `s:real`]) THEN
        ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
        ASM_SIMP_TAC[] THEN REPEAT CONJ_TAC THENL
         [ASM_REAL_ARITH_TAC;
          MAP_EVERY X_GEN_TAC [`s':real`; `v:real^3`] THEN STRIP_TAC THEN
          USE_THEN "EQV" (MP_TAC o SPECL [`s':real`; `x:real^3`; `v:real^3`]) THEN
          ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
          ASM_REWRITE_TAC[] THEN CONJ_TAC THEN MATCH_MP_TAC RFU_EI_FLIP THEN
          EXISTS_TAC `Ei:real` THEN ASM_REWRITE_TAC[];
          X_GEN_TAC `s':real` THEN STRIP_TAC THEN
          USE_THEN "SB" (MP_TAC o SPECL [`0`; `s':real`; `x:real^3`]) THEN
          ANTS_TAC THENL
           [CONJ_TAC THENL [ARITH_TAC; ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
            STRIP_TAC] THEN
          USE_THEN "SB" (MP_TAC o SPECL [`1`; `s':real`; `x:real^3`]) THEN
          ANTS_TAC THENL
           [CONJ_TAC THENL [ARITH_TAC; ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
            STRIP_TAC] THEN
          ASM_REWRITE_TAC[]]];
      (* the volume growth for g(s) *)
      MAP_EVERY X_GEN_TAC [`s:real`; `r:real`; `v:real`] THEN STRIP_TAC THEN
      SUBGOAL_THEN `riemannian_metric atlas ((g:real->real^3->real^3^3) a) /\
                    riemannian_metric atlas ((g:real->real^3->real^3^3) s)`
      STRIP_ASSUME_TAC THENL
       [CONJ_TAC THEN USE_THEN "RG" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MP_TAC(ISPECL [`top:(real^3)topology`; `atlas:((real^3->bool)#(real^3->real^3))->bool`;
                     `(g:real->real^3->real^3^3) a`; `(g:real->real^3->real^3^3) s`;
                     `{x:real^3 | x IN topspace top /\ phi x <= r}`; `v:real`; `E:real`]
                    RFU_VOLUME_TRANSFER) THEN
      ANTS_TAC THENL
       [ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN REWRITE_TAC[IN_ELIM_THM] THEN
        MAP_EVERY X_GEN_TAC [`x:real^3`; `w:real^3`] THEN STRIP_TAC THEN
        USE_THEN "EQV" (MP_TAC o SPECL [`s:real`; `x:real^3`; `w:real^3`]) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]];
        ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `v0:real`
        (CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o REWRITE_RULE[REAL_MUL_ASSOC]))) THEN
      DISCH_TAC THEN MATCH_MP_TAC RFU_VOL_ARITH THEN EXISTS_TAC `v0:real` THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE; SQRT_POS_LE];
        USE_THEN "VOL" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`t0:real`; `x0:real^3`]) THEN
  ASM_REWRITE_TAC[REAL_LE_REFL] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`atlas:((real^3->bool)#(real^3->real^3))->bool`; `top:(real^3)topology`;
                 `(g:real->real^3->real^3^3) t0`; `(g':real->real^3->real^3^3) t0`;
                 `x0:real^3`] PDE_KOT_DENSITY_ZERO) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [USE_THEN "RG" MATCH_MP_TAC; USE_THEN "RG'" MATCH_MP_TAC] THEN
    ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[]]);;

