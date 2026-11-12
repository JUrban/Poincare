(* ========================================================================= *)
(* pc_p2a_par: the leaf L8 P2A_PARABOLIC via route O5 (MT Claims 8.5 and     *)
(* 8.8): on a parabolic region with |Rm| <= r^-2 the metrics at times s and  *)
(* tt are exp(4 (tt - s) / r^2)-comparable (Ricci bounded by twice the       *)
(* sectional curvature bound in dimension 3, RFA_UPTO_QFORM_EQUIV), and      *)
(* Shi's estimate (the statement P2A_REQ_SHI_SCALED_STATEMENT) at the time   *)
(* s, on a ball of radius r / (4 e) around y, bounds |grad R|^2 <= 9 |nabla  *)
(* Rm|^2.                                                                    *)
(*                                                                           *)
(* First: the Ricci form is bounded by (n - 1) times the sectional curvature *)
(* bound (the upper half: copies of CMPZ_TERM_LOWER, CMPZ_LRICCI_SEC_LOWER,  *)
(* CMPZ_MFD_RICCI_SEC_LOWER of pc_cmp_bg with the inequalities reversed).    *)
(* ========================================================================= *)

needs "src/pc_rfa_shiscale.ml";;
needs "src/pc_rfa_slmfd.ml";;
needs "src/pc_cmp_bg.ml";;
needs "src/pc_p2c_cdiff.ml";;
needs "src/pc_mfd_restrict.ml";;
needs "src/pc_smt_glue.ml";;
needs "src/pc_apx_local.ml";;
needs "src/pc_rfa_doubling.ml";;
needs "src/pc_rfa_shi.ml";;
needs "src/pc_lrg_tensor.ml";;
needs "src/pc_p2c_fview.ml";;
needs "src/pc_p2c_l112.ml";;
needs "src/pc_grg_dist.ml";;

prioritize_real();;
type_invention_error := true;;

let P2AP_TERM_UPPER = prove
 (`!(G:real^N->real^N^N) y kappa (f1:real^N) fi c w.
        (!u v. ~collinear {vec 0,u,v} ==> lsectional G y u v <= kappa) /\
        fi dot (G y ** fi) = &1 /\ fi dot (G y ** f1) = &0 /\
        f1 dot (G y ** f1) = &1 /\ &0 < c /\ f1 = inv c % w
        ==> fi dot (G y ** lriemann G y fi w w) <= kappa * (w dot (G y ** w))`,
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
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN REAL_ARITH_TAC);;

let P2AP_LRICCI_SEC_UPPER = prove
 (`!U (G:real^N->real^N^N) y kappa w.
        metric_field U G /\ y IN U /\
        (!u v. ~collinear {vec 0,u,v} ==> lsectional G y u v <= kappa)
        ==> lricci G y w w <= &(dimindex(:N) - 1) * kappa * (w dot (G y ** w))`,
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
        ==> (matrix_inv(M:real^N^N) ** basis i) dot
            ((G:real^N->real^N^N) y ** lriemann G y (matrix_inv M ** basis i) w w) <=
            kappa * (w dot (G y ** w))`
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
    MATCH_MP_TAC P2AP_TERM_UPPER THEN
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
   [MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN USE_THEN "terms" MATCH_MP_TAC THEN
    MAP_EVERY UNDISCH_TAC [`1 + 1 <= i`; `i <= dimindex(:N)`] THEN ARITH_TAC;
    REWRITE_TAC[SUM_CONST_NUMSEG] THEN
    SUBGOAL_THEN `(dimindex(:N) + 1) - (1 + 1) = dimindex(:N) - 1` SUBST1_TAC THENL
     [ARITH_TAC; REWRITE_TAC[REAL_LE_REFL]]]);;

let P2AP_MFD_RICCI_SEC_UPPER = prove
 (`!top atlas (g:A->real^N^N) y kappa w.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        y IN topspace top /\
        (!u v. ~collinear {vec 0,u,v} ==> mfd_sectional atlas g y u v <= kappa)
        ==> mfd_ricci atlas g y w w <= &(dimindex(:N) - 1) * kappa * (w dot (g y ** w))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `y:A`] CMPF_LOCAL_METRIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[mfd_ricci] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
    rand(concl th) = `(g:A->real^N^N) y`)) THEN
  MATCH_MP_TAC P2AP_LRICCI_SEC_UPPER THEN
  EXISTS_TAC `IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (y:A)))
                    (FST(chart_at atlas y))` THEN
  ASM_REWRITE_TAC[GSYM mfd_sectional]);;

let P2AP_MFD_RICCI_ABS = prove
 (`!top atlas (g:A->real^N^N) y w.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\ y IN topspace top
     ==> abs(mfd_ricci atlas g y w w) <=
         &(dimindex(:N) - 1) * mfd_rm_norm atlas g y * (w dot (g y ** w))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `y:A`; `--(mfd_rm_norm (atlas:((A->bool)#(A->real^N))->bool) g y)`;
                 `w:real^N`] CMPZ_MFD_RICCI_SEC_LOWER) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `y:A`; `mfd_rm_norm (atlas:((A->bool)#(A->real^N))->bool) g y`;
                 `w:real^N`] P2AP_MFD_RICCI_SEC_UPPER) THEN
  SUBGOAL_THEN
   `!u v. ~collinear {vec 0,u,v}
          ==> abs(mfd_sectional (atlas:((A->bool)#(A->real^N))->bool) g y u v) <=
              mfd_rm_norm atlas g y`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MFD_SECTIONAL_LE_RM_NORM THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`u:real^N`; `v:real^N`]) THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    DISCH_TAC] THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`u:real^N`; `v:real^N`]) THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    DISCH_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The region family p2c_vfam V W b (= p2a_rmetric V W b) of a region of a   *)
(* smooth view setting, read in the restricted atlas at b: its chart         *)
(* representation at s < b is the pullback of the slice metric, its          *)
(* curvature norm is at most that of the slice, and its |nabla^l Rm|^2 at    *)
(* any s in (a,b] is that of the slice.  Copies of P2CW_DIFFEO_DERIV_INJ,    *)
(* P2CW_VFAM_PULLBACK_LOCAL, P2CW_VFAM_RM_NORM_LE of pc_p2c_fl511 with       *)
(* p2c_regular_view replaced by p2a_svs and the region (that unit loads a    *)
(* large stack of Part 2C units).                                            *)
(* ------------------------------------------------------------------------- *)

let P2AP_SLICE = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t x.
     p2a_svs V /\ x IN topspace(rfs_vtop V t)
     ==> hausdorff_space (rfs_vtop V t) /\
         smooth_manifold_atlas (rfs_vtop V t) (rfs_vatlas V t) /\
         riemannian_metric (rfs_vatlas V t) (rfs_vmetric V t)`,
  REWRITE_TAC[p2a_svs; P2A_VIEW_PROJ_3] THEN MESON_TAC[MEMBER_NOT_EMPTY]);;

let P2AP_REGION_PERSISTS = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) W a b.
     p2a_region V W a b ==> rfs_persists V W a b`,
  SIMP_TAC[p2a_region; GSYM P2A_PERSISTS_3]);;

let P2AP_REGION_DIFFEO = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    W a b s.
     p2a_region V W a b /\ a < s /\ s <= b
     ==> mfd_diffeo (rfs_vtop V s) (rfs_vatlas V s) W (rfs_vtop V b) (rfs_vatlas V b) W
                    (\y:A. y) (\y. y)`,
  REWRITE_TAC[p2a_region; P2A_VIEW_PROJ_3] THEN MESON_TAC[]);;

let P2AP_RMETRIC_VFAM = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) W b.
     p2a_rmetric V W b = p2c_vfam V W b`,
  REWRITE_TAC[FUN_EQ_THM; p2a_rmetric; p2c_vfam; P2A_VIEW_PROJ_3]);;

let P2AP_DIFFEO_DERIV_INJ = prove
 (`!s t (h:real^N->real^N) h'.
     diffeomorphism_on s t h h'
     ==> !y. y IN s
             ==> linear(frechet_derivative h (at y)) /\
                 !u v. frechet_derivative h (at y) u = frechet_derivative h (at y) v
                       ==> u = v`,
  REPEAT GEN_TAC THEN REWRITE_TAC[diffeomorphism_on] THEN STRIP_TAC THEN
  X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(h:real^N->real^N) y IN t` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `((h:real^N->real^N) has_derivative frechet_derivative h (at y)) (at y) /\
                ((h':real^N->real^N) has_derivative frechet_derivative h' (at (h y)))
                  (at (h y))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`s:real^N->bool`; `h:real^N->real^N`] SMOOTH_MAP_ON_HAS_DERIVATIVE) THEN
      ASM_SIMP_TAC[];
      MP_TAC(ISPECL [`t:real^N->bool`; `h':real^N->real^N`] SMOOTH_MAP_ON_HAS_DERIVATIVE) THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `linear(frechet_derivative (h:real^N->real^N) (at y))` ASSUME_TAC THENL
   [ASM_MESON_TAC[has_derivative]; ASM_REWRITE_TAC[]] THEN
  SUBGOAL_THEN `frechet_derivative (h':real^N->real^N) (at (h y)) o
                frechet_derivative (h:real^N->real^N) (at y) = (\w. w)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC FRECHET_DERIVATIVE_UNIQUE_AT THEN
    EXISTS_TAC `(h':real^N->real^N) o (h:real^N->real^N)` THEN
    EXISTS_TAC `y:real^N` THEN CONJ_TAC THENL
     [MATCH_MP_TAC DIFF_CHAIN_AT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `open(s:real^N->bool)` THEN REWRITE_TAC[OPEN_CONTAINS_BALL] THEN
    DISCH_THEN(MP_TAC o SPEC `y:real^N`) THEN ASM_REWRITE_TAC[SUBSET; IN_BALL] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_AT THEN
    MAP_EVERY EXISTS_TAC [`\w:real^N. w`; `d:real`] THEN
    ASM_REWRITE_TAC[HAS_DERIVATIVE_ID; o_THM] THEN X_GEN_TAC `w:real^N` THEN
    DISCH_TAC THEN CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`u:real^N`; `v:real^N`] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(fun th -> MP_TAC(AP_THM th `u:real^N`) THEN MP_TAC(AP_THM th `v:real^N`)) THEN
  REWRITE_TAC[o_THM] THEN ASM_MESON_TAC[]);;

let P2AP_VFAM_PULLBACK_LOCAL = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    W a b s U (phi:A->real^3) z.
     p2a_svs V /\ p2a_region V W a b /\ a < s /\ s < b /\
     (U,phi) IN rfs_vatlas V b /\ z IN IMAGE phi (U INTER W)
     ==> metric_local (restrict_atlas (rfs_vatlas V b) W) (U INTER W,phi)
                      (p2c_vfam V W b s) z =
         rfs_pullback (rfs_vatlas V s) (chart_inv (U,phi)) (rfs_vmetric V s) z`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `y:A` (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC) o
                REWRITE_RULE[IN_IMAGE]) THEN
  SUBGOAL_THEN `rfs_persists (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) W a b` ASSUME_TAC THENL
   [MATCH_MP_TAC P2AP_REGION_PERSISTS THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [CONJUNCT2(CONJUNCT2(SPEC_ALL P2C_VIEW_EXPAND))] o
              check (fun th -> can (find_term (fun t -> is_const t &&
                fst(dest_const t) = "rfs_persists")) (concl th))) THEN
  DISCH_THEN(fun th -> MP_TAC(SPEC `s:real` th) THEN MP_TAC(SPEC `b:real` th)) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `(y:A) IN topspace(rfs_vtop (V:(real->A topology)#
                  (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) s)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `(y:A) IN U INTER W` THEN REWRITE_TAC[IN_INTER] THEN
    ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) s`;
                 `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) s`; `y:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `chart_at (rfs_vatlas (V:(real->A topology)#
                  (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) s) (y:A)`
         PAIR_SURJECTIVE) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`U':A->bool`; `psi:A->real^3`] THEN
  DISCH_THEN(LABEL_TAC "ch") THEN USE_THEN "ch" SUBST1_TAC THEN
  REWRITE_TAC[FST] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(s:real = b)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[p2c_vfam] THEN REWRITE_TAC[ETA_AX] THEN
  MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) b`;
                 `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) b`; `U:A->bool`; `phi:A->real^3`;
                 `W:A->bool`;
                 `mfd_pullback_metric (rfs_vatlas (V:(real->A topology)#
                    (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b)
                    (rfs_vatlas V s) (\y:A. y) (rfs_vmetric V s)`; `y:A`]
         METRIC_LOCAL_RESTRICT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) b`;
                 `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) b`; `W:A->bool`;
                 `rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) s`;
                 `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) s`; `W:A->bool`;
                 `\y:A. y`; `\y:A. y`;
                 `rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                 (real->A->real^3^3)) s`;
                 `U:A->bool`; `phi:A->real^3`; `U':A->bool`; `psi:A->real^3`; `y:A`]
         P2C_PULLBACK_METRIC_LOCAL_W) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC MFD_DIFFEO_SYM THEN MATCH_MP_TAC P2AP_REGION_DIFFEO THEN
      EXISTS_TAC `a:real` THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      UNDISCH_TAC `(y:A) IN U INTER W` THEN SET_TAC[]];
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[rfs_pullback] THEN
  MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) b`;
                 `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) b`; `U:A->bool`; `phi:A->real^3`;
                 `W:A->bool`; `y:A`] MFDR_CHART_INV_RESTRICT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  USE_THEN "ch" SUBST1_TAC THEN REWRITE_TAC[SND] THEN
  AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[o_DEF]);;

let P2AP_VFAM_RM_NORM_LE = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    W a b s x.
     p2a_svs V /\ p2a_region V W a b /\ a < s /\ s <= b /\ x IN W
     ==> mfd_rm_norm (restrict_atlas (rfs_vatlas V b) W) (p2c_vfam V W b s) x <=
         p3_vrm V s x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `rfs_persists (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) W a b` ASSUME_TAC THENL
   [MATCH_MP_TAC P2AP_REGION_PERSISTS THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [CONJUNCT2(CONJUNCT2(SPEC_ALL P2C_VIEW_EXPAND))] o
              check (fun th -> can (find_term (fun t -> is_const t &&
                fst(dest_const t) = "rfs_persists")) (concl th))) THEN
  DISCH_THEN(fun th -> MP_TAC(SPEC `s:real` th) THEN MP_TAC(SPEC `b:real` th)) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN
   `(x:A) IN topspace(rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                  (real->A->real^3^3)) s) /\
    x IN topspace(rfs_vtop V b)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `s:real`; `x:A`] P2AP_SLICE) THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `b:real`; `x:A`] P2AP_SLICE) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `s:real = b` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[p2c_vfam; ETA_AX; p3_vrm] THEN
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC MFD_RM_NORM_RESTRICT THEN
    EXISTS_TAC `rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                            (real->A->real^3^3)) b` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `s < b` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[p3_vrm] THEN MATCH_MP_TAC RFA_MFD_RM_NORM_LE THEN
  REWRITE_TAC[DIMINDEX_3; ARITH] THEN
  MAP_EVERY X_GEN_TAC [`u:real^3`; `v:real^3`] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) b`;
                 `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) b`; `W:A->bool`; `x:A`]
         MFDR_CHART_AT_RESTRICT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `U:A->bool` (X_CHOOSE_THEN `phi:A->real^3` STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[mfd_sectional; SND] THEN
  ABBREV_TAC `O = IMAGE (phi:A->real^3) (U INTER W)` THEN
  SUBGOAL_THEN `open(O:real^3->bool) /\ (phi:A->real^3) x IN O` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "O" THEN CONJ_TAC THENL
     [MATCH_MP_TAC MFDR_RESTRICT_IMAGE_OPEN THEN
      MAP_EVERY EXISTS_TAC
       [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                     (real->A->real^3^3)) b`;
        `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                       (real->A->real^3^3)) b`] THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_INTER]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_param (rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                          (real->A->real^3^3)) s) (rfs_vatlas V s) O
              (chart_inv (U:A->bool,phi:A->real^3))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_PARAM_EQ THEN EXISTS_TAC `(\y:A. y) o chart_inv (U:A->bool,phi:A->real^3)` THEN
    ASM_REWRITE_TAC[o_THM] THEN
    MATCH_MP_TAC MFD_PARAM_COMPOSE_DIFFEO THEN
    MAP_EVERY EXISTS_TAC
     [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                   (real->A->real^3^3)) b`;
      `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                     (real->A->real^3^3)) b`;
      `W:A->bool`; `W:A->bool`; `\y:A. y`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MFD_PARAM_RESTRICT THEN
      EXISTS_TAC `IMAGE (phi:A->real^3) U` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC MFD_PARAM_CHART_INV THEN ASM_REWRITE_TAC[];
        EXPAND_TAC "O" THEN MATCH_MP_TAC IMAGE_SUBSET THEN SET_TAC[]];
      MATCH_MP_TAC MFD_DIFFEO_SYM THEN MATCH_MP_TAC P2AP_REGION_DIFFEO THEN
      EXISTS_TAC `a:real` THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      EXPAND_TAC "O" THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
      X_GEN_TAC `y:A` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                  (real->A->real^3^3)) b`;
                     `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                    (real->A->real^3^3)) b`; `U:A->bool`; `phi:A->real^3`;
                     `W:A->bool`; `y:A`] MFDR_CHART_INV_RESTRICT) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `lsectional (metric_local (restrict_atlas (rfs_vatlas (V:(real->A topology)#
                 (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b) W)
                 (U INTER W,phi:A->real^3) (p2c_vfam V W b s)) (phi x) u v =
    lsectional (rfs_pullback (rfs_vatlas V s) (chart_inv (U,phi)) (rfs_vmetric V s))
               (phi x) u v`
  SUBST1_TAC THENL
   [MATCH_MP_TAC MFDR_LSECTIONAL_LOCAL THEN EXISTS_TAC `O:real^3->bool` THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    MATCH_MP_TAC P2AP_VFAM_PULLBACK_LOCAL THEN EXISTS_TAC `a:real` THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) s`;
                 `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) s`;
                 `rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                 (real->A->real^3^3)) s`;
                 `O:real^3->bool`; `chart_inv (U:A->bool,phi:A->real^3)`;
                 `(phi:A->real^3) x`; `u:real^3`; `v:real^3`]
         APX_PULLBACK_SECTIONAL_GEN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) b`;
                 `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) b`; `U:A->bool`; `phi:A->real^3`;
                 `W:A->bool`; `x:A`] MFDR_CHART_INV_RESTRICT) THEN
  ASM_REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MFD_SECTIONAL_LE_RM_NORM THEN
  EXISTS_TAC `rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                          (real->A->real^3^3)) s` THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) s`;
                 `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) s`; `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `chart_at (rfs_vatlas (V:(real->A topology)#
                  (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) s) (x:A)`
         PAIR_SURJECTIVE) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`U':A->bool`; `psi:A->real^3`] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[FST; SND] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) b`;
                 `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) b`; `W:A->bool`;
                 `rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) s`;
                 `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) s`; `W:A->bool`;
                 `\y:A. y`; `\y:A. y`; `U:A->bool`; `phi:A->real^3`; `U':A->bool`;
                 `psi:A->real^3`] MFDR_DIFFEO_CHART_REP) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MFD_DIFFEO_SYM THEN
    MATCH_MP_TAC P2AP_REGION_DIFFEO THEN EXISTS_TAC `a:real` THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `(phi:A->real^3) x` o MATCH_MP P2AP_DIFFEO_DERIV_INJ) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_ELIM_THM; IN_INTER];
    ALL_TAC] THEN
  SUBGOAL_THEN `(psi:A->real^3) o (\y:A. y) o chart_inv (U:A->bool,phi:A->real^3) =
                psi o chart_inv (U,phi)` SUBST1_TAC THENL
   [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`frechet_derivative ((psi:A->real^3) o chart_inv (U:A->bool,phi:A->real^3))
                                     (at (phi(x:A)))`; `{vec 0:real^3,u,v}`]
         COLLINEAR_LINEAR_IMAGE_EQ) THEN
  ASM_REWRITE_TAC[IMAGE_CLAUSES] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LINEAR_0 th]));;

(* ------------------------------------------------------------------------- *)
(* |nabla^l Rm|^2 of the region family at any time s in (a,b] is that of the *)
(* slice s (the derivative norm is invariant under pullback by the chart     *)
(* transition, LRM_DERIV_NORM2_PULLBACK, and local, LRM_DERIV_NORM2_LOCAL;   *)
(* at s = b as in P2CW_VFAM_DERIV_LAST).                                     *)
(* ------------------------------------------------------------------------- *)

(* The inverse of a chart of the atlas at b, on the part in W, is a         *)
(* parametrisation of the slice s.                                            *)

let P2AP_VFAM_PARAM = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    W a b s U (phi:A->real^3).
     p2a_region V W a b /\ a < s /\ s < b /\
     smooth_manifold_atlas (rfs_vtop V s) (rfs_vatlas V s) /\
     smooth_manifold_atlas (rfs_vtop V b) (rfs_vatlas V b) /\
     open_in (rfs_vtop V b) W /\ (U,phi) IN rfs_vatlas V b
     ==> mfd_param (rfs_vtop V s) (rfs_vatlas V s) (IMAGE phi (U INTER W))
                   (chart_inv (U,phi))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open (IMAGE (phi:A->real^3) (U INTER W))` ASSUME_TAC THENL
   [MATCH_MP_TAC MFDR_RESTRICT_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC
     [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                   (real->A->real^3^3)) b`;
      `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                     (real->A->real^3^3)) b`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MFD_PARAM_EQ THEN
  EXISTS_TAC `(\y:A. y) o chart_inv (U:A->bool,phi:A->real^3)` THEN
  ASM_REWRITE_TAC[o_THM] THEN
  MATCH_MP_TAC MFD_PARAM_COMPOSE_DIFFEO THEN
  MAP_EVERY EXISTS_TAC
   [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                 (real->A->real^3^3)) b`;
    `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                   (real->A->real^3^3)) b`;
    `W:A->bool`; `W:A->bool`; `\y:A. y`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MFD_PARAM_RESTRICT THEN
    EXISTS_TAC `IMAGE (phi:A->real^3) U` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC MFD_PARAM_CHART_INV THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC IMAGE_SUBSET THEN SET_TAC[]];
    MATCH_MP_TAC MFD_DIFFEO_SYM THEN MATCH_MP_TAC P2AP_REGION_DIFFEO THEN
    EXISTS_TAC `a:real` THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
    X_GEN_TAC `y:A` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) b`;
                   `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                  (real->A->real^3^3)) b`; `U:A->bool`; `phi:A->real^3`;
                   `W:A->bool`; `y:A`] MFDR_CHART_INV_RESTRICT) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]]);;

(* |nabla^l Rm|^2 of a pullback by a parametrisation (the pattern of        *)
(* APX_PULLBACK_SCALAR_GEN).                                                  *)

let P2AP_PULLBACK_RMD_GEN = prove
 (`!l top atlas (g:A->real^N^N) s (e:real^N->A) y.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        mfd_param top atlas s e /\ y IN s
        ==> lrm_deriv_norm2 l (rfs_pullback atlas e g) y = rfa_rmd2 l atlas g (e y)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `s:real^N->bool`; `e:real^N->A`; `y:real^N`]
                APX_PARAM_LOCAL_REP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:real^N->bool` (X_CHOOSE_THEN `N':real^N->bool`
    (X_CHOOSE_THEN `h':real^N->real^N` STRIP_ASSUME_TAC))) THEN
  TRANS_TAC EQ_TRANS
   `lrm_deriv_norm2 l (mpullback (SND(chart_at atlas ((e:real^N->A) y)) o e)
                       (metric_local atlas (chart_at atlas (e y)) (g:A->real^N^N))) y` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LRM_DERIV_NORM2_LOCAL THEN EXISTS_TAC `N:real^N->bool` THEN
    ASM_SIMP_TAC[];
    MP_TAC(ISPECL [`l:num`; `N':real^N->bool`; `N:real^N->bool`;
                   `SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) ((e:real^N->A) y)) o e`;
                   `h':real^N->real^N`;
                   `metric_local atlas (chart_at (atlas:((A->bool)#(A->real^N))->bool)
                                                 ((e:real^N->A) y)) (g:A->real^N^N)`;
                   `y:real^N`] LRM_DERIV_NORM2_PULLBACK) THEN
    ASM_REWRITE_TAC[o_THM; rfa_rmd2]]);;

(* The region family at s, read in the restricted atlas at b, has the       *)
(* derivative norms of the slice s.                                           *)

let P2AP_VFAM_DERIV = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    W a b s l x.
     p2a_svs V /\ p2a_region V W a b /\ a < s /\ s <= b /\ x IN W
     ==> lrm_deriv_norm2 l
           (metric_local (restrict_atlas (rfs_vatlas V b) W)
                         (chart_at (restrict_atlas (rfs_vatlas V b) W) x) (p2c_vfam V W b s))
           (SND(chart_at (restrict_atlas (rfs_vatlas V b) W) x) x) =
         p3_vderiv2 V l s x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `rfs_persists (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) W a b` ASSUME_TAC THENL
   [MATCH_MP_TAC P2AP_REGION_PERSISTS THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [CONJUNCT2(CONJUNCT2(SPEC_ALL P2C_VIEW_EXPAND))] o
              check (fun th -> can (find_term (fun t -> is_const t &&
                fst(dest_const t) = "rfs_persists")) (concl th))) THEN
  DISCH_THEN(fun th -> MP_TAC(SPEC `s:real` th) THEN MP_TAC(SPEC `b:real` th)) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN
   `(x:A) IN topspace(rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                  (real->A->real^3^3)) s) /\
    x IN topspace(rfs_vtop V b)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `s:real`; `x:A`] P2AP_SLICE) THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `b:real`; `x:A`] P2AP_SLICE) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) b`;
                 `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) b`; `W:A->bool`; `x:A`]
         MFDR_CHART_AT_RESTRICT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `U:A->bool` (X_CHOOSE_THEN `phi:A->real^3` STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[SND] THEN
  SUBGOAL_THEN `open (IMAGE (phi:A->real^3) (U INTER W)) /\ phi x IN IMAGE phi (U INTER W)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC MFDR_RESTRICT_IMAGE_OPEN THEN
      MAP_EVERY EXISTS_TAC
       [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                     (real->A->real^3^3)) b`;
        `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                       (real->A->real^3^3)) b`] THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_INTER]];
    ALL_TAC] THEN
  ASM_CASES_TAC `s:real = b` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    REWRITE_TAC[p2c_vfam; ETA_AX; p3_vderiv2] THEN
    MP_TAC(ISPECL [`l:num`;
                   `rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) b`;
                   `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                  (real->A->real^3^3)) b`;
                   `rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                   (real->A->real^3^3)) b`;
                   `(U:A->bool,phi:A->real^3)`; `x:A`] RFA_RMD2_CHART) THEN
    ASM_REWRITE_TAC[FST; SND; rfa_rmd2] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC LRM_DERIV_NORM2_LOCAL THEN
    EXISTS_TAC `IMAGE (phi:A->real^3) (U INTER W)` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `y:A` THEN DISCH_TAC THEN
    MATCH_MP_TAC METRIC_LOCAL_RESTRICT THEN
    EXISTS_TAC `rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                            (real->A->real^3^3)) b` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `s < b` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  TRANS_TAC EQ_TRANS
   `lrm_deriv_norm2 l (rfs_pullback (rfs_vatlas V s) (chart_inv (U:A->bool,phi:A->real^3))
                                    (rfs_vmetric (V:(real->A topology)#
                                       (real->((A->bool)#(A->real^3))->bool)#
                                       (real->A->real^3^3)) s))
                    ((phi:A->real^3) x)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LRM_DERIV_NORM2_LOCAL THEN
    EXISTS_TAC `IMAGE (phi:A->real^3) (U INTER W)` THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    MATCH_MP_TAC P2AP_VFAM_PULLBACK_LOCAL THEN EXISTS_TAC `a:real` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `W:A->bool`; `a:real`; `b:real`; `s:real`;
                 `U:A->bool`; `phi:A->real^3`] P2AP_VFAM_PARAM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`l:num`;
                 `rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) s`;
                 `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) s`;
                 `rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                 (real->A->real^3^3)) s`;
                 `IMAGE (phi:A->real^3) (U INTER W)`; `chart_inv (U:A->bool,phi:A->real^3)`;
                 `(phi:A->real^3) x`] P2AP_PULLBACK_RMD_GEN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) b`;
                 `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) b`; `U:A->bool`; `phi:A->real^3`;
                 `W:A->bool`; `x:A`] MFDR_CHART_INV_RESTRICT) THEN
  ASM_REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[rfa_rmd2; p3_vderiv2]);;

(* ------------------------------------------------------------------------- *)
(* MT Claim 8.8 (metric comparison).  The region family of a region with abs *)
(* Rm <= K is a Ricci flow whose Ricci form is bounded by 2 K g (dimension   *)
(* 3, P2AP_MFD_RICCI_ABS), so the metrics at s and b are exp(4 K (b -        *)
(* s))-comparable (RFA_UPTO_QFORM_EQUIV).  Also the trace bound abs(grad     *)
(* R)^2 <= 9 abs(nabla Rm)^2 on slices.                                      *)
(* ------------------------------------------------------------------------- *)

let P2AP_QFORM_NONNEG = prove
 (`!top atlas (g:A->real^N^N) x v.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\ x IN topspace top
     ==> &0 <= v dot (g x ** v)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `v:real^N = vec 0` THEN
  ASM_REWRITE_TAC[DOT_LZERO; REAL_LE_REFL] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`] RIEMANNIAN_METRIC_POS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `v:real^N` o CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let P2AP_EXP_NEG_LE = prove
 (`!x a b. exp(--x) * a <= b ==> a <= exp x * b`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `exp x * (exp(--x) * a)` THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_MUL_ASSOC; REAL_EXP_NEG_MUL; REAL_MUL_LID; REAL_LE_REFL];
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_EXP_POS_LE]]);;

(* The region family is an rfs_flow_upto on the region manifold; its       *)
(* metrics over (a,b] are Riemannian.                                        *)

let P2AP_REGION_UPTO = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    W a b.
     p2a_region V W a b
     ==> rfs_flow_upto (subtopology (rfs_vtop V b) W,restrict_atlas (rfs_vatlas V b) W)
                       a b (p2c_vfam V W b)`,
  REWRITE_TAC[p2a_region; P2A_VIEW_PROJ_3; P2AP_RMETRIC_VFAM; P2A_FLOW_UPTO_3] THEN
  SIMP_TAC[]);;

let P2AP_UPTO_RIEM = prove
 (`!top atlas a b (g:real->A->real^3^3) t.
     rfs_flow_upto (top,atlas) a b g /\ a < t /\ t <= b
     ==> smooth_manifold_atlas top atlas /\ riemannian_metric atlas (g t)`,
  REWRITE_TAC[rfs_flow_upto; ricci_flow_on] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN ASM_CASES_TAC `t:real = b` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC);;

(* MT Claim 8.8 for a region with abs Rm <= K.                              *)

let P2AP_METRIC_COMPARE = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    W a b K s y w.
     p2a_svs V /\ p2a_region V W a b /\ &0 <= K /\
     (!t z. a < t /\ t <= b /\ z IN W ==> p3_vrm V t z <= K) /\
     a < s /\ s <= b /\ y IN W
     ==> w dot (p2a_rmetric V W b s y ** w) <=
         exp(&4 * K * (b - s)) * (w dot (p2a_rmetric V W b b y ** w)) /\
         w dot (p2a_rmetric V W b b y ** w) <=
         exp(&4 * K * (b - s)) * (w dot (p2a_rmetric V W b s y ** w))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[P2AP_RMETRIC_VFAM] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP P2AP_REGION_UPTO) THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [rfs_flow_upto]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ext"))) THEN
  SUBGOAL_THEN
   `smooth_manifold_atlas (subtopology (rfs_vtop V b) W)
      (restrict_atlas (rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                    (real->A->real^3^3)) b) W)`
  ASSUME_TAC THENL [ASM_MESON_TAC[ricci_flow_on]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(y:A) IN topspace(subtopology (rfs_vtop (V:(real->A topology)#
                        (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b) W)`
  ASSUME_TAC THENL
   [REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER] THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                      (real->A->real^3^3)`; `W:A->bool`; `a:real`; `b:real`]
                  P2AP_REGION_PERSISTS) THEN
    ASM_REWRITE_TAC[CONJUNCT2(CONJUNCT2(SPEC_ALL P2C_VIEW_EXPAND))] THEN
    DISCH_THEN(MP_TAC o SPEC `b:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o MATCH_MP OPEN_IN_SUBSET o CONJUNCT2) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`subtopology (rfs_vtop (V:(real->A topology)#
                    (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b) W`;
                 `restrict_atlas (rfs_vatlas (V:(real->A topology)#
                    (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b) W`;
                 `a:real`; `b:real`;
                 `p2c_vfam (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) W b`;
                 `y:A`; `s:real`; `&2 * K`; `w:real^3`] RFA_UPTO_QFORM_EQUIV) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `riemannian_metric (restrict_atlas (rfs_vatlas (V:(real->A topology)#
                           (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b) W)
                        (p2c_vfam V W b t)`
    ASSUME_TAC THENL
     [MP_TAC(ISPECL [`subtopology (rfs_vtop (V:(real->A topology)#
                        (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b) W`;
                     `restrict_atlas (rfs_vatlas (V:(real->A topology)#
                        (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b) W`;
                     `a:real`; `b:real`;
                     `p2c_vfam (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                  (real->A->real^3^3)) W b`; `t:real`] P2AP_UPTO_RIEM) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`subtopology (rfs_vtop (V:(real->A topology)#
                      (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b) W`;
                   `restrict_atlas (rfs_vatlas (V:(real->A topology)#
                      (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b) W`;
                   `p2c_vfam (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) W b t`; `y:A`; `w:real^3`]
                  P2AP_MFD_RICCI_ABS) THEN
    ASM_REWRITE_TAC[DIMINDEX_3] THEN CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                      (real->A->real^3^3)`; `W:A->bool`; `a:real`; `b:real`; `t:real`; `y:A`]
                  P2AP_VFAM_RM_NORM_LE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`t:real`; `y:A`] o
      check (fun th -> can (find_term (fun t -> is_const t && fst(dest_const t) = "p3_vrm"))
                           (concl th) && is_forall (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
    MP_TAC(ISPECL [`subtopology (rfs_vtop (V:(real->A topology)#
                      (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b) W`;
                   `restrict_atlas (rfs_vatlas (V:(real->A topology)#
                      (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b) W`;
                   `p2c_vfam (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) W b t`; `y:A`; `w:real^3`]
                  P2AP_QFORM_NONNEG) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    ABBREV_TAC `q = w dot (p2c_vfam (V:(real->A topology)#
                     (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) W b t y ** w)` THEN
    ABBREV_TAC `m = mfd_rm_norm (restrict_atlas (rfs_vatlas (V:(real->A topology)#
                     (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b) W)
                     (p2c_vfam V W b t) y` THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&2 * m * q` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&0 <= (K - m) * q` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH `&2 * (&2 * K) * d = &4 * K * d`] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P2AP_EXP_NEG_LE THEN
  ASM_REWRITE_TAC[]);;

(* abs(grad R)^2 <= n^2 abs(nabla Rm)^2 at the chart level and on slices.   *)

let P2AP_GRADR_DERIV = prove
 (`!s (G:real^N->real^N^N) y.
     metric_field s G /\ y IN s
     ==> lgrad2 G (lscalar G) y <= &(dimindex(:N)) pow 2 * lrm_deriv_norm2 1 G y`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `lrm_deriv_norm2 1 (G:real^N->real^N^N) y = ltnorm2 5 G (lnabla 4 G (lrm4 G)) y`
  SUBST1_TAC THENL
   [REWRITE_TAC[lrm_deriv_norm2; ARITH_RULE `4 + 1 = 5`] THEN
    REWRITE_TAC[ONE; lnabla_iter; ADD_CLAUSES];
    MP_TAC(ISPECL [`s:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`]
                  P2C_SCALAR_DERIV_TRACE) THEN
    ASM_SIMP_TAC[]]);;

let P2AP_VGRADR_DERIV = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t y.
     p2a_svs V /\ y IN topspace(rfs_vtop V t)
     ==> p2a_vgradR2 V t y <= &9 * p3_vderiv2 V 1 t y`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `t:real`; `y:A`] P2AP_SLICE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) t`;
                 `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) t`; `y:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[p2a_vgradR2; p3_vderiv2; P2A_VIEW_PROJ_3] THEN
  SUBGOAL_THEN `&9 = &(dimindex(:3)) pow 2` SUBST1_TAC THENL
   [REWRITE_TAC[DIMINDEX_3] THEN CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
  MATCH_MP_TAC P2AP_GRADR_DERIV THEN
  EXISTS_TAC `IMAGE (SND(chart_at (rfs_vatlas (V:(real->A topology)#
                (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t) (y:A)))
                    (FST(chart_at (rfs_vatlas V t) y))` THEN
  CONJ_TAC THENL
   [UNDISCH_TAC `riemannian_metric (rfs_vatlas (V:(real->A topology)#
                   (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t)
                   (rfs_vmetric V t)` THEN
    REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Balls of an open submanifold (subtopology top W, restrict_atlas atlas W)  *)
(* with the restricted metric lie in the balls of the manifold (copies of    *)
(* P2CW_C1_CURVE_RESTRICT, P2CW_LENGTH_RESTRICT, P2CW_RESTRICT_BALL of       *)
(* pc_p2c_fl511 and P2CU_BALL_SHIFT of pc_p2c_cgunif; those units load the   *)
(* Cheeger-Gromov and normal-coordinate stacks, about 48K further lines).    *)
(* The closure in the region manifold of a ball for a metric                 *)
(* lam^2-comparable to the restricted metric is compact.                     *)
(* ------------------------------------------------------------------------- *)

let P2AP_C1_CURVE_RESTRICT = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) W (gamma:real->A) a b.
     mfd_c1_curve (subtopology top W,restrict_atlas atlas W) gamma a b
     ==> mfd_c1_curve (top,atlas) gamma a b /\
         (!t. t IN real_interval[a,b] ==> gamma t IN W)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mfd_c1_curve; CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `!t. t IN real_interval[a,b] ==> (gamma:real->A) t IN W` ASSUME_TAC THENL
   [UNDISCH_TAC `IMAGE (gamma:real->A)
                   (topspace (subtopology euclideanreal (real_interval[a,b]))) SUBSET W` THEN
    REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; TOPSPACE_EUCLIDEANREAL; INTER_UNIV] THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN MAP_EVERY X_GEN_TAC [`U:A->bool`; `phi:A->real^N`] THEN
  DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(U INTER W:A->bool,phi:A->real^N)`) THEN
  REWRITE_TAC[IN_RESTRICT_ATLAS] THEN ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC EQ_IMP THEN REWRITE_TAC[FST; SND] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INTER] THEN X_GEN_TAC `s:real^1` THEN
  ASM_CASES_TAC `(s:real^1) IN interval[lift a,lift b]` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(gamma:real->A) (drop s) IN W` (fun th -> REWRITE_TAC[th]) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  UNDISCH_TAC `(s:real^1) IN interval[lift a,lift b]` THEN
  REWRITE_TAC[IN_INTERVAL_1; IN_REAL_INTERVAL; LIFT_DROP]);;

let P2AP_LENGTH_RESTRICT = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) W (g:A->real^N^N) (gamma:real->A) a b.
     smooth_manifold_atlas top atlas /\ open_in top W /\ a < b /\
     mfd_c1_curve (subtopology top W,restrict_atlas atlas W) gamma a b
     ==> mfd_length (restrict_atlas atlas W) (restrict_metric atlas W g) gamma a b =
         mfd_length atlas g gamma a b`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2AP_C1_CURVE_RESTRICT) THEN
  REWRITE_TAC[mfd_length] THEN MATCH_MP_TAC REAL_INTEGRAL_EQ THEN
  X_GEN_TAC `t:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(gamma:real->A) t IN topspace top /\ gamma t IN W` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MFD_C1_CURVE_IN_TOPSPACE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(gamma:real->A) t`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `chart_at (atlas:((A->bool)#(A->real^N))->bool) ((gamma:real->A) t)`
         PAIR_SURJECTIVE) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`U:A->bool`; `phi:A->real^N`] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[FST] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(U INTER W:A->bool,phi:A->real^N) IN restrict_atlas atlas W` ASSUME_TAC THENL
   [REWRITE_TAC[IN_RESTRICT_ATLAS] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`subtopology top (W:A->bool)`;
                 `restrict_atlas (atlas:((A->bool)#(A->real^N))->bool) W`;
                 `restrict_metric (atlas:((A->bool)#(A->real^N))->bool) W g`;
                 `gamma:real->A`; `a:real`; `b:real`; `t:real`;
                 `U INTER W:A->bool`; `phi:A->real^N`] MFD_SPEED_CHART) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[SMOOTH_MANIFOLD_ATLAS_RESTRICT; IN_INTER]; DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `a:real`; `b:real`; `t:real`;
                 `U:A->bool`; `phi:A->real^N`] MFD_SPEED_CHART) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC METRIC_LOCAL_RESTRICT THEN EXISTS_TAC `top:A topology` THEN
  ASM_REWRITE_TAC[IN_INTER]);;

let P2AP_RESTRICT_BALL = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) W (g:A->real^N^N) x r.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\ open_in top W
     ==> mfd_ball (subtopology top W,restrict_atlas atlas W) (restrict_metric atlas W g) x r
         SUBSET mfd_ball (top,atlas) g x r`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SUBSET] THEN X_GEN_TAC `y:A` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `W:A->bool`;
                 `g:A->real^N^N`] RIEMANNIAN_METRIC_RESTRICT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`subtopology top (W:A->bool)`;
                 `restrict_atlas (atlas:((A->bool)#(A->real^N))->bool) W`;
                 `restrict_metric (atlas:((A->bool)#(A->real^N))->bool) W g`;
                 `x:A`; `y:A`; `r:real`] P2C_BALL_CURVE) THEN
  ASM_SIMP_TAC[SMOOTH_MANIFOLD_ATLAS_RESTRICT] THEN
  DISCH_THEN(X_CHOOSE_THEN `gamma:real->A` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2AP_C1_CURVE_RESTRICT) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `W:A->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `&0`; `&1`] P2AP_LENGTH_RESTRICT) THEN
  ASM_REWRITE_TAC[REAL_LT_01] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `&0`; `&1`] MFD_DIST_LE_LENGTH) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN CONJ_TAC THENL
   [REWRITE_TAC[mfd_joinable] THEN EXISTS_TAC `gamma:real->A` THEN ASM_REWRITE_TAC[];
    ASM_REAL_ARITH_TAC]);;

let P2AP_BALL_SHIFT = prove
 (`!top atlas (g:A->real^N^N) x y A r.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     y IN mfd_ball (top,atlas) g x A
     ==> mfd_ball (top,atlas) g y r SUBSET mfd_ball (top,atlas) g x (A + r)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mfd_ball; SUBSET; IN_ELIM_THM] THEN STRIP_TAC THEN
  X_GEN_TAC `z:A` THEN STRIP_TAC THEN CONJ_TAC THENL
   [ASM_MESON_TAC[MFD_JOINABLE_TRANS];
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x:A`; `y:A`; `z:A`] MFD_DIST_TRIANGLE) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;
let P2AP_BALL_SUBSET = prove
 (`!top atlas (g:A->real^N^N) x r. mfd_ball (top,atlas) g x r SUBSET topspace top`,
  REWRITE_TAC[mfd_ball; SUBSET; IN_ELIM_THM] THEN MESON_TAC[MFD_JOINABLE_IN_TOPSPACE]);;

(* The ball B(y,rho) of the region manifold W = B(x,r), for a metric gs   *)
(* with restrict_metric g <= lam^2 gs on W, has compact closure in W when  *)
(* y is in B(x,r/2), lam rho <= r/4 and B(x,r) has compact closure.        *)

let P2AP_BALL_COMPACT = prove
 (`!top atlas (g:A->real^N^N) x r gs y rho lam.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     &0 < r /\ compact_in top (top closure_of mfd_ball (top,atlas) g x r) /\
     riemannian_metric (restrict_atlas atlas (mfd_ball (top,atlas) g x r)) gs /\
     y IN mfd_ball (top,atlas) g x (r / &2) /\ &0 < rho /\ &0 < lam /\ lam * rho <= r / &4 /\
     (!z v. z IN mfd_ball (top,atlas) g x r
            ==> v dot (restrict_metric atlas (mfd_ball (top,atlas) g x r) g z ** v) <=
                lam pow 2 * (v dot (gs z ** v)))
     ==> compact_in (subtopology top (mfd_ball (top,atlas) g x r))
           (subtopology top (mfd_ball (top,atlas) g x r) closure_of
            mfd_ball (subtopology top (mfd_ball (top,atlas) g x r),
                      restrict_atlas atlas (mfd_ball (top,atlas) g x r)) gs y rho)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `open_in top (mfd_ball (top,atlas) (g:A->real^N^N) x r)` ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_BALL_OPEN THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(y:A) IN mfd_ball (top,atlas) (g:A->real^N^N) x r` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                   `x:A`; `r / &2`; `r:real`] RFA_MFD_BALL_MONO) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM SET_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `W = mfd_ball (top,atlas) (g:A->real^N^N) x r` THEN
  ABBREV_TAC `S = mfd_ball (subtopology top W,
                            restrict_atlas (atlas:((A->bool)#(A->real^N))->bool) W)
                           (gs:A->real^N^N) y rho` THEN
  SUBGOAL_THEN `topspace(subtopology top (W:A->bool)) = W` ASSUME_TAC THENL
   [REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN
    MP_TAC(ISPECL [`top:A topology`; `W:A->bool`] OPEN_IN_SUBSET) THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_manifold_atlas (subtopology top W)
                          (restrict_atlas (atlas:((A->bool)#(A->real^N))->bool) W) /\
    riemannian_metric (restrict_atlas atlas W) (restrict_metric atlas W (g:A->real^N^N)) /\
    hausdorff_space (subtopology top (W:A->bool))`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SMOOTH_MANIFOLD_ATLAS_RESTRICT; HAUSDORFF_SPACE_SUBTOPOLOGY] THEN
    MATCH_MP_TAC RIEMANNIAN_METRIC_RESTRICT THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`subtopology top (W:A->bool)`;
                 `restrict_atlas (atlas:((A->bool)#(A->real^N))->bool) W`;
                 `gs:A->real^N^N`; `restrict_metric (atlas:((A->bool)#(A->real^N))->bool) W g`;
                 `W:A->bool`; `y:A`; `&2 * lam * rho`; `lam:real`] RFA_BALL_INCLUSION) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[OPEN_IN_SUBTOPOLOGY_REFL] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[OPEN_IN_SUBSET];
      ASM_MESON_TAC[MFD_JOINABLE_IN_TOPSPACE]];
    DISCH_THEN(LABEL_TAC "INC")] THEN
  SUBGOAL_THEN `(&2 * lam * rho) / lam = &2 * rho` ASSUME_TAC THENL
   [UNDISCH_TAC `&0 < lam` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  SUBGOAL_THEN
   `(S:A->bool) SUBSET
    mfd_ball (subtopology top W,restrict_atlas (atlas:((A->bool)#(A->real^N))->bool) W)
             (restrict_metric atlas W (g:A->real^N^N)) y (lam * rho)`
  ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN REWRITE_TAC[SUBSET; mfd_ball; IN_ELIM_THM] THEN
    X_GEN_TAC `z:A` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "INC" (MP_TAC o SPEC `z:A`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `lam * mfd_dist (subtopology top W,restrict_atlas
                  (atlas:((A->bool)#(A->real^N))->bool) W) (gs:A->real^N^N) y z` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(S:A->bool) SUBSET mfd_ball (top,atlas) (g:A->real^N^N) x (&3 * r / &4)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `mfd_ball (subtopology top W,restrict_atlas
                  (atlas:((A->bool)#(A->real^N))->bool) W)
                  (restrict_metric atlas W (g:A->real^N^N)) y (lam * rho)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `mfd_ball (top,atlas) (g:A->real^N^N) y (lam * rho)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC P2AP_RESTRICT_BALL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `mfd_ball (top,atlas) (g:A->real^N^N) x (r / &2 + lam * rho)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC P2AP_BALL_SHIFT THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC RFA_MFD_BALL_MONO THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `top closure_of (S:A->bool) SUBSET W` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `mfd_cball (top,atlas) (g:A->real^N^N) x (&3 * r / &4)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC CLOSURE_OF_MINIMAL THEN ASM_SIMP_TAC[MFD_CBALL_CLOSED] THEN
      MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `mfd_ball (top,atlas) (g:A->real^N^N) x (&3 * r / &4)` THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[mfd_ball; mfd_cball; SUBSET; IN_ELIM_THM] THEN
      MESON_TAC[REAL_LT_IMP_LE];
      SUBGOAL_THEN `mfd_cball (top,atlas) (g:A->real^N^N) x (&3 * r / &4) SUBSET
                    mfd_ball (top,atlas) g x r` MP_TAC THENL
       [REWRITE_TAC[mfd_ball; mfd_cball; SUBSET; IN_ELIM_THM] THEN
        GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
        ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(S:A->bool) SUBSET W` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`subtopology top (W:A->bool)`;
                   `restrict_atlas (atlas:((A->bool)#(A->real^N))->bool) W`;
                   `gs:A->real^N^N`; `y:A`; `rho:real`] P2AP_BALL_SUBSET) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `compact_in top (top closure_of (S:A->bool))` ASSUME_TAC THENL
   [MATCH_MP_TAC CLOSED_COMPACT_IN THEN EXISTS_TAC `top closure_of (W:A->bool)` THEN
    ASM_REWRITE_TAC[CLOSED_IN_CLOSURE_OF] THEN MATCH_MP_TAC CLOSURE_OF_MONO THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[CLOSURE_OF_SUBTOPOLOGY; COMPACT_IN_SUBTOPOLOGY] THEN
  SUBGOAL_THEN `(W:A->bool) INTER S = S` SUBST1_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(W:A->bool) INTER (top closure_of S) = top closure_of S` SUBST1_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* MT Claim 8.5 (the gradient bound) and the headline.  At (s,y) with s >=   *)
(* tt - r^2 / 2 and y in B(x,tt,r/2), Shi's estimate (the statement          *)
(* P2A_REQ_SHI_SCALED_STATEMENT) is applied to the region family over (s -   *)
(* rho^2, s] with rho = r / (4 e): the time-s ball B(y,rho) of the region    *)
(* manifold lies in the time-tt ball B(y,e rho) = B(y,r/4) (metrics          *)
(* e^2-comparable, P2AP_METRIC_COMPARE), so its closure is compact in the    *)
(* region (P2AP_BALL_COMPACT); then abs(grad R)^2 <= 9 abs(nabla Rm)^2 <= 9  *)
(* C (4 e)^6 / r^6, and C1 = 3 sqrt C (4 e)^3.                               *)
(* ------------------------------------------------------------------------- *)

(* The constants: rho = r / (4 e) with e = exp 1 >= 2.                      *)

let P2AP_RHO_FACTS = prove
 (`!r e rho.
     &0 < r /\ &2 <= e /\ rho = r / (&4 * e)
     ==> &0 < rho /\ rho * (&4 * e) = r /\ e * rho = r / &4 /\ rho <= r /\
         rho pow 2 <= r pow 2 / &2 /\ &0 < rho pow 2 /\ rho pow 2 <= r pow 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < rho /\ rho * (&4 * e) = r` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_DIV_RMUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&8 * rho <= (&4 * e) * rho` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&8 * rho <= r` ASSUME_TAC THENL
   [UNDISCH_TAC `rho * (&4 * e) = r` THEN UNDISCH_TAC `&8 * rho <= (&4 * e) * rho` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `rho pow 2 <= (r / &8) pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(r / &8) pow 2 = r pow 2 / &64` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_POW_DIV] THEN CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
  MP_TAC(SPEC `r:real` REAL_LE_POW_2) THEN
  SUBGOAL_THEN `&0 < rho pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `rho * (&4 * e) = r` THEN
  REPEAT(POP_ASSUM MP_TAC) THEN REAL_ARITH_TAC);;

(* Shi's estimate in the region at (s,y).                                    *)

let P2AP_GRAD_AT = prove
 (`!C. (!top atlas a b (g:real->A->real^3^3) x r.
          hausdorff_space top /\
          rfs_flow_upto (top,atlas:((A->bool)#(A->real^3))->bool) a b g /\
          &0 < r /\ r pow 2 <= b - a /\ x IN topspace top /\
          compact_in top (top closure_of mfd_ball (top,atlas) (g b) x r) /\
          (!t y. a < t /\ t <= b /\ y IN mfd_ball (top,atlas) (g b) x r
                 ==> mfd_rm_norm atlas (g t) y <= inv(r pow 2))
          ==> !y. y IN mfd_ball (top,atlas) (g b) x (r / &2)
                  ==> lrm_deriv_norm2 1 (metric_local atlas (chart_at atlas y) (g b))
                                        (SND(chart_at atlas y) y) <= C * inv(r pow 6))
       ==> !(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
            tt x r s y.
             p2a_svs V /\ &0 < r /\ x IN topspace(rfs_vtop V tt) /\
             p2a_region V (rfs_vball V tt x r) (tt - r pow 2) tt /\
             compact_in (rfs_vtop V tt) ((rfs_vtop V tt) closure_of (rfs_vball V tt x r)) /\
             (!s y. tt - r pow 2 < s /\ s <= tt /\ y IN rfs_vball V tt x r
                    ==> p3_vrm V s y <= inv(r pow 2)) /\
             tt - r pow 2 / &2 <= s /\ s <= tt /\ y IN rfs_vball V tt x (r / &2)
             ==> p2a_vgradR2 V s y <= &9 * C * (&4 * exp(&1)) pow 6 * inv(r pow 6)`,
  GEN_TAC THEN DISCH_THEN(LABEL_TAC "SHI") THEN
  MAP_EVERY X_GEN_TAC
   [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
    `tt:real`; `x:A`; `r:real`; `s:real`; `y:A`] THEN
  REWRITE_TAC[CONJUNCT1(CONJUNCT2(SPEC_ALL P2C_VIEW_EXPAND))] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `tt:real`; `x:A`] P2AP_SLICE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `e = exp(&1)` THEN
  SUBGOAL_THEN `&2 <= e` ASSUME_TAC THENL
   [EXPAND_TAC "e" THEN MP_TAC(SPEC `&1` REAL_EXP_LE_X) THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `rho = r / (&4 * e)` THEN
  MP_TAC(SPECL [`r:real`; `e:real`; `rho:real`] P2AP_RHO_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `W = mfd_ball (rfs_vtop V tt,rfs_vatlas V tt)
                           (rfs_vmetric (V:(real->A topology)#
                              (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt)
                           x r` THEN
  SUBGOAL_THEN
   `open_in (rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                         (real->A->real^3^3)) tt) W /\
    W SUBSET topspace(rfs_vtop V tt) /\ (y:A) IN W`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN
     `open_in (rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                           (real->A->real^3^3)) tt) W`
    ASSUME_TAC THENL
     [EXPAND_TAC "W" THEN MATCH_MP_TAC MFD_BALL_OPEN THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[OPEN_IN_SUBSET] THEN
    MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) tt`;
                   `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                  (real->A->real^3^3)) tt`;
                   `rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                   (real->A->real^3^3)) tt`;
                   `x:A`; `r / &2`; `r:real`] RFA_MFD_BALL_MONO) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:A) IN topspace(rfs_vtop (V:(real->A topology)#
                  (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt)`
  ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  (* the region flow and its restrictions *)
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `W:A->bool`; `tt - r pow 2`; `tt:real`]
                P2AP_REGION_UPTO) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `rfs_flow_upto (subtopology (rfs_vtop V tt) W,
                   restrict_atlas (rfs_vatlas (V:(real->A topology)#
                     (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt) W)
                  (s - rho pow 2) s (p2c_vfam V W tt)`
  ASSUME_TAC THENL
   [ASM_CASES_TAC `s:real = tt` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN MATCH_MP_TAC P2CF_RFU_LEFT THEN
      EXISTS_TAC `tt - r pow 2` THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC P2CF_RFO_UPTO THEN
      MAP_EVERY EXISTS_TAC [`tt - r pow 2`; `tt:real`] THEN
      CONJ_TAC THENL [ASM_MESON_TAC[rfs_flow_upto]; ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`subtopology (rfs_vtop (V:(real->A topology)#
                    (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt) W`;
                 `restrict_atlas (rfs_vatlas (V:(real->A topology)#
                    (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt) W`;
                 `tt - r pow 2`; `tt:real`;
                 `p2c_vfam (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) W tt`; `s:real`] P2AP_UPTO_RIEM) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN
   `topspace(subtopology (rfs_vtop (V:(real->A topology)#
      (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt) W) = W`
  ASSUME_TAC THENL [REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN ASM SET_TAC[]; ALL_TAC] THEN
  (* the metrics at tt and s are e^2-comparable on W *)
  SUBGOAL_THEN
   `!z v. z IN W
          ==> v dot (restrict_metric (rfs_vatlas V tt) W (rfs_vmetric V tt) z ** v) <=
              e pow 2 * (v dot (p2c_vfam (V:(real->A topology)#
                                  (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
                                  W tt s z ** v))`
  (LABEL_TAC "CMP") THENL
   [MAP_EVERY X_GEN_TAC [`z:A`; `v:real^3`] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                      (real->A->real^3^3)`; `W:A->bool`; `tt - r pow 2`; `tt:real`;
                   `inv(r pow 2)`; `s:real`; `z:A`; `v:real^3`] P2AP_METRIC_COMPARE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[REAL_LE_INV_EQ; REAL_LE_POW_2] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[P2AP_RMETRIC_VFAM] THEN
    SUBGOAL_THEN `p2c_vfam (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                             (real->A->real^3^3)) W tt tt =
                  restrict_metric (rfs_vatlas V tt) W (rfs_vmetric V tt)`
    SUBST1_TAC THENL [REWRITE_TAC[p2c_vfam; ETA_AX]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o CONJUNCT2) THEN
    MATCH_MP_TAC(REAL_ARITH `a <= b ==> x <= a ==> x <= b`) THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
     [EXPAND_TAC "e" THEN REWRITE_TAC[GSYM REAL_EXP_N; REAL_EXP_MONO_LE] THEN
      SUBGOAL_THEN `&0 < r pow 2` ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `&4 * inv(r pow 2) * (tt - s) = (&4 * (tt - s)) / r pow 2` SUBST1_TAC THENL
       [REWRITE_TAC[real_div] THEN REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC P2AP_QFORM_NONNEG THEN
      MAP_EVERY EXISTS_TAC
       [`subtopology (rfs_vtop (V:(real->A topology)#
           (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt) W`;
        `restrict_atlas (rfs_vatlas (V:(real->A topology)#
           (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt) W`] THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* compactness of the closure of the Shi ball *)
  MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) tt`;
                 `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) tt`;
                 `rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                 (real->A->real^3^3)) tt`;
                 `x:A`; `r:real`;
                 `p2c_vfam (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) W tt s`;
                 `y:A`; `rho:real`; `e:real`] P2AP_BALL_COMPACT) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  (* Shi *)
  USE_THEN "SHI" (MP_TAC o SPECL
   [`subtopology (rfs_vtop (V:(real->A topology)#
       (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt) W`;
    `restrict_atlas (rfs_vatlas (V:(real->A topology)#
       (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt) W`;
    `s - rho pow 2`; `s:real`;
    `p2c_vfam (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                 (real->A->real^3^3)) W tt`; `y:A`; `rho:real`]) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[HAUSDORFF_SPACE_SUBTOPOLOGY] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`t:real`; `z:A`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(z:A) IN W` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`subtopology (rfs_vtop (V:(real->A topology)#
                        (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt) W`;
                     `restrict_atlas (rfs_vatlas (V:(real->A topology)#
                        (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt) W`;
                     `p2c_vfam (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                  (real->A->real^3^3)) W tt s`; `y:A`; `rho:real`]
                    P2AP_BALL_SUBSET) THEN
      ASM SET_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `p3_vrm (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                          (real->A->real^3^3)) t z` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC P2AP_VFAM_RM_NORM_LE THEN EXISTS_TAC `tt - r pow 2` THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(r pow 2)` THEN CONJ_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `y:A`) THEN
  ANTS_TAC THENL
   [MP_TAC(ISPECL [`subtopology (rfs_vtop (V:(real->A topology)#
                      (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt) W`;
                   `restrict_atlas (rfs_vatlas (V:(real->A topology)#
                      (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt) W`;
                   `p2c_vfam (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) W tt s`; `y:A`; `rho / &2`]
                  MFD_CENTRE_IN_BALL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `W:A->bool`; `tt - r pow 2`; `tt:real`; `s:real`;
                 `1`; `y:A`] P2AP_VFAM_DERIV) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  DISCH_TAC THEN
  (* the slice s contains y *)
  SUBGOAL_THEN `(y:A) IN topspace(rfs_vtop (V:(real->A topology)#
                  (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) s)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                      (real->A->real^3^3)`; `W:A->bool`; `tt - r pow 2`; `tt:real`]
                  P2AP_REGION_PERSISTS) THEN
    ASM_REWRITE_TAC[CONJUNCT2(CONJUNCT2(SPEC_ALL P2C_VIEW_EXPAND))] THEN
    DISCH_THEN(MP_TAC o SPEC `s:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o MATCH_MP OPEN_IN_SUBSET o CONJUNCT2) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `s:real`; `y:A`] P2AP_VGRADR_DERIV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `inv(rho pow 6) = (&4 * e) pow 6 * inv(r pow 6)` ASSUME_TAC THENL
   [UNDISCH_TAC `rho * (&4 * e) = r` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    SUBGOAL_THEN `~(rho = &0) /\ ~(e = &0)` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&9 * p3_vderiv2 (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                 (real->A->real^3^3)) 1 s y` THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `p3_vderiv2 (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                             (real->A->real^3^3)) 1 s y <= C * inv(rho pow 6)` THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Headlines.  Route O5 (P2A_ROUTE_PARABOLIC_STATEMENT: the statement        *)
(* P2A_REQ_SHI_SCALED_STATEMENT implies L8) and L8 itself                    *)
(* (P2A_PARABOLIC_STATEMENT, with that statement from RFA_P2A_REQ_SHI_SCALED *)
(* of pc_rfa_shiscale), with C1 = 3 sqrt C (4 e)^3 for the Shi constant C.   *)
(* ------------------------------------------------------------------------- *)

let P2AP_C1_SQUARE = prove
 (`!C e. &0 <= C
         ==> (&3 * sqrt C * (&4 * e) pow 3) pow 2 = &9 * C * (&4 * e) pow 6`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[REAL_POW_MUL; GSYM REAL_POW_POW] THEN ASM_SIMP_TAC[SQRT_POW_2] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[REAL_POW_POW] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC);;

let P2AP_ROUTE_PARABOLIC = prove
 (`!u:A->bool. P2A_ROUTE_PARABOLIC_STATEMENT u`,
  GEN_TAC THEN REWRITE_TAC[P2A_ROUTE_PARABOLIC_STATEMENT] THEN
  DISCH_THEN(fun th ->
    MP_TAC(GEN_REWRITE_RULE I [P2A_REQ_SHI_SCALED_STATEMENT] th)) THEN
  DISCH_THEN(X_CHOOSE_THEN `C:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (MP_TAC o MATCH_MP P2AP_GRAD_AT))) THEN
  DISCH_THEN(LABEL_TAC "GRAD") THEN
  REWRITE_TAC[P2A_PARABOLIC_STATEMENT] THEN
  EXISTS_TAC `&3 * sqrt C * (&4 * exp(&1)) pow 3` THEN
  SUBGOAL_THEN `&0 < exp(&1)` ASSUME_TAC THENL [REWRITE_TAC[REAL_EXP_POS_LT]; ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN REWRITE_TAC[REAL_OF_NUM_LT; ARITH] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[SQRT_POS_LT] THEN
    MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC
   [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
    `tt:real`; `x:A`; `r:real`] THEN
  STRIP_TAC THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`s:real`; `y:A`] THEN STRIP_TAC THEN
    MP_TAC(SPECL [`C:real`; `exp(&1)`] P2AP_C1_SQUARE) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    USE_THEN "GRAD" (MP_TAC o SPECL
     [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
      `tt:real`; `x:A`; `r:real`; `s:real`; `y:A`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; REAL_ARITH_TAC];
    MAP_EVERY X_GEN_TAC [`s:real`; `y:A`; `w:real^3`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                      (real->A->real^3^3)`; `rfs_vball V tt (x:A) r`; `tt - r pow 2`; `tt:real`;
                   `inv(r pow 2)`; `s:real`; `y:A`; `w:real^3`] P2AP_METRIC_COMPARE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[REAL_LE_INV_EQ; REAL_LE_POW_2]; ALL_TAC] THEN
    SUBGOAL_THEN `&4 * inv(r pow 2) * (tt - s) = &4 * (tt - s) / r pow 2` SUBST1_TAC THENL
     [REWRITE_TAC[real_div] THEN REAL_ARITH_TAC; SIMP_TAC[]]]);;

let P2AP_PARABOLIC = prove
 (`!u:A->bool. P2A_PARABOLIC_STATEMENT u`,
  GEN_TAC THEN MP_TAC(SPEC `u:A->bool` P2AP_ROUTE_PARABOLIC) THEN
  REWRITE_TAC[P2A_ROUTE_PARABOLIC_STATEMENT] THEN DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[RFA_P2A_REQ_SHI_SCALED]);;

