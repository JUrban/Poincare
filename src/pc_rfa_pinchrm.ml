(* ========================================================================= *)
(* Unit pc_rfa_pinchrm: under the Hamilton-Ivey pinching the curvature norm  *)
(* is bounded by the scalar curvature, |Rm| <= 2 |R| + 2 e^4 (RFA_PINCH_RM), *)
(* in dimension 3, with its helpers: every plane has a G-orthonormal basis   *)
(* (RFA_PLANE_ONB, scaling invariance RFA_LSECT_HOMOG), orthonormal pairs    *)
(* are non-collinear (RFA_ON_NONCOLL), every sectional curvature is at most  *)
(* R/2 - 2 sec_min (RFA_LSEC_UPPER, RFA_SEC_UPPER), and every plane extends  *)
(* to a frame whose three sectional curvatures sum to R/2 (RFA_FRAME3).  The *)
(* proofs are copies of lemmas of pc_p3_s13conf, pc_p3_s13plane and          *)
(* pc_p3_s16end, renamed RFA_ (each copy names its source), so that Part 2   *)
(* units can use them without loading the Part 3 proof units.  Needs only    *)
(* pc_rfa_pinch and Multivariate/cross.ml.                                   *)
(* ========================================================================= *)

needs "src/pc_rfa_pinch.ml";;
let rfa_prm_saved_interface = !the_interface;;
needs "Multivariate/cross.ml";;
the_interface := rfa_prm_saved_interface;;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* The copied lemmas.  The statements and proofs are those of the Part 3     *)
(* lemmas with the names changed; the source of each is marked.              *)
(* ========================================================================= *)

(* Copy of pc_p3_s13conf (P3S_LSECT_HOMOG), renamed. *)
let RFA_LSECT_HOMOG = prove
 (`!U (G:real^N->real^N^N) y c d u v.
     metric_field U G /\ y IN U /\ ~(c = &0) /\ ~(d = &0)
     ==> lsectional G y (c % u) (d % v) = lsectional G y u v`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[lsectional] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`]
         LRIEMANN_TRILINEAR) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `lriemann (G:real^N->real^N^N) y (c % u) (d % v) (d % v) =
    (c * d * d) % lriemann G y u v v`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`\x:real^N. lriemann (G:real^N->real^N^N) y x (d % v) (d % v)`;
                   `c:real`; `u:real^N`] LINEAR_CMUL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MP_TAC(ISPECL [`\x:real^N. lriemann (G:real^N->real^N^N) y u x (d % v)`;
                   `d:real`; `v:real^N`] LINEAR_CMUL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MP_TAC(ISPECL [`\x:real^N. lriemann (G:real^N->real^N^N) y u v x`;
                   `d:real`; `v:real^N`] LINEAR_CMUL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[VECTOR_MUL_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_RMUL; DOT_LMUL; DOT_RMUL] THEN
  ASM_CASES_TAC
   `(u dot ((G:real^N->real^N^N) y ** u)) * (v dot (G y ** v)) -
    (u dot (G y ** v)) pow 2 = &0` THENL
   [ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `(c * c * (u dot ((G:real^N->real^N^N) y ** u))) * d * d * (v dot (G y ** v)) -
      (c * d * (u dot (G y ** v))) pow 2 =
      (c * c * d * d) * ((u dot (G y ** u)) * (v dot (G y ** v)) - (u dot (G y ** v)) pow 2)`
    SUBST1_TAC THENL [REAL_ARITH_TAC; ASM_REWRITE_TAC[REAL_MUL_RZERO; real_div; REAL_INV_0]] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  POP_ASSUM MP_TAC THEN UNDISCH_TAC `~(c = &0)` THEN UNDISCH_TAC `~(d = &0)` THEN
  CONV_TAC REAL_FIELD);;

(* Copy of pc_p3_s13plane (P3S_PLANE_ONB), renamed. *)
let RFA_PLANE_ONB = prove
 (`!U (G:real^N->real^N^N) y u v.
     metric_field U G /\ y IN U /\ ~collinear {vec 0,u,v}
     ==> ?c1 c2 c. ~(c1 = &0) /\ ~(c2 = &0) /\
                   (c1 % u) dot (G y ** (c1 % u)) = &1 /\
                   (c2 % (v - c % u)) dot (G y ** (c2 % (v - c % u))) = &1 /\
                   (c1 % u) dot (G y ** (c2 % (v - c % u))) = &0 /\
                   ~collinear {vec 0,c1 % u,c2 % (v - c % u)} /\
                   (!H. metric_field U H
                        ==> lsectional H y (c1 % u) (c2 % (v - c % u)) =
                            lsectional H y u v)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[COLLINEAR_LEMMA; DE_MORGAN_THM; NOT_EXISTS_THM] THEN
  STRIP_TAC THEN
  ABBREV_TAC `nu = (u:real^N) dot ((G:real^N->real^N^N) y ** u)` THEN
  SUBGOAL_THEN `&0 < nu` ASSUME_TAC THENL
   [EXPAND_TAC "nu" THEN MATCH_MP_TAC LRG_METRIC_POS THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `c0 = ((u:real^N) dot ((G:real^N->real^N^N) y ** v)) / nu` THEN
  ABBREV_TAC `w = (v:real^N) - c0 % u` THEN
  SUBGOAL_THEN `~(w:real^N = vec 0)` ASSUME_TAC THENL
   [EXPAND_TAC "w" THEN REWRITE_TAC[VECTOR_SUB_EQ] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `nw = (w:real^N) dot ((G:real^N->real^N^N) y ** w)` THEN
  SUBGOAL_THEN `&0 < nw` ASSUME_TAC THENL
   [EXPAND_TAC "nw" THEN MATCH_MP_TAC LRG_METRIC_POS THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(u:real^N) dot ((G:real^N->real^N^N) y ** w) = &0` ASSUME_TAC THENL
   [EXPAND_TAC "w" THEN
    REWRITE_TAC[MATRIX_VECTOR_MUL_SUB_LDISTRIB; MATRIX_VECTOR_MUL_RMUL; DOT_RSUB;
                DOT_RMUL] THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "c0" THEN
    UNDISCH_TAC `&0 < nu` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt nu /\ &0 < sqrt nw /\ sqrt nu pow 2 = nu /\ sqrt nw pow 2 = nw`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LT; SQRT_POW_2; REAL_LT_IMP_LE]; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`inv(sqrt nu)`; `inv(sqrt nw)`; `c0:real`] THEN
  ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[REAL_INV_EQ_0; REAL_LT_IMP_NZ] THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_RMUL; DOT_LMUL; DOT_RMUL] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `inv(sqrt nu) * inv(sqrt nu) * nu = &1 /\
                inv(sqrt nw) * inv(sqrt nw) * nw = &1` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `sqrt nu pow 2 = nu` THEN UNDISCH_TAC `&0 < sqrt nu`;
      UNDISCH_TAC `sqrt nw pow 2 = nw` THEN UNDISCH_TAC `&0 < sqrt nw`] THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[REAL_MUL_RZERO] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[VECTOR_MUL_EQ_0; REAL_INV_EQ_0] THEN ASM_SIMP_TAC[REAL_LT_IMP_NZ];
    REWRITE_TAC[VECTOR_MUL_EQ_0; REAL_INV_EQ_0] THEN ASM_SIMP_TAC[REAL_LT_IMP_NZ];
    X_GEN_TAC `c:real` THEN DISCH_TAC THEN
    UNDISCH_TAC `(u:real^N) dot ((G:real^N->real^N^N) y ** w) = &0` THEN
    SUBGOAL_THEN `(w:real^N) = (sqrt nw * c * inv(sqrt nu)) % u` SUBST1_TAC THENL
     [MP_TAC(AP_TERM `(%) (sqrt nw):real^N->real^N` (ASSUME
        `inv(sqrt nw) % (w:real^N) = c % inv(sqrt nu) % u`)) THEN
      REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
      SUBGOAL_THEN `sqrt nw * inv(sqrt nw) = &1` SUBST1_TAC THENL
       [ASM_SIMP_TAC[REAL_MUL_RINV; REAL_LT_IMP_NZ]; ALL_TAC] THEN
      REWRITE_TAC[VECTOR_MUL_LID] THEN DISCH_THEN SUBST1_TAC THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[MATRIX_VECTOR_MUL_RMUL; DOT_RMUL] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[REAL_ENTIRE] THEN
    SUBGOAL_THEN `~(c = &0)` ASSUME_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC `inv(sqrt nw) % (w:real^N) = c % inv(sqrt nu) % u` THEN
      ASM_REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_MUL_EQ_0; REAL_INV_EQ_0] THEN
      ASM_SIMP_TAC[REAL_LT_IMP_NZ];
      ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_IMP_NZ; REAL_INV_EQ_0];
    X_GEN_TAC `H:real^N->real^N^N` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `H:real^N->real^N^N`; `y:real^N`; `inv(sqrt nu)`;
                   `inv(sqrt nw)`; `u:real^N`; `w:real^N`] RFA_LSECT_HOMOG) THEN
    ASM_SIMP_TAC[REAL_INV_EQ_0; REAL_LT_IMP_NZ] THEN DISCH_THEN(K ALL_TAC) THEN
    EXPAND_TAC "w" THEN MATCH_MP_TAC LSECTIONAL_SHEAR THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[]]);;

(* Copy of pc_p3_s13plane (P3S_ON_NONCOLL), renamed. *)
let RFA_ON_NONCOLL = prove
 (`!U (G:real^N->real^N^N) y u v.
     metric_field U G /\ y IN U /\
     u dot (G y ** u) = &1 /\ v dot (G y ** v) = &1 /\ u dot (G y ** v) = &0
     ==> ~collinear {vec 0,u,v}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[COLLINEAR_LEMMA; DE_MORGAN_THM; NOT_EXISTS_THM] THEN REPEAT CONJ_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `(u:real^N) dot ((G:real^N->real^N^N) y ** u) = &1` THEN
    ASM_REWRITE_TAC[DOT_LZERO] THEN REAL_ARITH_TAC;
    DISCH_TAC THEN UNDISCH_TAC `(v:real^N) dot ((G:real^N->real^N^N) y ** v) = &1` THEN
    ASM_REWRITE_TAC[DOT_LZERO] THEN REAL_ARITH_TAC;
    X_GEN_TAC `c:real` THEN DISCH_TAC THEN
    UNDISCH_TAC `(u:real^N) dot ((G:real^N->real^N^N) y ** v) = &0` THEN
    UNDISCH_TAC `(v:real^N) dot ((G:real^N->real^N^N) y ** v) = &1` THEN
    ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_RMUL; DOT_RMUL; DOT_LMUL; REAL_MUL_RID] THEN
    DISCH_TAC THEN DISCH_TAC THEN UNDISCH_TAC `c * c = &1` THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]);;

(* Copy of pc_p3_s16end (P3N_LSEC_UPPER), renamed. *)
let RFA_LSEC_UPPER = prove
 (`!U (G:real^3->real^3^3) y u v m0.
     metric_field U G /\ y IN U /\ ~collinear {vec 0,u,v} /\
     (!a b. ~collinear {vec 0,a,b} ==> m0 <= lsectional G y a b)
     ==> lsectional G y u v <= lscalar G y / &2 - &2 * m0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `u:real^3`; `v:real^3`]
                RFA_PLANE_ONB) THEN
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
   [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN MATCH_MP_TAC RFA_ON_NONCOLL THEN
    MAP_EVERY EXISTS_TAC [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN UNDISCH_TAC `lpcurv (G:real^3->real^3^3) y (\m. u1) +
                lpcurv G y (\m. v1) + lpcurv G y (\m. w1) = lscalar G y / &2` THEN
  REAL_ARITH_TAC);;

(* Copy of pc_p3_s16end (P3N_SEC_UPPER), renamed. *)
let RFA_SEC_UPPER = prove
 (`!top atlas (g:A->real^3^3) x u v.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     x IN topspace top /\ ~collinear {vec 0,u,v}
     ==> mfd_sectional atlas g x u v <=
         mfd_scalar atlas g x / &2 - &2 * mfd_sec_min atlas g x`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[mfd_sectional; mfd_scalar] THEN MATCH_MP_TAC RFA_LSEC_UPPER THEN
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

(* Copy of pc_p3_s16end (P3N_PINCH_RM), renamed. *)
let RFA_PINCH_RM = prove
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
                 `x:A`; `u:real^3`; `v:real^3`] RFA_SEC_UPPER) THEN
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

(* Copy of pc_p3_s16end (P3N_FRAME3), renamed. *)
let RFA_FRAME3 = prove
 (`!U (G:real^3->real^3^3) y u v.
     metric_field U G /\ y IN U /\ ~collinear {vec 0,u,v}
     ==> ?u1 v1 w1. lsectional G y u1 v1 = lsectional G y u v /\
                    ~collinear {vec 0,u1,v1} /\ ~collinear {vec 0,u1,w1} /\
                    ~collinear {vec 0,v1,w1} /\
                    lscalar G y = &2 * (lsectional G y u1 v1 + lsectional G y u1 w1 +
                                        lsectional G y v1 w1)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `u:real^3`; `v:real^3`]
                RFA_PLANE_ONB) THEN
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
    MATCH_MP_TAC RFA_ON_NONCOLL THEN
    MAP_EVERY EXISTS_TAC [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`] THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC RFA_ON_NONCOLL THEN
    MAP_EVERY EXISTS_TAC [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`] THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC RFA_ON_NONCOLL THEN
    MAP_EVERY EXISTS_TAC [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`] THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[ASSUME `lsectional (G:real^3->real^3^3) y u1 v1 = lpcurv G y (\m. w1)`;
                ASSUME `lsectional (G:real^3->real^3^3) y u1 w1 = lpcurv G y (\m. v1)`;
                ASSUME `lsectional (G:real^3->real^3^3) y v1 w1 = lpcurv G y (\m. u1)`] THEN
    UNDISCH_TAC `lpcurv (G:real^3->real^3^3) y (\m. u1) + lpcurv G y (\m. v1) +
                 lpcurv G y (\m. w1) = lscalar G y / &2` THEN
    REAL_ARITH_TAC]);;


