(* ========================================================================= *)
(* Unit pc_cmp_seg (comparison-geometry layer CMP): the segment domain of    *)
(* exp_x and the volume of metric balls.  With compact closure of B(x,R),    *)
(* exp_x is defined on the tangent ball of radius R; in an orthonormal frame *)
(* E the segment domain D (the w with |w| < R and d(x, exp_x(E w)) = |w|)  *)
(* is star-shaped, its interior part D0 (the w with s w in D for some       *)
(* s > 1) is mapped injectively, D \ D0 is null (disjoint dilates), and so  *)
(* vol B(x,r) = int over B(0,r) of 1_D0 sqrt(det G) for the exp pullback     *)
(* metric G.                                                                 *)
(* ========================================================================= *)

needs "src/pc_cmp_dens.ml";;
needs "src/pc_grg_distcont.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* Compact closure of B(x,R) puts the tangent ball of radius R               *)
(* into the domain of exp_x (escape lemma MFD_GEO_ESCAPE).                   *)
(* ========================================================================= *)

let CMPQ_MAXINT_RADIUS = prove
 (`!top atlas (g:A->real^N^N) (x:A) u R t.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ x IN topspace top /\
        compact_in top (top closure_of mfd_ball (top,atlas) g x R) /\
        mfd_tnorm g x u = &1 /\ &0 <= t /\ t < R
        ==> t IN mfd_geo_maxint (top,atlas) g x u`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `u:real^N`] MFD_GEO_MAXIMAL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_CASES_TAC `t IN mfd_geo_maxint (top,atlas) (g:A->real^N^N) x u` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!s. s IN mfd_geo_maxint (top,atlas) (g:A->real^N^N) x u ==> s < t`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:real` THEN DISCH_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LE] THEN
    DISCH_TAC THEN
    UNDISCH_TAC `~(t IN mfd_geo_maxint (top,atlas) (g:A->real^N^N) x u)` THEN
    REWRITE_TAC[] THEN
    UNDISCH_TAC `is_realinterval(mfd_geo_maxint (top,atlas) (g:A->real^N^N) x u)` THEN
    REWRITE_TAC[is_realinterval] THEN DISCH_THEN MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`&0`; `s:real`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `u:real^N`;
                 `top closure_of mfd_ball (top,atlas) (g:A->real^N^N) x R`; `t:real`]
    MFD_GEO_ESCAPE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `t1:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `max (&0) t1 IN mfd_geo_maxint (top,atlas) (g:A->real^N^N) x u`
  ASSUME_TAC THENL
   [REWRITE_TAC[real_max] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `max (&0) t1`) THEN
  ASM_REWRITE_TAC[REAL_ARITH `t1 <= max (&0) t1`] THEN
  MATCH_MP_TAC(SET_RULE `!x:A s t. x IN s /\ s SUBSET t ==> x IN t`) THEN
  EXISTS_TAC `mfd_ball (top,atlas) (g:A->real^N^N) x R` THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `mfd_geo (top,atlas) (g:A->real^N^N) x u`;
                   `mfd_geo_maxint (top,atlas) (g:A->real^N^N) x u`; `&0`; `max (&0) t1`]
      GEOH_GEO_SEG_DIST) THEN
    ASM_REWRITE_TAC[REAL_SUB_RZERO; REAL_MUL_RID] THEN
    REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `max (&0) t1 < t` MP_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC CLOSURE_OF_SUBSET THEN REWRITE_TAC[SUBSET; mfd_ball; IN_ELIM_THM] THEN
    MESON_TAC[MFD_JOINABLE_IN_TOPSPACE]]);;

let CMPQ_COMPACT_DOM = prove
 (`!top atlas (g:A->real^N^N) (x:A) R.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ x IN topspace top /\
        compact_in top (top closure_of mfd_ball (top,atlas) g x R)
        ==> mfd_tball g x R SUBSET mfd_exp_dom (top,atlas) g x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SUBSET; mfd_tball; IN_ELIM_THM] THEN
  X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`] GEOD_TNORM_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_CASES_TAC `v:real^N = vec 0` THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x:A`] MFD_EXP_DOM) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < mfd_tnorm (g:A->real^N^N) x v` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ ~(x = &0) ==> &0 < x`) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x:A`; `v:real^N`] GEOD_TNORM_EQ_0) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `a = mfd_tnorm (g:A->real^N^N) x v` THEN
  SUBGOAL_THEN `mfd_tnorm (g:A->real^N^N) x (inv a % v) = &1` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_ABS_INV] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < a ==> abs a = a`; REAL_MUL_LINV; REAL_LT_IMP_NZ];
    ALL_TAC] THEN
  SUBGOAL_THEN `v:real^N = a % (inv a % v)` SUBST1_TAC THENL
   [ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_RINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `inv a % (v:real^N)`; `a:real`] MFD_EXP_RADIAL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN
  MATCH_MP_TAC CMPQ_MAXINT_RADIUS THEN EXISTS_TAC `R:real` THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE]);;

(* ========================================================================= *)
(* The segment domain D of x in an orthonormal frame E,                      *)
(* D: the w with |w| < R and d(x, exp_x(E w)) = |w|; its interior part     *)
(* D0: the w with s w in D for some s > 1.  D and D0 are star-shaped, D0 is *)
(* in D, exp_x o E maps D onto the ball, is injective on D0 and does not     *)
(* identify a point of D0 with a point of D, and d exp_x is injective along  *)
(* the rays of D0 a little beyond the point (S5).                            *)
(* ========================================================================= *)

let CMPQ_S5 = REWRITE_RULE[CMP_MINIMIZING_GEODESIC_STATEMENT]
  (ISPECL [`UNIV:A->bool`; `UNIV:N->bool`] CMP_MINIMIZING_GEODESIC);;

let CMPQ_FRAME_INVERTIBLE = prove
 (`!(g:A->real^N^N) x E. mfd_orthonormal_frame g x E ==> invertible E`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[INVERTIBLE_LEFT_INVERSE] THEN
  EXISTS_TAC `transp(E:real^N^N) ** (g:A->real^N^N) x` THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [mfd_orthonormal_frame]) THEN
  REWRITE_TAC[GSYM MATRIX_MUL_ASSOC]);;

let CMPQ_FRAME_DOM = prove
 (`!top atlas (g:A->real^N^N) (x:A) (E:real^N^N) R w.
        mfd_orthonormal_frame g x E /\
        mfd_tball g x R SUBSET mfd_exp_dom (top,atlas) g x /\ norm w < R
        ==> E ** w IN mfd_exp_dom (top,atlas) g x`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CMPP_BALL_IN_DOM THEN
  MAP_EVERY EXISTS_TAC [`g:A->real^N^N`; `x:A`; `R:real`] THEN ASM_REWRITE_TAC[]);;

let CMPQ_SEG_STAR = prove
 (`!top atlas (g:A->real^N^N) (x:A) (E:real^N^N) R w t.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ x IN topspace top /\
        mfd_orthonormal_frame g x E /\
        mfd_tball g x R SUBSET mfd_exp_dom (top,atlas) g x /\
        norm w < R /\
        mfd_dist (top,atlas) g x (mfd_exp (top,atlas) g x (E ** w)) = norm w /\
        &0 <= t /\ t <= &1
        ==> norm(t % w) < R /\
            mfd_dist (top,atlas) g x (mfd_exp (top,atlas) g x (E ** (t % w))) =
            norm(t % w)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `norm((t:real) % (w:real^N)) = t * norm w` ASSUME_TAC THENL
   [ASM_SIMP_TAC[NORM_MUL; REAL_ARITH `&0 <= t ==> abs t = t`]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `norm(w:real^N)` THEN
    ASM_REWRITE_TAC[] THEN GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[NORM_POS_LE];
    ALL_TAC] THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_RMUL] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `(E:real^N^N) ** w`; `t:real`] CMPS_RAY_DIST0) THEN
  ASM_SIMP_TAC[CMPP_TNORM_FRAME] THEN ANTS_TAC THENL
   [MATCH_MP_TAC CMPQ_FRAME_DOM THEN EXISTS_TAC `R:real` THEN ASM_REWRITE_TAC[];
    SIMP_TAC[]]);;

let CMPQ_SEG0_SUB = prove
 (`!top atlas (g:A->real^N^N) (x:A) (E:real^N^N) R w s.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ x IN topspace top /\
        mfd_orthonormal_frame g x E /\
        mfd_tball g x R SUBSET mfd_exp_dom (top,atlas) g x /\
        &1 < s /\ norm(s % w) < R /\
        mfd_dist (top,atlas) g x (mfd_exp (top,atlas) g x (E ** (s % w))) = norm(s % w)
        ==> norm w < R /\
            mfd_dist (top,atlas) g x (mfd_exp (top,atlas) g x (E ** w)) = norm w`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `E:real^N^N`; `R:real`; `(s:real) % (w:real^N)`;
                 `inv(s:real)`] CMPQ_SEG_STAR) THEN
  ASM_REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
  ASM_SIMP_TAC[REAL_MUL_LINV; REAL_ARITH `&1 < s ==> ~(s = &0)`; VECTOR_MUL_LID] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_INV_LE_1; REAL_LT_IMP_LE] THEN
  ASM_REAL_ARITH_TAC);;

let CMPQ_SEG_IMAGE = prove
 (`!top atlas (g:A->real^N^N) (x:A) (E:real^N^N) R r.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ x IN topspace top /\
        mfd_orthonormal_frame g x E /\
        mfd_tball g x R SUBSET mfd_exp_dom (top,atlas) g x /\ r <= R
        ==> IMAGE (\w. mfd_exp (top,atlas) g x (E ** w))
              ({w | norm w < R /\
                    mfd_dist (top,atlas) g x (mfd_exp (top,atlas) g x (E ** w)) = norm w}
               INTER ball(vec 0,r)) =
            mfd_ball (top,atlas) g x r`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP CMPQ_FRAME_INVERTIBLE) THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_INTER; IN_ELIM_THM; IN_BALL_0; mfd_ball] THEN
  X_GEN_TAC `y:A` THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x:A`; `(E:real^N^N) ** w`] CMPH_EXP_DIST_LE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CMPQ_FRAME_DOM THEN
      EXISTS_TAC `R:real` THEN ASM_REWRITE_TAC[];
      SIMP_TAC[]];
    STRIP_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `r:real`; `y:A`] MFD_LOCAL_HOPF_RINOW) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `mfd_tball (g:A->real^N^N) x R` THEN
    ASM_REWRITE_TAC[mfd_tball; SUBSET; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
    DISCH_THEN(X_CHOOSE_THEN `v:real^N` STRIP_ASSUME_TAC)] THEN
  EXISTS_TAC `matrix_inv(E:real^N^N) ** v` THEN
  SUBGOAL_THEN `(E:real^N^N) ** matrix_inv E ** v = v` ASSUME_TAC THENL
   [ASM_SIMP_TAC[MATRIX_VECTOR_MUL_ASSOC; MATRIX_INV; MATRIX_VECTOR_MUL_LID]; ALL_TAC] THEN
  SUBGOAL_THEN `norm(matrix_inv(E:real^N^N) ** v) = mfd_dist (top,atlas) (g:A->real^N^N) x (y:A)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`g:A->real^N^N`; `x:A`; `E:real^N^N`;
                   `matrix_inv(E:real^N^N) ** v`] CMPP_TNORM_FRAME) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let CMPQ_SEG_MIN = prove
 (`!top atlas (g:A->real^N^N) (x:A) (E:real^N^N) R w.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ x IN topspace top /\
        mfd_orthonormal_frame g x E /\
        mfd_tball g x R SUBSET mfd_exp_dom (top,atlas) g x /\ norm w < R /\
        mfd_dist (top,atlas) g x (mfd_exp (top,atlas) g x (E ** w)) = norm w
        ==> E ** w IN mfd_exp_dom (top,atlas) g x /\
            mfd_dist (top,atlas) g x (mfd_exp (top,atlas) g x (E ** w)) =
            mfd_tnorm g x (E ** w)`,
  REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC CMPQ_FRAME_DOM THEN EXISTS_TAC `R:real` THEN ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[CMPP_TNORM_FRAME]]);;

let CMPQ_SEG_INJ = prove
 (`!top atlas (g:A->real^N^N) (x:A) (E:real^N^N) R w1 w2 s.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ x IN topspace top /\
        mfd_orthonormal_frame g x E /\
        mfd_tball g x R SUBSET mfd_exp_dom (top,atlas) g x /\
        &1 < s /\ norm(s % w1) < R /\
        mfd_dist (top,atlas) g x (mfd_exp (top,atlas) g x (E ** (s % w1))) = norm(s % w1) /\
        norm w2 < R /\
        mfd_dist (top,atlas) g x (mfd_exp (top,atlas) g x (E ** w2)) = norm w2 /\
        mfd_exp (top,atlas) g x (E ** w1) = mfd_exp (top,atlas) g x (E ** w2)
        ==> w1 = w2`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `E:real^N^N`; `R:real`; `w1:real^N`; `s:real`]
    CMPQ_SEG0_SUB) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `norm(w2:real^N) = norm(w1:real^N)` ASSUME_TAC THENL
   [UNDISCH_TAC `mfd_dist (top,atlas) (g:A->real^N^N) x
                   (mfd_exp (top,atlas) g x ((E:real^N^N) ** w1)) = norm(w1:real^N)` THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `E:real^N^N`; `R:real`; `(s:real) % (w1:real^N)`]
    CMPQ_SEG_MIN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `(E:real^N^N) ** ((s:real) % (w1:real^N))`]
    CMPQ_S5) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[CMPP_TNORM_FRAME]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `inv(s:real)`) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_INV THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_INV_LT_1 THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `inv(s:real) % ((E:real^N^N) ** (s % w1)) = E ** w1` SUBST1_TAC THENL
   [REWRITE_TAC[MATRIX_VECTOR_MUL_RMUL; VECTOR_MUL_ASSOC] THEN
    ASM_SIMP_TAC[REAL_MUL_LINV; REAL_ARITH `&1 < s ==> ~(s = &0)`; VECTOR_MUL_LID];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `(E:real^N^N) ** w2` o CONJUNCT1 o CONJUNCT2) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CMPQ_FRAME_DOM THEN EXISTS_TAC `R:real` THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[CMPP_TNORM_FRAME; NORM_MUL; REAL_MUL_ASSOC;
                   REAL_ARITH `&1 < s ==> abs s = s`; REAL_MUL_LINV;
                   REAL_ARITH `&1 < s ==> ~(s = &0)`; REAL_MUL_LID; REAL_LE_REFL]];
    ALL_TAC] THEN
  DISCH_TAC THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC(VECTOR_ARITH `a - b:real^N = vec 0 ==> a = b`) THEN
  MATCH_MP_TAC CMPR_INVERTIBLE_KER THEN EXISTS_TAC `E:real^N^N` THEN
  ASM_SIMP_TAC[MATRIX_VECTOR_MUL_SUB_LDISTRIB; VECTOR_SUB_EQ] THEN
  ASM_MESON_TAC[CMPQ_FRAME_INVERTIBLE]);;

let CMPQ_SEG0_DEXP = prove
 (`!top atlas (g:A->real^N^N) (x:A) (E:real^N^N) R w s.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ x IN topspace top /\
        mfd_orthonormal_frame g x E /\
        mfd_tball g x R SUBSET mfd_exp_dom (top,atlas) g x /\
        &1 < s /\ norm(s % w) < R /\
        mfd_dist (top,atlas) g x (mfd_exp (top,atlas) g x (E ** (s % w))) = norm(s % w)
        ==> !t h. &0 <= t /\ t < s /\
                  mfd_differential (open_set_atlas (:real^N)) atlas
                    (mfd_exp (top,atlas) g x) (E ** (t % w)) h = vec 0
                  ==> h = vec 0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MAP_EVERY X_GEN_TAC [`t:real`; `h:real^N`] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `E:real^N^N`; `R:real`; `(s:real) % (w:real^N)`]
    CMPQ_SEG_MIN) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `(E:real^N^N) ** ((s:real) % (w:real^N))`]
    CMPQ_S5) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `t / s`) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_ARITH `&1 < s ==> &0 < s`] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(MATCH_MP_TAC o CONJUNCT2 o CONJUNCT2) THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_RMUL; VECTOR_MUL_ASSOC] THEN
  SUBGOAL_THEN `t / s * s = t` SUBST1_TAC THENL
   [MATCH_MP_TAC REAL_DIV_RMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) &&
     rand(concl th) = `vec 0:real^N`)) THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_RMUL]);;

(* ========================================================================= *)
(* Measurability.  w -> d(x, exp_x(E w)) is continuous on the                *)
(* tangent ball, so D is relatively closed in ball(0,R) and D0 is the        *)
(* countable union of the dilates (1 + 1/(n+1))^-1 D.                        *)
(* ========================================================================= *)

let CMPQ_EXPF_CONT = prove
 (`!top atlas (g:A->real^N^N) (x:A) (E:real^N^N) S.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ x IN topspace top /\
        (!w. w IN S ==> E ** w IN mfd_exp_dom (top,atlas) g x)
        ==> continuous_map (subtopology euclidean S,top)
              (\w. mfd_exp (top,atlas) g x (E ** w))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `(\w. mfd_exp (top,atlas) (g:A->real^N^N) x ((E:real^N^N) ** w)) =
    mfd_exp (top,atlas) g x o (\w. E ** w)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
  EXISTS_TAC `subtopology euclidean (mfd_exp_dom (top,atlas) (g:A->real^N^N) x)` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[CONTINUOUS_MAP_EUCLIDEAN2] THEN CONJ_TAC THENL
     [MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN REWRITE_TAC[MATRIX_VECTOR_MUL_LINEAR];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM_SIMP_TAC[]];
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x:A`] MFD_EXP_SMOOTH) THEN
    ASM_SIMP_TAC[]]);;

let CMPQ_SEG_MEAS = prove
 (`!top atlas (g:A->real^N^N) (x:A) (E:real^N^N) R.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ x IN topspace top /\
        mfd_orthonormal_frame g x E /\
        mfd_tball g x R SUBSET mfd_exp_dom (top,atlas) g x
        ==> lebesgue_measurable
              {w | norm w < R /\
                   mfd_dist (top,atlas) g x (mfd_exp (top,atlas) g x (E ** w)) = norm w} /\
            measurable
              {w | norm w < R /\
                   mfd_dist (top,atlas) g x (mfd_exp (top,atlas) g x (E ** w)) = norm w}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(\w. lift(mfd_dist (top,atlas) (g:A->real^N^N) x
                (mfd_exp (top,atlas) g x ((E:real^N^N) ** w)))) continuous_on
    ball(vec 0:real^N,R)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `(\w. lift(mfd_dist (top,atlas) (g:A->real^N^N) x
                  (mfd_exp (top,atlas) g x ((E:real^N^N) ** w)))) =
      lift o (\y. mfd_dist (top,atlas) g x y) o (\w. mfd_exp (top,atlas) g x (E ** w))`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    REWRITE_TAC[GSYM CONTINUOUS_MAP_EUCLIDEAN; GSYM CONTINUOUS_MAP_EQ_LIFT] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN EXISTS_TAC `top:A topology` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CMPQ_EXPF_CONT THEN ASM_REWRITE_TAC[IN_BALL_0] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC CMPQ_FRAME_DOM THEN
      EXISTS_TAC `R:real` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC MFD_DIST_CONTINUOUS_RIGHT THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `{w | norm w < R /\
         mfd_dist (top,atlas) (g:A->real^N^N) x
           (mfd_exp (top,atlas) g x ((E:real^N^N) ** w)) = norm w} =
    {w | w IN ball(vec 0:real^N,R) /\
         (\w. lift(mfd_dist (top,atlas) g x (mfd_exp (top,atlas) g x (E ** w))) -
              lift(norm w)) w = vec 0}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_BALL_0; VECTOR_SUB_EQ; LIFT_EQ]; ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
   [MATCH_MP_TAC LEBESGUE_MEASURABLE_CLOSED_IN THEN
    EXISTS_TAC `ball(vec 0:real^N,R)` THEN REWRITE_TAC[LEBESGUE_MEASURABLE_BALL] THEN
    MATCH_MP_TAC CONTINUOUS_CLOSED_IN_PREIMAGE_CONSTANT THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUB THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[REWRITE_RULE[o_DEF] CONTINUOUS_ON_LIFT_NORM];
    DISCH_TAC THEN MATCH_MP_TAC MEASURABLE_LEBESGUE_MEASURABLE_SUBSET THEN
    EXISTS_TAC `ball(vec 0:real^N,R)` THEN ASM_REWRITE_TAC[MEASURABLE_BALL] THEN
    SET_TAC[]]);;

let CMPQ_SEG0_UNIONS = prove
 (`!top atlas (g:A->real^N^N) (x:A) (E:real^N^N) R.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ x IN topspace top /\
        mfd_orthonormal_frame g x E /\
        mfd_tball g x R SUBSET mfd_exp_dom (top,atlas) g x
        ==> {w | ?s. &1 < s /\ norm(s % w) < R /\
                     mfd_dist (top,atlas) g x (mfd_exp (top,atlas) g x (E ** (s % w))) =
                     norm(s % w)} =
            UNIONS {IMAGE (\w. inv(&1 + inv(&n + &1)) % w)
                      {w | norm w < R /\
                           mfd_dist (top,atlas) g x (mfd_exp (top,atlas) g x (E ** w)) =
                           norm w} | n IN (:num)}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!n. &1 < &1 + inv(&n + &1)` ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[REAL_LT_ADDR; REAL_LT_INV_EQ] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_UNIONS; IN_ELIM_THM; IN_UNIV] THEN
  X_GEN_TAC `w:real^N` THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `s:real` STRIP_ASSUME_TAC) THEN
    MP_TAC(SPEC `s - &1` REAL_ARCH_INV) THEN
    ASM_REWRITE_TAC[REAL_SUB_LT] THEN
    DISCH_THEN(X_CHOOSE_THEN `n:num` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `&1 + inv(&n + &1) < s` ASSUME_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `!x y s. y <= x /\ x < s - &1 ==> &1 + y < s`) THEN
      EXISTS_TAC `inv(&n)` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_INV2 THEN ASM_SIMP_TAC[REAL_OF_NUM_LT; LE_1] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    EXISTS_TAC `IMAGE (\w:real^N. inv(&1 + inv(&n + &1)) % w)
                  {w | norm w < R /\
                       mfd_dist (top,atlas) (g:A->real^N^N) x
                         (mfd_exp (top,atlas) g x ((E:real^N^N) ** w)) = norm w}` THEN
    CONJ_TAC THENL [EXISTS_TAC `n:num` THEN REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
    EXISTS_TAC `(&1 + inv(&n + &1)) % (w:real^N)` THEN CONJ_TAC THENL
     [REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
      SUBGOAL_THEN `inv(&1 + inv(&n + &1)) * (&1 + inv(&n + &1)) = &1` SUBST1_TAC THENL
       [MATCH_MP_TAC REAL_MUL_LINV THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `n:num` o check (fun th -> is_forall(concl th) &&
          fst(dest_var(fst(dest_forall(concl th)))) = "n")) THEN REAL_ARITH_TAC;
        REWRITE_TAC[VECTOR_MUL_LID]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x:A`; `E:real^N^N`; `R:real`; `(s:real) % (w:real^N)`;
                   `(&1 + inv(&n + &1)) / s`] CMPQ_SEG_STAR) THEN
    ASM_REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
    SUBGOAL_THEN `(&1 + inv(&n + &1)) / s * s = &1 + inv(&n + &1)` SUBST1_TAC THENL
     [MATCH_MP_TAC REAL_DIV_RMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    SUBGOAL_THEN `&0 < s` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= &1 + inv(&n + &1)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_ADD THEN REWRITE_TAC[REAL_POS; REAL_LE_INV_EQ] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LE_DIV; REAL_MUL_LID; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` (CONJUNCTS_THEN2
    (X_CHOOSE_TAC `n:num`) ASSUME_TAC)) THEN
  UNDISCH_TAC `(w:real^N) IN t` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `&1 + inv(&n + &1)` THEN ASM_REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
  SUBGOAL_THEN `(&1 + inv(&n + &1)) * inv(&1 + inv(&n + &1)) = &1` SUBST1_TAC THENL
   [MATCH_MP_TAC REAL_MUL_RINV THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `n:num` o check (fun th -> is_forall(concl th) &&
      fst(dest_var(fst(dest_forall(concl th)))) = "n")) THEN REAL_ARITH_TAC;
    ASM_REWRITE_TAC[VECTOR_MUL_LID]]);;

let CMPQ_SEG0_MEAS = prove
 (`!top atlas (g:A->real^N^N) (x:A) (E:real^N^N) R.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ x IN topspace top /\
        mfd_orthonormal_frame g x E /\
        mfd_tball g x R SUBSET mfd_exp_dom (top,atlas) g x
        ==> lebesgue_measurable
              {w | ?s. &1 < s /\ norm(s % w) < R /\
                       mfd_dist (top,atlas) g x (mfd_exp (top,atlas) g x (E ** (s % w))) =
                       norm(s % w)}`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[CMPQ_SEG0_UNIONS] THEN
  MATCH_MP_TAC LEBESGUE_MEASURABLE_COUNTABLE_UNIONS THEN CONJ_TAC THENL
   [ONCE_REWRITE_TAC[SIMPLE_IMAGE] THEN MATCH_MP_TAC COUNTABLE_IMAGE THEN
    REWRITE_TAC[NUM_COUNTABLE];
    REWRITE_TAC[FORALL_IN_GSPEC; IN_UNIV] THEN GEN_TAC THEN
    MATCH_MP_TAC MEASURABLE_IMP_LEBESGUE_MEASURABLE THEN
    MATCH_MP_TAC MEASURABLE_SCALING THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x:A`; `E:real^N^N`; `R:real`] CMPQ_SEG_MEAS) THEN
    ASM_SIMP_TAC[]]);;

(* ========================================================================= *)
(* D \ D0 is null.  The dilates of Z = D \ D0 by distinct                    *)
(* factors in [1,2) are disjoint (a point of Z is not a proper dilate of a   *)
(* point of D), each has measure at least |Z|, and all lie in ball(0,2R);    *)
(* so m |Z| <= |ball(0,2R)| for every m.                                     *)
(* ========================================================================= *)

let CMPQ_NULL_ABSTRACT = prove
 (`!(D:real^N->bool) R.
        measurable D /\ D SUBSET ball(vec 0,R) /\
        lebesgue_measurable {w | ?s. &1 < s /\ s % w IN D}
        ==> negligible (D DIFF {w | ?s. &1 < s /\ s % w IN D})`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `Z = (D:real^N->bool) DIFF {w | ?s. &1 < s /\ s % w IN D}` THEN
  SUBGOAL_THEN `measurable(Z:real^N->bool) /\ Z SUBSET ball(vec 0,R)` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `q /\ (q ==> p) ==> p /\ q`) THEN CONJ_TAC THENL
     [EXPAND_TAC "Z" THEN ASM SET_TAC[]; DISCH_TAC] THEN
    MATCH_MP_TAC MEASURABLE_LEBESGUE_MEASURABLE_SUBSET THEN
    EXISTS_TAC `ball(vec 0:real^N,R)` THEN ASM_REWRITE_TAC[MEASURABLE_BALL] THEN
    EXPAND_TAC "Z" THEN MATCH_MP_TAC LEBESGUE_MEASURABLE_DIFF THEN
    ASM_SIMP_TAC[MEASURABLE_IMP_LEBESGUE_MEASURABLE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!a b z1 z2. &1 <= a /\ a < b /\ (z1:real^N) IN Z /\ z2 IN Z ==> ~(a % z1 = b % z2)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(z2:real^N) IN {w | ?s. &1 < s /\ s % w IN D}` MP_TAC THENL
     [REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `b / a` THEN
      ASM_SIMP_TAC[REAL_LT_RDIV_EQ; REAL_ARITH `&1 <= a ==> &0 < a`; REAL_MUL_LID] THEN
      SUBGOAL_THEN `(b / a) % (z2:real^N) = z1` SUBST1_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o AP_TERM `(%) (inv a):real^N->real^N` o SYM) THEN
        REWRITE_TAC[VECTOR_MUL_ASSOC; real_div] THEN
        ASM_SIMP_TAC[REAL_MUL_LINV; REAL_ARITH `&1 <= a ==> ~(a = &0)`; VECTOR_MUL_LID] THEN
        DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN
        AP_THM_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
        ASM SET_TAC[]];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!m. 1 <= m ==> &m * measure(Z:real^N->bool) <= measure(ball(vec 0:real^N,&2 * R))`
  ASSUME_TAC THENL
   [X_GEN_TAC `m:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 < &m` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LT] THEN UNDISCH_TAC `1 <= (m:num)` THEN ARITH_TAC; ALL_TAC] THEN
    ABBREV_TAC `c = \j. &1 + &j / &m` THEN
    SUBGOAL_THEN `!j. j <= m - 1 ==> &1 <= (c:num->real) j /\ c j < &2` ASSUME_TAC THENL
     [X_GEN_TAC `j:num` THEN DISCH_TAC THEN EXPAND_TAC "c" THEN
      ASM_SIMP_TAC[REAL_LE_ADDR; REAL_LE_DIV; REAL_POS; REAL_LT_IMP_LE] THEN
      MATCH_MP_TAC(REAL_ARITH `x < &1 ==> &1 + x < &2`) THEN
      ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_MUL_LID; REAL_OF_NUM_LT] THEN
      MAP_EVERY UNDISCH_TAC [`(j:num) <= m - 1`; `1 <= (m:num)`] THEN ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `!i j. i < j ==> (c:num->real) i < c j` ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN EXPAND_TAC "c" THEN
      REWRITE_TAC[REAL_LT_LADD; real_div] THEN MATCH_MP_TAC REAL_LT_RMUL THEN
      ASM_REWRITE_TAC[REAL_OF_NUM_LT; REAL_LT_INV_EQ];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`\j. IMAGE (\z:real^N. (c:num->real) j % z) Z`; `0..m-1`]
      MEASURE_DISJOINT_UNIONS_IMAGE) THEN
    REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG; LE_0] THEN ANTS_TAC THENL
     [CONJ_TAC THENL [ASM_SIMP_TAC[MEASURABLE_SCALING]; ALL_TAC] THEN
      MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
      REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_IMAGE; NOT_IN_EMPTY] THEN
      X_GEN_TAC `y:real^N` THEN
      DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `z1:real^N` STRIP_ASSUME_TAC)
                                 (X_CHOOSE_THEN `z2:real^N` STRIP_ASSUME_TAC)) THEN
      SUBGOAL_THEN `(i:num) < j \/ j < i` MP_TAC THENL
       [UNDISCH_TAC `~(i:num = j)` THEN ARITH_TAC; ALL_TAC] THEN
      STRIP_TAC THENL
       [UNDISCH_TAC `!a b z1 z2. &1 <= a /\ a < b /\ (z1:real^N) IN Z /\ z2 IN Z
                                 ==> ~(a % z1 = b % z2)` THEN
        DISCH_THEN(MP_TAC o SPECL [`(c:num->real) i`; `(c:num->real) j`;
                                   `z1:real^N`; `z2:real^N`]);
        UNDISCH_TAC `!a b z1 z2. &1 <= a /\ a < b /\ (z1:real^N) IN Z /\ z2 IN Z
                                 ==> ~(a % z1 = b % z2)` THEN
        DISCH_THEN(MP_TAC o SPECL [`(c:num->real) j`; `(c:num->real) i`;
                                   `z2:real^N`; `z1:real^N`])] THEN
      ASM_SIMP_TAC[] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    DISCH_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `measure(UNIONS(IMAGE (\j. IMAGE (\z:real^N. (c:num->real) j % z) Z)
                                     (0..m-1)))` THEN
    CONJ_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `sum(0..m-1) (\j. measure(Z:real^N->bool))` THEN CONJ_TAC THENL
       [REWRITE_TAC[SUM_CONST_NUMSEG] THEN
        SUBGOAL_THEN `(m - 1 + 1) - 0 = m` SUBST1_TAC THENL
         [UNDISCH_TAC `1 <= (m:num)` THEN ARITH_TAC; REWRITE_TAC[REAL_LE_REFL]];
        MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
        REWRITE_TAC[] THEN ASM_SIMP_TAC[MEASURE_SCALING] THEN
        GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
        MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[MEASURE_POS_LE] THEN
        MATCH_MP_TAC REAL_POW_LE_1 THEN
        SUBGOAL_THEN `&1 <= (c:num->real) j` MP_TAC THENL
         [ASM_SIMP_TAC[]; REAL_ARITH_TAC]];
      MATCH_MP_TAC MEASURE_SUBSET THEN REWRITE_TAC[MEASURABLE_BALL] THEN CONJ_TAC THENL
       [MATCH_MP_TAC MEASURABLE_UNIONS THEN
        SIMP_TAC[FINITE_IMAGE; FINITE_NUMSEG; FORALL_IN_IMAGE] THEN
        ASM_SIMP_TAC[MEASURABLE_SCALING];
        REWRITE_TAC[SUBSET; IN_UNIONS; IN_IMAGE; IN_NUMSEG; LE_0] THEN
        X_GEN_TAC `y:real^N` THEN
        DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` (CONJUNCTS_THEN2
          (X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) MP_TAC)) THEN
        ASM_REWRITE_TAC[IN_IMAGE] THEN
        DISCH_THEN(X_CHOOSE_THEN `z:real^N` STRIP_ASSUME_TAC) THEN
        ASM_REWRITE_TAC[IN_BALL_0; NORM_MUL] THEN
        SUBGOAL_THEN `&1 <= (c:num->real) j /\ c j < &2` STRIP_ASSUME_TAC THENL
         [ASM_SIMP_TAC[]; ALL_TAC] THEN
        SUBGOAL_THEN `norm(z:real^N) < R` ASSUME_TAC THENL
         [UNDISCH_TAC `(z:real^N) IN Z` THEN
          UNDISCH_TAC `Z SUBSET ball(vec 0:real^N,R)` THEN
          REWRITE_TAC[SUBSET; IN_BALL_0] THEN MESON_TAC[];
          ALL_TAC] THEN
        ASM_SIMP_TAC[REAL_ARITH `&1 <= c ==> abs c = c`] THEN
        MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `&2 * norm(z:real^N)` THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[NORM_POS_LE; REAL_LT_IMP_LE];
          ASM_REAL_ARITH_TAC]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `measure(Z:real^N->bool) = &0` MP_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ ~(&0 < x) ==> x = &0`) THEN
    ASM_SIMP_TAC[MEASURE_POS_LE] THEN DISCH_TAC THEN
    MP_TAC(SPEC `measure(ball(vec 0:real^N,&2 * R)) / measure(Z:real^N->bool)`
      REAL_ARCH_SIMPLE) THEN
    DISCH_THEN(X_CHOOSE_TAC `k:num`) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `k + 1`) THEN REWRITE_TAC[ARITH_RULE `1 <= k + 1`] THEN
    UNDISCH_TAC `measure(ball(vec 0:real^N,&2 * R)) / measure(Z:real^N->bool) <= &k` THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ; GSYM REAL_OF_NUM_ADD] THEN
    UNDISCH_TAC `&0 < measure(Z:real^N->bool)` THEN REAL_ARITH_TAC;
    ASM_SIMP_TAC[MEASURABLE_MEASURE_EQ_0]]);;

(* ========================================================================= *)
(* The volume of B(x,r), r <= R: exp_x o E maps D0 cap B(0,r)                *)
(* injectively and the null set (D \ D0) cap B(0,r) to a disjoint null      *)
(* image, so vol B(x,r) = int over D0 cap B(0,r) of sqrt(det G).             *)
(* ========================================================================= *)

let CMPQ_SEG_NULL = prove
 (`!top atlas (g:A->real^N^N) (x:A) (E:real^N^N) R.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ x IN topspace top /\
        mfd_orthonormal_frame g x E /\
        mfd_tball g x R SUBSET mfd_exp_dom (top,atlas) g x
        ==> negligible
             ({w | norm w < R /\
                   mfd_dist (top,atlas) g x (mfd_exp (top,atlas) g x (E ** w)) = norm w} DIFF
              {w | ?s. &1 < s /\ norm(s % w) < R /\
                       mfd_dist (top,atlas) g x (mfd_exp (top,atlas) g x (E ** (s % w))) =
                       norm(s % w)})`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `D = {w | norm w < R /\
                       mfd_dist (top,atlas) (g:A->real^N^N) x
                         (mfd_exp (top,atlas) g x ((E:real^N^N) ** w)) = norm w}` THEN
  SUBGOAL_THEN
   `{w | ?s. &1 < s /\ norm(s % w) < R /\
             mfd_dist (top,atlas) (g:A->real^N^N) x
               (mfd_exp (top,atlas) g x ((E:real^N^N) ** (s % w))) = norm(s % w)} =
    {w:real^N | ?s. &1 < s /\ s % w IN D}`
  SUBST1_TAC THENL
   [EXPAND_TAC "D" THEN REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  MATCH_MP_TAC CMPQ_NULL_ABSTRACT THEN EXISTS_TAC `R:real` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `E:real^N^N`; `R:real`] CMPQ_SEG_MEAS) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `E:real^N^N`; `R:real`] CMPQ_SEG0_MEAS) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `{w | ?s. &1 < s /\ norm(s % w) < R /\
             mfd_dist (top,atlas) (g:A->real^N^N) x
               (mfd_exp (top,atlas) g x ((E:real^N^N) ** (s % w))) = norm(s % w)} =
    {w:real^N | ?s. &1 < s /\ s % w IN D}`
  SUBST1_TAC THENL
   [EXPAND_TAC "D" THEN REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  SIMP_TAC[] THEN DISCH_TAC THEN DISCH_TAC THEN
  EXPAND_TAC "D" THEN REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_BALL_0] THEN SIMP_TAC[]);;

let CMPQ_BALL_VOLUME = prove
 (`!top atlas (g:A->real^N^N) (x:A) (E:real^N^N) R r.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ x IN topspace top /\
        mfd_orthonormal_frame g x E /\
        mfd_tball g x R SUBSET mfd_exp_dom (top,atlas) g x /\ r <= R /\
        (\w. lift(sqrt(det(cmp_expmetric (top,atlas) g x E w)))) integrable_on
        ({w | ?s. &1 < s /\ norm(s % w) < R /\
                  mfd_dist (top,atlas) g x (mfd_exp (top,atlas) g x (E ** (s % w))) =
                  norm(s % w)} INTER ball(vec 0,r))
        ==> mfd_has_volume (top,atlas) g (mfd_ball (top,atlas) g x r)
              (drop(integral
                 ({w | ?s. &1 < s /\ norm(s % w) < R /\
                       mfd_dist (top,atlas) g x (mfd_exp (top,atlas) g x (E ** (s % w))) =
                       norm(s % w)} INTER ball(vec 0,r))
                 (\w. lift(sqrt(det(cmp_expmetric (top,atlas) g x E w))))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `D = {w | norm w < R /\
                       mfd_dist (top,atlas) (g:A->real^N^N) x
                         (mfd_exp (top,atlas) g x ((E:real^N^N) ** w)) = norm w}` THEN
  ABBREV_TAC `D0 = {w | ?s. &1 < s /\ norm(s % w) < R /\
                       mfd_dist (top,atlas) (g:A->real^N^N) x
                         (mfd_exp (top,atlas) g x ((E:real^N^N) ** (s % w))) =
                       norm(s % w)}` THEN
  ABBREV_TAC `Fm = \w. mfd_exp (top,atlas) (g:A->real^N^N) x ((E:real^N^N) ** w)` THEN
  SUBGOAL_THEN `(D0:real^N->bool) SUBSET D` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["D"; "D0"] THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
    X_GEN_TAC `w:real^N` THEN DISCH_THEN(X_CHOOSE_THEN `s:real` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC CMPQ_SEG0_SUB THEN EXISTS_TAC `s:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!w. w IN (D:real^N->bool) ==> (E:real^N^N) ** w IN mfd_exp_dom (top,atlas) (g:A->real^N^N) x`
  ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC CMPQ_FRAME_DOM THEN EXISTS_TAC `R:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!w1 w2. w1 IN (D0:real^N->bool) /\ w2 IN D /\
            mfd_exp (top,atlas) (g:A->real^N^N) x ((E:real^N^N) ** w1) =
            mfd_exp (top,atlas) g x (E ** w2) ==> w1 = w2`
  ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["D"; "D0"] THEN REWRITE_TAC[IN_ELIM_THM] THEN
    MAP_EVERY X_GEN_TAC [`w1:real^N`; `w2:real^N`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `s:real` STRIP_ASSUME_TAC)
      STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC CMPQ_SEG_INJ THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                          `g:A->real^N^N`; `x:A`; `E:real^N^N`; `R:real`; `s:real`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `negligible((D:real^N->bool) DIFF D0)` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["D"; "D0"] THEN MATCH_MP_TAC CMPQ_SEG_NULL THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `lebesgue_measurable(D0:real^N->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "D0" THEN MATCH_MP_TAC CMPQ_SEG0_MEAS THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_ball (top,atlas) (g:A->real^N^N) x r =
    IMAGE (Fm:real^N->A) (D0 INTER ball(vec 0,r)) UNION
    IMAGE Fm ((D DIFF D0) INTER ball(vec 0,r))`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM IMAGE_UNION] THEN
    SUBGOAL_THEN `(D0:real^N->bool) INTER ball(vec 0,r) UNION (D DIFF D0) INTER ball(vec 0,r) =
                  D INTER ball(vec 0,r)` SUBST1_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    MAP_EVERY EXPAND_TAC ["Fm"; "D"] THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC CMPQ_SEG_IMAGE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `E:real^N^N`; `(D0:real^N->bool) INTER ball(vec 0,r)`]
    CMPD_IMAGE_VOLUME) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[LEBESGUE_MEASURABLE_INTER; LEBESGUE_MEASURABLE_BALL; IN_INTER] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `v0:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `E:real^N^N`;
                 `((D:real^N->bool) DIFF D0) INTER ball(vec 0,r)`] CMPD_IMAGE_VOLUME) THEN
  ANTS_TAC THENL
   [SUBGOAL_THEN `negligible(((D:real^N->bool) DIFF D0) INTER ball(vec 0,r))` ASSUME_TAC THENL
     [MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN EXISTS_TAC `(D:real^N->bool) DIFF D0` THEN
      ASM_REWRITE_TAC[INTER_SUBSET];
      ALL_TAC] THEN
    ASM_SIMP_TAC[NEGLIGIBLE_IMP_LEBESGUE_MEASURABLE; INTEGRABLE_ON_NEGLIGIBLE] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `v1:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `v1 = &0` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 <= v /\ v <= &0 ==> v = &0`) THEN CONJ_TAC THENL
     [MATCH_MP_TAC MFD_HAS_VOLUME_POS_LE THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                            `g:A->real^N^N`] THEN
      EXISTS_TAC `IMAGE (\w. mfd_exp (top,atlas) (g:A->real^N^N) x ((E:real^N^N) ** w))
                    (((D:real^N->bool) DIFF D0) INTER ball(vec 0,r))` THEN
      ASM_REWRITE_TAC[];
      FIRST_X_ASSUM(MP_TAC o check (fun th -> is_binary "real_le" (concl th))) THEN
      MATCH_MP_TAC(REAL_ARITH `y = &0 ==> v <= y ==> v <= &0`) THEN
      REWRITE_TAC[GSYM DROP_VEC] THEN AP_TERM_TAC THEN
      MATCH_MP_TAC INTEGRAL_ON_NEGLIGIBLE THEN
      MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN EXISTS_TAC `(D:real^N->bool) DIFF D0` THEN
      ASM_REWRITE_TAC[INTER_SUBSET]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `v0 = drop(integral ((D0:real^N->bool) INTER ball(vec 0,r))
           (\w. lift(sqrt(det(cmp_expmetric (top,atlas) (g:A->real^N^N) x (E:real^N^N) w)))))`
  SUBST_ALL_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_imp(concl th))) THEN
    REWRITE_TAC[IN_INTER] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall(concl th) && length(fst(strip_forall(concl th))) = 2)) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `IMAGE (Fm:real^N->A) (D0 INTER ball(vec 0,r))`;
                 `IMAGE (Fm:real^N->A) ((D DIFF D0) INTER ball(vec 0,r))`;
                 `drop(integral ((D0:real^N->bool) INTER ball(vec 0,r))
                    (\w. lift(sqrt(det(cmp_expmetric (top,atlas) (g:A->real^N^N) x
                                          (E:real^N^N) w)))))`;
                 `&0`] MFD_HAS_VOLUME_UNION) THEN
  REWRITE_TAC[REAL_ADD_RID] THEN DISCH_THEN MATCH_MP_TAC THEN
  EXPAND_TAC "Fm" THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_IMAGE; NOT_IN_EMPTY] THEN
  X_GEN_TAC `y:A` THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `a:real^N` STRIP_ASSUME_TAC)
                             (X_CHOOSE_THEN `b:real^N` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `a:real^N = b` SUBST_ALL_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall(concl th) && length(fst(strip_forall(concl th))) = 2)) THEN
    REPEAT CONJ_TAC THENL [ASM SET_TAC[]; ASM SET_TAC[]; ASM_MESON_TAC[]];
    ASM SET_TAC[]]);;

