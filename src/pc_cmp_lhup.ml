(* ========================================================================= *)
(* Unit pc_cmp_lhup (comparison-geometry layer CMP): the upper Hessian bound *)
(* of pc_cmp_hup on a possibly incomplete manifold.  The complete case uses  *)
(* exp_dom = UNIV (Hopf-Rinow); here exp_b is only assumed defined along the *)
(* ray through the point considered (and on the pullback domain), which is   *)
(* what the Jacobi field data along the ray need.  The proofs are those of   *)
(* pc_cmp_pull, pc_cmp_hess and pc_cmp_hup with the ball hypotheses replaced *)
(* by ray hypotheses.  Used for the local Toponogov theorem in convex        *)
(* regions (pc_cmp_ltpg).                                                    *)
(* ========================================================================= *)

needs "src/pc_cmp_hup.ml";;
needs "src/pc_cmp_reg.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* The ray data with a ray hypothesis.  CMPLH_RADIAL replaces                *)
(* CMPP_RADIAL (ball) by MFD_EXP_RADIAL along the ray; CMPLH_RAY_IDENTITY    *)
(* and CMPLH_RAY_DATA_SEC0 are CMPP_RAY_IDENTITY and CMPE_RAY_DATA_SEC0 with *)
(* that replacement.                                                          *)
(* ========================================================================= *)

let CMPLH_RADIAL = prove
 (`!top atlas (g:A->real^N^N) (x:A) (E:real^N^N) u rho.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ x IN topspace top /\
        (!r. &0 <= r /\ r < rho ==> r % (E ** u) IN mfd_exp_dom (top,atlas) g x)
        ==> !s. &0 <= s /\ s < rho
                ==> E ** (s % u) = s % (E ** u) /\
                    s % (E ** u) IN mfd_exp_dom (top,atlas) g x /\
                    s IN mfd_geo_maxint (top,atlas) g x (E ** u) /\
                    mfd_exp (top,atlas) g x (s % (E ** u)) =
                    mfd_geo (top,atlas) g x (E ** u) s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_RMUL] THEN
  SUBGOAL_THEN `s % ((E:real^N^N) ** u) IN mfd_exp_dom (top,atlas) (g:A->real^N^N) x`
  ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `(E:real^N^N) ** u`; `s:real`] MFD_EXP_RADIAL) THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

let CMPLH_RAY_IDENTITY = prove
 (`!top atlas (g:A->real^N^N) (x:A) (E:real^N^N) (P:real^N^N) u
    (Fr:num->real->real^N) (Y:num->real->real^N) rho s a.
        (!j. 1 <= j /\ j <= dimindex(:N)
             ==> mfd_differential (open_set_atlas (:real^N)) atlas
                   (mfd_exp (top,atlas) g x) (s % (E ** u)) (s % Fr j (&0)) = Y j s) /\
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ x IN topspace top /\
        mfd_orthonormal_frame g x E /\ orthogonal_matrix P /\ norm u = &1 /\
        (!r. &0 <= r /\ r < rho ==> r % (E ** u) IN mfd_exp_dom (top,atlas) g x) /\
        cmp_pframe atlas g (mfd_geo (top,atlas) g x (E ** u))
                   (mfd_geo_maxint (top,atlas) g x (E ** u)) Fr /\
        cmp_fmat Fr (&0) = E ** P /\
        &0 < s /\ s < rho
        ==> a dot (cmp_expmetric (top,atlas) g x E (s % u) ** a) =
            ((cmp_fmat (\j. cmp_fcoord g (mfd_geo (top,atlas) g x (E ** u)) Fr (Y j)) s **
              (transp P ** a)) dot
             (cmp_fmat (\j. cmp_fcoord g (mfd_geo (top,atlas) g x (E ** u)) Fr (Y j)) s **
              (transp P ** a))) / s pow 2`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "dexp") STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `gamma = mfd_geo (top,atlas) (g:A->real^N^N) x ((E:real^N^N) ** u)` THEN
  ABBREV_TAC `J0 = mfd_geo_maxint (top,atlas) (g:A->real^N^N) x ((E:real^N^N) ** u)` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `E:real^N^N`; `u:real^N`; `rho:real`]
    CMPLH_RADIAL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `s:real`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `E:real^N^N`; `s % (u:real^N)`; `a:real^N`;
                 `a:real^N`] CMPP_EXPMETRIC_DOT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `linear(mfd_differential (open_set_atlas (:real^N)) atlas
             (mfd_exp (top,atlas) (g:A->real^N^N) x) (s % ((E:real^N^N) ** u)))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x:A`; `s % ((E:real^N^N) ** u)`] CMPP_EXP_DIFF) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC
   `D = mfd_differential (open_set_atlas (:real^N)) atlas
          (mfd_exp (top,atlas) (g:A->real^N^N) x) (s % ((E:real^N^N) ** u))` THEN
  ABBREV_TAC `c:real^N = transp(P:real^N^N) ** a` THEN
  SUBGOAL_THEN
   `(E:real^N^N) ** a =
    vsum(1..dimindex(:N)) (\j. (c:real^N)$j % (Fr:num->real->real^N) j (&0))`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM CMPF_FMAT_MUL] THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "c" THEN REWRITE_TAC[MATRIX_VECTOR_MUL_ASSOC; GSYM MATRIX_MUL_ASSOC] THEN
    UNDISCH_TAC `orthogonal_matrix(P:real^N^N)` THEN
    SIMP_TAC[orthogonal_matrix; MATRIX_MUL_RID];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(D:real^N->real^N) ((E:real^N^N) ** a) =
    inv s % vsum(1..dimindex(:N)) (\j. (c:real^N)$j % (Y:num->real->real^N) j s)`
  SUBST1_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[LINEAR_VSUM_MUL; FINITE_NUMSEG] THEN
    REWRITE_TAC[GSYM VSUM_LMUL] THEN MATCH_MP_TAC VSUM_EQ THEN
    X_GEN_TAC `j:num` THEN REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `(Y:num->real->real^N) j s = s % (D:real^N->real^N) ((Fr:num->real->real^N) j (&0))`
    SUBST1_TAC THENL
     [USE_THEN "dexp" (fun th -> REWRITE_TAC[GSYM(MP (SPEC `j:num` th)
        (CONJ (ASSUME `1 <= j`) (ASSUME `j <= dimindex(:N)`)))]) THEN
      MATCH_MP_TAC LINEAR_CMUL THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[VECTOR_MUL_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    UNDISCH_TAC `&0 < s` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_RMUL; DOT_LMUL; DOT_RMUL] THEN
  MP_TAC(ISPECL [`atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `gamma:real->A`; `J0:real->bool`; `Fr:num->real->real^N`;
                 `\r. vsum(1..dimindex(:N)) (\j. (c:real^N)$j % (Y:num->real->real^N) j r)`;
                 `\r. vsum(1..dimindex(:N)) (\j. (c:real^N)$j % (Y:num->real->real^N) j r)`;
                 `s:real`] CMPF_FCOORD_DOT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN
   `cmp_fcoord (g:A->real^N^N) (gamma:real->A) (Fr:num->real->real^N)
      (\r. vsum(1..dimindex(:N)) (\j. (c:real^N)$j % (Y:num->real->real^N) j r)) s =
    cmp_fmat (\j. cmp_fcoord g gamma Fr (Y j)) s ** c`
  SUBST1_TAC THENL
   [REWRITE_TAC[cmp_fcoord; CMPF_FMAT_MUL; CMPF_MATVEC_VSUM; MATRIX_VECTOR_MUL_RMUL];
    ALL_TAC] THEN
  UNDISCH_TAC `&0 < s` THEN CONV_TAC REAL_FIELD);;

let CMPLH_RAY_DATA_SEC0 = prove
 (`!top atlas (g:A->real^N^N) (x:A) (E:real^N^N) rho w.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ x IN topspace top /\
        mfd_orthonormal_frame g x E /\ &0 < rho /\
        (!r. &0 <= r /\ r < rho
             ==> r % (E ** (inv(norm w) % w)) IN mfd_exp_dom (top,atlas) g x) /\
        (!y u v. y IN topspace top /\ ~collinear {vec 0,u,v}
                 ==> &0 <= mfd_sectional atlas g y u v) /\
        &0 < norm w
        ==> ?P A B R.
              orthogonal_matrix P /\ P ** basis 1 = inv(norm w) % w /\
              cmp_jsys A B R rho /\
              (!t v. &0 <= t /\ t < rho /\ v$1 = &0 ==> &0 <= v dot (R t ** v)) /\
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
    CMPLH_RADIAL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "rad") THEN
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
    MAP_EVERY X_GEN_TAC [`t:real`; `v:real^N`] THEN STRIP_TAC THEN
    USE_THEN "rad" (MP_TAC o SPEC `t:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`;
                   `mfd_geo (top,atlas) (g:A->real^N^N) x ((E:real^N^N) ** u)`;
                   `mfd_geo_maxint (top,atlas) (g:A->real^N^N) x ((E:real^N^N) ** u)`;
                   `Fr:num->real->real^N`; `&0`] CMPJ_FRAME_SEC_LOWER) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MAP_EVERY X_GEN_TAC [`s:real`; `z:real^N`] THEN
      STRIP_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> try fst(dest_const t) = "mfd_sectional" with Failure _ -> false))
          (concl th))) THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC GEOL_GEODESIC_IN_TOPSPACE THEN
      MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                            `mfd_geo_maxint (top,atlas) (g:A->real^N^N) x ((E:real^N^N) ** u)`] THEN
      ASM_REWRITE_TAC[];
      DISCH_THEN(MP_TAC o SPECL [`t:real`; `v:real^N`]) THEN
      ASM_REWRITE_TAC[REAL_MUL_LZERO]];
    MAP_EVERY X_GEN_TAC [`s:real`; `a:real^N`] THEN STRIP_TAC THEN
    MATCH_MP_TAC CMPLH_RAY_IDENTITY THEN EXISTS_TAC `rho:real` THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    MATCH_MP_TAC MFD_EXP_DIFFERENTIAL_JACOBI_RAY THEN
    REWRITE_TAC[ETA_AX] THEN ASM_SIMP_TAC[] THEN
    USE_THEN "rad" (MP_TAC o SPEC `s:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]]]);;

(* ========================================================================= *)
(* The upper Hessian bound of |w| in the exp pullback at w0,                 *)
(* CMPE_RAY_HESS_BOUND with exp_dom = UNIV replaced by: the pullback domain  *)
(* maps into exp_dom, and the ray through w0 lies in exp_dom up to rho >     *)
(* |w0| (CMPE_RAY_HESS_BOUND uses the ray up to |w0| + 1).                   *)
(* ========================================================================= *)

let CMPLH_RAY_HESS_BOUND = prove
 (`!top atlas (g:A->real^N^N) (q:A) (E:real^N^N) t w0 rho.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ q IN topspace top /\
        mfd_orthonormal_frame g q E /\
        (!w. w IN t ==> E ** w IN mfd_exp_dom (top,atlas) g q) /\ norm w0 < rho /\
        (!r. &0 <= r /\ r < rho
             ==> r % (E ** (inv(norm w0) % w0)) IN mfd_exp_dom (top,atlas) g q) /\
        (!y u v. y IN topspace top /\ ~collinear {vec 0,u,v}
                 ==> &0 <= mfd_sectional atlas g y u v) /\
        metric_field t (cmp_expmetric (top,atlas) g q E) /\ w0 IN t /\
        (!w. w IN t ==> ~(w = vec 0)) /\
        (!s h. &0 < s /\ s <= &1 /\
               mfd_differential (open_set_atlas (:real^N)) atlas
                 (mfd_exp (top,atlas) g q) (E ** (s % w0)) h = vec 0
               ==> h = vec 0)
        ==> !a. cmp_lhess (cmp_expmetric (top,atlas) g q E) (\z. norm z) w0 a a <=
                inv(norm w0) *
                (a dot (cmp_expmetric (top,atlas) g q E w0 ** a) -
                 (w0 dot a) pow 2 / norm w0 pow 2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `a:real^N` THEN
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
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `q:A`; `E:real^N^N`; `rho:real`; `w0:real^N`]
    CMPLH_RAY_DATA_SEC0) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`P:real^N^N`; `A:real->real^N^N`; `B:real->real^N^N`;
                       `R:real->real^N^N`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `!s. &0 < s /\ s <= norm(w0:real^N) ==> invertible((A:real->real^N^N) s)`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(E:real^N^N) ** (s % inv(norm(w0:real^N)) % w0) IN
                  mfd_exp_dom (top,atlas) (g:A->real^N^N) q`
    ASSUME_TAC THENL
     [SUBGOAL_THEN `(E:real^N^N) ** (s % inv(norm(w0:real^N)) % w0) =
                    s % (E ** (inv(norm w0) % w0))` SUBST1_TAC THENL
       [REWRITE_TAC[MATRIX_VECTOR_MUL_RMUL]; ALL_TAC] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        is_forall(concl th) && can (find_term ((=) `rho:real`)) (concl th) &&
        can (find_term (fun t -> try fst(dest_const t) = "mfd_exp_dom"
                                 with Failure _ -> false)) (concl th))) THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC CMPH_RAY_INVERTIBLE THEN
    MAP_EVERY EXISTS_TAC
     [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
      `q:A`; `E:real^N^N`; `P:real^N^N`; `s:real`;
      `s % inv(norm(w0:real^N)) % w0`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `b:real^N` THEN
      UNDISCH_TAC
       `!s a. &0 < s /\ s < rho
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
                 `rho:real`; `norm(w0:real^N)`] CMPH_JSYS_INV_NEAR) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[NORM_POS_LE; REAL_LE_REFL]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `eps:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `L' = norm(w0:real^N) + min eps (rho - norm w0) / &2` THEN
  SUBGOAL_THEN `norm(w0:real^N) < L' /\ L' <= rho /\ L' - norm w0 < eps`
  STRIP_ASSUME_TAC THENL [EXPAND_TAC "L'" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!s. &0 < s /\ s < L' ==> invertible((A:real->real^N^N) s)` ASSUME_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    ASM_CASES_TAC `s <= norm(w0:real^N)` THENL
     [ASM_SIMP_TAC[];
      UNDISCH_TAC `!s. abs(s - norm(w0:real^N)) < eps ==> invertible((A:real->real^N^N) s)` THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `cmp_jsys (A:real->real^N^N) B R L'` ASSUME_TAC THENL
   [MATCH_MP_TAC CMPH_JSYS_MONO THEN EXISTS_TAC `rho:real` THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:real^N->bool`; `cmp_expmetric (top,atlas) (g:A->real^N^N) q E`;
                 `w0:real^N`; `P:real^N^N`; `A:real->real^N^N`; `B:real->real^N^N`;
                 `R:real->real^N^N`; `rho:real`; `rho - norm(w0:real^N)`; `a:real^N`]
    CMPE_LHESS_RAY) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_SUB_LT] THEN
    MAP_EVERY X_GEN_TAC [`s:real`; `b:real^N`] THEN STRIP_TAC THEN
    UNDISCH_TAC
     `!s a. &0 < s /\ s < rho
            ==> a dot (cmp_expmetric (top,atlas) (g:A->real^N^N) q E
                         (s % inv(norm w0) % w0) ** a) =
                (((A:real->real^N^N) s ** (transp (P:real^N^N) ** a)) dot
                 (A s ** (transp P ** a))) / s pow 2` THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC (CONJUNCTS_THEN2 SUBST1_TAC SUBST1_TAC)) THEN
  MATCH_MP_TAC CMPE_RAY_HESS_UP THEN EXISTS_TAC `R:real->real^N^N` THEN
  EXISTS_TAC `L':real` THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `rho:real`)) (concl th) &&
    can (find_term (fun t -> try fst(dest_var t) = "R" with Failure _ -> false)) (concl th))) THEN
  ASM_REAL_ARITH_TAC);;

(* ========================================================================= *)
(* CMPH_EXP_CHART_NBHD with exp_dom = UNIV replaced by                       *)
(* E w0 IN exp_dom; the neighbourhood t of w0 then maps into exp_dom.        *)
(* ========================================================================= *)

let CMPLH_EXP_CHART_NBHD = prove
 (`!top atlas (g:A->real^N^N) (q:A) (E:real^N^N) w0 O x.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ q IN topspace top /\
        mfd_orthonormal_frame g q E /\
        E ** w0 IN mfd_exp_dom (top,atlas) g q /\
        (!h. mfd_differential (open_set_atlas (:real^N)) atlas
               (mfd_exp (top,atlas) g q) (E ** w0) h = vec 0 ==> h = vec 0) /\
        open O /\ w0 IN O /\ mfd_exp (top,atlas) g q (E ** w0) = x
        ==> ?t u Fi.
              open t /\ w0 IN t /\ t SUBSET O /\
              (!w. w IN t ==> E ** w IN mfd_exp_dom (top,atlas) g q) /\ open u /\
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
    MATCH_MP_TAC CMPP_EXP_IN_TOPSPACE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `q:A`; `E:real^N^N`; `w0:real^N`] CMPH_EXP_FRAME_DIFFEO) THEN
  ASM_REWRITE_TAC[] THEN
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
    ASM_MESON_TAC[SUBSET];
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
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`g:A->real^N^N`; `q:A`; `E:real^N^N`;
                 `(Fi:real^N->real^N)(SND (c:(A->bool)#(A->real^N)) y)`] CMPP_TNORM_FRAME) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN SIMP_TAC[]);;

(* ========================================================================= *)
(* The pullback data at the base point on an incomplete                      *)
(* manifold (CMPE_PB_SETUP with the ray from b in direction ub defined up    *)
(* to rho > L' instead of completeness).  CMPLH_DEXP_RAY: d exp_x at s u in  *)
(* the radial direction is s times the geodesic velocity, for any s u in    *)
(* exp_dom (the complete case uses the global identity exp(r v) = geo(r)).   *)
(* ========================================================================= *)

let CMPLH_DEXP_RAY = prove
 (`!top atlas (g:A->real^N^N) (x:A) u s.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ x IN topspace top /\
        s % u IN mfd_exp_dom (top,atlas) g x
        ==> mfd_differential (open_set_atlas (:real^N)) atlas
              (mfd_exp (top,atlas) g x) (s % u) (s % u) =
            s % mfd_vel atlas (mfd_geo (top,atlas) g x u) s`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `\r:real. r % (s % (u:real^N))`;
                 `s % (u:real^N)`; `&1`] GEOG_DEXP_CURVE) THEN
  ASM_REWRITE_TAC[VECTOR_MUL_LID] THEN ANTS_TAC THENL
   [REWRITE_TAC[has_vector_derivative] THEN MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN
    MATCH_MP_TAC LINEAR_VMUL_DROP THEN REWRITE_TAC[LINEAR_ID];
    DISCH_THEN(SUBST1_TAC o SYM)] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`] MFD_EXP_DOM) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `mfd_exp_dom (top,atlas) (g:A->real^N^N) x` OPEN_CONTAINS_BALL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `s % (u:real^N)`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!r. abs(r - &1) < e / (norm(s % (u:real^N)) + &1)
                    ==> (r * s) % (u:real^N) IN mfd_exp_dom (top,atlas) (g:A->real^N^N) x`
  ASSUME_TAC THENL
   [X_GEN_TAC `r:real` THEN DISCH_TAC THEN
    UNDISCH_TAC `ball(s % (u:real^N),e) SUBSET mfd_exp_dom (top,atlas) (g:A->real^N^N) x` THEN
    REWRITE_TAC[SUBSET; IN_BALL] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[dist; GSYM VECTOR_MUL_ASSOC;
                VECTOR_ARITH `s % (u:real^N) - r % s % u = (&1 - r) % s % u`] THEN
    ONCE_REWRITE_TAC[NORM_MUL] THEN
    SUBGOAL_THEN `&0 < norm(s % (u:real^N)) + &1` ASSUME_TAC THENL
     [MP_TAC(ISPEC `s % (u:real^N)` NORM_POS_LE) THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `abs(&1 - r) * (norm(s % (u:real^N)) + &1)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN REAL_ARITH_TAC;
      ONCE_REWRITE_TAC[REAL_ABS_SUB] THEN ASM_SIMP_TAC[GSYM REAL_LT_RDIV_EQ]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < e / (norm(s % (u:real^N)) + &1)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `s % (u:real^N)` NORM_POS_LE) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`atlas:((A->bool)#(A->real^N))->bool`;
                 `\r:real. mfd_exp (top,atlas) (g:A->real^N^N) x (r % s % u)`;
                 `\t:real. mfd_geo (top,atlas) (g:A->real^N^N) x u (s * t + &0)`;
                 `&1`; `e / (norm(s % (u:real^N)) + &1)`] GEOM_VEL_LOCAL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `r:real` THEN DISCH_TAC THEN
    REWRITE_TAC[VECTOR_MUL_ASSOC; REAL_ADD_RID] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x:A`; `u:real^N`; `r * s`] MFD_EXP_RADIAL) THEN
    ASM_SIMP_TAC[] THEN DISCH_TAC THEN REWRITE_TAC[REAL_MUL_SYM];
    DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `u:real^N`] MFD_GEO_MAXIMAL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `mfd_geo (top,atlas) (g:A->real^N^N) x u`;
                 `mfd_geo_maxint (top,atlas) (g:A->real^N^N) x u`; `s:real`; `&0`]
    MFD_GEODESIC_AFFINE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `&1` o CONJUNCT2) THEN
  REWRITE_TAC[REAL_MUL_RID; REAL_ADD_RID] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `u:real^N`; `s:real`] MFD_EXP_RADIAL) THEN
  ASM_REWRITE_TAC[] THEN SIMP_TAC[]);;

let CMPLH_PB_SETUP = prove
 (`!top atlas (g:A->real^N^N) (b:A) ub L' (z:A) X rho.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\
        (!y a c. y IN topspace top /\ ~collinear {vec 0,a,c}
                 ==> &0 <= mfd_sectional atlas g y a c) /\
        b IN topspace top /\ mfd_tnorm g b ub = &1 /\ &0 < L' /\ L' < rho /\
        (!r. &0 <= r /\ r < rho ==> r % ub IN mfd_exp_dom (top,atlas) g b) /\
        (!s h. &0 < s /\ s <= L' /\
               mfd_differential (open_set_atlas (:real^N)) atlas
                 (mfd_exp (top,atlas) g b) (s % ub) h = vec 0
               ==> h = vec 0) /\
        mfd_geo (top,atlas) g b ub L' = z
        ==> ?E t w0 V0.
              mfd_orthonormal_frame g b E /\
              (!w. w IN t ==> E ** w IN mfd_exp_dom (top,atlas) g b) /\
              open t /\ metric_field t (cmp_expmetric (top,atlas) g b E) /\ w0 IN t /\
              (!w. w IN t ==> ~(w = vec 0)) /\
              (!a. cmp_lhess (cmp_expmetric (top,atlas) g b E) (\z. norm z) w0 a a <=
                   inv(norm w0) *
                   (a dot (cmp_expmetric (top,atlas) g b E w0 ** a) -
                    (w0 dot a) pow 2 / norm w0 pow 2)) /\
              norm w0 = L' /\ cmp_psi (top,atlas) g b E w0 = z /\
              cmp_dexp (top,atlas) g b E w0 ** V0 = X /\
              V0 dot (cmp_expmetric (top,atlas) g b E w0 ** V0) = X dot (g z ** X) /\
              w0 dot V0 =
              L' * (mfd_vel atlas (mfd_geo (top,atlas) g b ub) L' dot (g z ** X))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `L' % (ub:real^N) IN mfd_exp_dom (top,atlas) (g:A->real^N^N) b`
  ASSUME_TAC THENL [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `b:A`] GEOJ_ONB) THEN
  ASM_REWRITE_TAC[GSYM mfd_orthonormal_frame] THEN
  DISCH_THEN(X_CHOOSE_TAC `E:real^N^N`) THEN EXISTS_TAC `E:real^N^N` THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP CMPQ_FRAME_INVERTIBLE) THEN
  ABBREV_TAC `w0 = L' % (matrix_inv(E:real^N^N) ** (ub:real^N))` THEN
  SUBGOAL_THEN `(E:real^N^N) ** w0 = L' % ub` ASSUME_TAC THENL
   [EXPAND_TAC "w0" THEN REWRITE_TAC[MATRIX_VECTOR_MUL_RMUL; MATRIX_VECTOR_MUL_ASSOC] THEN
    ASM_SIMP_TAC[MATRIX_INV; MATRIX_VECTOR_MUL_LID];
    ALL_TAC] THEN
  SUBGOAL_THEN `(E:real^N^N) ** w0 IN mfd_exp_dom (top,atlas) (g:A->real^N^N) b`
  ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `b:A`] GEOD_TNORM_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `norm(w0:real^N) = L'` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`g:A->real^N^N`; `b:A`; `E:real^N^N`; `w0:real^N`] CMPP_TNORM_FRAME) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    ASM_REWRITE_TAC[REAL_MUL_RID] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_exp (top,atlas) (g:A->real^N^N) b ((E:real^N^N) ** w0) = z`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `b:A`; `ub:real^N`; `L':real`] MFD_EXP_RADIAL) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(z:A) IN topspace top` ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN MATCH_MP_TAC CMPP_EXP_IN_TOPSPACE THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!h. mfd_differential (open_set_atlas (:real^N)) atlas
                      (mfd_exp (top,atlas) (g:A->real^N^N) b) ((E:real^N^N) ** w0) h = vec 0
                    ==> h = vec 0`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `L':real`)) (concl th) &&
      can (find_term (fun t -> try fst(dest_const t) = "mfd_differential"
                               with Failure _ -> false)) (concl th))) THEN
    EXISTS_TAC `L':real` THEN ASM_REWRITE_TAC[REAL_LE_REFL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `b:A`; `E:real^N^N`; `w0:real^N`;
                 `(:real^N) DELETE vec 0`; `z:A`] CMPLH_EXP_CHART_NBHD) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_DELETE; IN_UNIV] THEN SIMP_TAC[OPEN_DELETE; OPEN_UNIV] THEN
    REWRITE_TAC[GSYM NORM_POS_LT] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`t:real^N->bool`; `u:real^N->bool`; `Fi:real^N->real^N`] THEN
  STRIP_TAC THEN EXISTS_TAC `t:real^N->bool` THEN EXISTS_TAC `w0:real^N` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `z:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `b:A`; `E:real^N^N`;
                 `chart_at (atlas:((A->bool)#(A->real^N))->bool) (z:A)`;
                 `t:real^N->bool`; `u:real^N->bool`; `Fi:real^N->real^N`; `&0`;
                 `w0:real^N`] CMPH_CHART_TRANSFER) THEN
  SUBGOAL_THEN
   `!w. w IN t ==> (E:real^N^N) ** w IN mfd_exp_dom (top,atlas) (g:A->real^N^N) b /\
                   mfd_exp (top,atlas) g b (E ** w) IN
                   FST(chart_at (atlas:((A->bool)#(A->real^N))->bool) (z:A))`
  ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!w. w IN t ==> ~(w:real^N = vec 0)` ASSUME_TAC THENL
   [UNDISCH_TAC `t SUBSET (:real^N) DELETE vec 0` THEN
    REWRITE_TAC[SUBSET; IN_DELETE; IN_UNIV] THEN SIMP_TAC[];
    ALL_TAC] THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `!w. w IN t ==> ~(w:real^N = vec 0)` ASSUME_TAC THENL
   [UNDISCH_TAC `t SUBSET (:real^N) DELETE vec 0` THEN
    REWRITE_TAC[SUBSET; IN_DELETE; IN_UNIV] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!a. cmp_lhess (cmp_expmetric (top,atlas) (g:A->real^N^N) b (E:real^N^N)) (\z. norm z)
          w0 a a <=
        inv(norm w0) *
        (a dot (cmp_expmetric (top,atlas) g b E w0 ** a) - (w0 dot a) pow 2 / norm w0 pow 2)`
  (ASSUME_TAC o REWRITE_RULE[ASSUME `norm(w0:real^N) = L'`]) THENL
   [MATCH_MP_TAC CMPLH_RAY_HESS_BOUND THEN
    MAP_EVERY EXISTS_TAC [`t:real^N->bool`; `rho:real`] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(E:real^N^N) ** (inv L' % w0) = ub` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_RMUL; VECTOR_MUL_ASSOC] THEN
      ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`s:real`; `h:real^N`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `L':real`)) (concl th) &&
      can (find_term (fun t -> try fst(dest_const t) = "mfd_differential"
                               with Failure _ -> false)) (concl th))) THEN
    EXISTS_TAC `s * L'` THEN
    UNDISCH_TAC `mfd_differential (open_set_atlas (:real^N)) atlas
                   (mfd_exp (top,atlas) (g:A->real^N^N) b) ((E:real^N^N) ** (s % w0)) h =
                 vec 0` THEN
    ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_RMUL; VECTOR_MUL_ASSOC] THEN
    DISCH_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC(REAL_ARITH `s * L <= &1 * L ==> s * L <= L`) THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[cmp_psi] THEN
  SUBGOAL_THEN `invertible(cmp_dexp (top,atlas) (g:A->real^N^N) b (E:real^N^N) w0)`
  ASSUME_TAC THENL
   [REWRITE_TAC[INVERTIBLE_LEFT_INVERSE; MATRIX_LEFT_INVERTIBLE_KER] THEN
    X_GEN_TAC `h:real^N` THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `b:A`; `E:real^N^N`; `w0:real^N`; `h:real^N`]
      CMPP_DEXP_APPLY) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `(E:real^N^N) ** h = vec 0` MP_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        not(can (find_term ((=) `L':real`)) (concl th)) &&
        can (find_term (fun t -> try fst(dest_const t) = "mfd_differential"
                                 with Failure _ -> false)) (concl th))) THEN
      ASM_REWRITE_TAC[];
      DISCH_THEN(MP_TAC o AP_TERM `\v:real^N. matrix_inv(E:real^N^N) ** v`) THEN
      SIMP_TAC[MATRIX_VECTOR_MUL_ASSOC; MATRIX_INV; ASSUME `invertible(E:real^N^N)`;
               MATRIX_VECTOR_MUL_LID; MATRIX_VECTOR_MUL_RZERO]];
    ALL_TAC] THEN
  EXISTS_TAC `matrix_inv(cmp_dexp (top,atlas) (g:A->real^N^N) b (E:real^N^N) w0) ** X` THEN
  ABBREV_TAC `V0 = matrix_inv(cmp_dexp (top,atlas) (g:A->real^N^N) b (E:real^N^N) w0) ** X` THEN
  SUBGOAL_THEN `cmp_dexp (top,atlas) (g:A->real^N^N) b (E:real^N^N) w0 ** V0 = X`
  ASSUME_TAC THENL
   [EXPAND_TAC "V0" THEN
    SIMP_TAC[MATRIX_VECTOR_MUL_ASSOC; MATRIX_INV; MATRIX_VECTOR_MUL_LID;
             ASSUME `invertible(cmp_dexp (top,atlas) (g:A->real^N^N) b (E:real^N^N) w0)`];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_differential (open_set_atlas (:real^N)) atlas
      (mfd_exp (top,atlas) (g:A->real^N^N) b) ((E:real^N^N) ** w0) (E ** V0) = X`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `b:A`; `E:real^N^N`; `w0:real^N`; `V0:real^N`]
      CMPP_DEXP_APPLY) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(ACCEPT_TAC o SYM);
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `b:A`; `E:real^N^N`; `w0:real^N`; `V0:real^N`;
                   `V0:real^N`] CMPP_EXPMETRIC_DOT) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(w0:real^N) dot V0 =
    w0 dot (cmp_expmetric (top,atlas) (g:A->real^N^N) b (E:real^N^N) w0 ** V0)`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `b:A`; `E:real^N^N`; `w0:real^N`] CMPP_EXPMETRIC_SYM) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `b:A`; `E:real^N^N`; `w0:real^N`] CMPP_EXPMETRIC_GAUSS) THEN
    ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
    GEN_REWRITE_TAC (RAND_CONV o RAND_CONV o LAND_CONV) [SYM(ASSUME
      `transp(cmp_expmetric (top,atlas) (g:A->real^N^N) b (E:real^N^N) w0) =
       cmp_expmetric (top,atlas) g b E w0`)] THEN
    REWRITE_TAC[CMPP_DOT_TRANSP] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `b:A`; `E:real^N^N`; `w0:real^N`; `w0:real^N`;
                 `V0:real^N`] CMPP_EXPMETRIC_DOT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN
   `mfd_differential (open_set_atlas (:real^N)) atlas
      (mfd_exp (top,atlas) (g:A->real^N^N) b) (L' % ub) (L' % ub) =
    L' % mfd_vel atlas (mfd_geo (top,atlas) g b ub) L'`
  SUBST1_TAC THENL
   [MATCH_MP_TAC CMPLH_DEXP_RAY THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[DOT_LMUL]);;

(* ========================================================================= *)
(* CMPE_BARRIER_PB with exp_dom = UNIV replaced by: the                      *)
(* pullback domain t maps into exp_dom, and the image of the pullback      *)
(* geodesic agrees with sigma(t0 + .) only for |s| < e0.                    *)
(* ========================================================================= *)

let CMPLH_BARRIER_PB = prove
 (`!top atlas (g:A->real^N^N) (b:A) (E:real^N^N) t w0 (sigma:real->A) t0 V0 (q:A) delta e0.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ b IN topspace top /\ mfd_orthonormal_frame g b E /\
        (!w. w IN t ==> E ** w IN mfd_exp_dom (top,atlas) g b) /\ open t /\
        metric_field t (cmp_expmetric (top,atlas) g b E) /\ w0 IN t /\
        (!w. w IN t ==> ~(w = vec 0)) /\
        (!a. cmp_lhess (cmp_expmetric (top,atlas) g b E) (\z. norm z) w0 a a <=
             inv(norm w0) *
             (a dot (cmp_expmetric (top,atlas) g b E w0 ** a) -
              (w0 dot a) pow 2 / norm w0 pow 2)) /\
        &0 < e0 /\
        (!s. abs s < e0
             ==> mfd_geo (top,atlas) g (cmp_psi (top,atlas) g b E w0)
                   (cmp_dexp (top,atlas) g b E w0 ** V0) s = sigma(t0 + s)) /\
        V0 dot (cmp_expmetric (top,atlas) g b E w0 ** V0) = &1 /\
        mfd_joinable (top,atlas) q b /\ mfd_dist (top,atlas) g q b = delta /\ &0 < delta
        ==> ?e bf bf' bf2.
              &0 < e /\
              (!s. abs(s - t0) < e ==> (bf has_real_derivative bf'(s)) (atreal s)) /\
              (bf' has_real_derivative bf2) (atreal t0) /\
              bf2 <= &2 * delta / norm w0 /\
              bf t0 = (delta + norm w0) pow 2 - t0 pow 2 /\
              bf' t0 = &2 * (&1 + delta / norm w0) * (w0 dot V0) - &2 * t0 /\
              (!s. abs(s - t0) < e
                   ==> mfd_joinable (top,atlas) q (sigma s) /\
                       mfd_dist (top,atlas) g q (sigma s) pow 2 - s pow 2 <= bf s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `G = cmp_expmetric (top,atlas) (g:A->real^N^N) b (E:real^N^N)` THEN
  MP_TAC(ISPEC `t:real^N->bool` CMPW_PM_BASIC) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `riemannian_metric (open_set_atlas t) (G:real^N->real^N^N)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[RFB_OPEN_SET_RIEMANNIAN]; ALL_TAC] THEN
  MP_TAC(ISPECL [`subtopology euclidean (t:real^N->bool)`; `open_set_atlas (t:real^N->bool)`;
                 `G:real^N->real^N^N`; `w0:real^N`; `V0:real^N`] MFD_GEO_MAXIMAL) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `M = mfd_geo_maxint (subtopology euclidean t,open_set_atlas t)
                    (G:real^N->real^N^N) w0 V0` THEN
  ABBREV_TAC `beta = mfd_geo (subtopology euclidean t,open_set_atlas t)
                       (G:real^N->real^N^N) w0 V0` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `?e. &0 < e /\ e <= e0 /\ !r. abs r < e ==> r IN M` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `real_open (M:real->bool)` THEN REWRITE_TAC[real_open] THEN
    DISCH_THEN(MP_TAC o SPEC `&0`) THEN ASM_REWRITE_TAC[REAL_SUB_RZERO] THEN
    DISCH_THEN(X_CHOOSE_THEN `e1:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `min e1 e0` THEN ASM_REWRITE_TAC[REAL_LT_MIN; REAL_MIN_LE; REAL_LE_REFL] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `e:real` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `b:A`; `E:real^N^N`; `t:real^N->bool`; `w0:real^N`;
                 `V0:real^N`] CMPE_LIFT_GEO) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "lift") THEN
  ABBREV_TAC `c = norm(w0:real^N)` THEN
  SUBGOAL_THEN `&0 < c` ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN REWRITE_TAC[NORM_POS_LT] THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `V = mfd_vel (open_set_atlas t) (beta:real->real^N)` THEN
  MP_TAC(ISPECL [`t:real^N->bool`; `G:real^N->real^N^N`; `beta:real->real^N`;
                 `M:real->bool`] CMPE_GEO_DOT_DERIV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "dd") THEN
  SUBGOAL_THEN `!z. z IN t ==> (G:real^N->real^N^N) z ** z = z` ASSUME_TAC THENL
   [EXPAND_TAC "G" THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC CMPP_EXPMETRIC_GAUSS THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `psi2 = (V0:real^N) dot V0 -
                     (w0:real^N) dot christoffel (G:real^N->real^N^N) w0 V0 V0` THEN
  SUBGOAL_THEN `psi2 <= &1` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`t:real^N->bool`; `G:real^N->real^N^N`; `beta:real->real^N`;
                   `M:real->bool`; `&0`] CMPE_CONCAVE_DERIV) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `\s. (delta pow 2 + delta * c) +
                  (&1 + delta / c) * ((beta:real->real^N)(s - t0) dot beta(s - t0)) -
                  s pow 2` THEN
  EXISTS_TAC `\s. (&1 + delta / c) *
                  (&2 * ((beta:real->real^N)(s - t0) dot (V:real->real^N)(s - t0))) -
                  &2 * s` THEN
  EXISTS_TAC `(&1 + delta / c) * (&2 * psi2) - &2` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    MATCH_MP_TAC CMPE_BF_DERIV THEN
    MP_TAC(ISPECL [`\r. (beta:real->real^N) r dot beta r`;
                   `&2 * ((beta:real->real^N)(s - t0) dot (V:real->real^N)(s - t0))`;
                   `t0:real`; `s:real`] CMPE_SHIFT_DERIV) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    USE_THEN "dd" (MP_TAC o SPEC `s - t0`) THEN
    ANTS_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SIMP_TAC[];
    MATCH_MP_TAC CMPE_BF1_DERIV THEN
    MP_TAC(ISPECL [`\r. (beta:real->real^N) r dot (V:real->real^N) r`; `psi2:real`;
                   `t0:real`; `t0:real`] CMPE_SHIFT_DERIV) THEN
    REWRITE_TAC[REAL_SUB_REFL] THEN DISCH_THEN MATCH_MP_TAC THEN
    USE_THEN "dd" (fun th -> MP_TAC(MATCH_MP (SPEC `&0` th) (ASSUME `&0 IN M`))) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    SUBGOAL_THEN `&0 <= delta / c` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&2 * delta / c = (&1 + delta / c) * (&2 * &1) - &2` SUBST1_TAC THENL
     [REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_TAC THEN MATCH_MP_TAC(REAL_ARITH `x <= y ==> x - &2 <= y - &2`) THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    REWRITE_TAC[REAL_SUB_REFL] THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(w0:real^N) dot w0 = c pow 2` SUBST1_TAC THENL
     [EXPAND_TAC "c" THEN REWRITE_TAC[NORM_POW_2]; ALL_TAC] THEN
    UNDISCH_TAC `&0 < c` THEN CONV_TAC REAL_FIELD;
    REWRITE_TAC[REAL_SUB_REFL] THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `s:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(s - t0) IN M` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(sigma:real->A) s =
                mfd_exp (top,atlas) (g:A->real^N^N) b ((E:real^N^N) ** beta(s - t0))`
  ASSUME_TAC THENL
   [USE_THEN "lift" (fun th -> MP_TAC(MATCH_MP (SPEC `s - t0` th)
      (ASSUME `(s - t0) IN M`))) THEN
    REWRITE_TAC[cmp_psi] THEN DISCH_THEN SUBST1_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `s - t0` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `e0:real`)) (concl th) &&
      can (find_term ((=) `sigma:real->A`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[cmp_psi] THEN DISCH_THEN SUBST1_TAC THEN
    AP_TERM_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(beta:real->real^N)(s - t0) IN t` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`subtopology euclidean (t:real^N->bool)`; `open_set_atlas (t:real^N->bool)`;
                   `G:real^N->real^N^N`; `beta:real->real^N`; `M:real->bool`; `s - t0`]
      GEOL_GEODESIC_IN_TOPSPACE) THEN
    ASM_REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `b:A`; `(E:real^N^N) ** (beta:real->real^N)(s - t0)`]
    CMPH_EXP_DIST_LE) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[CMPP_TNORM_FRAME] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
    lhand(concl th) = `(sigma:real->A) s`)) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `mfd_joinable (top,atlas:((A->bool)#(A->real^N))->bool) (q:A) ((sigma:real->A) s)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_JOINABLE_TRANS THEN EXISTS_TAC `b:A` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `q:A`; `b:A`; `(sigma:real->A) s`] MFD_DIST_TRIANGLE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `q:A`; `(sigma:real->A) s`] MFD_DIST_POS_LE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `x <= a + b ==> x - z <= a + b - z`) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(delta + norm((beta:real->real^N)(s - t0))) pow 2` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM NORM_POW_2] THEN MATCH_MP_TAC CMPE_AMGM THEN
  ASM_REWRITE_TAC[NORM_POS_LE] THEN ASM_REAL_ARITH_TAC);;

(* ========================================================================= *)
(* The shifted base point on an incomplete manifold                          *)
(* (CMPE_BASE with [0,L] in the maximal interval instead of completeness).  *)
(* ========================================================================= *)

let CMPLH_BASE = prove
 (`!top atlas (g:A->real^N^N) (q:A) uq L delta.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\
        q IN topspace top /\ mfd_tnorm g q uq = &1 /\
        real_interval[&0,L] SUBSET mfd_geo_maxint (top,atlas) g q uq /\
        mfd_dist (top,atlas) g q (mfd_geo (top,atlas) g q uq L) = L /\
        &0 < delta /\ delta < L
        ==> mfd_geo (top,atlas) g q uq delta IN topspace top /\
            mfd_joinable (top,atlas) q (mfd_geo (top,atlas) g q uq delta) /\
            mfd_dist (top,atlas) g q (mfd_geo (top,atlas) g q uq delta) = delta /\
            mfd_tnorm g (mfd_geo (top,atlas) g q uq delta)
              (mfd_vel atlas (mfd_geo (top,atlas) g q uq) delta) = &1 /\
            (!t. t + delta IN mfd_geo_maxint (top,atlas) g q uq
                 ==> t IN mfd_geo_maxint (top,atlas) g (mfd_geo (top,atlas) g q uq delta)
                            (mfd_vel atlas (mfd_geo (top,atlas) g q uq) delta) /\
                     mfd_geo (top,atlas) g (mfd_geo (top,atlas) g q uq delta)
                       (mfd_vel atlas (mfd_geo (top,atlas) g q uq) delta) t =
                     mfd_geo (top,atlas) g q uq (t + delta)) /\
            (!s h. &0 < s /\ s <= L - delta /\
                   mfd_differential (open_set_atlas (:real^N)) atlas
                     (mfd_exp (top,atlas) g (mfd_geo (top,atlas) g q uq delta))
                     (s % mfd_vel atlas (mfd_geo (top,atlas) g q uq) delta) h = vec 0
                   ==> h = vec 0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 IN mfd_geo_maxint (top,atlas) (g:A->real^N^N) q uq /\
                delta IN mfd_geo_maxint (top,atlas) g q uq /\
                L IN mfd_geo_maxint (top,atlas) g q uq`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN
    FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
    REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `q:A`; `uq:real^N`; `delta:real`] CMPN_SHIFT_SETUP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `q:A`; `uq:real^N`] MFD_GEO_MAXIMAL) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `gam = mfd_geo (top,atlas) (g:A->real^N^N) q uq` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gam:real->A`;
                 `mfd_geo_maxint (top,atlas) (g:A->real^N^N) q uq`; `&0`; `delta:real`]
    GEOH_GEO_SEG_DIST) THEN
  ASM_REWRITE_TAC[REAL_SUB_RZERO; REAL_MUL_RID] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gam:real->A`;
                 `mfd_geo_maxint (top,atlas) (g:A->real^N^N) q uq`; `delta:real`; `L:real`]
    GEOH_GEO_SEG_DIST) THEN
  ASM_REWRITE_TAC[REAL_MUL_RID] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `q:A`; `(gam:real->A) delta`; `(gam:real->A) L`]
    MFD_DIST_TRIANGLE) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `mfd_joinable (top,atlas:((A->bool)#(A->real^N))->bool) (q:A) ((gam:real->A) delta)`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CMPN_NO_CONJ THEN
  MAP_EVERY EXISTS_TAC
   [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
    `q:A`; `uq:real^N`; `L:real`; `delta:real`; `s:real`] THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* ========================================================================= *)
(* The reversed segment on an incomplete manifold.  For w in                 *)
(* exp_dom(z) with L = |w| > 0 and zeta = geo(z, w/L): exp_z w = zeta(L),    *)
(* and the geodesic from zeta(L) with velocity -zeta'(L) is zeta(L - .) on   *)
(* the set of s with L - s in maxint(z,w/L), which contains [0,L]; its       *)
(* velocity at L is -w/L.  (CMPE_REVERSE with the maximal intervals made     *)
(* explicit.)                                                                *)
(* ========================================================================= *)

let CMPLH_REVERSE = prove
 (`!top atlas (g:A->real^N^N) (z:A) w.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ z IN topspace top /\
        w IN mfd_exp_dom (top,atlas) g z /\ &0 < mfd_tnorm g z w
        ==> mfd_exp (top,atlas) g z w =
            mfd_geo (top,atlas) g z (inv(mfd_tnorm g z w) % w) (mfd_tnorm g z w) /\
            mfd_exp (top,atlas) g z w IN topspace top /\
            real_interval[&0,mfd_tnorm g z w] SUBSET
              mfd_geo_maxint (top,atlas) g z (inv(mfd_tnorm g z w) % w) /\
            mfd_tnorm g (mfd_exp (top,atlas) g z w)
              (--(mfd_vel atlas (mfd_geo (top,atlas) g z (inv(mfd_tnorm g z w) % w))
                              (mfd_tnorm g z w))) = &1 /\
            mfd_geo_maxint (top,atlas) g (mfd_exp (top,atlas) g z w)
              (--(mfd_vel atlas (mfd_geo (top,atlas) g z (inv(mfd_tnorm g z w) % w))
                              (mfd_tnorm g z w))) =
            {s | mfd_tnorm g z w - s IN
                 mfd_geo_maxint (top,atlas) g z (inv(mfd_tnorm g z w) % w)} /\
            (!s. mfd_tnorm g z w - s IN
                 mfd_geo_maxint (top,atlas) g z (inv(mfd_tnorm g z w) % w)
                 ==> mfd_geo (top,atlas) g (mfd_exp (top,atlas) g z w)
                       (--(mfd_vel atlas (mfd_geo (top,atlas) g z (inv(mfd_tnorm g z w) % w))
                                       (mfd_tnorm g z w))) s =
                     mfd_geo (top,atlas) g z (inv(mfd_tnorm g z w) % w)
                       (mfd_tnorm g z w - s)) /\
            mfd_vel atlas
              (mfd_geo (top,atlas) g (mfd_exp (top,atlas) g z w)
                 (--(mfd_vel atlas (mfd_geo (top,atlas) g z (inv(mfd_tnorm g z w) % w))
                                 (mfd_tnorm g z w))))
              (mfd_tnorm g z w) =
            --(inv(mfd_tnorm g z w) % w)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `L = mfd_tnorm (g:A->real^N^N) z w` THEN
  ABBREV_TAC `w' = inv L % (w:real^N)` THEN
  SUBGOAL_THEN `L % (w':real^N) = w` ASSUME_TAC THENL
   [EXPAND_TAC "w'" THEN
    ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_RINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `z:A`] GEOD_TNORM_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `mfd_tnorm (g:A->real^N^N) z w' = &1` ASSUME_TAC THENL
   [EXPAND_TAC "w'" THEN ASM_REWRITE_TAC[REAL_ABS_INV] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < L ==> abs L = L`; REAL_MUL_LINV; REAL_LT_IMP_NZ];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `z:A`] MFD_EXP_DOM) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `zeta = mfd_geo (top,atlas) (g:A->real^N^N) z w'` THEN
  ABBREV_TAC `J = mfd_geo_maxint (top,atlas) (g:A->real^N^N) z w'` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `z:A`; `w':real^N`] MFD_GEO_MAXIMAL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!s. &0 <= s /\ s <= L ==> s IN (J:real->bool)` ASSUME_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `z:A`; `w':real^N`; `s:real`] MFD_EXP_RADIAL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT1) THEN
    SUBGOAL_THEN `s % (w':real^N) = (s * inv L) % w` SUBST1_TAC THENL
     [REWRITE_TAC[SYM(ASSUME `inv L % (w:real^N) = w'`); VECTOR_MUL_ASSOC]; ALL_TAC] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `&1`)) (concl th) &&
      can (find_term (fun t -> try fst(dest_const t) = "mfd_exp_dom"
                               with Failure _ -> false)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE];
      ASM_SIMP_TAC[GSYM real_div; REAL_LE_LDIV_EQ; REAL_MUL_LID]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(L:real) IN J /\ &0 IN (J:real->bool)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `mfd_exp (top,atlas) (g:A->real^N^N) z w = (zeta:real->A) L` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `z:A`; `w':real^N`; `L:real`] MFD_EXP_RADIAL) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(zeta:real->A) L IN topspace top` ASSUME_TAC THENL
   [MATCH_MP_TAC GEOL_GEODESIC_IN_TOPSPACE THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                          `J:real->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `v = mfd_vel (atlas:((A->bool)#(A->real^N))->bool) (zeta:real->A) L` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `z:A`; `w':real^N`; `L:real`] MFD_GEO_SHIFT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `(zeta:real->A) L`; `v:real^N`; `--(&1)`]
    MFD_GEO_RESCALE) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[VECTOR_MUL_LNEG; VECTOR_MUL_LID; REAL_MUL_LNEG; REAL_MUL_LID] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `mfd_geo_maxint (top,atlas) (g:A->real^N^N) ((zeta:real->A) L) (--v) =
                {s | L - s IN J}`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN GEN_TAC THEN
    REWRITE_TAC[real_sub]; ALL_TAC] THEN
  SUBGOAL_THEN `!s. L - s IN J
                    ==> mfd_geo (top,atlas) (g:A->real^N^N) ((zeta:real->A) L) (--v) s =
                        zeta(L - s)`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `--(v:real^N)`)) (concl th))) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[GSYM real_sub]; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `--s:real` o check (fun th -> is_forall(concl th) &&
      not(can (find_term ((=) `--(v:real^N)`)) (concl th)) &&
      can (find_term ((=) `v:real^N`)) (concl th))) THEN
    REWRITE_TAC[GSYM real_sub] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `(zeta:real->A) L`] GEOD_TNORM_BASIC) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ONCE_REWRITE_TAC[VECTOR_ARITH `--(v:real^N) = --(&1) % v`] THEN
    ASM_REWRITE_TAC[REAL_ABS_NEG; REAL_ABS_1; REAL_MUL_LID] THEN
    EXPAND_TAC "v" THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `zeta:real->A`; `J:real->bool`; `L:real`; `&0`]
      MFD_GEODESIC_SPEED) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?d. &0 < d /\ !s. abs(s - L) < d ==> L - s IN (J:real->bool)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `real_open(J:real->bool)` THEN REWRITE_TAC[real_open] THEN
    DISCH_THEN(MP_TAC o SPEC `&0`) THEN ASM_REWRITE_TAC[REAL_SUB_RZERO] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`atlas:((A->bool)#(A->real^N))->bool`;
                 `mfd_geo (top,atlas) (g:A->real^N^N) ((zeta:real->A) L) (--v)`;
                 `\s. (zeta:real->A)(--(&1) * s + L)`; `L:real`; `d:real`] GEOM_VEL_LOCAL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    SUBGOAL_THEN `L - s IN (J:real->bool)` ASSUME_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `zeta:real->A`; `J:real->bool`; `--(&1)`; `L:real`]
    MFD_GEODESIC_AFFINE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `L:real` o CONJUNCT2) THEN
  REWRITE_TAC[REAL_ARITH `--(&1) * L + L = &0`] THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM; real_sub] THEN
  VECTOR_ARITH_TAC);;

(* ========================================================================= *)
(* The Calabi barrier on a possibly incomplete manifold with                 *)
(* sec >= 0 (CMPE_BARRIER without completeness).  For a unit-speed geodesic *)
(* sigma = geo(p,u), t0 in its maximal interval, z = sigma(t0) and w in      *)
(* exp_dom(z) with q = exp_z(w), d(z,q) = |w|_g = L, and 0 < delta < L: a    *)
(* smooth upper barrier bf of d(q,sigma s)^2 - s^2 near t0, equal at t0,     *)
(* with bf''(t0) <= 2 delta / (L - delta) and bf'(t0) = -2 <w,sigma'(t0)> -   *)
(* 2 t0.  The ray from b used by CMPLH_PB_SETUP extends past z because the   *)
(* maximal interval of the segment from z is open.                          *)
(* ========================================================================= *)

let CMPLH_OPEN_LEFT = prove
 (`!J L. real_open J /\ &0 <= L /\ (!s. &0 <= s /\ s <= L ==> s IN J)
         ==> ?eps. &0 < eps /\ !x. --eps < x /\ x <= L ==> x IN J`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 IN (J:real->bool)` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `real_open (J:real->bool)` THEN REWRITE_TAC[real_open] THEN
  DISCH_THEN(MP_TAC o SPEC `&0`) THEN ASM_REWRITE_TAC[REAL_SUB_RZERO] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `eps:real` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:real` THEN STRIP_TAC THEN
  ASM_CASES_TAC `&0 <= x` THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `L:real`)) (concl th))) THEN ASM_REWRITE_TAC[];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC]);;

let CMPLH_BARRIER = prove
 (`!top atlas (g:A->real^N^N) (p:A) u t0 (z:A) w (q:A) delta.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\
        (!y a c. y IN topspace top /\ ~collinear {vec 0,a,c}
                 ==> &0 <= mfd_sectional atlas g y a c) /\
        p IN topspace top /\ mfd_tnorm g p u = &1 /\
        t0 IN mfd_geo_maxint (top,atlas) g p u /\
        mfd_geo (top,atlas) g p u t0 = z /\
        w IN mfd_exp_dom (top,atlas) g z /\ mfd_exp (top,atlas) g z w = q /\
        mfd_dist (top,atlas) g z q = mfd_tnorm g z w /\
        &0 < delta /\ delta < mfd_tnorm g z w
        ==> ?e bf bf' bf2.
              &0 < e /\
              (!s. abs(s - t0) < e ==> (bf has_real_derivative bf'(s)) (atreal s)) /\
              (bf' has_real_derivative bf2) (atreal t0) /\
              bf2 <= &2 * delta / (mfd_tnorm g z w - delta) /\
              bf t0 = mfd_tnorm g z w pow 2 - t0 pow 2 /\
              bf' t0 = --(&2 * (w dot (g z ** mfd_vel atlas (mfd_geo (top,atlas) g p u) t0))) -
                       &2 * t0 /\
              (!s. abs(s - t0) < e
                   ==> mfd_joinable (top,atlas) q (mfd_geo (top,atlas) g p u s) /\
                       mfd_dist (top,atlas) g q (mfd_geo (top,atlas) g p u s) pow 2 - s pow 2
                       <= bf s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `p:A`; `u:real^N`] MFD_GEO_MAXIMAL) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `sigma = mfd_geo (top,atlas) (g:A->real^N^N) p u` THEN
  ABBREV_TAC `Mp = mfd_geo_maxint (top,atlas) (g:A->real^N^N) p u` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `(z:A) IN topspace top` ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      rand(concl th) = `z:A`)) THEN
    MATCH_MP_TAC GEOL_GEODESIC_IN_TOPSPACE THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                          `Mp:real->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `L = mfd_tnorm (g:A->real^N^N) z w` THEN
  SUBGOAL_THEN `&0 < L` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `z:A`; `w:real^N`] CMPLH_REVERSE) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `zeta = mfd_geo (top,atlas) (g:A->real^N^N) z (inv L % w)` THEN
  ABBREV_TAC `Jz = mfd_geo_maxint (top,atlas) (g:A->real^N^N) z (inv L % w)` THEN
  ABBREV_TAC `uq = --(mfd_vel (atlas:((A->bool)#(A->real^N))->bool) (zeta:real->A) L)` THEN
  STRIP_TAC THEN
  UNDISCH_THEN `(q:A) = (zeta:real->A) L` (K ALL_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `z:A`; `inv L % (w:real^N)`] MFD_GEO_MAXIMAL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!s. &0 <= s /\ s <= L ==> s IN (Jz:real->bool)` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    UNDISCH_TAC `real_interval[&0,L] SUBSET (Jz:real->bool)` THEN
    REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `real_interval[&0,L] SUBSET mfd_geo_maxint (top,atlas) (g:A->real^N^N) q uq`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[SUBSET; IN_REAL_INTERVAL; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `Jz:real->bool`)) (concl th) &&
      can (find_term ((=) `L:real`)) (concl th))) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_geo (top,atlas) (g:A->real^N^N) q uq L = z` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `L:real` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `uq:real^N`)) (concl th) &&
      can (find_term (fun t -> try fst(dest_const t) = "mfd_geo"
                               with Failure _ -> false)) (concl th))) THEN
    ASM_REWRITE_TAC[REAL_SUB_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_dist (top,atlas) (g:A->real^N^N) q (mfd_geo (top,atlas) g q uq L) = L`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `q:A`; `z:A`] MFD_DIST_SYM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `q:A`; `uq:real^N`; `L:real`; `delta:real`] CMPLH_BASE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `b = mfd_geo (top,atlas) (g:A->real^N^N) q uq delta` THEN
  ABBREV_TAC `ub = mfd_vel (atlas:((A->bool)#(A->real^N))->bool)
                     (mfd_geo (top,atlas) (g:A->real^N^N) q uq) delta` THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`Jz:real->bool`; `L:real`] CMPLH_OPEN_LEFT) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `eps:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!r. &0 <= r /\ r < (L - delta) + eps
                    ==> r IN mfd_geo_maxint (top,atlas) (g:A->real^N^N) b ub /\
                        mfd_geo (top,atlas) g b ub r = mfd_geo (top,atlas) g q uq (r + delta)`
  ASSUME_TAC THENL
   [X_GEN_TAC `r:real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `ub:real^N`)) (concl th) &&
      can (find_term ((=) `delta:real`)) (concl th) &&
      not(can (find_term (fun t -> try fst(dest_const t) = "mfd_differential"
                                   with Failure _ -> false)) (concl th)))) THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `eps:real`)) (concl th))) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_geo (top,atlas) (g:A->real^N^N) b ub (L - delta) = z` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `L - delta` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `eps:real`)) (concl th) &&
      can (find_term ((=) `ub:real^N`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[REAL_SUB_ADD] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `b:A`; `ub:real^N`; `L - delta`; `z:A`;
                 `mfd_vel (atlas:((A->bool)#(A->real^N))->bool) (sigma:real->A) t0`;
                 `(L - delta) + eps`] CMPLH_PB_SETUP) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
      X_GEN_TAC `r:real` THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `g:A->real^N^N`; `b:A`; `ub:real^N`; `r:real`] MFD_EXP_RADIAL) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `r:real` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `eps:real`)) (concl th) &&
        can (find_term ((=) `ub:real^N`)) (concl th))) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]]];
    ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`E:real^N^N`; `t:real^N->bool`; `w0:real^N`; `V0:real^N`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `mfd_vel (atlas:((A->bool)#(A->real^N))->bool) (sigma:real->A) t0 dot
    ((g:A->real^N^N) z ** mfd_vel atlas sigma t0) = &1`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `z:A`] GEOD_TNORM_BASIC) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC
      `mfd_vel (atlas:((A->bool)#(A->real^N))->bool) (sigma:real->A) t0` o
      CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `sigma:real->A`; `Mp:real->bool`; `t0:real`; `&0`]
      MFD_GEODESIC_SPEED) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `?e0. &0 < e0 /\ !s. abs s < e0 ==> t0 + s IN (Mp:real->bool)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `real_open(Mp:real->bool)` THEN REWRITE_TAC[real_open] THEN
    DISCH_THEN(MP_TAC o SPEC `t0:real`) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `e0:real` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `b:A`; `E:real^N^N`; `t:real^N->bool`; `w0:real^N`;
                 `sigma:real->A`; `t0:real`; `V0:real^N`; `q:A`; `delta:real`; `e0:real`]
    CMPLH_BARRIER_PB) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `p:A`; `u:real^N`; `t0:real`] MFD_GEO_SHIFT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `s:real` o CONJUNCT2) THEN
    ANTS_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`e:real`; `bf:real->real`; `bf':real->real`; `bf2:real`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `mfd_vel (atlas:((A->bool)#(A->real^N))->bool)
      (mfd_geo (top,atlas) (g:A->real^N^N) b ub) (L - delta) = --(inv L % w)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`atlas:((A->bool)#(A->real^N))->bool`;
                   `mfd_geo (top,atlas) (g:A->real^N^N) b ub`;
                   `\s. mfd_geo (top,atlas) (g:A->real^N^N) q uq (&1 * s + delta)`;
                   `L - delta`; `min eps (L - delta)`] GEOM_VEL_LOCAL) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[REAL_MUL_LID; REAL_LT_MIN] THEN
      TRY(CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
      X_GEN_TAC `s:real` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `eps:real`)) (concl th) &&
        can (find_term ((=) `ub:real^N`)) (concl th))) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      DISCH_THEN SUBST1_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `q:A`; `uq:real^N`] MFD_GEO_MAXIMAL) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `mfd_geo (top,atlas) (g:A->real^N^N) q uq`;
                   `mfd_geo_maxint (top,atlas) (g:A->real^N^N) q uq`;
                   `&1`; `delta:real`] MFD_GEODESIC_AFFINE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `L - delta` o CONJUNCT2) THEN
    REWRITE_TAC[REAL_MUL_LID; REAL_SUB_ADD; VECTOR_MUL_LID] THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[IN_ELIM_THM; REAL_SUB_REFL];
      DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`e:real`; `bf:real->real`; `bf':real->real`; `bf2:real`] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    UNDISCH_TAC `bf2 <= &2 * delta / norm(w0:real^N)` THEN ASM_REWRITE_TAC[];
    UNDISCH_TAC `(bf:real->real) t0 = (delta + norm(w0:real^N)) pow 2 - t0 pow 2` THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[REAL_ARITH `delta + (L - delta) = L`];
    UNDISCH_TAC `(bf':real->real) t0 =
                 &2 * (&1 + delta / norm(w0:real^N)) * (w0 dot V0) - &2 * t0` THEN
    ASM_REWRITE_TAC[DOT_LNEG; DOT_LMUL] THEN DISCH_THEN SUBST1_TAC THEN
    SUBGOAL_THEN `~(L - delta = &0) /\ ~(L = &0)` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD];
    ASM_REWRITE_TAC[]]);;

