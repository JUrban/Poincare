(* ========================================================================= *)
(* Unit pc_cmp_conj (comparison-geometry layer CMP): S3, MT Lemma 1.32 with  *)
(* sec <= K: no conjugate points of x before pi / sqrt K, and exp_x is a     *)
(* local parametrization on the tangent ball of that radius.  Route: the     *)
(* Jacobi matrix along each ray (CMPP_FRAME_ALONG, CMPP_JACOBI_ALONG,        *)
(* CMPJ_FRAME_JSYS) is invertible by the Rauch-type comparison               *)
(* CMPJ_INVERTIBLE, and the pullback metric identity CMPP_RAY_IDENTITY turns *)
(* that into injectivity of d exp_x; MFD_LOCAL_PARAM then gives the local    *)
(* parametrization.                                                          *)
(* ========================================================================= *)

needs "src/pc_cmp_pull.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* Along a ray of an injectivity-type tangent ball, sec <= K on the metric   *)
(* ball bounds the curvature matrix of a parallel frame from above; the      *)
(* Jacobi matrix data of the ray (as in CMPP_RAY_DATA, with the one-sided    *)
(* bound).                                                                   *)
(* ========================================================================= *)

let CMPR_RAY_SEC_UPPER = prove
 (`!top atlas (g:A->real^N^N) (x:A) (E:real^N^N) u rho K (Fr:num->real->real^N).
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ x IN topspace top /\
        mfd_orthonormal_frame g x E /\ norm u = &1 /\
        mfd_tball g x rho SUBSET mfd_exp_dom (top,atlas) g x /\
        (!y e1 e2. y IN mfd_ball (top,atlas) g x rho /\ ~collinear {vec 0,e1,e2}
                   ==> mfd_sectional atlas g y e1 e2 <= K) /\
        cmp_pframe atlas g (mfd_geo (top,atlas) g x (E ** u))
                   (mfd_geo_maxint (top,atlas) g x (E ** u)) Fr /\
        (!t. t IN mfd_geo_maxint (top,atlas) g x (E ** u)
             ==> Fr 1 t = mfd_vel atlas (mfd_geo (top,atlas) g x (E ** u)) t)
        ==> !t v. &0 <= t /\ t < rho /\ v$1 = &0
                  ==> v dot (cmp_rmat atlas g (mfd_geo (top,atlas) g x (E ** u)) Fr t ** v)
                      <= K * (v dot v)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `gamma = mfd_geo (top,atlas) (g:A->real^N^N) x ((E:real^N^N) ** u)` THEN
  ABBREV_TAC `J0 = mfd_geo_maxint (top,atlas) (g:A->real^N^N) x ((E:real^N^N) ** u)` THEN
  ASM_CASES_TAC `v:real^N = vec 0` THEN
  ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_RZERO; DOT_LZERO; DOT_RZERO; REAL_MUL_RZERO;
                  REAL_LE_REFL] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `E:real^N^N`; `u:real^N`; `rho:real`]
    CMPP_RADIAL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `t:real`) THEN
  ASM_REWRITE_TAC[REAL_MUL_RID] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `(gamma:real->A) t IN mfd_ball (top,atlas) (g:A->real^N^N) x rho`
  ASSUME_TAC THENL
   [EXPAND_TAC "gamma" THEN MATCH_MP_TAC CMPP_RAY_IN_BALL THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(gamma:real->A) t IN topspace top` ASSUME_TAC THENL
   [MATCH_MP_TAC GEOL_GEODESIC_IN_TOPSPACE THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                          `J0:real->bool`] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x:A`; `(E:real^N^N) ** u`] MFD_GEO_MAXIMAL) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `J0:real->bool`;
                 `Fr:num->real->real^N`; `v:real^N`; `t:real`] CMPJ_FRAME_SEC) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; STRIP_TAC] THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[DOT_POS_LE] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
    is_forall(concl th) &&
    can (find_term ((=) `mfd_sectional atlas (g:A->real^N^N)`)) (concl th))) THEN
  ASM_REWRITE_TAC[]);;

let CMPR_RAY_DATA_SEC = prove
 (`!top atlas (g:A->real^N^N) (x:A) (E:real^N^N) K rho w.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ x IN topspace top /\
        mfd_orthonormal_frame g x E /\ &0 < rho /\
        mfd_tball g x rho SUBSET mfd_exp_dom (top,atlas) g x /\
        (!y e1 e2. y IN mfd_ball (top,atlas) g x rho /\ ~collinear {vec 0,e1,e2}
                   ==> mfd_sectional atlas g y e1 e2 <= K) /\
        &0 < norm w
        ==> ?P A B R.
              orthogonal_matrix P /\ P ** basis 1 = inv(norm w) % w /\
              cmp_jsys A B R rho /\
              (!t v. &0 <= t /\ t < rho /\ v$1 = &0
                     ==> v dot (R t ** v) <= K * (v dot v)) /\
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
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x:A`; `E:real^N^N`; `u:real^N`; `rho:real`;
                   `K:real`; `Fr:num->real->real^N`] CMPR_RAY_SEC_UPPER) THEN
    ASM_SIMP_TAC[];
    MAP_EVERY X_GEN_TAC [`s:real`; `a:real^N`] THEN STRIP_TAC THEN
    MATCH_MP_TAC CMPP_RAY_IDENTITY THEN EXISTS_TAC `rho:real` THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    MATCH_MP_TAC MFD_EXP_DIFFERENTIAL_JACOBI_RAY THEN
    REWRITE_TAC[ETA_AX] THEN ASM_SIMP_TAC[] THEN
    USE_THEN "rad" (MP_TAC o SPEC `s:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]]]);;

(* ========================================================================= *)
(* Injectivity of d exp_x on the tangent ball of radius pi / sqrt K under    *)
(* sec <= K.                                                                 *)
(* ========================================================================= *)

let CMPR_SN_POS = prove
 (`!K t. &0 < K /\ &0 < t /\ t < pi / sqrt K ==> &0 < cmp_sn K t`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[cmp_sn] THEN
  SUBGOAL_THEN `&0 < sqrt K` ASSUME_TAC THENL [ASM_SIMP_TAC[SQRT_POS_LT]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC SIN_POS_PI THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_MUL];
    UNDISCH_TAC `t < pi / sqrt K` THEN ASM_SIMP_TAC[REAL_LT_RDIV_EQ] THEN REAL_ARITH_TAC]);;

let CMPR_INVERTIBLE_KER = prove
 (`!(M:real^N^N) (y:real^N). invertible M /\ M ** y = vec 0 ==> y = vec 0`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `y:real^N = (matrix_inv (M:real^N^N) ** M) ** y` SUBST1_TAC THENL
   [ASM_SIMP_TAC[MATRIX_INV; MATRIX_VECTOR_MUL_LID]; ALL_TAC] THEN
  ASM_REWRITE_TAC[GSYM MATRIX_VECTOR_MUL_ASSOC; MATRIX_VECTOR_MUL_RZERO]);;

let CMPR_DEXP_INJ = prove
 (`!top atlas (g:A->real^N^N) (x:A) K v h.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ x IN topspace top /\ &0 < K /\
        mfd_tball g x (pi / sqrt K) SUBSET mfd_exp_dom (top,atlas) g x /\
        (!y e1 e2. y IN mfd_ball (top,atlas) g x (pi / sqrt K) /\
                   ~collinear {vec 0,e1,e2}
                   ==> mfd_sectional atlas g y e1 e2 <= K) /\
        v IN mfd_tball g x (pi / sqrt K) /\
        mfd_differential (open_set_atlas (:real^N)) atlas
          (mfd_exp (top,atlas) g x) v h = vec 0
        ==> h = vec 0`,
  REPEAT GEN_TAC THEN ABBREV_TAC `rho = pi / sqrt K` THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < rho` ASSUME_TAC THENL
   [EXPAND_TAC "rho" THEN MATCH_MP_TAC REAL_LT_DIV THEN
    ASM_SIMP_TAC[SQRT_POS_LT; PI_POS];
    ALL_TAC] THEN
  ASM_CASES_TAC `v:real^N = vec 0` THENL
   [UNDISCH_TAC `mfd_differential (open_set_atlas (:real^N)) atlas
                   (mfd_exp (top,atlas) (g:A->real^N^N) (x:A)) v h = vec 0` THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x:A`] MFD_EXP_DIFFERENTIAL_ZERO) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`] GEOJ_ONB) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `E:real^N^N`) THEN
  SUBGOAL_THEN `mfd_orthonormal_frame (g:A->real^N^N) (x:A) E` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[mfd_orthonormal_frame]; ALL_TAC] THEN
  SUBGOAL_THEN `invertible(E:real^N^N)` ASSUME_TAC THENL
   [REWRITE_TAC[INVERTIBLE_LEFT_INVERSE] THEN
    EXISTS_TAC `transp(E:real^N^N) ** (g:A->real^N^N) x` THEN
    ASM_REWRITE_TAC[GSYM MATRIX_MUL_ASSOC];
    ALL_TAC] THEN
  ABBREV_TAC `w = matrix_inv(E:real^N^N) ** v` THEN
  ABBREV_TAC `a = matrix_inv(E:real^N^N) ** h` THEN
  SUBGOAL_THEN `(E:real^N^N) ** w = v /\ E ** a = h` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["w"; "a"] THEN REWRITE_TAC[MATRIX_VECTOR_MUL_ASSOC] THEN
    ASM_SIMP_TAC[MATRIX_INV; MATRIX_VECTOR_MUL_LID];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < norm(w:real^N) /\ norm w < rho` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[NORM_POS_LT] THEN DISCH_TAC THEN
      UNDISCH_TAC `~(v:real^N = vec 0)` THEN
      SUBST1_TAC(SYM(ASSUME `(E:real^N^N) ** w = v`)) THEN
      REWRITE_TAC[ASSUME `w:real^N = vec 0`; MATRIX_VECTOR_MUL_RZERO];
      SUBGOAL_THEN `norm(w:real^N) = mfd_tnorm (g:A->real^N^N) (x:A) v` SUBST1_TAC THENL
       [SUBST1_TAC(SYM(ASSUME `(E:real^N^N) ** w = v`)) THEN
        CONV_TAC SYM_CONV THEN MATCH_MP_TAC CMPP_TNORM_FRAME THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      UNDISCH_TAC `v IN mfd_tball (g:A->real^N^N) (x:A) rho` THEN
      REWRITE_TAC[mfd_tball; IN_ELIM_THM]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `E:real^N^N`; `K:real`; `rho:real`; `w:real^N`]
    CMPR_RAY_DATA_SEC) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `P:real^N^N` (X_CHOOSE_THEN `A:real->real^N^N`
    (X_CHOOSE_THEN `B:real->real^N^N` (X_CHOOSE_THEN `R:real->real^N^N`
      (fun th -> STRIP_ASSUME_TAC th THEN LABEL_TAC "id" (last(CONJUNCTS th))))))) THEN
  MP_TAC(ISPECL [`A:real->real^N^N`; `B:real->real^N^N`; `R:real->real^N^N`;
                 `rho:real`; `K:real`] CMPJ_INVERTIBLE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC CMPR_SN_POS THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `norm(w:real^N)`) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  USE_THEN "id" (MP_TAC o SPECL [`norm(w:real^N)`; `a:real^N`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `norm(w:real^N) % inv(norm w) % w = w` SUBST1_TAC THENL
   [ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_RINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `E:real^N^N`; `w:real^N`; `a:real^N`;
                 `a:real^N`] CMPP_EXPMETRIC_DOT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `mfd_tball (g:A->real^N^N) (x:A) rho SUBSET mfd_exp_dom (top,atlas) g x` THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_RZERO; DOT_LZERO] THEN
  DISCH_THEN(MP_TAC o SYM) THEN
  ASM_SIMP_TAC[REAL_DIV_EQ_0; REAL_POW_EQ_0; REAL_LT_IMP_NZ; ARITH_EQ; DOT_EQ_0] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `transp(P:real^N^N) ** (a:real^N) = vec 0` ASSUME_TAC THENL
   [MATCH_MP_TAC CMPR_INVERTIBLE_KER THEN
    EXISTS_TAC `(A:real->real^N^N) (norm(w:real^N))` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `a:real^N = vec 0` ASSUME_TAC THENL
   [MATCH_MP_TAC CMPR_INVERTIBLE_KER THEN EXISTS_TAC `transp(P:real^N^N)` THEN
    ASM_REWRITE_TAC[INVERTIBLE_LEFT_INVERSE] THEN EXISTS_TAC `P:real^N^N` THEN
    ASM_MESON_TAC[orthogonal_matrix];
    ALL_TAC] THEN
  SUBST1_TAC(SYM(ASSUME `(E:real^N^N) ** a = h`)) THEN
  REWRITE_TAC[ASSUME `a:real^N = vec 0`; MATRIX_VECTOR_MUL_RZERO]);;

(* ========================================================================= *)
(* Exp_x is a local parametrization near each point of the tangent ball of   *)
(* radius pi / sqrt K (MFD_LOCAL_PARAM), and the headline S3.                *)
(* ========================================================================= *)

let CMPR_LOCAL_PARAM = prove
 (`!top atlas (g:A->real^N^N) (x:A) K v.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ x IN topspace top /\ &0 < K /\
        mfd_tball g x (pi / sqrt K) SUBSET mfd_exp_dom (top,atlas) g x /\
        (!y e1 e2. y IN mfd_ball (top,atlas) g x (pi / sqrt K) /\
                   ~collinear {vec 0,e1,e2}
                   ==> mfd_sectional atlas g y e1 e2 <= K) /\
        v IN mfd_tball g x (pi / sqrt K)
        ==> ?U. open U /\ v IN U /\ U SUBSET mfd_tball g x (pi / sqrt K) /\
                mfd_param top atlas U (mfd_exp (top,atlas) g x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `mfd_exp (top,atlas) (g:A->real^N^N) (x:A)`;
                 `mfd_tball (g:A->real^N^N) (x:A) (pi / sqrt K)`; `v:real^N`]
    MFD_LOCAL_PARAM) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x:A`] MFD_EXP_SMOOTH) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC GEOF_TBALL_OPEN THEN MATCH_MP_TAC REAL_LT_DIV THEN
      ASM_SIMP_TAC[SQRT_POS_LT; PI_POS];
      MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY_MONO THEN
      EXISTS_TAC `mfd_exp_dom (top,atlas) (g:A->real^N^N) (x:A)` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC MFD_SMOOTH_MAP_SUBSET THEN
      EXISTS_TAC `mfd_exp_dom (top,atlas) (g:A->real^N^N) (x:A)` THEN
      ASM_REWRITE_TAC[];
      X_GEN_TAC `h:real^N` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `g:A->real^N^N`; `x:A`; `K:real`; `v:real^N`; `h:real^N`]
        CMPR_DEXP_INJ) THEN
      ASM_REWRITE_TAC[]];
    SIMP_TAC[]]);;

let CMP_CONJUGATE_RADIUS = prove
 (`!u n. CMP_CONJUGATE_RADIUS_STATEMENT (u:A->bool) (n:N->bool)`,
  REWRITE_TAC[CMP_CONJUGATE_RADIUS_STATEMENT] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN CONJ_TAC THENL
   [X_GEN_TAC `h:real^N` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x:A`; `K:real`; `v:real^N`; `h:real^N`]
      CMPR_DEXP_INJ) THEN
    ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x:A`; `K:real`; `v:real^N`] CMPR_LOCAL_PARAM) THEN
    ASM_REWRITE_TAC[]]);;

