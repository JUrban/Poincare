(* ========================================================================= *)
(* Unit pc_geo_conj (geodesics layer): conjugate points.  d(exp_x) is        *)
(* singular at v iff 0 and 1 are conjugate along the geodesic of v           *)
(* (MFD_EXP_SINGULAR_CONJUGATE, from MFD_EXP_DIFFERENTIAL_JACOBI_RAY and     *)
(* MFD_JACOBI_EXISTS_UNIQUE); flat space has no conjugate points along lines *)
(* (MFD_NOT_CONJUGATE_EUCLIDEAN).                                            *)
(* ========================================================================= *)

needs "src/pc_geo_jvar.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* MFD_EXP_SINGULAR_CONJUGATE.                                               *)
(* ========================================================================= *)

(* Jacobi fields with zero initial data vanish. *)

let GEOCJ_JACOBI_ZERO_DATA = prove
 (`!top atlas (g:A->real^N^N) (gamma:real->A) J t0 Y.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        mfd_geodesic (top,atlas) g gamma J /\ t0 IN J /\
        mfd_jacobi atlas g gamma J Y /\ Y t0 = vec 0 /\
        mfd_covd atlas g gamma Y t0 = vec 0
        ==> !t. t IN J ==> Y t = vec 0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `J:real->bool`] CMPG_GEODESIC_C1) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `real_open (J:real->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[mfd_geodesic]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `J:real->bool`; `t0:real`;
                 `vec 0:real^N`; `vec 0:real^N`] MFD_JACOBI_EXISTS_UNIQUE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `Y0:real->real^N` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "uniq"))))) THEN
  SUBGOAL_THEN `mfd_jacobi atlas (g:A->real^N^N) (gamma:real->A) J (\t. vec 0:real^N)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `gamma:real->A`; `J:real->bool`;
                   `Y:real->real^N`; `Y:real->real^N`; `&0`; `&0`] MFD_JACOBI_LINEAR) THEN
    ASM_REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_LID];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_covd atlas (g:A->real^N^N) (gamma:real->A) (\t. vec 0:real^N) t0 =
                vec 0`
  ASSUME_TAC THENL
   [MATCH_MP_TAC GEOJ_COVD_ZERO THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `J:real->bool`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `t:real` THEN DISCH_TAC THEN
  USE_THEN "uniq" (MP_TAC o SPEC `Y:real->real^N`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(MP_TAC o SPEC `t:real`)] THEN
  USE_THEN "uniq" (MP_TAC o SPEC `\t:real. vec 0:real^N`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(MP_TAC o SPEC `t:real`)] THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

let MFD_EXP_SINGULAR_CONJUGATE = prove
 (`!top atlas (g:A->real^N^N) (x:A) v.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ x IN topspace top /\
        v IN mfd_exp_dom (top,atlas) g x
        ==> ((?w. ~(w = vec 0) /\
                  mfd_differential (open_set_atlas (:real^N)) atlas
                    (mfd_exp (top,atlas) g x) v w = vec 0) <=>
             mfd_conjugate atlas g (mfd_geo (top,atlas) g x v)
                           (mfd_geo_maxint (top,atlas) g x v) (&0) (&1))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `v:real^N`] MFD_GEO_MAXIMAL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&1 IN mfd_geo_maxint (top,atlas) (g:A->real^N^N) x v` ASSUME_TAC THENL
   [UNDISCH_TAC `v IN mfd_exp_dom (top,atlas) (g:A->real^N^N) x` THEN
    REWRITE_TAC[mfd_exp_dom; IN_ELIM_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!Y. mfd_jacobi atlas (g:A->real^N^N) (mfd_geo (top,atlas) g x v)
          (mfd_geo_maxint (top,atlas) g x v) Y /\ Y(&0) = vec 0
        ==> mfd_differential (open_set_atlas (:real^N)) atlas
              (mfd_exp (top,atlas) g x) v
              (mfd_covd atlas g (mfd_geo (top,atlas) g x v) Y (&0)) = Y(&1)`
  (LABEL_TAC "dexp") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x:A`; `v:real^N`;
                   `mfd_covd atlas (g:A->real^N^N) (mfd_geo (top,atlas) g x v) Y (&0)`;
                   `Y:real->real^N`; `&1`] MFD_EXP_DIFFERENTIAL_JACOBI_RAY) THEN
    ASM_REWRITE_TAC[VECTOR_MUL_LID];
    ALL_TAC] THEN
  ABBREV_TAC `gamma = mfd_geo (top,atlas) (g:A->real^N^N) x v` THEN
  ABBREV_TAC `J = mfd_geo_maxint (top,atlas) (g:A->real^N^N) x v` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `J:real->bool`] CMPG_GEODESIC_C1) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REWRITE_TAC[mfd_conjugate] THEN ASM_REWRITE_TAC[REAL_ARITH `~(&0 = &1)`] THEN
  EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `gamma:real->A`; `J:real->bool`; `&0`;
                   `vec 0:real^N`; `w:real^N`] MFD_JACOBI_EXISTS_UNIQUE) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `Y:real->real^N` (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC))))) THEN
    EXISTS_TAC `Y:real->real^N` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [USE_THEN "dexp" (MP_TAC o SPEC `Y:real->real^N`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN MESON_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[TAUT `p /\ ~q <=> ~(p ==> q)`; GSYM NOT_FORALL_THM] THEN
    DISCH_TAC THEN UNDISCH_TAC `~(w:real^N = vec 0)` THEN REWRITE_TAC[] THEN
    UNDISCH_TAC `mfd_covd atlas (g:A->real^N^N) (gamma:real->A) Y (&0) = w` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC CMPV_COVD_VANISHING THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `J:real->bool`; `Y:real->real^N`] THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[mfd_jacobi];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Y:real->real^N` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `mfd_covd atlas (g:A->real^N^N) (gamma:real->A) Y (&0)` THEN
  CONJ_TAC THENL
   [DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `gamma:real->A`; `J:real->bool`; `&0`;
                   `Y:real->real^N`] GEOCJ_JACOBI_ZERO_DATA) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    USE_THEN "dexp" (MP_TAC o SPEC `Y:real->real^N`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]]]);;

(* ========================================================================= *)
(* MFD_NOT_CONJUGATE_EUCLIDEAN.  In real^N with the identity                 *)
(* metric the covariant derivative along any curve is the ordinary          *)
(* derivative and the curvature vanishes, so t -> (t - a) c is a Jacobi     *)
(* field; by uniqueness every Jacobi field vanishing at a is of this form.   *)
(* ========================================================================= *)

let GEOCJ_EUCLID_FIELD_REP = prove
 (`!(gamma:real->real^N) (Y:real->real^N) s.
        mfd_field_rep (open_set_atlas (:real^N)) gamma Y ((:real^N),(\x. x)) s = Y s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mfd_field_rep; GEOL_EUCLID_FACTS] THEN
  MP_TAC(ISPECL [`euclidean:(real^N)topology`; `open_set_atlas (:real^N)`;
                 `(:real^N)`; `\x:real^N. x`; `(gamma:real->real^N) s`] CHART_JAC_SELF) THEN
  REWRITE_TAC[GEOL_EUCLID_FACTS] THEN REWRITE_TAC[open_set_atlas; IN_SING; IN_UNIV] THEN
  SIMP_TAC[]);;

let GEOCJ_EUCLID_METRIC_LOCAL = prove
 (`metric_local (open_set_atlas (:real^N)) ((:real^N),(\x:real^N. x)) (\x. mat 1) =
   (\y. mat 1)`,
  REWRITE_TAC[FUN_EQ_THM; GEOL_EUCLID_FACTS]);;

let GEOCJ_EUCLID_COVD = prove
 (`!(gamma:real->real^N) (Y:real->real^N) t Y'.
        ((\s. Y(drop s)) has_vector_derivative Y') (at (lift t))
        ==> mfd_covd (open_set_atlas (:real^N)) (\x. mat 1) gamma Y t = Y'`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[mfd_covd; GEOL_EUCLID_FACTS; GEOCJ_EUCLID_METRIC_LOCAL;
              GEOL_CHRISTOFFEL_CONST; VECTOR_ADD_RID; GEOCJ_EUCLID_FIELD_REP] THEN
  MATCH_MP_TAC VECTOR_DERIVATIVE_AT THEN ASM_REWRITE_TAC[]);;

let GEOCJ_EUCLID_FIELD_DIFF = prove
 (`!(gamma:real->real^N) (Y:real->real^N) J.
        (!t. t IN J ==> (\s. Y(drop s)) differentiable at (lift t))
        ==> mfd_field_diff (open_set_atlas (:real^N)) gamma Y J`,
  REWRITE_TAC[mfd_field_diff; GEOL_EUCLID_FACTS; GEOCJ_EUCLID_FIELD_REP]);;

let GEOCJ_EUCLID_RIEMANN = prove
 (`!(x:real^N) u v w. mfd_riemann (open_set_atlas (:real^N)) (\x. mat 1) x u v w = vec 0`,
  REWRITE_TAC[mfd_riemann; GEOL_EUCLID_FACTS; GEOCJ_EUCLID_METRIC_LOCAL; LRIEMANN_FLAT]);;

let GEOCJ_AFFINE_VDERIV = prove
 (`!a (c:real^N) t. ((\s. (drop s - a) % c) has_vector_derivative c) (at (lift t))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[has_vector_derivative] THEN
  SUBGOAL_THEN `(\s:real^1. (drop s - a) % (c:real^N)) = (\s. drop s % c - a % c)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM] THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`\s:real^1. drop s % (c:real^N)`; `\s:real^1. drop s % (c:real^N)`;
                 `(\s. a % c):real^1->real^N`; `(\h. vec 0):real^1->real^N`;
                 `at (lift t)`] HAS_DERIVATIVE_SUB) THEN
  REWRITE_TAC[HAS_DERIVATIVE_CONST; VECTOR_SUB_RZERO] THEN
  DISCH_THEN MATCH_MP_TAC THEN MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN
  REWRITE_TAC[GEOL_LINEAR_DROP_VMUL]);;

let GEOCJ_EUCLID_AFFINE_JACOBI = prove
 (`!(gamma:real->real^N) a c.
        mfd_jacobi (open_set_atlas (:real^N)) (\x. mat 1) gamma (:real)
                   (\t. (t - a) % c)`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN
   `mfd_covd (open_set_atlas (:real^N)) (\x. mat 1) (gamma:real->real^N)
             (\t. (t - a) % c) = (\t. c)`
  ASSUME_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `t:real` THEN
    MATCH_MP_TAC GEOCJ_EUCLID_COVD THEN REWRITE_TAC[GEOCJ_AFFINE_VDERIV];
    ALL_TAC] THEN
  REWRITE_TAC[mfd_jacobi; GEOCJ_EUCLID_RIEMANN; VECTOR_ADD_RID] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC GEOCJ_EUCLID_FIELD_DIFF THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_IMP_DIFFERENTIABLE THEN
    EXISTS_TAC `c:real^N` THEN REWRITE_TAC[GEOCJ_AFFINE_VDERIV];
    MATCH_MP_TAC GEOCJ_EUCLID_FIELD_DIFF THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_IMP_DIFFERENTIABLE THEN
    EXISTS_TAC `vec 0:real^N` THEN REWRITE_TAC[HAS_VECTOR_DERIVATIVE_CONST];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC GEOCJ_EUCLID_COVD THEN
    REWRITE_TAC[HAS_VECTOR_DERIVATIVE_CONST]]);;

let MFD_NOT_CONJUGATE_EUCLIDEAN = prove
 (`!(p:real^N) w a b.
        ~mfd_conjugate (open_set_atlas (:real^N)) (\x. mat 1) (\t. p + t % w)
                       (:real) a b`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mfd_conjugate; IN_UNIV] THEN STRIP_TAC THEN
  ABBREV_TAC `c = mfd_covd (open_set_atlas (:real^N)) (\x. mat 1)
                    (\t. (p:real^N) + t % w) Y a` THEN
  MP_TAC(ISPECL [`euclidean:(real^N)topology`; `open_set_atlas (:real^N)`;
                 `(\x. mat 1):real^N->real^N^N`; `\t. (p:real^N) + t % w`; `(:real)`;
                 `a:real`; `vec 0:real^N`; `c:real^N`] MFD_JACOBI_EXISTS_UNIQUE) THEN
  REWRITE_TAC[GEOL_EUCLID_FACTS; GEOL_EUCLID_LINE; IN_UNIV] THEN
  DISCH_THEN(X_CHOOSE_THEN `Y0:real->real^N` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "uniq"))))) THEN
  SUBGOAL_THEN `!s. (Y:real->real^N) s = (s - a) % c` ASSUME_TAC THENL
   [X_GEN_TAC `s:real` THEN
    USE_THEN "uniq" (MP_TAC o SPEC `Y:real->real^N`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(MP_TAC o SPEC `s:real`)] THEN
    USE_THEN "uniq" (MP_TAC o SPEC `\t. (t - a) % (c:real^N)`) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[GEOCJ_EUCLID_AFFINE_JACOBI; REAL_SUB_REFL; VECTOR_MUL_LZERO] THEN
      MATCH_MP_TAC GEOCJ_EUCLID_COVD THEN REWRITE_TAC[GEOCJ_AFFINE_VDERIV];
      DISCH_THEN(MP_TAC o SPEC `s:real`)] THEN
    REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `c:real^N = vec 0` ASSUME_TAC THENL
   [UNDISCH_TAC `(Y:real->real^N) b = vec 0` THEN ASM_REWRITE_TAC[VECTOR_MUL_EQ_0] THEN
    UNDISCH_TAC `~(a:real = b)` THEN MESON_TAC[REAL_SUB_0];
    ALL_TAC] THEN
  UNDISCH_TAC `~((Y:real->real^N) t = vec 0)` THEN
  ASM_REWRITE_TAC[VECTOR_MUL_RZERO]);;

