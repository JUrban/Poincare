(* ========================================================================= *)
(* Unit pc_geo_kh (geodesics layer): the Killing-Hopf theorem in dimension 3 *)
(* for curvature 1, compact case (MT Thm 1.11(2)): KILLING_HOPF_S3_ISOMETRY  *)
(* (the statement constant KILLING_HOPF_S3_STATEMENT of pc_geo_defs),        *)
(* KILLING_HOPF_S3 (diffeomorphic form) and KILLING_HOPF_COMPONENT (for a    *)
(* connected component, as needed by the space-form case of                  *)
(* RFS_LISTED_SC_S3_STATEMENT).  Route: two Cartan maps S^3 minus a point    *)
(* -> M (MFD_CARTAN_CONST1 with SPHERE3_EXP_BALL_PI) agree near a point,     *)
(* hence on S^3 minus two points (MFD_LOCAL_ISOMETRY_RIGID); glued they give *)
(* a local isometry S^3 -> M, which is a local homeomorphism, hence          *)
(* bijective (GEO_LOCAL_HOMEO_SC_BIJECTIVE) and a diffeomorphism             *)
(* (GEO_BIJECTIVE_LOCAL_DIFFEO).                                             *)
(* ========================================================================= *)

needs "src/pc_geo_s3.ml";;
needs "src/pc_geo_cover.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* Local isometries: the differential is isometric                           *)
(* (GEOH_LISOM_DIFF, GEOH_LISOM_TNORM) and nonsingular (GEOH_LISOM_DET);     *)
(* restriction to open subsets (GEOH_LISOM_SUBSET) and gluing                 *)
(* (GEOH_LISOM_LOCAL).                                                        *)
(* ========================================================================= *)

let GEOH_LISOM_POINTS = prove
 (`!top atlas (g:A->real^N^N) top' atlas' (g':B->real^N^N) W f x.
        mfd_local_isometry (top,atlas) g (top',atlas') g' W f /\ x IN W
        ==> x IN topspace top /\ f x IN topspace top'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mfd_local_isometry] THEN STRIP_TAC THEN
  CONJ_TAC THENL [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
  UNDISCH_TAC `continuous_map (subtopology top W,top') (f:A->B)` THEN
  REWRITE_TAC[continuous_map; TOPSPACE_SUBTOPOLOGY; IN_INTER] THEN
  DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]);;

let GEOH_LISOM_DIFF = prove
 (`!top atlas (g:A->real^N^N) top' atlas' (g':B->real^N^N) W f x.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        smooth_manifold_atlas top' atlas' /\ riemannian_metric atlas' g' /\
        mfd_local_isometry (top,atlas) g (top',atlas') g' W f /\ x IN W
        ==> g x = transp(matrix(mfd_differential atlas atlas' f x)) ** g'(f x) **
                  matrix(mfd_differential atlas atlas' f x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                 `g':B->real^N^N`; `W:A->bool`; `f:A->B`; `x:A`] GEOH_LISOM_POINTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`]
    CHART_AT) THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`; `(f:A->B) x`]
    CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`] CMPF_LOCAL_METRIC) THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                 `g':B->real^N^N`; `(f:A->B) x`] CMPF_LOCAL_METRIC) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `chart_inv (chart_at (atlas:((A->bool)#(A->real^N))->bool) x)
              (SND (chart_at atlas x) x) = x`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `chart_at (atlas:((A->bool)#(A->real^N))->bool) x`] MFDM_CHART) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `mfd_local_isometry (top,atlas) (g:A->real^N^N) (top',atlas')
                 (g':B->real^N^N) W (f:A->B)` THEN
  REWRITE_TAC[mfd_local_isometry] THEN
  DISCH_THEN(MP_TAC o SPECL [`chart_at (atlas:((A->bool)#(A->real^N))->bool) x`;
                             `chart_at (atlas':((B->bool)#(B->real^N))->bool) ((f:A->B) x)`;
                             `SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) x) x`] o
             CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
    ASM_REWRITE_TAC[IN_ELIM_THM; IN_INTER];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[mpullback; o_THM] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[mfd_differential] THEN
  SUBGOAL_THEN
   `(\y. SND(chart_at (atlas':((B->bool)#(B->real^N))->bool) ((f:A->B) x))
           (f(chart_inv (chart_at (atlas:((A->bool)#(A->real^N))->bool) x) y))) =
    SND (chart_at atlas' (f x)) o f o chart_inv (chart_at atlas x)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; REWRITE_TAC[]]);;

let GEOH_LISOM_TNORM = prove
 (`!top atlas (g:A->real^N^N) top' atlas' (g':B->real^N^N) W f x v.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        smooth_manifold_atlas top' atlas' /\ riemannian_metric atlas' g' /\
        mfd_local_isometry (top,atlas) g (top',atlas') g' W f /\ x IN W
        ==> mfd_tnorm g' (f x) (mfd_differential atlas atlas' f x v) =
            mfd_tnorm g x v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `linear(mfd_differential (atlas:((A->bool)#(A->real^N))->bool)
                         (atlas':((B->bool)#(B->real^N))->bool) (f:A->B) x)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC GEOI_DIFF_LINEAR THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `top':B topology`; `W:A->bool`] THEN
    ASM_MESON_TAC[mfd_local_isometry];
    ALL_TAC] THEN
  REWRITE_TAC[mfd_tnorm] THEN AP_TERM_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                 `g':B->real^N^N`; `W:A->bool`; `f:A->B`; `x:A`] GEOH_LISOM_DIFF) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[GSYM MATRIX_VECTOR_MUL_ASSOC; DOT_MATRIX_TRANSP_RMUL] THEN
  ASM_SIMP_TAC[MATRIX_WORKS]);;

let GEOH_LISOM_DET = prove
 (`!top atlas (g:A->real^N^N) top' atlas' (g':B->real^N^N) W f x.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        smooth_manifold_atlas top' atlas' /\ riemannian_metric atlas' g' /\
        mfd_local_isometry (top,atlas) g (top',atlas') g' W f /\ x IN W
        ==> ~(det(matrix(mfd_differential atlas atlas' f x)) = &0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM HOMOGENEOUS_LINEAR_EQUATIONS_DET] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real^N` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                 `g':B->real^N^N`; `W:A->bool`; `f:A->B`; `x:A`] GEOH_LISOM_POINTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`] GEOD_G_POS_DEF) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `v:real^N`) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                 `g':B->real^N^N`; `W:A->bool`; `f:A->B`; `x:A`] GEOH_LISOM_DIFF) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[GSYM MATRIX_VECTOR_MUL_ASSOC; DOT_MATRIX_TRANSP_RMUL] THEN
  ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_RZERO; DOT_LZERO; REAL_LT_REFL]);;

let GEOH_LISOM_SUBSET = prove
 (`!top atlas (g:A->real^N^N) top' atlas' (g':B->real^N^N) W V f.
        mfd_local_isometry (top,atlas) g (top',atlas') g' W f /\
        open_in top V /\ V SUBSET W
        ==> mfd_local_isometry (top,atlas) g (top',atlas') g' V f`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mfd_local_isometry] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY_MONO THEN
    EXISTS_TAC `W:A->bool` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC MFD_SMOOTH_MAP_SUBSET THEN
    EXISTS_TAC `W:A->bool` THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC
     `(y:real^N) IN IMAGE (SND (c:(A->bool)#(A->real^N)))
        {x | x IN FST c INTER V /\ (f:A->B) x IN FST (c':(B->bool)#(B->real^N))}` THEN
    MATCH_MP_TAC(SET_RULE `(s:A->bool) SUBSET t
                           ==> (y:real^N) IN IMAGE (h:A->real^N) s ==> y IN IMAGE h t`) THEN
    ASM SET_TAC[]]);;

let GEOH_LISOM_LOCAL = prove
 (`!top atlas (g:A->real^N^N) top' atlas' (g':B->real^N^N) W f.
        smooth_manifold_atlas top atlas /\ smooth_manifold_atlas top' atlas' /\
        open_in top W /\
        (!x. x IN W
             ==> ?U h. open_in top U /\ x IN U /\ U SUBSET W /\
                       mfd_local_isometry (top,atlas) g (top',atlas') g' U h /\
                       (!z. z IN U ==> f z = h z))
        ==> mfd_local_isometry (top,atlas) g (top',atlas') g' W f`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!x. x IN W
        ==> ?U. open_in top U /\ x IN U /\ U SUBSET W /\
                mfd_local_isometry (top,atlas) (g:A->real^N^N) (top',atlas')
                                   (g':B->real^N^N) U (f:A->B)`
  (LABEL_TAC "loc") THENL
   [X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `U:A->bool` (X_CHOOSE_THEN `h:A->B` STRIP_ASSUME_TAC)) THEN
    EXISTS_TAC `U:A->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC GEOI_LISOM_EQ THEN EXISTS_TAC `h:A->B` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `continuous_map (subtopology top W,top') (f:A->B)` ASSUME_TAC THENL
   [MATCH_MP_TAC TOPC_CONTINUOUS_MAP_LOCAL THEN
    REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER] THEN X_GEN_TAC `x:A` THEN STRIP_TAC THEN
    USE_THEN "loc" (MP_TAC o C MATCH_MP (ASSUME `(x:A) IN W`)) THEN
    DISCH_THEN(X_CHOOSE_THEN `U:A->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `U:A->bool` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[OPEN_IN_SUBTOPOLOGY] THEN EXISTS_TAC `U:A->bool` THEN ASM SET_TAC[];
      REWRITE_TAC[SUBTOPOLOGY_SUBTOPOLOGY] THEN
      SUBGOAL_THEN `W INTER U:A->bool = U` SUBST1_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      ASM_MESON_TAC[mfd_local_isometry]];
    ALL_TAC] THEN
  REWRITE_TAC[mfd_local_isometry] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC MFDD_SMOOTH_MAP_LOCAL THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `top':B topology`] THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    USE_THEN "loc" (MP_TAC o C MATCH_MP (ASSUME `(x:A) IN W`)) THEN
    MATCH_MP_TAC MONO_EXISTS THEN SIMP_TAC[mfd_local_isometry];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`c:(A->bool)#(A->real^N)`; `c':(B->bool)#(B->real^N)`; `y:real^N`] THEN
  REWRITE_TAC[IN_IMAGE; IN_ELIM_THM; IN_INTER] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `x:A` STRIP_ASSUME_TAC))) THEN
  USE_THEN "loc" (MP_TAC o C MATCH_MP (ASSUME `(x:A) IN W`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `U:A->bool` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `mfd_local_isometry (top,atlas) (g:A->real^N^N) (top',atlas')
                 (g':B->real^N^N) U (f:A->B)` THEN
  REWRITE_TAC[mfd_local_isometry] THEN
  DISCH_THEN(MATCH_MP_TAC o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
  ASM_REWRITE_TAC[IN_IMAGE; IN_ELIM_THM; IN_INTER] THEN
  EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* A local isometry defined on the whole manifold is a local                 *)
(* homeomorphism (GEOH_LISOM_LOCAL_HOMEO): on a common injectivity ball it    *)
(* is exp_(f x) o d f_x o exp_x^-1 (MFD_LOCAL_ISOMETRY_EXP), and d f_x maps   *)
(* the tangent ball at x onto the one at f x (GEOH_LISOM_TNORM).             *)
(* ========================================================================= *)

let GEOH_INJ_BALL_FACTS = prove
 (`!top atlas (g:A->real^N^N) x r.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ x IN topspace top /\ &0 < r /\
        mfd_inj_ball (top,atlas) g x r
        ==> ?e. open_in top (IMAGE (mfd_exp (top,atlas) g x) (mfd_tball g x r)) /\
                x IN IMAGE (mfd_exp (top,atlas) g x) (mfd_tball g x r) /\
                continuous_map (subtopology euclidean (mfd_tball g x r),top)
                               (mfd_exp (top,atlas) g x) /\
                continuous_map (subtopology top (IMAGE (mfd_exp (top,atlas) g x)
                                                       (mfd_tball g x r)),
                                subtopology euclidean (mfd_tball g x r)) e /\
                (!v. v IN mfd_tball g x r ==> e(mfd_exp (top,atlas) g x v) = v) /\
                (!z. z IN IMAGE (mfd_exp (top,atlas) g x) (mfd_tball g x r)
                     ==> e z IN mfd_tball g x r /\ mfd_exp (top,atlas) g x (e z) = z)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(vec 0:real^N) IN mfd_tball (g:A->real^N^N) x r /\
                mfd_exp (top,atlas) g x (vec 0) = x`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[mfd_tball; IN_ELIM_THM] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x:A`] MFD_EXP_DOM) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x:A`] GEOD_TNORM_BASIC) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `mfd_inj_ball (top,atlas) (g:A->real^N^N) x r` THEN
  REWRITE_TAC[mfd_inj_ball; mfd_param; mfd_diffeo; homeomorphic_maps] THEN
  REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; TOPSPACE_EUCLIDEAN; INTER_UNIV] THEN
  ABBREV_TAC `B = mfd_tball (g:A->real^N^N) x r` THEN
  ABBREV_TAC `E = mfd_exp (top,atlas) (g:A->real^N^N) x` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `e:A->real^N` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `e:A->real^N` THEN
  SUBGOAL_THEN `IMAGE (E:real^N->A) B SUBSET topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[FUN_IN_IMAGE];
    UNDISCH_TAC `continuous_map (subtopology euclidean B,subtopology top (IMAGE E B))
                                (E:real^N->A)` THEN
    SIMP_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY];
    X_GEN_TAC `z:A` THEN DISCH_TAC THEN CONJ_TAC THENL
     [UNDISCH_TAC `continuous_map (subtopology top (IMAGE (E:real^N->A) B),
                                  subtopology euclidean B) (e:A->real^N)` THEN
      REWRITE_TAC[continuous_map; TOPSPACE_SUBTOPOLOGY; TOPSPACE_EUCLIDEAN; INTER_UNIV;
                  IN_INTER] THEN
      DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN ASM SET_TAC[];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]]]);;

let GEOH_LISOM_LOCAL_HOMEO = prove
 (`!top atlas (g:A->real^N^N) top' atlas' (g':B->real^N^N) f x.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\
        hausdorff_space top' /\ smooth_manifold_atlas top' atlas' /\
        riemannian_metric atlas' g' /\
        mfd_local_isometry (top,atlas) g (top',atlas') g' (topspace top) f /\
        x IN topspace top
        ==> ?U V. open_in top U /\ x IN U /\ open_in top' V /\
                  homeomorphic_map (subtopology top U,subtopology top' V) f`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                 `g':B->real^N^N`; `topspace top:A->bool`; `f:A->B`; `x:A`]
    GEOH_LISOM_POINTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  (* a common injectivity radius *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`] MFD_EXP_LOCAL_DIFFEO) THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                 `g':B->real^N^N`; `(f:A->B) x`] MFD_EXP_LOCAL_DIFFEO) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r2:real` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `r1:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `r = min r1 r2` THEN
  SUBGOAL_THEN `&0 < r /\ r <= r1 /\ r <= r2` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "r" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `r:real`] GEOH_INJ_BALL_FACTS) THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                 `g':B->real^N^N`; `(f:A->B) x`; `r:real`] GEOH_INJ_BALL_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `mfd_inj_ball (top,atlas) (g:A->real^N^N) x r /\
                mfd_inj_ball (top',atlas') (g':B->real^N^N) ((f:A->B) x) r`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC MFD_INJ_BALL_MONO THENL
     [EXISTS_TAC `r1:real`; EXISTS_TAC `r2:real`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `B1 = mfd_tball (g:A->real^N^N) x r` THEN
  ABBREV_TAC `B2 = mfd_tball (g':B->real^N^N) ((f:A->B) x) r` THEN
  ABBREV_TAC `E1 = mfd_exp (top,atlas) (g:A->real^N^N) x` THEN
  ABBREV_TAC `E2 = mfd_exp (top',atlas') (g':B->real^N^N) ((f:A->B) x)` THEN
  DISCH_THEN(X_CHOOSE_THEN `e2:B->real^N` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `e1:A->real^N` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`IMAGE (E1:real^N->A) B1`; `IMAGE (E2:real^N->B) B2`] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `IMAGE (E1:real^N->A) B1 SUBSET topspace top /\
                IMAGE (E2:real^N->B) B2 SUBSET topspace top'`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[OPEN_IN_SUBSET]; ALL_TAC] THEN
  (* the differential *)
  ABBREV_TAC `D = mfd_differential (atlas:((A->bool)#(A->real^N))->bool)
                    (atlas':((B->bool)#(B->real^N))->bool) (f:A->B) x` THEN
  SUBGOAL_THEN `linear(D:real^N->real^N)` ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN MATCH_MP_TAC GEOI_DIFF_LINEAR THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `top':B topology`; `topspace top:A->bool`] THEN
    ASM_MESON_TAC[mfd_local_isometry; OPEN_IN_TOPSPACE];
    ALL_TAC] THEN
  SUBGOAL_THEN `!v. mfd_tnorm (g':B->real^N^N) ((f:A->B) x) ((D:real^N->real^N) v) =
                    mfd_tnorm (g:A->real^N^N) x v`
  ASSUME_TAC THENL
   [X_GEN_TAC `v:real^N` THEN EXPAND_TAC "D" THEN MATCH_MP_TAC GEOH_LISOM_TNORM THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `top':B topology`; `topspace top:A->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `invertible(matrix(D:real^N->real^N))` ASSUME_TAC THENL
   [REWRITE_TAC[INVERTIBLE_DET_NZ] THEN EXPAND_TAC "D" THEN
    MATCH_MP_TAC GEOH_LISOM_DET THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `g:A->real^N^N`; `top':B topology`;
                          `g':B->real^N^N`; `topspace top:A->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `Di = \w:real^N. matrix_inv(matrix(D:real^N->real^N)) ** w` THEN
  SUBGOAL_THEN `(!w. (D:real^N->real^N) ((Di:real^N->real^N) w) = w) /\
                (!v. Di (D v) = v) /\ linear Di`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "Di" THEN REWRITE_TAC[MATRIX_VECTOR_MUL_LINEAR] THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[GSYM(MATCH_MP MATRIX_WORKS th)]) THEN
    ASM_SIMP_TAC[MATRIX_VECTOR_MUL_ASSOC; MATRIX_INV; MATRIX_VECTOR_MUL_LID];
    ALL_TAC] THEN
  SUBGOAL_THEN `(!v. v IN B1 ==> (D:real^N->real^N) v IN B2) /\
                (!w. w IN B2 ==> (Di:real^N->real^N) w IN B1)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["B1"; "B2"] THEN REWRITE_TAC[mfd_tball; IN_ELIM_THM] THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `w:real^N` THEN
    SUBGOAL_THEN `mfd_tnorm (g':B->real^N^N) ((f:A->B) x) w =
                  mfd_tnorm (g:A->real^N^N) x ((Di:real^N->real^N) w)`
    SUBST1_TAC THENL [ASM_MESON_TAC[]; REWRITE_TAC[]];
    ALL_TAC] THEN
  (* f commutes with the exponential maps *)
  SUBGOAL_THEN `!v. v IN B1 ==> (f:A->B) ((E1:real^N->A) v) = (E2:real^N->B) (D v)`
  ASSUME_TAC THENL
   [X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `top':B topology`;
                   `atlas':((B->bool)#(B->real^N))->bool`; `g':B->real^N^N`;
                   `topspace top:A->bool`; `f:A->B`; `x:A`; `v:real^N`]
      MFD_LOCAL_ISOMETRY_EXP) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [CONJ_TAC THENL
       [UNDISCH_TAC `mfd_inj_ball (top,atlas) (g:A->real^N^N) x r` THEN
        REWRITE_TAC[mfd_inj_ball] THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
        X_GEN_TAC `t:real` THEN STRIP_TAC THEN
        SUBGOAL_THEN `t % (v:real^N) IN B1` MP_TAC THENL
         [UNDISCH_TAC `(v:real^N) IN B1` THEN EXPAND_TAC "B1" THEN
          REWRITE_TAC[mfd_tball; IN_ELIM_THM] THEN
          MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                         `g:A->real^N^N`; `x:A`] GEOD_TNORM_BASIC) THEN
          ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
          DISCH_TAC THEN MATCH_MP_TAC REAL_LET_TRANS THEN
          EXISTS_TAC `mfd_tnorm (g:A->real^N^N) x v` THEN ASM_REWRITE_TAC[] THEN
          GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
          MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
          ASM SET_TAC[]]];
      SIMP_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[HOMEOMORPHIC_MAP_MAPS] THEN
  EXISTS_TAC `\w. (E1:real^N->A) ((Di:real^N->real^N) ((e2:B->real^N) w))` THEN
  REWRITE_TAC[homeomorphic_maps; TOPSPACE_SUBTOPOLOGY] THEN
  SUBGOAL_THEN `topspace top INTER IMAGE (E1:real^N->A) B1 = IMAGE E1 B1 /\
                topspace top' INTER IMAGE (E2:real^N->B) B2 = IMAGE E2 B2`
  (CONJUNCTS_THEN SUBST1_TAC) THENL [ASM SET_TAC[]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY; TOPSPACE_SUBTOPOLOGY] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY_MONO THEN
      EXISTS_TAC `topspace top:A->bool` THEN
      CONJ_TAC THENL [ASM_MESON_TAC[mfd_local_isometry]; ASM SET_TAC[]];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTER] THEN
      X_GEN_TAC `z:A` THEN STRIP_TAC THEN
      UNDISCH_TAC `(z:A) IN IMAGE (E1:real^N->A) B1` THEN
      REWRITE_TAC[IN_IMAGE] THEN
      DISCH_THEN(X_CHOOSE_THEN `v:real^N` STRIP_ASSUME_TAC) THEN
      ASM_SIMP_TAC[] THEN ASM SET_TAC[]];
    SUBGOAL_THEN `(\w. (E1:real^N->A) ((Di:real^N->real^N) ((e2:B->real^N) w))) =
                  E1 o Di o e2`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
    EXISTS_TAC `subtopology euclidean (B1:real^N->bool)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
      EXISTS_TAC `subtopology euclidean (B2:real^N->bool)` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
      CONJ_TAC THENL
       [REWRITE_TAC[CONTINUOUS_MAP_EUCLIDEAN] THEN MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN
        ASM_REWRITE_TAC[];
        ASM SET_TAC[]];
      ASM_REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY;
                      SUBSET_REFL]];
    REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[];
    REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `w:real^N` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[]]);;

(* ========================================================================= *)
(* Cartan maps from the round S^3 (GEOH_S3_CARTAN): for a                    *)
(* linear isometry L : T_q S^3 -> T_p M, exp_p o L o (exp_q on the tangent   *)
(* ball of radius pi)^-1 is a local isometry on S^3 minus -q.                 *)
(* ========================================================================= *)

let GEOH_S3_CARTAN = prove
 (`!top atlas (g:A->real^3^3) q p L.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ compact_space top /\
        (!x u v. x IN topspace top /\ ~collinear {vec 0,u,v}
                 ==> mfd_sectional atlas g x u v = &1) /\
        q IN sphere(vec 0:real^4,&1) /\ p IN topspace top /\
        transp L ** g p ** L = round3_metric q
        ==> mfd_local_isometry
              (subtopology euclidean (sphere(vec 0,&1)),sphere3_atlas) round3_metric
              (top,atlas) g (sphere(vec 0,&1) DELETE --q)
              (\y. mfd_exp (top,atlas) g p
                     (L ** (@v. v IN mfd_tball round3_metric q pi /\
                                mfd_exp (subtopology euclidean (sphere(vec 0,&1)),
                                         sphere3_atlas) round3_metric q v = y))) /\
            (!v. v IN mfd_tball round3_metric q pi
                 ==> (@w. w IN mfd_tball round3_metric q pi /\
                          mfd_exp (subtopology euclidean (sphere(vec 0,&1)),
                                   sphere3_atlas) round3_metric q w =
                          mfd_exp (subtopology euclidean (sphere(vec 0,&1)),
                                   sphere3_atlas) round3_metric q v) = v)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SPHERE3_EXP_BALL_PI) THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC MFD_CARTAN_CONST1 THEN ASM_REWRITE_TAC[GEOS_S3_BASIC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `g:A->real^3^3`; `p:A`; `vec 0:real^3`] MFD_COMPACT_GEO_COMPLETE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN
    REWRITE_TAC[SUBSET_UNIV] THEN
    UNDISCH_TAC `mfd_inj_ball (subtopology euclidean (sphere(vec 0:real^4,&1)),sphere3_atlas)
                              round3_metric q pi` THEN
    SIMP_TAC[mfd_inj_ball];
    ALL_TAC] THEN
  X_GEN_TAC `v:real^3` THEN DISCH_TAC THEN MATCH_MP_TAC SELECT_UNIQUE THEN
  X_GEN_TAC `w:real^3` THEN REWRITE_TAC[] THEN EQ_TAC THENL
   [STRIP_TAC THEN MATCH_MP_TAC GEOS_EXP_INJ THEN EXISTS_TAC `q:real^4` THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP GEOS_S3_TANGENT) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[mfd_tball; IN_ELIM_THM]) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ASSUME
     `!v. mfd_tnorm round3_metric q v =
          norm(mfd_differential sphere3_atlas (open_set_atlas (:real^4)) (\y. y) q v)`]) THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* The global local isometry S^3 -> M (GEOH_KH_MAIN): the                    *)
(* Cartan maps F0 at (basis 4, p, L) and F1 at (basis 1, F0(basis 1), dF0)    *)
(* agree near basis 1, hence on S^3 minus {-basis 4, -basis 1}, and glue.     *)
(* ========================================================================= *)

let GEOH_BASIS_FACTS = prove
 (`basis 4 IN sphere(vec 0:real^4,&1) /\ basis 1 IN sphere(vec 0:real^4,&1) /\
   (basis 1:real^4) dot basis 4 = &0 /\
   ~((basis 1:real^4) = --(basis 4)) /\ ~(--(basis 4):real^4 = --(basis 1)) /\
   ~((basis 1:real^4) = --(basis 1)) /\
   (basis 1:real^4) dot --(basis 4) = &0`,
  SIMP_TAC[IN_SPHERE_0; NORM_BASIS; DIMINDEX_4; ARITH; DOT_BASIS_BASIS; DOT_RNEG;
           REAL_NEG_0] THEN
  REWRITE_TAC[CART_EQ; DIMINDEX_4; FORALL_4; VECTOR_NEG_COMPONENT] THEN
  SIMP_TAC[BASIS_COMPONENT; DIMINDEX_4; ARITH] THEN REAL_ARITH_TAC);;

let GEOH_S3_ROUND3_ISOMETRY = prove
 (`!top atlas (g:A->real^3^3) p q.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        p IN topspace top /\ q IN sphere(vec 0:real^4,&1)
        ==> ?L:real^3^3. transp L ** g p ** L = round3_metric q`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `p:A`] GEOJ_ONB) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `E:real^3^3`) THEN
  ABBREV_TAC `k = &4 / (&1 + norm(SND(chart_at sphere3_atlas (q:real^4)) q) pow 2) pow 2` THEN
  SUBGOAL_THEN `&0 <= k` ASSUME_TAC THENL
   [EXPAND_TAC "k" THEN MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_POW_LE THEN
    MP_TAC(ISPEC `SND(chart_at sphere3_atlas (q:real^4)) q` LRG_SPH_POS) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `sqrt k %% (E:real^3^3)` THEN
  ASM_REWRITE_TAC[round3_metric; TRANSP_MATRIX_CMUL; MATRIX_MUL_LMUL; MATRIX_MUL_RMUL;
                  MATRIX_CMUL_ASSOC] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  ASM_SIMP_TAC[GSYM REAL_POW_2; SQRT_POW_2]);;

let GEOH_S3_W = prove
 (`open_in (subtopology euclidean (sphere(vec 0:real^4,&1)))
           (sphere(vec 0,&1) DELETE --(basis 4) DELETE --(basis 1)) /\
   connected_in (subtopology euclidean (sphere(vec 0:real^4,&1)))
                (sphere(vec 0,&1) DELETE --(basis 4) DELETE --(basis 1)) /\
   open_in (subtopology euclidean (sphere(vec 0:real^4,&1)))
           (sphere(vec 0,&1) DELETE --(basis 4)) /\
   open_in (subtopology euclidean (sphere(vec 0:real^4,&1)))
           (sphere(vec 0,&1) DELETE --(basis 1))`,
  SUBGOAL_THEN `open_in (subtopology euclidean (sphere(vec 0:real^4,&1)))
                        (sphere(vec 0,&1))` ASSUME_TAC THENL
   [MESON_TAC[OPEN_IN_TOPSPACE; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY]; ALL_TAC] THEN
  ASM_SIMP_TAC[OPEN_IN_DELETE] THEN
  REWRITE_TAC[CONNECTED_IN_SUBTOPOLOGY; CONNECTED_IN_EUCLIDEAN] THEN
  CONJ_TAC THENL [ALL_TAC; SET_TAC[]] THEN
  MP_TAC(ISPECL [`vec 0:real^4`; `--(basis 1):real^4`; `&1`;
                 `sphere(vec 0:real^4,&1) DELETE --(basis 4)`]
    CONNECTED_OPEN_IN_SPHERE_DELETE_EQ) THEN
  ASM_SIMP_TAC[OPEN_IN_DELETE; DIMINDEX_4; ARITH] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[CONNECTED_PUNCTURED_SPHERE; DIMINDEX_4; ARITH]);;

(* Rays from basis 1 of length < pi / 2 stay away from -basis 4. *)

let GEOH_RAY_AVOIDS = prove
 (`!v t. v IN mfd_tball round3_metric (basis 1) (pi / &2) /\ &0 <= t /\ t <= &1
         ==> mfd_exp (subtopology euclidean (sphere(vec 0,&1)),sphere3_atlas)
                     round3_metric (basis 1) (t % v) IN
             sphere(vec 0:real^4,&1) DELETE --(basis 4)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC GEOH_BASIS_FACTS THEN STRIP_TAC THEN
  ASM_SIMP_TAC[IN_DELETE; GEOS_EXP_IN_SPHERE] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`basis 1:real^4`; `t % v:real^3`] GEOS_EXP_DOTQ) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP GEOS_S3_TANGENT o
    check (fun th -> concl th = `basis 1 IN sphere(vec 0:real^4,&1)`)) THEN
  UNDISCH_TAC `v IN mfd_tball round3_metric (basis 1) (pi / &2)` THEN
  ASM_REWRITE_TAC[mfd_tball; IN_ELIM_THM] THEN
  ASM_SIMP_TAC[LINEAR_CMUL; NORM_MUL] THEN DISCH_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `&0 < x ==> ~(&0 = x)`) THEN
  MATCH_MP_TAC COS_POS_PI THEN
  ABBREV_TAC `n = norm(mfd_differential sphere3_atlas (open_set_atlas (:real^4))
                         (\y:real^4. y) (basis 1) v)` THEN
  SUBGOAL_THEN `&0 <= n` ASSUME_TAC THENL
   [EXPAND_TAC "n" THEN REWRITE_TAC[NORM_POS_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `abs t * n <= n` ASSUME_TAC THENL
   [GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`abs t`; `n:real`] REAL_LE_MUL) THEN MP_TAC PI_POS THEN
  REWRITE_TAC[REAL_ABS_POS] THEN ASM_REAL_ARITH_TAC);;

(* ========================================================================= *)
(* GEOH_KH_MAIN, a local isometry from the round S^3 onto any                *)
(* compact 3-manifold of constant curvature 1.                                *)
(* ========================================================================= *)

let GEOH_KH_MAIN = prove
 (`!top atlas (g:A->real^3^3).
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        compact_space top /\ ~(topspace top = {}) /\ riemannian_metric atlas g /\
        (!x u v. x IN topspace top /\ ~collinear {vec 0,u,v}
                 ==> mfd_sectional atlas g x u v = &1)
        ==> ?Fm. mfd_local_isometry
                   (subtopology euclidean (sphere(vec 0:real^4,&1)),sphere3_atlas)
                   round3_metric (top,atlas) g (sphere(vec 0,&1)) Fm`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `p:A` o REWRITE_RULE[GSYM MEMBER_NOT_EMPTY]) THEN
  MP_TAC GEOH_BASIS_FACTS THEN STRIP_TAC THEN
  MP_TAC GEOH_S3_W THEN STRIP_TAC THEN
  MP_TAC GEOS_S3_BASIC THEN STRIP_TAC THEN
  SUBGOAL_THEN `basis 1 IN sphere(vec 0:real^4,&1) DELETE --(basis 4)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[IN_DELETE]; ALL_TAC] THEN
  (* the first Cartan map, at basis 4 *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `p:A`; `basis 4:real^4`] GEOH_S3_ROUND3_ISOMETRY) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `L:real^3^3`) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `basis 4:real^4`; `p:A`; `L:real^3^3`]
    GEOH_S3_CARTAN) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC
   `F0 = \y. mfd_exp (top,atlas) (g:A->real^3^3) p
               ((L:real^3^3) **
                (@v. v IN mfd_tball round3_metric (basis 4) pi /\
                     mfd_exp (subtopology euclidean (sphere(vec 0:real^4,&1)),
                              sphere3_atlas) round3_metric (basis 4) v = y))` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC)) THEN
  (* the second Cartan map, at basis 1, with the differential of F0 *)
  ABBREV_TAC `p1 = (F0:real^4->A) (basis 1)` THEN
  ABBREV_TAC `L1 = matrix(mfd_differential sphere3_atlas
                            (atlas:((A->bool)#(A->real^3))->bool) (F0:real^4->A) (basis 1))` THEN
  SUBGOAL_THEN `(p1:A) IN topspace top` ASSUME_TAC THENL
   [EXPAND_TAC "p1" THEN
    MP_TAC(ISPECL [`subtopology euclidean (sphere(vec 0:real^4,&1))`; `sphere3_atlas`;
                   `round3_metric`; `top:A topology`;
                   `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `sphere(vec 0:real^4,&1) DELETE --(basis 4)`; `F0:real^4->A`;
                   `basis 1:real^4`] GEOH_LISOM_POINTS) THEN
    ASM_REWRITE_TAC[IN_DELETE] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `linear(mfd_differential sphere3_atlas
                        (atlas:((A->bool)#(A->real^3))->bool) (F0:real^4->A) (basis 1))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC GEOI_DIFF_LINEAR THEN
    MAP_EVERY EXISTS_TAC [`subtopology euclidean (sphere(vec 0:real^4,&1))`;
                          `top:A topology`; `sphere(vec 0:real^4,&1) DELETE --(basis 4)`] THEN
    ASM_REWRITE_TAC[IN_DELETE] THEN ASM_MESON_TAC[mfd_local_isometry];
    ALL_TAC] THEN
  SUBGOAL_THEN `transp (L1:real^3^3) ** (g:A->real^3^3) p1 ** L1 = round3_metric (basis 1)`
  ASSUME_TAC THENL
   [EXPAND_TAC "L1" THEN EXPAND_TAC "p1" THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC GEOH_LISOM_DIFF THEN
    MAP_EVERY EXISTS_TAC [`subtopology euclidean (sphere(vec 0:real^4,&1))`;
                          `top:A topology`; `sphere(vec 0:real^4,&1) DELETE --(basis 4)`] THEN
    ASM_REWRITE_TAC[IN_DELETE];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `basis 1:real^4`; `p1:A`; `L1:real^3^3`]
    GEOH_S3_CARTAN) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC
   `F1 = \y. mfd_exp (top,atlas) (g:A->real^3^3) p1
               ((L1:real^3^3) **
                (@v. v IN mfd_tball round3_metric (basis 1) pi /\
                     mfd_exp (subtopology euclidean (sphere(vec 0:real^4,&1)),
                              sphere3_atlas) round3_metric (basis 1) v = y))` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "choice1")) THEN
  (* F0 = F1 near basis 1 *)
  SUBGOAL_THEN
   `!v. v IN mfd_tball round3_metric (basis 1) (pi / &2)
        ==> (F0:real^4->A)
              (mfd_exp (subtopology euclidean (sphere(vec 0:real^4,&1)),sphere3_atlas)
                       round3_metric (basis 1) v) =
            (F1:real^4->A)
              (mfd_exp (subtopology euclidean (sphere(vec 0:real^4,&1)),sphere3_atlas)
                       round3_metric (basis 1) v)`
  ASSUME_TAC THENL
   [X_GEN_TAC `v:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `v IN mfd_tball round3_metric (basis 1) pi` ASSUME_TAC THENL
     [UNDISCH_TAC `v IN mfd_tball round3_metric (basis 1) (pi / &2)` THEN
      REWRITE_TAC[mfd_tball; IN_ELIM_THM] THEN MP_TAC PI_POS THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    EXPAND_TAC "F1" THEN REWRITE_TAC[] THEN
    USE_THEN "choice1" (fun th -> REWRITE_TAC[MATCH_MP th
      (ASSUME `v IN mfd_tball round3_metric (basis 1) pi`)]) THEN
    MP_TAC(ISPECL [`subtopology euclidean (sphere(vec 0:real^4,&1))`; `sphere3_atlas`;
                   `round3_metric`; `top:A topology`;
                   `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `sphere(vec 0:real^4,&1) DELETE --(basis 4)`; `F0:real^4->A`;
                   `basis 1:real^4`; `v:real^3`] MFD_LOCAL_ISOMETRY_EXP) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [CONJ_TAC THENL
       [ASM_SIMP_TAC[SPHERE3_EXP; IN_UNIV];
        REPEAT STRIP_TAC THEN MATCH_MP_TAC GEOH_RAY_AVOIDS THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN AP_TERM_TAC THEN
    EXPAND_TAC "L1" THEN ASM_SIMP_TAC[MATRIX_WORKS];
    ALL_TAC] THEN
  (* the neighbourhood U1 of basis 1 *)
  MP_TAC(ISPECL [`subtopology euclidean (sphere(vec 0:real^4,&1))`; `sphere3_atlas`;
                 `round3_metric`; `basis 1:real^4`; `pi / &2`] GEOH_INJ_BALL_FACTS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    SIMP_TAC[PI_POS; REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
    MATCH_MP_TAC MFD_INJ_BALL_MONO THEN EXISTS_TAC `pi` THEN
    ASM_SIMP_TAC[SPHERE3_EXP_BALL_PI] THEN MP_TAC PI_POS THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `U1 = IMAGE (mfd_exp (subtopology euclidean (sphere(vec 0:real^4,&1)),
                                   sphere3_atlas) round3_metric (basis 1))
                         (mfd_tball round3_metric (basis 1) (pi / &2))` THEN
  DISCH_THEN(X_CHOOSE_THEN `e1:real^4->real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!z. z IN U1 ==> (F0:real^4->A) z = (F1:real^4->A) z` ASSUME_TAC THENL
   [EXPAND_TAC "U1" THEN REWRITE_TAC[FORALL_IN_IMAGE] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  (* rigidity on S^3 minus two points *)
  MP_TAC(ISPECL [`subtopology euclidean (sphere(vec 0:real^4,&1))`; `sphere3_atlas`;
                 `round3_metric`; `top:A topology`;
                 `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `sphere(vec 0:real^4,&1) DELETE --(basis 4) DELETE --(basis 1)`;
                 `F0:real^4->A`; `F1:real^4->A`; `basis 1:real^4`]
    MFD_LOCAL_ISOMETRY_RIGID) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_DELETE] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC GEOH_LISOM_SUBSET THEN
      EXISTS_TAC `sphere(vec 0:real^4,&1) DELETE --(basis 4)` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      MATCH_MP_TAC GEOH_LISOM_SUBSET THEN
      EXISTS_TAC `sphere(vec 0:real^4,&1) DELETE --(basis 1)` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      EXPAND_TAC "p1" THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC GEOI_DIFFERENTIAL_LOCAL THEN
      MAP_EVERY EXISTS_TAC [`subtopology euclidean (sphere(vec 0:real^4,&1))`;
                            `U1:real^4->bool`] THEN
      ASM_REWRITE_TAC[]];
    DISCH_TAC] THEN
  (* gluing *)
  EXISTS_TAC `\x. if x = --(basis 4) then (F1:real^4->A) x else F0 x` THEN
  MATCH_MP_TAC GEOH_LISOM_LOCAL THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MESON_TAC[OPEN_IN_TOPSPACE; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY]; ALL_TAC] THEN
  X_GEN_TAC `x:real^4` THEN DISCH_TAC THEN
  ASM_CASES_TAC `x:real^4 = --(basis 4)` THENL
   [MAP_EVERY EXISTS_TAC [`sphere(vec 0:real^4,&1) DELETE --(basis 1)`; `F1:real^4->A`] THEN
    ASM_REWRITE_TAC[DELETE_SUBSET] THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC[IN_DELETE] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_DELETE] THEN X_GEN_TAC `z:real^4` THEN STRIP_TAC THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_DELETE];
    MAP_EVERY EXISTS_TAC [`sphere(vec 0:real^4,&1) DELETE --(basis 4)`; `F0:real^4->A`] THEN
    ASM_REWRITE_TAC[DELETE_SUBSET; IN_DELETE] THEN
    X_GEN_TAC `z:real^4` THEN STRIP_TAC THEN ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* The Killing-Hopf theorem: KILLING_HOPF_S3_ISOMETRY (the                   *)
(* local isometry of GEOH_KH_MAIN is a local homeomorphism, hence bijective   *)
(* onto the simply connected M and a diffeomorphism, hence an isometry),      *)
(* KILLING_HOPF_S3 and KILLING_HOPF_COMPONENT.                                *)
(* ========================================================================= *)

let KILLING_HOPF_S3_ISOMETRY = prove
 (`KILLING_HOPF_S3_STATEMENT (:A)`,
  REWRITE_TAC[KILLING_HOPF_S3_STATEMENT] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`] GEOH_KH_MAIN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `Fm:real^4->A`) THEN
  MP_TAC GEOS_S3_BASIC THEN STRIP_TAC THEN
  MP_TAC POINCARE_SMOOTH_HYPOTHESES_SPHERE_3 THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(sphere(vec 0:real^4,&1) = {})` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_local_isometry (subtopology euclidean (sphere(vec 0:real^4,&1)),sphere3_atlas)
      round3_metric (top,atlas) (g:A->real^3^3)
      (topspace(subtopology euclidean (sphere(vec 0:real^4,&1)))) (Fm:real^4->A)`
  ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `continuous_map (subtopology euclidean (sphere(vec 0:real^4,&1)),top) (Fm:real^4->A) /\
    mfd_smooth_map sphere3_atlas (atlas:((A->bool)#(A->real^3))->bool)
      (topspace(subtopology euclidean (sphere(vec 0:real^4,&1)))) Fm`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC
     `mfd_local_isometry (subtopology euclidean (sphere(vec 0:real^4,&1)),sphere3_atlas)
        round3_metric (top,atlas) (g:A->real^3^3)
        (topspace(subtopology euclidean (sphere(vec 0:real^4,&1)))) (Fm:real^4->A)` THEN
    REWRITE_TAC[mfd_local_isometry; SUBTOPOLOGY_TOPSPACE] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`subtopology euclidean (sphere(vec 0:real^4,&1))`; `top:A topology`;
                 `Fm:real^4->A`] GEO_LOCAL_HOMEO_SC_BIJECTIVE) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[TOPC_SIMPLY_CONNECTED_IMP_PATH_CONNECTED] THEN
    X_GEN_TAC `x:real^4` THEN DISCH_TAC THEN
    MATCH_MP_TAC(INST_TYPE [`:3`,`:N`] GEOH_LISOM_LOCAL_HOMEO) THEN
    MAP_EVERY EXISTS_TAC [`sphere3_atlas`; `round3_metric`;
                          `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`subtopology euclidean (sphere(vec 0:real^4,&1))`; `sphere3_atlas`;
                 `top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `Fm:real^4->A`] GEO_BIJECTIVE_LOCAL_DIFFEO) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:real^4` THEN DISCH_TAC THEN
    MATCH_MP_TAC GEOH_LISOM_DET THEN
    MAP_EVERY EXISTS_TAC [`subtopology euclidean (sphere(vec 0:real^4,&1))`;
                          `round3_metric`; `top:A topology`; `g:A->real^3^3`;
                          `topspace(subtopology euclidean (sphere(vec 0:real^4,&1)))`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `Fi:A->real^4`) THEN
  MAP_EVERY EXISTS_TAC [`Fm:real^4->A`; `Fi:A->real^4`] THEN
  REWRITE_TAC[mfd_isometry] THEN CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`c:(real^4->bool)#(real^4->real^3)`; `c':(A->bool)#(A->real^3)`] THEN
  STRIP_TAC THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
  UNDISCH_TAC
   `mfd_local_isometry (subtopology euclidean (sphere(vec 0:real^4,&1)),sphere3_atlas)
      round3_metric (top,atlas) (g:A->real^3^3) (sphere(vec 0,&1)) (Fm:real^4->A)` THEN
  REWRITE_TAC[mfd_local_isometry] THEN
  DISCH_THEN(MATCH_MP_TAC o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `FST(c:(real^4->bool)#(real^4->real^3)) SUBSET sphere(vec 0,&1)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`c:(real^4->bool)#(real^4->real^3)`; `vec 0:real^3`]
      RFB_SPHERE3_CHART_FACTS) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC
   `(y:real^3) IN IMAGE (SND (c:(real^4->bool)#(real^4->real^3)))
      {x | x IN FST c /\ (Fm:real^4->A) x IN FST (c':(A->bool)#(A->real^3))}` THEN
  MATCH_MP_TAC(SET_RULE `(s:real^4->bool) = t
                         ==> (y:real^3) IN IMAGE (h:real^4->real^3) s
                             ==> y IN IMAGE h t`) THEN
  ASM SET_TAC[]);;

let KILLING_HOPF_S3 = prove
 (`!top atlas (g:A->real^3^3).
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        compact_space top /\ ~(topspace top = {}) /\ simply_connected_space top /\
        riemannian_metric atlas g /\
        (!x u v. x IN topspace top /\ ~collinear {vec 0,u,v}
                 ==> mfd_sectional atlas g x u v = &1)
        ==> mfd_diffeomorphic top atlas
              (subtopology euclidean (sphere(vec 0:real^4,&1))) sphere3_atlas`,
  REPEAT STRIP_TAC THEN
  MP_TAC KILLING_HOPF_S3_ISOMETRY THEN REWRITE_TAC[KILLING_HOPF_S3_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                             `g:A->real^3^3`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[mfd_isometry; mfd_diffeomorphic] THEN
  DISCH_THEN(X_CHOOSE_THEN `Fm:real^4->A` (X_CHOOSE_THEN `Fi:A->real^4`
    (MP_TAC o MATCH_MP MFD_DIFFEO_SYM o CONJUNCT1))) THEN
  MESON_TAC[]);;

let KILLING_HOPF_COMPONENT = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) U.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        compact_space top /\ U IN connected_components_of top /\
        simply_connected_space (subtopology top U) /\
        smooth_manifold_atlas (subtopology top U) (restrict_atlas atlas U) /\
        (?g. riemannian_metric (restrict_atlas atlas U) g /\
             !x u v. x IN topspace (subtopology top U) /\ ~collinear {vec 0,u,v}
                     ==> mfd_sectional (restrict_atlas atlas U) g x u v = &1)
        ==> mfd_diffeomorphic (subtopology top U) (restrict_atlas atlas U)
              (subtopology euclidean (sphere(vec 0:real^4,&1))) sphere3_atlas`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC KILLING_HOPF_S3 THEN
  EXISTS_TAC `g:A->real^3^3` THEN ASM_SIMP_TAC[HAUSDORFF_SPACE_SUBTOPOLOGY] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC COMPACT_SPACE_SUBTOPOLOGY THEN
    MATCH_MP_TAC CLOSED_IN_COMPACT_SPACE THEN
    ASM_MESON_TAC[CLOSED_IN_CONNECTED_COMPONENTS_OF];
    REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN
    MP_TAC(ISPECL [`top:A topology`; `U:A->bool`] NONEMPTY_CONNECTED_COMPONENTS_OF) THEN
    MP_TAC(ISPECL [`top:A topology`; `U:A->bool`] CONNECTED_COMPONENTS_OF_SUBSET) THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[]]);;

