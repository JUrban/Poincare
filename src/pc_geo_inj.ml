(* ========================================================================= *)
(* Unit pc_geo_inj (geodesics layer): injectivity radius.  Injectivity balls *)
(* are closed under increasing unions (MFD_INJ_BALL_SUP).                    *)
(* ========================================================================= *)

needs "src/pc_geo_s3.ml";;
needs "src/pc_geo_hr.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* MFD_INJ_BALL_SUP.  A parametrization is open, continuous,                 *)
(* smooth, injective, with injective differential (GEOJR_PARAM_FACTS); these *)
(* properties are local, so they pass to the union of the balls of radius    *)
(* s < r, which is a parametrization by GEOS_INJECTIVE_PARAM.                 *)
(* ========================================================================= *)

let GEOJR_PARAM_FACTS = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (e:real^N->A) W.
        smooth_manifold_atlas top atlas /\ mfd_param top atlas W e
        ==> open W /\
            continuous_map (subtopology euclidean W,top) e /\
            mfd_smooth_map (open_set_atlas (:real^N)) atlas W e /\
            (!v w. v IN W /\ w IN W /\ e v = e w ==> v = w) /\
            (!v h. v IN W /\
                   mfd_differential (open_set_atlas (:real^N)) atlas e v h = vec 0
                   ==> h = vec 0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `mfd_param top (atlas:((A->bool)#(A->real^N))->bool) W (e:real^N->A)` THEN
  REWRITE_TAC[mfd_param] THEN DISCH_THEN(X_CHOOSE_TAC `e':A->real^N`) THEN
  MP_TAC(ASSUME `mfd_diffeo euclidean (open_set_atlas (:real^N)) W top
                   (atlas:((A->bool)#(A->real^N))->bool) (IMAGE (e:real^N->A) W) e e'`) THEN
  REWRITE_TAC[mfd_diffeo; homeomorphic_maps] THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM OPEN_IN; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY]) THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `continuous_map (subtopology euclidean W,subtopology top (IMAGE e W))
                                (e:real^N->A)` THEN
    SIMP_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY];
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `linear(mfd_differential (open_set_atlas (:real^N))
                         (atlas:((A->bool)#(A->real^N))->bool) (e:real^N->A) v)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC GEOI_DIFF_LINEAR THEN
    MAP_EVERY EXISTS_TAC [`euclidean:(real^N)topology`; `top:A topology`;
                          `W:real^N->bool`] THEN
    ASM_REWRITE_TAC[GEOI_EUCLIDEAN_ATLAS; GSYM OPEN_IN] THEN
    UNDISCH_TAC `continuous_map (subtopology euclidean W,subtopology top (IMAGE e W))
                                (e:real^N->A)` THEN
    SIMP_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `e:real^N->A`; `e':A->real^N`; `W:real^N->bool`; `v:real^N`]
    GEOI_PARAM_DIFF_SURJ) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPEC `mfd_differential (open_set_atlas (:real^N))
                  (atlas:((A->bool)#(A->real^N))->bool) (e:real^N->A) v`
    LINEAR_SURJECTIVE_IMP_INJECTIVE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPECL [`h:real^N`; `vec 0:real^N`]) THEN
  ASM_MESON_TAC[LINEAR_0]);;

let MFD_INJ_BALL_SUP = prove
 (`!top atlas (g:A->real^N^N) (x:A) r.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\
        (!s. s < r ==> mfd_inj_ball (top,atlas) g x s)
        ==> mfd_inj_ball (top,atlas) g x r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!v. v IN mfd_tball (g:A->real^N^N) x r ==> ?s. s < r /\ v IN mfd_tball g x s`
  ASSUME_TAC THENL
   [REWRITE_TAC[mfd_tball; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    EXISTS_TAC `(mfd_tnorm (g:A->real^N^N) x v + r) / &2` THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s t. s <= t ==> mfd_tball (g:A->real^N^N) x s SUBSET mfd_tball g x t`
  ASSUME_TAC THENL
   [REWRITE_TAC[mfd_tball; SUBSET; IN_ELIM_THM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. s < r
        ==> mfd_tball (g:A->real^N^N) x s SUBSET mfd_exp_dom (top,atlas) g x /\
            open(mfd_tball g x s) /\
            continuous_map (subtopology euclidean (mfd_tball g x s),top)
                           (mfd_exp (top,atlas) g x) /\
            mfd_smooth_map (open_set_atlas (:real^N)) atlas (mfd_tball g x s)
                           (mfd_exp (top,atlas) g x) /\
            (!v w. v IN mfd_tball g x s /\ w IN mfd_tball g x s /\
                   mfd_exp (top,atlas) g x v = mfd_exp (top,atlas) g x w ==> v = w) /\
            (!v h. v IN mfd_tball g x s /\
                   mfd_differential (open_set_atlas (:real^N)) atlas
                     (mfd_exp (top,atlas) g x) v h = vec 0
                   ==> h = vec 0)`
  (LABEL_TAC "ball") THENL
   [X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME `s < r`)) THEN
    REWRITE_TAC[mfd_inj_ball] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC GEOJR_PARAM_FACTS THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[mfd_inj_ball] THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET] THEN X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN
    FIRST_ASSUM(fun th -> MP_TAC(MATCH_MP th
      (ASSUME `(v:real^N) IN mfd_tball (g:A->real^N^N) x r`))) THEN
    DISCH_THEN(X_CHOOSE_THEN `s:real` STRIP_ASSUME_TAC) THEN
    USE_THEN "ball" (MP_TAC o C MATCH_MP (ASSUME `s < r`)) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC GEOS_INJECTIVE_PARAM THEN ASM_REWRITE_TAC[GEOI_TBALL_OPEN] THEN
  SUBGOAL_THEN
   `continuous_map (subtopology euclidean (mfd_tball (g:A->real^N^N) x r),top)
                   (mfd_exp (top,atlas) g x)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC TOPC_CONTINUOUS_MAP_LOCAL THEN
    REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN
    FIRST_ASSUM(fun th -> MP_TAC(MATCH_MP th
      (ASSUME `(v:real^N) IN mfd_tball (g:A->real^N^N) x r`))) THEN
    DISCH_THEN(X_CHOOSE_THEN `s:real` STRIP_ASSUME_TAC) THEN
    USE_THEN "ball" (MP_TAC o C MATCH_MP (ASSUME `s < r`)) THEN STRIP_TAC THEN
    EXISTS_TAC `mfd_tball (g:A->real^N^N) x s` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `mfd_tball (g:A->real^N^N) x s SUBSET mfd_tball g x r` ASSUME_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[OPEN_IN_SUBTOPOLOGY] THEN
      EXISTS_TAC `mfd_tball (g:A->real^N^N) x s` THEN
      ASM_REWRITE_TAC[GSYM OPEN_IN] THEN ASM SET_TAC[];
      REWRITE_TAC[SUBTOPOLOGY_SUBTOPOLOGY] THEN
      SUBGOAL_THEN `mfd_tball (g:A->real^N^N) x r INTER mfd_tball g x s = mfd_tball g x s`
      SUBST1_TAC THENL [ASM SET_TAC[]; ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MP_TAC(ISPEC `(:real^N)` OPEN_SET_ATLAS) THEN
    REWRITE_TAC[OPEN_UNIV; SUBTOPOLOGY_UNIV] THEN DISCH_TAC THEN
    MATCH_MP_TAC MFDD_SMOOTH_MAP_LOCAL THEN
    MAP_EVERY EXISTS_TAC [`euclidean:(real^N)topology`; `top:A topology`] THEN
    ASM_REWRITE_TAC[GSYM OPEN_IN; GEOI_TBALL_OPEN] THEN
    X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN
    FIRST_ASSUM(fun th -> MP_TAC(MATCH_MP th
      (ASSUME `(v:real^N) IN mfd_tball (g:A->real^N^N) x r`))) THEN
    DISCH_THEN(X_CHOOSE_THEN `s:real` STRIP_ASSUME_TAC) THEN
    USE_THEN "ball" (MP_TAC o C MATCH_MP (ASSUME `s < r`)) THEN STRIP_TAC THEN
    EXISTS_TAC `mfd_tball (g:A->real^N^N) x s` THEN
    ASM_REWRITE_TAC[GSYM OPEN_IN] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REAL_ARITH_TAC;
    MAP_EVERY X_GEN_TAC [`v:real^N`; `w:real^N`] THEN STRIP_TAC THEN
    FIRST_ASSUM(fun th -> MP_TAC(MATCH_MP th
      (ASSUME `(v:real^N) IN mfd_tball (g:A->real^N^N) x r`))) THEN
    DISCH_THEN(X_CHOOSE_THEN `s1:real` STRIP_ASSUME_TAC) THEN
    FIRST_ASSUM(fun th -> MP_TAC(MATCH_MP th
      (ASSUME `(w:real^N) IN mfd_tball (g:A->real^N^N) x r`))) THEN
    DISCH_THEN(X_CHOOSE_THEN `s2:real` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `max s1 s2 < r` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "ball" (MP_TAC o C MATCH_MP (ASSUME `max s1 s2 < r`)) THEN STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `mfd_tball (g:A->real^N^N) x s1 SUBSET mfd_tball g x (max s1 s2) /\
                  mfd_tball (g:A->real^N^N) x s2 SUBSET mfd_tball g x (max s1 s2)`
    MP_TAC THENL
     [CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN REAL_ARITH_TAC; ASM SET_TAC[]];
    MAP_EVERY X_GEN_TAC [`v:real^N`; `h:real^N`] THEN STRIP_TAC THEN
    FIRST_ASSUM(fun th -> MP_TAC(MATCH_MP th
      (ASSUME `(v:real^N) IN mfd_tball (g:A->real^N^N) x r`))) THEN
    DISCH_THEN(X_CHOOSE_THEN `s:real` STRIP_ASSUME_TAC) THEN
    USE_THEN "ball" (MP_TAC o C MATCH_MP (ASSUME `s < r`)) THEN STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `v:real^N` THEN ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* On a compact manifold the distances from x are bounded                    *)
(* (GEOJR_DIST_BOUNDED, the joinable class is a compact metric space), so    *)
(* injectivity balls and balls on which exp_x is injective have bounded      *)
(* radius (GEOJR_INJ_BALL_BOUND, GEOJR_INTRINSIC_BOUND).                      *)
(* ========================================================================= *)

let GEOJR_EXP_JOINABLE = prove
 (`!top atlas (g:A->real^N^N) (x:A) v.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ x IN topspace top /\
        v IN mfd_exp_dom (top,atlas) g x
        ==> mfd_joinable (top,atlas) x (mfd_exp (top,atlas) g x v)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `v:real^N`] MFD_GEO_MAXIMAL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&1 IN mfd_geo_maxint (top,atlas) (g:A->real^N^N) x v` ASSUME_TAC THENL
   [UNDISCH_TAC `v IN mfd_exp_dom (top,atlas) (g:A->real^N^N) x` THEN
    REWRITE_TAC[mfd_exp_dom; IN_ELIM_THM];
    ALL_TAC] THEN
  REWRITE_TAC[mfd_joinable; mfd_exp] THEN
  EXISTS_TAC `mfd_geo (top,atlas) (g:A->real^N^N) x v` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `mfd_geo (top,atlas) (g:A->real^N^N) x v`;
                 `mfd_geo_maxint (top,atlas) (g:A->real^N^N) x v`; `&0`; `&1`]
    MFD_GEODESIC_C1_CURVE) THEN
  ASM_REWRITE_TAC[REAL_POS] THEN ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
  REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN X_GEN_TAC `t:real` THEN STRIP_TAC THEN
  UNDISCH_TAC `is_realinterval(mfd_geo_maxint (top,atlas) (g:A->real^N^N) x v)` THEN
  REWRITE_TAC[is_realinterval] THEN DISCH_THEN MATCH_MP_TAC THEN
  MAP_EVERY EXISTS_TAC [`&0`; `&1`] THEN ASM_REWRITE_TAC[]);;

let GEOJR_DIST_BOUNDED = prove
 (`!top atlas (g:A->real^N^N) (x:A).
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ compact_space top
        ==> ?B. &0 <= B /\
                !y. mfd_joinable (top,atlas) x y ==> mfd_dist (top,atlas) g x y <= B`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`] MFD_METRIC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`] MFD_MTOPOLOGY) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `m = mfd_metric (top,atlas) (g:A->real^N^N) x` THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `mbounded m (mspace m:A->bool)` MP_TAC THENL
   [MATCH_MP_TAC COMPACT_IN_IMP_MBOUNDED THEN
    REWRITE_TAC[GSYM TOPSPACE_MTOPOLOGY; GSYM compact_space] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC COMPACT_SPACE_SUBTOPOLOGY THEN
    MATCH_MP_TAC CLOSED_IN_COMPACT_SPACE THEN ASM_REWRITE_TAC[closed_in] THEN
    ASM_SIMP_TAC[GRGD_JOINABLE_COMPLEMENT_OPEN] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[MFD_JOINABLE_IN_TOPSPACE];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[MBOUNDED_ALT; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_TAC `b:real` o CONJUNCT2) THEN
  EXISTS_TAC `abs b` THEN REWRITE_TAC[REAL_ABS_POS] THEN
  X_GEN_TAC `y:A` THEN DISCH_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `x <= b ==> x <= abs b`) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`x:A`; `y:A`]) THEN ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [ASM_MESON_TAC[MFD_JOINABLE_IN_TOPSPACE; MFD_JOINABLE_REFL]; SIMP_TAC[]]);;

let GEOJR_TNORM_VALUE = prove
 (`!top atlas (g:A->real^N^N) (x:A) t.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        x IN topspace top /\ &0 <= t
        ==> ?v. mfd_tnorm g x v = t`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`] GEOD_TNORM_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < mfd_tnorm (g:A->real^N^N) x (basis 1)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x:A`] GEOD_G_POS_DEF) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `basis 1:real^N`) THEN
    SIMP_TAC[BASIS_NONZERO; DIMINDEX_GE_1; LE_REFL] THEN
    REWRITE_TAC[GSYM(ASSUME `!v. mfd_tnorm (g:A->real^N^N) x v pow 2 =
                                 v dot (g x ** v)`)] THEN
    DISCH_TAC THEN REWRITE_TAC[REAL_LT_LE] THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th ->
      UNDISCH_TAC `&0 < mfd_tnorm (g:A->real^N^N) x (basis 1) pow 2` THEN
      REWRITE_TAC[GSYM th]) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `(t / mfd_tnorm (g:A->real^N^N) x (basis 1)) % basis 1:real^N` THEN
  ASM_REWRITE_TAC[REAL_ABS_DIV] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`; REAL_LT_IMP_LE] THEN
  ASM_SIMP_TAC[REAL_DIV_RMUL; REAL_LT_IMP_NZ]);;

let GEOJR_INJ_BALL_BOUND = prove
 (`!top atlas (g:A->real^N^N) (x:A) B r.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ x IN topspace top /\ &0 <= B /\
        (!y. mfd_joinable (top,atlas) x y ==> mfd_dist (top,atlas) g x y <= B) /\
        mfd_inj_ball (top,atlas) g x r
        ==> r <= B`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `(B + r) / &2`] GEOJR_TNORM_VALUE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `v:real^N`) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `r:real`; `v:real^N`] MFD_EXP_DIST) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `mfd_exp (top,atlas) (g:A->real^N^N) x v`) THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let GEOJR_INTRINSIC_BOUND = prove
 (`!top atlas (g:A->real^N^N) (x:A) B r.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ compact_space top /\ x IN topspace top /\
        &0 <= B /\
        (!y. mfd_joinable (top,atlas) x y ==> mfd_dist (top,atlas) g x y <= B) /\
        (!v w. v IN mfd_tball g x r /\ w IN mfd_tball g x r /\
               mfd_exp (top,atlas) g x v = mfd_exp (top,atlas) g x w ==> v = w)
        ==> r <= B`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `vec 0:real^N`] MFD_COMPACT_GEO_COMPLETE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `(B + r) / &2`] GEOJR_TNORM_VALUE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `v:real^N`) THEN
  SUBGOAL_THEN `mfd_joinable (top,atlas) x (mfd_exp (top,atlas) (g:A->real^N^N) x v)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC GEOJR_EXP_JOINABLE THEN ASM_REWRITE_TAC[IN_UNIV]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `mfd_exp (top,atlas) (g:A->real^N^N) x v`]
    MFD_EXP_TOTAL_MINIMIZING) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `mfd_dist (top,atlas) (g:A->real^N^N) x
                  (mfd_exp (top,atlas) g x v) <= B` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `w:real^N = v` MP_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[mfd_tball; IN_ELIM_THM] THEN
    ASM_REAL_ARITH_TAC;
    DISCH_THEN SUBST_ALL_TAC THEN ASM_REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* A uniform injectivity radius on compact manifolds                         *)
(* (GEOJR_UNIFORM_RADIUS, from MFD_UNIFORMLY_NORMAL and a finite subcover),   *)
(* MFD_INJRAD_COMPACT and MFD_INJRAD_LE_INTRINSIC.                            *)
(* ========================================================================= *)

let GEOJR_UNIFORM_RADIUS = prove
 (`!top atlas (g:A->real^N^N).
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ compact_space top
        ==> ?r0. &0 < r0 /\ !x. x IN topspace top ==> mfd_inj_ball (top,atlas) g x r0`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `topspace top:A->bool = {}` THENL
   [EXISTS_TAC `&1` THEN ASM_REWRITE_TAC[NOT_IN_EMPTY] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN topspace top
        ==> ?W r. open_in top W /\ x IN W /\ &0 < r /\
                  !y. y IN W ==> mfd_inj_ball (top,atlas) (g:A->real^N^N) y r`
  MP_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x:A`] MFD_UNIFORMLY_NORMAL) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [RIGHT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`Wf:A->A->bool`; `rf:A->real`] THEN DISCH_TAC THEN
  UNDISCH_TAC `compact_space (top:A topology)` THEN
  REWRITE_TAC[compact_space; compact_in] THEN
  DISCH_THEN(MP_TAC o SPEC `IMAGE (Wf:A->A->bool) (topspace top)` o CONJUNCT2) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FORALL_IN_IMAGE; SUBSET; IN_UNIONS; EXISTS_IN_IMAGE] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `V:(A->bool)->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`Wf:A->A->bool`; `topspace top:A->bool`; `V:(A->bool)->bool`]
    FINITE_SUBSET_IMAGE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `K:A->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `~(K:A->bool = {})` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `topspace top SUBSET UNIONS (V:(A->bool)->bool)` THEN
    ASM_REWRITE_TAC[IMAGE_CLAUSES; UNIONS_0; SUBSET_EMPTY];
    ALL_TAC] THEN
  MP_TAC(ISPEC `IMAGE (rf:A->real) K` INF_FINITE) THEN
  ASM_SIMP_TAC[FINITE_IMAGE; IMAGE_EQ_EMPTY] THEN
  REWRITE_TAC[IN_IMAGE; FORALL_IN_IMAGE] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `k:A` STRIP_ASSUME_TAC) ASSUME_TAC) THEN
  EXISTS_TAC `inf (IMAGE (rf:A->real) K)` THEN CONJ_TAC THENL
   [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
  X_GEN_TAC `y:A` THEN DISCH_TAC THEN
  SUBGOAL_THEN `?k'. k' IN K /\ (y:A) IN (Wf:A->A->bool) k'` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `topspace top SUBSET UNIONS (V:(A->bool)->bool)` THEN
    ASM_REWRITE_TAC[SUBSET; IN_UNIONS; EXISTS_IN_IMAGE] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MFD_INJ_BALL_MONO THEN EXISTS_TAC `(rf:A->real) k'` THEN
  ASM_SIMP_TAC[] THEN ASM_MESON_TAC[SUBSET]);;

let MFD_INJRAD_COMPACT = prove
 (`!top atlas (g:A->real^N^N).
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ compact_space top
        ==> ?r0. &0 < r0 /\
                 !x. x IN topspace top
                     ==> r0 <= mfd_injrad (top,atlas) g x /\
                         !r. mfd_inj_ball (top,atlas) g x r <=>
                             r <= mfd_injrad (top,atlas) g x`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`] GEOJR_UNIFORM_RADIUS) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `r0:real` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`] GEOJR_DIST_BOUNDED) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[mfd_injrad] THEN
  ABBREV_TAC `S = {r | &0 < r /\ mfd_inj_ball (top,atlas) (g:A->real^N^N) x r}` THEN
  SUBGOAL_THEN `(r0:real) IN S /\ (!r. r IN S ==> r <= B)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_SIMP_TAC[] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC GEOJR_INJ_BALL_BOUND THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                          `g:A->real^N^N`; `x:A`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `r0 <= sup S` ASSUME_TAC THENL
   [MATCH_MP_TAC ELEMENT_LE_SUP THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `r:real` THEN EQ_TAC THENL
   [DISCH_TAC THEN ASM_CASES_TAC `&0 < r` THENL
     [MATCH_MP_TAC ELEMENT_LE_SUP THEN CONJ_TAC THENL
       [ASM_MESON_TAC[]; EXPAND_TAC "S" THEN ASM_REWRITE_TAC[IN_ELIM_THM]];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_TAC THEN MATCH_MP_TAC MFD_INJ_BALL_SUP THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `s:real` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`S:real->bool`; `s:real`] SUP_APPROACH) THEN ANTS_TAC THENL
   [CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[]; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC MFD_INJ_BALL_MONO THEN EXISTS_TAC `t:real` THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `(t:real) IN S` THEN EXPAND_TAC "S" THEN
  SIMP_TAC[IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC);;

let MFD_INJRAD_LE_INTRINSIC = prove
 (`!top atlas (g:A->real^N^N) (x:A).
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ compact_space top /\ x IN topspace top
        ==> mfd_injrad (top,atlas) g x <= mfd_injrad_intrinsic (top,atlas) g x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_injrad; mfd_injrad_intrinsic] THEN
  MATCH_MP_TAC REAL_SUP_LE_SUBSET THEN REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x:A`] MFD_EXP_LOCAL_DIFFEO) THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `r:real` THEN
    REWRITE_TAC[mfd_inj_ball] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `mfd_exp (top,atlas) (g:A->real^N^N) x`; `mfd_tball (g:A->real^N^N) x r`]
      GEOJR_PARAM_FACTS) THEN
    ASM_SIMP_TAC[GSYM SUBSET] THEN MESON_TAC[];
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x:A`] GEOJR_DIST_BOUNDED) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `B:real` THEN REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `r:real` THEN
    STRIP_TAC THEN MATCH_MP_TAC GEOJR_INTRINSIC_BOUND THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                          `g:A->real^N^N`; `x:A`] THEN
    ASM_REWRITE_TAC[]]);;

