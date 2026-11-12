(* ========================================================================= *)
(* pc_p2b_kfl (Part 2B, a step of the proof of P2B_SPLIT_ROUND_STATEMENT):   *)
(* the flow of a parallel unit field.                                        *)
(*                                                                           *)
(* For a complete metric g with a parallel unit field X (p2b_parallel_on):  *)
(*  - the orbits Phi_r y = mfd_geo y (X y) r are geodesics with velocity X,  *)
(*    defined for all r, with the group law (P2BKF_ORBIT, _SHIFT); two       *)
(*    metrics for which X is parallel have the same orbits (_ORBIT_TIME);    *)
(*  - along a Ricci flow with X parallel at every time, g(s) X does not     *)
(*    depend on s (P2BKF_OMEGA_CONST: Ric X = 0);                            *)
(*  - the exponential map of the g-orthogonal complement of X(x0) is        *)
(*    horizontal (P2BKF_HORIZ, Jacobi fields);                               *)
(*  - flow charts fmap(z) = Phi_(z$3)(exp_x0(z$1 u1 + z$2 u2)) (dimension 3): *)
(*    smooth, a local parametrization near 0, d fmap(e3) = X, and for every *)
(*    metric g2 with X parallel the inner products of the coordinate fields *)
(*    do not depend on z$3 (P2BKF_FMAP_METRIC_INV2, the Killing equation in  *)
(*    coordinates P2BKF_KILLING_CHART) and the first two are orthogonal to X *)
(*    when g2 X = g X (P2BKF_FMAP_HORIZ_ALL);                                *)
(*  - Phi_r is a diffeomorphism of M and an isometry of every such g2        *)
(*    (P2BKF_PHI_DIFFEO, P2BKF_PHI_ISOMETRY).                                *)
(*                                                                           *)
(* The needs lines load the parallel-field chart kit pc_p2b_parkit,          *)
(* p2b_parallel_on of pc_p2b_splitreq, geodesics, distances and the mfd      *)
(* units (not pc_p2b_x0).                                                    *)
(* ========================================================================= *)

needs "src/pc_p2b_parkit.ml";;
needs "src/pc_p2b_splitreq.ml";;
needs "src/pc_geo_iface.ml";;
needs "src/pc_geo_jvar.ml";;
needs "src/pc_grg_dist.ml";;
needs "src/pc_mfd_diff.ml";;
needs "src/pc_mfd_restrict.ml";;
needs "src/pc_rf_basic.ml";;
needs "src/pc_smt_glue.ml";;
needs "src/pc_top_cover.ml";;
needs "src/pc_mfd_examples.ml";;

prioritize_real();;
type_invention_error := true;;

(* KFL.A1 A parallel field along geodesics; the orbits of a parallel unit *)
(* field (geodesics with velocity X), their group law.                     *)

let P2BKF_FIELD_REP_DERIV = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (X:A->real^N) (gamma:real->A) c t v d.
     smooth_manifold_atlas top atlas /\ c IN atlas /\ &0 < d /\
     (!s. abs(s - t) < d ==> gamma s IN FST c) /\
     ((\s. SND c (gamma(drop s))) has_vector_derivative v) (at (lift t)) /\
     mfd_vrep atlas X c differentiable at (SND c (gamma t))
     ==> ((\s. mfd_field_rep atlas gamma (\u. X(gamma u)) c (drop s)) has_vector_derivative
          frechet_derivative (mfd_vrep atlas X c) (at (SND c (gamma t))) v) (at (lift t))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_TRANSFORM_AT THEN
  EXISTS_TAC `(mfd_vrep atlas (X:A->real^N) c) o (\s. SND c ((gamma:real->A)(drop s)))` THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `s:real^1` THEN REWRITE_TAC[DIST_LIFT; o_THM] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `(gamma:real->A)(drop s) IN FST(c:(A->bool)#(A->real^N))` ASSUME_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN
      UNDISCH_TAC `dist(s:real^1,lift t) < d` THEN
      REWRITE_TAC[DIST_REAL; GSYM drop; LIFT_DROP];
      ALL_TAC] THEN
    REWRITE_TAC[mfd_field_rep; mfd_vrep] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[has_vector_derivative] THEN
  SUBGOAL_THEN
   `(\h. drop h % frechet_derivative (mfd_vrep atlas (X:A->real^N) c)
                     (at (SND c ((gamma:real->A) t))) v) =
    frechet_derivative (mfd_vrep atlas X c) (at (SND c (gamma t))) o (\h. drop h % v)`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM] THEN X_GEN_TAC `h:real^1` THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC LINEAR_CMUL THEN
    MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC DIFF_CHAIN_AT THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[GSYM has_vector_derivative];
    REWRITE_TAC[LIFT_DROP] THEN ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS]]);;

let P2BKF_EVENTUALLY_IN = prove
 (`!top (gamma:real->A) J U t.
     continuous_map (subtopology euclideanreal J,top) gamma /\ real_open J /\ t IN J /\
     open_in top U /\ gamma t IN U
     ==> ?d. &0 < d /\ !s. abs(s - t) < d ==> s IN J /\ gamma s IN U`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o CONJUNCT2 o GEN_REWRITE_RULE I [CONTINUOUS_MAP]) THEN
  DISCH_THEN(MP_TAC o SPEC `U:A->bool`) THEN
  ASM_REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; TOPSPACE_EUCLIDEANREAL; INTER_UNIV] THEN
  SUBGOAL_THEN `open_in euclideanreal (J:real->bool)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[GSYM REAL_OPEN_IN]; ALL_TAC] THEN
  ASM_SIMP_TAC[OPEN_IN_OPEN_SUBTOPOLOGY; IN_UNIV] THEN
  REWRITE_TAC[GSYM REAL_OPEN_IN; real_open; IN_ELIM_THM] THEN
  DISCH_THEN(MP_TAC o SPEC `t:real` o CONJUNCT1) THEN ASM_REWRITE_TAC[] THEN
  MESON_TAC[]);;

let P2BKF_PAR_ALONG_GEO = prove
 (`!top atlas (g:A->real^N^N) (X:A->real^N) (gamma:real->A) J.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     p2b_parallel_on atlas g (topspace top) X /\ mfd_geodesic (top,atlas) g gamma J
     ==> mfd_parallel atlas g gamma J (\t. X(gamma t))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2b_parallel_on]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [mfd_geodesic]) THEN
  SUBGOAL_THEN
   `!t. t IN J
        ==> ((\s. mfd_field_rep atlas (gamma:real->A) (\u. (X:A->real^N)(gamma u))
                    (chart_at atlas (gamma t)) (drop s)) has_vector_derivative
             frechet_derivative (mfd_vrep atlas X (chart_at atlas (gamma t)))
                                (at (SND(chart_at atlas (gamma t)) (gamma t)))
                                (mfd_vel atlas gamma t)) (at (lift t))`
  ASSUME_TAC THENL
   [X_GEN_TAC `t:real` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(gamma:real->A) t IN topspace top` ASSUME_TAC THENL
     [UNDISCH_TAC `continuous_map (subtopology euclideanreal J,top) (gamma:real->A)` THEN
      REWRITE_TAC[CONTINUOUS_MAP; SUBSET; FORALL_IN_IMAGE; TOPSPACE_SUBTOPOLOGY;
                  TOPSPACE_EUCLIDEANREAL; INTER_UNIV] THEN
      ASM_MESON_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `(gamma:real->A) t`]
                  CHART_AT) THEN
    ASM_REWRITE_TAC[] THEN
    ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^N))->bool) ((gamma:real->A) t)` THEN
    STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `c:(A->bool)#(A->real^N)` o check (fun th ->
      is_forall(concl th) &&
      can (find_term (fun t -> try fst(dest_const t) = "christoffel" with Failure _ -> false))
          (concl th) &&
      can (find_term (fun t -> try fst(dest_const t) = "has_vector_derivative"
                               with Failure _ -> false)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `v:real->real^N` (MP_TAC o SPEC `t:real`)) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `mfd_vel atlas (gamma:real->A) t = (v:real->real^N) t` SUBST1_TAC THENL
     [REWRITE_TAC[mfd_vel] THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC VECTOR_DERIVATIVE_AT THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `gamma:real->A`; `J:real->bool`;
                   `FST(c:(A->bool)#(A->real^N))`; `t:real`] P2BKF_EVENTUALLY_IN) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC P2BKF_FIELD_REP_DERIV THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `d:real`] THEN ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c INTER topspace top)` THEN
    SUBGOAL_THEN `FST(c:(A->bool)#(A->real^N)) INTER topspace top = FST c` SUBST1_TAC THENL
     [FIRST_ASSUM(MP_TAC o MATCH_MP OPEN_IN_SUBSET) THEN SET_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `c:(A->bool)#(A->real^N)` o check (fun th ->
        is_forall(concl th) &&
        can (find_term (fun t -> try fst(dest_const t) = "smooth_map_on" with Failure _ -> false))
            (concl th))) THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `FST(c:(A->bool)#(A->real^N)) INTER topspace top = FST c` SUBST1_TAC THENL
       [FIRST_ASSUM(MP_TAC o MATCH_MP OPEN_IN_SUBSET) THEN SET_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[];
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[mfd_parallel; mfd_field_diff] THEN CONJ_TAC THENL
   [X_GEN_TAC `t:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `t:real`) THEN ASM_REWRITE_TAC[] THEN
    MESON_TAC[differentiable; has_vector_derivative];
    ALL_TAC] THEN
  X_GEN_TAC `t:real` THEN DISCH_TAC THEN
  REWRITE_TAC[mfd_covd] THEN
  FIRST_X_ASSUM(fun th -> MP_TAC(MATCH_MP VECTOR_DERIVATIVE_AT (MP (SPEC `t:real` th)
    (ASSUME `(t:real) IN J`)))) THEN
  DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `(gamma:real->A) t IN topspace top` ASSUME_TAC THENL
   [UNDISCH_TAC `continuous_map (subtopology euclideanreal J,top) (gamma:real->A)` THEN
    REWRITE_TAC[CONTINUOUS_MAP; SUBSET; FORALL_IN_IMAGE; TOPSPACE_SUBTOPOLOGY;
                TOPSPACE_EUCLIDEANREAL; INTER_UNIV] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `X:A->real^N`;
                 `(gamma:real->A) t`] P2BX0_VREP_AT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `(gamma:real->A) t`]
                CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
    is_forall(concl th) &&
    can (find_term (fun t -> try fst(dest_const t) = "christoffel" with Failure _ -> false))
        (concl th) &&
    not (can (find_term (fun t -> try fst(dest_const t) = "has_vector_derivative"
                                  with Failure _ -> false)) (concl th)))) THEN
  ASM_REWRITE_TAC[IN_INTER] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_INTER]);;

let P2BKF_ORBIT = prove
 (`!top atlas (g:A->real^N^N) (X:A->real^N) y.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_complete (top,atlas) g /\ p2b_parallel_on atlas g (topspace top) X /\
     y IN topspace top
     ==> mfd_geo_maxint (top,atlas) g y (X y) = (:real) /\
         mfd_geodesic (top,atlas) g (mfd_geo (top,atlas) g y (X y)) (:real) /\
         (!r. mfd_geo (top,atlas) g y (X y) r IN topspace top) /\
         (!r. mfd_vel atlas (mfd_geo (top,atlas) g y (X y)) r =
              X(mfd_geo (top,atlas) g y (X y) r))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `mfd_geo_maxint (top,atlas) (g:A->real^N^N) y ((X:A->real^N) y) = (:real)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`]
                  MFD_COMPLETE_GEO_COMPLETE) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC MFD_COMPLETE_IMP_MCOMPLETE THEN ASM_REWRITE_TAC[];
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `y:A`; `(X:A->real^N) y`] MFD_GEO_MAXIMAL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `gamma = mfd_geo (top,atlas) (g:A->real^N^N) y ((X:A->real^N) y)` THEN
  SUBGOAL_THEN `!r. (gamma:real->A) r IN topspace top` ASSUME_TAC THENL
   [UNDISCH_TAC `mfd_geodesic (top,atlas) (g:A->real^N^N) (gamma:real->A) (:real)` THEN
    REWRITE_TAC[mfd_geodesic; CONTINUOUS_MAP; SUBSET; FORALL_IN_IMAGE;
                TOPSPACE_SUBTOPOLOGY; TOPSPACE_EUCLIDEANREAL; INTER_UNIV; IN_UNIV] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `gamma:real->A`; `(:real)`; `&0`; `(X:A->real^N) y`]
                MFD_PARALLEL_EXISTS_UNIQUE) THEN
  ASM_REWRITE_TAC[IN_UNIV; REAL_OPEN_UNIV; IS_REALINTERVAL_UNIV] THEN ANTS_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                   `gamma:real->A`; `(:real)`; `a:real`; `b:real`] MFD_GEODESIC_C1_CURVE) THEN
    ASM_REWRITE_TAC[SUBSET_UNIV] THEN SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Y:real->real^N` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "uniq")))) THEN
  SUBGOAL_THEN `!r. mfd_vel atlas (gamma:real->A) r = (Y:real->real^N) r /\
                    (\t. (X:A->real^N)(gamma t)) r = Y r`
  (fun th -> REWRITE_TAC[REWRITE_RULE[] th]) THEN
  X_GEN_TAC `r:real` THEN CONJ_TAC THEN USE_THEN "uniq" (MATCH_MP_TAC o REWRITE_RULE[IN_UNIV; RIGHT_IMP_FORALL_THM]) THEN
  ASM_REWRITE_TAC[ETA_AX] THENL
   [MATCH_MP_TAC MFD_GEODESIC_VEL_PARALLEL THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                   `X:A->real^N`; `gamma:real->A`; `(:real)`] P2BKF_PAR_ALONG_GEO) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th])]);;

let P2BKF_ORBIT_SHIFT = prove
 (`!top atlas (g:A->real^N^N) (X:A->real^N) y.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_complete (top,atlas) g /\ p2b_parallel_on atlas g (topspace top) X /\
     y IN topspace top
     ==> !r s. mfd_geo (top,atlas) g (mfd_geo (top,atlas) g y (X y) r)
                       (X(mfd_geo (top,atlas) g y (X y) r)) s =
               mfd_geo (top,atlas) g y (X y) (r + s)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BKF_ORBIT) THEN
  POP_ASSUM_LIST(MAP_EVERY ASSUME_TAC) THEN STRIP_ASSUME_TAC(ASSUME
   `hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
    mfd_complete (top,atlas) (g:A->real^N^N) /\ p2b_parallel_on atlas g (topspace top) (X:A->real^N) /\
    (y:A) IN topspace top`) THEN
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `y:A`; `(X:A->real^N) y`; `r:real`] MFD_GEO_SHIFT) THEN
  ASM_REWRITE_TAC[IN_UNIV] THEN
  DISCH_THEN(MP_TAC o SPEC `s:real` o CONJUNCT2) THEN ASM_REWRITE_TAC[]);;

let P2BKF_VREP_CHAIN = prove
 (`!(atlas:((A->bool)#(A->real^N))->bool) (X:A->real^N) (gamma:real->A) c t w.
     ((\s. SND c (gamma(drop s))) has_vector_derivative w) (at (lift t)) /\
     mfd_vrep atlas X c differentiable at (SND c (gamma t))
     ==> ((\s. mfd_vrep atlas X c (SND c (gamma(drop s)))) has_vector_derivative
          frechet_derivative (mfd_vrep atlas X c) (at (SND c (gamma t))) w) (at (lift t))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[has_vector_derivative] THEN
  SUBGOAL_THEN
   `(\h. drop h % frechet_derivative (mfd_vrep atlas (X:A->real^N) c)
                     (at (SND c ((gamma:real->A) t))) w) =
    frechet_derivative (mfd_vrep atlas X c) (at (SND c (gamma t))) o (\h. drop h % w)`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM] THEN X_GEN_TAC `h:real^1` THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC LINEAR_CMUL THEN
    MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\s. mfd_vrep atlas (X:A->real^N) c (SND c ((gamma:real->A)(drop s)))) =
                mfd_vrep atlas X c o (\s. SND c (gamma(drop s)))` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC DIFF_CHAIN_AT THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[GSYM has_vector_derivative];
    REWRITE_TAC[LIFT_DROP] THEN ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS]]);;

let P2BKF_VREP_DIFF = prove
 (`!top atlas (g:A->real^N^N) (X:A->real^N) c y.
     smooth_manifold_atlas top atlas /\ p2b_parallel_on atlas g (topspace top) X /\
     c IN atlas /\ y IN IMAGE (SND c) (FST c)
     ==> mfd_vrep atlas X c differentiable at y /\
         !z. frechet_derivative (mfd_vrep atlas X c) (at y) z +
             christoffel (metric_local atlas c g) y z (mfd_vrep atlas X c y) = vec 0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `FST(c:(A->bool)#(A->real^N)) INTER topspace top = FST c` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP OPEN_IN_SUBSET) THEN SET_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2b_parallel_on]) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `c:(A->bool)#(A->real^N)` o check (fun th ->
      can (find_term (fun t -> try fst(dest_const t) = "smooth_map_on" with Failure _ -> false))
          (concl th))) THEN
    ASM_REWRITE_TAC[];
    GEN_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

let P2BKF_ORBIT_TIME = prove
 (`!top atlas (g1:A->real^N^N) g2 (X:A->real^N) y.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\
     riemannian_metric atlas g1 /\ riemannian_metric atlas g2 /\
     mfd_complete (top,atlas) g1 /\ mfd_complete (top,atlas) g2 /\
     p2b_parallel_on atlas g1 (topspace top) X /\ p2b_parallel_on atlas g2 (topspace top) X /\
     y IN topspace top
     ==> mfd_geo (top,atlas) g1 y (X y) = mfd_geo (top,atlas) g2 y (X y)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g1:A->real^N^N`;
                 `X:A->real^N`; `y:A`] P2BKF_ORBIT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g2:A->real^N^N`;
                 `X:A->real^N`; `y:A`] P2BKF_ORBIT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g1:A->real^N^N`;
                 `y:A`; `(X:A->real^N) y`] MFD_GEO_MAXIMAL) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g2:A->real^N^N`;
                 `y:A`; `(X:A->real^N) y`] MFD_GEO_MAXIMAL) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  ABBREV_TAC `gamma1 = mfd_geo (top,atlas) (g1:A->real^N^N) y ((X:A->real^N) y)` THEN
  ABBREV_TAC `gamma2 = mfd_geo (top,atlas) (g2:A->real^N^N) y ((X:A->real^N) y)` THEN
  SUBGOAL_THEN `mfd_geodesic (top,atlas) (g2:A->real^N^N) (gamma1:real->A) (:real)`
  ASSUME_TAC THENL
   [MP_TAC(ASSUME `mfd_geodesic (top,atlas) (g1:A->real^N^N) (gamma1:real->A) (:real)`) THEN
    REWRITE_TAC[mfd_geodesic; IN_UNIV] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
    EXISTS_TAC `\t. mfd_vrep atlas (X:A->real^N) (c:(A->bool)#(A->real^N)) (SND c ((gamma1:real->A) t))` THEN
    X_GEN_TAC `t:real` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `((\s. SND (c:(A->bool)#(A->real^N)) ((gamma1:real->A)(drop s))) has_vector_derivative
                   mfd_vrep atlas (X:A->real^N) c (SND c (gamma1 t))) (at (lift t))`
    ASSUME_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g1:A->real^N^N`;
                     `gamma1:real->A`; `(:real)`; `c:(A->bool)#(A->real^N)`; `t:real`]
                    MFD_GEODESIC_VEL_CHART) THEN
      ASM_REWRITE_TAC[IN_UNIV] THEN REWRITE_TAC[mfd_vrep] THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g2:A->real^N^N`;
                   `X:A->real^N`; `c:(A->bool)#(A->real^N)`;
                   `SND (c:(A->bool)#(A->real^N)) ((gamma1:real->A) t)`] P2BKF_VREP_DIFF) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC
      `mfd_vrep atlas (X:A->real^N) (c:(A->bool)#(A->real^N)) (SND c ((gamma1:real->A) t))`)) THEN
    REWRITE_TAC[VECTOR_ARITH `a + b:real^N = vec 0 <=> a = --b`] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC P2BKF_VREP_CHAIN THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `r:real` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g2:A->real^N^N`;
                 `gamma1:real->A`; `gamma2:real->A`; `(:real)`; `(:real)`; `&0`]
                MFD_GEODESIC_UNIQUE) THEN
  ASM_REWRITE_TAC[IN_UNIV; INTER_UNIV] THEN SIMP_TAC[]);;

(* KFL.A2 The Ricci form kills a parallel field; g(s) X does not depend on  *)
(* s along a Ricci flow for which X is parallel at every time.              *)

let P2BKF_RICCI_MATRIX_PAR = prove
 (`!top atlas (g:A->real^N^N) (X:A->real^N) x.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     p2b_parallel_on atlas g (topspace top) X /\ x IN topspace top
     ==> mfd_ricci_matrix atlas g x ** X x = vec 0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `FST(c:(A->bool)#(A->real^N)) INTER topspace top = FST c` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP OPEN_IN_SUBSET) THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `metric_field (IMAGE (SND c) (FST c))
                  (metric_local atlas (c:(A->bool)#(A->real^N)) (g:A->real^N^N))` ASSUME_TAC THENL
   [UNDISCH_TAC `riemannian_metric atlas (g:A->real^N^N)` THEN
    REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `SND (c:(A->bool)#(A->real^N)) x IN IMAGE (SND c) (FST c)` ASSUME_TAC THENL
   [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)`;
                 `metric_local atlas (c:(A->bool)#(A->real^N)) (g:A->real^N^N)`;
                 `mfd_vrep atlas (X:A->real^N) c`; `SND (c:(A->bool)#(A->real^N)) x`]
                P2BX0_LRICCI_PAR) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2b_parallel_on]) THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `c:(A->bool)#(A->real^N)` o check (fun th ->
        can (find_term (fun t -> try fst(dest_const t) = "smooth_map_on" with Failure _ -> false))
            (concl th))) THEN ASM_REWRITE_TAC[];
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `X:A->real^N`; `x:A`]
                P2BX0_VREP_AT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[GSYM VECTOR_EQ_LDOT] THEN X_GEN_TAC `u:real^N` THEN
  REWRITE_TAC[DOT_RZERO] THEN
  SUBGOAL_THEN
   `u dot (mfd_ricci_matrix atlas (g:A->real^N^N) x ** (X:A->real^N) x) =
    lricci (metric_local atlas (c:(A->bool)#(A->real^N)) g) (SND c x) u (X x)`
  SUBST1_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[]] THEN
  MP_TAC(ISPECL [`IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)`;
                 `metric_local atlas (c:(A->bool)#(A->real^N)) (g:A->real^N^N)`;
                 `SND (c:(A->bool)#(A->real^N)) x`; `u:real^N`; `(X:A->real^N) x`]
                LRG_LRICCI_EXPAND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[mfd_ricci_matrix; mfd_ricci] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[dot] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `p:num` THEN
  STRIP_TAC THEN REWRITE_TAC[] THEN AP_TERM_TAC THEN
  ASM_SIMP_TAC[matrix_vector_mul; LAMBDA_BETA] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `q:num` THEN STRIP_TAC THEN
  REWRITE_TAC[] THEN ASM_SIMP_TAC[LAMBDA_BETA] THEN REAL_ARITH_TAC);;

let P2BKF_OMEGA_CONST = prove
 (`!top atlas (g:real->A->real^N^N) (X:A->real^N) a b.
     ricci_flow_on (top,atlas) a b g /\
     (!s. a < s /\ s < b ==> p2b_parallel_on atlas (g s) (topspace top) X)
     ==> !s1 s2 y. a < s1 /\ s1 < b /\ a < s2 /\ s2 < b /\ y IN topspace top
                   ==> g s1 y ** X y = g s2 y ** X y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [ricci_flow_on]) THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[CART_EQ] THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`\s. ((g:real->A->real^N^N) s y ** (X:A->real^N) y)$i`;
                 `real_interval(a,b)`] HAS_REAL_DERIVATIVE_ZERO_CONSTANT) THEN
  REWRITE_TAC[IS_REALINTERVAL_INTERVAL; IN_REAL_INTERVAL] THEN ANTS_TAC THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
    ASM_SIMP_TAC[matrix_vector_mul; LAMBDA_BETA] THEN
    SUBGOAL_THEN `&0 = sum(1..dimindex(:N))
                     (\j. (--(&2) * mfd_ricci_matrix atlas ((g:real->A->real^N^N) t) y$i$j) *
                          (X:A->real^N) y$j)` SUBST1_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `(g:real->A->real^N^N) t`; `X:A->real^N`; `y:A`]
                    P2BKF_RICCI_MATRIX_PAR) THEN
      ASM_SIMP_TAC[] THEN
      DISCH_THEN(MP_TAC o AP_TERM `\v:real^N. v$i`) THEN
      ASM_SIMP_TAC[matrix_vector_mul; LAMBDA_BETA; VEC_COMPONENT] THEN
      REWRITE_TAC[GSYM REAL_MUL_ASSOC; SUM_LMUL] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUM THEN REWRITE_TAC[FINITE_NUMSEG] THEN
    X_GEN_TAC `j:num` THEN REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_RMUL_ATREAL THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (find_term (fun t -> try fst(dest_const t) = "has_real_derivative"
                               with Failure _ -> false)) (concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `k:real`) THEN
  FIRST_ASSUM(MP_TAC o SPEC `s1:real`) THEN FIRST_X_ASSUM(MP_TAC o SPEC `s2:real`) THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* KFL.A3 The curvature against a parallel field vanishes; geodesics from x0 *)
(* with initial velocity orthogonal to X, and the Jacobi fields along them   *)
(* with Y(0) = 0 and Y'(0) orthogonal to X, stay orthogonal to X: the        *)
(* exponential map of the orthogonal complement of X(x0) is horizontal.     *)

let P2BKF_SYM_DOT = prove
 (`!(A:real^N^N) u v. transp A = A ==> u dot (A ** v) = v dot (A ** u)`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM DOT_LMUL_MATRIX] THEN
  ASM_REWRITE_TAC[VECTOR_MATRIX_MUL_TRANSP] THEN REWRITE_TAC[DOT_SYM]);;

let P2BKF_RIEMANN_DOT_PAR = prove
 (`!top atlas (g:A->real^N^N) (X:A->real^N) x a b c.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     p2b_parallel_on atlas g (topspace top) X /\ x IN topspace top
     ==> mfd_riemann atlas g x a b c dot (g x ** X x) = &0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `c0 = chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c0:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `FST(c0:(A->bool)#(A->real^N)) INTER topspace top = FST c0` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP OPEN_IN_SUBSET) THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `metric_field (IMAGE (SND c0) (FST c0))
                  (metric_local atlas (c0:(A->bool)#(A->real^N)) (g:A->real^N^N))` ASSUME_TAC THENL
   [UNDISCH_TAC `riemannian_metric atlas (g:A->real^N^N)` THEN
    REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `SND (c0:(A->bool)#(A->real^N)) x IN IMAGE (SND c0) (FST c0)` ASSUME_TAC THENL
   [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `x:A`] METRIC_LOCAL_AT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `X:A->real^N`; `x:A`]
                P2BX0_VREP_AT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  ASM_REWRITE_TAC[mfd_riemann] THEN
  ABBREV_TAC `G = metric_local atlas (c0:(A->bool)#(A->real^N)) (g:A->real^N^N)` THEN
  ABBREV_TAC `y = SND (c0:(A->bool)#(A->real^N)) x` THEN
  ABBREV_TAC `W = mfd_vrep atlas (X:A->real^N) c0` THEN
  SUBGOAL_THEN `transp((G:real^N->real^N^N) y) = G y` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  ASM_SIMP_TAC[P2BKF_SYM_DOT] THEN
  MP_TAC(ISPECL [`IMAGE (SND (c0:(A->bool)#(A->real^N))) (FST c0)`; `G:real^N->real^N^N`;
                 `y:real^N`; `a:real^N`; `b:real^N`; `c:real^N`; `(W:real^N->real^N) y`]
                LRIEMANN_METRIC_ANTISYM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`IMAGE (SND (c0:(A->bool)#(A->real^N))) (FST c0)`; `G:real^N->real^N^N`;
                 `W:real^N->real^N`; `y:real^N`; `a:real^N`; `b:real^N`]
                P2BX0_LRIEMANN_PARALLEL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2b_parallel_on]) THEN
    EXPAND_TAC "W" THEN EXPAND_TAC "G" THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `c0:(A->bool)#(A->real^N)` o check (fun th ->
        can (find_term (fun t -> try fst(dest_const t) = "smooth_map_on" with Failure _ -> false))
            (concl th))) THEN ASM_REWRITE_TAC[];
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[MATRIX_VECTOR_MUL_RZERO; DOT_RZERO; REAL_NEG_0]);;

let P2BKF_HORIZ = prove
 (`!top atlas (g:A->real^N^N) (X:A->real^N) x0 w v.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_complete (top,atlas) g /\ p2b_parallel_on atlas g (topspace top) X /\
     x0 IN topspace top /\ v dot (g x0 ** X x0) = &0
     ==> mfd_differential (open_set_atlas (:real^N)) atlas (mfd_exp (top,atlas) g x0) w v dot
         (g (mfd_exp (top,atlas) g x0 w) ** X (mfd_exp (top,atlas) g x0 w)) = &0`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `mfd_geo_maxint (top,atlas) (g:A->real^N^N) x0 w = (:real)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`]
                  MFD_COMPLETE_GEO_COMPLETE) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC MFD_COMPLETE_IMP_MCOMPLETE THEN ASM_REWRITE_TAC[];
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `x0:A`; `w:real^N`] MFD_GEO_MAXIMAL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `gamma = mfd_geo (top,atlas) (g:A->real^N^N) x0 w` THEN
  SUBGOAL_THEN `!t. (gamma:real->A) t IN topspace top` ASSUME_TAC THENL
   [UNDISCH_TAC `mfd_geodesic (top,atlas) (g:A->real^N^N) (gamma:real->A) (:real)` THEN
    REWRITE_TAC[mfd_geodesic; CONTINUOUS_MAP; SUBSET; FORALL_IN_IMAGE;
                TOPSPACE_SUBTOPOLOGY; TOPSPACE_EUCLIDEANREAL; INTER_UNIV; IN_UNIV] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!a b. a <= b /\ real_interval[a,b] SUBSET (:real)
                      ==> mfd_c1_curve (top,atlas:((A->bool)#(A->real^N))->bool) (gamma:real->A) a b` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                   `gamma:real->A`; `(:real)`; `a:real`; `b:real`] MFD_GEODESIC_C1_CURVE) THEN
    ASM_REWRITE_TAC[SUBSET_UNIV] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `gamma:real->A`; `(:real)`; `&0`; `vec 0:real^N`; `v:real^N`]
                MFD_JACOBI_EXISTS_UNIQUE) THEN
  ASM_REWRITE_TAC[IN_UNIV] THEN
  DISCH_THEN(X_CHOOSE_THEN `Y:real->real^N` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `x0:A`; `w:real^N`; `v:real^N`; `Y:real->real^N`]
                MFD_EXP_DIFFERENTIAL_JACOBI) THEN
  ASM_REWRITE_TAC[mfd_exp_dom; IN_ELIM_THM; IN_UNIV] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[mfd_exp] THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `X:A->real^N`; `gamma:real->A`; `(:real)`] P2BKF_PAR_ALONG_GEO) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [mfd_parallel]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [mfd_jacobi]) THEN
  ABBREV_TAC `f1 = \t. (Y:real->real^N) t dot
                       ((g:A->real^N^N)((gamma:real->A) t) ** (X:A->real^N)(gamma t))` THEN
  ABBREV_TAC `f2 = \t. mfd_covd atlas (g:A->real^N^N) (gamma:real->A) (Y:real->real^N) t dot
                       (g(gamma t) ** (X:A->real^N)(gamma t))` THEN
  SUBGOAL_THEN `!t. ((f1:real->real) has_real_derivative f2 t) (atreal t)` ASSUME_TAC THENL
   [X_GEN_TAC `t:real` THEN REWRITE_TAC[HAS_REAL_VECTOR_DERIVATIVE_AT] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                   `gamma:real->A`; `(:real)`; `Y:real->real^N`;
                   `\t. (X:A->real^N)((gamma:real->A) t)`; `t:real`] MFD_COVD_METRIC) THEN
    ASM_REWRITE_TAC[IN_UNIV; REAL_OPEN_UNIV; IS_REALINTERVAL_UNIV] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN BINOP_TAC THENL
     [EXPAND_TAC "f1" THEN REWRITE_TAC[FUN_EQ_THM; o_THM];
      EXPAND_TAC "f2" THEN AP_TERM_TAC THEN
      SUBGOAL_THEN `mfd_covd atlas (g:A->real^N^N) (gamma:real->A)
                      (\t. (X:A->real^N)(gamma t)) t = vec 0` SUBST1_TAC THENL
       [ASM_SIMP_TAC[IN_UNIV]; ALL_TAC] THEN
      REWRITE_TAC[MATRIX_VECTOR_MUL_RZERO; DOT_RZERO; REAL_ADD_RID]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!t. ((f2:real->real) has_real_derivative &0) (atreal t)` ASSUME_TAC THENL
   [X_GEN_TAC `t:real` THEN REWRITE_TAC[HAS_REAL_VECTOR_DERIVATIVE_AT] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                   `gamma:real->A`; `(:real)`; `mfd_covd atlas (g:A->real^N^N) gamma Y`;
                   `\t. (X:A->real^N)((gamma:real->A) t)`; `t:real`] MFD_COVD_METRIC) THEN
    ASM_REWRITE_TAC[IN_UNIV; REAL_OPEN_UNIV; IS_REALINTERVAL_UNIV] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN BINOP_TAC THENL
     [EXPAND_TAC "f2" THEN REWRITE_TAC[FUN_EQ_THM; o_THM];
      AP_TERM_TAC THEN
      SUBGOAL_THEN `mfd_covd atlas (g:A->real^N^N) (gamma:real->A)
                      (\t. (X:A->real^N)(gamma t)) t = vec 0` SUBST1_TAC THENL
       [ASM_SIMP_TAC[IN_UNIV]; ALL_TAC] THEN
      REWRITE_TAC[MATRIX_VECTOR_MUL_RZERO; DOT_RZERO; REAL_ADD_RID] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `t:real` o check (fun th ->
        can (find_term (fun t -> try fst(dest_const t) = "mfd_riemann" with Failure _ -> false))
            (concl th))) THEN
      REWRITE_TAC[IN_UNIV; VECTOR_ARITH `a + b:real^N = vec 0 <=> a = --b`] THEN
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[DOT_LNEG; REAL_NEG_EQ_0] THEN
      MATCH_MP_TAC P2BKF_RIEMANN_DOT_PAR THEN EXISTS_TAC `top:A topology` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!t. (f2:real->real) t = f2 (&0)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`f2:real->real`; `(:real)`] HAS_REAL_DERIVATIVE_ZERO_CONSTANT) THEN
    ASM_SIMP_TAC[IS_REALINTERVAL_UNIV; IN_UNIV; HAS_REAL_DERIVATIVE_ATREAL_WITHIN] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(f2:real->real) (&0) = &0` ASSUME_TAC THENL
   [EXPAND_TAC "f2" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!t. (f1:real->real) t = f1 (&0)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`f1:real->real`; `(:real)`] HAS_REAL_DERIVATIVE_ZERO_CONSTANT) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[IS_REALINTERVAL_UNIV; IN_UNIV] THEN X_GEN_TAC `t:real` THEN
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
      SUBGOAL_THEN `&0 = (f2:real->real) t` SUBST1_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[];
      MESON_TAC[IN_UNIV]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(f1:real->real) (&0) = &0` ASSUME_TAC THENL
   [EXPAND_TAC "f1" THEN ASM_REWRITE_TAC[DOT_LZERO]; ALL_TAC] THEN
  SUBGOAL_THEN `(f1:real->real) (&1) = &0` MP_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  EXPAND_TAC "f1" THEN REWRITE_TAC[]);;

(* KFL.A4 Smoothness of the orbit map z |-> Phi_(z$k)(E z) for a smooth   *)
(* E from real^N: locally the exponential map in a tangent-bundle chart.   *)

let P2BKF_EUCLID_SMOOTH = prove
 (`!(atlas:((A->bool)#(A->real^N))->bool) W (f:real^M->A) c.
     mfd_smooth_map (open_set_atlas (:real^M)) atlas W f /\ c IN atlas
     ==> smooth_map_on {z | z IN W /\ f z IN FST c} (SND c o f)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`((:real^M),(\x:real^M. x))`; `c:(A->bool)#(A->real^N)`] o
    GEN_REWRITE_RULE I [mfd_smooth_map]) THEN
  ASM_REWRITE_TAC[RFB_OPEN_SET_ATLAS_CASES; IMAGE_ID; INTER_UNIV] THEN
  SUBGOAL_THEN `!y:real^M. chart_inv ((:real^M),(\x:real^M. x)) y = y` ASSUME_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`subtopology euclidean (:real^M)`; `open_set_atlas (:real^M)`;
                   `(:real^M)`; `\x:real^M. x`] CHART_INV) THEN
    SIMP_TAC[OPEN_SET_ATLAS; OPEN_UNIV; RFB_OPEN_SET_ATLAS_CASES; IN_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN `SND (c:(A->bool)#(A->real^N)) o (f:real^M->A) o
                chart_inv ((:real^M),(\x:real^M. x)) = SND c o f` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  REWRITE_TAC[]);;

let P2BKF_ORBITMAP_LOCAL = prove
 (`!top atlas (g:A->real^N^N) (X:A->real^N) (E:real^N->A) k z0.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_complete (top,atlas) g /\ p2b_parallel_on atlas g (topspace top) X /\
     1 <= k /\ k <= dimindex(:N) /\
     continuous_map (euclidean,top) E /\
     mfd_smooth_map (open_set_atlas (:real^N)) atlas (:real^N) E
     ==> ?W. open W /\ z0 IN W /\
             continuous_map (subtopology euclidean W,top)
               (\z. mfd_geo (top,atlas) g (E z) (X(E z)) (z$k)) /\
             mfd_smooth_map (open_set_atlas (:real^N)) atlas W
               (\z. mfd_geo (top,atlas) g (E z) (X(E z)) (z$k))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!z:real^N. (E:real^N->A) z IN topspace top` ASSUME_TAC THENL
   [UNDISCH_TAC `continuous_map (euclidean,top) (E:real^N->A)` THEN
    REWRITE_TAC[CONTINUOUS_MAP; SUBSET; FORALL_IN_IMAGE; TOPSPACE_EUCLIDEAN; IN_UNIV] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(E:real^N->A) z0`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^N))->bool) ((E:real^N->A) z0)` THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `W = {z | (E:real^N->A) z IN FST(c:(A->bool)#(A->real^N))}` THEN
  SUBGOAL_THEN `open (W:real^N->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "W" THEN
    UNDISCH_TAC `continuous_map (euclidean,top) (E:real^N->A)` THEN
    REWRITE_TAC[CONTINUOUS_MAP; TOPSPACE_EUCLIDEAN; IN_UNIV] THEN
    DISCH_THEN(MP_TAC o SPEC `FST(c:(A->bool)#(A->real^N))` o CONJUNCT2) THEN
    ASM_REWRITE_TAC[GSYM OPEN_IN] THEN REWRITE_TAC[IN_UNIV];
    ALL_TAC] THEN
  EXISTS_TAC `W:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [EXPAND_TAC "W" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `FST(c:(A->bool)#(A->real^N)) INTER topspace top = FST c` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP OPEN_IN_SUBSET) THEN SET_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `kk = \z:real^N. pastecart (SND (c:(A->bool)#(A->real^N)) ((E:real^N->A) z))
                     ((z:real^N)$k % mfd_vrep atlas (X:A->real^N) c (SND c (E z)))` THEN
  SUBGOAL_THEN `smooth_map_on (W:real^N->bool) (kk:real^N->real^(N,N)finite_sum)` ASSUME_TAC THENL
   [EXPAND_TAC "kk" THEN MATCH_MP_TAC SMOOTH_MAP_ON_PASTECART_OPEN THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `smooth_map_on (W:real^N->bool) (\z. SND (c:(A->bool)#(A->real^N)) ((E:real^N->A) z))`
    ASSUME_TAC THENL
     [MP_TAC(ISPECL [`atlas:((A->bool)#(A->real^N))->bool`; `(:real^N)`; `E:real^N->A`;
                     `c:(A->bool)#(A->real^N)`] P2BKF_EUCLID_SMOOTH) THEN
      ASM_REWRITE_TAC[IN_UNIV] THEN EXPAND_TAC "W" THEN REWRITE_TAC[o_DEF];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(\z:real^N. z$k % mfd_vrep atlas (X:A->real^N) c
                                 (SND (c:(A->bool)#(A->real^N)) ((E:real^N->A) z))) =
                  (\z. drop(lift(z$k)) % (mfd_vrep atlas X c o (\z. SND c (E z))) z)`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_DROP]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_MUL_DROP_OPEN THEN ASM_REWRITE_TAC[ETA_AX] THEN CONJ_TAC THENL
     [SUBGOAL_THEN `(\z:real^N. lift(z$k)) = (\v:real^N. lift(v$k)) o (\z. z)` SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_LINEAR_O THEN
      ASM_REWRITE_TAC[SMOOTH_MAP_ON_ID; linear; VECTOR_ADD_COMPONENT;
                      VECTOR_MUL_COMPONENT; LIFT_ADD; LIFT_CMUL];
      MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
      EXISTS_TAC `IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)` THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL
       [EXPAND_TAC "W" THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
        REPEAT STRIP_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
        FIRST_X_ASSUM(MP_TAC o SPEC `c:(A->bool)#(A->real^N)` o CONJUNCT1 o
          GEN_REWRITE_RULE I [p2b_parallel_on]) THEN
        ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `c:(A->bool)#(A->real^N)`] MFD_EXP_CHART_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `IMAGE (kk:real^N->real^(N,N)finite_sum) W SUBSET
                mfd_exp_chart_dom (top,atlas) (g:A->real^N^N) c` ASSUME_TAC THENL
   [EXPAND_TAC "kk" THEN EXPAND_TAC "W" THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; mfd_exp_chart_dom;
                FSTCART_PASTECART; SNDCART_PASTECART] THEN
    X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`]
                  MFD_COMPLETE_GEO_COMPLETE) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC MFD_COMPLETE_IMP_MCOMPLETE THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_TAC THEN ASM_SIMP_TAC[mfd_exp_dom; IN_ELIM_THM; IN_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z. z IN W
        ==> mfd_geo (top,atlas) (g:A->real^N^N) ((E:real^N->A) z) ((X:A->real^N)(E z)) ((z:real^N)$k) =
            (mfd_exp_chart (top,atlas) g c o (kk:real^N->real^(N,N)finite_sum)) z`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:real^N` THEN EXPAND_TAC "W" THEN REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
    EXPAND_TAC "kk" THEN
    REWRITE_TAC[o_THM; mfd_exp_chart; FSTCART_PASTECART; SNDCART_PASTECART] THEN
    ASM_SIMP_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `(E:real^N->A) z`] CHART_AT) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `chart_jac c (chart_at atlas ((E:real^N->A) z)) (E z)
        ((z:real^N)$k % mfd_vrep atlas (X:A->real^N) c (SND (c:(A->bool)#(A->real^N)) (E z))) =
      z$k % X(E z)` SUBST1_TAC THENL
     [REWRITE_TAC[mfd_vrep] THEN ASM_SIMP_TAC[] THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`;
                     `FST(chart_at (atlas:((A->bool)#(A->real^N))->bool) ((E:real^N->A) z))`;
                     `SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) ((E:real^N->A) z))`; `(E:real^N->A) z`]
                    CHART_JAC_LINEAR) THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `FST(chart_at (atlas:((A->bool)#(A->real^N))->bool) ((E:real^N->A) z))`;
                     `SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) ((E:real^N->A) z))`;
                     `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`; `(E:real^N->A) z`]
                    CHART_JAC_INVERSE) THEN
      ASM_REWRITE_TAC[PAIR; IN_INTER] THEN
      REWRITE_TAC[FUN_EQ_THM; o_THM] THEN REPEAT STRIP_TAC THEN
      ASM_SIMP_TAC[LINEAR_CMUL];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                   `(E:real^N->A) z`; `(X:A->real^N)((E:real^N->A) z)`; `(z:real^N)$k`]
                  MFD_EXP_RADIAL) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`]
                  MFD_COMPLETE_GEO_COMPLETE) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC MFD_COMPLETE_IMP_MCOMPLETE THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_TAC THEN ASM_SIMP_TAC[IN_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN `(kk:real^N->real^(N,N)finite_sum) continuous_on W` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `continuous_map (subtopology euclidean W,top)
                  (mfd_exp_chart (top,atlas) (g:A->real^N^N) c o (kk:real^N->real^(N,N)finite_sum))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
    EXISTS_TAC `subtopology euclidean (mfd_exp_chart_dom (top,atlas) (g:A->real^N^N) c)` THEN
    ASM_REWRITE_TAC[CONTINUOUS_MAP_EUCLIDEAN2];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_MAP_EQ THEN
    EXISTS_TAC `mfd_exp_chart (top,atlas) (g:A->real^N^N) c o (kk:real^N->real^(N,N)finite_sum)` THEN
    ASM_SIMP_TAC[TOPSPACE_SUBTOPOLOGY; TOPSPACE_EUCLIDEAN; INTER_UNIV; IN_INTER; IN_UNIV];
    ALL_TAC] THEN
  MATCH_MP_TAC MFD_SMOOTH_MAP_EQ THEN
  EXISTS_TAC `subtopology euclidean (:real^N)` THEN
  EXISTS_TAC `mfd_exp_chart (top,atlas) (g:A->real^N^N) c o (kk:real^N->real^(N,N)finite_sum)` THEN
  ASM_SIMP_TAC[OPEN_SET_ATLAS; OPEN_UNIV] THEN
  MATCH_MP_TAC (INST_TYPE [`:real^N`,`:A`; `:real^(N,N)finite_sum`,`:B`; `:A`,`:C`;
                           `:N`,`:M`; `:(N,N)finite_sum`,`:N`; `:N`,`:P`]
                MFD_SMOOTH_MAP_COMPOSE) THEN
  MAP_EVERY EXISTS_TAC [`subtopology euclidean (:real^N)`;
                        `subtopology euclidean (:real^(N,N)finite_sum)`;
                        `open_set_atlas (:real^(N,N)finite_sum)`; `top:A topology`;
                        `mfd_exp_chart_dom (top,atlas) (g:A->real^N^N) c`] THEN
  ASM_SIMP_TAC[OPEN_SET_ATLAS; OPEN_UNIV; SUBTOPOLOGY_UNIV; GSYM OPEN_IN;
               SUBTOPOLOGY_SUBTOPOLOGY; INTER_UNIV; MFD_SMOOTH_MAP_OPEN_SET_ATLAS; IN_UNIV] THEN
  REWRITE_TAC[CONTINUOUS_MAP_EUCLIDEAN; CONTINUOUS_MAP_EUCLIDEAN2; SUBSET_UNIV] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[SET_RULE `{x:real^N | x IN s} = s`] THEN ASM_REWRITE_TAC[]);;

let P2BKF_ORBITMAP_SMOOTH = prove
 (`!top atlas (g:A->real^N^N) (X:A->real^N) (E:real^N->A) k.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_complete (top,atlas) g /\ p2b_parallel_on atlas g (topspace top) X /\
     1 <= k /\ k <= dimindex(:N) /\
     continuous_map (euclidean,top) E /\
     mfd_smooth_map (open_set_atlas (:real^N)) atlas (:real^N) E
     ==> continuous_map (euclidean,top) (\z. mfd_geo (top,atlas) g (E z) (X(E z)) (z$k)) /\
         mfd_smooth_map (open_set_atlas (:real^N)) atlas (:real^N)
           (\z. mfd_geo (top,atlas) g (E z) (X(E z)) (z$k))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `continuous_map (euclidean,top)
                  (\z. mfd_geo (top,atlas) (g:A->real^N^N) ((E:real^N->A) z)
                         ((X:A->real^N)(E z)) ((z:real^N)$k))` ASSUME_TAC THENL
   [MATCH_MP_TAC TOPC_CONTINUOUS_MAP_LOCAL THEN
    REWRITE_TAC[TOPSPACE_EUCLIDEAN; IN_UNIV] THEN X_GEN_TAC `z0:real^N` THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                   `X:A->real^N`; `E:real^N->A`; `k:num`; `z0:real^N`] P2BKF_ORBITMAP_LOCAL) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `W:real^N->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `W:real^N->bool` THEN ASM_REWRITE_TAC[GSYM OPEN_IN];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MFDD_SMOOTH_MAP_LOCAL THEN
  MAP_EVERY EXISTS_TAC [`subtopology euclidean (:real^N)`; `top:A topology`] THEN
  ASM_SIMP_TAC[OPEN_SET_ATLAS; OPEN_UNIV; SUBTOPOLOGY_UNIV; GSYM OPEN_IN; TOPSPACE_EUCLIDEAN;
               SUBTOPOLOGY_SUBTOPOLOGY; INTER_UNIV; IN_UNIV; SUBSET_UNIV] THEN
  X_GEN_TAC `z0:real^N` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `X:A->real^N`; `E:real^N->A`; `k:num`; `z0:real^N`] P2BKF_ORBITMAP_LOCAL) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `W:real^N->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `W:real^N->bool` THEN ASM_REWRITE_TAC[GSYM OPEN_IN; SUBSET_UNIV]);;

let P2BKF_EXP_LINEAR_SMOOTH = prove
 (`!top atlas (g:A->real^N^N) x0 (L:real^N->real^N).
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_complete (top,atlas) g /\ x0 IN topspace top /\ linear L
     ==> continuous_map (euclidean,top) (\z. mfd_exp (top,atlas) g x0 (L z)) /\
         mfd_smooth_map (open_set_atlas (:real^N)) atlas (:real^N)
           (\z. mfd_exp (top,atlas) g x0 (L z))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `x0:A`] MFD_EXP_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `mfd_exp_dom (top,atlas) (g:A->real^N^N) x0 = (:real^N)` SUBST1_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`]
                  MFD_COMPLETE_GEO_COMPLETE) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC MFD_COMPLETE_IMP_MCOMPLETE THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_TAC THEN ASM_SIMP_TAC[EXTENSION; mfd_exp_dom; IN_ELIM_THM; IN_UNIV];
    ALL_TAC] THEN
  REWRITE_TAC[SUBTOPOLOGY_UNIV] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(\z. mfd_exp (top,atlas) (g:A->real^N^N) x0 ((L:real^N->real^N) z)) =
                mfd_exp (top,atlas) g x0 o L` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `continuous_map (euclidean,euclidean) (L:real^N->real^N)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[CONTINUOUS_MAP_EUCLIDEAN_EUCLIDEAN; LINEAR_CONTINUOUS_ON]; ALL_TAC] THEN
  CONJ_TAC THENL [MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN EXISTS_TAC `euclidean:(real^N)topology` THEN
                  ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC (INST_TYPE [`:real^N`,`:A`; `:real^N`,`:B`; `:A`,`:C`;
                           `:N`,`:M`; `:N`,`:P`]
                MFD_SMOOTH_MAP_COMPOSE) THEN
  MAP_EVERY EXISTS_TAC [`subtopology euclidean (:real^N)`; `subtopology euclidean (:real^N)`;
                        `open_set_atlas (:real^N)`; `top:A topology`; `(:real^N)`] THEN
  ASM_SIMP_TAC[OPEN_SET_ATLAS; OPEN_UNIV; SUBTOPOLOGY_UNIV; GSYM OPEN_IN; TOPSPACE_EUCLIDEAN;
               SUBTOPOLOGY_SUBTOPOLOGY; INTER_UNIV; SUBSET_UNIV; MFD_SMOOTH_MAP_OPEN_SET_ATLAS;
               IN_UNIV; SET_RULE `{x:real^N | T} = UNIV`] THEN
  SUBGOAL_THEN `(L:real^N->real^N) = L o (\x:real^N. x)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_LINEAR_O THEN ASM_REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_ID]);;

(* KFL.A5 The differential of a map from real^M along a direction, read off *)
(* a curve; the flow-chart map: its z3-derivative is X, and at z3 = 0 its    *)
(* first two partials are horizontal.                                        *)

let P2BKF_DIFF_ALONG_CURVE = prove
 (`!(atlas:((A->bool)#(A->real^N))->bool) (Fm:real^M->A) z v (gamma:real->A) w.
     (\y. SND(chart_at atlas (Fm z)) (Fm y)) differentiable at z /\
     (!t. Fm(z + t % v) = gamma t) /\
     ((\s. SND(chart_at atlas (Fm z)) (gamma(drop s))) has_vector_derivative w)
       (at (lift(&0)))
     ==> mfd_differential (open_set_atlas (:real^M)) atlas Fm z v = w`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[MFD_DIFFERENTIAL_OPEN_SET_ATLAS] THEN
  ABBREV_TAC `H = \y. SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) ((Fm:real^M->A) z)) (Fm y)` THEN
  MATCH_MP_TAC VECTOR_DERIVATIVE_UNIQUE_AT THEN
  MAP_EVERY EXISTS_TAC [`(H:real^M->real^N) o (\s. z + drop s % v)`; `lift(&0)`] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[has_vector_derivative] THEN
    SUBGOAL_THEN `(\h:real^1. drop h % frechet_derivative (H:real^M->real^N) (at z) v) =
                  frechet_derivative H (at z) o (\h. drop h % v)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM] THEN X_GEN_TAC `h:real^1` THEN
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC LINEAR_CMUL THEN
      MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC DIFF_CHAIN_AT THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`(\s:real^1. z:real^M)`; `(\h:real^1. vec 0:real^M)`;
                     `(\s:real^1. drop s % (v:real^M))`; `(\h:real^1. drop h % (v:real^M))`;
                     `at(lift(&0))`] HAS_DERIVATIVE_ADD) THEN
      REWRITE_TAC[HAS_DERIVATIVE_CONST; VECTOR_ADD_LID] THEN
      DISCH_THEN MATCH_MP_TAC THEN MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN
      REWRITE_TAC[linear; DROP_ADD; DROP_CMUL] THEN VECTOR_ARITH_TAC;
      REWRITE_TAC[LIFT_DROP; DROP_VEC; VECTOR_MUL_LZERO; VECTOR_ADD_RID; LIFT_NUM] THEN
      ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS]];
    EXPAND_TAC "H" THEN REWRITE_TAC[o_DEF] THEN ASM_REWRITE_TAC[]]);;

(* KFL.A6 The flow-chart map of a parallel unit field in dimension 3:       *)
(* fmap(z) = Phi_(z$3)(exp_x0(z$1 u1 + z$2 u2)).                             *)

let p2bkf_fmap = new_definition
 `p2bkf_fmap (top:A topology,atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3)
             (X:A->real^3) (x0:A) (u1:real^3) (u2:real^3) =
    \z:real^3. mfd_geo (top,atlas) g (mfd_exp (top,atlas) g x0 (z$1 % u1 + z$2 % u2))
                       (X(mfd_exp (top,atlas) g x0 (z$1 % u1 + z$2 % u2))) (z$3)`;;

let P2BKF_FMAP_SMOOTH = prove
 (`!top atlas (g:A->real^3^3) (X:A->real^3) x0 u1 u2.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_complete (top,atlas) g /\ p2b_parallel_on atlas g (topspace top) X /\
     x0 IN topspace top
     ==> continuous_map (euclidean,top) (p2bkf_fmap (top,atlas) g X x0 u1 u2) /\
         mfd_smooth_map (open_set_atlas (:real^3)) atlas (:real^3)
                        (p2bkf_fmap (top,atlas) g X x0 u1 u2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[p2bkf_fmap] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `X:A->real^3`; `\z:real^3. mfd_exp (top,atlas) (g:A->real^3^3) x0 (z$1 % u1 + z$2 % u2)`;
                 `3`] P2BKF_ORBITMAP_SMOOTH) THEN
  REWRITE_TAC[DIMINDEX_3; ARITH] THEN ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `x0:A`; `\z:real^3. z$1 % (u1:real^3) + z$2 % (u2:real^3)`]
                P2BKF_EXP_LINEAR_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[linear; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN VECTOR_ARITH_TAC);;

let P2BKF_SMOOTH_DIFFABLE = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (Fm:real^M->A) z.
     smooth_manifold_atlas top atlas /\ continuous_map (euclidean,top) Fm /\
     mfd_smooth_map (open_set_atlas (:real^M)) atlas (:real^M) Fm
     ==> (\y. SND(chart_at atlas (Fm z)) (Fm y)) differentiable at z`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(Fm:real^M->A) z IN topspace top` ASSUME_TAC THENL
   [UNDISCH_TAC `continuous_map (euclidean,top) (Fm:real^M->A)` THEN
    REWRITE_TAC[CONTINUOUS_MAP; SUBSET; FORALL_IN_IMAGE; TOPSPACE_EUCLIDEAN; IN_UNIV] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `(Fm:real^M->A) z`]
                CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^N))->bool) ((Fm:real^M->A) z)` THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`atlas:((A->bool)#(A->real^N))->bool`; `(:real^M)`; `Fm:real^M->A`;
                 `c:(A->bool)#(A->real^N)`] P2BKF_EUCLID_SMOOTH) THEN
  ASM_REWRITE_TAC[IN_UNIV] THEN DISCH_TAC THEN
  SUBGOAL_THEN `open {y:real^M | (Fm:real^M->A) y IN FST(c:(A->bool)#(A->real^N))}` ASSUME_TAC THENL
   [UNDISCH_TAC `continuous_map (euclidean,top) (Fm:real^M->A)` THEN
    REWRITE_TAC[CONTINUOUS_MAP; TOPSPACE_EUCLIDEAN; IN_UNIV] THEN
    DISCH_THEN(MP_TAC o SPEC `FST(c:(A->bool)#(A->real^N))` o CONJUNCT2) THEN
    ASM_REWRITE_TAC[GSYM OPEN_IN] THEN REWRITE_TAC[IN_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\y. SND(c:(A->bool)#(A->real^N)) ((Fm:real^M->A) y)) = SND c o Fm` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
  EXISTS_TAC `{y:real^M | (Fm:real^M->A) y IN FST(c:(A->bool)#(A->real^N))}` THEN
  ASM_REWRITE_TAC[IN_ELIM_THM]);;

let P2BKF_ORBIT_VEL0 = prove
 (`!top atlas (g:A->real^N^N) (X:A->real^N) y.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_complete (top,atlas) g /\ p2b_parallel_on atlas g (topspace top) X /\
     y IN topspace top
     ==> ((\s. SND(chart_at atlas y) (mfd_geo (top,atlas) g y (X y) (drop s)))
          has_vector_derivative X y) (at (lift(&0)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `X:A->real^N`; `y:A`] P2BKF_ORBIT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `y:A`; `(X:A->real^N) y`] MFD_GEO_MAXIMAL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `y:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `mfd_geo (top,atlas) (g:A->real^N^N) y ((X:A->real^N) y)`; `(:real)`;
                 `chart_at (atlas:((A->bool)#(A->real^N))->bool) (y:A)`; `&0`]
                MFD_GEODESIC_VEL_CHART) THEN
  ASM_REWRITE_TAC[IN_UNIV] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `FST(chart_at (atlas:((A->bool)#(A->real^N))->bool) (y:A))`;
                 `SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (y:A))`; `y:A`]
                CHART_JAC_SELF) THEN
  ASM_REWRITE_TAC[PAIR] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[LIFT_NUM]);;

let P2BKF_FMAP_D3 = prove
 (`!top atlas (g:A->real^3^3) (X:A->real^3) x0 u1 u2 z.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_complete (top,atlas) g /\ p2b_parallel_on atlas g (topspace top) X /\
     x0 IN topspace top
     ==> mfd_differential (open_set_atlas (:real^3)) atlas (p2bkf_fmap (top,atlas) g X x0 u1 u2)
                          z (basis 3) =
         X(p2bkf_fmap (top,atlas) g X x0 u1 u2 z)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `X:A->real^3`; `x0:A`; `u1:real^3`; `u2:real^3`] P2BKF_FMAP_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!w:real^3. p2bkf_fmap (top,atlas) (g:A->real^3^3) X x0 u1 u2 w IN topspace top`
  ASSUME_TAC THENL
   [UNDISCH_TAC `continuous_map (euclidean,top) (p2bkf_fmap (top,atlas) (g:A->real^3^3) X x0 u1 u2)` THEN
    REWRITE_TAC[CONTINUOUS_MAP; SUBSET; FORALL_IN_IMAGE; TOPSPACE_EUCLIDEAN; IN_UNIV] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!w:real^3. mfd_exp (top,atlas) (g:A->real^3^3) x0 (w$1 % u1 + w$2 % u2) IN topspace top`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `x0:A`; `\z:real^3. z$1 % (u1:real^3) + z$2 % (u2:real^3)`]
                  P2BKF_EXP_LINEAR_SMOOTH) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[linear; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN VECTOR_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[CONTINUOUS_MAP; SUBSET; FORALL_IN_IMAGE; TOPSPACE_EUCLIDEAN; IN_UNIV] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC P2BKF_DIFF_ALONG_CURVE THEN
  EXISTS_TAC `mfd_geo (top,atlas) (g:A->real^3^3) (p2bkf_fmap (top,atlas) g X x0 u1 u2 z)
                      ((X:A->real^3)(p2bkf_fmap (top,atlas) g X x0 u1 u2 z))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC P2BKF_SMOOTH_DIFFABLE THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `t:real` THEN REWRITE_TAC[p2bkf_fmap] THEN
    SIMP_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; BASIS_COMPONENT; DIMINDEX_3; ARITH] THEN
    REWRITE_TAC[REAL_MUL_RZERO; REAL_ADD_RID; REAL_MUL_RID] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `X:A->real^3`;
                   `mfd_exp (top,atlas) (g:A->real^3^3) x0 ((z:real^3)$1 % u1 + z$2 % u2)`]
                  P2BKF_ORBIT_SHIFT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  MATCH_MP_TAC P2BKF_ORBIT_VEL0 THEN ASM_REWRITE_TAC[]);;

let P2BKF_MAP_CURVE_DERIV = prove
 (`!(H:real^M->real^N) y0 u.
     H differentiable at y0
     ==> ((\s. H(y0 + drop s % u)) has_vector_derivative frechet_derivative H (at y0) u)
         (at (lift(&0)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[has_vector_derivative] THEN
  SUBGOAL_THEN `(\h:real^1. drop h % frechet_derivative (H:real^M->real^N) (at y0) u) =
                frechet_derivative H (at y0) o (\h. drop h % u)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM] THEN X_GEN_TAC `h:real^1` THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC LINEAR_CMUL THEN
    MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\s. (H:real^M->real^N)(y0 + drop s % u)) = H o (\s. y0 + drop s % u)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC DIFF_CHAIN_AT THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`(\s:real^1. y0:real^M)`; `(\h:real^1. vec 0:real^M)`;
                   `(\s:real^1. drop s % (u:real^M))`; `(\h:real^1. drop h % (u:real^M))`;
                   `at(lift(&0))`] HAS_DERIVATIVE_ADD) THEN
    REWRITE_TAC[HAS_DERIVATIVE_CONST; VECTOR_ADD_LID] THEN
    DISCH_THEN MATCH_MP_TAC THEN MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN
    REWRITE_TAC[linear; DROP_ADD; DROP_CMUL] THEN VECTOR_ARITH_TAC;
    REWRITE_TAC[LIFT_DROP; DROP_VEC; VECTOR_MUL_LZERO; VECTOR_ADD_RID; LIFT_NUM] THEN
    ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS]]);;

let P2BKF_FMAP_DH = prove
 (`!top atlas (g:A->real^3^3) (X:A->real^3) x0 u1 u2 z d.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_complete (top,atlas) g /\ p2b_parallel_on atlas g (topspace top) X /\
     x0 IN topspace top /\ z$3 = &0 /\ d$3 = &0
     ==> mfd_differential (open_set_atlas (:real^3)) atlas (p2bkf_fmap (top,atlas) g X x0 u1 u2)
                          z d =
         mfd_differential (open_set_atlas (:real^3)) atlas (mfd_exp (top,atlas) g x0)
                          (z$1 % u1 + z$2 % u2) (d$1 % u1 + d$2 % u2) /\
         p2bkf_fmap (top,atlas) g X x0 u1 u2 z = mfd_exp (top,atlas) g x0 (z$1 % u1 + z$2 % u2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `X:A->real^3`; `x0:A`; `u1:real^3`; `u2:real^3`] P2BKF_FMAP_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `x0:A`; `\y:real^3. y`] P2BKF_EXP_LINEAR_SMOOTH) THEN
  ASM_REWRITE_TAC[LINEAR_ID; ETA_AX] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!y:real^3. mfd_exp (top,atlas) (g:A->real^3^3) x0 y IN topspace top`
  ASSUME_TAC THENL
   [UNDISCH_TAC `continuous_map (euclidean,top) (mfd_exp (top,atlas) (g:A->real^3^3) x0)` THEN
    REWRITE_TAC[CONTINUOUS_MAP; SUBSET; FORALL_IN_IMAGE; TOPSPACE_EUCLIDEAN; IN_UNIV] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!w:real^3. w$3 = &0
                ==> p2bkf_fmap (top,atlas) (g:A->real^3^3) X x0 u1 u2 w =
                    mfd_exp (top,atlas) g x0 (w$1 % u1 + w$2 % u2)` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[p2bkf_fmap] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `mfd_exp (top,atlas) (g:A->real^3^3) x0 ((w:real^3)$1 % u1 + w$2 % u2)`;
                   `(X:A->real^3)(mfd_exp (top,atlas) (g:A->real^3^3) x0 ((w:real^3)$1 % u1 + w$2 % u2))`]
                  MFD_GEO_MAXIMAL) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL [ALL_TAC; FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]] THEN
  MATCH_MP_TAC P2BKF_DIFF_ALONG_CURVE THEN
  EXISTS_TAC `\t. mfd_exp (top,atlas) (g:A->real^3^3) x0
                     (((z:real^3)$1 % u1 + z$2 % u2) + t % ((d:real^3)$1 % u1 + d$2 % u2))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC P2BKF_SMOOTH_DIFFABLE THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `t:real` THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `((z:real^3) + t % d)$3 = &0` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN AP_TERM_TAC THEN
    REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN REWRITE_TAC[MFD_DIFFERENTIAL_OPEN_SET_ATLAS] THEN
  MATCH_MP_TAC P2BKF_MAP_CURVE_DERIV THEN
  MATCH_MP_TAC P2BKF_SMOOTH_DIFFABLE THEN EXISTS_TAC `top:A topology` THEN
  ASM_REWRITE_TAC[ETA_AX]);;

let P2BKF_FMAP_HORIZ = prove
 (`!top atlas (g:A->real^3^3) (X:A->real^3) x0 u1 u2 z d.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_complete (top,atlas) g /\ p2b_parallel_on atlas g (topspace top) X /\
     x0 IN topspace top /\
     u1 dot (g x0 ** X x0) = &0 /\ u2 dot (g x0 ** X x0) = &0 /\
     z$3 = &0 /\ d$3 = &0
     ==> mfd_differential (open_set_atlas (:real^3)) atlas (p2bkf_fmap (top,atlas) g X x0 u1 u2)
                          z d dot
         (g (p2bkf_fmap (top,atlas) g X x0 u1 u2 z) ** X (p2bkf_fmap (top,atlas) g X x0 u1 u2 z)) =
         &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `X:A->real^3`; `x0:A`; `u1:real^3`; `u2:real^3`; `z:real^3`; `d:real^3`]
                P2BKF_FMAP_DH) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN SUBST1_TAC) THEN
  MATCH_MP_TAC P2BKF_HORIZ THEN ASM_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[DOT_LADD; DOT_LMUL] THEN REAL_ARITH_TAC);;

let P2BKF_FMAP_D0 = prove
 (`!top atlas (g:A->real^3^3) (X:A->real^3) x0 u1 u2 h.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_complete (top,atlas) g /\ p2b_parallel_on atlas g (topspace top) X /\
     x0 IN topspace top
     ==> p2bkf_fmap (top,atlas) g X x0 u1 u2 (vec 0) = x0 /\
         mfd_differential (open_set_atlas (:real^3)) atlas (p2bkf_fmap (top,atlas) g X x0 u1 u2)
                          (vec 0) h =
         h$1 % u1 + h$2 % u2 + h$3 % X x0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `X:A->real^3`; `x0:A`; `u1:real^3`; `u2:real^3`; `vec 0:real^3`;
                 `h - (h:real^3)$3 % basis 3`] P2BKF_FMAP_DH) THEN
  ASM_SIMP_TAC[VEC_COMPONENT; VECTOR_SUB_COMPONENT; VECTOR_MUL_COMPONENT; BASIS_COMPONENT;
               DIMINDEX_3; ARITH; REAL_MUL_RID; REAL_SUB_REFL; VECTOR_MUL_LZERO;
               VECTOR_ADD_LID; REAL_MUL_RZERO; REAL_SUB_RZERO] THEN
  ASM_SIMP_TAC[MFD_EXP_DOM] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `x0:A`] MFD_EXP_DIFFERENTIAL_ZERO) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `X:A->real^3`; `x0:A`; `u1:real^3`; `u2:real^3`; `vec 0:real^3`]
                P2BKF_FMAP_D3) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `X:A->real^3`; `x0:A`; `u1:real^3`; `u2:real^3`] P2BKF_FMAP_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `linear (mfd_differential (open_set_atlas (:real^3)) atlas
                         (p2bkf_fmap (top,atlas) (g:A->real^3^3) X x0 u1 u2) (vec 0))` ASSUME_TAC THENL
   [REWRITE_TAC[MFD_DIFFERENTIAL_OPEN_SET_ATLAS] THEN MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
    MATCH_MP_TAC P2BKF_SMOOTH_DIFFABLE THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
  SUBGOAL_THEN `h:real^3 = (h - h$3 % basis 3) + h$3 % basis 3` SUBST1_TAC THENL
   [VECTOR_ARITH_TAC; ALL_TAC] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LINEAR_ADD th; MATCH_MP LINEAR_CMUL th]) THEN
  ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[MFD_EXP_DOM; VECTOR_SUB_COMPONENT; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
               BASIS_COMPONENT; DIMINDEX_3; ARITH] THEN
  REWRITE_TAC[REAL_MUL_RZERO; REAL_SUB_RZERO; REAL_ADD_RID; REAL_MUL_RID] THEN
  CONV_TAC VECTOR_ARITH);;

let P2BKF_FMAP_PARAM = prove
 (`!top atlas (g:A->real^3^3) (X:A->real^3) x0 u1 u2.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_complete (top,atlas) g /\ p2b_parallel_on atlas g (topspace top) X /\
     x0 IN topspace top /\
     (!a b c. a % u1 + b % u2 + c % X x0 = vec 0 ==> a = &0 /\ b = &0 /\ c = &0)
     ==> ?V. open V /\ vec 0 IN V /\
             mfd_param top atlas V (p2bkf_fmap (top,atlas) g X x0 u1 u2)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `X:A->real^3`; `x0:A`; `u1:real^3`; `u2:real^3`] P2BKF_FMAP_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `p2bkf_fmap (top,atlas) (g:A->real^3^3) X x0 u1 u2`; `(:real^3)`; `vec 0:real^3`]
                MFD_LOCAL_PARAM) THEN
  ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV; SUBTOPOLOGY_UNIV; SUBSET_UNIV] THEN
  ANTS_TAC THENL
   [X_GEN_TAC `h:real^3` THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `X:A->real^3`; `x0:A`; `u1:real^3`; `u2:real^3`; `h:real^3`] P2BKF_FMAP_D0) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`(h:real^3)$1`; `(h:real^3)$2`; `(h:real^3)$3`]) THEN
    ASM_REWRITE_TAC[] THEN
    SIMP_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VEC_COMPONENT];
    ALL_TAC] THEN
  MESON_TAC[]);;

(* KFL.A11 Killing property of a parallel field in coordinates: if the      *)
(* coordinate field e of h is the parallel field W, the inner products of   *)
(* coordinate fields do not change along e (GEOC_DOT_DERIV).                *)

let P2BKF_KILLING_CHART = prove
 (`!U (G:real^N->real^N^N) (W:real^N->real^N) (h:real^N->real^N) s z e a b.
     metric_field U G /\ smooth_map_on U W /\
     (!y w. y IN U ==> frechet_derivative W (at y) w + christoffel G y w (W y) = vec 0) /\
     open s /\ smooth_map_on s h /\ IMAGE h s SUBSET U /\ z IN s /\
     (!z'. z' IN s ==> frechet_derivative h (at z') e = W(h z'))
     ==> ((\t. lift(frechet_derivative h (at (z + drop t % e)) a dot
                    (G(h(z + drop t % e)) ** frechet_derivative h (at (z + drop t % e)) b)))
          has_vector_derivative lift(&0)) (at (lift(&0)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(h:real^N->real^N) z IN U` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!z'. z' IN s ==> (h:real^N->real^N) differentiable at z'` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!c. ((\t. frechet_derivative (h:real^N->real^N) (at (z + drop t % e)) c) has_vector_derivative
         --(christoffel (G:real^N->real^N^N) (h z) (W(h z)) (frechet_derivative h (at z) c)))
        (at (lift(&0)))`
  ASSUME_TAC THENL
   [X_GEN_TAC `c:real^N` THEN
    SUBGOAL_THEN `(\z'. frechet_derivative (h:real^N->real^N) (at z') c) differentiable at z`
    ASSUME_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `s:real^N->bool` THEN
      ASM_SIMP_TAC[SMOOTH_MAP_ON_FRECHET_DERIVATIVE];
      ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o SPEC `e:real^N` o MATCH_MP P2BKF_MAP_CURVE_DERIV) THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    SUBGOAL_THEN `frechet_derivative (\z'. frechet_derivative (h:real^N->real^N) (at z') c) (at z) e =
                  dd2 h z e c` SUBST1_TAC THENL [REWRITE_TAC[dd2]; ALL_TAC] THEN
    MP_TAC(ISPECL [`s:real^N->bool`; `h:real^N->real^N`; `z:real^N`; `e:real^N`; `c:real^N`]
                  LRG_DD2_SYM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[dd2] THEN
    SUBGOAL_THEN `frechet_derivative (\z'. frechet_derivative (h:real^N->real^N) (at z') e) (at z) =
                  frechet_derivative (W:real^N->real^N) (at (h z)) o frechet_derivative h (at z)`
    SUBST1_TAC THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
      MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_WITHIN_OPEN THEN
      EXISTS_TAC `(W:real^N->real^N) o (h:real^N->real^N)` THEN
      EXISTS_TAC `s:real^N->bool` THEN ASM_SIMP_TAC[o_THM] THEN
      MATCH_MP_TAC DIFF_CHAIN_AT THEN
      ASM_SIMP_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `U:real^N->bool` THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[metric_field];
      ALL_TAC] THEN
    REWRITE_TAC[o_THM] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`(h:real^N->real^N) z`;
                                  `frechet_derivative (h:real^N->real^N) (at z) c`] o
      check (fun th -> can (find_term (fun t -> try fst(dest_const t) = "christoffel"
                                                  with Failure _ -> false)) (concl th))) THEN
    ASM_REWRITE_TAC[VECTOR_ARITH `a + b:real^N = vec 0 <=> a = --b`] THEN
    DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC CHRISTOFFEL_SYM THEN EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `((\t. (h:real^N->real^N)(z + drop t % e)) has_vector_derivative W(h z))
                (at (lift(&0)))` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPEC `e:real^N` o MATCH_MP P2BKF_MAP_CURVE_DERIV o
      C MP (ASSUME `(z:real^N) IN s`) o SPEC `z:real^N`) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `\t. (h:real^N->real^N)(z + t % e)`;
                 `(W:real^N->real^N)((h:real^N->real^N) z)`;
                 `\t. frechet_derivative (h:real^N->real^N) (at (z + t % e)) a`;
                 `--(christoffel (G:real^N->real^N^N) ((h:real^N->real^N) z) (W(h z))
                                 (frechet_derivative h (at z) a))`;
                 `\t. frechet_derivative (h:real^N->real^N) (at (z + t % e)) b`;
                 `--(christoffel (G:real^N->real^N^N) ((h:real^N->real^N) z) (W(h z))
                                 (frechet_derivative h (at z) b))`; `&0`] GEOC_DOT_DERIV) THEN
  ASM_REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_RID; LIFT_NUM] THEN
  ASM_REWRITE_TAC[GSYM LIFT_NUM] THEN
  REWRITE_TAC[VECTOR_ARITH `--a + a:real^N = vec 0`; DOT_LZERO; MATRIX_VECTOR_MUL_RZERO;
              DOT_RZERO; REAL_ADD_LID]);;

let P2BKF_CHART_DIFF = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (Fm:real^M->A) z c.
     smooth_manifold_atlas top atlas /\ c IN atlas /\ Fm z IN FST c /\
     continuous_map (euclidean,top) Fm /\
     mfd_smooth_map (open_set_atlas (:real^M)) atlas (:real^M) Fm
     ==> ((\y. SND c (Fm y)) has_derivative
          (chart_jac (chart_at atlas (Fm z)) c (Fm z) o
           mfd_differential (open_set_atlas (:real^M)) atlas Fm z)) (at z)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(Fm:real^M->A) z IN topspace top` ASSUME_TAC THENL
   [UNDISCH_TAC `continuous_map (euclidean,top) (Fm:real^M->A)` THEN
    REWRITE_TAC[CONTINUOUS_MAP; SUBSET; FORALL_IN_IMAGE; TOPSPACE_EUCLIDEAN; IN_UNIV] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `(Fm:real^M->A) z`]
                CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `p = chart_at (atlas:((A->bool)#(A->real^N))->bool) ((Fm:real^M->A) z)` THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `p:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `O = {y:real^M | (Fm:real^M->A) y IN FST(p:(A->bool)#(A->real^N)) INTER FST(c:(A->bool)#(A->real^N))}` THEN
  SUBGOAL_THEN `open (O:real^M->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "O" THEN
    UNDISCH_TAC `continuous_map (euclidean,top) (Fm:real^M->A)` THEN
    REWRITE_TAC[CONTINUOUS_MAP; TOPSPACE_EUCLIDEAN; IN_UNIV] THEN
    DISCH_THEN(MP_TAC o SPEC `FST(p:(A->bool)#(A->real^N)) INTER FST(c:(A->bool)#(A->real^N))` o
      CONJUNCT2) THEN
    ASM_SIMP_TAC[OPEN_IN_INTER; GSYM OPEN_IN] THEN REWRITE_TAC[IN_UNIV];
    ALL_TAC] THEN
  MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_WITHIN_OPEN THEN
  EXISTS_TAC `chart_trans (p:(A->bool)#(A->real^N)) c o (\y. SND p ((Fm:real^M->A) y))` THEN
  EXISTS_TAC `O:real^M->bool` THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [EXPAND_TAC "O" THEN REWRITE_TAC[IN_ELIM_THM; IN_INTER] THEN ASM_REWRITE_TAC[];
    EXPAND_TAC "O" THEN REWRITE_TAC[IN_ELIM_THM; IN_INTER; o_THM; chart_trans] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC DIFF_CHAIN_AT THEN CONJ_TAC THENL
   [REWRITE_TAC[GSYM MFD_DIFFERENTIAL_OPEN_SET_ATLAS] THEN
    ONCE_REWRITE_TAC[MFD_DIFFERENTIAL_OPEN_SET_ATLAS] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `Fm:real^M->A`;
                   `z:real^M`] P2BKF_SMOOTH_DIFFABLE) THEN
    ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `FST(p:(A->bool)#(A->real^N))`; `SND(p:(A->bool)#(A->real^N))`;
                   `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`;
                   `(Fm:real^M->A) z`] CHART_TRANS_HAS_DERIVATIVE) THEN
    ASM_REWRITE_TAC[PAIR; IN_INTER]]);;

let P2BKF_GE2_DERIV0 = prove
 (`!top atlas (g:A->real^3^3) (g2:A->real^3^3) (X:A->real^3) x0 u1 u2 z0 a b.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_complete (top,atlas) g /\ p2b_parallel_on atlas g (topspace top) X /\
     riemannian_metric atlas g2 /\ p2b_parallel_on atlas g2 (topspace top) X /\
     x0 IN topspace top
     ==> ((\t. mfd_differential (open_set_atlas (:real^3)) atlas
                 (p2bkf_fmap (top,atlas) g X x0 u1 u2) (z0 + t % basis 3) a dot
               (g2 (p2bkf_fmap (top,atlas) g X x0 u1 u2 (z0 + t % basis 3)) **
                mfd_differential (open_set_atlas (:real^3)) atlas
                 (p2bkf_fmap (top,atlas) g X x0 u1 u2) (z0 + t % basis 3) b))
          has_real_derivative &0) (atreal (&0))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `X:A->real^3`; `x0:A`; `u1:real^3`; `u2:real^3`] P2BKF_FMAP_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `fm = p2bkf_fmap (top,atlas) (g:A->real^3^3) X x0 u1 u2` THEN
  SUBGOAL_THEN `!w:real^3. (fm:real^3->A) w IN topspace top` ASSUME_TAC THENL
   [UNDISCH_TAC `continuous_map (euclidean,top) (fm:real^3->A)` THEN
    REWRITE_TAC[CONTINUOUS_MAP; SUBSET; FORALL_IN_IMAGE; TOPSPACE_EUCLIDEAN; IN_UNIV] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `(fm:real^3->A) z0`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^3))->bool) ((fm:real^3->A) z0)` THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `c:(A->bool)#(A->real^3)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `s = {w:real^3 | (fm:real^3->A) w IN FST(c:(A->bool)#(A->real^3))}` THEN
  SUBGOAL_THEN `open (s:real^3->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN
    UNDISCH_TAC `continuous_map (euclidean,top) (fm:real^3->A)` THEN
    REWRITE_TAC[CONTINUOUS_MAP; TOPSPACE_EUCLIDEAN; IN_UNIV] THEN
    DISCH_THEN(MP_TAC o SPEC `FST(c:(A->bool)#(A->real^3))` o CONJUNCT2) THEN
    ASM_REWRITE_TAC[GSYM OPEN_IN] THEN REWRITE_TAC[IN_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN `(z0:real^3) IN s` ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `FST(c:(A->bool)#(A->real^3)) INTER topspace top = FST c` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP OPEN_IN_SUBSET) THEN SET_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `hh = \w:real^3. SND (c:(A->bool)#(A->real^3)) ((fm:real^3->A) w)` THEN
  SUBGOAL_THEN `!w. w IN s ==> frechet_derivative (hh:real^3->real^3) (at w) =
                               chart_jac (chart_at atlas ((fm:real^3->A) w)) (c:(A->bool)#(A->real^3)) (fm w) o
                               mfd_differential (open_set_atlas (:real^3)) atlas fm w`
  ASSUME_TAC THENL
   [X_GEN_TAC `w:real^3` THEN EXPAND_TAC "s" THEN REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN EXPAND_TAC "hh" THEN
    MATCH_MP_TAC P2BKF_CHART_DIFF THEN EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t. (z0 + t % basis 3:real^3) IN s
        ==> mfd_differential (open_set_atlas (:real^3)) atlas (fm:real^3->A) (z0 + t % basis 3) a dot
            ((g2:A->real^3^3) (fm (z0 + t % basis 3)) **
             mfd_differential (open_set_atlas (:real^3)) atlas fm (z0 + t % basis 3) b) =
            frechet_derivative (hh:real^3->real^3) (at (z0 + t % basis 3)) a dot
            (metric_local atlas (c:(A->bool)#(A->real^3)) g2 (hh(z0 + t % basis 3)) **
             frechet_derivative hh (at (z0 + t % basis 3)) b)`
  ASSUME_TAC THENL
   [X_GEN_TAC `t:real` THEN DISCH_TAC THEN ASM_SIMP_TAC[o_THM] THEN
    EXPAND_TAC "hh" THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC GEOC_BILIN_CHART THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(z0 + t % basis 3:real^3) IN s` THEN EXPAND_TAC "s" THEN
    REWRITE_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (SND(c:(A->bool)#(A->real^3))) (FST c)`;
                 `metric_local atlas (c:(A->bool)#(A->real^3)) (g2:A->real^3^3)`;
                 `mfd_vrep atlas (X:A->real^3) (c:(A->bool)#(A->real^3))`;
                 `hh:real^3->real^3`; `s:real^3->bool`; `z0:real^3`; `basis 3:real^3`;
                 `a:real^3`; `b:real^3`] P2BKF_KILLING_CHART) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `riemannian_metric atlas (g2:A->real^3^3)` THEN
      REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `p2b_parallel_on atlas (g2:A->real^3^3) (topspace top) X` THEN
      DISCH_THEN(MP_TAC o SPEC `c:(A->bool)#(A->real^3)` o CONJUNCT1 o
        GEN_REWRITE_RULE I [p2b_parallel_on]) THEN ASM_REWRITE_TAC[];
      REPEAT STRIP_TAC THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g2:A->real^3^3`;
                     `X:A->real^3`; `c:(A->bool)#(A->real^3)`; `y:real^3`] P2BKF_VREP_DIFF) THEN
      ASM_SIMP_TAC[];
      ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`atlas:((A->bool)#(A->real^3))->bool`; `(:real^3)`; `fm:real^3->A`;
                     `c:(A->bool)#(A->real^3)`] P2BKF_EUCLID_SMOOTH) THEN
      ASM_REWRITE_TAC[IN_UNIV; o_DEF] THEN DISCH_TAC THEN
      EXPAND_TAC "hh" THEN EXPAND_TAC "s" THEN ASM_REWRITE_TAC[];
      EXPAND_TAC "hh" THEN EXPAND_TAC "s" THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN ASM_SIMP_TAC[o_THM] THEN
      EXPAND_TAC "fm" THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                     `X:A->real^3`; `x0:A`; `u1:real^3`; `u2:real^3`; `w:real^3`]
                    P2BKF_FMAP_D3) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      UNDISCH_TAC `(w:real^3) IN s` THEN EXPAND_TAC "s" THEN REWRITE_TAC[IN_ELIM_THM] THEN
      EXPAND_TAC "fm" THEN DISCH_TAC THEN EXPAND_TAC "hh" THEN
      REWRITE_TAC[mfd_vrep] THEN EXPAND_TAC "fm" THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `?d. &0 < d /\ !t. abs t < d ==> (z0 + t % basis 3:real^3) IN s` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `open (s:real^3->bool)` THEN REWRITE_TAC[OPEN_CONTAINS_BALL] THEN
    DISCH_THEN(MP_TAC o SPEC `z0:real^3`) THEN ASM_REWRITE_TAC[SUBSET; IN_BALL] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `t:real` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[dist; VECTOR_ARITH `z - (z + t % b:real^3) = --(t % b)`; NORM_NEG; NORM_MUL] THEN
    SIMP_TAC[NORM_BASIS; DIMINDEX_3; ARITH] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_TRANSFORM_ATREAL THEN
  EXISTS_TAC `\t. frechet_derivative (hh:real^3->real^3) (at (z0 + t % basis 3)) a dot
                  (metric_local atlas (c:(A->bool)#(A->real^3)) (g2:A->real^3^3) (hh(z0 + t % basis 3)) **
                   frechet_derivative hh (at (z0 + t % basis 3)) b)` THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `t:real` THEN REWRITE_TAC[REAL_SUB_RZERO] THEN DISCH_TAC THEN
    CONV_TAC SYM_CONV THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (find_term (fun t -> try fst(dest_const t) = "metric_local" with Failure _ -> false))
          (concl th) && is_forall(concl th))) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[HAS_REAL_VECTOR_DERIVATIVE_AT; o_DEF; LIFT_NUM] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    can (find_term (fun t -> try fst(dest_const t) = "has_vector_derivative" with Failure _ -> false))
        (concl th))) THEN
  REWRITE_TAC[LIFT_NUM]);;

let P2BKF_FMAP_METRIC_INV2 = prove
 (`!top atlas (g:A->real^3^3) (g2:A->real^3^3) (X:A->real^3) x0 u1 u2 z t a b.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_complete (top,atlas) g /\ p2b_parallel_on atlas g (topspace top) X /\
     riemannian_metric atlas g2 /\ p2b_parallel_on atlas g2 (topspace top) X /\
     x0 IN topspace top
     ==> mfd_differential (open_set_atlas (:real^3)) atlas
           (p2bkf_fmap (top,atlas) g X x0 u1 u2) (z + t % basis 3) a dot
         (g2 (p2bkf_fmap (top,atlas) g X x0 u1 u2 (z + t % basis 3)) **
          mfd_differential (open_set_atlas (:real^3)) atlas
           (p2bkf_fmap (top,atlas) g X x0 u1 u2) (z + t % basis 3) b) =
         mfd_differential (open_set_atlas (:real^3)) atlas
           (p2bkf_fmap (top,atlas) g X x0 u1 u2) z a dot
         (g2 (p2bkf_fmap (top,atlas) g X x0 u1 u2 z) **
          mfd_differential (open_set_atlas (:real^3)) atlas
           (p2bkf_fmap (top,atlas) g X x0 u1 u2) z b)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `phi = \t. mfd_differential (open_set_atlas (:real^3)) atlas
           (p2bkf_fmap (top,atlas) (g:A->real^3^3) X x0 u1 u2) ((z:real^3) + t % basis 3) a dot
         (g2 (p2bkf_fmap (top,atlas) g X x0 u1 u2 (z + t % basis 3)) **
          mfd_differential (open_set_atlas (:real^3)) atlas
           (p2bkf_fmap (top,atlas) g X x0 u1 u2) (z + t % basis 3) b)` THEN
  SUBGOAL_THEN `!t0. ((phi:real->real) has_real_derivative &0) (atreal t0)` ASSUME_TAC THENL
   [X_GEN_TAC `t0:real` THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `g2:A->real^3^3`; `X:A->real^3`; `x0:A`; `u1:real^3`; `u2:real^3`;
                   `(z:real^3) + t0 % basis 3`; `a:real^3`; `b:real^3`] P2BKF_GE2_DERIV0) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`\t:real. t - t0`;
                   `\t. mfd_differential (open_set_atlas (:real^3)) atlas
                          (p2bkf_fmap (top,atlas) (g:A->real^3^3) X x0 u1 u2)
                          (((z:real^3) + t0 % basis 3) + t % basis 3) a dot
                        (g2 (p2bkf_fmap (top,atlas) g X x0 u1 u2 ((z + t0 % basis 3) + t % basis 3)) **
                         mfd_differential (open_set_atlas (:real^3)) atlas
                          (p2bkf_fmap (top,atlas) g X x0 u1 u2) ((z + t0 % basis 3) + t % basis 3) b)`;
                   `&1`; `&0`; `t0:real`] REAL_DIFF_CHAIN_ATREAL) THEN
    REWRITE_TAC[REAL_SUB_REFL; REAL_MUL_LZERO] THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      MP_TAC(SPECL [`\t:real. t`; `&1`; `\t:real. t0:real`; `&0`; `atreal t0`]
                   HAS_REAL_DERIVATIVE_SUB) THEN
      REWRITE_TAC[HAS_REAL_DERIVATIVE_ID; HAS_REAL_DERIVATIVE_CONST; REAL_SUB_RZERO];
      ALL_TAC] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    EXPAND_TAC "phi" THEN REWRITE_TAC[FUN_EQ_THM; o_THM] THEN X_GEN_TAC `t:real` THEN
    REWRITE_TAC[VECTOR_ARITH `(z + t0 % b) + (t - t0) % b:real^3 = z + t % b`];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`phi:real->real`; `(:real)`] HAS_REAL_DERIVATIVE_ZERO_CONSTANT) THEN
  ASM_SIMP_TAC[IS_REALINTERVAL_UNIV; IN_UNIV; HAS_REAL_DERIVATIVE_ATREAL_WITHIN] THEN
  DISCH_THEN(X_CHOOSE_TAC `k:real`) THEN
  FIRST_ASSUM(MP_TAC o SPEC `t:real`) THEN FIRST_X_ASSUM(MP_TAC o SPEC `&0`) THEN
  EXPAND_TAC "phi" THEN REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_RID] THEN
  REAL_ARITH_TAC);;

let P2BKF_FMAP_HORIZ_ALL = prove
 (`!top atlas (g:A->real^3^3) (g2:A->real^3^3) (X:A->real^3) x0 u1 u2 z a.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_complete (top,atlas) g /\ p2b_parallel_on atlas g (topspace top) X /\
     riemannian_metric atlas g2 /\ p2b_parallel_on atlas g2 (topspace top) X /\
     (!y. y IN topspace top ==> g2 y ** X y = g y ** X y) /\
     x0 IN topspace top /\
     u1 dot (g x0 ** X x0) = &0 /\ u2 dot (g x0 ** X x0) = &0 /\ a$3 = &0
     ==> mfd_differential (open_set_atlas (:real^3)) atlas (p2bkf_fmap (top,atlas) g X x0 u1 u2)
                          z a dot
         (g2 (p2bkf_fmap (top,atlas) g X x0 u1 u2 z) ** X (p2bkf_fmap (top,atlas) g X x0 u1 u2 z)) =
         &0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `X:A->real^3`; `x0:A`; `u1:real^3`; `u2:real^3`] P2BKF_FMAP_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!w:real^3. p2bkf_fmap (top,atlas) (g:A->real^3^3) X x0 u1 u2 w IN topspace top`
  ASSUME_TAC THENL
   [UNDISCH_TAC `continuous_map (euclidean,top) (p2bkf_fmap (top,atlas) (g:A->real^3^3) X x0 u1 u2)` THEN
    REWRITE_TAC[CONTINUOUS_MAP; SUBSET; FORALL_IN_IMAGE; TOPSPACE_EUCLIDEAN; IN_UNIV] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `z' = (z:real^3) - z$3 % basis 3` THEN
  SUBGOAL_THEN `(z':real^3)$3 = &0 /\ z = z' + z$3 % basis 3` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "z'" THEN CONJ_TAC THENL
     [SIMP_TAC[VECTOR_SUB_COMPONENT; VECTOR_MUL_COMPONENT; BASIS_COMPONENT; DIMINDEX_3; ARITH] THEN
      REAL_ARITH_TAC;
      VECTOR_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `g2:A->real^3^3`; `X:A->real^3`; `x0:A`; `u1:real^3`; `u2:real^3`;
                 `z':real^3`; `(z:real^3)$3`; `a:real^3`; `basis 3:real^3`]
                P2BKF_FMAP_METRIC_INV2) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [SYM th] THEN
                          ASSUME_TAC th) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `X:A->real^3`; `x0:A`; `u1:real^3`; `u2:real^3`] P2BKF_FMAP_D3) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_SIMP_TAC[] THEN MATCH_MP_TAC P2BKF_FMAP_HORIZ THEN ASM_REWRITE_TAC[]);;

let P2BKF_HCOMPLEMENT = prove
 (`!(w:real^3) (x:real^3).
     x dot w = &1
     ==> ?u1 u2. u1 dot w = &0 /\ u2 dot w = &0 /\
                 (!a b c. a % u1 + b % u2 + c % x = vec 0 ==> a = &0 /\ b = &0 /\ c = &0)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(w:real^3 = vec 0)` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `(x:real^3) dot w = &1` THEN
    ASM_REWRITE_TAC[DOT_RZERO] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPEC `{y:real^3 | w dot y = &0}` ORTHONORMAL_BASIS_SUBSPACE) THEN
  REWRITE_TAC[SUBSPACE_HYPERPLANE] THEN
  ASM_SIMP_TAC[DIM_HYPERPLANE; DIMINDEX_3] THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN(X_CHOOSE_THEN `bb:real^3->bool` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o CONV_RULE HAS_SIZE_CONV) THEN
  DISCH_THEN(X_CHOOSE_THEN `u1:real^3` (X_CHOOSE_THEN `u2:real^3` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `(w:real^3) dot u1 = &0 /\ w dot u2 = &0` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(bb:real^3->bool) SUBSET {y | w dot y = &0}` THEN
    ASM_REWRITE_TAC[INSERT_SUBSET; IN_ELIM_THM] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(u1:real^3) dot u2 = &0` ASSUME_TAC THENL
   [UNDISCH_TAC `pairwise orthogonal (bb:real^3->bool)` THEN
    ASM_REWRITE_TAC[pairwise; IN_INSERT; NOT_IN_EMPTY; orthogonal] THEN
    DISCH_THEN(MP_TAC o SPECL [`u1:real^3`; `u2:real^3`]) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(u1:real^3) dot u1 = &1 /\ (u2:real^3) dot u2 = &1` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM NORM_EQ_1] THEN CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[IN_INSERT];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`u1:real^3`; `u2:real^3`] THEN
  ONCE_REWRITE_TAC[DOT_SYM] THEN ASM_REWRITE_TAC[] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `c = &0` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o AP_TERM `\v:real^3. w dot v`) THEN
    REWRITE_TAC[DOT_RADD; DOT_RMUL; DOT_RZERO] THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[DOT_SYM] THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `a % u1 + b % u2 + c % (x:real^3) = vec 0` THEN
  ASM_REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_RID] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(u2:real^3) dot u1 = &0` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[DOT_SYM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o AP_TERM `\v:real^3. u1 dot v`);
    FIRST_X_ASSUM(MP_TAC o AP_TERM `\v:real^3. u2 dot v`)] THEN
  REWRITE_TAC[DOT_RADD; DOT_RMUL; DOT_RZERO] THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let P2BKF_MDIFF_CHAIN = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) top' (atlas':((B->bool)#(B->real^N))->bool)
    (Fm:real^M->A) (F1:A->B) W z.
     smooth_manifold_atlas top atlas /\ smooth_manifold_atlas top' atlas' /\
     continuous_map (euclidean,top) Fm /\
     mfd_smooth_map (open_set_atlas (:real^M)) atlas (:real^M) Fm /\
     open_in top W /\ Fm z IN W /\ continuous_map (subtopology top W,top') F1 /\
     mfd_smooth_map atlas atlas' W F1
     ==> mfd_differential (open_set_atlas (:real^M)) atlas' (F1 o Fm) z =
         mfd_differential atlas atlas' F1 (Fm z) o
         mfd_differential (open_set_atlas (:real^M)) atlas Fm z`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(Fm:real^M->A) z IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `(F1:A->B) ((Fm:real^M->A) z) IN topspace top'` ASSUME_TAC THENL
   [UNDISCH_TAC `continuous_map (subtopology top W,top') (F1:A->B)` THEN
    REWRITE_TAC[CONTINUOUS_MAP; SUBSET; FORALL_IN_IMAGE; TOPSPACE_SUBTOPOLOGY; IN_INTER] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `(Fm:real^M->A) z`]
                CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `p = chart_at (atlas:((A->bool)#(A->real^N))->bool) ((Fm:real^M->A) z)` THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                 `(F1:A->B) ((Fm:real^M->A) z)`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `p' = chart_at (atlas':((B->bool)#(B->real^N))->bool) ((F1:A->B) ((Fm:real^M->A) z))` THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `p:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                 `p':(B->bool)#(B->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[MFD_DIFFERENTIAL_OPEN_SET_ATLAS; mfd_differential; o_THM] THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `R1 = \y. SND (p':(B->bool)#(B->real^N)) ((F1:A->B) (chart_inv (p:(A->bool)#(A->real^N)) y))` THEN
  ABBREV_TAC `R2 = \y. SND (p:(A->bool)#(A->real^N)) ((Fm:real^M->A) y)` THEN
  ABBREV_TAC `S1 = IMAGE (SND (p:(A->bool)#(A->real^N)))
                     {x | x IN FST p INTER W /\ (F1:A->B) x IN FST(p':(B->bool)#(B->real^N))}` THEN
  SUBGOAL_THEN `open (S1:real^N->bool) /\ smooth_map_on S1 (R1:real^N->real^N)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [EXPAND_TAC "S1" THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                     `p:(A->bool)#(A->real^N)`; `p':(B->bool)#(B->real^N)`;
                     `W:A->bool`; `F1:A->B`] MFDM_CHART_DOMAIN_OPEN) THEN
      ASM_SIMP_TAC[];
      EXPAND_TAC "S1" THEN EXPAND_TAC "R1" THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`p:(A->bool)#(A->real^N)`; `p':(B->bool)#(B->real^N)`] o
        GEN_REWRITE_RULE I [mfd_smooth_map]) THEN
      ASM_REWRITE_TAC[o_DEF]];
    ALL_TAC] THEN
  SUBGOAL_THEN `SND (p:(A->bool)#(A->real^N)) ((Fm:real^M->A) z) IN S1` ASSUME_TAC THENL
   [EXPAND_TAC "S1" THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
    ASM_REWRITE_TAC[IN_ELIM_THM; IN_INTER] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `O = {y:real^M | (Fm:real^M->A) y IN FST(p:(A->bool)#(A->real^N)) INTER W /\ (F1:A->B) (Fm y) IN FST(p':(B->bool)#(B->real^N))}` THEN
  SUBGOAL_THEN `open (O:real^M->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "O" THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                   `p:(A->bool)#(A->real^N)`; `p':(B->bool)#(B->real^N)`;
                   `W:A->bool`; `F1:A->B`] MFDM_CHART_DOMAIN_OPEN) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    UNDISCH_TAC `continuous_map (euclidean,top) (Fm:real^M->A)` THEN
    REWRITE_TAC[CONTINUOUS_MAP; TOPSPACE_EUCLIDEAN; IN_UNIV] THEN
    DISCH_THEN(MP_TAC o SPEC `{x | x IN FST(p:(A->bool)#(A->real^N)) INTER W /\ (F1:A->B) x IN FST(p':(B->bool)#(B->real^N))}` o CONJUNCT2) THEN
    ASM_REWRITE_TAC[GSYM OPEN_IN; IN_ELIM_THM; IN_UNIV];
    ALL_TAC] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
  MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_WITHIN_OPEN THEN
  MAP_EVERY EXISTS_TAC [`(R1:real^N->real^N) o (R2:real^M->real^N)`; `O:real^M->bool`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [EXPAND_TAC "O" THEN REWRITE_TAC[IN_ELIM_THM; IN_INTER] THEN ASM_REWRITE_TAC[];
    EXPAND_TAC "O" THEN EXPAND_TAC "R1" THEN EXPAND_TAC "R2" THEN
    REWRITE_TAC[IN_ELIM_THM; IN_INTER; o_THM] THEN SIMP_TAC[] THEN
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC DIFF_CHAIN_AT THEN CONJ_TAC THENL
   [REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN EXPAND_TAC "R2" THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `Fm:real^M->A`;
                   `z:real^M`] P2BKF_SMOOTH_DIFFABLE) THEN
    ASM_REWRITE_TAC[];
    SUBGOAL_THEN `(R2:real^M->real^N) z = SND (p:(A->bool)#(A->real^N)) ((Fm:real^M->A) z)`
    SUBST1_TAC THENL [EXPAND_TAC "R2" THEN REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `S1:real^N->bool` THEN
    ASM_REWRITE_TAC[]]);;

(* KFL.A19 The flow Phi_r of a parallel unit field: smooth on M (locally    *)
(* fmap o (translation by r e3) o fmap^-1 in a flow chart).                   *)

let p2bkf_phi = new_definition
 `p2bkf_phi (top:A topology,atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N)
            (X:A->real^N) (r:real) =
    \y. mfd_geo (top,atlas) g y (X y) r`;;

let P2BKF_FMAP_SHIFT = prove
 (`!top atlas (g:A->real^3^3) (X:A->real^3) x0 u1 u2 z r.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_complete (top,atlas) g /\ p2b_parallel_on atlas g (topspace top) X /\
     x0 IN topspace top
     ==> p2bkf_fmap (top,atlas) g X x0 u1 u2 (z + r % basis 3) =
         p2bkf_phi (top,atlas) g X r (p2bkf_fmap (top,atlas) g X x0 u1 u2 z)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p2bkf_fmap; p2bkf_phi] THEN
  SIMP_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; BASIS_COMPONENT; DIMINDEX_3; ARITH] THEN
  REWRITE_TAC[REAL_MUL_RZERO; REAL_ADD_RID; REAL_MUL_RID] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `x0:A`; `\z:real^3. z$1 % (u1:real^3) + z$2 % (u2:real^3)`]
                P2BKF_EXP_LINEAR_SMOOTH) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[linear; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[CONTINUOUS_MAP; SUBSET; FORALL_IN_IMAGE; TOPSPACE_EUCLIDEAN; IN_UNIV] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `X:A->real^3`;
                 `mfd_exp (top,atlas) (g:A->real^3^3) x0 ((z:real^3)$1 % u1 + z$2 % u2)`]
                P2BKF_ORBIT_SHIFT) THEN
  ASM_SIMP_TAC[]);;

let P2BKF_FMAP_TRANSL_SMOOTH = prove
 (`!top atlas (g:A->real^3^3) (X:A->real^3) x0 u1 u2 r.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_complete (top,atlas) g /\ p2b_parallel_on atlas g (topspace top) X /\
     x0 IN topspace top
     ==> continuous_map (euclidean,top)
           (p2bkf_fmap (top,atlas) g X x0 u1 u2 o (\z. z + r % basis 3)) /\
         mfd_smooth_map (open_set_atlas (:real^3)) atlas (:real^3)
           (p2bkf_fmap (top,atlas) g X x0 u1 u2 o (\z. z + r % basis 3))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `X:A->real^3`; `x0:A`; `u1:real^3`; `u2:real^3`] P2BKF_FMAP_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `smooth_map_on (:real^3) (\z:real^3. z + r % basis 3)` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN
    REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_ID; SMOOTH_MAP_ON_CONST];
    ALL_TAC] THEN
  SUBGOAL_THEN `continuous_map (euclidean,euclidean) (\z:real^3. z + r % basis 3)` ASSUME_TAC THENL
   [REWRITE_TAC[CONTINUOUS_MAP_EUCLIDEAN_EUCLIDEAN] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN EXISTS_TAC `euclidean:(real^3)topology` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC (INST_TYPE [`:real^3`,`:A`; `:real^3`,`:B`; `:A`,`:C`;
                           `:3`,`:M`; `:3`,`:N`; `:3`,`:P`]
                MFD_SMOOTH_MAP_COMPOSE) THEN
  MAP_EVERY EXISTS_TAC [`subtopology euclidean (:real^3)`; `subtopology euclidean (:real^3)`;
                        `open_set_atlas (:real^3)`; `top:A topology`; `(:real^3)`] THEN
  ASM_SIMP_TAC[OPEN_SET_ATLAS; OPEN_UNIV; SUBTOPOLOGY_UNIV; GSYM OPEN_IN; SUBSET_UNIV;
               SUBTOPOLOGY_SUBTOPOLOGY; INTER_UNIV; MFD_SMOOTH_MAP_OPEN_SET_ATLAS; IN_UNIV;
               SET_RULE `{x:real^3 | T} = UNIV`]);;

let P2BKF_PHI_LOCAL = prove
 (`!top atlas (g:A->real^3^3) (X:A->real^3) r y.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_complete (top,atlas) g /\ p2b_parallel_on atlas g (topspace top) X /\
     (!x. x IN topspace top ==> X x dot (g x ** X x) = &1) /\ y IN topspace top
     ==> ?W. open_in top W /\ y IN W /\
             continuous_map (subtopology top W,top) (p2bkf_phi (top,atlas) g X r) /\
             mfd_smooth_map atlas atlas W (p2bkf_phi (top,atlas) g X r)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`(g:A->real^3^3) y ** (X:A->real^3) y`; `(X:A->real^3) y`] P2BKF_HCOMPLEMENT) THEN
  ASM_SIMP_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `u1:real^3` (X_CHOOSE_THEN `u2:real^3` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `X:A->real^3`; `y:A`; `u1:real^3`; `u2:real^3`] P2BKF_FMAP_PARAM) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `V:real^3->bool` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `e':A->real^3` o GEN_REWRITE_RULE I [mfd_param]) THEN
  ABBREV_TAC `fm = p2bkf_fmap (top,atlas) (g:A->real^3^3) X y u1 u2` THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [mfd_diffeo]) THEN
  EXISTS_TAC `IMAGE (fm:real^3->A) V` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `X:A->real^3`; `y:A`; `u1:real^3`; `u2:real^3`; `r:real`]
                P2BKF_FMAP_TRANSL_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `X:A->real^3`; `y:A`; `u1:real^3`; `u2:real^3`; `vec 0:real^3`]
                P2BKF_FMAP_D0) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  SUBGOAL_THEN `(y:A) IN IMAGE (fm:real^3->A) V` ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!x. x IN IMAGE (fm:real^3->A) V
                    ==> p2bkf_phi (top,atlas) (g:A->real^3^3) X r x =
                        ((fm o (\z. z + r % basis 3)) o (e':A->real^3)) x`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    UNDISCH_TAC `homeomorphic_maps (subtopology euclidean V,subtopology top (IMAGE (fm:real^3->A) V))
                   (fm,(e':A->real^3))` THEN
    REWRITE_TAC[homeomorphic_maps; TOPSPACE_SUBTOPOLOGY; TOPSPACE_EUCLIDEAN; INTER_UNIV] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `(x:A) IN topspace top INTER IMAGE (fm:real^3->A) V` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[IN_INTER] THEN
      FIRST_ASSUM(MP_TAC o MATCH_MP OPEN_IN_SUBSET o check (fun th ->
        can (find_term ((=) `IMAGE (fm:real^3->A) V`)) (concl th) &&
        can (find_term (fun t -> try fst(dest_const t) = "open_in" with Failure _ -> false)) (concl th))) THEN
      ASM SET_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[o_THM] THEN
    SUBGOAL_THEN `x = (fm:real^3->A) ((e':A->real^3) x)` (fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THENL
     [CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    EXPAND_TAC "fm" THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC P2BKF_FMAP_SHIFT THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_MAP_EQ THEN
    EXISTS_TAC `((fm:real^3->A) o (\z. z + r % basis 3)) o (e':A->real^3)` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER] THEN ASM_MESON_TAC[];
      MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN EXISTS_TAC `euclidean:(real^3)topology` THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `homeomorphic_maps (subtopology euclidean V,subtopology top (IMAGE (fm:real^3->A) V))
                     (fm,(e':A->real^3))` THEN
      REWRITE_TAC[homeomorphic_maps] THEN STRIP_TAC THEN
      UNDISCH_TAC `continuous_map (subtopology top (IMAGE (fm:real^3->A) V),subtopology euclidean V)
                     (e':A->real^3)` THEN
      REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN SIMP_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC MFD_SMOOTH_MAP_EQ THEN
  MAP_EVERY EXISTS_TAC [`top:A topology`; `((fm:real^3->A) o (\z. z + r % basis 3)) o (e':A->real^3)`] THEN
  ASM_SIMP_TAC[] THEN
  MATCH_MP_TAC (INST_TYPE [`:A`,`:A`; `:real^3`,`:B`; `:A`,`:C`;
                           `:3`,`:M`; `:3`,`:N`; `:3`,`:P`]
                MFD_SMOOTH_MAP_COMPOSE) THEN
  MAP_EVERY EXISTS_TAC [`top:A topology`; `subtopology euclidean (:real^3)`;
                        `open_set_atlas (:real^3)`; `top:A topology`; `(:real^3)`] THEN
  ASM_SIMP_TAC[OPEN_SET_ATLAS; OPEN_UNIV; SUBTOPOLOGY_UNIV; GSYM OPEN_IN; SUBSET_UNIV] THEN
  UNDISCH_TAC `homeomorphic_maps (subtopology euclidean V,subtopology top (IMAGE (fm:real^3->A) V))
                 (fm,(e':A->real^3))` THEN
  REWRITE_TAC[homeomorphic_maps] THEN STRIP_TAC THEN
  UNDISCH_TAC `continuous_map (subtopology top (IMAGE (fm:real^3->A) V),subtopology euclidean V)
                 (e':A->real^3)` THEN
  REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN SIMP_TAC[]);;

let P2BKF_PHI_SMOOTH = prove
 (`!top atlas (g:A->real^3^3) (X:A->real^3) r.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_complete (top,atlas) g /\ p2b_parallel_on atlas g (topspace top) X /\
     (!x. x IN topspace top ==> X x dot (g x ** X x) = &1)
     ==> continuous_map (top,top) (p2bkf_phi (top,atlas) g X r) /\
         mfd_smooth_map atlas atlas (topspace top) (p2bkf_phi (top,atlas) g X r)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `continuous_map (top,top) (p2bkf_phi (top,atlas) (g:A->real^3^3) X r)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC TOPC_CONTINUOUS_MAP_LOCAL THEN X_GEN_TAC `y:A` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `X:A->real^3`; `r:real`; `y:A`] P2BKF_PHI_LOCAL) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MFDD_SMOOTH_MAP_LOCAL THEN
  MAP_EVERY EXISTS_TAC [`top:A topology`; `top:A topology`] THEN
  ASM_REWRITE_TAC[OPEN_IN_TOPSPACE; SUBTOPOLOGY_TOPSPACE] THEN
  X_GEN_TAC `y:A` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `X:A->real^3`; `r:real`; `y:A`] P2BKF_PHI_LOCAL) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `W:A->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `W:A->bool` THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[OPEN_IN_SUBSET]);;

let P2BKF_PHI_INVERSE = prove
 (`!top atlas (g:A->real^N^N) (X:A->real^N) r y.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_complete (top,atlas) g /\ p2b_parallel_on atlas g (topspace top) X /\
     y IN topspace top
     ==> p2bkf_phi (top,atlas) g X r y IN topspace top /\
         p2bkf_phi (top,atlas) g X (--r) (p2bkf_phi (top,atlas) g X r y) = y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p2bkf_phi] THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                   `X:A->real^N`; `y:A`] P2BKF_ORBIT) THEN
    ASM_SIMP_TAC[];
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                   `X:A->real^N`; `y:A`] P2BKF_ORBIT_SHIFT) THEN
    ASM_SIMP_TAC[REAL_ADD_RINV] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                   `y:A`; `(X:A->real^N) y`] MFD_GEO_MAXIMAL) THEN
    ASM_SIMP_TAC[]]);;

let P2BKF_TRANSL_DIFF = prove
 (`!(atlas:((A->bool)#(A->real^N))->bool) (Fm:real^M->A) c.
     (\y. SND(chart_at atlas (Fm c)) (Fm y)) differentiable at c
     ==> mfd_differential (open_set_atlas (:real^M)) atlas (Fm o (\z. z + c)) (vec 0) =
         mfd_differential (open_set_atlas (:real^M)) atlas Fm c`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[MFD_DIFFERENTIAL_OPEN_SET_ATLAS; o_THM; VECTOR_ADD_LID] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
  ABBREV_TAC `H = \y. SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) ((Fm:real^M->A) c)) (Fm y)` THEN
  SUBGOAL_THEN `(\y. SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) ((Fm:real^M->A) c)) (Fm (y + c))) =
                (H:real^M->real^N) o (\z. z + c)` SUBST1_TAC THENL
   [EXPAND_TAC "H" THEN REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MP_TAC(ISPECL [`(\z:real^M. z + c)`; `H:real^M->real^N`; `(\h:real^M. h)`;
                 `frechet_derivative (H:real^M->real^N) (at c)`; `vec 0:real^M`] DIFF_CHAIN_AT) THEN
  REWRITE_TAC[VECTOR_ADD_LID] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`(\z:real^M. z)`; `(\h:real^M. h)`; `(\z:real^M. c:real^M)`;
                     `(\h:real^M. vec 0:real^M)`; `at(vec 0:real^M)`] HAS_DERIVATIVE_ADD) THEN
      REWRITE_TAC[HAS_DERIVATIVE_ID; HAS_DERIVATIVE_CONST; VECTOR_ADD_RID];
      ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS]];
    REWRITE_TAC[o_DEF; ETA_AX]]);;

let P2BKF_PULLBACK_FORMULA = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) top' (atlas':((B->bool)#(B->real^N))->bool)
    (f:A->B) (g':B->real^N^N) y.
     smooth_manifold_atlas top atlas /\ smooth_manifold_atlas top' atlas' /\
     y IN topspace top /\ f y IN topspace top'
     ==> mfd_pullback_metric atlas atlas' f g' y =
         transp(matrix(mfd_differential atlas atlas' f y)) ** g'(f y) **
         matrix(mfd_differential atlas atlas' f y)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_pullback_metric; mpullback; mfd_differential] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `y:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `chart_at (atlas:((A->bool)#(A->real^N))->bool) (y:A)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_SIMP_TAC[o_THM; o_DEF] THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`; `g':B->real^N^N`;
                 `(f:A->B) y`] METRIC_LOCAL_AT) THEN
  ASM_SIMP_TAC[]);;

let P2BKF_MDIFF_LINEAR = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) top' (atlas':((B->bool)#(B->real^M))->bool)
    (F1:A->B) W x.
     smooth_manifold_atlas top atlas /\ smooth_manifold_atlas top' atlas' /\
     open_in top W /\ x IN W /\ continuous_map (subtopology top W,top') F1 /\
     mfd_smooth_map atlas atlas' W F1
     ==> linear(mfd_differential atlas atlas' F1 x)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `(F1:A->B) x IN topspace top'` ASSUME_TAC THENL
   [UNDISCH_TAC `continuous_map (subtopology top W,top') (F1:A->B)` THEN
    REWRITE_TAC[CONTINUOUS_MAP; SUBSET; FORALL_IN_IMAGE; TOPSPACE_SUBTOPOLOGY; IN_INTER] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `p = chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^M))->bool`;
                 `(F1:A->B) x`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `p' = chart_at (atlas':((B->bool)#(B->real^M))->bool) ((F1:A->B) x)` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `p:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[mfd_differential] THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
  EXISTS_TAC `IMAGE (SND (p:(A->bool)#(A->real^N)))
                {z | z IN FST p INTER W /\ (F1:A->B) z IN FST(p':(B->bool)#(B->real^M))}` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `top':B topology`; `atlas':((B->bool)#(B->real^M))->bool`;
                 `p:(A->bool)#(A->real^N)`; `p':(B->bool)#(B->real^M)`;
                 `W:A->bool`; `F1:A->B`] MFDM_CHART_DOMAIN_OPEN) THEN
  ASM_SIMP_TAC[] THEN DISCH_TAC THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`p:(A->bool)#(A->real^N)`; `p':(B->bool)#(B->real^M)`] o
      GEN_REWRITE_RULE I [mfd_smooth_map]) THEN
    ASM_REWRITE_TAC[o_DEF];
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_ELIM_THM; IN_INTER]]);;

let P2BKF_TRIPLE_DOT = prove
 (`!(M:real^3^3) (G:real^3^3) v w.
     v dot ((transp M ** G ** M) ** w) = (M ** v) dot (G ** (M ** w))`,
  SIMP_TAC[dot; matrix_vector_mul; transp; matrix_mul; LAMBDA_BETA; DIMINDEX_3; SUM_3; ARITH] THEN
  REAL_ARITH_TAC);;

let P2BKF_PHI_PULLBACK = prove
 (`!top atlas (g:A->real^3^3) (g2:A->real^3^3) (X:A->real^3) r y.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_complete (top,atlas) g /\ p2b_parallel_on atlas g (topspace top) X /\
     (!x. x IN topspace top ==> X x dot (g x ** X x) = &1) /\
     riemannian_metric atlas g2 /\ p2b_parallel_on atlas g2 (topspace top) X /\
     y IN topspace top
     ==> mfd_pullback_metric atlas atlas (p2bkf_phi (top,atlas) g X r) g2 y = g2 y`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `P = p2bkf_phi (top,atlas) (g:A->real^3^3) X r` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `X:A->real^3`; `r:real`] P2BKF_PHI_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `X:A->real^3`; `r:real`; `y:A`] P2BKF_PHI_INVERSE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  (* the flow chart at y *)
  MP_TAC(ISPECL [`(g:A->real^3^3) y ** (X:A->real^3) y`; `(X:A->real^3) y`] P2BKF_HCOMPLEMENT) THEN
  ASM_SIMP_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `u1:real^3` (X_CHOOSE_THEN `u2:real^3` STRIP_ASSUME_TAC)) THEN
  ABBREV_TAC `fm = p2bkf_fmap (top,atlas) (g:A->real^3^3) X y u1 u2` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `X:A->real^3`; `y:A`; `u1:real^3`; `u2:real^3`] P2BKF_FMAP_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(fm:real^3->A) (vec 0) = y` ASSUME_TAC THENL
   [EXPAND_TAC "fm" THEN MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
      `g:A->real^3^3`; `X:A->real^3`; `y:A`; `u1:real^3`; `u2:real^3`; `vec 0:real^3`]
      P2BKF_FMAP_D0) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!h. mfd_differential (open_set_atlas (:real^3)) atlas (fm:real^3->A) (vec 0) h =
                    h$1 % u1 + h$2 % u2 + h$3 % (X:A->real^3) y` ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "fm" THEN MP_TAC(ISPECL [`top:A topology`;
      `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`; `X:A->real^3`; `y:A`;
      `u1:real^3`; `u2:real^3`; `h:real^3`] P2BKF_FMAP_D0) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  (* differential of P at y composed with the chart *)
  SUBGOAL_THEN `mfd_differential (open_set_atlas (:real^3)) (atlas:((A->bool)#(A->real^3))->bool) ((P:A->A) o (fm:real^3->A)) (vec 0) =
                mfd_differential atlas atlas P y o
                mfd_differential (open_set_atlas (:real^3)) atlas fm (vec 0)` ASSUME_TAC THENL
   [FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (RAND_CONV o LAND_CONV o RAND_CONV) [SYM th]) THEN
    MATCH_MP_TAC P2BKF_MDIFF_CHAIN THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `top:A topology`; `topspace top:A->bool`] THEN
    ASM_REWRITE_TAC[OPEN_IN_TOPSPACE; SUBTOPOLOGY_TOPSPACE];
    ALL_TAC] THEN
  SUBGOAL_THEN `(P:A->A) o (fm:real^3->A) = fm o (\z. z + r % basis 3)` ASSUME_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM] THEN X_GEN_TAC `z:real^3` THEN
    EXPAND_TAC "P" THEN EXPAND_TAC "fm" THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC P2BKF_FMAP_SHIFT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_differential (open_set_atlas (:real^3)) (atlas:((A->bool)#(A->real^3))->bool) ((fm:real^3->A) o (\z. z + r % basis 3)) (vec 0) =
                mfd_differential (open_set_atlas (:real^3)) atlas fm (r % basis 3)` ASSUME_TAC THENL
   [MATCH_MP_TAC P2BKF_TRANSL_DIFF THEN MATCH_MP_TAC P2BKF_SMOOTH_DIFFABLE THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!a. mfd_differential (atlas:((A->bool)#(A->real^3))->bool) atlas (P:A->A) y
                      (mfd_differential (open_set_atlas (:real^3)) atlas (fm:real^3->A) (vec 0) a) =
                    mfd_differential (open_set_atlas (:real^3)) atlas fm (r % basis 3) a`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    FIRST_X_ASSUM(fun th -> REWRITE_TAC[SYM th]) THEN
    FIRST_X_ASSUM(fun th -> REWRITE_TAC[SYM th]) THEN
    FIRST_X_ASSUM(fun th -> REWRITE_TAC[th]) THEN REWRITE_TAC[o_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN `(P:A->A) y = (fm:real^3->A) (r % basis 3)` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o C AP_THM `vec 0:real^3` o check (fun th ->
      can (find_term (fun t -> try fst(dest_var t) = "P" with Failure _ -> false)) (concl th) &&
      is_eq(concl th) && not(is_forall(concl th)) &&
      can (find_term (fun t -> try fst(dest_const t) = "o" with Failure _ -> false)) (lhs(concl th)))) THEN
    REWRITE_TAC[o_THM; VECTOR_ADD_LID] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `P:A->A`; `g2:A->real^3^3`; `y:A`] P2BKF_PULLBACK_FORMULA) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `P:A->A`; `topspace top:A->bool`; `y:A`] P2BKF_MDIFF_LINEAR) THEN
  ASM_REWRITE_TAC[OPEN_IN_TOPSPACE; SUBTOPOLOGY_TOPSPACE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `!v:real^3. ?a. mfd_differential (open_set_atlas (:real^3)) (atlas:((A->bool)#(A->real^3))->bool) (fm:real^3->A) (vec 0) a = v`
  ASSUME_TAC THENL
   [MATCH_MP_TAC LINEAR_INJECTIVE_IMP_SURJECTIVE THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[linear; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN VECTOR_ARITH_TAC;
      MAP_EVERY X_GEN_TAC [`h1:real^3`; `h2:real^3`] THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`(h1:real^3)$1 - (h2:real^3)$1`; `(h1:real^3)$2 - (h2:real^3)$2`;
                                    `(h1:real^3)$3 - (h2:real^3)$3`] o check (fun th ->
        can (find_term (fun t -> try fst(dest_var t) = "c" with Failure _ -> false)) (concl th) &&
        is_forall(concl th))) THEN
      ANTS_TAC THENL
       [UNDISCH_TAC `(h1:real^3)$1 % u1 + h1$2 % u2 + h1$3 % (X:A->real^3) y =
                     (h2:real^3)$1 % u1 + h2$2 % u2 + h2$3 % X y` THEN
        VECTOR_ARITH_TAC;
        SIMP_TAC[CART_EQ; DIMINDEX_3; FORALL_3] THEN REAL_ARITH_TAC]];
    ALL_TAC] THEN
  REWRITE_TAC[MATRIX_EQ] THEN X_GEN_TAC `w:real^3` THEN
  ONCE_REWRITE_TAC[GSYM VECTOR_EQ_LDOT] THEN X_GEN_TAC `v:real^3` THEN
  REWRITE_TAC[P2BKF_TRIPLE_DOT] THEN
  ASM_SIMP_TAC[MATRIX_WORKS] THEN
  FIRST_ASSUM(X_CHOOSE_THEN `a:real^3` (SUBST1_TAC o SYM) o SPEC `v:real^3`) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `b:real^3` (SUBST1_TAC o SYM) o SPEC `w:real^3`) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `g2:A->real^3^3`; `X:A->real^3`; `y:A`; `u1:real^3`; `u2:real^3`;
                 `vec 0:real^3`; `r:real`; `a:real^3`; `b:real^3`] P2BKF_FMAP_METRIC_INV2) THEN
  ASM_REWRITE_TAC[VECTOR_ADD_LID]);;

let P2BKF_PHI_DIFFEO = prove
 (`!top atlas (g:A->real^3^3) (X:A->real^3) r.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_complete (top,atlas) g /\ p2b_parallel_on atlas g (topspace top) X /\
     (!x. x IN topspace top ==> X x dot (g x ** X x) = &1)
     ==> mfd_diffeo top atlas (topspace top) top atlas (topspace top)
                    (p2bkf_phi (top,atlas) g X r) (p2bkf_phi (top,atlas) g X (--r))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_diffeo; OPEN_IN_TOPSPACE; SUBTOPOLOGY_TOPSPACE] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `X:A->real^3`; `r:real`] P2BKF_PHI_SMOOTH) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `X:A->real^3`; `--r:real`] P2BKF_PHI_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[homeomorphic_maps] THEN
  CONJ_TAC THEN X_GEN_TAC `y:A` THEN DISCH_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `X:A->real^3`; `r:real`; `y:A`] P2BKF_PHI_INVERSE) THEN
    ASM_SIMP_TAC[];
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `X:A->real^3`; `--r:real`; `y:A`] P2BKF_PHI_INVERSE) THEN
    ASM_SIMP_TAC[REAL_NEG_NEG]]);;

let P2BKF_ISOMETRY_METRIC_EQ = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (g1:A->real^N^N) g2 top'
    (atlas':((B->bool)#(B->real^N))->bool) (g':B->real^N^N) f f'.
     smooth_manifold_atlas top atlas /\
     (!x. x IN topspace top ==> g1 x = g2 x) /\
     mfd_isometry (top,atlas) g1 (top',atlas') g' f f'
     ==> mfd_isometry (top,atlas) g2 (top',atlas') g' f f'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mfd_isometry] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`c:(A->bool)#(A->real^N)`; `c':(B->bool)#(B->real^N)`] THEN
  STRIP_TAC THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`c:(A->bool)#(A->real^N)`; `c':(B->bool)#(B->real^N)`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `y:real^N`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[metric_local] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `chart_inv (c:(A->bool)#(A->real^N)) y IN topspace top` ASSUME_TAC THENL
   [SUBGOAL_THEN `(y:real^N) IN IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)` ASSUME_TAC THENL
     [UNDISCH_TAC `(y:real^N) IN IMAGE (SND(c:(A->bool)#(A->real^N)))
                      {x | x IN FST c /\ (f:A->B) x IN FST(c':(B->bool)#(B->real^N))}` THEN
      SET_TAC[];
      ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]];
    ASM_SIMP_TAC[]]);;

let P2BKF_PHI_ISOMETRY = prove
 (`!top atlas (g:A->real^3^3) (g2:A->real^3^3) (X:A->real^3) r.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_complete (top,atlas) g /\ p2b_parallel_on atlas g (topspace top) X /\
     (!x. x IN topspace top ==> X x dot (g x ** X x) = &1) /\
     riemannian_metric atlas g2 /\ p2b_parallel_on atlas g2 (topspace top) X
     ==> mfd_isometry (top,atlas) g2 (top,atlas) g2
                      (p2bkf_phi (top,atlas) g X r) (p2bkf_phi (top,atlas) g X (--r))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC P2BKF_ISOMETRY_METRIC_EQ THEN
  EXISTS_TAC `mfd_pullback_metric atlas atlas (p2bkf_phi (top,atlas) (g:A->real^3^3) X r) (g2:A->real^3^3)` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC P2BKF_PHI_PULLBACK THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC MFD_ISOMETRY_PULLBACK THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC P2BKF_PHI_DIFFEO THEN ASM_REWRITE_TAC[]]);;

