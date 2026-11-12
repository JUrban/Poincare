(* ========================================================================= *)
(* Unit pc_p4_pinch: the pinch bridge P4_PINCH_FROM_INV_STATEMENT (MT Prop   *)
(* 15.12 in corrected form).  For an event k and a component Y of the new    *)
(* stage, a map p from the component X of the old stage containing the       *)
(* retained points of Y onto Y: the identity on the retained points, the     *)
(* radial collapse of the cap data across each cut neck, the cap tip beyond; *)
(* |dp v| <= (1+e)|v| from the limit metric.  Separation of the cut spheres  *)
(* (in a simply connected 3-manifold every 2-sphere separates, MT Remark     *)
(* 0.6(ii)) is SMT_SC_SPHERE_SEP (pc_smt_sep).                               *)
(*                                                                           *)
(* In order: uniform comparison with the limit metric; components without    *)
(* caps (identity pinch maps); the topological decomposition of the old      *)
(* component along the cut spheres of Y; the neck domain and the cap data of *)
(* p3_cap_param (pc_p3_inv); local derivative tools, the neck bound          *)
(* P4_NECK_QF; the cap data p4_capdata, the neck index p4_pidx, the pinch    *)
(* map p4_pmap and its values; pieces of X0, continuity; smoothness; the     *)
(* derivative bound; the degree-one condition, the event theorem             *)
(* P4_PINCH_EVENT, cap data from p3_struct, and the main theorem             *)
(* P4_PINCH_FROM_INV (hypothesis RFS_CUTCAP_SC_STATEMENT only).              *)
(* ========================================================================= *)

needs "src/pc_p4_align.ml";;
needs "src/pc_smt_sep.ml";;
needs "src/pc_apx_event.ml";;
needs "src/pc_lrg_stab.ml";;
needs "src/pc_apx_local.ml";;
needs "src/pc_p3_route.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* The slab metric near the event time against the limit                     *)
(* metric, uniformly on compact subsets of Omega (rfs_limit_metric with     *)
(* k = 0 and the chart-invariant bound LCK_DIST_C0); the identity at a      *)
(* retained point; the facts of one event in equation-free form.            *)
(* ------------------------------------------------------------------------- *)

let P4_QF_COMPARE_ARITH = prove
 (`!Q Q0 s e. &0 < e /\ &0 <= Q0 /\ s <= e / (&1 + e) /\ abs(Q - Q0) <= s * Q0
              ==> Q0 <= (&1 + e) pow 2 * Q`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `s * Q0 <= e / (&1 + e) * Q0` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(&1 + e) * (e / (&1 + e) * Q0) = e * Q0` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_FIELD `~(&1 + e = &0) ==> (&1 + e) * (e / (&1 + e) * Q0) = e * Q0`) THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(&1 + e) * (Q0 - Q) <= (&1 + e) * (e / (&1 + e) * Q0)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `Q0 <= (&1 + e) * Q` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= Q` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 <= (&1 + e) * Q` MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_MUL_POS_LE] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(&1 + e) * Q <= (&1 + e) pow 2 * Q` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[REAL_POW_2] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= (&1 + e) * e ==> &1 + e <= (&1 + e) * (&1 + e)`) THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC]);;

let P4_LIMIT_METRIC_UNIFORM = prove
 (`!top atlas (g:real->A->real^3^3) Om ts gl a K e.
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool) /\
        open_in top Om /\ rfs_limit_metric (top,atlas) Om ts g gl /\
        (!t. a <= t /\ t < ts ==> riemannian_metric atlas (g t)) /\
        a < ts /\ compact_in top K /\ K SUBSET Om /\ &0 < e
        ==> ?d. &0 < d /\ d <= ts - a /\
                !t x v. ts - d < t /\ t < ts /\ x IN K
                        ==> v dot (gl x ** v) <= (&1 + e) pow 2 * (v dot (g t x ** v))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rfs_limit_metric] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`K:A->bool`; `0`; `(e / (&1 + e)) pow 2`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_POW_LT THEN
    MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
    DISCH_THEN(X_CHOOSE_THEN `d0:real` STRIP_ASSUME_TAC)] THEN
  EXISTS_TAC `min d0 (ts - a)` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `x:A`; `v:real^3`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL
   [MP_TAC(MATCH_MP OPEN_IN_SUBSET (ASSUME `open_in top (Om:A->bool)`)) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `x:A`]
         CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^3))->bool) x` THEN
  SUBGOAL_THEN
   `metric_field (IMAGE (SND c) (FST c INTER Om))
                 (metric_local (atlas:((A->bool)#(A->real^3))->bool) c gl) /\
    metric_field (IMAGE (SND c) (FST c INTER Om))
                 (metric_local atlas c ((g:real->A->real^3^3) t))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC METRIC_FIELD_SUBSET THEN
    EXISTS_TAC `IMAGE (SND (c:(A->bool)#(A->real^3))) (FST c)` THEN
    CONJ_TAC THENL
     [MP_TAC(SPEC `t:real` (ASSUME
        `!t. a <= t /\ t < ts ==> riemannian_metric (atlas:((A->bool)#(A->real^3))->bool)
                                                   ((g:real->A->real^3^3) t)`)) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MP_TAC(ISPEC `c:(A->bool)#(A->real^3)` PAIR_SURJECTIVE) THEN
      REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [`U:A->bool`; `phi:A->real^3`] THEN
      DISCH_THEN SUBST_ALL_TAC THEN REWRITE_TAC[FST; SND] THEN
      MATCH_MP_TAC MFDR_RESTRICT_IMAGE_OPEN THEN
      EXISTS_TAC `top:A topology` THEN EXISTS_TAC `atlas:((A->bool)#(A->real^3))->bool` THEN
      ASM_REWRITE_TAC[];
      SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`0`; `IMAGE (SND (c:(A->bool)#(A->real^3))) (FST c INTER Om)`;
                 `metric_local (atlas:((A->bool)#(A->real^3))->bool) c gl`;
                 `metric_local (atlas:((A->bool)#(A->real^3))->bool) c ((g:real->A->real^3^3) t)`;
                 `SND (c:(A->bool)#(A->real^3)) x`; `v:real^3`] LCK_DIST_C0) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `gl:A->real^3^3`; `x:A`] METRIC_LOCAL_AT) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `(g:real->A->real^3^3) t`; `x:A`] METRIC_LOCAL_AT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN DISCH_THEN SUBST1_TAC THEN
  DISCH_TAC THEN MATCH_MP_TAC P4_QF_COMPARE_ARITH THEN
  EXISTS_TAC `sqrt(lck_dist2 0 (metric_local (atlas:((A->bool)#(A->real^3))->bool) c gl)
                     (metric_local atlas c ((g:real->A->real^3^3) t))
                     (SND (c:(A->bool)#(A->real^3)) x))` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`IMAGE (SND (c:(A->bool)#(A->real^3))) (FST c INTER Om)`;
                   `metric_local (atlas:((A->bool)#(A->real^3))->bool) c gl`;
                   `SND (c:(A->bool)#(A->real^3)) x`; `v:real^3`] LRG_METRIC_NONNEG) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `gl:A->real^3^3`; `x:A`] METRIC_LOCAL_AT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN DISCH_THEN MATCH_MP_TAC THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt((e / (&1 + e)) pow 2)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SQRT_MONO_LE THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`t:real`; `x:A`] o check (fun th ->
      try fst(dest_const(fst(strip_comb(lhand(rand(snd(strip_forall(concl th)))))))) = "lck_dist2"
      with Failure _ -> false)) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]];
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC POW_2_SQRT THEN
    MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC]);;

(* At a retained point the identity map, read in the preferred charts of the *)
(* old and the new stage, carries the new metric at the event time back to   *)
(* the limit metric (rfs_same_metric_on of rfs_event_ok).                    *)

let P4_RETAINED_QF = prove
 (`!topX atlasX (gl:A->real^3^3) topY atlasY (gY:A->real^3^3) W x v.
        smooth_manifold_atlas topX (atlasX:((A->bool)#(A->real^3))->bool) /\
        smooth_manifold_atlas topY (atlasY:((A->bool)#(A->real^3))->bool) /\
        rfs_same_metric_on atlasX gl atlasY gY W /\
        x IN W /\ x IN topspace topX /\ x IN topspace topY
        ==> (jacobian (\y. SND (chart_at atlasY x) (chart_inv (chart_at atlasX x) y))
                      (at (SND (chart_at atlasX x) x)) ** v) dot
            (gY x ** (jacobian (\y. SND (chart_at atlasY x) (chart_inv (chart_at atlasX x) y))
                               (at (SND (chart_at atlasX x) x)) ** v)) =
            v dot (gl x ** v)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rfs_same_metric_on] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`; `x:A`]
         CHART_AT) THEN
  MP_TAC(ISPECL [`topY:A topology`; `atlasY:((A->bool)#(A->real^3))->bool`; `x:A`]
         CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`chart_at (atlasX:((A->bool)#(A->real^3))->bool) x`;
    `chart_at (atlasY:((A->bool)#(A->real^3))->bool) x`;
    `SND(chart_at (atlasX:((A->bool)#(A->real^3))->bool) x) x`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                 `gl:A->real^3^3`; `x:A`] METRIC_LOCAL_AT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN
   `chart_inv (chart_at (atlasX:((A->bool)#(A->real^3))->bool) x)
              (SND(chart_at atlasX x) x) = x`
  ASSUME_TAC THENL
   [MP_TAC(ISPEC `chart_at (atlasX:((A->bool)#(A->real^3))->bool) x` PAIR_SURJECTIVE) THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`U:A->bool`; `phi:A->real^3`] THEN
    DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th]) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[FST; SND]) THEN REWRITE_TAC[SND] THEN
    MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                   `U:A->bool`; `phi:A->real^3`] CHART_INV) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[mpullback; o_THM] THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`topY:A topology`; `atlasY:((A->bool)#(A->real^3))->bool`;
                 `gY:A->real^3^3`; `x:A`] METRIC_LOCAL_AT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[P4_GRAM_QF_GEN; jacobian] THEN
  SUBGOAL_THEN
   `(\y. SND (chart_at (atlasY:((A->bool)#(A->real^3))->bool) x)
             (chart_inv (chart_at (atlasX:((A->bool)#(A->real^3))->bool) x) y)) =
    SND (chart_at atlasY x) o chart_inv (chart_at atlasX x)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; REFL_TAC]);;

(* The facts of one event in equation-free form (the stage equations of      *)
(* rfs_event_ok are replaced by their consequences for points, subspaces and *)
(* smooth maps, so that assumption rewriting is safe in later proofs).       *)

let P4_EVENT_FACTS = prove
 (`!topX atlasX (gX:real->A->real^3^3) ts topY atlasY gY ev.
        rfs_event_ok (topX,atlasX) gX ts (topY,atlasY) gY ev /\
        smooth_manifold_atlas topX (atlasX:((A->bool)#(A->real^3))->bool)
        ==> open_in topX (ev_omega ev) /\
            rfs_limit_metric (topX,atlasX) (ev_omega ev) ts gX (ev_limit ev) /\
            rfs_same_metric_on atlasX (ev_limit ev) atlasY (gY ts)
                               (topspace topY INTER topspace topX) /\
            topspace topY INTER topspace topX SUBSET ev_omega ev /\
            hausdorff_space (ev_ztop ev) /\
            smooth_manifold_atlas (ev_ztop ev) (ev_zatlas ev) /\
            compact_space (ev_ztop ev) /\
            mfd_cut_cap topX atlasX (ev_ztop ev) (ev_zatlas ev) (ev_index ev)
                        (ev_neck ev) (ev_capp ev) (ev_capm ev) (\x. x) (\x. x) /\
            topspace topX DIFF mfd_cut_spheres (ev_index ev) (ev_neck ev) =
            topspace (ev_ztop ev) DIFF
            mfd_cut_cores (ev_index ev) (ev_capp ev) (ev_capm ev) /\
            subtopology topX (topspace topX DIFF mfd_cut_spheres (ev_index ev) (ev_neck ev)) =
            subtopology (ev_ztop ev) (topspace (ev_ztop ev) DIFF
              mfd_cut_cores (ev_index ev) (ev_capp ev) (ev_capm ev)) /\
            open_in topX (topspace topX DIFF mfd_cut_spheres (ev_index ev) (ev_neck ev)) /\
            open_in (ev_ztop ev) (topspace (ev_ztop ev) DIFF
              mfd_cut_cores (ev_index ev) (ev_capp ev) (ev_capm ev)) /\
            DISJOINT (topspace topX) (mfd_cut_cores (ev_index ev) (ev_capp ev) (ev_capm ev)) /\
            (!i. i IN ev_index ev
                 ==> IMAGE (ev_neck ev i) (annulus (&1 / &2) (&2)) SUBSET ev_omega ev) /\
            ev_disc ev SUBSET topspace(ev_ztop ev) /\
            open_in (ev_ztop ev) (ev_disc ev) /\ closed_in (ev_ztop ev) (ev_disc ev) /\
            (!i. i IN ev_index ev
                 ==> IMAGE (ev_capp ev i) (cball(vec 0,&1)) SUBSET ev_disc ev /\
                     DISJOINT (IMAGE (ev_capm ev i) (cball(vec 0,&1))) (ev_disc ev)) /\
            topspace topY = topspace (ev_ztop ev) DIFF ev_disc ev /\
            open_in (ev_ztop ev) (topspace topY) /\
            closed_in (ev_ztop ev) (topspace topY) /\
            (!S. S SUBSET topspace topY ==> subtopology topY S = subtopology (ev_ztop ev) S) /\
            (!S f:A->A. S SUBSET topspace topX /\ IMAGE f S SUBSET topspace topY
                        ==> (mfd_smooth_map atlasX atlasY S f <=>
                             mfd_smooth_map atlasX (ev_zatlas ev) S f)) /\
            smooth_manifold_atlas topY atlasY`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rfs_event_ok] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP APX_CUTCAP_ID) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
    is_eq(concl th) && lhs(concl th) = `topY:A topology`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
    is_eq(concl th) && lhs(concl th) = `atlasY:((A->bool)#(A->real^3))->bool`)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[TOPSPACE_SUBTOPOLOGY;
    SET_RULE `(s:A->bool) INTER (s DIFF t) = s DIFF t`]) THEN
  REWRITE_TAC[TOPSPACE_SUBTOPOLOGY;
    SET_RULE `(s:A->bool) INTER (s DIFF t) = s DIFF t`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_IN_DIFF THEN ASM_REWRITE_TAC[OPEN_IN_TOPSPACE];
    MATCH_MP_TAC CLOSED_IN_DIFF THEN ASM_REWRITE_TAC[CLOSED_IN_TOPSPACE];
    REPEAT STRIP_TAC THEN REWRITE_TAC[SUBTOPOLOGY_SUBTOPOLOGY] THEN AP_TERM_TAC THEN
    ASM SET_TAC[];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `mfd_smooth_map (restrict_atlas (atlasX:((A->bool)#(A->real^3))->bool)
                                (topspace topX))
                  (restrict_atlas (ev_zatlas ev)
                    (topspace (ev_ztop ev) DIFF ev_disc (ev:(A)rfs_event))) S (f:A->A)` THEN
    CONJ_TAC THENL [ASM_SIMP_TAC[RESTRICT_ATLAS_TOPSPACE]; ALL_TAC] THEN
    MATCH_MP_TAC APX_SMOOTH_MAP_RESTRICT THEN
    MAP_EVERY EXISTS_TAC [`topX:A topology`; `ev_ztop (ev:(A)rfs_event)`] THEN
    ASM_REWRITE_TAC[OPEN_IN_TOPSPACE] THEN ASM SET_TAC[];
    MATCH_MP_TAC SMOOTH_MANIFOLD_ATLAS_RESTRICT THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC OPEN_IN_DIFF THEN ASM_REWRITE_TAC[OPEN_IN_TOPSPACE]]);;

(* ------------------------------------------------------------------------- *)
(* Components of the new stage without caps.  Such a component               *)
(* consists of retained old points off the cut spheres; it is a component   *)
(* of the old stage with the same subspace topology, and the identity is a  *)
(* (1+e)-pinch map for slab times close to the event time.                  *)
(* ------------------------------------------------------------------------- *)

let P4_NOCAP_COMPONENT = prove
 (`!topX atlasX (gX:real->A->real^3^3) ts topY atlasY gY ev Y.
        rfs_event_ok (topX,atlasX) gX ts (topY,atlasY) gY ev /\
        hausdorff_space topX /\
        smooth_manifold_atlas topX (atlasX:((A->bool)#(A->real^3))->bool) /\
        smooth_manifold_atlas topY (atlasY:((A->bool)#(A->real^3))->bool) /\
        compact_space topY /\
        Y IN connected_components_of topY /\ Y SUBSET topspace topX
        ==> Y IN connected_components_of topX /\
            subtopology topX Y = subtopology topY Y /\
            Y SUBSET topspace topX DIFF mfd_cut_spheres (ev_index ev) (ev_neck ev) /\
            Y SUBSET topspace topY /\ Y SUBSET ev_omega ev`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rfs_event_ok] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP APX_CUTCAP_ID) THEN
  SUBGOAL_THEN `(Y:A->bool) SUBSET topspace topY` ASSUME_TAC THENL
   [ASM_MESON_TAC[CONNECTED_COMPONENTS_OF_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `topspace topY = topspace (ev_ztop ev) DIFF ev_disc (ev:(A)rfs_event)`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(Y:A->bool) SUBSET topspace topX DIFF mfd_cut_spheres (ev_index ev) (ev_neck ev)`
  ASSUME_TAC THENL
   [MAP_EVERY (fun t -> MP_TAC(ASSUME t))
     [`DISJOINT (topspace topX)
        (mfd_cut_cores (ev_index ev) (ev_capp ev) (ev_capm (ev:(A)rfs_event)))`;
      `topspace topX DIFF mfd_cut_spheres (ev_index ev) (ev_neck ev) =
       topspace (ev_ztop ev) DIFF
       mfd_cut_cores (ev_index ev) (ev_capp ev) (ev_capm (ev:(A)rfs_event))`;
      `topspace topY = topspace (ev_ztop ev) DIFF ev_disc (ev:(A)rfs_event)`;
      `(Y:A->bool) SUBSET topspace topY`; `(Y:A->bool) SUBSET topspace topX`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `subtopology topX (Y:A->bool) = subtopology topY Y` ASSUME_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `subtopology (subtopology topX
                  (topspace topX DIFF mfd_cut_spheres (ev_index ev) (ev_neck ev)))
                  (Y:A->bool)` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[SUBTOPOLOGY_SUBTOPOLOGY] THEN AP_TERM_TAC THEN ASM SET_TAC[];
      ALL_TAC] THEN
    SUBST1_TAC(ASSUME
     `subtopology topX (topspace topX DIFF mfd_cut_spheres (ev_index ev) (ev_neck ev)) =
      subtopology (ev_ztop ev) (topspace (ev_ztop ev) DIFF
        mfd_cut_cores (ev_index ev) (ev_capp ev) (ev_capm (ev:(A)rfs_event)))`) THEN
    SUBST1_TAC(ASSUME `topY = subtopology (ev_ztop ev)
                      (topspace (ev_ztop ev) DIFF ev_disc (ev:(A)rfs_event))`) THEN
    REWRITE_TAC[SUBTOPOLOGY_SUBTOPOLOGY] THEN AP_TERM_TAC THEN
    MAP_EVERY (fun t -> MP_TAC(ASSUME t))
     [`topspace topX DIFF mfd_cut_spheres (ev_index ev) (ev_neck ev) =
       topspace (ev_ztop ev) DIFF
       mfd_cut_cores (ev_index ev) (ev_capp ev) (ev_capm (ev:(A)rfs_event))`;
      `topspace topY = topspace (ev_ztop ev) DIFF ev_disc (ev:(A)rfs_event)`;
      `(Y:A->bool) SUBSET topspace topY`;
      `(Y:A->bool) SUBSET topspace topX DIFF mfd_cut_spheres (ev_index ev) (ev_neck ev)`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC APX_CLOPEN_COMPONENT THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[connected_in] THEN
      CONJ_TAC THENL
       [ASM SET_TAC[];
        REWRITE_TAC[ASSUME `subtopology topX (Y:A->bool) = subtopology topY Y`]] THEN
      MP_TAC(MATCH_MP CONNECTED_IN_CONNECTED_COMPONENTS_OF
        (ASSUME `(Y:A->bool) IN connected_components_of topY`)) THEN
      SIMP_TAC[connected_in];
      MATCH_MP_TAC OPEN_IN_TRANS_FULL THEN
      EXISTS_TAC `topspace topX DIFF mfd_cut_spheres (ev_index ev) (ev_neck (ev:(A)rfs_event))` THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC OPEN_IN_SUBSET_TOPSPACE THEN CONJ_TAC THENL
       [ALL_TAC;
        MAP_EVERY (fun t -> MP_TAC(ASSUME t))
         [`topspace topX DIFF mfd_cut_spheres (ev_index ev) (ev_neck ev) =
           topspace (ev_ztop ev) DIFF
           mfd_cut_cores (ev_index ev) (ev_capp ev) (ev_capm (ev:(A)rfs_event))`;
          `(Y:A->bool) SUBSET topspace topX DIFF
             mfd_cut_spheres (ev_index ev) (ev_neck (ev:(A)rfs_event))`] THEN
        SET_TAC[]] THEN
      MATCH_MP_TAC OPEN_IN_TRANS_FULL THEN
      EXISTS_TAC `topspace (ev_ztop ev) DIFF ev_disc (ev:(A)rfs_event)` THEN
      CONJ_TAC THENL
       [SUBST1_TAC(SYM(ASSUME `topY = subtopology (ev_ztop ev)
                      (topspace (ev_ztop ev) DIFF ev_disc (ev:(A)rfs_event))`)) THEN
        MATCH_MP_TAC(ISPECL [`topY:A topology`; `atlasY:((A->bool)#(A->real^3))->bool`]
                            APX_COMPONENT_OPEN) THEN
        CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
        MATCH_MP_TAC OPEN_IN_DIFF THEN
        CONJ_TAC THENL [REWRITE_TAC[OPEN_IN_TOPSPACE]; FIRST_ASSUM ACCEPT_TAC]];
      MATCH_MP_TAC COMPACT_IN_IMP_CLOSED_IN THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[COMPACT_IN_SUBSPACE] THEN
      CONJ_TAC THENL
       [ASM SET_TAC[];
        REWRITE_TAC[ASSUME `subtopology topX (Y:A->bool) = subtopology topY Y`]] THEN
      SUBGOAL_THEN `compact_in topY (Y:A->bool)` MP_TAC THENL
       [MATCH_MP_TAC CLOSED_IN_COMPACT_SPACE THEN
        ASM_MESON_TAC[CLOSED_IN_CONNECTED_COMPONENTS_OF];
        SIMP_TAC[COMPACT_IN_SUBSPACE]];
      ASM_MESON_TAC[NONEMPTY_CONNECTED_COMPONENTS_OF]];
    ASM SET_TAC[]]);;

let P4_PINCH_NOCAP = prove
 (`!topX atlasX (gX:real->A->real^3^3) ts topY atlasY gY ev Y a e.
        rfs_event_ok (topX,atlasX) gX ts (topY,atlasY) gY ev /\
        hausdorff_space topX /\
        smooth_manifold_atlas topX (atlasX:((A->bool)#(A->real^3))->bool) /\
        smooth_manifold_atlas topY (atlasY:((A->bool)#(A->real^3))->bool) /\
        compact_space topY /\
        (!t. a <= t /\ t < ts ==> riemannian_metric atlasX (gX t)) /\ a < ts /\
        Y IN connected_components_of topY /\ Y SUBSET topspace topX /\ &0 < e
        ==> Y IN connected_components_of topX /\
            ?d. &0 < d /\ d <= ts - a /\
                !t. ts - d < t /\ t < ts
                    ==> p4_pinch_map (topX,atlasX) (gX t) Y (topY,atlasY) (gY ts) Y
                                     (&1 + e) (\x. x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                 `gX:real->A->real^3^3`; `ts:real`; `topY:A topology`;
                 `atlasY:((A->bool)#(A->real^3))->bool`; `gY:real->A->real^3^3`;
                 `ev:(A)rfs_event`; `Y:A->bool`] P4_NOCAP_COMPONENT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                 `gX:real->A->real^3^3`; `ts:real`; `topY:A topology`;
                 `atlasY:((A->bool)#(A->real^3))->bool`; `gY:real->A->real^3^3`;
                 `ev:(A)rfs_event`] P4_EVENT_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `compact_in topX (Y:A->bool)` ASSUME_TAC THENL
   [REWRITE_TAC[COMPACT_IN_SUBSPACE] THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `compact_in topY (Y:A->bool)` MP_TAC THENL
     [MATCH_MP_TAC CLOSED_IN_COMPACT_SPACE THEN
      ASM_MESON_TAC[CLOSED_IN_CONNECTED_COMPONENTS_OF];
      SIMP_TAC[COMPACT_IN_SUBSPACE]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                 `gX:real->A->real^3^3`; `ev_omega (ev:(A)rfs_event)`; `ts:real`;
                 `ev_limit (ev:(A)rfs_event)`; `a:real`; `Y:A->bool`; `e:real`]
         P4_LIMIT_METRIC_UNIFORM) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `t:real` THEN STRIP_TAC THEN
  REWRITE_TAC[p4_pinch_map; IMAGE_ID] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[CONTINUOUS_MAP_ID];
    SUBGOAL_THEN `mfd_smooth_map (atlasX:((A->bool)#(A->real^3))->bool)
                    (atlasY:((A->bool)#(A->real^3))->bool) Y (\x:A. x) <=>
                  mfd_smooth_map atlasX (ev_zatlas (ev:(A)rfs_event)) Y (\x:A. x)`
    SUBST1_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IMAGE_ID] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC MFD_SMOOTH_MAP_SUBSET THEN
    EXISTS_TAC `topspace topX DIFF mfd_cut_spheres (ev_index ev) (ev_neck (ev:(A)rfs_event))` THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o check (fun th ->
        try fst(dest_const(fst(strip_comb(concl th)))) = "mfd_cut_cap" with Failure _ -> false)) THEN
      REWRITE_TAC[mfd_cut_cap; mfd_diffeo] THEN SIMP_TAC[];
      FIRST_ASSUM ACCEPT_TAC];
    MAP_EVERY X_GEN_TAC [`x:A`; `v:real^3`] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                   `ev_limit (ev:(A)rfs_event)`; `topY:A topology`;
                   `atlasY:((A->bool)#(A->real^3))->bool`;
                   `(gY:real->A->real^3^3) ts`;
                   `topspace topY INTER topspace (topX:A topology)`; `x:A`; `v:real^3`]
           P4_RETAINED_QF) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    EXISTS_TAC `Y:A->bool` THEN
    ASM_REWRITE_TAC[SUBSET_REFL; HOMEOMORPHIC_MAP_ID] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[APX_COMPONENT_OPEN]; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[NONEMPTY_CONNECTED_COMPONENTS_OF]; ALL_TAC] THEN
    ASM_MESON_TAC[APX_COMPONENT_OPEN]]);;

(* ------------------------------------------------------------------------- *)
(* The topological decomposition.  For a component Y of the                  *)
(* new stage: its retained points Y0, the necks whose minus caps lie in Y,  *)
(* the branches B_i beyond their cut spheres, and the old component X =     *)
(* Y0 + spheres + branches (separation of the cut spheres).                 *)
(* ------------------------------------------------------------------------- *)

let P4_SPHERE_CLOSURE_INNER = prove
 (`sphere(vec 0:real^N,&1) SUBSET closure(annulus (&1 / &2) (&1))`,
  REWRITE_TAC[SUBSET; IN_SPHERE_0; CLOSURE_APPROACHABLE; annulus; IN_ELIM_THM] THEN
  X_GEN_TAC `u:real^N` THEN DISCH_TAC THEN X_GEN_TAC `d:real` THEN DISCH_TAC THEN
  EXISTS_TAC `(&1 - min d (&1 / &2) / &2) % u:real^N` THEN
  ASM_REWRITE_TAC[NORM_MUL; dist;
                  VECTOR_ARITH `(&1 - b) % u - u:real^N = --(b % u)`; NORM_NEG] THEN
  ASM_REAL_ARITH_TAC);;

(* A neck chart: the two collars, the cut sphere between them, and the       *)
(* sphere in the closure of both collars.                                    *)

let P4_NECK_PIECES = prove
 (`!top atlas (e:real^3->A).
        mfd_neck_chart top atlas e
        ==> connected_in top (IMAGE e (annulus (&1 / &2) (&1))) /\
            connected_in top (IMAGE e (annulus (&1) (&2))) /\
            connected_in top (IMAGE e (annulus (&1 / &2) (&2))) /\
            open_in top (IMAGE e (annulus (&1 / &2) (&2))) /\
            compact_in top (IMAGE e (sphere(vec 0,&1))) /\
            IMAGE e (annulus (&1 / &2) (&2)) =
            IMAGE e (annulus (&1 / &2) (&1)) UNION IMAGE e (sphere(vec 0,&1)) UNION
            IMAGE e (annulus (&1) (&2)) /\
            DISJOINT (IMAGE e (annulus (&1 / &2) (&1))) (IMAGE e (sphere(vec 0,&1))) /\
            DISJOINT (IMAGE e (annulus (&1) (&2))) (IMAGE e (sphere(vec 0,&1))) /\
            DISJOINT (IMAGE e (annulus (&1 / &2) (&1))) (IMAGE e (annulus (&1) (&2))) /\
            e(&3 / &4 % basis 1) IN IMAGE e (annulus (&1 / &2) (&1)) /\
            e(&4 / &3 % basis 1) IN IMAGE e (annulus (&1) (&2)) /\
            IMAGE e (sphere(vec 0,&1)) SUBSET
            top closure_of IMAGE e (annulus (&1 / &2) (&1))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mfd_neck_chart] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `annulus (&1 / &2) (&1) SUBSET annulus (&1 / &2) (&2):real^3->bool /\
    annulus (&1) (&2) SUBSET annulus (&1 / &2) (&2):real^3->bool /\
    sphere(vec 0,&1) SUBSET annulus (&1 / &2) (&2):real^3->bool`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; annulus; IN_ELIM_THM; IN_SPHERE_0] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y y'. y IN annulus (&1 / &2) (&2) /\ y' IN annulus (&1 / &2) (&2) /\
           (e:real^3->A) y = e y' ==> y = y'`
  ASSUME_TAC THENL [ASM_MESON_TAC[MFD_PARAM_INJ]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC APX_PARAM_CONNECTED_IMAGE THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`;
                          `annulus (&1 / &2) (&2):real^3->bool`] THEN
    ASM_REWRITE_TAC[APX_CONNECTED_ANNULUS3];
    MATCH_MP_TAC APX_PARAM_CONNECTED_IMAGE THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`;
                          `annulus (&1 / &2) (&2):real^3->bool`] THEN
    ASM_REWRITE_TAC[APX_CONNECTED_ANNULUS3];
    MATCH_MP_TAC APX_PARAM_CONNECTED_IMAGE THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`;
                          `annulus (&1 / &2) (&2):real^3->bool`] THEN
    ASM_REWRITE_TAC[APX_CONNECTED_ANNULUS3; SUBSET_REFL];
    MATCH_MP_TAC MFD_PARAM_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`;
                          `annulus (&1 / &2) (&2):real^3->bool`] THEN
    ASM_REWRITE_TAC[OPEN_ANNULUS; SUBSET_REFL];
    MATCH_MP_TAC MFD_PARAM_COMPACT_IMAGE THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`;
                          `annulus (&1 / &2) (&2):real^3->bool`] THEN
    ASM_REWRITE_TAC[COMPACT_SPHERE];
    REWRITE_TAC[GSYM IMAGE_UNION] THEN AP_TERM_TAC THEN
    REWRITE_TAC[EXTENSION; annulus; IN_UNION; IN_ELIM_THM; IN_SPHERE_0] THEN
    REAL_ARITH_TAC;
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_IMAGE; NOT_IN_EMPTY] THEN
    X_GEN_TAC `z:A` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC)
                               (X_CHOOSE_THEN `y':real^3` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `y:real^3 = y'` MP_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[annulus; IN_ELIM_THM; IN_SPHERE_0]) THEN
    ASM_REAL_ARITH_TAC;
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_IMAGE; NOT_IN_EMPTY] THEN
    X_GEN_TAC `z:A` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC)
                               (X_CHOOSE_THEN `y':real^3` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `y:real^3 = y'` MP_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[annulus; IN_ELIM_THM; IN_SPHERE_0]) THEN
    ASM_REAL_ARITH_TAC;
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_IMAGE; NOT_IN_EMPTY] THEN
    X_GEN_TAC `z:A` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC)
                               (X_CHOOSE_THEN `y':real^3` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `y:real^3 = y'` MP_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[annulus; IN_ELIM_THM; IN_SPHERE_0]) THEN
    ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC FUN_IN_IMAGE THEN
    SIMP_TAC[annulus; IN_ELIM_THM; NORM_MUL; NORM_BASIS; DIMINDEX_3; ARITH] THEN
    REAL_ARITH_TAC;
    MATCH_MP_TAC FUN_IN_IMAGE THEN
    SIMP_TAC[annulus; IN_ELIM_THM; NORM_MUL; NORM_BASIS; DIMINDEX_3; ARITH] THEN
    REAL_ARITH_TAC;
    FIRST_ASSUM(MP_TAC o MATCH_MP MFD_PARAM_MAPS) THEN
    DISCH_THEN(X_CHOOSE_THEN `e':A->real^3` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `IMAGE (e:real^3->A)
                  ((subtopology euclidean (annulus (&1 / &2) (&2))) closure_of
                   annulus (&1 / &2) (&1))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC IMAGE_SUBSET THEN
      REWRITE_TAC[CLOSURE_OF_SUBTOPOLOGY; EUCLIDEAN_CLOSURE_OF] THEN
      SUBGOAL_THEN `annulus (&1 / &2) (&2) INTER annulus (&1 / &2) (&1) =
                    annulus (&1 / &2) (&1):real^3->bool` SUBST1_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      MP_TAC(INST_TYPE [`:3`,`:N`] P4_SPHERE_CLOSURE_INNER) THEN
      ASM SET_TAC[];
      MATCH_MP_TAC CONTINUOUS_MAP_IMAGE_CLOSURE_SUBSET THEN ASM_REWRITE_TAC[]]]);;

(* The new stage as a subspace of the cut-and-capped manifold: open, closed, *)
(* connected and compact subsets are those of Z inside the stage.            *)

let P4_EVENT_SUBSPACE = prove
 (`!topX atlasX (gX:real->A->real^3^3) ts topY atlasY gY ev.
        rfs_event_ok (topX,atlasX) gX ts (topY,atlasY) gY ev
        ==> (!S. open_in topY S <=>
                 open_in (ev_ztop ev) S /\ S SUBSET topspace topY) /\
            (!S. closed_in topY S <=>
                 closed_in (ev_ztop ev) S /\ S SUBSET topspace topY) /\
            (!S. connected_in topY S <=>
                 connected_in (ev_ztop ev) S /\ S SUBSET topspace topY) /\
            (!S. compact_in topY S <=>
                 compact_in (ev_ztop ev) S /\ S SUBSET topspace topY)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rfs_event_ok] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
    is_eq(concl th) && lhs(concl th) = `topY:A topology`)) THEN
  REWRITE_TAC[TOPSPACE_SUBTOPOLOGY;
    SET_RULE `(s:A->bool) INTER (s DIFF t) = s DIFF t`] THEN
  SUBGOAL_THEN `open_in (ev_ztop ev) (topspace (ev_ztop ev) DIFF ev_disc (ev:(A)rfs_event)) /\
                closed_in (ev_ztop ev) (topspace (ev_ztop ev) DIFF ev_disc ev)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_IN_DIFF THEN ASM_REWRITE_TAC[OPEN_IN_TOPSPACE];
      MATCH_MP_TAC CLOSED_IN_DIFF THEN ASM_REWRITE_TAC[CLOSED_IN_TOPSPACE]];
    ALL_TAC] THEN
  ASM_SIMP_TAC[OPEN_IN_OPEN_SUBTOPOLOGY; CLOSED_IN_CLOSED_SUBTOPOLOGY;
               CONNECTED_IN_SUBTOPOLOGY; COMPACT_IN_SUBTOPOLOGY]);;

(* The caps of one event: the minus cap ball lies in the new stage, the plus *)
(* cap ball in the discarded part; the collars of the neck chart.            *)

let P4_EVENT_CAPS = prove
 (`!topX atlasX (gX:real->A->real^3^3) ts topY atlasY gY ev i.
        rfs_event_ok (topX,atlasX) gX ts (topY,atlasY) gY ev /\
        smooth_manifold_atlas topX (atlasX:((A->bool)#(A->real^3))->bool) /\
        i IN ev_index ev
        ==> mfd_neck_chart topX atlasX (ev_neck ev i) /\
            IMAGE (ev_capm ev i) (ball(vec 0,&2)) SUBSET topspace topY /\
            connected_in topY (IMAGE (ev_capm ev i) (ball(vec 0,&2))) /\
            open_in topY (IMAGE (ev_capm ev i) (ball(vec 0,&2))) /\
            IMAGE (ev_neck ev i) (annulus (&1 / &2) (&1)) SUBSET
            IMAGE (ev_capm ev i) (ball(vec 0,&2)) /\
            DISJOINT (IMAGE (ev_neck ev i) (annulus (&1) (&2))) (topspace topY) /\
            IMAGE (ev_capm ev i) (cball(vec 0,&1)) SUBSET
            mfd_cut_cores (ev_index ev) (ev_capp ev) (ev_capm ev) /\
            ev_capm ev i (vec 0) IN IMAGE (ev_capm ev i) (cball(vec 0,&1))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                 `gX:real->A->real^3^3`; `ts:real`; `topY:A topology`;
                 `atlasY:((A->bool)#(A->real^3))->bool`; `gY:real->A->real^3^3`;
                 `ev:(A)rfs_event`] P4_EVENT_FACTS) THEN
  MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                 `gX:real->A->real^3^3`; `ts:real`; `topY:A topology`;
                 `atlasY:((A->bool)#(A->real^3))->bool`; `gY:real->A->real^3^3`;
                 `ev:(A)rfs_event`] P4_EVENT_SUBSPACE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC o check (fun th ->
    try fst(dest_const(fst(strip_comb(concl th)))) = "mfd_cut_cap" with Failure _ -> false)) THEN
  REWRITE_TAC[mfd_cut_cap] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th ->
    try let t = snd(dest_forall(concl th)) in
        is_imp t && length(conjuncts(rand t)) = 3 &&
        (try fst(dest_const(fst(strip_comb(hd(conjuncts(rand t)))))) = "mfd_neck_chart"
         with Failure _ -> false)
    with Failure _ -> false)) THEN
  ASM_REWRITE_TAC[mfd_ball_chart] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `connected_in (ev_ztop ev) (IMAGE (ev_capm ev i) (ball(vec 0:real^3,&2))) /\
    open_in (ev_ztop ev) (IMAGE (ev_capm (ev:(A)rfs_event) i) (ball(vec 0:real^3,&2))) /\
    connected_in (ev_ztop ev) (IMAGE (ev_capp ev i) (ball(vec 0:real^3,&2))) /\
    IMAGE (ev_capm ev i) (ball(vec 0:real^3,&2)) SUBSET topspace (ev_ztop ev) /\
    IMAGE (ev_capp ev i) (ball(vec 0:real^3,&2)) SUBSET topspace (ev_ztop ev)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC APX_PARAM_CONNECTED_IMAGE THEN
      MAP_EVERY EXISTS_TAC [`ev_zatlas (ev:(A)rfs_event)`; `ball(vec 0:real^3,&2)`] THEN
      ASM_REWRITE_TAC[CONNECTED_BALL; SUBSET_REFL];
      MATCH_MP_TAC MFD_PARAM_IMAGE_OPEN THEN
      MAP_EVERY EXISTS_TAC [`ev_zatlas (ev:(A)rfs_event)`; `ball(vec 0:real^3,&2)`] THEN
      ASM_REWRITE_TAC[OPEN_BALL; SUBSET_REFL];
      MATCH_MP_TAC APX_PARAM_CONNECTED_IMAGE THEN
      MAP_EVERY EXISTS_TAC [`ev_zatlas (ev:(A)rfs_event)`; `ball(vec 0:real^3,&2)`] THEN
      ASM_REWRITE_TAC[CONNECTED_BALL; SUBSET_REFL];
      MATCH_MP_TAC MFD_PARAM_IMAGE_SUBSET THEN
      MAP_EVERY EXISTS_TAC [`ev_zatlas (ev:(A)rfs_event)`; `ball(vec 0:real^3,&2)`] THEN
      ASM_REWRITE_TAC[SUBSET_REFL];
      MATCH_MP_TAC MFD_PARAM_IMAGE_SUBSET THEN
      MAP_EVERY EXISTS_TAC [`ev_zatlas (ev:(A)rfs_event)`; `ball(vec 0:real^3,&2)`] THEN
      ASM_REWRITE_TAC[SUBSET_REFL]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(vec 0:real^3) IN cball(vec 0,&1) /\ (vec 0:real^3) IN ball(vec 0,&2)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[IN_CBALL_0; IN_BALL_0; NORM_0] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (ev_capm ev i) (ball(vec 0:real^3,&2)) SUBSET
    topspace (ev_ztop ev) DIFF ev_disc (ev:(A)rfs_event)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`ev_ztop (ev:(A)rfs_event)`;
                   `IMAGE (ev_capm (ev:(A)rfs_event) i) (ball(vec 0:real^3,&2))`;
                   `ev_disc (ev:(A)rfs_event)`] CONNECTED_IN_CLOPEN_CASES) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(SPEC `i:num` (ASSUME
     `!i. i IN ev_index ev
          ==> IMAGE (ev_capp ev i) (cball(vec 0:real^3,&1)) SUBSET ev_disc ev /\
              DISJOINT (IMAGE (ev_capm ev i) (cball(vec 0:real^3,&1)))
                       (ev_disc (ev:(A)rfs_event))`)) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`ev_capm (ev:(A)rfs_event) i`; `cball(vec 0:real^3,&1)`; `vec 0:real^3`]
                  FUN_IN_IMAGE) THEN
    MP_TAC(ISPECL [`ev_capm (ev:(A)rfs_event) i`; `ball(vec 0:real^3,&2)`; `vec 0:real^3`]
                  FUN_IN_IMAGE) THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (ev_capp ev i) (ball(vec 0:real^3,&2)) SUBSET ev_disc (ev:(A)rfs_event)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`ev_ztop (ev:(A)rfs_event)`;
                   `IMAGE (ev_capp (ev:(A)rfs_event) i) (ball(vec 0:real^3,&2))`;
                   `ev_disc (ev:(A)rfs_event)`] CONNECTED_IN_CLOPEN_CASES) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(SPEC `i:num` (ASSUME
     `!i. i IN ev_index ev
          ==> IMAGE (ev_capp ev i) (cball(vec 0:real^3,&1)) SUBSET ev_disc ev /\
              DISJOINT (IMAGE (ev_capm ev i) (cball(vec 0:real^3,&1)))
                       (ev_disc (ev:(A)rfs_event))`)) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`ev_capp (ev:(A)rfs_event) i`; `cball(vec 0:real^3,&1)`; `vec 0:real^3`]
                  FUN_IN_IMAGE) THEN
    MP_TAC(ISPECL [`ev_capp (ev:(A)rfs_event) i`; `ball(vec 0:real^3,&2)`; `vec 0:real^3`]
                  FUN_IN_IMAGE) THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `inv(norm(y:real^3) pow 2) % y` THEN
    CONJ_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[annulus; IN_ELIM_THM]) THEN
    REWRITE_TAC[IN_BALL_0; NORM_MUL; REAL_ABS_INV; REAL_ABS_POW; REAL_ABS_NORM] THEN
    SUBGOAL_THEN `inv(norm(y:real^3) pow 2) * norm y = inv(norm y)` SUBST1_TAC THENL
     [MATCH_MP_TAC(REAL_FIELD `~(x = &0) ==> inv(x pow 2) * x = inv x`) THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LT_LINV THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_IMAGE] THEN
    X_GEN_TAC `z:A` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) ASSUME_TAC) THEN
    SUBGOAL_THEN `(z:A) IN IMAGE (ev_capp ev i) (ball(vec 0:real^3,&2))` MP_TAC THENL
     [REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `y:real^3` THEN
      CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[annulus; IN_ELIM_THM]) THEN
      REWRITE_TAC[IN_BALL_0] THEN ASM_REAL_ARITH_TAC;
      ASM SET_TAC[]];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_MFD_CUT_CORES] THEN
    REWRITE_TAC[IN_CBALL_0] THEN ASM_MESON_TAC[];
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]]);;

(* A minus cap ball lies in a component of the new stage or misses it; the   *)
(* collars of the cut neck follow.                                           *)

let P4_CAP_IN_COMPONENT = prove
 (`!topX atlasX (gX:real->A->real^3^3) ts topY atlasY gY ev Y i.
        rfs_event_ok (topX,atlasX) gX ts (topY,atlasY) gY ev /\
        smooth_manifold_atlas topX (atlasX:((A->bool)#(A->real^3))->bool) /\
        Y IN connected_components_of topY /\ i IN ev_index ev
        ==> (ev_capm ev i (vec 0) IN Y
             ==> IMAGE (ev_capm ev i) (ball(vec 0,&2)) SUBSET Y /\
                 IMAGE (ev_neck ev i) (annulus (&1 / &2) (&1)) SUBSET
                 Y INTER topspace topX) /\
            (~(ev_capm ev i (vec 0) IN Y)
             ==> DISJOINT (IMAGE (ev_capm ev i) (ball(vec 0,&2))) Y /\
                 DISJOINT (IMAGE (ev_neck ev i) (annulus (&1 / &2) (&1))) Y) /\
            DISJOINT (IMAGE (ev_neck ev i) (annulus (&1) (&2))) Y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                 `gX:real->A->real^3^3`; `ts:real`; `topY:A topology`;
                 `atlasY:((A->bool)#(A->real^3))->bool`; `gY:real->A->real^3^3`;
                 `ev:(A)rfs_event`; `i:num`] P4_EVENT_CAPS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(Y:A->bool) SUBSET topspace topY` ASSUME_TAC THENL
   [ASM_MESON_TAC[CONNECTED_COMPONENTS_OF_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (ev_neck ev i) (annulus (&1 / &2) (&1)) SUBSET topspace (topX:A topology)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_PARAM_IMAGE_SUBSET THEN
    MAP_EVERY EXISTS_TAC [`atlasX:((A->bool)#(A->real^3))->bool`;
                          `annulus (&1 / &2) (&2):real^3->bool`] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[mfd_neck_chart]) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ev_capm ev i (vec 0) IN Y
    ==> IMAGE (ev_capm (ev:(A)rfs_event) i) (ball(vec 0,&2)) SUBSET Y`
  ASSUME_TAC THENL
   [DISCH_TAC THEN MATCH_MP_TAC CONNECTED_COMPONENTS_OF_MAXIMAL THEN
    EXISTS_TAC `topY:A topology` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SET_RULE `~DISJOINT (s:A->bool) t <=> ?x. x IN s /\ x IN t`] THEN
    EXISTS_TAC `ev_capm (ev:(A)rfs_event) i (vec 0)` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[IN_BALL_0; NORM_0] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `~(ev_capm ev i (vec 0) IN Y)
    ==> DISJOINT (IMAGE (ev_capm (ev:(A)rfs_event) i) (ball(vec 0,&2))) Y`
  ASSUME_TAC THENL
   [DISCH_TAC THEN
    ASM_CASES_TAC `DISJOINT (IMAGE (ev_capm (ev:(A)rfs_event) i) (ball(vec 0,&2)))
                            (Y:A->bool)` THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `IMAGE (ev_capm (ev:(A)rfs_event) i) (ball(vec 0,&2)) SUBSET Y`
    MP_TAC THENL
     [MATCH_MP_TAC CONNECTED_COMPONENTS_OF_MAXIMAL THEN
      EXISTS_TAC `topY:A topology` THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN(MP_TAC o SPEC `ev_capm (ev:(A)rfs_event) i (vec 0)`) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
    REWRITE_TAC[IN_BALL_0; NORM_0] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [DISCH_TAC THEN CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[SUBSET_INTER] THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    DISCH_TAC THEN CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ASM_REWRITE_TAC[] THEN
    ASM SET_TAC[];
    ASM SET_TAC[]]);;
(* The retained part Y0 = Y INTER topspace topX of a component Y of the new  *)
(* stage: off the cut spheres, inside Omega, open in the old stage, and Y    *)
(* minus Y0 is the union of the minus cap cores lying in Y.                  *)

let P4_RETAINED_BASIC = prove
 (`!topX atlasX (gX:real->A->real^3^3) ts topY atlasY gY ev Y.
        rfs_event_ok (topX,atlasX) gX ts (topY,atlasY) gY ev /\
        smooth_manifold_atlas topX (atlasX:((A->bool)#(A->real^3))->bool) /\
        Y IN connected_components_of topY
        ==> Y SUBSET topspace topY /\
            Y INTER topspace topX SUBSET
            topspace topX DIFF mfd_cut_spheres (ev_index ev) (ev_neck ev) /\
            Y INTER topspace topX SUBSET ev_omega ev /\
            Y INTER topspace topX =
            Y DIFF mfd_cut_cores (ev_index ev) (ev_capp ev) (ev_capm ev) /\
            Y DIFF topspace topX =
            UNIONS {IMAGE (ev_capm ev i) (cball(vec 0,&1)) | i |
                    i IN ev_index ev /\ ev_capm ev i (vec 0) IN Y} /\
            open_in topX (Y INTER topspace topX) /\
            ~(Y INTER topspace topX = {})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                 `gX:real->A->real^3^3`; `ts:real`; `topY:A topology`;
                 `atlasY:((A->bool)#(A->real^3))->bool`; `gY:real->A->real^3^3`;
                 `ev:(A)rfs_event`] P4_EVENT_FACTS) THEN
  MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                 `gX:real->A->real^3^3`; `ts:real`; `topY:A topology`;
                 `atlasY:((A->bool)#(A->real^3))->bool`; `gY:real->A->real^3^3`;
                 `ev:(A)rfs_event`] P4_EVENT_SUBSPACE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "sub") THEN STRIP_TAC THEN
  SUBGOAL_THEN `(Y:A->bool) SUBSET topspace topY` ASSUME_TAC THENL
   [ASM_MESON_TAC[CONNECTED_COMPONENTS_OF_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN
   `Y INTER topspace topX =
    Y DIFF mfd_cut_cores (ev_index ev) (ev_capp ev) (ev_capm (ev:(A)rfs_event))`
  ASSUME_TAC THENL
   [MAP_EVERY (fun t -> MP_TAC(ASSUME t))
     [`DISJOINT (topspace topX)
        (mfd_cut_cores (ev_index ev) (ev_capp ev) (ev_capm (ev:(A)rfs_event)))`;
      `topspace topX DIFF mfd_cut_spheres (ev_index ev) (ev_neck ev) =
       topspace (ev_ztop ev) DIFF
       mfd_cut_cores (ev_index ev) (ev_capp ev) (ev_capm (ev:(A)rfs_event))`;
      `topspace topY = topspace (ev_ztop ev) DIFF ev_disc (ev:(A)rfs_event)`;
      `(Y:A->bool) SUBSET topspace topY`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `Y INTER topspace topX SUBSET
    topspace topX DIFF mfd_cut_spheres (ev_index ev) (ev_neck (ev:(A)rfs_event))`
  ASSUME_TAC THENL
   [MAP_EVERY (fun t -> MP_TAC(ASSUME t))
     [`topspace topX DIFF mfd_cut_spheres (ev_index ev) (ev_neck ev) =
       topspace (ev_ztop ev) DIFF
       mfd_cut_cores (ev_index ev) (ev_capp ev) (ev_capm (ev:(A)rfs_event))`;
      `topspace topY = topspace (ev_ztop ev) DIFF ev_disc (ev:(A)rfs_event)`;
      `(Y:A->bool) SUBSET topspace topY`;
      `Y INTER topspace topX =
       Y DIFF mfd_cut_cores (ev_index ev) (ev_capp ev) (ev_capm (ev:(A)rfs_event))`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `Y DIFF topspace topX =
    UNIONS {IMAGE (ev_capm ev i) (cball(vec 0,&1)) | i |
            i IN ev_index ev /\ ev_capm (ev:(A)rfs_event) i (vec 0) IN Y}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_DIFF; IN_UNIONS; IN_ELIM_THM] THEN
      X_GEN_TAC `z:A` THEN STRIP_TAC THEN
      SUBGOAL_THEN
       `(z:A) IN mfd_cut_cores (ev_index ev) (ev_capp ev) (ev_capm (ev:(A)rfs_event))`
      MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[IN_MFD_CUT_CORES] THEN
      DISCH_THEN(X_CHOOSE_THEN `i:num` (X_CHOOSE_THEN `x:real^3` STRIP_ASSUME_TAC)) THENL
       [UNDISCH_TAC `(z:A) IN Y` THEN
        MP_TAC(SPEC `i:num` (ASSUME
         `!i. i IN ev_index ev
              ==> IMAGE (ev_capp ev i) (cball(vec 0:real^3,&1)) SUBSET ev_disc ev /\
                  DISJOINT (IMAGE (ev_capm ev i) (cball(vec 0:real^3,&1)))
                           (ev_disc (ev:(A)rfs_event))`)) THEN
        ASM_REWRITE_TAC[] THEN
        SUBGOAL_THEN `(z:A) IN IMAGE (ev_capp ev i) (cball(vec 0:real^3,&1))` MP_TAC THENL
         [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
          ASM_REWRITE_TAC[IN_CBALL_0];
          ASM SET_TAC[]];
        EXISTS_TAC `IMAGE (ev_capm (ev:(A)rfs_event) i) (cball(vec 0:real^3,&1))` THEN
        CONJ_TAC THENL
         [EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[] THEN
          MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                         `gX:real->A->real^3^3`; `ts:real`; `topY:A topology`;
                         `atlasY:((A->bool)#(A->real^3))->bool`; `gY:real->A->real^3^3`;
                         `ev:(A)rfs_event`; `Y:A->bool`; `i:num`] P4_CAP_IN_COMPONENT) THEN
          ASM_REWRITE_TAC[] THEN
          ASM_CASES_TAC `ev_capm (ev:(A)rfs_event) i (vec 0) IN Y` THEN ASM_REWRITE_TAC[] THEN
          DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT1) THEN
          REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
          DISCH_THEN(MP_TAC o SPEC `z:A`) THEN ASM_REWRITE_TAC[] THEN
          MATCH_MP_TAC FUN_IN_IMAGE THEN
          RULE_ASSUM_TAC(REWRITE_RULE[IN_CBALL_0]) THEN
          REWRITE_TAC[IN_BALL_0] THEN ASM_REAL_ARITH_TAC;
          ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
          ASM_REWRITE_TAC[IN_CBALL_0]]];
      REWRITE_TAC[SUBSET; IN_DIFF; IN_UNIONS; IN_ELIM_THM] THEN
      X_GEN_TAC `z:A` THEN
      DISCH_THEN(X_CHOOSE_THEN `c:A->bool` (CONJUNCTS_THEN2
        (X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
      MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                     `gX:real->A->real^3^3`; `ts:real`; `topY:A topology`;
                     `atlasY:((A->bool)#(A->real^3))->bool`; `gY:real->A->real^3^3`;
                     `ev:(A)rfs_event`; `Y:A->bool`; `i:num`] P4_CAP_IN_COMPONENT) THEN
      MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                     `gX:real->A->real^3^3`; `ts:real`; `topY:A topology`;
                     `atlasY:((A->bool)#(A->real^3))->bool`; `gY:real->A->real^3^3`;
                     `ev:(A)rfs_event`; `i:num`] P4_EVENT_CAPS) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN STRIP_TAC THEN
      SUBGOAL_THEN `cball(vec 0:real^3,&1) SUBSET ball(vec 0,&2)` ASSUME_TAC THENL
       [REWRITE_TAC[SUBSET; IN_CBALL_0; IN_BALL_0] THEN REAL_ARITH_TAC; ALL_TAC] THEN
      CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      MAP_EVERY (fun t -> MP_TAC(ASSUME t))
       [`DISJOINT (topspace topX)
          (mfd_cut_cores (ev_index ev) (ev_capp ev) (ev_capm (ev:(A)rfs_event)))`;
        `IMAGE (ev_capm ev i) (cball(vec 0:real^3,&1)) SUBSET
         mfd_cut_cores (ev_index ev) (ev_capp ev) (ev_capm (ev:(A)rfs_event))`;
        `(z:A) IN c`; `c = IMAGE (ev_capm (ev:(A)rfs_event) i) (cball(vec 0:real^3,&1))`] THEN
      SET_TAC[]];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
   [MAP_EVERY (fun t -> MP_TAC(ASSUME t))
     [`topspace topY INTER topspace topX SUBSET ev_omega (ev:(A)rfs_event)`;
      `(Y:A->bool) SUBSET topspace topY`] THEN
    SET_TAC[];
    SUBGOAL_THEN `open_in (ev_ztop ev) (Y:A->bool)` ASSUME_TAC THENL
     [USE_THEN "sub" (MP_TAC o SPEC `Y:A->bool` o CONJUNCT1) THEN
      DISCH_THEN(MP_TAC o fst o EQ_IMP_RULE) THEN
      ANTS_TAC THENL
       [MATCH_MP_TAC(ISPECL [`topY:A topology`; `atlasY:((A->bool)#(A->real^3))->bool`]
                            APX_COMPONENT_OPEN) THEN
        CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
        SIMP_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `open_in (ev_ztop ev)
        ((Y:A->bool) INTER (topspace (ev_ztop ev) DIFF
          mfd_cut_cores (ev_index ev) (ev_capp ev) (ev_capm (ev:(A)rfs_event))))`
    ASSUME_TAC THENL
     [MATCH_MP_TAC OPEN_IN_INTER THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    SUBST1_TAC(ASSUME `Y INTER topspace topX =
        Y DIFF mfd_cut_cores (ev_index ev) (ev_capp ev) (ev_capm (ev:(A)rfs_event))`) THEN
    SUBGOAL_THEN
     `Y DIFF mfd_cut_cores (ev_index ev) (ev_capp ev) (ev_capm (ev:(A)rfs_event)) =
      (Y:A->bool) INTER (topspace (ev_ztop ev) DIFF
          mfd_cut_cores (ev_index ev) (ev_capp ev) (ev_capm (ev:(A)rfs_event)))`
    SUBST1_TAC THENL
     [MAP_EVERY (fun t -> MP_TAC(ASSUME t))
       [`topspace topY = topspace (ev_ztop ev) DIFF ev_disc (ev:(A)rfs_event)`;
        `(Y:A->bool) SUBSET topspace topY`] THEN
      SET_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC OPEN_IN_TRANS_FULL THEN
    EXISTS_TAC `topspace topX DIFF mfd_cut_spheres (ev_index ev) (ev_neck (ev:(A)rfs_event))` THEN
    CONJ_TAC THENL [ALL_TAC; FIRST_ASSUM ACCEPT_TAC] THEN
    SUBST1_TAC(ASSUME
     `subtopology topX (topspace topX DIFF mfd_cut_spheres (ev_index ev) (ev_neck ev)) =
      subtopology (ev_ztop ev) (topspace (ev_ztop ev) DIFF
        mfd_cut_cores (ev_index ev) (ev_capp ev) (ev_capm (ev:(A)rfs_event)))`) THEN
    MATCH_MP_TAC OPEN_IN_SUBSET_TOPSPACE THEN
    CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; SET_TAC[]];
    ASM_CASES_TAC `?i. i IN ev_index ev /\ ev_capm (ev:(A)rfs_event) i (vec 0) IN Y` THENL
     [FIRST_X_ASSUM(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
      MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                     `gX:real->A->real^3^3`; `ts:real`; `topY:A topology`;
                     `atlasY:((A->bool)#(A->real^3))->bool`; `gY:real->A->real^3^3`;
                     `ev:(A)rfs_event`; `Y:A->bool`; `i:num`] P4_CAP_IN_COMPONENT) THEN
      MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                     `gX:real->A->real^3^3`; `ts:real`; `topY:A topology`;
                     `atlasY:((A->bool)#(A->real^3))->bool`; `gY:real->A->real^3^3`;
                     `ev:(A)rfs_event`; `i:num`] P4_EVENT_CAPS) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN
      DISCH_THEN(MP_TAC o MATCH_MP P4_NECK_PIECES) THEN STRIP_TAC THEN STRIP_TAC THEN
      ASM SET_TAC[];
      SUBGOAL_THEN `(Y:A->bool) SUBSET topspace topX` ASSUME_TAC THENL
       [MATCH_MP_TAC(SET_RULE `!u. Y DIFF x = UNIONS u /\ u = {} ==> (Y:A->bool) SUBSET x`) THEN
        EXISTS_TAC `{IMAGE (ev_capm ev i) (cball(vec 0,&1)) | i |
                     i IN ev_index ev /\ ev_capm (ev:(A)rfs_event) i (vec 0) IN Y}` THEN
        ASM_REWRITE_TAC[] THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN
        ASM_MESON_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `~(Y:A->bool = {})` MP_TAC THENL
       [ASM_MESON_TAC[NONEMPTY_CONNECTED_COMPONENTS_OF]; ASM SET_TAC[]]]]);;
(* Y0 is connected: Y minus finitely many disjoint closed balls with         *)
(* connected collars (APX_CONNECTED_REMOVE).                                 *)

let P4_RETAINED_CONNECTED = prove
 (`!topX atlasX (gX:real->A->real^3^3) ts topY atlasY gY ev Y.
        rfs_event_ok (topX,atlasX) gX ts (topY,atlasY) gY ev /\
        smooth_manifold_atlas topX (atlasX:((A->bool)#(A->real^3))->bool) /\
        Y IN connected_components_of topY
        ==> connected_in topX (Y INTER topspace topX)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                 `gX:real->A->real^3^3`; `ts:real`; `topY:A topology`;
                 `atlasY:((A->bool)#(A->real^3))->bool`; `gY:real->A->real^3^3`;
                 `ev:(A)rfs_event`; `Y:A->bool`] P4_RETAINED_BASIC) THEN
  MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                 `gX:real->A->real^3^3`; `ts:real`; `topY:A topology`;
                 `atlasY:((A->bool)#(A->real^3))->bool`; `gY:real->A->real^3^3`;
                 `ev:(A)rfs_event`] P4_EVENT_FACTS) THEN
  MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                 `gX:real->A->real^3^3`; `ts:real`; `topY:A topology`;
                 `atlasY:((A->bool)#(A->real^3))->bool`; `gY:real->A->real^3^3`;
                 `ev:(A)rfs_event`] P4_EVENT_SUBSPACE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "sub") THEN STRIP_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `subtopology topX (Y INTER topspace topX) =
    subtopology (ev_ztop (ev:(A)rfs_event)) (Y INTER topspace (topX:A topology))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `subtopology (subtopology topX
                  (topspace topX DIFF mfd_cut_spheres (ev_index ev) (ev_neck ev)))
                  (Y INTER topspace (topX:A topology))` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[SUBTOPOLOGY_SUBTOPOLOGY] THEN AP_TERM_TAC THEN ASM SET_TAC[];
      ALL_TAC] THEN
    SUBST1_TAC(ASSUME
     `subtopology topX (topspace topX DIFF mfd_cut_spheres (ev_index ev) (ev_neck ev)) =
      subtopology (ev_ztop ev) (topspace (ev_ztop ev) DIFF
        mfd_cut_cores (ev_index ev) (ev_capp ev) (ev_capm (ev:(A)rfs_event)))`) THEN
    REWRITE_TAC[SUBTOPOLOGY_SUBTOPOLOGY] THEN AP_TERM_TAC THEN
    MAP_EVERY (fun t -> MP_TAC(ASSUME t))
     [`Y INTER topspace topX SUBSET
       topspace topX DIFF mfd_cut_spheres (ev_index ev) (ev_neck (ev:(A)rfs_event))`;
      `topspace topX DIFF mfd_cut_spheres (ev_index ev) (ev_neck ev) =
       topspace (ev_ztop ev) DIFF
       mfd_cut_cores (ev_index ev) (ev_capp ev) (ev_capm (ev:(A)rfs_event))`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `connected_in (ev_ztop ev) (Y INTER topspace (topX:A topology))` MP_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[connected_in] THEN
    REWRITE_TAC[ASSUME `subtopology topX (Y INTER topspace topX) =
                        subtopology (ev_ztop (ev:(A)rfs_event))
                                    (Y INTER topspace (topX:A topology))`] THEN
    SIMP_TAC[INTER_SUBSET]] THEN
  MATCH_MP_TAC APX_CONNECTED_REMOVE THEN
  MAP_EVERY EXISTS_TAC
   [`Y:A->bool`; `{i | i IN ev_index ev /\ ev_capm (ev:(A)rfs_event) i (vec 0) IN Y}`;
    `\i. IMAGE (ev_capm (ev:(A)rfs_event) i) (ball(vec 0:real^3,&2))`;
    `\i. IMAGE (ev_capm (ev:(A)rfs_event) i) (cball(vec 0:real^3,&1))`] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN `connected_in topY (Y:A->bool)` MP_TAC THENL
     [ASM_MESON_TAC[CONNECTED_IN_CONNECTED_COMPONENTS_OF]; ALL_TAC] THEN
    USE_THEN "sub" (fun th -> REWRITE_TAC[th]) THEN SIMP_TAC[];
    MATCH_MP_TAC OPEN_IN_TRANS_FULL THEN
    EXISTS_TAC `topspace (ev_ztop ev) DIFF
      mfd_cut_cores (ev_index ev) (ev_capp ev) (ev_capm (ev:(A)rfs_event))` THEN
    CONJ_TAC THENL [ALL_TAC; FIRST_ASSUM ACCEPT_TAC] THEN
    SUBST1_TAC(SYM(ASSUME
     `subtopology topX (topspace topX DIFF mfd_cut_spheres (ev_index ev) (ev_neck ev)) =
      subtopology (ev_ztop ev) (topspace (ev_ztop ev) DIFF
        mfd_cut_cores (ev_index ev) (ev_capp ev) (ev_capm (ev:(A)rfs_event)))`)) THEN
    MATCH_MP_TAC OPEN_IN_SUBSET_TOPSPACE THEN
    CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    SUBST1_TAC(SYM(ASSUME
     `Y DIFF topspace topX =
       UNIONS {IMAGE (ev_capm ev i) (cball(vec 0,&1)) | i |
               i IN ev_index ev /\ ev_capm (ev:(A)rfs_event) i (vec 0) IN Y}`)) THEN
    SET_TAC[];
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                   `gX:real->A->real^3^3`; `ts:real`; `topY:A topology`;
                   `atlasY:((A->bool)#(A->real^3))->bool`; `gY:real->A->real^3^3`;
                   `ev:(A)rfs_event`; `Y:A->bool`; `i:num`] P4_CAP_IN_COMPONENT) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
    MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                   `gX:real->A->real^3^3`; `ts:real`; `topY:A topology`;
                   `atlasY:((A->bool)#(A->real^3))->bool`; `gY:real->A->real^3^3`;
                   `ev:(A)rfs_event`; `i:num`] P4_EVENT_CAPS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    FIRST_ASSUM(MP_TAC o check (fun th ->
      try fst(dest_const(fst(strip_comb(concl th)))) = "mfd_cut_cap" with Failure _ -> false)) THEN
    REWRITE_TAC[mfd_cut_cap] THEN
    DISCH_THEN(MP_TAC o SPEC `i:num` o CONJUNCT1 o CONJUNCT2) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; REWRITE_TAC[mfd_ball_chart] THEN STRIP_TAC] THEN
    SUBGOAL_THEN
     `IMAGE (ev_capm (ev:(A)rfs_event) i) (ball(vec 0:real^3,&2)) DIFF
      IMAGE (ev_capm ev i) (cball(vec 0,&1)) =
      IMAGE (ev_capm ev i) (annulus (&1) (&2))`
    SUBST1_TAC THENL
     [MP_TAC(ISPECL [`ev_ztop (ev:(A)rfs_event)`; `ev_zatlas (ev:(A)rfs_event)`;
                     `ball(vec 0:real^3,&2)`; `ball(vec 0:real^3,&2)`; `cball(vec 0:real^3,&1)`;
                     `ev_capm (ev:(A)rfs_event) i`] APX_PARAM_IMAGE_DIFF) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[SUBSET_REFL] THEN
        REWRITE_TAC[SUBSET; IN_BALL_0; IN_CBALL_0] THEN REAL_ARITH_TAC;
        DISCH_THEN SUBST1_TAC] THEN
      AP_TERM_TAC THEN
      REWRITE_TAC[EXTENSION; IN_DIFF; IN_BALL_0; IN_CBALL_0; annulus; IN_ELIM_THM] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [USE_THEN "sub" (MP_TAC o SPEC `IMAGE (ev_capm (ev:(A)rfs_event) i)
                                         (ball(vec 0:real^3,&2))` o CONJUNCT1) THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[];
      FIRST_ASSUM ACCEPT_TAC;
      MATCH_MP_TAC IMAGE_SUBSET THEN
      REWRITE_TAC[SUBSET; IN_BALL_0; IN_CBALL_0] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC APX_PARAM_CONNECTED_IMAGE THEN
      MAP_EVERY EXISTS_TAC [`ev_zatlas (ev:(A)rfs_event)`; `ball(vec 0:real^3,&2)`] THEN
      ASM_REWRITE_TAC[APX_CONNECTED_ANNULUS3] THEN
      REWRITE_TAC[SUBSET; IN_BALL_0; annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC;
      REWRITE_TAC[IMAGE_EQ_EMPTY] THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
      EXISTS_TAC `&3 / &2 % basis 1:real^3` THEN
      SIMP_TAC[annulus; IN_ELIM_THM; NORM_MUL; NORM_BASIS; DIMINDEX_3; ARITH] THEN
      REAL_ARITH_TAC];
    MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o check (fun th ->
      try fst(dest_const(fst(strip_comb(concl th)))) = "mfd_cut_cap" with Failure _ -> false)) THEN
    REWRITE_TAC[mfd_cut_cap] THEN
    DISCH_THEN(MP_TAC o SPECL [`i:num`; `j:num`] o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
    ASM_SIMP_TAC[]]);;
(* The closure of Y0 in the old stage adds exactly the cut spheres of the    *)
(* necks whose minus caps lie in Y.                                          *)

let P4_RETAINED_CLOSURE = prove
 (`!topX atlasX (gX:real->A->real^3^3) ts topY atlasY gY ev Y.
        rfs_event_ok (topX,atlasX) gX ts (topY,atlasY) gY ev /\
        smooth_manifold_atlas topX (atlasX:((A->bool)#(A->real^3))->bool) /\
        Y IN connected_components_of topY
        ==> topX closure_of (Y INTER topspace topX) SUBSET
            (Y INTER topspace topX) UNION
            UNIONS {IMAGE (ev_neck ev i) (sphere(vec 0,&1)) | i |
                    i IN ev_index ev /\ ev_capm ev i (vec 0) IN Y} /\
            (!i. i IN ev_index ev /\ ev_capm ev i (vec 0) IN Y
                 ==> IMAGE (ev_neck ev i) (sphere(vec 0,&1)) SUBSET
                     topX closure_of (Y INTER topspace topX))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                 `gX:real->A->real^3^3`; `ts:real`; `topY:A topology`;
                 `atlasY:((A->bool)#(A->real^3))->bool`; `gY:real->A->real^3^3`;
                 `ev:(A)rfs_event`; `Y:A->bool`] P4_RETAINED_BASIC) THEN
  MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                 `gX:real->A->real^3^3`; `ts:real`; `topY:A topology`;
                 `atlasY:((A->bool)#(A->real^3))->bool`; `gY:real->A->real^3^3`;
                 `ev:(A)rfs_event`] P4_EVENT_FACTS) THEN
  MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                 `gX:real->A->real^3^3`; `ts:real`; `topY:A topology`;
                 `atlasY:((A->bool)#(A->real^3))->bool`; `gY:real->A->real^3^3`;
                 `ev:(A)rfs_event`] P4_EVENT_SUBSPACE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "sub") THEN STRIP_TAC THEN STRIP_TAC THEN
  CONJ_TAC THENL
   [ALL_TAC;
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                   `gX:real->A->real^3^3`; `ts:real`; `topY:A topology`;
                   `atlasY:((A->bool)#(A->real^3))->bool`; `gY:real->A->real^3^3`;
                   `ev:(A)rfs_event`; `Y:A->bool`; `i:num`] P4_CAP_IN_COMPONENT) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
    MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                   `gX:real->A->real^3^3`; `ts:real`; `topY:A topology`;
                   `atlasY:((A->bool)#(A->real^3))->bool`; `gY:real->A->real^3^3`;
                   `ev:(A)rfs_event`; `i:num`] P4_EVENT_CAPS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o MATCH_MP P4_NECK_PIECES o CONJUNCT1) THEN STRIP_TAC THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `(topX:A topology) closure_of IMAGE (ev_neck (ev:(A)rfs_event) i) (annulus (&1 / &2) (&1))` THEN
    CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    MATCH_MP_TAC CLOSURE_OF_MONO THEN FIRST_ASSUM ACCEPT_TAC] THEN
  REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(x:A) IN topspace topX` ASSUME_TAC THENL
   [ASM_MESON_TAC[CLOSURE_OF_SUBSET_TOPSPACE; SUBSET]; ALL_TAC] THEN
  ASM_CASES_TAC
   `(x:A) IN mfd_cut_spheres (ev_index ev) (ev_neck (ev:(A)rfs_event))` THENL
   [FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_MFD_CUT_SPHERES]) THEN
    DISCH_THEN(X_CHOOSE_THEN `j:num` (X_CHOOSE_THEN `y:real^3`
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)))) THEN
    ASM_CASES_TAC `ev_capm (ev:(A)rfs_event) j (vec 0) IN Y` THENL
     [REWRITE_TAC[IN_UNION; IN_UNIONS; IN_ELIM_THM] THEN DISJ2_TAC THEN
      EXISTS_TAC `IMAGE (ev_neck (ev:(A)rfs_event) j) (sphere(vec 0,&1))` THEN
      CONJ_TAC THENL [EXISTS_TAC `j:num` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
      ASM_REWRITE_TAC[IN_SPHERE_0];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                   `gX:real->A->real^3^3`; `ts:real`; `topY:A topology`;
                   `atlasY:((A->bool)#(A->real^3))->bool`; `gY:real->A->real^3^3`;
                   `ev:(A)rfs_event`; `Y:A->bool`; `j:num`] P4_CAP_IN_COMPONENT) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
    MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                   `gX:real->A->real^3^3`; `ts:real`; `topY:A topology`;
                   `atlasY:((A->bool)#(A->real^3))->bool`; `gY:real->A->real^3^3`;
                   `ev:(A)rfs_event`; `j:num`] P4_EVENT_CAPS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o MATCH_MP P4_NECK_PIECES o CONJUNCT1) THEN STRIP_TAC THEN
    MP_TAC(ASSUME `(x:A) IN topX closure_of (Y INTER topspace topX)`) THEN
    REWRITE_TAC[IN_CLOSURE_OF] THEN
    DISCH_THEN(MP_TAC o SPEC `IMAGE (ev_neck (ev:(A)rfs_event) j) (annulus (&1 / &2) (&2))` o
               CONJUNCT2) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL [ALL_TAC; FIRST_ASSUM ACCEPT_TAC] THEN
      SUBST1_TAC(ASSUME `x = ev_neck (ev:(A)rfs_event) j y`) THEN
      MATCH_MP_TAC FUN_IN_IMAGE THEN
      REWRITE_TAC[annulus; IN_ELIM_THM] THEN
      MP_TAC(ASSUME `norm(y:real^3) = &1`) THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `z:A` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN
     `IMAGE (ev_neck ev j) (sphere(vec 0,&1)) SUBSET
      mfd_cut_spheres (ev_index ev) (ev_neck (ev:(A)rfs_event))`
    ASSUME_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_SPHERE_0; IN_MFD_CUT_SPHERES] THEN
      X_GEN_TAC `y':real^3` THEN DISCH_TAC THEN
      MAP_EVERY EXISTS_TAC [`j:num`; `y':real^3`] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MAP_EVERY (fun t -> MP_TAC(ASSUME t))
     [`IMAGE (ev_neck ev j) (annulus (&1 / &2) (&2)) =
       IMAGE (ev_neck ev j) (annulus (&1 / &2) (&1)) UNION
       IMAGE (ev_neck ev j) (sphere(vec 0,&1)) UNION
       IMAGE (ev_neck (ev:(A)rfs_event) j) (annulus (&1) (&2))`;
      `DISJOINT (IMAGE (ev_neck ev j) (annulus (&1 / &2) (&1))) (Y:A->bool)`;
      `DISJOINT (IMAGE (ev_neck ev j) (annulus (&1) (&2))) (Y:A->bool)`;
      `Y INTER topspace topX SUBSET
       topspace topX DIFF mfd_cut_spheres (ev_index ev) (ev_neck (ev:(A)rfs_event))`;
      `IMAGE (ev_neck ev j) (sphere(vec 0,&1)) SUBSET
       mfd_cut_spheres (ev_index ev) (ev_neck (ev:(A)rfs_event))`;
      `(z:A) IN Y INTER topspace topX`;
      `(z:A) IN IMAGE (ev_neck (ev:(A)rfs_event) j) (annulus (&1 / &2) (&2))`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[IN_UNION] THEN DISJ1_TAC THEN
  SUBGOAL_THEN `closed_in (ev_ztop ev) (Y:A->bool)` ASSUME_TAC THENL
   [USE_THEN "sub" (MP_TAC o SPEC `Y:A->bool` o CONJUNCT1 o CONJUNCT2) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN
    ASM_MESON_TAC[CLOSED_IN_CONNECTED_COMPONENTS_OF];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(x:A) IN (subtopology topX
       (topspace topX DIFF mfd_cut_spheres (ev_index ev) (ev_neck (ev:(A)rfs_event))))
       closure_of (Y INTER topspace topX)`
  MP_TAC THENL
   [REWRITE_TAC[CLOSURE_OF_SUBTOPOLOGY; IN_INTER] THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[IN_DIFF]; ALL_TAC] THEN
    SUBGOAL_THEN
     `(topspace topX DIFF mfd_cut_spheres (ev_index ev) (ev_neck (ev:(A)rfs_event))) INTER
      (Y INTER topspace topX) = Y INTER topspace topX`
    SUBST1_TAC THENL
     [MP_TAC(ASSUME `Y INTER topspace topX SUBSET
        topspace topX DIFF mfd_cut_spheres (ev_index ev) (ev_neck (ev:(A)rfs_event))`) THEN
      SET_TAC[];
      FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  SUBST1_TAC(ASSUME
   `subtopology topX (topspace topX DIFF mfd_cut_spheres (ev_index ev) (ev_neck ev)) =
    subtopology (ev_ztop ev) (topspace (ev_ztop ev) DIFF
      mfd_cut_cores (ev_index ev) (ev_capp ev) (ev_capm (ev:(A)rfs_event)))`) THEN
  REWRITE_TAC[CLOSURE_OF_SUBTOPOLOGY; IN_INTER] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(x:A) IN Y` MP_TAC THENL
   [SUBGOAL_THEN
     `(ev_ztop ev) closure_of
        ((topspace (ev_ztop ev) DIFF
          mfd_cut_cores (ev_index ev) (ev_capp ev) (ev_capm (ev:(A)rfs_event))) INTER
         (Y INTER topspace (topX:A topology))) SUBSET Y`
    MP_TAC THENL
     [MATCH_MP_TAC CLOSURE_OF_MINIMAL THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
      MP_TAC(ASSUME `(x:A) IN (ev_ztop ev) closure_of
        ((topspace (ev_ztop ev) DIFF
          mfd_cut_cores (ev_index ev) (ev_capp ev) (ev_capm (ev:(A)rfs_event))) INTER
         (Y INTER topspace (topX:A topology)))`) THEN
      SET_TAC[]];
    MP_TAC(ASSUME `(x:A) IN topspace topX`) THEN SET_TAC[]]);;

(* The two sides of a neck-chart sphere: the components of its complement   *)
(* through e(3/4 b1) and e(4/3 b1).  Open (manifolds are locally connected),*)
(* maximal among connected sets missing the sphere, and their closures add  *)
(* only points of the sphere.                                                *)

let p4_side = new_definition
 `p4_side (top:A topology) (e:real^3->A) (p:A) =
    connected_component_of
      (subtopology top (topspace top DIFF IMAGE e (sphere(vec 0,&1)))) p`;;

let P4_SIDE_FACTS = prove
 (`!top atlas (e:real^3->A) p.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        mfd_neck_chart top atlas e /\
        p IN topspace top DIFF IMAGE e (sphere(vec 0,&1))
        ==> open_in top (p4_side top e p) /\
            connected_in top (p4_side top e p) /\
            p IN p4_side top e p /\
            p4_side top e p SUBSET topspace top DIFF IMAGE e (sphere(vec 0,&1)) /\
            (!C. connected_in top C /\ DISJOINT C (IMAGE e (sphere(vec 0,&1))) /\ p IN C
                 ==> C SUBSET p4_side top e p) /\
            (!q. q IN p4_side top e p ==> p4_side top e q = p4_side top e p) /\
            top closure_of (p4_side top e p) SUBSET
            p4_side top e p UNION IMAGE e (sphere(vec 0,&1))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P4_NECK_PIECES) THEN
  REWRITE_TAC[p4_side] THEN
  ABBREV_TAC `O = topspace top DIFF IMAGE (e:real^3->A) (sphere(vec 0,&1))` THEN
  SUBGOAL_THEN `open_in top (O:A->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "O" THEN MATCH_MP_TAC OPEN_IN_DIFF THEN
    REWRITE_TAC[OPEN_IN_TOPSPACE] THEN MATCH_MP_TAC COMPACT_IN_IMP_CLOSED_IN THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(O:A->bool) SUBSET topspace top` ASSUME_TAC THENL
   [EXPAND_TAC "O" THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!q:A. q IN O ==> q IN topspace (subtopology top O)` ASSUME_TAC THENL
   [REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER] THEN ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `locally_connected_space (top:A topology)` ASSUME_TAC THENL
   [MATCH_MP_TAC LOCALLY_PATH_CONNECTED_IMP_LOCALLY_CONNECTED_SPACE THEN
    ASM_MESON_TAC[GEO_MANIFOLD_LOCALLY_PATH_CONNECTED];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!q:A. q IN O ==> open_in top (connected_component_of (subtopology top O) q)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [LOCALLY_CONNECTED_SPACE_OPEN_CONNECTED_COMPONENTS]) THEN
    DISCH_THEN MATCH_MP_TAC THEN EXISTS_TAC `O:A->bool` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[CONNECTED_COMPONENT_IN_CONNECTED_COMPONENTS_OF] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!q:A. connected_component_of (subtopology top O) q SUBSET O` ASSUME_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`subtopology top (O:A->bool)`; `q:A`]
                  CONNECTED_COMPONENT_OF_SUBSET_TOPSPACE) THEN
    REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!q:A. q IN O ==> q IN connected_component_of (subtopology top O) q`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[IN] THEN REWRITE_TAC[CONNECTED_COMPONENT_OF_REFL] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      try fst(dest_const(fst(strip_comb(rand(rand(snd(strip_forall(concl th)))))))) =
          "topspace" with Failure _ -> false)) THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      try fst(dest_const(fst(strip_comb(rand(snd(strip_forall(concl th))))))) = "open_in"
      with Failure _ -> false)) THEN FIRST_ASSUM ACCEPT_TAC;
    MP_TAC(ISPECL [`subtopology top (O:A->bool)`; `p:A`]
           CONNECTED_IN_CONNECTED_COMPONENT_OF) THEN
    SIMP_TAC[CONNECTED_IN_SUBTOPOLOGY];
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      try is_imp(snd(strip_forall(concl th))) &&
          fst(dest_const(fst(strip_comb(rand(snd(strip_forall(concl th))))))) = "IN" &&
          (try fst(dest_const(fst(strip_comb(rand(rand(snd(strip_forall(concl th)))))))) =
               "connected_component_of" with Failure _ -> false)
      with Failure _ -> false)) THEN FIRST_ASSUM ACCEPT_TAC;
    ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC CONNECTED_COMPONENT_OF_MAXIMAL THEN
    ASM_REWRITE_TAC[CONNECTED_IN_SUBTOPOLOGY] THEN
    MP_TAC(MATCH_MP CONNECTED_IN_SUBSET_TOPSPACE (ASSUME `connected_in top (C:A->bool)`)) THEN
    MP_TAC(ASSUME `DISJOINT (C:A->bool) (IMAGE (e:real^3->A) (sphere(vec 0,&1)))`) THEN
    EXPAND_TAC "O" THEN SET_TAC[];
    REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
    REWRITE_TAC[CONNECTED_COMPONENT_OF_EQ] THEN DISJ2_TAC THEN
    SUBGOAL_THEN `(q:A) IN O` ASSUME_TAC THENL
     [MP_TAC(SPEC `p:A` (ASSUME
        `!q:A. connected_component_of (subtopology top O) q SUBSET O`)) THEN
      MP_TAC(ASSUME `(q:A) IN connected_component_of (subtopology top O) p`) THEN
      SET_TAC[];
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        try fst(dest_const(fst(strip_comb(rand(rand(snd(strip_forall(concl th)))))))) =
            "topspace" with Failure _ -> false)) THEN FIRST_ASSUM ACCEPT_TAC;
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        try fst(dest_const(fst(strip_comb(rand(rand(snd(strip_forall(concl th)))))))) =
            "topspace" with Failure _ -> false)) THEN FIRST_ASSUM ACCEPT_TAC;
      MP_TAC(ASSUME `(q:A) IN connected_component_of (subtopology top O) p`) THEN
      REWRITE_TAC[IN]];
    REWRITE_TAC[SUBSET; IN_UNION] THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    ASM_CASES_TAC `(x:A) IN IMAGE (e:real^3->A) (sphere(vec 0:real^3,&1))` THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`;
                     `connected_component_of (subtopology top O) (p:A)`]
                    CLOSURE_OF_SUBSET_TOPSPACE) THEN
      MP_TAC(ASSUME `(x:A) IN top closure_of connected_component_of (subtopology top O) p`) THEN
      SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(x:A) IN O` ASSUME_TAC THENL
     [EXPAND_TAC "O" THEN REWRITE_TAC[IN_DIFF] THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_CLOSURE_OF] o check (fun th ->
      try fst(dest_const(fst(strip_comb(rand(concl th))))) = "closure_of"
      with Failure _ -> false)) THEN
    DISCH_THEN(MP_TAC o SPEC `connected_component_of (subtopology top O) (x:A)` o CONJUNCT2) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
          try is_imp(snd(strip_forall(concl th))) &&
              (try fst(dest_const(fst(strip_comb(rand(rand(snd(strip_forall(concl th)))))))) =
                   "connected_component_of" with Failure _ -> false)
          with Failure _ -> false)) THEN FIRST_ASSUM ACCEPT_TAC;
        FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
          try fst(dest_const(fst(strip_comb(rand(snd(strip_forall(concl th))))))) = "open_in"
          with Failure _ -> false)) THEN FIRST_ASSUM ACCEPT_TAC];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:A` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN
     `connected_component_of (subtopology top O) (x:A) =
      connected_component_of (subtopology top O) (p:A)`
    (SUBST1_TAC o SYM) THENL
     [REWRITE_TAC[CONNECTED_COMPONENT_OF_EQ_OVERLAP] THEN DISJ2_TAC THEN
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN EXISTS_TAC `y:A` THEN
      CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      try is_imp(snd(strip_forall(concl th))) &&
          (try fst(dest_const(fst(strip_comb(rand(rand(snd(strip_forall(concl th)))))))) =
               "connected_component_of" with Failure _ -> false)
      with Failure _ -> false)) THEN FIRST_ASSUM ACCEPT_TAC]);;

(* For a neck i whose minus cap lies in Y: the branch B_i (the side of the  *)
(* cut sphere through e_i(4/3 b1)) contains the plus collar and misses Y0,  *)
(* which lies on the other side (separation of the cut spheres).            *)

let P4_BRANCH_BASIC = prove
 (`!topX atlasX (gX:real->A->real^3^3) ts topY atlasY gY ev Y i.
        rfs_event_ok (topX,atlasX) gX ts (topY,atlasY) gY ev /\
        hausdorff_space topX /\
        smooth_manifold_atlas topX (atlasX:((A->bool)#(A->real^3))->bool) /\
        apx_sphere_sep topX atlasX /\
        Y IN connected_components_of topY /\
        i IN ev_index ev /\ ev_capm ev i (vec 0) IN Y
        ==> open_in topX (p4_side topX (ev_neck ev i) (ev_neck ev i (&4 / &3 % basis 1))) /\
            connected_in topX
              (p4_side topX (ev_neck ev i) (ev_neck ev i (&4 / &3 % basis 1))) /\
            IMAGE (ev_neck ev i) (annulus (&1) (&2)) SUBSET
            p4_side topX (ev_neck ev i) (ev_neck ev i (&4 / &3 % basis 1)) /\
            DISJOINT (p4_side topX (ev_neck ev i) (ev_neck ev i (&4 / &3 % basis 1)))
                     (IMAGE (ev_neck ev i) (sphere(vec 0,&1))) /\
            DISJOINT (p4_side topX (ev_neck ev i) (ev_neck ev i (&4 / &3 % basis 1)))
                     (Y INTER topspace topX) /\
            (!q. q IN p4_side topX (ev_neck ev i) (ev_neck ev i (&4 / &3 % basis 1))
                 ==> p4_side topX (ev_neck ev i) q =
                     p4_side topX (ev_neck ev i) (ev_neck ev i (&4 / &3 % basis 1))) /\
            (!C. connected_in topX C /\ DISJOINT C (IMAGE (ev_neck ev i) (sphere(vec 0,&1))) /\
                 ev_neck ev i (&3 / &4 % basis 1) IN C
                 ==> ~(ev_neck ev i (&4 / &3 % basis 1) IN C)) /\
            topX closure_of (p4_side topX (ev_neck ev i) (ev_neck ev i (&4 / &3 % basis 1)))
            SUBSET p4_side topX (ev_neck ev i) (ev_neck ev i (&4 / &3 % basis 1)) UNION
                   IMAGE (ev_neck ev i) (sphere(vec 0,&1))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                 `gX:real->A->real^3^3`; `ts:real`; `topY:A topology`;
                 `atlasY:((A->bool)#(A->real^3))->bool`; `gY:real->A->real^3^3`;
                 `ev:(A)rfs_event`; `i:num`] P4_EVENT_CAPS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P4_NECK_PIECES) THEN
  MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                 `gX:real->A->real^3^3`; `ts:real`; `topY:A topology`;
                 `atlasY:((A->bool)#(A->real^3))->bool`; `gY:real->A->real^3^3`;
                 `ev:(A)rfs_event`; `Y:A->bool`; `i:num`] P4_CAP_IN_COMPONENT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
  MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                 `gX:real->A->real^3^3`; `ts:real`; `topY:A topology`;
                 `atlasY:((A->bool)#(A->real^3))->bool`; `gY:real->A->real^3^3`;
                 `ev:(A)rfs_event`; `Y:A->bool`] P4_RETAINED_BASIC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                 `gX:real->A->real^3^3`; `ts:real`; `topY:A topology`;
                 `atlasY:((A->bool)#(A->real^3))->bool`; `gY:real->A->real^3^3`;
                 `ev:(A)rfs_event`; `Y:A->bool`] P4_RETAINED_CONNECTED) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (ev_neck ev i) (sphere(vec 0,&1)) SUBSET
    mfd_cut_spheres (ev_index ev) (ev_neck (ev:(A)rfs_event))`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_SPHERE_0; IN_MFD_CUT_SPHERES] THEN
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    MAP_EVERY EXISTS_TAC [`i:num`; `y:real^3`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `e = ev_neck (ev:(A)rfs_event) i` THEN
  ABBREV_TAC `pB = (e:real^3->A) (&4 / &3 % basis 1)` THEN
  ABBREV_TAC `pM = (e:real^3->A) (&3 / &4 % basis 1)` THEN
  ABBREV_TAC `S = IMAGE (e:real^3->A) (sphere(vec 0,&1))` THEN
  ABBREV_TAC `Y0 = Y INTER topspace (topX:A topology)` THEN
  SUBGOAL_THEN `IMAGE (e:real^3->A) (annulus (&1 / &2) (&2)) SUBSET topspace topX`
  ASSUME_TAC THENL
   [MATCH_MP_TAC OPEN_IN_SUBSET THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(pB:A) IN topspace topX DIFF S /\ (pM:A) IN topspace topX DIFF S`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY (fun t -> MP_TAC(ASSUME t))
     [`IMAGE (e:real^3->A) (annulus (&1 / &2) (&2)) SUBSET topspace topX`;
      `IMAGE (e:real^3->A) (annulus (&1 / &2) (&2)) =
       IMAGE e (annulus (&1 / &2) (&1)) UNION S UNION IMAGE e (annulus (&1) (&2))`;
      `DISJOINT (IMAGE (e:real^3->A) (annulus (&1 / &2) (&1))) S`;
      `DISJOINT (IMAGE (e:real^3->A) (annulus (&1) (&2))) S`;
      `(pM:A) IN IMAGE (e:real^3->A) (annulus (&1 / &2) (&1))`;
      `(pB:A) IN IMAGE (e:real^3->A) (annulus (&1) (&2))`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                 `e:real^3->A`; `pB:A`] P4_SIDE_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(LABEL_TAC "sB" o
    REWRITE_RULE[ASSUME `IMAGE (e:real^3->A) (sphere(vec 0,&1)) = S`])] THEN
  MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                 `e:real^3->A`; `pM:A`] P4_SIDE_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(LABEL_TAC "sM" o
    REWRITE_RULE[ASSUME `IMAGE (e:real^3->A) (sphere(vec 0,&1)) = S`])] THEN
  SUBGOAL_THEN `~((pB:A) IN p4_side topX (e:real^3->A) pM)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `e:real^3->A` o GEN_REWRITE_RULE I [apx_sphere_sep] o
      check (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) = "apx_sphere_sep"
                       with Failure _ -> false)) THEN
    ASM_REWRITE_TAC[apx_separates; p4_side] THEN REWRITE_TAC[IN] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(Y0:A->bool) SUBSET p4_side topX (e:real^3->A) pM` ASSUME_TAC THENL
   [USE_THEN "sM" (fun th -> MATCH_MP_TAC(el 4 (CONJUNCTS th))) THEN
    REPEAT CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC;
      MAP_EVERY (fun t -> MP_TAC(ASSUME t))
       [`Y0 SUBSET
         topspace topX DIFF mfd_cut_spheres (ev_index ev) (ev_neck (ev:(A)rfs_event))`;
        `S SUBSET mfd_cut_spheres (ev_index ev) (ev_neck (ev:(A)rfs_event))`] THEN
      SET_TAC[];
      MAP_EVERY (fun t -> MP_TAC(ASSUME t))
       [`IMAGE (e:real^3->A) (annulus (&1 / &2) (&1)) SUBSET Y0`;
        `(pM:A) IN IMAGE (e:real^3->A) (annulus (&1 / &2) (&1))`] THEN
      SET_TAC[]];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [USE_THEN "sB" (fun th -> ACCEPT_TAC(el 0 (CONJUNCTS th)));
    USE_THEN "sB" (fun th -> ACCEPT_TAC(el 1 (CONJUNCTS th)));
    USE_THEN "sB" (fun th -> MATCH_MP_TAC(el 4 (CONJUNCTS th))) THEN
    REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    USE_THEN "sB" (fun th -> MP_TAC(el 3 (CONJUNCTS th))) THEN SET_TAC[];
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
    X_GEN_TAC `z:A` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(z:A) IN p4_side topX (e:real^3->A) pM` ASSUME_TAC THENL
     [MP_TAC(ASSUME `(Y0:A->bool) SUBSET p4_side topX (e:real^3->A) pM`) THEN
      MP_TAC(ASSUME `(z:A) IN Y0`) THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `p4_side topX (e:real^3->A) pB = p4_side topX e pM` ASSUME_TAC THENL
     [MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `p4_side topX (e:real^3->A) z` THEN
      CONJ_TAC THENL
       [CONV_TAC SYM_CONV THEN
        USE_THEN "sB" (fun th -> MATCH_MP_TAC(el 5 (CONJUNCTS th))) THEN
        FIRST_ASSUM ACCEPT_TAC;
        USE_THEN "sM" (fun th -> MATCH_MP_TAC(el 5 (CONJUNCTS th))) THEN
        FIRST_ASSUM ACCEPT_TAC];
      ALL_TAC] THEN
    UNDISCH_TAC `~((pB:A) IN p4_side topX (e:real^3->A) pM)` THEN REWRITE_TAC[] THEN
    SUBST1_TAC(SYM(ASSUME `p4_side topX (e:real^3->A) pB = p4_side topX e pM`)) THEN
    USE_THEN "sB" (fun th -> ACCEPT_TAC(el 2 (CONJUNCTS th)));
    USE_THEN "sB" (fun th -> ACCEPT_TAC(el 5 (CONJUNCTS th)));
    X_GEN_TAC `C:A->bool` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(C:A->bool) SUBSET p4_side topX (e:real^3->A) pM` MP_TAC THENL
     [USE_THEN "sM" (fun th -> MATCH_MP_TAC(el 4 (CONJUNCTS th))) THEN
      REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      MP_TAC(ASSUME `~((pB:A) IN p4_side topX (e:real^3->A) pM)`) THEN SET_TAC[]];
    USE_THEN "sB" (fun th -> ACCEPT_TAC(el 6 (CONJUNCTS th)))]);;

(* Branches miss the cut spheres of the other necks of Y (those spheres lie *)
(* in the closure of Y0), and the branches of distinct necks are disjoint   *)
(* (otherwise Y0, a neck and a branch would join the two sides of a sphere). *)

let P4_BRANCH_SPHERE = prove
 (`!topX atlasX (gX:real->A->real^3^3) ts topY atlasY gY ev Y i j.
        rfs_event_ok (topX,atlasX) gX ts (topY,atlasY) gY ev /\
        hausdorff_space topX /\
        smooth_manifold_atlas topX (atlasX:((A->bool)#(A->real^3))->bool) /\
        apx_sphere_sep topX atlasX /\
        Y IN connected_components_of topY /\
        i IN ev_index ev /\ ev_capm ev i (vec 0) IN Y /\
        j IN ev_index ev /\ ev_capm ev j (vec 0) IN Y
        ==> DISJOINT (p4_side topX (ev_neck ev i) (ev_neck ev i (&4 / &3 % basis 1)))
                     (IMAGE (ev_neck ev j) (sphere(vec 0,&1)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                 `gX:real->A->real^3^3`; `ts:real`; `topY:A topology`;
                 `atlasY:((A->bool)#(A->real^3))->bool`; `gY:real->A->real^3^3`;
                 `ev:(A)rfs_event`; `Y:A->bool`; `i:num`] P4_BRANCH_BASIC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                 `gX:real->A->real^3^3`; `ts:real`; `topY:A topology`;
                 `atlasY:((A->bool)#(A->real^3))->bool`; `gY:real->A->real^3^3`;
                 `ev:(A)rfs_event`; `Y:A->bool`] P4_RETAINED_CLOSURE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `j:num` o CONJUNCT2) THEN
  ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; DISCH_TAC] THEN
  MP_TAC(ISPECL [`topX:A topology`;
                 `p4_side topX (ev_neck ev i) (ev_neck (ev:(A)rfs_event) i (&4 / &3 % basis 1))`;
                 `Y INTER topspace (topX:A topology)`] OPEN_IN_INTER_CLOSURE_OF_EQ_EMPTY) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  MP_TAC(ASSUME
   `DISJOINT (p4_side topX (ev_neck ev i) (ev_neck (ev:(A)rfs_event) i (&4 / &3 % basis 1)))
             (Y INTER topspace (topX:A topology))`) THEN
  MP_TAC(ASSUME
   `IMAGE (ev_neck ev j) (sphere(vec 0,&1)) SUBSET
    topX closure_of (Y INTER topspace (topX:A topology))`) THEN
  REWRITE_TAC[DISJOINT] THEN SET_TAC[]);;


let P4_BRANCH_DISJOINT = prove
 (`!topX atlasX (gX:real->A->real^3^3) ts topY atlasY gY ev Y i j.
        rfs_event_ok (topX,atlasX) gX ts (topY,atlasY) gY ev /\
        hausdorff_space topX /\
        smooth_manifold_atlas topX (atlasX:((A->bool)#(A->real^3))->bool) /\
        apx_sphere_sep topX atlasX /\
        Y IN connected_components_of topY /\
        i IN ev_index ev /\ ev_capm ev i (vec 0) IN Y /\
        j IN ev_index ev /\ ev_capm ev j (vec 0) IN Y /\ ~(i = j)
        ==> DISJOINT (p4_side topX (ev_neck ev i) (ev_neck ev i (&4 / &3 % basis 1)))
                     (p4_side topX (ev_neck ev j) (ev_neck ev j (&4 / &3 % basis 1)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                 `gX:real->A->real^3^3`; `ts:real`; `topY:A topology`;
                 `atlasY:((A->bool)#(A->real^3))->bool`; `gY:real->A->real^3^3`;
                 `ev:(A)rfs_event`; `Y:A->bool`; `i:num`] P4_BRANCH_BASIC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(LABEL_TAC "bi")] THEN
  MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                 `gX:real->A->real^3^3`; `ts:real`; `topY:A topology`;
                 `atlasY:((A->bool)#(A->real^3))->bool`; `gY:real->A->real^3^3`;
                 `ev:(A)rfs_event`; `Y:A->bool`; `j:num`] P4_BRANCH_BASIC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(LABEL_TAC "bj")] THEN
  MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                 `gX:real->A->real^3^3`; `ts:real`; `topY:A topology`;
                 `atlasY:((A->bool)#(A->real^3))->bool`; `gY:real->A->real^3^3`;
                 `ev:(A)rfs_event`; `Y:A->bool`; `j:num`; `i:num`] P4_BRANCH_SPHERE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                 `gX:real->A->real^3^3`; `ts:real`; `topY:A topology`;
                 `atlasY:((A->bool)#(A->real^3))->bool`; `gY:real->A->real^3^3`;
                 `ev:(A)rfs_event`; `i:num`] P4_EVENT_CAPS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> ASSUME_TAC(CONJUNCT1 th) THEN
    LABEL_TAC "ni" (MATCH_MP P4_NECK_PIECES (CONJUNCT1 th))) THEN
  MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                 `gX:real->A->real^3^3`; `ts:real`; `topY:A topology`;
                 `atlasY:((A->bool)#(A->real^3))->bool`; `gY:real->A->real^3^3`;
                 `ev:(A)rfs_event`; `j:num`] P4_EVENT_CAPS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> ASSUME_TAC(CONJUNCT1 th) THEN
    LABEL_TAC "nj" (MATCH_MP P4_NECK_PIECES (CONJUNCT1 th))) THEN
  MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                 `gX:real->A->real^3^3`; `ts:real`; `topY:A topology`;
                 `atlasY:((A->bool)#(A->real^3))->bool`; `gY:real->A->real^3^3`;
                 `ev:(A)rfs_event`; `Y:A->bool`; `j:num`] P4_CAP_IN_COMPONENT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; DISCH_THEN(ASSUME_TAC o CONJUNCT2)] THEN
  MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                 `gX:real->A->real^3^3`; `ts:real`; `topY:A topology`;
                 `atlasY:((A->bool)#(A->real^3))->bool`; `gY:real->A->real^3^3`;
                 `ev:(A)rfs_event`; `Y:A->bool`; `i:num`] P4_CAP_IN_COMPONENT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; DISCH_THEN(ASSUME_TAC o CONJUNCT2)] THEN
  MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                 `gX:real->A->real^3^3`; `ts:real`; `topY:A topology`;
                 `atlasY:((A->bool)#(A->real^3))->bool`; `gY:real->A->real^3^3`;
                 `ev:(A)rfs_event`; `Y:A->bool`] P4_RETAINED_BASIC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                 `gX:real->A->real^3^3`; `ts:real`; `topY:A topology`;
                 `atlasY:((A->bool)#(A->real^3))->bool`; `gY:real->A->real^3^3`;
                 `ev:(A)rfs_event`; `Y:A->bool`] P4_RETAINED_CONNECTED) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN
   `DISJOINT (IMAGE (ev_neck ev j) (annulus (&1 / &2) (&2)))
             (IMAGE (ev_neck (ev:(A)rfs_event) i) (sphere(vec 0,&1)))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                   `gX:real->A->real^3^3`; `ts:real`; `topY:A topology`;
                   `atlasY:((A->bool)#(A->real^3))->bool`; `gY:real->A->real^3^3`;
                   `ev:(A)rfs_event`] P4_EVENT_FACTS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o
      CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
    REWRITE_TAC[mfd_cut_cap] THEN
    DISCH_THEN(MP_TAC o SPECL [`j:num`; `i:num`] o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `sphere(vec 0:real^3,&1) SUBSET annulus (&1 / &2) (&2)` MP_TAC THENL
     [REWRITE_TAC[SUBSET; IN_SPHERE_0; annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[DISJOINT] THEN SET_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `Bi = p4_side topX (ev_neck ev i) (ev_neck (ev:(A)rfs_event) i (&4 / &3 % basis 1))` THEN
  ABBREV_TAC `Bj = p4_side topX (ev_neck ev j) (ev_neck (ev:(A)rfs_event) j (&4 / &3 % basis 1))` THEN
  ABBREV_TAC `Y0 = Y INTER topspace (topX:A topology)` THEN
  REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
  X_GEN_TAC `z:A` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(Bj:A->bool) SUBSET Bi` ASSUME_TAC THENL
   [SUBGOAL_THEN `(z:A) IN topspace topX DIFF IMAGE (ev_neck ev i) (sphere(vec 0,&1))`
    ASSUME_TAC THENL
     [USE_THEN "bi" (fun th -> MP_TAC(el 0 (CONJUNCTS th))) THEN
      DISCH_THEN(MP_TAC o MATCH_MP OPEN_IN_SUBSET) THEN
      USE_THEN "bi" (fun th -> MP_TAC(el 3 (CONJUNCTS th))) THEN
      MP_TAC(ASSUME `(z:A) IN Bi`) THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `p4_side topX (ev_neck ev i) (z:A) = Bi` ASSUME_TAC THENL
     [USE_THEN "bi" (fun th -> MATCH_MP_TAC(el 5 (CONJUNCTS th))) THEN
      FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                   `ev_neck (ev:(A)rfs_event) i`; `z:A`] P4_SIDE_FACTS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `Bj:A->bool` o el 4 o CONJUNCTS) THEN
    REWRITE_TAC[ASSUME `p4_side topX (ev_neck ev i) (z:A) = Bi`] THEN
    DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
     [USE_THEN "bj" (fun th -> ACCEPT_TAC(el 1 (CONJUNCTS th)));
      FIRST_ASSUM ACCEPT_TAC;
      FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  USE_THEN "bi" (fun th -> MP_TAC(SPEC
    `Y0 UNION IMAGE (ev_neck ev j) (annulus (&1 / &2) (&2)) UNION (Bi:A->bool)`
    (el 6 (CONJUNCTS th)))) THEN
  REWRITE_TAC[NOT_IMP] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONNECTED_IN_UNION THEN REPEAT CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC;
      MATCH_MP_TAC CONNECTED_IN_UNION THEN REPEAT CONJ_TAC THENL
       [USE_THEN "nj" (fun th -> ACCEPT_TAC(el 2 (CONJUNCTS th)));
        USE_THEN "bi" (fun th -> ACCEPT_TAC(el 1 (CONJUNCTS th)));
        REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
        EXISTS_TAC `ev_neck (ev:(A)rfs_event) j (&4 / &3 % basis 1)` THEN
        USE_THEN "nj" (fun th -> MP_TAC(el 5 (CONJUNCTS th))) THEN
        USE_THEN "nj" (fun th -> MP_TAC(el 10 (CONJUNCTS th))) THEN
        USE_THEN "bj" (fun th -> MP_TAC(el 2 (CONJUNCTS th))) THEN
        MP_TAC(ASSUME `(Bj:A->bool) SUBSET Bi`) THEN SET_TAC[]];
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_UNION] THEN
      EXISTS_TAC `ev_neck (ev:(A)rfs_event) j (&3 / &4 % basis 1)` THEN
      USE_THEN "nj" (fun th -> MP_TAC(el 9 (CONJUNCTS th))) THEN
      USE_THEN "nj" (fun th -> MP_TAC(el 5 (CONJUNCTS th))) THEN
      MP_TAC(ASSUME `IMAGE (ev_neck ev j) (annulus (&1 / &2) (&1)) SUBSET (Y0:A->bool)`) THEN
      SET_TAC[]];
    MAP_EVERY (fun t -> MP_TAC(ASSUME t))
     [`Y0 SUBSET
       topspace topX DIFF mfd_cut_spheres (ev_index ev) (ev_neck (ev:(A)rfs_event))`;
      `DISJOINT (IMAGE (ev_neck ev j) (annulus (&1 / &2) (&2)))
                (IMAGE (ev_neck (ev:(A)rfs_event) i) (sphere(vec 0,&1)))`] THEN
    USE_THEN "bi" (fun th -> MP_TAC(el 3 (CONJUNCTS th))) THEN
    SUBGOAL_THEN
     `IMAGE (ev_neck ev i) (sphere(vec 0,&1)) SUBSET
      mfd_cut_spheres (ev_index ev) (ev_neck (ev:(A)rfs_event))`
    MP_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_SPHERE_0; IN_MFD_CUT_SPHERES] THEN
      X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
      MAP_EVERY EXISTS_TAC [`i:num`; `y:real^3`] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SET_TAC[];
    USE_THEN "ni" (fun th -> MP_TAC(el 9 (CONJUNCTS th))) THEN
    MP_TAC(ASSUME `IMAGE (ev_neck ev i) (annulus (&1 / &2) (&1)) SUBSET (Y0:A->bool)`) THEN
    SET_TAC[];
    USE_THEN "ni" (fun th -> MP_TAC(el 10 (CONJUNCTS th))) THEN
    USE_THEN "bi" (fun th -> MP_TAC(el 2 (CONJUNCTS th))) THEN
    SET_TAC[]]);;

(* The decomposition: the component X of the old stage through a retained   *)
(* point of Y is Y0, the cut spheres of the necks with minus cap in Y and   *)
(* their branches (clopen, hence all of X).                                 *)

let P4_DECOMPOSITION = prove
 (`!topX atlasX (gX:real->A->real^3^3) ts topY atlasY gY ev Y x0.
        rfs_event_ok (topX,atlasX) gX ts (topY,atlasY) gY ev /\
        hausdorff_space topX /\
        smooth_manifold_atlas topX (atlasX:((A->bool)#(A->real^3))->bool) /\
        apx_sphere_sep topX atlasX /\
        Y IN connected_components_of topY /\ x0 IN Y INTER topspace topX
        ==> connected_component_of topX x0 IN connected_components_of topX /\
            Y INTER topspace topX SUBSET connected_component_of topX x0 /\
            (!i. i IN ev_index ev /\ ev_capm ev i (vec 0) IN Y
                 ==> IMAGE (ev_neck ev i) (annulus (&1 / &2) (&2)) SUBSET
                     connected_component_of topX x0 /\
                     p4_side topX (ev_neck ev i) (ev_neck ev i (&4 / &3 % basis 1)) SUBSET
                     connected_component_of topX x0) /\
            connected_component_of topX x0 =
            (Y INTER topspace topX) UNION
            UNIONS {IMAGE (ev_neck ev i) (sphere(vec 0,&1)) UNION
                    p4_side topX (ev_neck ev i) (ev_neck ev i (&4 / &3 % basis 1)) | i |
                    i IN ev_index ev /\ ev_capm ev i (vec 0) IN Y}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                 `gX:real->A->real^3^3`; `ts:real`; `topY:A topology`;
                 `atlasY:((A->bool)#(A->real^3))->bool`; `gY:real->A->real^3^3`;
                 `ev:(A)rfs_event`; `Y:A->bool`] P4_RETAINED_BASIC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                 `gX:real->A->real^3^3`; `ts:real`; `topY:A topology`;
                 `atlasY:((A->bool)#(A->real^3))->bool`; `gY:real->A->real^3^3`;
                 `ev:(A)rfs_event`; `Y:A->bool`] P4_RETAINED_CONNECTED) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                 `gX:real->A->real^3^3`; `ts:real`; `topY:A topology`;
                 `atlasY:((A->bool)#(A->real^3))->bool`; `gY:real->A->real^3^3`;
                 `ev:(A)rfs_event`; `Y:A->bool`] P4_RETAINED_CLOSURE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(ASSUME_TAC o CONJUNCT1)] THEN
  SUBGOAL_THEN
   `FINITE {i | i IN ev_index ev /\ ev_capm (ev:(A)rfs_event) i (vec 0) IN Y}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_RESTRICT THEN
    MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                   `gX:real->A->real^3^3`; `ts:real`; `topY:A topology`;
                   `atlasY:((A->bool)#(A->real^3))->bool`; `gY:real->A->real^3^3`;
                   `ev:(A)rfs_event`] P4_EVENT_FACTS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o
      CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
    SIMP_TAC[mfd_cut_cap];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. i IN ev_index ev /\ ev_capm ev i (vec 0) IN Y
        ==> mfd_neck_chart topX atlasX (ev_neck ev i) /\
            IMAGE (ev_neck ev i) (annulus (&1 / &2) (&1)) SUBSET Y INTER topspace topX /\
            open_in topX (p4_side topX (ev_neck ev i) (ev_neck ev i (&4 / &3 % basis 1))) /\
            connected_in topX
              (p4_side topX (ev_neck ev i) (ev_neck ev i (&4 / &3 % basis 1))) /\
            IMAGE (ev_neck ev i) (annulus (&1) (&2)) SUBSET
            p4_side topX (ev_neck ev i) (ev_neck (ev:(A)rfs_event) i (&4 / &3 % basis 1)) /\
            topX closure_of
              (p4_side topX (ev_neck ev i) (ev_neck ev i (&4 / &3 % basis 1)))
            SUBSET p4_side topX (ev_neck ev i) (ev_neck ev i (&4 / &3 % basis 1)) UNION
                   IMAGE (ev_neck ev i) (sphere(vec 0,&1))`
  (LABEL_TAC "br") THENL
   [X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                   `gX:real->A->real^3^3`; `ts:real`; `topY:A topology`;
                   `atlasY:((A->bool)#(A->real^3))->bool`; `gY:real->A->real^3^3`;
                   `ev:(A)rfs_event`; `Y:A->bool`; `i:num`] P4_BRANCH_BASIC) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                   `gX:real->A->real^3^3`; `ts:real`; `topY:A topology`;
                   `atlasY:((A->bool)#(A->real^3))->bool`; `gY:real->A->real^3^3`;
                   `ev:(A)rfs_event`; `Y:A->bool`; `i:num`] P4_CAP_IN_COMPONENT) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
    MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                   `gX:real->A->real^3^3`; `ts:real`; `topY:A topology`;
                   `atlasY:((A->bool)#(A->real^3))->bool`; `gY:real->A->real^3^3`;
                   `ev:(A)rfs_event`; `i:num`] P4_EVENT_CAPS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(ASSUME_TAC o CONJUNCT1)] THEN
    REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `X = connected_component_of topX (x0:A)` THEN
  ABBREV_TAC `Y0 = Y INTER topspace (topX:A topology)` THEN
  SUBGOAL_THEN `(x0:A) IN topspace topX` ASSUME_TAC THENL
   [MP_TAC(ASSUME `(x0:A) IN Y0`) THEN EXPAND_TAC "Y0" THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(Y0:A->bool) SUBSET topspace topX` ASSUME_TAC THENL
   [EXPAND_TAC "Y0" THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `connected_in topX (X:A->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "X" THEN REWRITE_TAC[CONNECTED_IN_CONNECTED_COMPONENT_OF]; ALL_TAC] THEN
  SUBGOAL_THEN `(Y0:A->bool) SUBSET X` ASSUME_TAC THENL
   [EXPAND_TAC "X" THEN MATCH_MP_TAC CONNECTED_COMPONENT_OF_MAXIMAL THEN
    CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. i IN ev_index ev /\ ev_capm ev i (vec 0) IN Y
        ==> IMAGE (ev_neck ev i) (annulus (&1 / &2) (&2)) =
            IMAGE (ev_neck ev i) (annulus (&1 / &2) (&1)) UNION
            IMAGE (ev_neck ev i) (sphere(vec 0,&1)) UNION
            IMAGE (ev_neck ev i) (annulus (&1) (&2)) /\
            open_in topX (IMAGE (ev_neck ev i) (annulus (&1 / &2) (&2))) /\
            connected_in topX (IMAGE (ev_neck ev i) (annulus (&1 / &2) (&2))) /\
            closed_in topX (IMAGE (ev_neck ev i) (sphere(vec 0,&1))) /\
            ev_neck ev i (&3 / &4 % basis 1) IN IMAGE (ev_neck ev i) (annulus (&1 / &2) (&1)) /\
            ev_neck ev i (&4 / &3 % basis 1) IN
            IMAGE (ev_neck (ev:(A)rfs_event) i) (annulus (&1) (&2))`
  (LABEL_TAC "nk") THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    USE_THEN "br" (fun th -> MP_TAC(MP (SPEC `i:num` th) (ASSUME
      `i IN ev_index ev /\ ev_capm (ev:(A)rfs_event) i (vec 0) IN Y`))) THEN
    DISCH_THEN(MP_TAC o MATCH_MP P4_NECK_PIECES o CONJUNCT1) THEN STRIP_TAC THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    MATCH_MP_TAC COMPACT_IN_IMP_CLOSED_IN THEN
    CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. i IN ev_index ev /\ ev_capm ev i (vec 0) IN Y
        ==> IMAGE (ev_neck ev i) (annulus (&1 / &2) (&2)) SUBSET X /\
            p4_side topX (ev_neck ev i) (ev_neck (ev:(A)rfs_event) i (&4 / &3 % basis 1))
            SUBSET (X:A->bool)`
  (LABEL_TAC "inX") THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    USE_THEN "br" (fun th -> MP_TAC(MP (SPEC `i:num` th) (ASSUME
      `i IN ev_index ev /\ ev_capm (ev:(A)rfs_event) i (vec 0) IN Y`))) THEN
    USE_THEN "nk" (fun th -> MP_TAC(MP (SPEC `i:num` th) (ASSUME
      `i IN ev_index ev /\ ev_capm (ev:(A)rfs_event) i (vec 0) IN Y`))) THEN
    REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
    ABBREV_TAC `N = IMAGE (ev_neck (ev:(A)rfs_event) i) (annulus (&1 / &2) (&2))` THEN
    ABBREV_TAC `B = p4_side topX (ev_neck ev i) (ev_neck (ev:(A)rfs_event) i (&4 / &3 % basis 1))` THEN
    SUBGOAL_THEN `connected_in topX ((Y0:A->bool) UNION N)` ASSUME_TAC THENL
     [MATCH_MP_TAC CONNECTED_IN_UNION THEN REPEAT CONJ_TAC THEN
      TRY(FIRST_ASSUM ACCEPT_TAC) THEN
      MAP_EVERY (fun t -> MP_TAC(ASSUME t))
       [`IMAGE (ev_neck ev i) (annulus (&1 / &2) (&1)) SUBSET (Y0:A->bool)`;
        `ev_neck ev i (&3 / &4 % basis 1) IN
         IMAGE (ev_neck (ev:(A)rfs_event) i) (annulus (&1 / &2) (&1))`;
        `(N:A->bool) =
         IMAGE (ev_neck ev i) (annulus (&1 / &2) (&1)) UNION
         IMAGE (ev_neck ev i) (sphere (vec 0,&1)) UNION
         IMAGE (ev_neck (ev:(A)rfs_event) i) (annulus (&1) (&2))`] THEN
      SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `connected_in topX (((Y0:A->bool) UNION N) UNION B)` ASSUME_TAC THENL
     [MATCH_MP_TAC CONNECTED_IN_UNION THEN REPEAT CONJ_TAC THEN
      TRY(FIRST_ASSUM ACCEPT_TAC) THEN
      MAP_EVERY (fun t -> MP_TAC(ASSUME t))
       [`IMAGE (ev_neck ev i) (annulus (&1) (&2)) SUBSET (B:A->bool)`;
        `ev_neck ev i (&4 / &3 % basis 1) IN
         IMAGE (ev_neck (ev:(A)rfs_event) i) (annulus (&1) (&2))`;
        `(N:A->bool) =
         IMAGE (ev_neck ev i) (annulus (&1 / &2) (&1)) UNION
         IMAGE (ev_neck ev i) (sphere (vec 0,&1)) UNION
         IMAGE (ev_neck (ev:(A)rfs_event) i) (annulus (&1) (&2))`] THEN
      SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `((Y0:A->bool) UNION N) UNION B SUBSET X` MP_TAC THENL
     [EXPAND_TAC "X" THEN MATCH_MP_TAC CONNECTED_COMPONENT_OF_MAXIMAL THEN
      CONJ_TAC THENL
       [FIRST_ASSUM ACCEPT_TAC;
        MP_TAC(ASSUME `(x0:A) IN Y0`) THEN SET_TAC[]];
      SET_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC
   `W = (Y0:A->bool) UNION
        UNIONS {IMAGE (ev_neck ev i) (sphere(vec 0,&1)) UNION
                p4_side topX (ev_neck ev i) (ev_neck ev i (&4 / &3 % basis 1)) | i |
                i IN ev_index ev /\ ev_capm (ev:(A)rfs_event) i (vec 0) IN Y}` THEN
  SUBGOAL_THEN `(W:A->bool) SUBSET X` ASSUME_TAC THENL
   [EXPAND_TAC "W" THEN REWRITE_TAC[UNION_SUBSET; UNIONS_SUBSET; FORALL_IN_GSPEC] THEN
    CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    USE_THEN "inX" (fun th -> MP_TAC(MP (SPEC `i:num` th) (ASSUME
          `i IN ev_index ev /\ ev_capm (ev:(A)rfs_event) i (vec 0) IN Y`))) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
    REWRITE_TAC[UNION_SUBSET] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `IMAGE (ev_neck (ev:(A)rfs_event) i) (annulus (&1 / &2) (&2))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC IMAGE_SUBSET THEN
        REWRITE_TAC[SUBSET; IN_SPHERE_0; annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC;
        FIRST_ASSUM ACCEPT_TAC];
      FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i y. i IN ev_index ev /\ ev_capm (ev:(A)rfs_event) i (vec 0) IN Y /\
          y IN IMAGE (ev_neck (ev:(A)rfs_event) i) (sphere(vec 0,&1)) UNION p4_side topX (ev_neck ev i) (ev_neck (ev:(A)rfs_event) i (&4 / &3 % basis 1))
          ==> (y:A) IN W`
  (LABEL_TAC "inW") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN EXPAND_TAC "W" THEN
    REWRITE_TAC[IN_UNION; IN_UNIONS; IN_ELIM_THM] THEN DISJ2_TAC THEN
    EXISTS_TAC `IMAGE (ev_neck (ev:(A)rfs_event) i) (sphere(vec 0,&1)) UNION p4_side topX (ev_neck ev i) (ev_neck (ev:(A)rfs_event) i (&4 / &3 % basis 1))` THEN
    CONJ_TAC THENL [EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[]; FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(Y0:A->bool) SUBSET W` ASSUME_TAC THENL
   [EXPAND_TAC "W" THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. i IN ev_index ev /\ ev_capm (ev:(A)rfs_event) i (vec 0) IN Y
        ==> IMAGE (ev_neck (ev:(A)rfs_event) i) (annulus (&1 / &2) (&2)) SUBSET (W:A->bool) /\ p4_side topX (ev_neck ev i) (ev_neck (ev:(A)rfs_event) i (&4 / &3 % basis 1)) SUBSET W /\ IMAGE (ev_neck (ev:(A)rfs_event) i) (sphere(vec 0,&1)) SUBSET W`
  (LABEL_TAC "subW") THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    USE_THEN "nk" (fun th -> MP_TAC(MP (SPEC `i:num` th) (ASSUME
          `i IN ev_index ev /\ ev_capm (ev:(A)rfs_event) i (vec 0) IN Y`))) THEN USE_THEN "br" (fun th -> MP_TAC(MP (SPEC `i:num` th) (ASSUME
          `i IN ev_index ev /\ ev_capm (ev:(A)rfs_event) i (vec 0) IN Y`))) THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
    REPEAT CONJ_TAC THEN REWRITE_TAC[SUBSET] THEN X_GEN_TAC `y:A` THEN DISCH_TAC THENL
     [SUBGOAL_THEN `(y:A) IN IMAGE (ev_neck (ev:(A)rfs_event) i) (annulus (&1 / &2) (&1)) \/ y IN IMAGE (ev_neck (ev:(A)rfs_event) i) (sphere(vec 0,&1)) \/ y IN IMAGE (ev_neck (ev:(A)rfs_event) i) (annulus (&1) (&2))` STRIP_ASSUME_TAC THENL
       [MP_TAC(ASSUME `IMAGE (ev_neck (ev:(A)rfs_event) i) (annulus (&1 / &2) (&2)) = IMAGE (ev_neck (ev:(A)rfs_event) i) (annulus (&1 / &2) (&1)) UNION IMAGE (ev_neck (ev:(A)rfs_event) i) (sphere(vec 0,&1)) UNION IMAGE (ev_neck (ev:(A)rfs_event) i) (annulus (&1) (&2))`) THEN
        MP_TAC(ASSUME `(y:A) IN IMAGE (ev_neck (ev:(A)rfs_event) i) (annulus (&1 / &2) (&2))`) THEN SET_TAC[];
        MP_TAC(ASSUME `IMAGE (ev_neck (ev:(A)rfs_event) i) (annulus (&1 / &2) (&1)) SUBSET (Y0:A->bool)`) THEN
        MP_TAC(ASSUME `(Y0:A->bool) SUBSET W`) THEN
        MP_TAC(ASSUME `(y:A) IN IMAGE (ev_neck (ev:(A)rfs_event) i) (annulus (&1 / &2) (&1))`) THEN SET_TAC[];
        USE_THEN "inW" MATCH_MP_TAC THEN EXISTS_TAC `i:num` THEN
        ASM_REWRITE_TAC[IN_UNION];
        USE_THEN "inW" MATCH_MP_TAC THEN EXISTS_TAC `i:num` THEN
        ASM_REWRITE_TAC[IN_UNION] THEN DISJ2_TAC THEN
        MP_TAC(ASSUME `IMAGE (ev_neck (ev:(A)rfs_event) i) (annulus (&1) (&2)) SUBSET p4_side topX (ev_neck ev i) (ev_neck (ev:(A)rfs_event) i (&4 / &3 % basis 1))`) THEN MP_TAC(ASSUME `(y:A) IN IMAGE (ev_neck (ev:(A)rfs_event) i) (annulus (&1) (&2))`) THEN
        SET_TAC[]];
      USE_THEN "inW" MATCH_MP_TAC THEN EXISTS_TAC `i:num` THEN
      ASM_REWRITE_TAC[IN_UNION];
      USE_THEN "inW" MATCH_MP_TAC THEN EXISTS_TAC `i:num` THEN
      ASM_REWRITE_TAC[IN_UNION]];
    ALL_TAC] THEN
  SUBGOAL_THEN `open_in topX (W:A->bool)` ASSUME_TAC THENL
   [GEN_REWRITE_TAC I [OPEN_IN_SUBOPEN] THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `(x:A) IN Y0 \/
      ?i. (i IN ev_index ev /\ ev_capm (ev:(A)rfs_event) i (vec 0) IN Y) /\
          (x IN IMAGE (ev_neck (ev:(A)rfs_event) i) (sphere(vec 0,&1)) \/ x IN p4_side topX (ev_neck ev i) (ev_neck (ev:(A)rfs_event) i (&4 / &3 % basis 1)))`
    STRIP_ASSUME_TAC THENL
     [MP_TAC(ASSUME `(x:A) IN W`) THEN EXPAND_TAC "W" THEN
      REWRITE_TAC[IN_UNION; IN_UNIONS; IN_ELIM_THM] THEN MESON_TAC[IN_UNION];
      EXISTS_TAC `Y0:A->bool` THEN REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      EXISTS_TAC `IMAGE (ev_neck (ev:(A)rfs_event) i) (annulus (&1 / &2) (&2))` THEN
      USE_THEN "nk" (fun th -> MP_TAC(MP (SPEC `i:num` th) (ASSUME
          `i IN ev_index ev /\ ev_capm (ev:(A)rfs_event) i (vec 0) IN Y`))) THEN USE_THEN "subW" (fun th -> MP_TAC(MP (SPEC `i:num` th) (ASSUME
          `i IN ev_index ev /\ ev_capm (ev:(A)rfs_event) i (vec 0) IN Y`))) THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
      REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
      MP_TAC(ASSUME `IMAGE (ev_neck (ev:(A)rfs_event) i) (annulus (&1 / &2) (&2)) = IMAGE (ev_neck (ev:(A)rfs_event) i) (annulus (&1 / &2) (&1)) UNION IMAGE (ev_neck (ev:(A)rfs_event) i) (sphere(vec 0,&1)) UNION IMAGE (ev_neck (ev:(A)rfs_event) i) (annulus (&1) (&2))`) THEN
      MP_TAC(ASSUME `(x:A) IN IMAGE (ev_neck (ev:(A)rfs_event) i) (sphere(vec 0,&1))`) THEN SET_TAC[];
      EXISTS_TAC `p4_side topX (ev_neck ev i) (ev_neck (ev:(A)rfs_event) i (&4 / &3 % basis 1))` THEN
      USE_THEN "br" (fun th -> MP_TAC(MP (SPEC `i:num` th) (ASSUME
          `i IN ev_index ev /\ ev_capm (ev:(A)rfs_event) i (vec 0) IN Y`))) THEN USE_THEN "subW" (fun th -> MP_TAC(MP (SPEC `i:num` th) (ASSUME
          `i IN ev_index ev /\ ev_capm (ev:(A)rfs_event) i (vec 0) IN Y`))) THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
      REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `closed_in topX (W:A->bool)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM CLOSURE_OF_SUBSET_EQ] THEN CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_IN_SUBSET THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [SYM(ASSUME `(Y0:A->bool) UNION UNIONS {IMAGE (ev_neck ev i) (sphere(vec 0,&1)) UNION p4_side topX (ev_neck ev i) (ev_neck ev i (&4 / &3 % basis 1)) | i | i IN ev_index ev /\ ev_capm (ev:(A)rfs_event) i (vec 0) IN Y} = W`)] THEN
    REWRITE_TAC[CLOSURE_OF_UNION; UNION_SUBSET] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `(Y0:A->bool) UNION UNIONS {IMAGE (ev_neck ev i) (sphere(vec 0,&1)) | i | i IN ev_index ev /\ ev_capm (ev:(A)rfs_event) i (vec 0) IN Y}` THEN
      CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      REWRITE_TAC[UNION_SUBSET; UNIONS_SUBSET; FORALL_IN_GSPEC] THEN
      CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      USE_THEN "subW" (fun th -> MP_TAC(MP (SPEC `i:num` th) (ASSUME `i IN ev_index ev /\ ev_capm (ev:(A)rfs_event) i (vec 0) IN Y`))) THEN
      SIMP_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`topX:A topology`; `{IMAGE (ev_neck ev i) (sphere(vec 0,&1)) UNION p4_side topX (ev_neck ev i) (ev_neck ev i (&4 / &3 % basis 1)) | i | i IN ev_index ev /\ ev_capm (ev:(A)rfs_event) i (vec 0) IN Y}`] CLOSURE_OF_UNIONS) THEN
    ANTS_TAC THENL
     [GEN_REWRITE_TAC ONCE_DEPTH_CONV [SIMPLE_IMAGE_GEN] THEN MATCH_MP_TAC FINITE_IMAGE THEN
      FIRST_ASSUM ACCEPT_TAC;
      DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    USE_THEN "subW" (fun th -> MP_TAC(MP (SPEC `i:num` th) (ASSUME `i IN ev_index ev /\ ev_capm (ev:(A)rfs_event) i (vec 0) IN Y`))) THEN
    USE_THEN "nk" (fun th -> MP_TAC(MP (SPEC `i:num` th) (ASSUME `i IN ev_index ev /\ ev_capm (ev:(A)rfs_event) i (vec 0) IN Y`))) THEN
    USE_THEN "br" (fun th -> MP_TAC(MP (SPEC `i:num` th) (ASSUME `i IN ev_index ev /\ ev_capm (ev:(A)rfs_event) i (vec 0) IN Y`))) THEN
    REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
    REWRITE_TAC[CLOSURE_OF_UNION; UNION_SUBSET] THEN CONJ_TAC THENL
     [SUBGOAL_THEN `topX closure_of IMAGE (ev_neck (ev:(A)rfs_event) i) (sphere(vec 0,&1)) = IMAGE (ev_neck (ev:(A)rfs_event) i) (sphere(vec 0,&1))` SUBST1_TAC THENL
       [REWRITE_TAC[CLOSURE_OF_EQ] THEN FIRST_ASSUM ACCEPT_TAC; FIRST_ASSUM ACCEPT_TAC];
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `p4_side topX (ev_neck ev i) (ev_neck (ev:(A)rfs_event) i (&4 / &3 % basis 1)) UNION IMAGE (ev_neck (ev:(A)rfs_event) i) (sphere(vec 0,&1))` THEN
      CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ASM_REWRITE_TAC[UNION_SUBSET]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x0:A) IN X` ASSUME_TAC THENL
   [EXPAND_TAC "X" THEN REWRITE_TAC[IN] THEN REWRITE_TAC[CONNECTED_COMPONENT_OF_REFL] THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(X:A->bool) SUBSET W` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`topX:A topology`; `X:A->bool`; `W:A->bool`] CONNECTED_IN_CLOPEN_CASES) THEN
    ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    MP_TAC(ASSUME `(x0:A) IN X`) THEN MP_TAC(ASSUME `(x0:A) IN Y0`) THEN
    MP_TAC(ASSUME `(Y0:A->bool) SUBSET W`) THEN SET_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [EXPAND_TAC "X" THEN REWRITE_TAC[CONNECTED_COMPONENT_IN_CONNECTED_COMPONENTS_OF] THEN
    FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    USE_THEN "inX" ACCEPT_TAC;
    MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The cap data (p3_cap_param) and the neck parametrizations of the surgery  *)
(* necks (rfs_surgery_ok).                                                   *)
(* ------------------------------------------------------------------------- *)

(* With (A0 + 4) dl < 1 the neck domain contains the cut annulus 1/2 < |y| < 2 *)
(* and the collapse region 1 <= |y| <= exp((A0 + 4) / sqrt 2).                 *)

let P4_NECK_DOM_FACTS = prove
 (`!dl A0. &0 < dl /\ &0 < A0 /\ (A0 + &4) * dl < &1
           ==> open (rfs_neck_dom dl) /\
               (!y:real^3. y IN rfs_neck_dom dl ==> ~(y = vec 0)) /\
               annulus (&1 / &2) (&2) SUBSET rfs_neck_dom dl /\
               {y:real^3 | &1 <= norm y /\ norm y <= exp((A0 + &4) / sqrt(&2))}
               SUBSET rfs_neck_dom dl /\
               &2 <= exp((A0 + &4) / sqrt(&2))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[rfs_neck_dom; OPEN_ANNULUS] THEN
  SUBGOAL_THEN `&0 < sqrt(&2) /\ sqrt(&2) < &2` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LT THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_LSQRT THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `c = inv(sqrt(&2) * dl)` THEN
  SUBGOAL_THEN `A0 + &4 < inv dl` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[REAL_ARITH `inv dl = &1 * inv dl`] THEN
    REWRITE_TAC[GSYM real_div] THEN ASM_SIMP_TAC[REAL_LT_RDIV_EQ];
    ALL_TAC] THEN
  SUBGOAL_THEN `(A0 + &4) / sqrt(&2) < c` ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN REWRITE_TAC[REAL_INV_MUL; real_div] THEN
    GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
    MATCH_MP_TAC REAL_LT_RMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LT_INV THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= (A0 + &4) / sqrt(&2)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&2 <= exp((A0 + &4) / sqrt(&2))` ASSUME_TAC THENL
   [MP_TAC(SPEC `(A0 + &4) / sqrt(&2)` REAL_EXP_LE_X) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `exp((A0 + &4) / sqrt(&2)) < exp c` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_EXP_MONO_LT] THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `exp(--c) < &1 / &2` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_EXP_NEG] THEN
    SUBGOAL_THEN `&2 < exp c` MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPEC `c:real` REAL_EXP_POS_LT) THEN
    SPEC_TAC(`exp c`,`z:real`) THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC[REAL_ARITH `&1 / &2 = inv(&2)`] THEN
    MATCH_MP_TAC REAL_LT_INV2 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[annulus; IN_ELIM_THM] THEN GEN_TAC THEN
    MP_TAC(SPEC `--c` REAL_EXP_POS_LT) THEN
    MESON_TAC[NORM_0; REAL_LT_ANTISYM; REAL_LT_TRANS];
    REWRITE_TAC[SUBSET; annulus; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[SUBSET; annulus; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC]);;

(* A surgery neck of event k parametrizes the neck domain inside Omega, in  *)
(* the old stage and in the open subspace Omega (rfs_surgery_ok, the strong *)
(* neck of the pre-surgery view at the event time).                         *)

let P4_SURGERY_NECK_PARAM = prove
 (`!(hs:(A)rfs_history) C eps dl h k i.
        rfs_history_ok hs /\ 1 <= k /\ k <= hs_count hs /\
        rfs_surgery_ok hs C eps dl h k /\ i IN ev_index (hs_event hs k)
        ==> &0 < dl(hs_time hs k) /\
            mfd_param (hs_top hs (k - 1)) (hs_atlas hs (k - 1))
                      (rfs_neck_dom (dl(hs_time hs k))) (ev_neck (hs_event hs k) i) /\
            mfd_param (subtopology (hs_top hs (k - 1)) (ev_omega (hs_event hs k)))
                      (restrict_atlas (hs_atlas hs (k - 1)) (ev_omega (hs_event hs k)))
                      (rfs_neck_dom (dl(hs_time hs k))) (ev_neck (hs_event hs k) i) /\
            IMAGE (ev_neck (hs_event hs k) i) (rfs_neck_dom (dl(hs_time hs k))) SUBSET
            ev_omega (hs_event hs k)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `smooth_manifold_atlas (hs_top hs (k - 1)) (hs_atlas (hs:(A)rfs_history) (k - 1))`
  ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPEC `k - 1` o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o
      GEN_REWRITE_RULE I [rfs_history_ok]) THEN
    ANTS_TAC THENL
     [UNDISCH_TAC `k <= hs_count (hs:(A)rfs_history)` THEN ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `open_in (hs_top hs (k - 1)) (ev_omega (hs_event (hs:(A)rfs_history) k))`
  ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPEC `k:num` o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o
      GEN_REWRITE_RULE I [rfs_history_ok]) THEN
    ASM_REWRITE_TAC[rfs_event_ok] THEN SIMP_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [rfs_surgery_ok]) THEN
  DISCH_THEN(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:A` (MP_TAC o CONJUNCT1)) THEN
  REWRITE_TAC[rfs_strong_neck; rfs_preview; rfs_evolving_neck; rfs_neck] THEN
  REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC APX_PARAM_FROM_RESTRICT THEN ASM_REWRITE_TAC[]);;

(* The cap data of one neck (p3_cap_param): the collapse is the identity     *)
(* through Phi on the retained side, lands in the closed core on the plus    *)
(* side, and is the tip beyond s = A0 + 4.                                   *)

let P4_STD_NC_NORM = prove
 (`!g0 A0 (x:real^3).
        ~(x = vec 0)
        ==> norm(p3_std_nc g0 A0 x) = exp((A0 + &4 - p3_std_dist g0 x) / sqrt(&2))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p3_std_nc; NORM_MUL; REAL_ABS_EXP] THEN
  ASM_SIMP_TAC[REAL_ABS_INV; REAL_ABS_NORM; REAL_MUL_LINV; NORM_EQ_0; REAL_MUL_RID]);;

let P4_CAP_FACTS = prove
 (`!md g0 A0 dl h (hs:(A)rfs_history) k i Phi xi.
        p3_cap_param (md,g0,A0) (dl,h) hs k i Phi xi /\
        &0 < dl(hs_time hs k) /\ &0 < A0
        ==> (!y. y IN rfs_neck_dom (dl(hs_time hs k)) /\ sqrt(&2) * log(norm y) < &0
                 ==> Phi(xi y) = ev_neck (hs_event hs k) i y) /\
            (!y. y IN rfs_neck_dom (dl(hs_time hs k)) /\ &0 <= sqrt(&2) * log(norm y)
                 ==> Phi(xi y) IN IMAGE (ev_capm (hs_event hs k) i) (cball(vec 0,&1))) /\
            (!y. y IN rfs_neck_dom (dl(hs_time hs k)) /\
                 A0 + &4 <= sqrt(&2) * log(norm y)
                 ==> xi y = vec 0) /\
            Phi (vec 0) IN IMAGE (ev_capm (hs_event hs k) i) (cball(vec 0,&1)) /\
            (A0 + &4) * dl(hs_time hs k) < &1 /\
            smooth_map_on (rfs_neck_dom (dl(hs_time hs k))) xi /\
            mfd_param (hs_top hs k) (hs_atlas hs k)
              {x | --(inv(dl(hs_time hs k))) < A0 + &4 - p3_std_dist g0 x} Phi /\
            (!y. y IN rfs_neck_dom (dl(hs_time hs k))
                 ==> xi y IN {x | --(inv(dl(hs_time hs k))) < A0 + &4 - p3_std_dist g0 x}) /\
            (!y v. y IN rfs_neck_dom (dl(hs_time hs k))
                   ==> (jacobian xi (at y) ** v) dot
                       (rfs_pullback (hs_atlas hs k) Phi (hs_metric hs k (hs_time hs k))
                                     (xi y) ** (jacobian xi (at y) ** v)) <=
                       v dot (rfs_pullback (rfs_vatlas (rfs_preview hs k) (hs_time hs k))
                                           (ev_neck (hs_event hs k) i)
                                           (rfs_vmetric (rfs_preview hs k) (hs_time hs k))
                                           y ** v))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p3_cap_param] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN
  MP_TAC(SPECL [`dl(hs_time (hs:(A)rfs_history) k):real`; `A0:real`] P4_NECK_DOM_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!y. y IN rfs_neck_dom (dl(hs_time (hs:(A)rfs_history) k)) /\
        &0 <= sqrt(&2) * log(norm y)
        ==> Phi((xi:real^3->real^3) y) IN
            IMAGE (ev_capm (hs_event hs k) i) (cball(vec 0,&1))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "IMAGE" with Failure _ -> false)) THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[IN_ELIM_THM] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:real^3` o check (fun th ->
      try let t = snd(dest_forall(concl th)) in
          is_imp t && length(conjuncts(rand t)) = 4
      with Failure _ -> false)) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM MATCH_ACCEPT_TAC) THEN
  FIRST
   [(X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
     FIRST_ASSUM(MP_TAC o C MP (ASSUME `(y:real^3) IN rfs_neck_dom (dl(hs_time (hs:(A)rfs_history) k))`) o SPEC `y:real^3` o check (fun th ->
      try let t = snd(dest_forall(concl th)) in
          is_imp t && length(conjuncts(rand t)) = 4
      with Failure _ -> false)) THEN
     DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
       (fun th -> ASSUME_TAC(MP th (MATCH_MP REAL_LT_IMP_LE
          (ASSUME `sqrt(&2) * log(norm(y:real^3)) < &0`)))) (K ALL_TAC))) THEN
     SUBGOAL_THEN `~((xi:real^3->real^3) y = vec 0)` ASSUME_TAC THENL
      [DISCH_TAC THEN
       UNDISCH_TAC `p3_std_nc g0 A0 ((xi:real^3->real^3) y) = y` THEN
       ASM_REWRITE_TAC[p3_std_nc; NORM_0; REAL_INV_0; VECTOR_MUL_LZERO;
                       VECTOR_MUL_RZERO] THEN
       DISCH_THEN(SUBST_ALL_TAC o SYM) THEN ASM_MESON_TAC[];
       ALL_TAC] THEN
     SUBGOAL_THEN
      `A0 + &4 - p3_std_dist g0 ((xi:real^3->real^3) y) = sqrt(&2) * log(norm(y:real^3))`
     ASSUME_TAC THENL
      [MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `(xi:real^3->real^3) y`]
                    P4_STD_NC_NORM) THEN
       ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
       REWRITE_TAC[LOG_EXP] THEN
       SUBGOAL_THEN `&0 < sqrt(&2)` MP_TAC THENL
        [MATCH_MP_TAC SQRT_POS_LT THEN REAL_ARITH_TAC; ALL_TAC] THEN
       CONV_TAC REAL_FIELD;
       ALL_TAC] THEN
     UNDISCH_TAC `p3_std_nc g0 A0 ((xi:real^3->real^3) y) = y` THEN
     DISCH_THEN(fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [SYM th]) THEN
     FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]) THEN NO_TAC;
    (X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
     FIRST_ASSUM(MP_TAC o C MP (ASSUME `(y:real^3) IN rfs_neck_dom (dl(hs_time (hs:(A)rfs_history) k))`) o SPEC `y:real^3` o check (fun th ->
      try let t = snd(dest_forall(concl th)) in
          is_imp t && length(conjuncts(rand t)) = 4
      with Failure _ -> false)) THEN
     DISCH_THEN(MP_TAC o el 3 o CONJUNCTS) THEN
     DISCH_THEN MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC) THEN NO_TAC;
    (X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
     FIRST_ASSUM(MP_TAC o C MP (ASSUME `(y:real^3) IN rfs_neck_dom (dl(hs_time (hs:(A)rfs_history) k))`) o SPEC `y:real^3` o check (fun th ->
      try let t = snd(dest_forall(concl th)) in
          is_imp t && length(conjuncts(rand t)) = 4
      with Failure _ -> false)) THEN
     DISCH_THEN(ACCEPT_TAC o el 0 o CONJUNCTS)) THEN NO_TAC;
    (SUBGOAL_THEN
      `(exp((A0 + &4) / sqrt(&2)) % basis 1:real^3) IN
       rfs_neck_dom (dl(hs_time (hs:(A)rfs_history) k)) /\
       sqrt(&2) * log(norm(exp((A0 + &4) / sqrt(&2)) % basis 1:real^3)) = A0 + &4`
     STRIP_ASSUME_TAC THENL
      [SIMP_TAC[NORM_MUL; NORM_BASIS; DIMINDEX_3; ARITH; REAL_ABS_EXP; REAL_MUL_RID] THEN
       REWRITE_TAC[LOG_EXP] THEN CONJ_TAC THENL
        [FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
           try fst(dest_const(fst(strip_comb(lhand(concl th))))) = "GSPEC"
           with Failure _ -> false)) THEN
         SIMP_TAC[IN_ELIM_THM; NORM_MUL; NORM_BASIS; DIMINDEX_3; ARITH; REAL_ABS_EXP;
                  REAL_MUL_RID; REAL_LE_REFL] THEN
         ASM_REAL_ARITH_TAC;
         SUBGOAL_THEN `&0 < sqrt(&2)` MP_TAC THENL
          [MATCH_MP_TAC SQRT_POS_LT THEN REAL_ARITH_TAC; ALL_TAC] THEN
         CONV_TAC REAL_FIELD];
       ALL_TAC] THEN
     SUBGOAL_THEN `(xi:real^3->real^3) (exp((A0 + &4) / sqrt(&2)) % basis 1) = vec 0`
     (fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [SYM th]) THENL
      [FIRST_ASSUM(MP_TAC o C MP (ASSUME
         `(exp((A0 + &4) / sqrt(&2)) % basis 1:real^3) IN
          rfs_neck_dom (dl(hs_time (hs:(A)rfs_history) k))`) o
         SPEC `exp((A0 + &4) / sqrt(&2)) % basis 1:real^3` o check (fun th ->
      try let t = snd(dest_forall(concl th)) in
          is_imp t && length(conjuncts(rand t)) = 4
      with Failure _ -> false)) THEN
       DISCH_THEN(MP_TAC o el 3 o CONJUNCTS) THEN
       DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[REAL_LE_REFL];
       FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]) THEN NO_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Local tools for the pinch map (smoothness, continuity and                 *)
(* the pinch Jacobian only depend on the map near each point).              *)
(* ------------------------------------------------------------------------- *)

let P4_FRECHET_LOCAL = prove
 (`!s (f:real^M->real^N) g y.
        open s /\ y IN s /\ (!z. z IN s ==> f z = g z)
        ==> frechet_derivative f (at y) = frechet_derivative g (at y)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[frechet_derivative] THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `f':real^M->real^N` THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL]) THEN
  DISCH_THEN(MP_TAC o SPEC `y:real^M`) THEN ASM_REWRITE_TAC[SUBSET; IN_BALL] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EQ_TAC THEN DISCH_TAC THEN MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_AT THENL
   [EXISTS_TAC `f:real^M->real^N`; EXISTS_TAC `g:real^M->real^N`] THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `z:real^M` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(z:real^M) IN s` (fun th -> ASM_MESON_TAC[th]) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[DIST_SYM]);;

let P4_MFD_SMOOTH_LOCAL = prove
 (`!top atlas top' atlas' W (f:A->B).
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
        smooth_manifold_atlas top' (atlas':((B->bool)#(B->real^M))->bool) /\
        open_in top W /\ continuous_map (subtopology top W,top') f /\
        (!x. x IN W
             ==> ?U g. open_in top U /\ x IN U /\ U SUBSET W /\
                       mfd_smooth_map atlas atlas' U g /\
                       (!z. z IN U ==> f z = g z))
        ==> mfd_smooth_map atlas atlas' W f`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_smooth_map] THEN
  MAP_EVERY X_GEN_TAC [`c:(A->bool)#(A->real^N)`; `c':(B->bool)#(B->real^M)`] THEN
  STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `top':B topology`; `atlas':((B->bool)#(B->real^M))->bool`;
                   `c:(A->bool)#(A->real^N)`; `c':(B->bool)#(B->real^M)`;
                   `W:A->bool`; `f:A->B`] MFDM_CHART_DOMAIN_OPEN) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[FORALL_IN_IMAGE; IN_ELIM_THM; IN_INTER] THEN
  X_GEN_TAC `x:A` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `U:A->bool` (X_CHOOSE_THEN `g:A->B` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `continuous_map (subtopology top U,top') (f:A->B)` ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY_MONO THEN
    EXISTS_TAC `W:A->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `IMAGE (SND (c:(A->bool)#(A->real^N)))
                {z | z IN FST c INTER U /\ (f:A->B) z IN FST (c':(B->bool)#(B->real^M))}` THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `top':B topology`; `atlas':((B->bool)#(B->real^M))->bool`;
                   `c:(A->bool)#(A->real^N)`; `c':(B->bool)#(B->real^M)`;
                   `U:A->bool`; `f:A->B`] MFDM_CHART_DOMAIN_OPEN) THEN
    ASM_SIMP_TAC[];
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_ELIM_THM; IN_INTER];
    SUBGOAL_THEN
     `{z | z IN FST c INTER U /\ (f:A->B) z IN FST (c':(B->bool)#(B->real^M))} =
      {z | z IN FST (c:(A->bool)#(A->real^N)) INTER U /\ (g:A->B) z IN FST c'}`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INTER] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`c:(A->bool)#(A->real^N)`; `c':(B->bool)#(B->real^M)`] o
      GEN_REWRITE_RULE I [mfd_smooth_map]) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] SMOOTH_MAP_ON_EQ) THEN
    REWRITE_TAC[FORALL_IN_IMAGE; IN_ELIM_THM; IN_INTER; o_THM] THEN
    X_GEN_TAC `z:A` THEN STRIP_TAC THEN AP_TERM_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_SIMP_TAC[]]);;

(* The pinch Jacobian at x only depends on the map near x. *)

let P4_PINCH_JAC_LOCAL = prove
 (`!topX atlasX topY atlasY O (f:A->B) g x.
        smooth_manifold_atlas topX (atlasX:((A->bool)#(A->real^N))->bool) /\
        smooth_manifold_atlas topY (atlasY:((B->bool)#(B->real^M))->bool) /\
        open_in topX O /\ x IN O /\ (!z. z IN O ==> f z = g z)
        ==> jacobian (\y. SND (chart_at atlasY (f x)) (f (chart_inv (chart_at atlasX x) y)))
                     (at (SND (chart_at atlasX x) x)) =
            jacobian (\y. SND (chart_at atlasY (g x)) (g (chart_inv (chart_at atlasX x) y)))
                     (at (SND (chart_at atlasX x) x))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(f:A->B) x = g x` SUBST1_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[jacobian] THEN AP_TERM_TAC THEN
  MATCH_MP_TAC P4_FRECHET_LOCAL THEN
  SUBGOAL_THEN `(x:A) IN topspace topX` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^N))->bool`; `x:A`]
         CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^N))->bool`;
                 `chart_at (atlasX:((A->bool)#(A->real^N))->bool) x`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  EXISTS_TAC `IMAGE (SND (chart_at (atlasX:((A->bool)#(A->real^N))->bool) x))
                    (FST (chart_at atlasX x) INTER O)` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MFDM_CHART_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`topX:A topology`; `atlasX:((A->bool)#(A->real^N))->bool`] THEN
    ASM_SIMP_TAC[OPEN_IN_INTER; INTER_SUBSET];
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_INTER];
    REWRITE_TAC[FORALL_IN_IMAGE; IN_INTER] THEN X_GEN_TAC `w:A` THEN STRIP_TAC THEN
    ASM_SIMP_TAC[]]);;

(* Derivatives of parametrizations and of their inverses, read in charts.   *)

let P4_PARAM_CHART_HASDERIV = prove
 (`!top atlas s (e:real^N->A) c y.
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
        mfd_param top atlas s e /\ c IN atlas /\ y IN s /\ e y IN FST c
        ==> ((SND c o e) has_derivative frechet_derivative (SND c o e) (at y)) (at y)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `s:real^N->bool`; `e:real^N->A`] GRGD_PARAM_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `e':A->real^N` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`subtopology euclidean (s:real^N->bool)`; `open_set_atlas (s:real^N->bool)`;
                 `top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `s:real^N->bool`; `e:real^N->A`; `(s:real^N->bool,(\x:real^N. x))`;
                 `c:(A->bool)#(A->real^N)`; `y:real^N`] GRGD_CHART_MAP_DIFF) THEN
  ASM_SIMP_TAC[OPEN_SET_ATLAS; SUBTOPOLOGY_SUBTOPOLOGY; INTER_IDEMPOT; FST; SND] THEN
  ANTS_TAC THENL
   [REWRITE_TAC[open_set_atlas; IN_SING; OPEN_IN_SUBTOPOLOGY_REFL;
                TOPSPACE_EUCLIDEAN; SUBSET_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z. z IN s
        ==> (SND (c:(A->bool)#(A->real^N)) o (e:real^N->A) o
             chart_inv (s:real^N->bool,(\x:real^N. x))) z = (SND c o e) z`
  ASSUME_TAC THENL [SIMP_TAC[o_THM; MFDM_CHART_INV_ID]; ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^N->bool`;
                 `SND (c:(A->bool)#(A->real^N)) o (e:real^N->A) o
                  chart_inv (s:real^N->bool,(\x:real^N. x))`;
                 `SND (c:(A->bool)#(A->real^N)) o (e:real^N->A)`; `y:real^N`]
                P4_FRECHET_LOCAL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_AT THEN
  EXISTS_TAC `SND (c:(A->bool)#(A->real^N)) o (e:real^N->A) o
              chart_inv (s:real^N->bool,(\x:real^N. x))` THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL] o check (fun th ->
    try fst(dest_const(fst(strip_comb(concl th)))) = "open" with Failure _ -> false)) THEN
  DISCH_THEN(MP_TAC o SPEC `y:real^N`) THEN ASM_REWRITE_TAC[SUBSET; IN_BALL] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
    try is_eq(rand(snd(dest_forall(concl th)))) with Failure _ -> false)) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[DIST_SYM]);;

let P4_PARAM_INV_CHART_HASDERIV = prove
 (`!top atlas s (e:real^N->A) einv c x.
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
        mfd_param top atlas s e /\ (!z. z IN s ==> einv (e z) = z) /\
        c IN atlas /\ x IN FST c /\ x IN IMAGE e s
        ==> ((einv o chart_inv c) has_derivative
             frechet_derivative (einv o chart_inv c) (at (SND c x))) (at (SND c x)) /\
            ?N. open N /\ SND c x IN N /\
                (!w. w IN N ==> chart_inv c w IN FST c INTER IMAGE e s /\
                                SND c (chart_inv c w) = w)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `s:real^N->bool`; `e:real^N->A`] GRGD_PARAM_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `e':A->real^N` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `N = IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c INTER IMAGE (e:real^N->A) s)` THEN
  SUBGOAL_THEN `open (N:real^N->bool) /\ SND (c:(A->bool)#(A->real^N)) x IN N /\
                (!w. w IN N ==> chart_inv c w IN FST c INTER IMAGE (e:real^N->A) s /\
                                SND c (chart_inv c w) = w)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "N" THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MFDM_CHART_IMAGE_OPEN THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
      ASM_SIMP_TAC[OPEN_IN_INTER; INTER_SUBSET];
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_INTER];
      REWRITE_TAC[FORALL_IN_IMAGE; IN_INTER] THEN X_GEN_TAC `z:A` THEN STRIP_TAC THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  CONJ_TAC THENL [ALL_TAC; EXISTS_TAC `N:real^N->bool` THEN ASM_REWRITE_TAC[]] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `subtopology euclidean (s:real^N->bool)`; `open_set_atlas (s:real^N->bool)`;
                 `IMAGE (e:real^N->A) s`; `e':A->real^N`; `c:(A->bool)#(A->real^N)`;
                 `(s:real^N->bool,(\x:real^N. x))`; `x:A`] GRGD_CHART_MAP_DIFF) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[OPEN_SET_ATLAS; FST] THEN REPEAT CONJ_TAC THEN
    FIRST
     [REWRITE_TAC[open_set_atlas; IN_SING] THEN NO_TAC;
      MP_TAC(ASSUME `(x:A) IN IMAGE (e:real^N->A) s`) THEN REWRITE_TAC[IN_IMAGE] THEN
      STRIP_TAC THEN ASM_SIMP_TAC[] THEN NO_TAC;
      MATCH_MP_TAC CONTINUOUS_MAP_INTO_FULLTOPOLOGY THEN
      EXISTS_TAC `s:real^N->bool` THEN FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[SND] THEN
  SUBGOAL_THEN
   `!w. w IN N
        ==> ((\x:real^N. x) o (e':A->real^N) o chart_inv (c:(A->bool)#(A->real^N))) w =
            (einv o chart_inv c) w`
  ASSUME_TAC THENL
   [X_GEN_TAC `w:real^N` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `w:real^N` o check (fun th ->
      try is_imp(snd(dest_forall(concl th))) &&
          fst(dest_const(fst(strip_comb(lhand(rand(snd(dest_forall(concl th))))))))
          = "IN" with Failure _ -> false)) THEN
    ASM_REWRITE_TAC[IN_INTER; IN_IMAGE] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `z:real^N` STRIP_ASSUME_TAC)) ASSUME_TAC) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`N:real^N->bool`;
                 `(\x:real^N. x) o (e':A->real^N) o chart_inv (c:(A->bool)#(A->real^N))`;
                 `(einv:A->real^N) o chart_inv (c:(A->bool)#(A->real^N))`;
                 `SND (c:(A->bool)#(A->real^N)) x`] P4_FRECHET_LOCAL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_AT THEN
  EXISTS_TAC `(\x:real^N. x) o (e':A->real^N) o chart_inv (c:(A->bool)#(A->real^N))` THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL] o check (fun th ->
    try concl th = `open (N:real^N->bool)` with Failure _ -> false)) THEN
  DISCH_THEN(MP_TAC o SPEC `SND (c:(A->bool)#(A->real^N)) x`) THEN
  ASM_REWRITE_TAC[SUBSET; IN_BALL] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
    try is_eq(rand(snd(dest_forall(concl th)))) with Failure _ -> false)) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[DIST_SYM]);;

(* The derivative bound through a collapse: if xi is 1-Lipschitz from the  *)
(* pullback of gl by the neck e to the pullback of gY by Phi, then the map  *)
(* Phi o xi o e^-1 has |dp v|_gY <= |v|_gl, read in preferred charts.        *)

let P4_NECK_QF = prove
 (`!topX atlasX topY atlasY Om (e:real^3->A) s (PHI:real^3->B) D (XI:real^3->real^3)
    einv (gl:A->real^3^3) (gY:B->real^3^3) y v.
        smooth_manifold_atlas topX (atlasX:((A->bool)#(A->real^3))->bool) /\
        smooth_manifold_atlas topY (atlasY:((B->bool)#(B->real^3))->bool) /\
        open_in topX Om /\ open s /\ open D /\
        mfd_param topX atlasX s e /\
        mfd_param (subtopology topX Om) (restrict_atlas atlasX Om) s e /\
        mfd_param topY atlasY D PHI /\
        smooth_map_on s XI /\ (!z. z IN s ==> XI z IN D) /\
        (!z. z IN s ==> einv (e z) = z) /\ y IN s /\
        (!w. (jacobian XI (at y) ** w) dot
             (rfs_pullback atlasY PHI gY (XI y) ** (jacobian XI (at y) ** w)) <=
             w dot (rfs_pullback (restrict_atlas atlasX Om) e
                                 (restrict_metric atlasX Om gl) y ** w))
        ==> (jacobian (\w. SND (chart_at atlasY (PHI (XI (einv (e y)))))
                               (PHI (XI (einv (chart_inv (chart_at atlasX (e y)) w)))))
                      (at (SND (chart_at atlasX (e y)) (e y))) ** v) dot
            (gY (PHI (XI (einv (e y)))) **
             (jacobian (\w. SND (chart_at atlasY (PHI (XI (einv (e y)))))
                                (PHI (XI (einv (chart_inv (chart_at atlasX (e y)) w)))))
                       (at (SND (chart_at atlasX (e y)) (e y))) ** v)) <=
            v dot (gl (e y) ** v)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `x = (e:real^3->A) y` THEN
  SUBGOAL_THEN `(einv:A->real^3) x = y` ASSUME_TAC THENL
   [EXPAND_TAC "x" THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(x:A) IN IMAGE (e:real^3->A) s /\ (x:A) IN topspace topX /\ x IN Om`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                   `Om:A->bool`; `s:real^3->bool`; `e:real^3->A`] APX_PARAM_FROM_RESTRICT) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(x:A) IN IMAGE (e:real^3->A) s` ASSUME_TAC THENL
     [EXPAND_TAC "x" THEN MATCH_MP_TAC FUN_IN_IMAGE THEN FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                     `s:real^3->bool`; `e:real^3->A`; `s:real^3->bool`]
                    MFD_PARAM_IMAGE_SUBSET) THEN
      ASM_REWRITE_TAC[SUBSET_REFL] THEN ASM SET_TAC[];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(PHI:real^3->B) ((XI:real^3->real^3) y) IN topspace topY` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`topY:B topology`; `atlasY:((B->bool)#(B->real^3))->bool`;
                   `D:real^3->bool`; `PHI:real^3->B`; `D:real^3->bool`]
                  MFD_PARAM_IMAGE_SUBSET) THEN
    ASM_REWRITE_TAC[SUBSET_REFL; SUBSET; FORALL_IN_IMAGE] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`; `x:A`]
         CHART_AT) THEN
  MP_TAC(ISPECL [`topY:B topology`; `atlasY:((B->bool)#(B->real^3))->bool`;
                 `(PHI:real^3->B) ((XI:real^3->real^3) y)`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  ABBREV_TAC `cX = chart_at (atlasX:((A->bool)#(A->real^3))->bool) x` THEN
  ABBREV_TAC `cY = chart_at (atlasY:((B->bool)#(B->real^3))->bool) ((PHI:real^3->B) ((XI:real^3->real^3) y))` THEN
  (* the three derivatives *)
  MP_TAC(ISPECL [`topY:B topology`; `atlasY:((B->bool)#(B->real^3))->bool`;
                 `D:real^3->bool`; `PHI:real^3->B`; `cY:(B->bool)#(B->real^3)`;
                 `(XI:real^3->real^3) y`] P4_PARAM_CHART_HASDERIV) THEN
  ASM_SIMP_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                 `s:real^3->bool`; `e:real^3->A`; `einv:A->real^3`;
                 `cX:(A->bool)#(A->real^3)`; `x:A`] P4_PARAM_INV_CHART_HASDERIV) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `N:real^3->bool` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `((XI:real^3->real^3) has_derivative frechet_derivative XI (at y)) (at y)`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `s:real^3->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                 `s:real^3->bool`; `e:real^3->A`; `cX:(A->bool)#(A->real^3)`; `y:real^3`]
                P4_PARAM_CHART_HASDERIV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `chart_inv (cX:(A->bool)#(A->real^3)) (SND cX x) = x` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                   `cX:(A->bool)#(A->real^3)`] MFDM_CHART) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `D1 = frechet_derivative ((einv:A->real^3) o chart_inv (cX:(A->bool)#(A->real^3)))
                                      (at (SND cX x))` THEN
  ABBREV_TAC `D2 = frechet_derivative (XI:real^3->real^3) (at y)` THEN
  ABBREV_TAC `D3 = frechet_derivative (SND (cY:(B->bool)#(B->real^3)) o (PHI:real^3->B))
                                      (at ((XI:real^3->real^3) y))` THEN
  ABBREV_TAC `DE = frechet_derivative (SND (cX:(A->bool)#(A->real^3)) o (e:real^3->A))
                                      (at y)` THEN
  SUBGOAL_THEN
   `(\w. SND (cY:(B->bool)#(B->real^3)) ((PHI:real^3->B) ((XI:real^3->real^3)
          ((einv:A->real^3) (chart_inv (cX:(A->bool)#(A->real^3)) w))))) =
    (SND cY o PHI) o XI o (einv o chart_inv cX)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(((SND (cY:(B->bool)#(B->real^3)) o (PHI:real^3->B)) o (XI:real^3->real^3) o
      ((einv:A->real^3) o chart_inv (cX:(A->bool)#(A->real^3)))) has_derivative
     ((D3:real^3->real^3) o (D2:real^3->real^3) o (D1:real^3->real^3))) (at (SND cX x))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC DIFF_CHAIN_AT THEN CONJ_TAC THENL
     [MATCH_MP_TAC DIFF_CHAIN_AT THEN ASM_REWRITE_TAC[o_THM];
      ASM_REWRITE_TAC[o_THM]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `linear (D1:real^3->real^3) /\ linear (D2:real^3->real^3) /\
    linear (D3:real^3->real^3) /\ linear (DE:real^3->real^3)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN
    FIRST_ASSUM(MATCH_ACCEPT_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [has_derivative] o
      check (fun th -> try
        let t = concl th in
        fst(dest_const(fst(strip_comb t))) = "has_derivative" &&
        (let d = rand(rator t) in is_var d)
      with Failure _ -> false)) ORELSE
    ALL_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `jacobian ((SND (cY:(B->bool)#(B->real^3)) o (PHI:real^3->B)) o (XI:real^3->real^3) o
              (einv:A->real^3) o chart_inv (cX:(A->bool)#(A->real^3))) (at (SND cX x)) =
    matrix(D3:real^3->real^3) ** matrix(D2:real^3->real^3) ** matrix(D1:real^3->real^3)`
  SUBST1_TAC THENL
   [REWRITE_TAC[jacobian] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT o check (fun th ->
      try fst(dest_const(fst(strip_comb(concl th)))) = "has_derivative" &&
          is_comb(rand(rator(concl th))) with Failure _ -> false)) THEN
    ASM_SIMP_TAC[MATRIX_COMPOSE; LINEAR_COMPOSE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `rfs_pullback (atlasY:((B->bool)#(B->real^3))->bool) (PHI:real^3->B) (gY:B->real^3^3)
                 ((XI:real^3->real^3) y) =
    transp(matrix(D3:real^3->real^3)) ** gY (PHI (XI y)) ** matrix D3`
  (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [REWRITE_TAC[rfs_pullback; mpullback] THEN ASM_REWRITE_TAC[o_THM] THEN
    MP_TAC(ISPECL [`topY:B topology`; `atlasY:((B->bool)#(B->real^3))->bool`;
                   `gY:B->real^3^3`; `(PHI:real^3->B) ((XI:real^3->real^3) y)`]
                  METRIC_LOCAL_AT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REFL_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `rfs_pullback (restrict_atlas atlasX Om) (e:real^3->A)
                 (restrict_metric (atlasX:((A->bool)#(A->real^3))->bool) Om gl) y =
    transp(matrix(DE:real^3->real^3)) ** (gl:A->real^3^3) x ** matrix DE`
  (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [MP_TAC(ISPEC `cX:(A->bool)#(A->real^3)` PAIR_SURJECTIVE) THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`U:A->bool`; `phi:A->real^3`] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`subtopology topX (Om:A->bool)`;
                   `restrict_atlas (atlasX:((A->bool)#(A->real^3))->bool) Om`;
                   `restrict_metric (atlasX:((A->bool)#(A->real^3))->bool) Om gl`;
                   `s:real^3->bool`; `e:real^3->A`; `U INTER (Om:A->bool)`; `phi:A->real^3`;
                   `y:real^3`] APX_RFS_PULLBACK_CHART) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC SMOOTH_MANIFOLD_ATLAS_RESTRICT THEN ASM_REWRITE_TAC[];
        FIRST_ASSUM ACCEPT_TAC;
        REWRITE_TAC[IN_RESTRICT_ATLAS] THEN EXISTS_TAC `U:A->bool` THEN
        REWRITE_TAC[] THEN ASM_MESON_TAC[];
        FIRST_ASSUM ACCEPT_TAC;
        ASM_REWRITE_TAC[IN_INTER] THEN
        UNDISCH_TAC `(x:A) IN FST (cX:(A->bool)#(A->real^3))` THEN
        ASM_REWRITE_TAC[FST]];
      DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[mpullback; o_THM] THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(phi:A->real^3) o (e:real^3->A) = SND (cX:(A->bool)#(A->real^3)) o e`
    SUBST1_TAC THENL [ASM_REWRITE_TAC[SND]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                   `U:A->bool`; `phi:A->real^3`; `Om:A->bool`; `gl:A->real^3^3`; `x:A`]
                  METRIC_LOCAL_RESTRICT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[IN_INTER] THEN
      UNDISCH_TAC `(x:A) IN FST (cX:(A->bool)#(A->real^3))` THEN
      UNDISCH_TAC `(cX:(A->bool)#(A->real^3)) IN atlasX` THEN
      ASM_REWRITE_TAC[FST] THEN SIMP_TAC[];
      DISCH_THEN SUBST1_TAC] THEN
    MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                   `gl:A->real^3^3`; `x:A`] METRIC_LOCAL_AT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN
    REFL_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `matrix(DE:real^3->real^3) ** matrix(D1:real^3->real^3) = mat 1`
  ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["DE"; "D1"] THEN
    MATCH_MP_TAC GRGD_JAC_INVERSE THEN EXISTS_TAC `N:real^3->bool` THEN
    ASM_REWRITE_TAC[o_THM] THEN REPEAT CONJ_TAC THENL
     [X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `w:real^3` o check (fun th ->
        try fst(dest_const(fst(strip_comb(lhand(rand(snd(dest_forall(concl th))))))))
            = "IN" &&
            (try fst(dest_const(fst(strip_comb(rand(lhand(rand(snd(dest_forall(concl th)))))))))
                 = "INTER" with Failure _ -> false)
        with Failure _ -> false)) THEN
      ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      REWRITE_TAC[IN_INTER; IN_IMAGE] THEN
      DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC
        (X_CHOOSE_THEN `z1:real^3` STRIP_ASSUME_TAC)) ASSUME_TAC) THEN
      SUBGOAL_THEN `(e:real^3->A) ((einv:A->real^3) (chart_inv (cX:(A->bool)#(A->real^3)) w)) =
                    chart_inv cX w`
      SUBST1_TAC THENL [ASM_SIMP_TAC[]; FIRST_ASSUM ACCEPT_TAC];
      REWRITE_TAC[differentiable] THEN EXISTS_TAC `D1:real^3->real^3` THEN
      FIRST_ASSUM ACCEPT_TAC;
      REWRITE_TAC[differentiable] THEN EXISTS_TAC `DE:real^3->real^3` THEN
      FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `matrix(D1:real^3->real^3) ** (v:real^3)` o
    REWRITE_RULE[jacobian; ASSUME `frechet_derivative (XI:real^3->real^3) (at y) = D2`] o
    check (fun th -> try
      let t = snd(dest_forall(concl th)) in
      fst(dest_const(fst(strip_comb t))) = "real_le" &&
      can (find_term (fun u -> try fst(dest_const u) = "transp" with Failure _ -> false)) t
    with Failure _ -> false)) THEN
  REWRITE_TAC[P4_GRAM_QF_GEN; MATRIX_VECTOR_MUL_ASSOC] THEN
  ASM_REWRITE_TAC[GSYM MATRIX_VECTOR_MUL_ASSOC; MATRIX_VECTOR_MUL_LID] THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_ASSOC] THEN ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_LID] THEN
  REWRITE_TAC[GSYM MATRIX_MUL_ASSOC] THEN ASM_REWRITE_TAC[MATRIX_MUL_RID]);;

(* ------------------------------------------------------------------------- *)
(* The pinch map of a component Y with caps.  p4_capdata bundles, for the    *)
(* necks J of an event, the neck parametrizations of the neck domain s,      *)
(* their inverses EINV, and the cap data PHI, XI of p3_cap_param.  p4_pidx   *)
(* picks the neck whose branch or cut sphere contains a point; p4_pmap is    *)
(* the identity on Y0, Phi o xi o e^-1 on the plus side of each neck, and    *)
(* the cap tip beyond.                                                       *)
(* ------------------------------------------------------------------------- *)

let p4_capdata = new_definition
 `p4_capdata (topX:A topology,atlasX:((A->bool)#(A->real^3))->bool)
             (topY:A topology,atlasY:((A->bool)#(A->real^3))->bool)
             (Om:A->bool) (gl:A->real^3^3) (gYts:A->real^3^3)
             (J:num->bool) (e:num->real^3->A) (cm:num->real^3->A)
             (s:real^3->bool) (D:real^3->bool) (A0:real)
             (PHI:num->real^3->A) (XI:num->real^3->real^3) (EINV:num->A->real^3) <=>
    open s /\ open D /\ &0 < A0 /\
    annulus (&1 / &2) (&2) SUBSET s /\
    {y | &1 <= norm y /\ norm y <= exp((A0 + &4) / sqrt(&2))} SUBSET s /\
    (!y. y IN s ==> ~(y = vec 0)) /\
    !i. i IN J
        ==> mfd_param topX atlasX s (e i) /\
            mfd_param (subtopology topX Om) (restrict_atlas atlasX Om) s (e i) /\
            (!z. z IN s ==> EINV i (e i z) = z) /\
            mfd_param topY atlasY D (PHI i) /\
            smooth_map_on s (XI i) /\ (!y. y IN s ==> XI i y IN D) /\
            (!y. y IN s /\ sqrt(&2) * log(norm y) < &0 ==> PHI i (XI i y) = e i y) /\
            (!y. y IN s /\ &0 <= sqrt(&2) * log(norm y)
                 ==> PHI i (XI i y) IN IMAGE (cm i) (cball(vec 0,&1))) /\
            (!y. y IN s /\ A0 + &4 <= sqrt(&2) * log(norm y) ==> XI i y = vec 0) /\
            PHI i (vec 0) IN IMAGE (cm i) (cball(vec 0,&1)) /\
            (!y w. y IN s
                   ==> (jacobian (XI i) (at y) ** w) dot
                       (rfs_pullback atlasY (PHI i) gYts (XI i y) **
                        (jacobian (XI i) (at y) ** w)) <=
                       w dot (rfs_pullback (restrict_atlas atlasX Om) (e i)
                                           (restrict_metric atlasX Om gl) y ** w))`;;

let p4_pidx = new_definition
 `p4_pidx (topX:A topology) (IY:num->bool) (e:num->real^3->A) (x:A) =
    @i. i IN IY /\
        (x IN IMAGE (e i) (sphere(vec 0,&1)) \/
         x IN p4_side topX (e i) (e i (&4 / &3 % basis 1)))`;;

let p4_pmap = new_definition
 `p4_pmap (topX:A topology) (Y0:A->bool) (IY:num->bool) (e:num->real^3->A)
          (s:real^3->bool) (PHI:num->real^3->A) (XI:num->real^3->real^3)
          (EINV:num->A->real^3) (x:A) =
    if x IN Y0 then x
    else if x IN IMAGE (e (p4_pidx topX IY e x)) {y | y IN s /\ &1 <= norm y}
    then PHI (p4_pidx topX IY e x) (XI (p4_pidx topX IY e x) (EINV (p4_pidx topX IY e x) x))
    else PHI (p4_pidx topX IY e x) (vec 0)`;;

(* The plus half of a cut neck lies in its branch. *)

let P4_HALF_NECK_PLUS = prove
 (`!topX atlasX (gX:real->A->real^3^3) ts topY atlasY gY ev i s.
        rfs_event_ok (topX,atlasX) gX ts (topY,atlasY) gY ev /\
        hausdorff_space topX /\
        smooth_manifold_atlas topX (atlasX:((A->bool)#(A->real^3))->bool) /\
        i IN ev_index ev /\
        mfd_param topX atlasX s (ev_neck ev i) /\
        annulus (&1 / &2) (&2) SUBSET s /\
        connected {y | y IN s /\ &1 < norm y}
        ==> IMAGE (ev_neck ev i) {y | y IN s /\ &1 < norm y} SUBSET
            p4_side topX (ev_neck ev i) (ev_neck ev i (&4 / &3 % basis 1))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                 `gX:real->A->real^3^3`; `ts:real`; `topY:A topology`;
                 `atlasY:((A->bool)#(A->real^3))->bool`; `gY:real->A->real^3^3`;
                 `ev:(A)rfs_event`; `i:num`] P4_EVENT_CAPS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(ASSUME_TAC o CONJUNCT1)] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P4_NECK_PIECES) THEN
  SUBGOAL_THEN
   `ev_neck ev i (&4 / &3 % basis 1) IN
    topspace topX DIFF IMAGE (ev_neck (ev:(A)rfs_event) i) (sphere(vec 0,&1))`
  ASSUME_TAC THENL
   [MP_TAC(MATCH_MP OPEN_IN_SUBSET (ASSUME
      `open_in topX (IMAGE (ev_neck (ev:(A)rfs_event) i) (annulus (&1 / &2) (&2)))`)) THEN
    MAP_EVERY (fun t -> MP_TAC(ASSUME t))
     [`IMAGE (ev_neck ev i) (annulus (&1 / &2) (&2)) =
       IMAGE (ev_neck ev i) (annulus (&1 / &2) (&1)) UNION
       IMAGE (ev_neck ev i) (sphere(vec 0,&1)) UNION
       IMAGE (ev_neck (ev:(A)rfs_event) i) (annulus (&1) (&2))`;
      `DISJOINT (IMAGE (ev_neck ev i) (annulus (&1) (&2)))
                (IMAGE (ev_neck (ev:(A)rfs_event) i) (sphere(vec 0,&1)))`;
      `ev_neck ev i (&4 / &3 % basis 1) IN
       IMAGE (ev_neck (ev:(A)rfs_event) i) (annulus (&1) (&2))`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                 `ev_neck (ev:(A)rfs_event) i`; `ev_neck (ev:(A)rfs_event) i (&4 / &3 % basis 1)`]
                P4_SIDE_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MATCH_MP_TAC o el 4 o CONJUNCTS) THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC APX_PARAM_CONNECTED_IMAGE THEN
    MAP_EVERY EXISTS_TAC [`atlasX:((A->bool)#(A->real^3))->bool`; `s:real^3->bool`] THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_IMAGE; IN_ELIM_THM;
                IN_SPHERE_0] THEN
    X_GEN_TAC `z:A` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC)
                               (X_CHOOSE_THEN `y':real^3` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `(y:real^3) = y'` MP_TAC THENL
     [MATCH_MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                           `s:real^3->bool`; `ev_neck (ev:(A)rfs_event) i`] MFD_PARAM_INJ) THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
        try fst(dest_const(fst(strip_comb(lhand(concl th))))) = "annulus"
        with Failure _ -> false)) THEN
      REWRITE_TAC[annulus; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
      DISCH_THEN SUBST_ALL_TAC THEN ASM_REAL_ARITH_TAC];
    REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN EXISTS_TAC `&4 / &3 % basis 1:real^3` THEN
    REWRITE_TAC[] THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
        try fst(dest_const(fst(strip_comb(lhand(concl th))))) = "annulus"
        with Failure _ -> false)) THEN
      SIMP_TAC[annulus; IN_ELIM_THM; NORM_MUL; NORM_BASIS; DIMINDEX_3; ARITH] THEN
      REAL_ARITH_TAC;
      SIMP_TAC[NORM_MUL; NORM_BASIS; DIMINDEX_3; ARITH] THEN REAL_ARITH_TAC]]);;

(* The neck index of a point of a cut sphere or a branch is unique. *)

let P4_PIDX_UNIQUE = prove
 (`!topX atlasX (gX:real->A->real^3^3) ts topY atlasY gY ev Y i x.
        rfs_event_ok (topX,atlasX) gX ts (topY,atlasY) gY ev /\
        hausdorff_space topX /\
        smooth_manifold_atlas topX (atlasX:((A->bool)#(A->real^3))->bool) /\
        apx_sphere_sep topX atlasX /\
        Y IN connected_components_of topY /\
        i IN ev_index ev /\ ev_capm ev i (vec 0) IN Y /\
        (x IN IMAGE (ev_neck ev i) (sphere(vec 0,&1)) \/
         x IN p4_side topX (ev_neck ev i) (ev_neck ev i (&4 / &3 % basis 1)))
        ==> p4_pidx topX {i | i IN ev_index ev /\ ev_capm ev i (vec 0) IN Y}
                    (ev_neck ev) x = i`,
  REPEAT GEN_TAC THEN DISCH_THEN(MAP_EVERY ASSUME_TAC o CONJUNCTS) THEN
  REWRITE_TAC[p4_pidx] THEN
  MATCH_MP_TAC SELECT_UNIQUE THEN X_GEN_TAC `j:num` THEN
  REWRITE_TAC[IN_ELIM_THM] THEN EQ_TAC THENL
   [ALL_TAC; DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]] THEN
  DISCH_THEN(MAP_EVERY ASSUME_TAC o CONJUNCTS) THEN
  ASM_CASES_TAC `j:num = i` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `DISJOINT (IMAGE (ev_neck ev i) (sphere(vec 0,&1)))
             (IMAGE (ev_neck (ev:(A)rfs_event) j) (sphere(vec 0,&1)))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                   `gX:real->A->real^3^3`; `ts:real`; `topY:A topology`;
                   `atlasY:((A->bool)#(A->real^3))->bool`; `gY:real->A->real^3^3`;
                   `ev:(A)rfs_event`] P4_EVENT_FACTS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o
      CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
    REWRITE_TAC[mfd_cut_cap] THEN
    DISCH_THEN(MP_TAC o SPECL [`i:num`; `j:num`] o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `sphere(vec 0:real^3,&1) SUBSET annulus (&1 / &2) (&2)` MP_TAC THENL
     [REWRITE_TAC[SUBSET; IN_SPHERE_0; annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[DISJOINT] THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                 `gX:real->A->real^3^3`; `ts:real`; `topY:A topology`;
                 `atlasY:((A->bool)#(A->real^3))->bool`; `gY:real->A->real^3^3`;
                 `ev:(A)rfs_event`; `Y:A->bool`; `i:num`; `j:num`] P4_BRANCH_SPHERE) THEN
  MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                 `gX:real->A->real^3^3`; `ts:real`; `topY:A topology`;
                 `atlasY:((A->bool)#(A->real^3))->bool`; `gY:real->A->real^3^3`;
                 `ev:(A)rfs_event`; `Y:A->bool`; `j:num`; `i:num`] P4_BRANCH_SPHERE) THEN
  MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                 `gX:real->A->real^3^3`; `ts:real`; `topY:A topology`;
                 `atlasY:((A->bool)#(A->real^3))->bool`; `gY:real->A->real^3^3`;
                 `ev:(A)rfs_event`; `Y:A->bool`; `i:num`; `j:num`] P4_BRANCH_DISJOINT) THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY (fun t -> UNDISCH_TAC t)
   [`(x:A) IN IMAGE (ev_neck ev i) (sphere(vec 0,&1)) \/
     x IN p4_side topX (ev_neck ev i) (ev_neck (ev:(A)rfs_event) i (&4 / &3 % basis 1))`;
    `(x:A) IN IMAGE (ev_neck ev j) (sphere(vec 0,&1)) \/
     x IN p4_side topX (ev_neck ev j) (ev_neck (ev:(A)rfs_event) j (&4 / &3 % basis 1))`;
    `DISJOINT (IMAGE (ev_neck ev i) (sphere(vec 0,&1)))
              (IMAGE (ev_neck (ev:(A)rfs_event) j) (sphere(vec 0,&1)))`] THEN
  REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN MESON_TAC[]);;
(* Values of the pinch map: the identity on the retained points, the cap  *)
(* formula on the neck parameters beyond radius 1/2, the cap tip beyond    *)
(* the collapse radius, and values in the cap on the cut sphere and the   *)
(* branch.  Small separate lemmas.                                          *)

let P4_LOG_FACTS = prove
 (`!r c. &0 < r
         ==> (r < &1 ==> sqrt(&2) * log r < &0) /\
             (&1 <= r ==> &0 <= sqrt(&2) * log r) /\
             (exp(c / sqrt(&2)) < r ==> c <= sqrt(&2) * log r)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < sqrt(&2)` ASSUME_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LT THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT CONJ_TAC THEN DISCH_TAC THENL
   [SUBGOAL_THEN `log r < &0` ASSUME_TAC THENL
     [MP_TAC(SPECL [`r:real`; `&1`] LOG_MONO_LT_IMP) THEN
      ASM_REWRITE_TAC[LOG_1];
      ALL_TAC] THEN
    REWRITE_TAC[REAL_ARITH `a * b < &0 <=> &0 < a * --b`] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_SIMP_TAC[LOG_POS; REAL_LT_IMP_LE];
    SUBGOAL_THEN `c / sqrt(&2) < log r` MP_TAC THENL
     [MP_TAC(SPECL [`exp(c / sqrt(&2))`; `r:real`] LOG_MONO_LT_IMP) THEN
      ASM_REWRITE_TAC[REAL_EXP_POS_LT; LOG_EXP];
      ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN REAL_ARITH_TAC]);;

let P4_PMAP_OFF_RETAINED = prove
 (`!topX atlasX (gX:real->A->real^3^3) ts topY atlasY gY ev Y i x.
        rfs_event_ok (topX,atlasX) gX ts (topY,atlasY) gY ev /\
        hausdorff_space topX /\
        smooth_manifold_atlas topX (atlasX:((A->bool)#(A->real^3))->bool) /\
        apx_sphere_sep topX atlasX /\
        Y IN connected_components_of topY /\
        i IN ev_index ev /\ ev_capm ev i (vec 0) IN Y /\
        (x IN IMAGE (ev_neck ev i) (sphere(vec 0,&1)) \/
         x IN p4_side topX (ev_neck ev i) (ev_neck ev i (&4 / &3 % basis 1)))
        ==> ~(x IN Y INTER topspace topX)`,
  REPEAT GEN_TAC THEN DISCH_THEN(MAP_EVERY ASSUME_TAC o CONJUNCTS) THEN
  MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                 `gX:real->A->real^3^3`; `ts:real`; `topY:A topology`;
                 `atlasY:((A->bool)#(A->real^3))->bool`; `gY:real->A->real^3^3`;
                 `ev:(A)rfs_event`; `Y:A->bool`] P4_RETAINED_BASIC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(ASSUME_TAC o el 1 o CONJUNCTS)] THEN
  MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                 `gX:real->A->real^3^3`; `ts:real`; `topY:A topology`;
                 `atlasY:((A->bool)#(A->real^3))->bool`; `gY:real->A->real^3^3`;
                 `ev:(A)rfs_event`; `Y:A->bool`; `i:num`] P4_BRANCH_BASIC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(ASSUME_TAC o el 4 o CONJUNCTS)] THEN
  SUBGOAL_THEN
   `IMAGE (ev_neck ev i) (sphere(vec 0,&1)) SUBSET
    mfd_cut_spheres (ev_index ev) (ev_neck (ev:(A)rfs_event))`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_SPHERE_0; IN_MFD_CUT_SPHERES] THEN
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    MAP_EVERY EXISTS_TAC [`i:num`; `y:real^3`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o check (fun th -> is_disj(concl th))) THENL
   [MAP_EVERY (fun t -> MP_TAC(ASSUME t))
     [`(x:A) IN IMAGE (ev_neck ev i) (sphere(vec 0,&1))`;
      `IMAGE (ev_neck ev i) (sphere(vec 0,&1)) SUBSET
       mfd_cut_spheres (ev_index ev) (ev_neck (ev:(A)rfs_event))`;
      `Y INTER topspace topX SUBSET
       topspace topX DIFF mfd_cut_spheres (ev_index ev) (ev_neck (ev:(A)rfs_event))`] THEN
    SET_TAC[];
    MAP_EVERY (fun t -> MP_TAC(ASSUME t))
     [`(x:A) IN p4_side topX (ev_neck ev i) (ev_neck (ev:(A)rfs_event) i (&4 / &3 % basis 1))`;
      `DISJOINT (p4_side topX (ev_neck ev i) (ev_neck (ev:(A)rfs_event) i (&4 / &3 % basis 1)))
                (Y INTER topspace topX)`] THEN
    SET_TAC[]]);;

let P4_PMAP_RETAINED = prove
 (`!topX (Y0:A->bool) IY e s PHI XI EINV x.
        x IN Y0 ==> p4_pmap topX Y0 IY e s PHI XI EINV x = x`,
  SIMP_TAC[p4_pmap]);;

let P4_PMAP_PLUS = prove
 (`!topX atlasX (gX:real->A->real^3^3) ts topY atlasY gY ev Y
    (s:real^3->bool) (PHI:num->real^3->A) (XI:num->real^3->real^3)
    (EINV:num->A->real^3) i x.
        rfs_event_ok (topX,atlasX) gX ts (topY,atlasY) gY ev /\
        hausdorff_space topX /\
        smooth_manifold_atlas topX (atlasX:((A->bool)#(A->real^3))->bool) /\
        apx_sphere_sep topX atlasX /\
        Y IN connected_components_of topY /\
        i IN ev_index ev /\ ev_capm ev i (vec 0) IN Y /\
        (x IN IMAGE (ev_neck ev i) (sphere(vec 0,&1)) \/
         x IN p4_side topX (ev_neck ev i) (ev_neck ev i (&4 / &3 % basis 1)))
        ==> p4_pmap topX (Y INTER topspace topX)
              {i | i IN ev_index ev /\ ev_capm ev i (vec 0) IN Y}
              (ev_neck ev) s PHI XI EINV x =
            (if x IN IMAGE (ev_neck ev i) {y | y IN s /\ &1 <= norm y}
             then PHI i (XI i (EINV i x)) else PHI i (vec 0))`,
  REPEAT GEN_TAC THEN DISCH_THEN(MAP_EVERY ASSUME_TAC o CONJUNCTS) THEN
  SUBGOAL_THEN `~((x:A) IN Y INTER topspace topX)` ASSUME_TAC THENL
   [MATCH_MP_TAC P4_PMAP_OFF_RETAINED THEN
    MAP_EVERY EXISTS_TAC
     [`atlasX:((A->bool)#(A->real^3))->bool`; `gX:real->A->real^3^3`; `ts:real`;
      `topY:A topology`; `atlasY:((A->bool)#(A->real^3))->bool`;
      `gY:real->A->real^3^3`; `ev:(A)rfs_event`; `i:num`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `p4_pidx topX {i | i IN ev_index ev /\ ev_capm ev i (vec 0) IN Y}
            (ev_neck ev) (x:A) = i`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P4_PIDX_UNIQUE THEN
    MAP_EVERY EXISTS_TAC
     [`atlasX:((A->bool)#(A->real^3))->bool`; `gX:real->A->real^3^3`; `ts:real`;
      `topY:A topology`; `atlasY:((A->bool)#(A->real^3))->bool`;
      `gY:real->A->real^3^3`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[p4_pmap]);;

let P4_PMAP_NECK = prove
 (`!topX atlasX (gX:real->A->real^3^3) ts topY atlasY gY ev Y s D A0 PHI XI EINV i y.
        rfs_event_ok (topX,atlasX) gX ts (topY,atlasY) gY ev /\
        hausdorff_space topX /\
        smooth_manifold_atlas topX (atlasX:((A->bool)#(A->real^3))->bool) /\
        apx_sphere_sep topX atlasX /\
        Y IN connected_components_of topY /\
        p4_capdata (topX,atlasX) (topY,atlasY) (ev_omega ev) (ev_limit ev) (gY ts)
                   (ev_index ev) (ev_neck ev) (ev_capm ev) s D A0 PHI XI EINV /\
        connected {y | y IN s /\ &1 < norm y} /\
        i IN ev_index ev /\ ev_capm ev i (vec 0) IN Y /\
        y IN s /\ &1 / &2 < norm y
        ==> p4_pmap topX (Y INTER topspace topX)
              {i | i IN ev_index ev /\ ev_capm ev i (vec 0) IN Y}
              (ev_neck ev) s PHI XI EINV (ev_neck ev i y) = PHI i (XI i y)`,
  REPEAT GEN_TAC THEN DISCH_THEN(MAP_EVERY ASSUME_TAC o CONJUNCTS) THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [p4_capdata]) THEN
  DISCH_THEN(MAP_EVERY ASSUME_TAC o CONJUNCTS) THEN
  FIRST_X_ASSUM(MP_TAC o C MP (ASSUME `i IN ev_index (ev:(A)rfs_event)`) o SPEC `i:num`) THEN
  DISCH_THEN(MAP_EVERY ASSUME_TAC o CONJUNCTS) THEN
  SUBGOAL_THEN `&0 < norm(y:real^3)` ASSUME_TAC THENL
   [UNDISCH_TAC `&1 / &2 < norm(y:real^3)` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`norm(y:real^3)`; `A0 + &4`] P4_LOG_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_CASES_TAC `norm(y:real^3) < &1` THENL
   [SUBGOAL_THEN `ev_neck ev i (y:real^3) IN Y INTER topspace (topX:A topology)`
    ASSUME_TAC THENL
     [MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                     `gX:real->A->real^3^3`; `ts:real`; `topY:A topology`;
                     `atlasY:((A->bool)#(A->real^3))->bool`; `gY:real->A->real^3^3`;
                     `ev:(A)rfs_event`; `Y:A->bool`; `i:num`] P4_CAP_IN_COMPONENT) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o CONJUNCT2 o
                 C MP (ASSUME `ev_capm ev i (vec 0) IN (Y:A->bool)`) o CONJUNCT1) THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN DISCH_THEN MATCH_MP_TAC THEN
      REWRITE_TAC[annulus; IN_ELIM_THM] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[MATCH_MP P4_PMAP_RETAINED
      (ASSUME `ev_neck ev i (y:real^3) IN Y INTER topspace (topX:A topology)`)] THEN
    CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ev_neck ev i (y:real^3) IN IMAGE (ev_neck ev i) (sphere(vec 0,&1)) \/
    ev_neck ev i y IN
    p4_side topX (ev_neck ev i) (ev_neck (ev:(A)rfs_event) i (&4 / &3 % basis 1))`
  ASSUME_TAC THENL
   [ASM_CASES_TAC `norm(y:real^3) = &1` THENL
     [DISJ1_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_SPHERE_0];
      DISJ2_TAC THEN
      MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                     `gX:real->A->real^3^3`; `ts:real`; `topY:A topology`;
                     `atlasY:((A->bool)#(A->real^3))->bool`; `gY:real->A->real^3^3`;
                     `ev:(A)rfs_event`; `i:num`; `s:real^3->bool`] P4_HALF_NECK_PLUS) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      MAP_EVERY UNDISCH_TAC [`~(norm(y:real^3) < &1)`; `~(norm(y:real^3) = &1)`] THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                 `gX:real->A->real^3^3`; `ts:real`; `topY:A topology`;
                 `atlasY:((A->bool)#(A->real^3))->bool`; `gY:real->A->real^3^3`;
                 `ev:(A)rfs_event`; `Y:A->bool`; `s:real^3->bool`;
                 `PHI:num->real^3->A`; `XI:num->real^3->real^3`; `EINV:num->A->real^3`;
                 `i:num`; `ev_neck (ev:(A)rfs_event) i (y:real^3)`] P4_PMAP_PLUS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN
   `ev_neck ev i (y:real^3) IN
    IMAGE (ev_neck (ev:(A)rfs_event) i) {y | y IN s /\ &1 <= norm y}`
  (fun th -> REWRITE_TAC[th]) THENL
   [MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `~(norm(y:real^3) < &1)` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let P4_PMAP_TIP = prove
 (`!topX atlasX (gX:real->A->real^3^3) ts topY atlasY gY ev Y s D A0 PHI XI EINV i x.
        rfs_event_ok (topX,atlasX) gX ts (topY,atlasY) gY ev /\
        hausdorff_space topX /\
        smooth_manifold_atlas topX (atlasX:((A->bool)#(A->real^3))->bool) /\
        apx_sphere_sep topX atlasX /\
        Y IN connected_components_of topY /\
        p4_capdata (topX,atlasX) (topY,atlasY) (ev_omega ev) (ev_limit ev) (gY ts)
                   (ev_index ev) (ev_neck ev) (ev_capm ev) s D A0 PHI XI EINV /\
        i IN ev_index ev /\ ev_capm ev i (vec 0) IN Y /\
        x IN p4_side topX (ev_neck ev i) (ev_neck ev i (&4 / &3 % basis 1)) /\
        ~(x IN IMAGE (ev_neck ev i)
                 {y | &1 <= norm y /\ norm y <= exp((A0 + &4) / sqrt(&2))})
        ==> p4_pmap topX (Y INTER topspace topX)
              {i | i IN ev_index ev /\ ev_capm ev i (vec 0) IN Y}
              (ev_neck ev) s PHI XI EINV x = PHI i (vec 0)`,
  REPEAT GEN_TAC THEN DISCH_THEN(MAP_EVERY ASSUME_TAC o CONJUNCTS) THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [p4_capdata]) THEN
  DISCH_THEN(MAP_EVERY ASSUME_TAC o CONJUNCTS) THEN
  FIRST_X_ASSUM(MP_TAC o C MP (ASSUME `i IN ev_index (ev:(A)rfs_event)`) o SPEC `i:num`) THEN
  DISCH_THEN(MAP_EVERY ASSUME_TAC o CONJUNCTS) THEN
  MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                 `gX:real->A->real^3^3`; `ts:real`; `topY:A topology`;
                 `atlasY:((A->bool)#(A->real^3))->bool`; `gY:real->A->real^3^3`;
                 `ev:(A)rfs_event`; `Y:A->bool`; `s:real^3->bool`;
                 `PHI:num->real^3->A`; `XI:num->real^3->real^3`; `EINV:num->A->real^3`;
                 `i:num`; `x:A`] P4_PMAP_PLUS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  COND_CASES_TAC THENL [ALL_TAC; REFL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_IMAGE]) THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:real^3` (CONJUNCTS_THEN2 ASSUME_TAC STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `exp((A0 + &4) / sqrt(&2)) < norm(y:real^3)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    UNDISCH_TAC `~((x:A) IN IMAGE (ev_neck (ev:(A)rfs_event) i)
                     {y | &1 <= norm y /\ norm y <= exp((A0 + &4) / sqrt(&2))})` THEN
    REWRITE_TAC[] THEN REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
    EXISTS_TAC `y:real^3` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`norm(y:real^3)`; `A0 + &4`] P4_LOG_FACTS) THEN
  ANTS_TAC THENL [UNDISCH_TAC `&1 <= norm(y:real^3)` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o C MP (ASSUME `exp((A0 + &4) / sqrt(&2)) < norm(y:real^3)`) o
             CONJUNCT2 o CONJUNCT2) THEN
  DISCH_TAC THEN
  SUBST1_TAC(ASSUME `(x:A) = ev_neck ev i (y:real^3)`) THEN
  SUBGOAL_THEN `EINV i (ev_neck (ev:(A)rfs_event) i (y:real^3)) = y:real^3` SUBST1_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  AP_TERM_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let P4_PMAP_CAPVAL = prove
 (`!topX atlasX (gX:real->A->real^3^3) ts topY atlasY gY ev Y s D A0 PHI XI EINV i x.
        rfs_event_ok (topX,atlasX) gX ts (topY,atlasY) gY ev /\
        hausdorff_space topX /\
        smooth_manifold_atlas topX (atlasX:((A->bool)#(A->real^3))->bool) /\
        apx_sphere_sep topX atlasX /\
        Y IN connected_components_of topY /\
        p4_capdata (topX,atlasX) (topY,atlasY) (ev_omega ev) (ev_limit ev) (gY ts)
                   (ev_index ev) (ev_neck ev) (ev_capm ev) s D A0 PHI XI EINV /\
        i IN ev_index ev /\ ev_capm ev i (vec 0) IN Y /\
        (x IN IMAGE (ev_neck ev i) (sphere(vec 0,&1)) \/
         x IN p4_side topX (ev_neck ev i) (ev_neck ev i (&4 / &3 % basis 1)))
        ==> p4_pmap topX (Y INTER topspace topX)
              {i | i IN ev_index ev /\ ev_capm ev i (vec 0) IN Y}
              (ev_neck ev) s PHI XI EINV x IN
            IMAGE (ev_capm ev i) (cball(vec 0,&1))`,
  REPEAT GEN_TAC THEN DISCH_THEN(MAP_EVERY ASSUME_TAC o CONJUNCTS) THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [p4_capdata]) THEN
  DISCH_THEN(MAP_EVERY ASSUME_TAC o CONJUNCTS) THEN
  FIRST_X_ASSUM(MP_TAC o C MP (ASSUME `i IN ev_index (ev:(A)rfs_event)`) o SPEC `i:num`) THEN
  DISCH_THEN(MAP_EVERY ASSUME_TAC o CONJUNCTS) THEN
  MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                 `gX:real->A->real^3^3`; `ts:real`; `topY:A topology`;
                 `atlasY:((A->bool)#(A->real^3))->bool`; `gY:real->A->real^3^3`;
                 `ev:(A)rfs_event`; `Y:A->bool`; `s:real^3->bool`;
                 `PHI:num->real^3->A`; `XI:num->real^3->real^3`; `EINV:num->A->real^3`;
                 `i:num`; `x:A`] P4_PMAP_PLUS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  COND_CASES_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[]] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_IMAGE]) THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:real^3` (CONJUNCTS_THEN2 SUBST1_TAC STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `EINV i (ev_neck (ev:(A)rfs_event) i (y:real^3)) = y:real^3` SUBST1_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`norm(y:real^3)`; `A0:real`] P4_LOG_FACTS) THEN
  ANTS_TAC THENL [UNDISCH_TAC `&1 <= norm(y:real^3)` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MATCH_MP_TAC o CONJUNCT1 o CONJUNCT2) THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The pieces of the old component X0 of a retained point x0: the retained  *)
(* points Y0 = Y INTER topspace topX, the collars beyond radius 1/2 of the  *)
(* necks of Y (where p is PHI o XI o EINV), and the branches minus the      *)
(* collapse annuli (where p is the cap tip).                                 *)
(* ------------------------------------------------------------------------- *)

let P4_KSET_COMPACT = prove
 (`!R. compact {y:real^3 | &1 <= norm y /\ norm y <= R}`,
  GEN_TAC THEN
  SUBGOAL_THEN `{y:real^3 | &1 <= norm y /\ norm y <= R} = cball(vec 0,R) DIFF ball(vec 0,&1)`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_DIFF; IN_CBALL_0; IN_BALL_0; REAL_NOT_LT] THEN
    MESON_TAC[];
    MATCH_MP_TAC COMPACT_DIFF THEN REWRITE_TAC[COMPACT_CBALL; OPEN_BALL]]);;

let P4_COLLAR_OPEN = prove
 (`!s. open s ==> open {y:real^3 | y IN s /\ &1 / &2 < norm y}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `{y:real^3 | y IN s /\ &1 / &2 < norm y} =
                s INTER ((:real^3) DIFF cball(vec 0,&1 / &2))`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INTER; IN_DIFF; IN_UNIV; IN_CBALL_0;
                REAL_NOT_LE];
    MATCH_MP_TAC OPEN_INTER THEN ASM_REWRITE_TAC[GSYM closed; CLOSED_CBALL]]);;

let P4_COLLAR_CASES = prove
 (`!topX atlasX (gX:real->A->real^3^3) ts topY atlasY gY ev Y s i y.
        rfs_event_ok (topX,atlasX) gX ts (topY,atlasY) gY ev /\
        hausdorff_space topX /\
        smooth_manifold_atlas topX (atlasX:((A->bool)#(A->real^3))->bool) /\
        Y IN connected_components_of topY /\
        i IN ev_index ev /\ ev_capm ev i (vec 0) IN Y /\
        mfd_param topX atlasX s (ev_neck ev i) /\
        annulus (&1 / &2) (&2) SUBSET s /\
        connected {y | y IN s /\ &1 < norm y} /\
        y IN s /\ &1 / &2 < norm y
        ==> (norm y < &1 ==> ev_neck ev i y IN Y INTER topspace topX) /\
            (&1 <= norm y
             ==> ev_neck ev i y IN IMAGE (ev_neck ev i) (sphere(vec 0,&1)) \/
                 ev_neck ev i y IN
                 p4_side topX (ev_neck ev i) (ev_neck ev i (&4 / &3 % basis 1)))`,
  REPEAT GEN_TAC THEN DISCH_THEN(MAP_EVERY ASSUME_TAC o CONJUNCTS) THEN
  CONJ_TAC THEN DISCH_TAC THENL
   [MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                   `gX:real->A->real^3^3`; `ts:real`; `topY:A topology`;
                   `atlasY:((A->bool)#(A->real^3))->bool`; `gY:real->A->real^3^3`;
                   `ev:(A)rfs_event`; `Y:A->bool`; `i:num`] P4_CAP_IN_COMPONENT) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o CONJUNCT2 o
               C MP (ASSUME `ev_capm ev i (vec 0) IN (Y:A->bool)`) o CONJUNCT1) THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[annulus; IN_ELIM_THM] THEN ASM_REWRITE_TAC[];
    ASM_CASES_TAC `norm(y:real^3) = &1` THENL
     [DISJ1_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_SPHERE_0];
      DISJ2_TAC THEN
      MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                     `gX:real->A->real^3^3`; `ts:real`; `topY:A topology`;
                     `atlasY:((A->bool)#(A->real^3))->bool`; `gY:real->A->real^3^3`;
                     `ev:(A)rfs_event`; `i:num`; `s:real^3->bool`] P4_HALF_NECK_PLUS) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      MAP_EVERY UNDISCH_TAC [`&1 <= norm(y:real^3)`; `~(norm(y:real^3) = &1)`] THEN
      REAL_ARITH_TAC]]);;

let P4_PMAP_ON_COLLAR = prove
 (`!topX atlasX (gX:real->A->real^3^3) ts topY atlasY gY ev Y s D A0 PHI XI EINV i z.
        rfs_event_ok (topX,atlasX) gX ts (topY,atlasY) gY ev /\
        hausdorff_space topX /\
        smooth_manifold_atlas topX (atlasX:((A->bool)#(A->real^3))->bool) /\
        apx_sphere_sep topX atlasX /\
        Y IN connected_components_of topY /\
        p4_capdata (topX,atlasX) (topY,atlasY) (ev_omega ev) (ev_limit ev) (gY ts)
                   (ev_index ev) (ev_neck ev) (ev_capm ev) s D A0 PHI XI EINV /\
        connected {y | y IN s /\ &1 < norm y} /\
        i IN ev_index ev /\ ev_capm ev i (vec 0) IN Y /\
        z IN IMAGE (ev_neck ev i) {y | y IN s /\ &1 / &2 < norm y}
        ==> p4_pmap topX (Y INTER topspace topX)
              {i | i IN ev_index ev /\ ev_capm ev i (vec 0) IN Y}
              (ev_neck ev) s PHI XI EINV z = PHI i (XI i (EINV i z))`,
  REPEAT GEN_TAC THEN DISCH_THEN(MAP_EVERY ASSUME_TAC o CONJUNCTS) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_IMAGE]) THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:real^3` (CONJUNCTS_THEN2 SUBST1_TAC STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [p4_capdata]) THEN
  DISCH_THEN(MP_TAC o C MP (ASSUME `i IN ev_index (ev:(A)rfs_event)`) o SPEC `i:num` o
             last o CONJUNCTS) THEN
  DISCH_THEN(MP_TAC o el 2 o CONJUNCTS) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `(y:real^3) IN s`)]) THEN
  MATCH_MP_TAC P4_PMAP_NECK THEN
  MAP_EVERY EXISTS_TAC
   [`atlasX:((A->bool)#(A->real^3))->bool`; `gX:real->A->real^3^3`; `ts:real`;
    `topY:A topology`; `atlasY:((A->bool)#(A->real^3))->bool`;
    `gY:real->A->real^3^3`; `D:real^3->bool`; `A0:real`] THEN
  ASM_REWRITE_TAC[]);;

let P4_CAP_PIECES = prove
 (`!topX atlasX (gX:real->A->real^3^3) ts topY atlasY gY ev Y s D A0 PHI XI EINV x0.
        rfs_event_ok (topX,atlasX) gX ts (topY,atlasY) gY ev /\
        hausdorff_space topX /\
        smooth_manifold_atlas topX (atlasX:((A->bool)#(A->real^3))->bool) /\
        apx_sphere_sep topX atlasX /\
        Y IN connected_components_of topY /\
        p4_capdata (topX,atlasX) (topY,atlasY) (ev_omega ev) (ev_limit ev) (gY ts)
                   (ev_index ev) (ev_neck ev) (ev_capm ev) s D A0 PHI XI EINV /\
        connected {y | y IN s /\ &1 < norm y} /\
        x0 IN Y INTER topspace topX
        ==> connected_component_of topX x0 IN connected_components_of topX /\
            open_in topX (connected_component_of topX x0) /\
            Y INTER topspace topX SUBSET connected_component_of topX x0 /\
            (!i. i IN ev_index ev /\ ev_capm ev i (vec 0) IN Y
                 ==> open_in topX (IMAGE (ev_neck ev i) {y | y IN s /\ &1 / &2 < norm y}) /\
                     IMAGE (ev_neck ev i) {y | y IN s /\ &1 / &2 < norm y} SUBSET
                     connected_component_of topX x0 /\
                     compact_in topX (IMAGE (ev_neck ev i)
                        {y | &1 <= norm y /\ norm y <= exp((A0 + &4) / sqrt(&2))}) /\
                     IMAGE (ev_neck ev i)
                        {y | &1 <= norm y /\ norm y <= exp((A0 + &4) / sqrt(&2))} SUBSET
                     IMAGE (ev_neck ev i) {y | y IN s /\ &1 / &2 < norm y} /\
                     IMAGE (ev_neck ev i)
                        {y | &1 <= norm y /\ norm y <= exp((A0 + &4) / sqrt(&2))} SUBSET
                     ev_omega ev /\
                     open_in topX
                       (p4_side topX (ev_neck ev i) (ev_neck ev i (&4 / &3 % basis 1)) DIFF
                        IMAGE (ev_neck ev i)
                          {y | &1 <= norm y /\ norm y <= exp((A0 + &4) / sqrt(&2))}) /\
                     p4_side topX (ev_neck ev i) (ev_neck ev i (&4 / &3 % basis 1)) SUBSET
                     connected_component_of topX x0) /\
            (!x. x IN connected_component_of topX x0
                 ==> x IN Y INTER topspace topX \/
                     ?i. i IN ev_index ev /\ ev_capm ev i (vec 0) IN Y /\
                         (x IN IMAGE (ev_neck ev i)
                                 {y | &1 <= norm y /\ norm y <= exp((A0 + &4) / sqrt(&2))} \/
                          x IN p4_side topX (ev_neck ev i)
                                 (ev_neck ev i (&4 / &3 % basis 1))))`,
  REPEAT GEN_TAC THEN DISCH_THEN(MAP_EVERY ASSUME_TAC o CONJUNCTS) THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [p4_capdata]) THEN
  DISCH_THEN(MAP_EVERY ASSUME_TAC o CONJUNCTS) THEN
  MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                 `gX:real->A->real^3^3`; `ts:real`; `topY:A topology`;
                 `atlasY:((A->bool)#(A->real^3))->bool`; `gY:real->A->real^3^3`;
                 `ev:(A)rfs_event`] P4_EVENT_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(ASSUME_TAC o CONJUNCT1)] THEN
  MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                 `gX:real->A->real^3^3`; `ts:real`; `topY:A topology`;
                 `atlasY:((A->bool)#(A->real^3))->bool`; `gY:real->A->real^3^3`;
                 `ev:(A)rfs_event`; `Y:A->bool`; `x0:A`] P4_DECOMPOSITION) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC
      (ASSUME_TAC o GEN `x:A` o fst o EQ_IMP_RULE o SPEC `x:A` o
       REWRITE_RULE[EXTENSION; IN_UNION; UNIONS_GSPEC; IN_ELIM_THM])))) THEN
  SUBGOAL_THEN `&1 <= exp((A0 + &4) / sqrt(&2))` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `!c e. &0 <= c /\ &1 + c <= e ==> &1 <= e`) THEN
    EXISTS_TAC `(A0 + &4) / sqrt(&2)` THEN REWRITE_TAC[REAL_EXP_LE_X] THEN
    MATCH_MP_TAC REAL_LE_DIV THEN
    SIMP_TAC[SQRT_POS_LE; REAL_POS] THEN
    UNDISCH_TAC `&0 < A0` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    MATCH_MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`]
                        APX_COMPONENT_OPEN) THEN
    ASM_REWRITE_TAC[];
    FIRST_ASSUM ACCEPT_TAC;
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `IMAGE (ev_neck ev i) (annulus (&1 / &2) (&2)) SUBSET
      connected_component_of topX (x0:A) /\
      p4_side topX (ev_neck ev i) (ev_neck (ev:(A)rfs_event) i (&4 / &3 % basis 1)) SUBSET
      connected_component_of topX x0`
    STRIP_ASSUME_TAC THENL
     [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o C MP (ASSUME `i IN ev_index (ev:(A)rfs_event)`) o SPEC `i:num`) THEN
    DISCH_THEN(STRIP_ASSUME_TAC o el 0 o CONJUNCTS) THEN
    FIRST_ASSUM(MP_TAC o C MP (ASSUME `i IN ev_index (ev:(A)rfs_event)`) o SPEC `i:num`) THEN
    DISCH_THEN(ASSUME_TAC o el 1 o CONJUNCTS) THEN
    SUBGOAL_THEN
     `compact_in topX (IMAGE (ev_neck ev i)
        {y | &1 <= norm y /\ norm y <= exp((A0 + &4) / sqrt(&2))}:A->bool)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC MFD_PARAM_COMPACT_IMAGE THEN
      MAP_EVERY EXISTS_TAC [`atlasX:((A->bool)#(A->real^3))->bool`; `s:real^3->bool`] THEN
      ASM_REWRITE_TAC[P4_KSET_COMPACT];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `{y:real^3 | &1 <= norm y /\ norm y <= exp((A0 + &4) / sqrt(&2))} SUBSET
      {y | y IN s /\ &1 / &2 < norm y}`
    ASSUME_TAC THENL
     [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
      CONJ_TAC THENL
       [UNDISCH_TAC `{y:real^3 | &1 <= norm y /\ norm y <= exp((A0 + &4) / sqrt(&2))}
                     SUBSET s` THEN
        REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN DISCH_THEN MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[];
        UNDISCH_TAC `&1 <= norm(y:real^3)` THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MFD_PARAM_IMAGE_OPEN THEN
      MAP_EVERY EXISTS_TAC [`atlasX:((A->bool)#(A->real^3))->bool`; `s:real^3->bool`] THEN
      ASM_SIMP_TAC[P4_COLLAR_OPEN; SUBSET; IN_ELIM_THM];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
      X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                     `gX:real->A->real^3^3`; `ts:real`; `topY:A topology`;
                     `atlasY:((A->bool)#(A->real^3))->bool`; `gY:real->A->real^3^3`;
                     `ev:(A)rfs_event`; `Y:A->bool`; `s:real^3->bool`; `i:num`; `y:real^3`]
             P4_COLLAR_CASES) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      ASM_CASES_TAC `norm(y:real^3) < &1` THENL
       [DISCH_THEN(MP_TAC o C MP (ASSUME `norm(y:real^3) < &1`) o CONJUNCT1) THEN
        UNDISCH_TAC `Y INTER topspace topX SUBSET connected_component_of topX (x0:A)` THEN
        SET_TAC[];
        DISCH_THEN(MP_TAC o C MP (UNDISCH(REAL_ARITH
          `~(norm(y:real^3) < &1) ==> &1 <= norm y`)) o CONJUNCT2) THEN
        SUBGOAL_THEN `sphere(vec 0:real^3,&1) SUBSET annulus (&1 / &2) (&2)` MP_TAC THENL
         [REWRITE_TAC[SUBSET; IN_SPHERE_0; annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC;
          ALL_TAC] THEN
        MAP_EVERY UNDISCH_TAC
         [`IMAGE (ev_neck ev i) (annulus (&1 / &2) (&2)) SUBSET
           connected_component_of topX (x0:A)`;
          `p4_side topX (ev_neck ev i) (ev_neck (ev:(A)rfs_event) i (&4 / &3 % basis 1))
           SUBSET connected_component_of topX x0`] THEN
        SET_TAC[]];
      FIRST_ASSUM ACCEPT_TAC;
      MATCH_MP_TAC IMAGE_SUBSET THEN FIRST_ASSUM ACCEPT_TAC;
      MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                     `ev_omega (ev:(A)rfs_event)`; `s:real^3->bool`;
                     `ev_neck (ev:(A)rfs_event) i`] APX_PARAM_FROM_RESTRICT) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(MP_TAC o CONJUNCT2)] THEN
      UNDISCH_TAC `{y:real^3 | &1 <= norm y /\ norm y <= exp((A0 + &4) / sqrt(&2))}
                   SUBSET s` THEN
      SET_TAC[];
      MATCH_MP_TAC OPEN_IN_DIFF THEN CONJ_TAC THENL
       [MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                       `gX:real->A->real^3^3`; `ts:real`; `topY:A topology`;
                       `atlasY:((A->bool)#(A->real^3))->bool`; `gY:real->A->real^3^3`;
                       `ev:(A)rfs_event`; `Y:A->bool`; `i:num`] P4_BRANCH_BASIC) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
        MATCH_MP_TAC COMPACT_IN_IMP_CLOSED_IN THEN ASM_REWRITE_TAC[]];
      FIRST_ASSUM ACCEPT_TAC];
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o C MP (ASSUME `(x:A) IN connected_component_of topX x0`) o
                  SPEC `x:A`) THEN
    STRIP_TAC THENL
     [DISJ1_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      DISJ2_TAC THEN EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[] THEN DISJ1_TAC THEN
      UNDISCH_TAC `(x:A) IN IMAGE (ev_neck ev i) (sphere(vec 0,&1))` THEN
      SPEC_TAC(`x:A`,`x:A`) THEN REWRITE_TAC[GSYM SUBSET] THEN
      MATCH_MP_TAC IMAGE_SUBSET THEN
      REWRITE_TAC[SUBSET; IN_SPHERE_0; IN_ELIM_THM] THEN
      GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[REAL_LE_REFL];
      DISJ2_TAC THEN EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* Continuity of the pinch map on the old component X0.                      *)
(* ------------------------------------------------------------------------- *)

let P4_RETAINED_SUBTOP = prove
 (`!topX atlasX (gX:real->A->real^3^3) ts topY atlasY gY ev Y.
        rfs_event_ok (topX,atlasX) gX ts (topY,atlasY) gY ev /\
        smooth_manifold_atlas topX (atlasX:((A->bool)#(A->real^3))->bool) /\
        Y IN connected_components_of topY
        ==> subtopology topX (Y INTER topspace topX) =
            subtopology topY (Y INTER topspace topX) /\
            open_in topY (Y INTER topspace topX)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                 `gX:real->A->real^3^3`; `ts:real`; `topY:A topology`;
                 `atlasY:((A->bool)#(A->real^3))->bool`; `gY:real->A->real^3^3`;
                 `ev:(A)rfs_event`; `Y:A->bool`] P4_RETAINED_BASIC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> MAP_EVERY (fun i -> ASSUME_TAC(el i (CONJUNCTS th))) [0;1]) THEN
  MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                 `gX:real->A->real^3^3`; `ts:real`; `topY:A topology`;
                 `atlasY:((A->bool)#(A->real^3))->bool`; `gY:real->A->real^3^3`;
                 `ev:(A)rfs_event`] P4_EVENT_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> let cs = CONJUNCTS th in
    MAP_EVERY (fun i -> ASSUME_TAC(el i cs)) [8;9;11;21;23]) THEN
  SUBGOAL_THEN
   `Y INTER topspace topX SUBSET
    topspace (ev_ztop ev) DIFF
    mfd_cut_cores (ev_index ev) (ev_capp ev) (ev_capm (ev:(A)rfs_event))`
  ASSUME_TAC THENL
   [MAP_EVERY (fun t -> MP_TAC(ASSUME t))
     [`Y INTER topspace topX SUBSET
       topspace topX DIFF mfd_cut_spheres (ev_index ev) (ev_neck (ev:(A)rfs_event))`;
      `topspace topX DIFF mfd_cut_spheres (ev_index ev) (ev_neck ev) =
       topspace (ev_ztop ev) DIFF
       mfd_cut_cores (ev_index ev) (ev_capp ev) (ev_capm (ev:(A)rfs_event))`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `subtopology topX (Y INTER topspace topX) =
    subtopology (ev_ztop ev) (Y INTER topspace (topX:A topology))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `subtopology (subtopology topX
                  (topspace topX DIFF mfd_cut_spheres (ev_index ev) (ev_neck ev)))
                  (Y INTER topspace (topX:A topology))` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[SUBTOPOLOGY_SUBTOPOLOGY] THEN AP_TERM_TAC THEN
      UNDISCH_TAC `Y INTER topspace topX SUBSET
                   topspace topX DIFF mfd_cut_spheres (ev_index ev) (ev_neck (ev:(A)rfs_event))` THEN
      SET_TAC[];
      SUBST1_TAC(ASSUME
       `subtopology topX (topspace topX DIFF mfd_cut_spheres (ev_index ev) (ev_neck ev)) =
        subtopology (ev_ztop ev) (topspace (ev_ztop ev) DIFF
          mfd_cut_cores (ev_index ev) (ev_capp ev) (ev_capm (ev:(A)rfs_event)))`) THEN
      REWRITE_TAC[SUBTOPOLOGY_SUBTOPOLOGY] THEN AP_TERM_TAC THEN
      UNDISCH_TAC `Y INTER topspace topX SUBSET
                   topspace (ev_ztop ev) DIFF
                   mfd_cut_cores (ev_index ev) (ev_capp ev) (ev_capm (ev:(A)rfs_event))` THEN
      SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `Y INTER topspace topX SUBSET topspace (topY:A topology)` ASSUME_TAC THENL
   [UNDISCH_TAC `(Y:A->bool) SUBSET topspace topY` THEN SET_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                 `gX:real->A->real^3^3`; `ts:real`; `topY:A topology`;
                 `atlasY:((A->bool)#(A->real^3))->bool`; `gY:real->A->real^3^3`;
                 `ev:(A)rfs_event`] P4_EVENT_SUBSPACE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT1 th]) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `open_in (ev_ztop ev) (Y:A->bool)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                   `gX:real->A->real^3^3`; `ts:real`; `topY:A topology`;
                   `atlasY:((A->bool)#(A->real^3))->bool`; `gY:real->A->real^3^3`;
                   `ev:(A)rfs_event`] P4_EVENT_SUBSPACE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `Y:A->bool` o CONJUNCT1) THEN
    MATCH_MP_TAC(TAUT `p ==> (p <=> q /\ r) ==> q`) THEN
    MATCH_MP_TAC(ISPECL [`topY:A topology`; `atlasY:((A->bool)#(A->real^3))->bool`]
                        APX_COMPONENT_OPEN) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `Y INTER topspace topX =
    Y INTER (topspace (ev_ztop ev) DIFF
             mfd_cut_cores (ev_index ev) (ev_capp ev) (ev_capm (ev:(A)rfs_event)))`
  SUBST1_TAC THENL
   [MAP_EVERY (fun t -> MP_TAC(ASSUME t))
     [`Y INTER topspace topX SUBSET
       topspace (ev_ztop ev) DIFF
       mfd_cut_cores (ev_index ev) (ev_capp ev) (ev_capm (ev:(A)rfs_event))`;
      `topspace topX DIFF mfd_cut_spheres (ev_index ev) (ev_neck ev) =
       topspace (ev_ztop ev) DIFF
       mfd_cut_cores (ev_index ev) (ev_capp ev) (ev_capm (ev:(A)rfs_event))`] THEN
    SET_TAC[];
    MATCH_MP_TAC OPEN_IN_INTER THEN ASM_REWRITE_TAC[]]);;

let P4_CAP_IMAGE_IN_Y = prove
 (`!topX atlasX (gX:real->A->real^3^3) ts topY atlasY gY ev Y i.
        rfs_event_ok (topX,atlasX) gX ts (topY,atlasY) gY ev /\
        smooth_manifold_atlas topX (atlasX:((A->bool)#(A->real^3))->bool) /\
        Y IN connected_components_of topY /\
        i IN ev_index ev /\ ev_capm ev i (vec 0) IN Y
        ==> IMAGE (ev_capm ev i) (cball(vec 0,&1)) SUBSET Y /\ Y SUBSET topspace topY`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                   `gX:real->A->real^3^3`; `ts:real`; `topY:A topology`;
                   `atlasY:((A->bool)#(A->real^3))->bool`; `gY:real->A->real^3^3`;
                   `ev:(A)rfs_event`; `Y:A->bool`; `i:num`] P4_CAP_IN_COMPONENT) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1 o
               C MP (ASSUME `ev_capm ev i (vec 0) IN (Y:A->bool)`) o CONJUNCT1) THEN
    MATCH_MP_TAC(SET_RULE `(t:real^3->bool) SUBSET u
                          ==> IMAGE (f:real^3->A) u SUBSET Y ==> IMAGE f t SUBSET Y`) THEN
    REWRITE_TAC[SUBSET; IN_CBALL_0; IN_BALL_0] THEN REAL_ARITH_TAC;
    ASM_MESON_TAC[CONNECTED_COMPONENTS_OF_SUBSET]]);;

let P4_PMAP_IN_Y = prove
 (`!topX atlasX (gX:real->A->real^3^3) ts topY atlasY gY ev Y s D A0 PHI XI EINV x0 x.
        rfs_event_ok (topX,atlasX) gX ts (topY,atlasY) gY ev /\
        hausdorff_space topX /\
        smooth_manifold_atlas topX (atlasX:((A->bool)#(A->real^3))->bool) /\
        apx_sphere_sep topX atlasX /\
        Y IN connected_components_of topY /\
        p4_capdata (topX,atlasX) (topY,atlasY) (ev_omega ev) (ev_limit ev) (gY ts)
                   (ev_index ev) (ev_neck ev) (ev_capm ev) s D A0 PHI XI EINV /\
        x0 IN Y INTER topspace topX /\ x IN connected_component_of topX x0
        ==> p4_pmap topX (Y INTER topspace topX)
              {i | i IN ev_index ev /\ ev_capm ev i (vec 0) IN Y}
              (ev_neck ev) s PHI XI EINV x IN Y`,
  REPEAT GEN_TAC THEN DISCH_THEN(MAP_EVERY ASSUME_TAC o CONJUNCTS) THEN
  MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                 `gX:real->A->real^3^3`; `ts:real`; `topY:A topology`;
                 `atlasY:((A->bool)#(A->real^3))->bool`; `gY:real->A->real^3^3`;
                 `ev:(A)rfs_event`; `Y:A->bool`; `x0:A`] P4_DECOMPOSITION) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o C MP (ASSUME `(x:A) IN connected_component_of topX x0`) o
    fst o EQ_IMP_RULE o SPEC `x:A` o
    REWRITE_RULE[EXTENSION; IN_UNION; UNIONS_GSPEC; IN_ELIM_THM] o last o CONJUNCTS) THEN
  STRIP_TAC THENL
   [ASM_SIMP_TAC[P4_PMAP_RETAINED] THEN
    UNDISCH_TAC `(x:A) IN Y INTER topspace topX` THEN SET_TAC[];
    ALL_TAC;
    ALL_TAC] THEN
  (MATCH_MP_TAC(SET_RULE `!a:A s t. a IN s /\ s SUBSET t ==> a IN t`) THEN
   EXISTS_TAC `IMAGE (ev_capm ev i) (cball(vec 0,&1)):A->bool` THEN CONJ_TAC THENL
    [MATCH_MP_TAC P4_PMAP_CAPVAL THEN
     MAP_EVERY EXISTS_TAC
      [`atlasX:((A->bool)#(A->real^3))->bool`; `gX:real->A->real^3^3`; `ts:real`;
       `topY:A topology`; `atlasY:((A->bool)#(A->real^3))->bool`;
       `gY:real->A->real^3^3`; `D:real^3->bool`; `A0:real`] THEN
     ASM_REWRITE_TAC[];
     MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                    `gX:real->A->real^3^3`; `ts:real`; `topY:A topology`;
                    `atlasY:((A->bool)#(A->real^3))->bool`; `gY:real->A->real^3^3`;
                    `ev:(A)rfs_event`; `Y:A->bool`; `i:num`] P4_CAP_IMAGE_IN_Y) THEN
     ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]]]));;

let P4_CAP_COVER3 = prove
 (`!topX atlasX (gX:real->A->real^3^3) ts topY atlasY gY ev Y s D A0 PHI XI EINV x0 x.
        rfs_event_ok (topX,atlasX) gX ts (topY,atlasY) gY ev /\
        hausdorff_space topX /\
        smooth_manifold_atlas topX (atlasX:((A->bool)#(A->real^3))->bool) /\
        apx_sphere_sep topX atlasX /\
        Y IN connected_components_of topY /\
        p4_capdata (topX,atlasX) (topY,atlasY) (ev_omega ev) (ev_limit ev) (gY ts)
                   (ev_index ev) (ev_neck ev) (ev_capm ev) s D A0 PHI XI EINV /\
        connected {y | y IN s /\ &1 < norm y} /\
        x0 IN Y INTER topspace topX /\ x IN connected_component_of topX x0
        ==> x IN Y INTER topspace topX \/
            (?i. (i IN ev_index ev /\ ev_capm ev i (vec 0) IN Y) /\
                 x IN IMAGE (ev_neck ev i)
                        {y | &1 <= norm y /\ norm y <= exp((A0 + &4) / sqrt(&2))}) \/
            (?i. (i IN ev_index ev /\ ev_capm ev i (vec 0) IN Y) /\
                 x IN p4_side topX (ev_neck ev i) (ev_neck ev i (&4 / &3 % basis 1)) DIFF
                      IMAGE (ev_neck ev i)
                        {y | &1 <= norm y /\ norm y <= exp((A0 + &4) / sqrt(&2))})`,
  REPEAT GEN_TAC THEN DISCH_THEN(MAP_EVERY ASSUME_TAC o CONJUNCTS) THEN
  MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                 `gX:real->A->real^3^3`; `ts:real`; `topY:A topology`;
                 `atlasY:((A->bool)#(A->real^3))->bool`; `gY:real->A->real^3^3`;
                 `ev:(A)rfs_event`; `Y:A->bool`; `s:real^3->bool`; `D:real^3->bool`;
                 `A0:real`; `PHI:num->real^3->A`; `XI:num->real^3->real^3`;
                 `EINV:num->A->real^3`; `x0:A`] P4_CAP_PIECES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o C MP (ASSUME `(x:A) IN connected_component_of topX x0`) o
             SPEC `x:A` o last o CONJUNCTS) THEN
  REWRITE_TAC[IN_DIFF] THEN MESON_TAC[]);;

let P4_PMAP_CONT_RETAINED = prove
 (`!topX atlasX (gX:real->A->real^3^3) ts topY atlasY gY ev Y IY s PHI XI EINV.
        rfs_event_ok (topX,atlasX) gX ts (topY,atlasY) gY ev /\
        smooth_manifold_atlas topX (atlasX:((A->bool)#(A->real^3))->bool) /\
        Y IN connected_components_of topY
        ==> continuous_map (subtopology topX (Y INTER topspace topX),topY)
              (p4_pmap topX (Y INTER topspace topX) IY (ev_neck ev) s PHI XI EINV)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC CONTINUOUS_MAP_EQ THEN EXISTS_TAC `\x:A. x` THEN CONJ_TAC THENL
   [REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN SIMP_TAC[P4_PMAP_RETAINED; IN_INTER];
    MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                   `gX:real->A->real^3^3`; `ts:real`; `topY:A topology`;
                   `atlasY:((A->bool)#(A->real^3))->bool`; `gY:real->A->real^3^3`;
                   `ev:(A)rfs_event`; `Y:A->bool`] P4_RETAINED_SUBTOP) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN
    MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY THEN REWRITE_TAC[CONTINUOUS_MAP_ID]]);;

let P4_PMAP_CONT_COLLAR = prove
 (`!topX atlasX (gX:real->A->real^3^3) ts topY atlasY gY ev Y s D A0 PHI XI EINV i.
        rfs_event_ok (topX,atlasX) gX ts (topY,atlasY) gY ev /\
        hausdorff_space topX /\
        smooth_manifold_atlas topX (atlasX:((A->bool)#(A->real^3))->bool) /\
        apx_sphere_sep topX atlasX /\
        Y IN connected_components_of topY /\
        p4_capdata (topX,atlasX) (topY,atlasY) (ev_omega ev) (ev_limit ev) (gY ts)
                   (ev_index ev) (ev_neck ev) (ev_capm ev) s D A0 PHI XI EINV /\
        connected {y | y IN s /\ &1 < norm y} /\
        i IN ev_index ev /\ ev_capm ev i (vec 0) IN Y
        ==> continuous_map
              (subtopology topX (IMAGE (ev_neck ev i) {y | y IN s /\ &1 / &2 < norm y}),topY)
              (p4_pmap topX (Y INTER topspace topX)
                 {i | i IN ev_index ev /\ ev_capm ev i (vec 0) IN Y}
                 (ev_neck ev) s PHI XI EINV)`,
  REPEAT GEN_TAC THEN DISCH_THEN(MAP_EVERY ASSUME_TAC o CONJUNCTS) THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [p4_capdata]) THEN
  DISCH_THEN(MAP_EVERY ASSUME_TAC o CONJUNCTS) THEN
  FIRST_X_ASSUM(MP_TAC o C MP (ASSUME `i IN ev_index (ev:(A)rfs_event)`) o SPEC `i:num`) THEN
  DISCH_THEN(MAP_EVERY ASSUME_TAC o CONJUNCTS) THEN
  MATCH_MP_TAC CONTINUOUS_MAP_EQ THEN
  EXISTS_TAC `(PHI:num->real^3->A) i o (XI:num->real^3->real^3) i o (EINV:num->A->real^3) i` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER; o_THM] THEN
    X_GEN_TAC `z:A` THEN STRIP_TAC THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC P4_PMAP_ON_COLLAR THEN
    MAP_EVERY EXISTS_TAC
     [`atlasX:((A->bool)#(A->real^3))->bool`; `gX:real->A->real^3^3`; `ts:real`;
      `topY:A topology`; `atlasY:((A->bool)#(A->real^3))->bool`;
      `gY:real->A->real^3^3`; `D:real^3->bool`; `A0:real`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
  EXISTS_TAC `subtopology euclidean (D:real^3->bool)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
    EXISTS_TAC `subtopology euclidean (s:real^3->bool)` THEN CONJ_TAC THENL
     [REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN CONJ_TAC THENL
       [MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                       `s:real^3->bool`; `ev_neck (ev:(A)rfs_event) i`] MFD_PARAM_MAPS) THEN
        ASM_REWRITE_TAC[] THEN
        DISCH_THEN(X_CHOOSE_THEN `e':A->real^3` STRIP_ASSUME_TAC) THEN
        MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY_MONO THEN
        EXISTS_TAC `IMAGE (ev_neck (ev:(A)rfs_event) i) s` THEN CONJ_TAC THENL
         [MATCH_MP_TAC CONTINUOUS_MAP_EQ THEN EXISTS_TAC `e':A->real^3` THEN
          ASM_REWRITE_TAC[] THEN
          REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER; IN_IMAGE] THEN
          X_GEN_TAC `x:A` THEN
          DISCH_THEN(X_CHOOSE_THEN `z:real^3` (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC) o
                     CONJUNCT2) THEN
          ASM_SIMP_TAC[];
          MATCH_MP_TAC IMAGE_SUBSET THEN SET_TAC[]];
        REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; SUBSET; FORALL_IN_IMAGE; IN_INTER; IN_IMAGE;
                    IN_ELIM_THM] THEN
        X_GEN_TAC `x:A` THEN
        DISCH_THEN(X_CHOOSE_THEN `z:real^3` (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC) o
                   CONJUNCT2) THEN
        ASM_SIMP_TAC[]];
      REWRITE_TAC[CONTINUOUS_MAP_EUCLIDEAN2] THEN CONJ_TAC THENL
       [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM_SIMP_TAC[]]];
    MP_TAC(ISPECL [`topY:A topology`; `atlasY:((A->bool)#(A->real^3))->bool`;
                   `D:real^3->bool`; `(PHI:num->real^3->A) i`] MFD_PARAM_MAPS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[]]);;

let P4_PMAP_CONT_TIP = prove
 (`!topX atlasX (gX:real->A->real^3^3) ts topY atlasY gY ev Y s D A0 PHI XI EINV i.
        rfs_event_ok (topX,atlasX) gX ts (topY,atlasY) gY ev /\
        hausdorff_space topX /\
        smooth_manifold_atlas topX (atlasX:((A->bool)#(A->real^3))->bool) /\
        apx_sphere_sep topX atlasX /\
        Y IN connected_components_of topY /\
        p4_capdata (topX,atlasX) (topY,atlasY) (ev_omega ev) (ev_limit ev) (gY ts)
                   (ev_index ev) (ev_neck ev) (ev_capm ev) s D A0 PHI XI EINV /\
        i IN ev_index ev /\ ev_capm ev i (vec 0) IN Y
        ==> continuous_map
              (subtopology topX
                 (p4_side topX (ev_neck ev i) (ev_neck ev i (&4 / &3 % basis 1)) DIFF
                  IMAGE (ev_neck ev i)
                    {y | &1 <= norm y /\ norm y <= exp((A0 + &4) / sqrt(&2))}),topY)
              (p4_pmap topX (Y INTER topspace topX)
                 {i | i IN ev_index ev /\ ev_capm ev i (vec 0) IN Y}
                 (ev_neck ev) s PHI XI EINV)`,
  REPEAT GEN_TAC THEN DISCH_THEN(MAP_EVERY ASSUME_TAC o CONJUNCTS) THEN
  MATCH_MP_TAC CONTINUOUS_MAP_EQ THEN
  EXISTS_TAC `\x:A. (PHI:num->real^3->A) i (vec 0)` THEN CONJ_TAC THENL
   [REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER; IN_DIFF] THEN
    X_GEN_TAC `x:A` THEN STRIP_TAC THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC P4_PMAP_TIP THEN
    MAP_EVERY EXISTS_TAC
     [`atlasX:((A->bool)#(A->real^3))->bool`; `gX:real->A->real^3^3`; `ts:real`;
      `topY:A topology`; `atlasY:((A->bool)#(A->real^3))->bool`;
      `gY:real->A->real^3^3`; `D:real^3->bool`; `A0:real`] THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[CONTINUOUS_MAP_CONST] THEN DISJ2_TAC THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [p4_capdata]) THEN
    DISCH_THEN(MP_TAC o C MP (ASSUME `i IN ev_index (ev:(A)rfs_event)`) o SPEC `i:num` o
               last o CONJUNCTS) THEN
    DISCH_THEN(MP_TAC o el 9 o CONJUNCTS) THEN
    MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                   `gX:real->A->real^3^3`; `ts:real`; `topY:A topology`;
                   `atlasY:((A->bool)#(A->real^3))->bool`; `gY:real->A->real^3^3`;
                   `ev:(A)rfs_event`; `Y:A->bool`; `i:num`] P4_CAP_IMAGE_IN_Y) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SET_TAC[]]]);;

(* The pinch map is continuous from the old component X0 into Y. *)

let P4_PMAP_CONTINUOUS = prove
 (`!topX atlasX (gX:real->A->real^3^3) ts topY atlasY gY ev Y s D A0 PHI XI EINV x0.
        rfs_event_ok (topX,atlasX) gX ts (topY,atlasY) gY ev /\
        hausdorff_space topX /\
        smooth_manifold_atlas topX (atlasX:((A->bool)#(A->real^3))->bool) /\
        apx_sphere_sep topX atlasX /\
        Y IN connected_components_of topY /\
        p4_capdata (topX,atlasX) (topY,atlasY) (ev_omega ev) (ev_limit ev) (gY ts)
                   (ev_index ev) (ev_neck ev) (ev_capm ev) s D A0 PHI XI EINV /\
        connected {y | y IN s /\ &1 < norm y} /\
        x0 IN Y INTER topspace topX
        ==> continuous_map (subtopology topX (connected_component_of topX x0),
                            subtopology topY Y)
                           (p4_pmap topX (Y INTER topspace topX)
                              {i | i IN ev_index ev /\ ev_capm ev i (vec 0) IN Y}
                              (ev_neck ev) s PHI XI EINV)`,
  REPEAT GEN_TAC THEN DISCH_THEN(MAP_EVERY ASSUME_TAC o CONJUNCTS) THEN
  MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                 `gX:real->A->real^3^3`; `ts:real`; `topY:A topology`;
                 `atlasY:((A->bool)#(A->real^3))->bool`; `gY:real->A->real^3^3`;
                 `ev:(A)rfs_event`; `Y:A->bool`; `s:real^3->bool`; `D:real^3->bool`;
                 `A0:real`; `PHI:num->real^3->A`; `XI:num->real^3->real^3`;
                 `EINV:num->A->real^3`; `x0:A`] P4_CAP_PIECES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> let cs = CONJUNCTS th in
    MAP_EVERY (fun i -> ASSUME_TAC(el i cs)) [1;2;3]) THEN
  MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                 `gX:real->A->real^3^3`; `ts:real`; `topY:A topology`;
                 `atlasY:((A->bool)#(A->real^3))->bool`; `gY:real->A->real^3^3`;
                 `ev:(A)rfs_event`; `Y:A->bool`] P4_RETAINED_BASIC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(ASSUME_TAC o el 5 o CONJUNCTS)] THEN
  REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; SUBSET; FORALL_IN_IMAGE; IN_INTER] THEN
    X_GEN_TAC `x:A` THEN STRIP_TAC THEN
    MATCH_MP_TAC P4_PMAP_IN_Y THEN
    MAP_EVERY EXISTS_TAC
     [`atlasX:((A->bool)#(A->real^3))->bool`; `gX:real->A->real^3^3`; `ts:real`;
      `topY:A topology`; `atlasY:((A->bool)#(A->real^3))->bool`;
      `gY:real->A->real^3^3`; `D:real^3->bool`; `A0:real`; `x0:A`] THEN
    ASM_REWRITE_TAC[]] THEN
  MATCH_MP_TAC TOPC_CONTINUOUS_MAP_LOCAL THEN
  REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER] THEN
  X_GEN_TAC `x:A` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                 `gX:real->A->real^3^3`; `ts:real`; `topY:A topology`;
                 `atlasY:((A->bool)#(A->real^3))->bool`; `gY:real->A->real^3^3`;
                 `ev:(A)rfs_event`; `Y:A->bool`; `s:real^3->bool`; `D:real^3->bool`;
                 `A0:real`; `PHI:num->real^3->A`; `XI:num->real^3->real^3`;
                 `EINV:num->A->real^3`; `x0:A`; `x:A`] P4_CAP_COVER3) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  STRIP_TAC THENL
   [EXISTS_TAC `Y INTER topspace (topX:A topology)` THEN
    REWRITE_TAC[SUBTOPOLOGY_SUBTOPOLOGY] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_IN_SUBSET_TOPSPACE THEN ASM_REWRITE_TAC[];
      FIRST_ASSUM ACCEPT_TAC;
      SUBGOAL_THEN
       `connected_component_of topX x0 INTER (Y INTER topspace topX) =
        Y INTER topspace (topX:A topology)`
      SUBST1_TAC THENL
       [UNDISCH_TAC `Y INTER topspace topX SUBSET connected_component_of topX (x0:A)` THEN
        SET_TAC[];
        MATCH_MP_TAC P4_PMAP_CONT_RETAINED THEN
        MAP_EVERY EXISTS_TAC
         [`atlasX:((A->bool)#(A->real^3))->bool`; `gX:real->A->real^3^3`; `ts:real`;
          `atlasY:((A->bool)#(A->real^3))->bool`; `gY:real->A->real^3^3`] THEN
        ASM_REWRITE_TAC[]]];
    FIRST_X_ASSUM(MP_TAC o C MP (CONJ (ASSUME `i IN ev_index (ev:(A)rfs_event)`)
      (ASSUME `ev_capm ev i (vec 0) IN (Y:A->bool)`)) o SPEC `i:num`) THEN
    STRIP_TAC THEN
    EXISTS_TAC `IMAGE (ev_neck ev i) {y | y IN s /\ &1 / &2 < norm y}:A->bool` THEN
    REWRITE_TAC[SUBTOPOLOGY_SUBTOPOLOGY] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_IN_SUBSET_TOPSPACE THEN ASM_REWRITE_TAC[];
      MAP_EVERY UNDISCH_TAC
       [`IMAGE (ev_neck (ev:(A)rfs_event) i)
           {y | &1 <= norm y /\ norm y <= exp((A0 + &4) / sqrt(&2))} SUBSET
         IMAGE (ev_neck ev i) {y | y IN s /\ &1 / &2 < norm y}`;
        `(x:A) IN IMAGE (ev_neck (ev:(A)rfs_event) i)
           {y | &1 <= norm y /\ norm y <= exp((A0 + &4) / sqrt(&2))}`] THEN
      SET_TAC[];
      SUBGOAL_THEN
       `connected_component_of topX x0 INTER
        IMAGE (ev_neck ev i) {y | y IN s /\ &1 / &2 < norm y} =
        IMAGE (ev_neck (ev:(A)rfs_event) i) {y | y IN s /\ &1 / &2 < norm y}`
      SUBST1_TAC THENL
       [UNDISCH_TAC `IMAGE (ev_neck ev i) {y | y IN s /\ &1 / &2 < norm y} SUBSET
                     connected_component_of topX (x0:A)` THEN
        SET_TAC[];
        MATCH_MP_TAC P4_PMAP_CONT_COLLAR THEN
        MAP_EVERY EXISTS_TAC
         [`atlasX:((A->bool)#(A->real^3))->bool`; `gX:real->A->real^3^3`; `ts:real`;
          `atlasY:((A->bool)#(A->real^3))->bool`; `gY:real->A->real^3^3`;
          `D:real^3->bool`; `A0:real`] THEN
        ASM_REWRITE_TAC[]]];
    FIRST_X_ASSUM(MP_TAC o C MP (CONJ (ASSUME `i IN ev_index (ev:(A)rfs_event)`)
      (ASSUME `ev_capm ev i (vec 0) IN (Y:A->bool)`)) o SPEC `i:num`) THEN
    STRIP_TAC THEN
    EXISTS_TAC
     `p4_side topX (ev_neck ev i) (ev_neck ev i (&4 / &3 % basis 1)) DIFF
      IMAGE (ev_neck ev i)
        {y | &1 <= norm y /\ norm y <= exp((A0 + &4) / sqrt(&2))}:A->bool` THEN
    REWRITE_TAC[SUBTOPOLOGY_SUBTOPOLOGY] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_IN_SUBSET_TOPSPACE THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `p4_side topX (ev_neck ev i) (ev_neck (ev:(A)rfs_event) i (&4 / &3 % basis 1))
                   SUBSET connected_component_of topX (x0:A)` THEN
      SET_TAC[];
      FIRST_ASSUM ACCEPT_TAC;
      SUBGOAL_THEN
       `connected_component_of topX x0 INTER
        (p4_side topX (ev_neck ev i) (ev_neck ev i (&4 / &3 % basis 1)) DIFF
         IMAGE (ev_neck ev i)
           {y | &1 <= norm y /\ norm y <= exp((A0 + &4) / sqrt(&2))}) =
        p4_side topX (ev_neck ev i) (ev_neck ev i (&4 / &3 % basis 1)) DIFF
        IMAGE (ev_neck (ev:(A)rfs_event) i)
          {y | &1 <= norm y /\ norm y <= exp((A0 + &4) / sqrt(&2))}`
      SUBST1_TAC THENL
       [UNDISCH_TAC `p4_side topX (ev_neck ev i) (ev_neck (ev:(A)rfs_event) i (&4 / &3 % basis 1))
                     SUBSET connected_component_of topX (x0:A)` THEN
        SET_TAC[];
        MATCH_MP_TAC P4_PMAP_CONT_TIP THEN
        MAP_EVERY EXISTS_TAC
         [`atlasX:((A->bool)#(A->real^3))->bool`; `gX:real->A->real^3^3`; `ts:real`;
          `atlasY:((A->bool)#(A->real^3))->bool`; `gY:real->A->real^3^3`;
          `D:real^3->bool`] THEN
        ASM_REWRITE_TAC[]]]]);;

(* ------------------------------------------------------------------------- *)
(* Smoothness of the pinch map on the old component X0.                      *)
(* ------------------------------------------------------------------------- *)

let P4_MFD_SMOOTH_MAP_CONST = prove
 (`!(atlas:((A->bool)#(A->real^N))->bool) (atlas':((B->bool)#(B->real^M))->bool) W b.
        mfd_smooth_map atlas atlas' W (\x. b)`,
  REWRITE_TAC[mfd_smooth_map; o_DEF; SMOOTH_MAP_ON_CONST]);;

let P4_PARAM_INV_FACTS = prove
 (`!top atlas s (e:real^N->A) einv.
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
        mfd_param top atlas s e /\ (!z. z IN s ==> einv (e z) = z)
        ==> continuous_map (subtopology top (IMAGE e s),subtopology euclidean s) einv /\
            mfd_smooth_map atlas (open_set_atlas s) (IMAGE e s) einv`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `s:real^N->bool`; `e:real^N->A`] GRGD_PARAM_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `e':A->real^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!x. x IN IMAGE (e:real^N->A) s ==> einv x = (e':A->real^N) x`
  ASSUME_TAC THENL
   [REWRITE_TAC[FORALL_IN_IMAGE] THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_MAP_EQ THEN EXISTS_TAC `e':A->real^N` THEN
    ASM_REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER] THEN ASM_SIMP_TAC[];
    MATCH_MP_TAC MFD_SMOOTH_MAP_EQ THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `e':A->real^N`] THEN ASM_SIMP_TAC[]]);;

let P4_PARAM_COMPOSE_SMOOTH = prove
 (`!topX atlasX topY atlasY s D (e:real^3->A) einv (XI:real^3->real^3) (PHI:real^3->B) t.
        smooth_manifold_atlas topX (atlasX:((A->bool)#(A->real^3))->bool) /\
        smooth_manifold_atlas topY (atlasY:((B->bool)#(B->real^3))->bool) /\
        mfd_param topX atlasX s e /\ (!z. z IN s ==> einv (e z) = z) /\
        open D /\ mfd_param topY atlasY D PHI /\
        smooth_map_on s XI /\ (!y. y IN s ==> XI y IN D) /\
        open t /\ t SUBSET s
        ==> continuous_map (subtopology topX (IMAGE e t),topY) (PHI o XI o einv) /\
            mfd_smooth_map atlasX atlasY (IMAGE e t) (PHI o XI o einv)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                 `s:real^3->bool`; `e:real^3->A`; `einv:A->real^3`] P4_PARAM_INV_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                 `s:real^3->bool`; `e:real^3->A`] GRGD_PARAM_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `e':A->real^3` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`topY:B topology`; `atlasY:((B->bool)#(B->real^3))->bool`;
                 `D:real^3->bool`; `PHI:real^3->B`] GRGD_PARAM_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `PHI':B->real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `open_in topX (IMAGE (e:real^3->A) t)` ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_PARAM_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`atlasX:((A->bool)#(A->real^3))->bool`; `s:real^3->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (e:real^3->A) t SUBSET IMAGE e s` ASSUME_TAC THENL
   [MATCH_MP_TAC IMAGE_SUBSET THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `continuous_map (subtopology topX (IMAGE (e:real^3->A) t),
                   subtopology euclidean (s:real^3->bool)) einv`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY_MONO THEN
    EXISTS_TAC `IMAGE (e:real^3->A) s` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `continuous_map (subtopology euclidean s,subtopology euclidean D) (XI:real^3->real^3)`
  ASSUME_TAC THENL
   [REWRITE_TAC[CONTINUOUS_MAP_EUCLIDEAN2] THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS; SUBSET; FORALL_IN_IMAGE];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (einv:A->real^3) (IMAGE (e:real^3->A) t) SUBSET s` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(z:real^3) IN s` ASSUME_TAC THENL
     [UNDISCH_TAC `(t:real^3->bool) SUBSET s` THEN UNDISCH_TAC `(z:real^3) IN t` THEN
      SET_TAC[];
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `continuous_map (subtopology topX (IMAGE (e:real^3->A) t),subtopology euclidean D)
                   ((XI:real^3->real^3) o einv)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
    EXISTS_TAC `subtopology euclidean (s:real^3->bool)` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_smooth_map (open_set_atlas s) (open_set_atlas D) s (XI:real^3->real^3)`
  ASSUME_TAC THENL
   [REWRITE_TAC[MFD_SMOOTH_MAP_OPEN_SET_ATLAS] THEN
    SUBGOAL_THEN `{x:real^3 | x IN s INTER s /\ (XI:real^3->real^3) x IN D} = s` SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INTER] THEN ASM_MESON_TAC[];
      FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_smooth_map (atlasX:((A->bool)#(A->real^3))->bool) (open_set_atlas D)
                   (IMAGE (e:real^3->A) t)
                   ((XI:real^3->real^3) o einv)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                         `subtopology euclidean (s:real^3->bool)`;
                         `open_set_atlas (s:real^3->bool)`] MFD_SMOOTH_MAP_COMPOSE) THEN
    MAP_EVERY EXISTS_TAC [`subtopology euclidean (D:real^3->bool)`; `s:real^3->bool`] THEN
    ASM_SIMP_TAC[OPEN_SET_ATLAS; OPEN_IN_SUBTOPOLOGY_REFL; TOPSPACE_EUCLIDEAN;
                 SUBSET_UNIV; SUBTOPOLOGY_SUBTOPOLOGY; INTER_IDEMPOT] THEN
    MATCH_MP_TAC MFD_SMOOTH_MAP_SUBSET THEN
    EXISTS_TAC `IMAGE (e:real^3->A) s` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
    EXISTS_TAC `subtopology euclidean (D:real^3->bool)` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                         `subtopology euclidean (D:real^3->bool)`;
                         `open_set_atlas (D:real^3->bool)`] MFD_SMOOTH_MAP_COMPOSE) THEN
    MAP_EVERY EXISTS_TAC [`topY:B topology`; `D:real^3->bool`] THEN
    ASM_SIMP_TAC[OPEN_SET_ATLAS; OPEN_IN_SUBTOPOLOGY_REFL; TOPSPACE_EUCLIDEAN;
                 SUBSET_UNIV; SUBTOPOLOGY_SUBTOPOLOGY; INTER_IDEMPOT] THEN
    REWRITE_TAC[IMAGE_o] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(z:real^3) IN s` ASSUME_TAC THENL [ASM SET_TAC[]; ASM_SIMP_TAC[]]]);;

let P4_PMAP_SMOOTH_RETAINED = prove
 (`!topX atlasX (gX:real->A->real^3^3) ts topY atlasY gY ev Y IY s PHI XI EINV.
        rfs_event_ok (topX,atlasX) gX ts (topY,atlasY) gY ev /\
        smooth_manifold_atlas topX (atlasX:((A->bool)#(A->real^3))->bool) /\
        Y IN connected_components_of topY
        ==> mfd_smooth_map atlasX atlasY (Y INTER topspace topX)
              (p4_pmap topX (Y INTER topspace topX) IY (ev_neck ev) s PHI XI EINV)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC MFD_SMOOTH_MAP_EQ THEN
  MAP_EVERY EXISTS_TAC [`topX:A topology`; `\x:A. x`] THEN
  ASM_SIMP_TAC[P4_PMAP_RETAINED] THEN
  MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                 `gX:real->A->real^3^3`; `ts:real`; `topY:A topology`;
                 `atlasY:((A->bool)#(A->real^3))->bool`; `gY:real->A->real^3^3`;
                 `ev:(A)rfs_event`] P4_EVENT_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> let cs = CONJUNCTS th in
    MAP_EVERY (fun i -> ASSUME_TAC(el i cs)) [7;22]) THEN
  MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                 `gX:real->A->real^3^3`; `ts:real`; `topY:A topology`;
                 `atlasY:((A->bool)#(A->real^3))->bool`; `gY:real->A->real^3^3`;
                 `ev:(A)rfs_event`; `Y:A->bool`] P4_RETAINED_BASIC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> MAP_EVERY (fun i -> ASSUME_TAC(el i (CONJUNCTS th))) [0;1]) THEN
  SUBGOAL_THEN
   `mfd_smooth_map (atlasX:((A->bool)#(A->real^3))->bool)
                   (atlasY:((A->bool)#(A->real^3))->bool)
                   (Y INTER topspace topX) (\x:A. x) <=>
    mfd_smooth_map atlasX (ev_zatlas (ev:(A)rfs_event)) (Y INTER topspace topX) (\x:A. x)`
  SUBST1_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IMAGE_ID] THEN
    UNDISCH_TAC `(Y:A->bool) SUBSET topspace topY` THEN SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MFD_SMOOTH_MAP_SUBSET THEN
  EXISTS_TAC `topspace topX DIFF mfd_cut_spheres (ev_index ev) (ev_neck (ev:(A)rfs_event))` THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th ->
      try fst(dest_const(fst(strip_comb(concl th)))) = "mfd_cut_cap" with Failure _ -> false)) THEN
    REWRITE_TAC[mfd_cut_cap; mfd_diffeo] THEN SIMP_TAC[];
    FIRST_ASSUM ACCEPT_TAC]);;

let P4_PMAP_SMOOTH_COLLAR = prove
 (`!topX atlasX (gX:real->A->real^3^3) ts topY atlasY gY ev Y s D A0 PHI XI EINV i.
        rfs_event_ok (topX,atlasX) gX ts (topY,atlasY) gY ev /\
        hausdorff_space topX /\
        smooth_manifold_atlas topX (atlasX:((A->bool)#(A->real^3))->bool) /\
        apx_sphere_sep topX atlasX /\
        Y IN connected_components_of topY /\
        p4_capdata (topX,atlasX) (topY,atlasY) (ev_omega ev) (ev_limit ev) (gY ts)
                   (ev_index ev) (ev_neck ev) (ev_capm ev) s D A0 PHI XI EINV /\
        connected {y | y IN s /\ &1 < norm y} /\
        i IN ev_index ev /\ ev_capm ev i (vec 0) IN Y
        ==> mfd_smooth_map atlasX atlasY
              (IMAGE (ev_neck ev i) {y | y IN s /\ &1 / &2 < norm y})
              (p4_pmap topX (Y INTER topspace topX)
                 {i | i IN ev_index ev /\ ev_capm ev i (vec 0) IN Y}
                 (ev_neck ev) s PHI XI EINV)`,
  REPEAT GEN_TAC THEN DISCH_THEN(MAP_EVERY ASSUME_TAC o CONJUNCTS) THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [p4_capdata]) THEN
  DISCH_THEN(MAP_EVERY ASSUME_TAC o CONJUNCTS) THEN
  FIRST_X_ASSUM(MP_TAC o C MP (ASSUME `i IN ev_index (ev:(A)rfs_event)`) o SPEC `i:num`) THEN
  DISCH_THEN(MAP_EVERY ASSUME_TAC o CONJUNCTS) THEN
  MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                 `gX:real->A->real^3^3`; `ts:real`; `topY:A topology`;
                 `atlasY:((A->bool)#(A->real^3))->bool`; `gY:real->A->real^3^3`;
                 `ev:(A)rfs_event`] P4_EVENT_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(ASSUME_TAC o last o CONJUNCTS)] THEN
  MATCH_MP_TAC MFD_SMOOTH_MAP_EQ THEN
  MAP_EVERY EXISTS_TAC
   [`topX:A topology`;
    `(PHI:num->real^3->A) i o (XI:num->real^3->real^3) i o (EINV:num->A->real^3) i`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                   `topY:A topology`; `atlasY:((A->bool)#(A->real^3))->bool`;
                   `s:real^3->bool`; `D:real^3->bool`; `ev_neck (ev:(A)rfs_event) i`;
                   `(EINV:num->A->real^3) i`; `(XI:num->real^3->real^3) i`;
                   `(PHI:num->real^3->A) i`; `{y:real^3 | y IN s /\ &1 / &2 < norm y}`]
           P4_PARAM_COMPOSE_SMOOTH) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[P4_COLLAR_OPEN] THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[];
      SIMP_TAC[]];
    X_GEN_TAC `z:A` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN
    MATCH_MP_TAC P4_PMAP_ON_COLLAR THEN
    MAP_EVERY EXISTS_TAC
     [`atlasX:((A->bool)#(A->real^3))->bool`; `gX:real->A->real^3^3`; `ts:real`;
      `topY:A topology`; `atlasY:((A->bool)#(A->real^3))->bool`;
      `gY:real->A->real^3^3`; `D:real^3->bool`; `A0:real`] THEN
    ASM_REWRITE_TAC[]]);;

let P4_PMAP_SMOOTH_TIP = prove
 (`!topX atlasX (gX:real->A->real^3^3) ts topY atlasY gY ev Y s D A0 PHI XI EINV i.
        rfs_event_ok (topX,atlasX) gX ts (topY,atlasY) gY ev /\
        hausdorff_space topX /\
        smooth_manifold_atlas topX (atlasX:((A->bool)#(A->real^3))->bool) /\
        apx_sphere_sep topX atlasX /\
        Y IN connected_components_of topY /\
        p4_capdata (topX,atlasX) (topY,atlasY) (ev_omega ev) (ev_limit ev) (gY ts)
                   (ev_index ev) (ev_neck ev) (ev_capm ev) s D A0 PHI XI EINV /\
        i IN ev_index ev /\ ev_capm ev i (vec 0) IN Y
        ==> mfd_smooth_map atlasX atlasY
              (p4_side topX (ev_neck ev i) (ev_neck ev i (&4 / &3 % basis 1)) DIFF
               IMAGE (ev_neck ev i)
                 {y | &1 <= norm y /\ norm y <= exp((A0 + &4) / sqrt(&2))})
              (p4_pmap topX (Y INTER topspace topX)
                 {i | i IN ev_index ev /\ ev_capm ev i (vec 0) IN Y}
                 (ev_neck ev) s PHI XI EINV)`,
  REPEAT GEN_TAC THEN DISCH_THEN(MAP_EVERY ASSUME_TAC o CONJUNCTS) THEN
  MATCH_MP_TAC MFD_SMOOTH_MAP_EQ THEN
  MAP_EVERY EXISTS_TAC [`topX:A topology`; `\x:A. (PHI:num->real^3->A) i (vec 0)`] THEN
  ASM_REWRITE_TAC[P4_MFD_SMOOTH_MAP_CONST; IN_DIFF] THEN
  X_GEN_TAC `x:A` THEN STRIP_TAC THEN
  MATCH_MP_TAC P4_PMAP_TIP THEN
  MAP_EVERY EXISTS_TAC
   [`atlasX:((A->bool)#(A->real^3))->bool`; `gX:real->A->real^3^3`; `ts:real`;
    `topY:A topology`; `atlasY:((A->bool)#(A->real^3))->bool`;
    `gY:real->A->real^3^3`; `D:real^3->bool`; `A0:real`] THEN
  ASM_REWRITE_TAC[]);;

let P4_PMAP_SMOOTH = prove
 (`!topX atlasX (gX:real->A->real^3^3) ts topY atlasY gY ev Y s D A0 PHI XI EINV x0.
        rfs_event_ok (topX,atlasX) gX ts (topY,atlasY) gY ev /\
        hausdorff_space topX /\
        smooth_manifold_atlas topX (atlasX:((A->bool)#(A->real^3))->bool) /\
        apx_sphere_sep topX atlasX /\
        Y IN connected_components_of topY /\
        p4_capdata (topX,atlasX) (topY,atlasY) (ev_omega ev) (ev_limit ev) (gY ts)
                   (ev_index ev) (ev_neck ev) (ev_capm ev) s D A0 PHI XI EINV /\
        connected {y | y IN s /\ &1 < norm y} /\
        x0 IN Y INTER topspace topX
        ==> mfd_smooth_map atlasX atlasY (connected_component_of topX x0)
                           (p4_pmap topX (Y INTER topspace topX)
                              {i | i IN ev_index ev /\ ev_capm ev i (vec 0) IN Y}
                              (ev_neck ev) s PHI XI EINV)`,
  REPEAT GEN_TAC THEN DISCH_THEN(MAP_EVERY ASSUME_TAC o CONJUNCTS) THEN
  MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                 `gX:real->A->real^3^3`; `ts:real`; `topY:A topology`;
                 `atlasY:((A->bool)#(A->real^3))->bool`; `gY:real->A->real^3^3`;
                 `ev:(A)rfs_event`; `Y:A->bool`; `s:real^3->bool`; `D:real^3->bool`;
                 `A0:real`; `PHI:num->real^3->A`; `XI:num->real^3->real^3`;
                 `EINV:num->A->real^3`; `x0:A`] P4_CAP_PIECES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> let cs = CONJUNCTS th in
    MAP_EVERY (fun i -> ASSUME_TAC(el i cs)) [1;2;3]) THEN
  MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                 `gX:real->A->real^3^3`; `ts:real`; `topY:A topology`;
                 `atlasY:((A->bool)#(A->real^3))->bool`; `gY:real->A->real^3^3`;
                 `ev:(A)rfs_event`; `Y:A->bool`] P4_RETAINED_BASIC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(ASSUME_TAC o el 5 o CONJUNCTS)] THEN
  MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                 `gX:real->A->real^3^3`; `ts:real`; `topY:A topology`;
                 `atlasY:((A->bool)#(A->real^3))->bool`; `gY:real->A->real^3^3`;
                 `ev:(A)rfs_event`] P4_EVENT_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(ASSUME_TAC o last o CONJUNCTS)] THEN
  MATCH_MP_TAC P4_MFD_SMOOTH_LOCAL THEN
  MAP_EVERY EXISTS_TAC [`topX:A topology`; `topY:A topology`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                   `gX:real->A->real^3^3`; `ts:real`; `topY:A topology`;
                   `atlasY:((A->bool)#(A->real^3))->bool`; `gY:real->A->real^3^3`;
                   `ev:(A)rfs_event`; `Y:A->bool`; `s:real^3->bool`; `D:real^3->bool`;
                   `A0:real`; `PHI:num->real^3->A`; `XI:num->real^3->real^3`;
                   `EINV:num->A->real^3`; `x0:A`] P4_PMAP_CONTINUOUS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY]];
    ALL_TAC] THEN
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                 `gX:real->A->real^3^3`; `ts:real`; `topY:A topology`;
                 `atlasY:((A->bool)#(A->real^3))->bool`; `gY:real->A->real^3^3`;
                 `ev:(A)rfs_event`; `Y:A->bool`; `s:real^3->bool`; `D:real^3->bool`;
                 `A0:real`; `PHI:num->real^3->A`; `XI:num->real^3->real^3`;
                 `EINV:num->A->real^3`; `x0:A`; `x:A`] P4_CAP_COVER3) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  STRIP_TAC THENL
   [MAP_EVERY EXISTS_TAC
     [`Y INTER topspace (topX:A topology)`;
      `p4_pmap topX (Y INTER topspace topX)
         {i | i IN ev_index ev /\ ev_capm ev i (vec 0) IN Y}
         (ev_neck (ev:(A)rfs_event)) s PHI XI EINV`] THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC P4_PMAP_SMOOTH_RETAINED THEN
    MAP_EVERY EXISTS_TAC
     [`gX:real->A->real^3^3`; `ts:real`; `topY:A topology`; `gY:real->A->real^3^3`] THEN
    ASM_REWRITE_TAC[];
    FIRST_X_ASSUM(MP_TAC o C MP (CONJ (ASSUME `i IN ev_index (ev:(A)rfs_event)`)
      (ASSUME `ev_capm ev i (vec 0) IN (Y:A->bool)`)) o SPEC `i:num`) THEN
    STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC
     [`IMAGE (ev_neck ev i) {y | y IN s /\ &1 / &2 < norm y}:A->bool`;
      `p4_pmap topX (Y INTER topspace topX)
         {i | i IN ev_index ev /\ ev_capm ev i (vec 0) IN Y}
         (ev_neck (ev:(A)rfs_event)) s PHI XI EINV`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       [`IMAGE (ev_neck (ev:(A)rfs_event) i)
           {y | &1 <= norm y /\ norm y <= exp((A0 + &4) / sqrt(&2))} SUBSET
         IMAGE (ev_neck ev i) {y | y IN s /\ &1 / &2 < norm y}`;
        `(x:A) IN IMAGE (ev_neck (ev:(A)rfs_event) i)
           {y | &1 <= norm y /\ norm y <= exp((A0 + &4) / sqrt(&2))}`] THEN
      SET_TAC[];
      MATCH_MP_TAC P4_PMAP_SMOOTH_COLLAR THEN
      MAP_EVERY EXISTS_TAC
       [`gX:real->A->real^3^3`; `ts:real`; `topY:A topology`; `gY:real->A->real^3^3`;
        `D:real^3->bool`; `A0:real`] THEN
      ASM_REWRITE_TAC[]];
    FIRST_X_ASSUM(MP_TAC o C MP (CONJ (ASSUME `i IN ev_index (ev:(A)rfs_event)`)
      (ASSUME `ev_capm ev i (vec 0) IN (Y:A->bool)`)) o SPEC `i:num`) THEN
    STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC
     [`p4_side topX (ev_neck ev i) (ev_neck ev i (&4 / &3 % basis 1)) DIFF
       IMAGE (ev_neck ev i)
         {y | &1 <= norm y /\ norm y <= exp((A0 + &4) / sqrt(&2))}:A->bool`;
      `p4_pmap topX (Y INTER topspace topX)
         {i | i IN ev_index ev /\ ev_capm ev i (vec 0) IN Y}
         (ev_neck (ev:(A)rfs_event)) s PHI XI EINV`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [UNDISCH_TAC `p4_side topX (ev_neck ev i) (ev_neck (ev:(A)rfs_event) i (&4 / &3 % basis 1))
                   SUBSET connected_component_of topX (x0:A)` THEN
      SET_TAC[];
      MATCH_MP_TAC P4_PMAP_SMOOTH_TIP THEN
      MAP_EVERY EXISTS_TAC
       [`gX:real->A->real^3^3`; `ts:real`; `topY:A topology`; `gY:real->A->real^3^3`;
        `D:real^3->bool`] THEN
      ASM_REWRITE_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* The derivative bound of the pinch map.                                    *)
(* ------------------------------------------------------------------------- *)

let p4_jqf = new_definition
 `p4_jqf (atlasX:((A->bool)#(A->real^3))->bool) (atlasY:((B->bool)#(B->real^3))->bool)
         (gY:B->real^3^3) (p:A->B) (x:A) (v:real^3) =
    (jacobian (\y. SND (chart_at atlasY (p x)) (p (chart_inv (chart_at atlasX x) y)))
              (at (SND (chart_at atlasX x) x)) ** v) dot
    (gY (p x) **
     (jacobian (\y. SND (chart_at atlasY (p x)) (p (chart_inv (chart_at atlasX x) y)))
               (at (SND (chart_at atlasX x) x)) ** v))`;;

let P4_JQF_LOCAL = prove
 (`!topX atlasX topY atlasY (gY:B->real^3^3) O (f:A->B) g x v.
        smooth_manifold_atlas topX (atlasX:((A->bool)#(A->real^3))->bool) /\
        smooth_manifold_atlas topY (atlasY:((B->bool)#(B->real^3))->bool) /\
        open_in topX O /\ x IN O /\ (!z. z IN O ==> f z = g z)
        ==> p4_jqf atlasX atlasY gY f x v = p4_jqf atlasX atlasY gY g x v`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p4_jqf] THEN
  MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                 `topY:B topology`; `atlasY:((B->bool)#(B->real^3))->bool`;
                 `O:A->bool`; `f:A->B`; `g:A->B`; `x:A`] P4_PINCH_JAC_LOCAL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `(f:A->B) x = g x` (fun th -> REWRITE_TAC[th]) THEN ASM_SIMP_TAC[]);;

let P4_JQF_CONST = prove
 (`!(atlasX:((A->bool)#(A->real^3))->bool) (atlasY:((B->bool)#(B->real^3))->bool)
    (gY:B->real^3^3) (c:B) x v.
        p4_jqf atlasX atlasY gY (\z. c) x v = &0`,
  REWRITE_TAC[p4_jqf; jacobian; FRECHET_DERIVATIVE_CONST_AT; MATRIX_0;
              MATRIX_VECTOR_MUL_LZERO; DOT_LZERO]);;

let P4_JQF_RETAINED = prove
 (`!topX atlasX (gX:real->A->real^3^3) ts topY atlasY gY ev x v.
        rfs_event_ok (topX,atlasX) gX ts (topY,atlasY) gY ev /\
        smooth_manifold_atlas topX (atlasX:((A->bool)#(A->real^3))->bool) /\
        x IN topspace topY /\ x IN topspace topX
        ==> p4_jqf atlasX atlasY (gY ts) (\x. x) x v = v dot (ev_limit ev x ** v)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p4_jqf] THEN
  MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                 `gX:real->A->real^3^3`; `ts:real`; `topY:A topology`;
                 `atlasY:((A->bool)#(A->real^3))->bool`; `gY:real->A->real^3^3`;
                 `ev:(A)rfs_event`] P4_EVENT_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> let cs = CONJUNCTS th in
    MAP_EVERY (fun i -> ASSUME_TAC(el i cs)) [2;23]) THEN
  MATCH_MP_TAC P4_RETAINED_QF THEN
  MAP_EVERY EXISTS_TAC
   [`topX:A topology`; `topY:A topology`;
    `topspace topY INTER topspace (topX:A topology)`] THEN
  ASM_REWRITE_TAC[IN_INTER; ETA_AX]);;

let P4_JQF_COLLAR = prove
 (`!topX atlasX (gX:real->A->real^3^3) ts topY atlasY gY ev s D A0 PHI XI EINV i y v.
        rfs_event_ok (topX,atlasX) gX ts (topY,atlasY) gY ev /\
        smooth_manifold_atlas topX (atlasX:((A->bool)#(A->real^3))->bool) /\
        p4_capdata (topX,atlasX) (topY,atlasY) (ev_omega ev) (ev_limit ev) (gY ts)
                   (ev_index ev) (ev_neck ev) (ev_capm ev) s D A0 PHI XI EINV /\
        i IN ev_index ev /\ y IN s
        ==> p4_jqf atlasX atlasY (gY ts)
                   (\z. (PHI:num->real^3->A) i ((XI:num->real^3->real^3) i
                          ((EINV:num->A->real^3) i z)))
                   (ev_neck ev i y) v <=
            v dot (ev_limit ev (ev_neck ev i y) ** v)`,
  REPEAT GEN_TAC THEN DISCH_THEN(MAP_EVERY ASSUME_TAC o CONJUNCTS) THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [p4_capdata]) THEN
  DISCH_THEN(MAP_EVERY ASSUME_TAC o CONJUNCTS) THEN
  FIRST_X_ASSUM(MP_TAC o C MP (ASSUME `i IN ev_index (ev:(A)rfs_event)`) o SPEC `i:num`) THEN
  DISCH_THEN(MAP_EVERY ASSUME_TAC o CONJUNCTS) THEN
  MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                 `gX:real->A->real^3^3`; `ts:real`; `topY:A topology`;
                 `atlasY:((A->bool)#(A->real^3))->bool`; `gY:real->A->real^3^3`;
                 `ev:(A)rfs_event`] P4_EVENT_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> let cs = CONJUNCTS th in
    MAP_EVERY (fun i -> ASSUME_TAC(el i cs)) [0;23]) THEN
  REWRITE_TAC[p4_jqf] THEN
  MATCH_MP_TAC P4_NECK_QF THEN
  MAP_EVERY EXISTS_TAC
   [`topX:A topology`; `topY:A topology`; `ev_omega (ev:(A)rfs_event)`;
    `s:real^3->bool`; `D:real^3->bool`] THEN
  ASM_SIMP_TAC[]);;

let P4_PMAP_JQF_RETAINED = prove
 (`!topX atlasX (gX:real->A->real^3^3) ts topY atlasY gY ev Y IY s PHI XI EINV x v.
        rfs_event_ok (topX,atlasX) gX ts (topY,atlasY) gY ev /\
        smooth_manifold_atlas topX (atlasX:((A->bool)#(A->real^3))->bool) /\
        Y IN connected_components_of topY /\ x IN Y INTER topspace topX
        ==> p4_jqf atlasX atlasY (gY ts)
              (p4_pmap topX (Y INTER topspace topX) IY (ev_neck ev) s PHI XI EINV) x v =
            v dot (ev_limit ev x ** v)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                 `gX:real->A->real^3^3`; `ts:real`; `topY:A topology`;
                 `atlasY:((A->bool)#(A->real^3))->bool`; `gY:real->A->real^3^3`;
                 `ev:(A)rfs_event`] P4_EVENT_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(ASSUME_TAC o last o CONJUNCTS)] THEN
  MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                 `gX:real->A->real^3^3`; `ts:real`; `topY:A topology`;
                 `atlasY:((A->bool)#(A->real^3))->bool`; `gY:real->A->real^3^3`;
                 `ev:(A)rfs_event`; `Y:A->bool`] P4_RETAINED_BASIC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> MAP_EVERY (fun i -> ASSUME_TAC(el i (CONJUNCTS th))) [0;5]) THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `p4_jqf (atlasX:((A->bool)#(A->real^3))->bool)
                     (atlasY:((A->bool)#(A->real^3))->bool)
                     ((gY:real->A->real^3^3) ts) (\x:A. x) x v` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC P4_JQF_LOCAL THEN
    MAP_EVERY EXISTS_TAC
     [`topX:A topology`; `topY:A topology`; `Y INTER topspace (topX:A topology)`] THEN
    ASM_SIMP_TAC[P4_PMAP_RETAINED];
    MATCH_MP_TAC P4_JQF_RETAINED THEN
    MAP_EVERY EXISTS_TAC [`topX:A topology`; `gX:real->A->real^3^3`; `topY:A topology`] THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC [`(x:A) IN Y INTER topspace topX`; `(Y:A->bool) SUBSET topspace topY`] THEN
    SET_TAC[]]);;

let P4_PMAP_JQF_COLLAR = prove
 (`!topX atlasX (gX:real->A->real^3^3) ts topY atlasY gY ev Y s D A0 PHI XI EINV i x v.
        rfs_event_ok (topX,atlasX) gX ts (topY,atlasY) gY ev /\
        hausdorff_space topX /\
        smooth_manifold_atlas topX (atlasX:((A->bool)#(A->real^3))->bool) /\
        apx_sphere_sep topX atlasX /\
        Y IN connected_components_of topY /\
        p4_capdata (topX,atlasX) (topY,atlasY) (ev_omega ev) (ev_limit ev) (gY ts)
                   (ev_index ev) (ev_neck ev) (ev_capm ev) s D A0 PHI XI EINV /\
        connected {y | y IN s /\ &1 < norm y} /\
        i IN ev_index ev /\ ev_capm ev i (vec 0) IN Y /\
        x IN IMAGE (ev_neck ev i) {y | y IN s /\ &1 / &2 < norm y}
        ==> p4_jqf atlasX atlasY (gY ts)
              (p4_pmap topX (Y INTER topspace topX)
                 {i | i IN ev_index ev /\ ev_capm ev i (vec 0) IN Y}
                 (ev_neck ev) s PHI XI EINV) x v <=
            v dot (ev_limit ev x ** v)`,
  REPEAT GEN_TAC THEN DISCH_THEN(MAP_EVERY ASSUME_TAC o CONJUNCTS) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_IMAGE]) THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:real^3` (CONJUNCTS_THEN2 SUBST1_TAC STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [p4_capdata]) THEN
  DISCH_THEN(MP_TAC o C MP (ASSUME `i IN ev_index (ev:(A)rfs_event)`) o SPEC `i:num` o
             last o CONJUNCTS) THEN
  DISCH_THEN(ASSUME_TAC o el 0 o CONJUNCTS) THEN
  FIRST_ASSUM(ASSUME_TAC o el 0 o CONJUNCTS o GEN_REWRITE_RULE I [p4_capdata]) THEN
  MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                 `gX:real->A->real^3^3`; `ts:real`; `topY:A topology`;
                 `atlasY:((A->bool)#(A->real^3))->bool`; `gY:real->A->real^3^3`;
                 `ev:(A)rfs_event`] P4_EVENT_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(ASSUME_TAC o last o CONJUNCTS)] THEN
  MATCH_MP_TAC(REAL_ARITH `!a b c:real. a = b /\ b <= c ==> a <= c`) THEN
  EXISTS_TAC
   `p4_jqf (atlasX:((A->bool)#(A->real^3))->bool) (atlasY:((A->bool)#(A->real^3))->bool)
           ((gY:real->A->real^3^3) ts)
           (\z. (PHI:num->real^3->A) i ((XI:num->real^3->real^3) i
                  ((EINV:num->A->real^3) i z)))
           (ev_neck ev i (y:real^3)) v` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC P4_JQF_LOCAL THEN
    MAP_EVERY EXISTS_TAC
     [`topX:A topology`; `topY:A topology`;
      `IMAGE (ev_neck (ev:(A)rfs_event) i) {y | y IN s /\ &1 / &2 < norm y}`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MFD_PARAM_IMAGE_OPEN THEN
      MAP_EVERY EXISTS_TAC [`atlasX:((A->bool)#(A->real^3))->bool`; `s:real^3->bool`] THEN
      ASM_SIMP_TAC[P4_COLLAR_OPEN; SUBSET; IN_ELIM_THM];
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_ELIM_THM];
      X_GEN_TAC `z:A` THEN DISCH_TAC THEN
      MATCH_MP_TAC P4_PMAP_ON_COLLAR THEN
      MAP_EVERY EXISTS_TAC
       [`atlasX:((A->bool)#(A->real^3))->bool`; `gX:real->A->real^3^3`; `ts:real`;
        `topY:A topology`; `atlasY:((A->bool)#(A->real^3))->bool`;
        `gY:real->A->real^3^3`; `D:real^3->bool`; `A0:real`] THEN
      ASM_REWRITE_TAC[]];
    MATCH_MP_TAC P4_JQF_COLLAR THEN
    MAP_EVERY EXISTS_TAC
     [`topX:A topology`; `gX:real->A->real^3^3`; `topY:A topology`;
      `s:real^3->bool`; `D:real^3->bool`; `A0:real`] THEN
    ASM_REWRITE_TAC[]]);;

let P4_PMAP_JQF_TIP = prove
 (`!topX atlasX (gX:real->A->real^3^3) ts topY atlasY gY ev Y s D A0 PHI XI EINV i x v.
        rfs_event_ok (topX,atlasX) gX ts (topY,atlasY) gY ev /\
        hausdorff_space topX /\
        smooth_manifold_atlas topX (atlasX:((A->bool)#(A->real^3))->bool) /\
        apx_sphere_sep topX atlasX /\
        Y IN connected_components_of topY /\
        p4_capdata (topX,atlasX) (topY,atlasY) (ev_omega ev) (ev_limit ev) (gY ts)
                   (ev_index ev) (ev_neck ev) (ev_capm ev) s D A0 PHI XI EINV /\
        i IN ev_index ev /\ ev_capm ev i (vec 0) IN Y /\
        x IN p4_side topX (ev_neck ev i) (ev_neck ev i (&4 / &3 % basis 1)) DIFF
             IMAGE (ev_neck ev i)
               {y | &1 <= norm y /\ norm y <= exp((A0 + &4) / sqrt(&2))}
        ==> p4_jqf atlasX atlasY (gY ts)
              (p4_pmap topX (Y INTER topspace topX)
                 {i | i IN ev_index ev /\ ev_capm ev i (vec 0) IN Y}
                 (ev_neck ev) s PHI XI EINV) x v = &0`,
  REPEAT GEN_TAC THEN DISCH_THEN(MAP_EVERY ASSUME_TAC o CONJUNCTS) THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [p4_capdata]) THEN
  DISCH_THEN(MAP_EVERY ASSUME_TAC o CONJUNCTS) THEN
  FIRST_X_ASSUM(MP_TAC o C MP (ASSUME `i IN ev_index (ev:(A)rfs_event)`) o SPEC `i:num`) THEN
  DISCH_THEN(ASSUME_TAC o el 0 o CONJUNCTS) THEN
  MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                 `gX:real->A->real^3^3`; `ts:real`; `topY:A topology`;
                 `atlasY:((A->bool)#(A->real^3))->bool`; `gY:real->A->real^3^3`;
                 `ev:(A)rfs_event`] P4_EVENT_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(ASSUME_TAC o last o CONJUNCTS)] THEN
  SUBGOAL_THEN
   `open_in topX
      (p4_side topX (ev_neck ev i) (ev_neck ev i (&4 / &3 % basis 1)) DIFF
       IMAGE (ev_neck (ev:(A)rfs_event) i)
         {y | &1 <= norm y /\ norm y <= exp((A0 + &4) / sqrt(&2))})`
  ASSUME_TAC THENL
   [MATCH_MP_TAC OPEN_IN_DIFF THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                     `gX:real->A->real^3^3`; `ts:real`; `topY:A topology`;
                     `atlasY:((A->bool)#(A->real^3))->bool`; `gY:real->A->real^3^3`;
                     `ev:(A)rfs_event`; `Y:A->bool`; `i:num`] P4_BRANCH_BASIC) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
      MATCH_MP_TAC COMPACT_IN_IMP_CLOSED_IN THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC MFD_PARAM_COMPACT_IMAGE THEN
      MAP_EVERY EXISTS_TAC [`atlasX:((A->bool)#(A->real^3))->bool`; `s:real^3->bool`] THEN
      ASM_REWRITE_TAC[P4_KSET_COMPACT]];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `p4_jqf (atlasX:((A->bool)#(A->real^3))->bool) (atlasY:((A->bool)#(A->real^3))->bool)
           ((gY:real->A->real^3^3) ts) (\z:A. (PHI:num->real^3->A) i (vec 0)) x v` THEN
  CONJ_TAC THENL [ALL_TAC; REWRITE_TAC[P4_JQF_CONST]] THEN
  MATCH_MP_TAC P4_JQF_LOCAL THEN
  MAP_EVERY EXISTS_TAC
   [`topX:A topology`; `topY:A topology`;
    `p4_side topX (ev_neck ev i) (ev_neck ev i (&4 / &3 % basis 1)) DIFF
     IMAGE (ev_neck (ev:(A)rfs_event) i)
       {y | &1 <= norm y /\ norm y <= exp((A0 + &4) / sqrt(&2))}`] THEN
  ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `z:A` THEN REWRITE_TAC[IN_DIFF] THEN STRIP_TAC THEN
  MATCH_MP_TAC P4_PMAP_TIP THEN
  MAP_EVERY EXISTS_TAC
   [`atlasX:((A->bool)#(A->real^3))->bool`; `gX:real->A->real^3^3`; `ts:real`;
    `topY:A topology`; `atlasY:((A->bool)#(A->real^3))->bool`;
    `gY:real->A->real^3^3`; `D:real^3->bool`; `A0:real`] THEN
  ASM_REWRITE_TAC[]);;

let P4_QF_NONNEG = prove
 (`!top atlas (g:A->real^3^3) x v.
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool) /\
        riemannian_metric atlas g /\ x IN topspace top
        ==> &0 <= v dot (g x ** v)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `v:real^3 = vec 0` THEN
  ASM_REWRITE_TAC[DOT_LZERO; REAL_LE_REFL] THEN
  MATCH_MP_TAC REAL_LT_IMP_LE THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `x:A`] RIEMANNIAN_METRIC_POS) THEN
  ASM_SIMP_TAC[]);;

let P4_PMAP_JAC_BOUND = prove
 (`!topX atlasX (gX:real->A->real^3^3) ts topY atlasY gY ev Y s D A0 PHI XI EINV x0 a e.
        rfs_event_ok (topX,atlasX) gX ts (topY,atlasY) gY ev /\
        hausdorff_space topX /\ compact_space topX /\
        smooth_manifold_atlas topX (atlasX:((A->bool)#(A->real^3))->bool) /\
        apx_sphere_sep topX atlasX /\
        Y IN connected_components_of topY /\
        p4_capdata (topX,atlasX) (topY,atlasY) (ev_omega ev) (ev_limit ev) (gY ts)
                   (ev_index ev) (ev_neck ev) (ev_capm ev) s D A0 PHI XI EINV /\
        connected {y | y IN s /\ &1 < norm y} /\
        x0 IN Y INTER topspace topX /\
        (!t. a <= t /\ t < ts ==> riemannian_metric atlasX (gX t)) /\ a < ts /\ &0 < e
        ==> ?d. &0 < d /\ d <= ts - a /\
                !t x v. ts - d < t /\ t < ts /\ x IN connected_component_of topX x0
                        ==> p4_jqf atlasX atlasY (gY ts)
                              (p4_pmap topX (Y INTER topspace topX)
                                 {i | i IN ev_index ev /\ ev_capm ev i (vec 0) IN Y}
                                 (ev_neck ev) s PHI XI EINV) x v
                            <= (&1 + e) pow 2 * (v dot (gX t x ** v))`,
  REPEAT GEN_TAC THEN DISCH_THEN(MAP_EVERY ASSUME_TAC o CONJUNCTS) THEN
  MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                 `gX:real->A->real^3^3`; `ts:real`; `topY:A topology`;
                 `atlasY:((A->bool)#(A->real^3))->bool`; `gY:real->A->real^3^3`;
                 `ev:(A)rfs_event`; `Y:A->bool`; `s:real^3->bool`; `D:real^3->bool`;
                 `A0:real`; `PHI:num->real^3->A`; `XI:num->real^3->real^3`;
                 `EINV:num->A->real^3`; `x0:A`] P4_CAP_PIECES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> let cs = CONJUNCTS th in
    MAP_EVERY (fun i -> ASSUME_TAC(el i cs)) [1;2;3]) THEN
  MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                 `gX:real->A->real^3^3`; `ts:real`; `topY:A topology`;
                 `atlasY:((A->bool)#(A->real^3))->bool`; `gY:real->A->real^3^3`;
                 `ev:(A)rfs_event`] P4_EVENT_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> let cs = CONJUNCTS th in
    MAP_EVERY (fun i -> ASSUME_TAC(el i cs)) [0;1;7;13]) THEN
  MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                 `gX:real->A->real^3^3`; `ts:real`; `topY:A topology`;
                 `atlasY:((A->bool)#(A->real^3))->bool`; `gY:real->A->real^3^3`;
                 `ev:(A)rfs_event`; `Y:A->bool`] P4_RETAINED_BASIC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> MAP_EVERY (fun i -> ASSUME_TAC(el i (CONJUNCTS th))) [2]) THEN
  MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                 `gX:real->A->real^3^3`; `ts:real`; `topY:A topology`;
                 `atlasY:((A->bool)#(A->real^3))->bool`; `gY:real->A->real^3^3`;
                 `ev:(A)rfs_event`; `Y:A->bool`] P4_RETAINED_CLOSURE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(ASSUME_TAC o CONJUNCT1)] THEN
  SUBGOAL_THEN `FINITE (ev_index (ev:(A)rfs_event))` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th ->
      try fst(dest_const(fst(strip_comb(concl th)))) = "mfd_cut_cap" with Failure _ -> false)) THEN
    REWRITE_TAC[mfd_cut_cap] THEN SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC
   `K = topX closure_of (Y INTER topspace topX) UNION
        UNIONS {IMAGE (ev_neck ev i)
                  {y | &1 <= norm y /\ norm y <= exp((A0 + &4) / sqrt(&2))} | i |
                i IN ev_index (ev:(A)rfs_event) /\ ev_capm ev i (vec 0) IN Y}` THEN
  SUBGOAL_THEN `compact_in topX (K:A->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "K" THEN MATCH_MP_TAC COMPACT_IN_UNION THEN CONJ_TAC THENL
     [MATCH_MP_TAC CLOSED_IN_COMPACT_SPACE THEN ASM_REWRITE_TAC[CLOSED_IN_CLOSURE_OF];
      MATCH_MP_TAC COMPACT_IN_UNIONS THEN CONJ_TAC THENL
       [GEN_REWRITE_TAC ONCE_DEPTH_CONV [SIMPLE_IMAGE_GEN] THEN
        MATCH_MP_TAC FINITE_IMAGE THEN MATCH_MP_TAC FINITE_RESTRICT THEN
        FIRST_ASSUM ACCEPT_TAC;
        REWRITE_TAC[FORALL_IN_GSPEC] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
        FIRST_ASSUM(MP_TAC o C MP (ASSUME
          `i IN ev_index ev /\ ev_capm ev i (vec 0) IN (Y:A->bool)`) o SPEC `i:num`) THEN
        SIMP_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(K:A->bool) SUBSET ev_omega ev` ASSUME_TAC THENL
   [EXPAND_TAC "K" THEN REWRITE_TAC[UNION_SUBSET; UNIONS_SUBSET; FORALL_IN_GSPEC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC
       `Y INTER topspace topX UNION
        UNIONS {IMAGE (ev_neck ev i) (sphere(vec 0,&1)) | i |
                i IN ev_index (ev:(A)rfs_event) /\ ev_capm ev i (vec 0) IN Y}` THEN
      ASM_REWRITE_TAC[UNION_SUBSET; UNIONS_SUBSET; FORALL_IN_GSPEC] THEN
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `IMAGE (ev_neck ev i) (annulus (&1 / &2) (&2)):A->bool` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC IMAGE_SUBSET THEN
        REWRITE_TAC[SUBSET; IN_SPHERE_0; annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC;
        ASM_SIMP_TAC[]];
      X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      FIRST_ASSUM(MP_TAC o C MP (ASSUME
        `i IN ev_index ev /\ ev_capm ev i (vec 0) IN (Y:A->bool)`) o SPEC `i:num`) THEN
      SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                 `gX:real->A->real^3^3`; `ev_omega (ev:(A)rfs_event)`; `ts:real`;
                 `ev_limit (ev:(A)rfs_event)`; `a:real`; `K:A->bool`; `e:real`]
         P4_LIMIT_METRIC_UNIFORM) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `x:A`; `v:real^3`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                 `gX:real->A->real^3^3`; `ts:real`; `topY:A topology`;
                 `atlasY:((A->bool)#(A->real^3))->bool`; `gY:real->A->real^3^3`;
                 `ev:(A)rfs_event`; `Y:A->bool`; `s:real^3->bool`; `D:real^3->bool`;
                 `A0:real`; `PHI:num->real^3->A`; `XI:num->real^3->real^3`;
                 `EINV:num->A->real^3`; `x0:A`; `x:A`] P4_CAP_COVER3) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  STRIP_TAC THENL
   [MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                   `gX:real->A->real^3^3`; `ts:real`; `topY:A topology`;
                   `atlasY:((A->bool)#(A->real^3))->bool`; `gY:real->A->real^3^3`;
                   `ev:(A)rfs_event`; `Y:A->bool`;
                   `{i | i IN ev_index ev /\ ev_capm (ev:(A)rfs_event) i (vec 0) IN Y}`;
                   `s:real^3->bool`; `PHI:num->real^3->A`; `XI:num->real^3->real^3`;
                   `EINV:num->A->real^3`; `x:A`; `v:real^3`] P4_PMAP_JQF_RETAINED) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "K" THEN REWRITE_TAC[IN_UNION] THEN DISJ1_TAC THEN
    MP_TAC(ISPECL [`topX:A topology`; `Y INTER topspace (topX:A topology)`]
                  CLOSURE_OF_SUBSET) THEN
    ANTS_TAC THENL [SET_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `(x:A) IN Y INTER topspace topX` THEN SET_TAC[];
    SUBGOAL_THEN `(x:A) IN IMAGE (ev_neck ev i) {y | y IN s /\ &1 / &2 < norm y}`
    ASSUME_TAC THENL
     [FIRST_ASSUM(MP_TAC o el 3 o CONJUNCTS o
        C MP (CONJ (ASSUME `i IN ev_index (ev:(A)rfs_event)`)
                   (ASSUME `ev_capm ev i (vec 0) IN (Y:A->bool)`)) o SPEC `i:num`) THEN
      UNDISCH_TAC `(x:A) IN IMAGE (ev_neck (ev:(A)rfs_event) i)
                     {y | &1 <= norm y /\ norm y <= exp((A0 + &4) / sqrt(&2))}` THEN
      SET_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `v dot (ev_limit (ev:(A)rfs_event) x ** v)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC P4_PMAP_JQF_COLLAR THEN
      MAP_EVERY EXISTS_TAC
       [`gX:real->A->real^3^3`; `topY:A topology`; `D:real^3->bool`; `A0:real`;
        `i:num`] THEN
      ASM_REWRITE_TAC[];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      EXPAND_TAC "K" THEN REWRITE_TAC[IN_UNION; UNIONS_GSPEC; IN_ELIM_THM] THEN
      DISJ2_TAC THEN EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[]];
    MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                   `gX:real->A->real^3^3`; `ts:real`; `topY:A topology`;
                   `atlasY:((A->bool)#(A->real^3))->bool`; `gY:real->A->real^3^3`;
                   `ev:(A)rfs_event`; `Y:A->bool`; `s:real^3->bool`; `D:real^3->bool`;
                   `A0:real`; `PHI:num->real^3->A`; `XI:num->real^3->real^3`;
                   `EINV:num->A->real^3`; `i:num`; `x:A`; `v:real^3`] P4_PMAP_JQF_TIP) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE THEN UNDISCH_TAC `&0 < e` THEN REAL_ARITH_TAC;
      MATCH_MP_TAC P4_QF_NONNEG THEN
      MAP_EVERY EXISTS_TAC [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`] THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN
        MAP_EVERY UNDISCH_TAC [`ts - d < t`; `d <= ts - a`; `t < ts`] THEN REAL_ARITH_TAC;
        MP_TAC(ISPECL [`topX:A topology`; `x0:A`] CONNECTED_COMPONENT_OF_SUBSET_TOPSPACE) THEN
        UNDISCH_TAC `(x:A) IN connected_component_of topX x0` THEN SET_TAC[]]]]);;

(* ------------------------------------------------------------------------- *)
(* The degree-one condition (U = Y0) and the event-level pinch theorem.     *)
(* ------------------------------------------------------------------------- *)

let P4_PMAP_UCOND = prove
 (`!topX atlasX (gX:real->A->real^3^3) ts topY atlasY gY ev Y s D A0 PHI XI EINV x0.
        rfs_event_ok (topX,atlasX) gX ts (topY,atlasY) gY ev /\
        hausdorff_space topX /\
        smooth_manifold_atlas topX (atlasX:((A->bool)#(A->real^3))->bool) /\
        apx_sphere_sep topX atlasX /\
        Y IN connected_components_of topY /\
        p4_capdata (topX,atlasX) (topY,atlasY) (ev_omega ev) (ev_limit ev) (gY ts)
                   (ev_index ev) (ev_neck ev) (ev_capm ev) s D A0 PHI XI EINV /\
        connected {y | y IN s /\ &1 < norm y} /\
        x0 IN Y INTER topspace topX
        ==> ?U. open_in topX U /\ ~(U = {}) /\ U SUBSET connected_component_of topX x0 /\
                open_in topY
                  (IMAGE (p4_pmap topX (Y INTER topspace topX)
                            {i | i IN ev_index ev /\ ev_capm ev i (vec 0) IN Y}
                            (ev_neck ev) s PHI XI EINV) U) /\
                homeomorphic_map
                  (subtopology topX U,
                   subtopology topY
                     (IMAGE (p4_pmap topX (Y INTER topspace topX)
                               {i | i IN ev_index ev /\ ev_capm ev i (vec 0) IN Y}
                               (ev_neck ev) s PHI XI EINV) U))
                  (p4_pmap topX (Y INTER topspace topX)
                     {i | i IN ev_index ev /\ ev_capm ev i (vec 0) IN Y}
                     (ev_neck ev) s PHI XI EINV) /\
                !x. x IN connected_component_of topX x0 /\
                    p4_pmap topX (Y INTER topspace topX)
                      {i | i IN ev_index ev /\ ev_capm ev i (vec 0) IN Y}
                      (ev_neck ev) s PHI XI EINV x IN
                    IMAGE (p4_pmap topX (Y INTER topspace topX)
                             {i | i IN ev_index ev /\ ev_capm ev i (vec 0) IN Y}
                             (ev_neck ev) s PHI XI EINV) U
                    ==> x IN U`,
  REPEAT GEN_TAC THEN DISCH_THEN(MAP_EVERY ASSUME_TAC o CONJUNCTS) THEN
  EXISTS_TAC `Y INTER topspace (topX:A topology)` THEN
  SUBGOAL_THEN
   `IMAGE (p4_pmap topX (Y INTER topspace topX)
             {i | i IN ev_index ev /\ ev_capm ev i (vec 0) IN Y}
             (ev_neck ev) s PHI XI EINV) (Y INTER topspace topX) =
    Y INTER topspace (topX:A topology)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC(SET_RULE `!f:A->A s. (!x. x IN s ==> f x = x) ==> IMAGE f s = s`) THEN
    SIMP_TAC[P4_PMAP_RETAINED];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                 `gX:real->A->real^3^3`; `ts:real`; `topY:A topology`;
                 `atlasY:((A->bool)#(A->real^3))->bool`; `gY:real->A->real^3^3`;
                 `ev:(A)rfs_event`; `Y:A->bool`] P4_RETAINED_BASIC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> MAP_EVERY (fun i -> ASSUME_TAC(el i (CONJUNCTS th))) [5;6]) THEN
  MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                 `gX:real->A->real^3^3`; `ts:real`; `topY:A topology`;
                 `atlasY:((A->bool)#(A->real^3))->bool`; `gY:real->A->real^3^3`;
                 `ev:(A)rfs_event`; `Y:A->bool`] P4_RETAINED_SUBTOP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                 `gX:real->A->real^3^3`; `ts:real`; `topY:A topology`;
                 `atlasY:((A->bool)#(A->real^3))->bool`; `gY:real->A->real^3^3`;
                 `ev:(A)rfs_event`; `Y:A->bool`; `s:real^3->bool`; `D:real^3->bool`;
                 `A0:real`; `PHI:num->real^3->A`; `XI:num->real^3->real^3`;
                 `EINV:num->A->real^3`; `x0:A`] P4_CAP_PIECES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(ASSUME_TAC o el 2 o CONJUNCTS)] THEN
  REPEAT CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    MATCH_MP_TAC HOMEOMORPHIC_MAP_EQ THEN EXISTS_TAC `\x:A. x` THEN CONJ_TAC THENL
     [REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN SIMP_TAC[P4_PMAP_RETAINED; IN_INTER];
      ASM_REWRITE_TAC[HOMEOMORPHIC_MAP_ID]];
    ALL_TAC] THEN
  X_GEN_TAC `x:A` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                 `gX:real->A->real^3^3`; `ts:real`; `topY:A topology`;
                 `atlasY:((A->bool)#(A->real^3))->bool`; `gY:real->A->real^3^3`;
                 `ev:(A)rfs_event`; `Y:A->bool`; `x0:A`] P4_DECOMPOSITION) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o C MP (ASSUME `(x:A) IN connected_component_of topX x0`) o
    fst o EQ_IMP_RULE o SPEC `x:A` o
    REWRITE_RULE[EXTENSION; IN_UNION; UNIONS_GSPEC; IN_ELIM_THM] o last o CONJUNCTS) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  (MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                  `gX:real->A->real^3^3`; `ts:real`; `topY:A topology`;
                  `atlasY:((A->bool)#(A->real^3))->bool`; `gY:real->A->real^3^3`;
                  `ev:(A)rfs_event`; `Y:A->bool`; `s:real^3->bool`; `D:real^3->bool`;
                  `A0:real`; `PHI:num->real^3->A`; `XI:num->real^3->real^3`;
                  `EINV:num->A->real^3`; `i:num`; `x:A`] P4_PMAP_CAPVAL) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
   MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                  `gX:real->A->real^3^3`; `ts:real`; `topY:A topology`;
                  `atlasY:((A->bool)#(A->real^3))->bool`; `gY:real->A->real^3^3`;
                  `ev:(A)rfs_event`; `i:num`] P4_EVENT_CAPS) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(MP_TAC o el 6 o CONJUNCTS)] THEN
   MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                  `gX:real->A->real^3^3`; `ts:real`; `topY:A topology`;
                  `atlasY:((A->bool)#(A->real^3))->bool`; `gY:real->A->real^3^3`;
                  `ev:(A)rfs_event`] P4_EVENT_FACTS) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(MP_TAC o el 12 o CONJUNCTS)] THEN
   UNDISCH_TAC
    `p4_pmap topX (Y INTER topspace topX)
       {i | i IN ev_index ev /\ ev_capm ev i (vec 0) IN Y}
       (ev_neck ev) s PHI XI EINV (x:A) IN Y INTER topspace topX` THEN
   SET_TAC[]));;

let P4_PINCH_EVENT = prove
 (`!topX atlasX (gX:real->A->real^3^3) ts topY atlasY gY ev Y s D A0 PHI XI EINV a.
        rfs_event_ok (topX,atlasX) gX ts (topY,atlasY) gY ev /\
        hausdorff_space topX /\ compact_space topX /\
        smooth_manifold_atlas topX (atlasX:((A->bool)#(A->real^3))->bool) /\
        apx_sphere_sep topX atlasX /\
        Y IN connected_components_of topY /\
        p4_capdata (topX,atlasX) (topY,atlasY) (ev_omega ev) (ev_limit ev) (gY ts)
                   (ev_index ev) (ev_neck ev) (ev_capm ev) s D A0 PHI XI EINV /\
        connected {y | y IN s /\ &1 < norm y} /\
        (!t. a <= t /\ t < ts ==> riemannian_metric atlasX (gX t)) /\ a < ts
        ==> ?X. X IN connected_components_of topX /\
                !e. &0 < e
                    ==> ?t1. a <= t1 /\ t1 < ts /\
                             !t. t1 < t /\ t < ts
                                 ==> ?p. p4_pinch_map (topX,atlasX) (gX t) X
                                           (topY,atlasY) (gY ts) Y (&1 + e) p`,
  REPEAT GEN_TAC THEN DISCH_THEN(MAP_EVERY ASSUME_TAC o CONJUNCTS) THEN
  MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                 `gX:real->A->real^3^3`; `ts:real`; `topY:A topology`;
                 `atlasY:((A->bool)#(A->real^3))->bool`; `gY:real->A->real^3^3`;
                 `ev:(A)rfs_event`; `Y:A->bool`] P4_RETAINED_BASIC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o el 6 o CONJUNCTS) THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
  DISCH_THEN(X_CHOOSE_TAC `x0:A`) THEN
  EXISTS_TAC `connected_component_of topX (x0:A)` THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                   `gX:real->A->real^3^3`; `ts:real`; `topY:A topology`;
                   `atlasY:((A->bool)#(A->real^3))->bool`; `gY:real->A->real^3^3`;
                   `ev:(A)rfs_event`; `Y:A->bool`; `s:real^3->bool`; `D:real^3->bool`;
                   `A0:real`; `PHI:num->real^3->A`; `XI:num->real^3->real^3`;
                   `EINV:num->A->real^3`; `x0:A`] P4_CAP_PIECES) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                 `gX:real->A->real^3^3`; `ts:real`; `topY:A topology`;
                 `atlasY:((A->bool)#(A->real^3))->bool`; `gY:real->A->real^3^3`;
                 `ev:(A)rfs_event`; `Y:A->bool`; `s:real^3->bool`; `D:real^3->bool`;
                 `A0:real`; `PHI:num->real^3->A`; `XI:num->real^3->real^3`;
                 `EINV:num->A->real^3`; `x0:A`; `a:real`; `e:real`] P4_PMAP_JAC_BOUND) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `ts - d:real` THEN CONJ_TAC THENL
   [UNDISCH_TAC `d <= ts - a` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [UNDISCH_TAC `&0 < d` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `t:real` THEN STRIP_TAC THEN
  EXISTS_TAC
   `p4_pmap topX (Y INTER topspace topX)
      {i | i IN ev_index ev /\ ev_capm ev i (vec 0) IN Y}
      (ev_neck (ev:(A)rfs_event)) s PHI XI EINV` THEN
  REWRITE_TAC[p4_pinch_map] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC P4_PMAP_CONTINUOUS THEN
    MAP_EVERY EXISTS_TAC
     [`atlasX:((A->bool)#(A->real^3))->bool`; `gX:real->A->real^3^3`; `ts:real`;
      `atlasY:((A->bool)#(A->real^3))->bool`; `gY:real->A->real^3^3`;
      `D:real^3->bool`; `A0:real`] THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC P4_PMAP_SMOOTH THEN
    MAP_EVERY EXISTS_TAC
     [`gX:real->A->real^3^3`; `ts:real`; `topY:A topology`; `gY:real->A->real^3^3`;
      `D:real^3->bool`; `A0:real`] THEN
    ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`x:A`; `v:real^3`] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`t:real`; `x:A`; `v:real^3`]) THEN
    ASM_REWRITE_TAC[p4_jqf];
    MATCH_MP_TAC P4_PMAP_UCOND THEN
    MAP_EVERY EXISTS_TAC
     [`atlasX:((A->bool)#(A->real^3))->bool`; `gX:real->A->real^3^3`; `ts:real`;
      `atlasY:((A->bool)#(A->real^3))->bool`; `gY:real->A->real^3^3`;
      `D:real^3->bool`; `A0:real`] THEN
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The history level: cap data from the Part 3 structure, and the theorem.  *)
(* ------------------------------------------------------------------------- *)

let P4_RF_METRIC_AT = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) a b (g:real->A->real^N^N) t.
        ricci_flow_from (top,atlas) a b g /\ a <= t /\ t < b
        ==> riemannian_metric atlas (g t)`,
  REWRITE_TAC[ricci_flow_from; ricci_flow_on] THEN REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `t:real = a` THENL
   [ASM_REWRITE_TAC[];
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      try type_of(fst(dest_forall(concl th))) = `:real` with Failure _ -> false)) THEN
    MAP_EVERY UNDISCH_TAC [`a <= t:real`; `t < b:real`; `~(t:real = a)`] THEN
    REAL_ARITH_TAC]);;

let P4_PREVIEW_AT = prove
 (`!(hs:(A)rfs_history) k.
        rfs_vatlas (rfs_preview hs k) (hs_time hs k) =
        restrict_atlas (hs_atlas hs (k - 1)) (ev_omega(hs_event hs k)) /\
        rfs_vmetric (rfs_preview hs k) (hs_time hs k) =
        restrict_metric (hs_atlas hs (k - 1)) (ev_omega(hs_event hs k))
                        (ev_limit(hs_event hs k))`,
  REWRITE_TAC[rfs_preview; rfs_vatlas; rfs_vmetric]);;

let P4_EXP_NEG_LT_1 = prove
 (`!x. &0 < x ==> exp(--x) < &1`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC RAND_CONV [GSYM REAL_EXP_0] THEN
  REWRITE_TAC[REAL_EXP_MONO_LT] THEN ASM_REAL_ARITH_TAC);;

let P4_NECK_DOM_COLLAR_CONNECTED = prove
 (`!dl. &0 < dl ==> connected {y:real^3 | y IN rfs_neck_dom dl /\ &1 < norm y}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `exp(--(inv(sqrt(&2) * dl))) < &1` ASSUME_TAC THENL
   [MATCH_MP_TAC P4_EXP_NEG_LT_1 THEN MATCH_MP_TAC REAL_LT_INV THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SQRT_POS_LT THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `{y:real^3 | y IN rfs_neck_dom dl /\ &1 < norm y} =
    {x | &1 < norm(x - vec 0) /\ norm(x - vec 0) < exp(inv(sqrt(&2) * dl))}`
  SUBST1_TAC THENL
   [REWRITE_TAC[rfs_neck_dom; annulus; EXTENSION; IN_ELIM_THM; VECTOR_SUB_RZERO] THEN
    X_GEN_TAC `y:real^3` THEN
    UNDISCH_TAC `exp(--(inv(sqrt(&2) * dl))) < &1` THEN REAL_ARITH_TAC;
    MATCH_MP_TAC(CONJUNCT1 CONNECTED_ANNULUS) THEN REWRITE_TAC[DIMINDEX_3] THEN ARITH_TAC]);;

let P4_EMPTY_CAPDATA = prove
 (`!topX atlasX topY atlasY Om (gl:A->real^3^3) gYts J (e:num->real^3->A) cm A0.
        &0 < A0 /\ J = {}
        ==> ?s D PHI XI EINV.
              p4_capdata (topX,atlasX) (topY,atlasY) Om gl gYts J e cm s D A0 PHI XI EINV /\
              connected {y | y IN s /\ &1 < norm y}`,
  REPEAT STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC
   [`annulus (&1 / &2) (exp((A0 + &4) / sqrt(&2)) + &2):real^3->bool`;
    `(:real^3)`; `\i:num. \y:real^3. (ARB:A)`; `\i:num. \y:real^3. y`;
    `\i:num. \x:A. (ARB:real^3)`] THEN
  ASM_REWRITE_TAC[p4_capdata; NOT_IN_EMPTY; OPEN_ANNULUS; OPEN_UNIV] THEN
  MP_TAC(SPEC `(A0 + &4) / sqrt(&2)` REAL_EXP_POS_LT) THEN DISCH_TAC THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; annulus; IN_ELIM_THM] THEN GEN_TAC THEN
    UNDISCH_TAC `&0 < exp((A0 + &4) / sqrt(&2))` THEN REAL_ARITH_TAC;
    REWRITE_TAC[SUBSET; annulus; IN_ELIM_THM] THEN GEN_TAC THEN
    UNDISCH_TAC `&0 < exp((A0 + &4) / sqrt(&2))` THEN REAL_ARITH_TAC;
    REWRITE_TAC[annulus; IN_ELIM_THM] THEN X_GEN_TAC `y:real^3` THEN
    ASM_CASES_TAC `y:real^3 = vec 0` THEN ASM_REWRITE_TAC[NORM_0] THEN REAL_ARITH_TAC;
    SUBGOAL_THEN
     `{y:real^3 | y IN annulus (&1 / &2) (exp((A0 + &4) / sqrt(&2)) + &2) /\ &1 < norm y} =
      {x | &1 < norm(x - vec 0) /\ norm(x - vec 0) < exp((A0 + &4) / sqrt(&2)) + &2}`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; annulus; IN_ELIM_THM; VECTOR_SUB_RZERO] THEN
      GEN_TAC THEN REAL_ARITH_TAC;
      MATCH_MP_TAC(CONJUNCT1 CONNECTED_ANNULUS) THEN REWRITE_TAC[DIMINDEX_3] THEN
      ARITH_TAC]]);;

let P4_HISTORY_CAPDATA = prove
 (`!C eps hf md g0 A0 rp dl (hs:(A)rfs_history) k.
        p3_std_initial g0 A0 /\
        p3_struct (C,eps,hf,md,g0,A0) (rp,dl) hs /\ 1 <= k /\ k <= hs_count hs
        ==> ?s D PHI XI EINV.
              p4_capdata (hs_top hs (k - 1),hs_atlas hs (k - 1))
                         (hs_top hs k,hs_atlas hs k)
                         (ev_omega (hs_event hs k)) (ev_limit (hs_event hs k))
                         (hs_metric hs k (hs_time hs k))
                         (ev_index (hs_event hs k)) (ev_neck (hs_event hs k))
                         (ev_capm (hs_event hs k)) s D A0 PHI XI EINV /\
              connected {y | y IN s /\ &1 < norm y}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < A0` ASSUME_TAC THENL
   [UNDISCH_TAC `p3_std_initial g0 A0` THEN REWRITE_TAC[p3_std_initial] THEN SIMP_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `ev_index (hs_event (hs:(A)rfs_history) k) = {}` THENL
   [MATCH_MP_TAC P4_EMPTY_CAPDATA THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [p3_struct]) THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o C MP (CONJ (ASSUME `1 <= k`)
    (ASSUME `k <= hs_count (hs:(A)rfs_history)`)) o SPEC `k:num`) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (K ALL_TAC)
    (MP_TAC o REWRITE_RULE[p3_cap_ok; RIGHT_IMP_EXISTS_THM; SKOLEM_THM]))) THEN
  DISCH_THEN(X_CHOOSE_THEN `PHI:num->real^3->A` (X_CHOOSE_TAC `XI:num->real^3->real^3`)) THEN
  SUBGOAL_THEN `&0 <= hs_time (hs:(A)rfs_history) k` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `hs_time (hs:(A)rfs_history) 0` THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `rfs_history_ok (hs:(A)rfs_history)` THEN
      SIMP_TAC[rfs_history_ok; REAL_LE_REFL];
      MATCH_MP_TAC RFS_TIME_MONO THEN ASM_REWRITE_TAC[LE_0] THEN
      UNDISCH_TAC `k <= hs_count (hs:(A)rfs_history)` THEN ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < dl(hs_time (hs:(A)rfs_history) k)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o C MP (ASSUME `&0 <= hs_time (hs:(A)rfs_history) k`) o
      SPEC `hs_time (hs:(A)rfs_history) k` o
      check (fun th -> is_forall(concl th) &&
        try type_of(fst(dest_forall(concl th))) = `:real` &&
            not(is_forall(snd(dest_forall(concl th)))) with Failure _ -> false)) THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  DISCH_THEN(X_CHOOSE_TAC `i0:num`) THEN
  MP_TAC(ISPECL [`md:real->real`; `g0:real^3->real^3^3`; `A0:real`; `dl:real->real`;
                 `p3_hscale hf rp dl`; `hs:(A)rfs_history`; `k:num`; `i0:num`;
                 `(PHI:num->real^3->A) i0`; `(XI:num->real^3->real^3) i0`] P4_CAP_FACTS) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> let cs = CONJUNCTS th in
    MAP_EVERY (fun i -> ASSUME_TAC(el i cs)) [4;6]) THEN
  MP_TAC(SPECL [`dl(hs_time (hs:(A)rfs_history) k):real`; `A0:real`] P4_NECK_DOM_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `open {x:real^3 | --(inv(dl(hs_time (hs:(A)rfs_history) k))) <
                                 A0 + &4 - p3_std_dist g0 x}`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`hs_top (hs:(A)rfs_history) k`; `hs_atlas (hs:(A)rfs_history) k`;
                   `{x:real^3 | --(inv(dl(hs_time (hs:(A)rfs_history) k))) <
                                A0 + &4 - p3_std_dist g0 x}`;
                   `(PHI:num->real^3->A) i0`] MFD_PARAM_MAPS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?EINV:num->A->real^3.
      !i. i IN ev_index (hs_event hs k)
          ==> !z. z IN rfs_neck_dom (dl(hs_time hs k))
                  ==> EINV i (ev_neck (hs_event hs k) i z) = z`
  (X_CHOOSE_TAC `EINV:num->A->real^3`) THENL
   [REWRITE_TAC[GSYM SKOLEM_THM; GSYM RIGHT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`hs:(A)rfs_history`; `C:real`; `eps:real`; `dl:real->real`;
                   `p3_hscale hf rp dl`; `k:num`; `i:num`] P4_SURGERY_NECK_PARAM) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`hs_top (hs:(A)rfs_history) (k - 1)`; `hs_atlas (hs:(A)rfs_history) (k - 1)`;
                   `rfs_neck_dom (dl(hs_time (hs:(A)rfs_history) k))`;
                   `ev_neck (hs_event (hs:(A)rfs_history) k) i`] MFD_PARAM_MAPS) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `e':A->real^3` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `e':A->real^3` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`rfs_neck_dom (dl(hs_time (hs:(A)rfs_history) k))`;
    `{x:real^3 | --(inv(dl(hs_time (hs:(A)rfs_history) k))) < A0 + &4 - p3_std_dist g0 x}`;
    `PHI:num->real^3->A`; `XI:num->real^3->real^3`; `EINV:num->A->real^3`] THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC P4_NECK_DOM_COLLAR_CONNECTED THEN FIRST_ASSUM ACCEPT_TAC] THEN
  REWRITE_TAC[p4_capdata] THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `C:real`; `eps:real`; `dl:real->real`;
                 `p3_hscale hf rp dl`; `k:num`; `i:num`] P4_SURGERY_NECK_PARAM) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`md:real->real`; `g0:real^3->real^3^3`; `A0:real`; `dl:real->real`;
                 `p3_hscale hf rp dl`; `hs:(A)rfs_history`; `k:num`; `i:num`;
                 `(PHI:num->real^3->A) i`; `(XI:num->real^3->real^3) i`] P4_CAP_FACTS) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; REWRITE_TAC[P4_PREVIEW_AT] THEN STRIP_TAC] THEN
  ASM_SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* MT Prop 15.12 (in corrected form): every history with the Part 3          *)
(* invariant has the pinch property.  The only hypothesis is the             *)
(* smooth-topology statement RFS_CUTCAP_SC_STATEMENT (simply connected       *)
(* components survive cut-and-cap); APX_SC_SPHERE_SEP_STATEMENT is           *)
(* SMT_SC_SPHERE_SEP.                                                        *)
(* ------------------------------------------------------------------------- *)

let P4_PINCH_FROM_INV = prove
 (`RFS_CUTCAP_SC_STATEMENT (:A+num#num#real^3) (:A+num#num#real^3)
   ==> P4_PINCH_FROM_INV_STATEMENT (:A)`,
  REWRITE_TAC[P4_PINCH_FROM_INV_STATEMENT] THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`;
    `g0:real^3->real^3^3`; `A0:real`; `rs:num->real`; `ks:num->real`; `dd:num->real`;
    `hs:(A+num#num#real^3)rfs_history`; `top:A topology`;
    `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
    `iota:A->A+num#num#real^3`; `iota':A+num#num#real^3->A`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `p3_struct (C,eps,hf,md,g0,A0) (p3_stepf rs,p3_stepf dd)
              (hs:(A+num#num#real^3)rfs_history)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `p3_inv (C,eps,hf,md,g0,A0) (rs,ks,dd)
                        (hs:(A+num#num#real^3)rfs_history)` THEN
    SIMP_TAC[p3_inv];
    ALL_TAC] THEN
  SUBGOAL_THEN `p2b_hs_sep (hs:(A+num#num#real^3)rfs_history)` MP_TAC THENL
   [MATCH_MP_TAC P3_STRUCT_SPHERE_SEP THEN
    MAP_EVERY EXISTS_TAC
     [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`;
      `g0:real^3->real^3^3`; `A0:real`; `p3_stepf rs`; `p3_stepf dd`] THEN
    ASM_REWRITE_TAC[SMT_SC_SPHERE_SEP];
    REWRITE_TAC[p2b_hs_sep] THEN DISCH_TAC] THEN
  SUBGOAL_THEN `rfs_history_ok (hs:(A+num#num#real^3)rfs_history)` MP_TAC THENL
   [UNDISCH_TAC `p3_struct (C,eps,hf,md,g0,A0) (p3_stepf rs,p3_stepf dd)
                           (hs:(A+num#num#real^3)rfs_history)` THEN
    SIMP_TAC[p3_struct];
    ALL_TAC] THEN
  REWRITE_TAC[rfs_history_ok] THEN STRIP_TAC THEN
  REWRITE_TAC[p4_pinch_ok] THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
  X_GEN_TAC `Y:(A+num#num#real^3)->bool` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`;
                 `g0:real^3->real^3^3`; `A0:real`; `p3_stepf rs`; `p3_stepf dd`;
                 `hs:(A+num#num#real^3)rfs_history`; `k:num`] P4_HISTORY_CAPDATA) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real^3->bool` (X_CHOOSE_THEN `D:real^3->bool`
    (X_CHOOSE_THEN `PHI:num->real^3->A+num#num#real^3`
      (X_CHOOSE_THEN `XI:num->real^3->real^3`
        (X_CHOOSE_THEN `EINV:num->A+num#num#real^3->real^3` STRIP_ASSUME_TAC))))) THEN
  SUBGOAL_THEN `k - 1 + 1 = k /\ k - 1 <= hs_count (hs:(A+num#num#real^3)rfs_history)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`1 <= k`; `k <= hs_count (hs:(A+num#num#real^3)rfs_history)`] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o C MP (CONJ (ASSUME `1 <= k`)
    (ASSUME `k <= hs_count (hs:(A+num#num#real^3)rfs_history)`)) o SPEC `k:num` o
    check (fun th -> try fst(dest_const(fst(strip_comb(snd(dest_imp(snd(dest_forall
      (concl th)))))))) = "rfs_event_ok" with Failure _ -> false)) THEN
  DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o C MP (ASSUME `k - 1 <= hs_count (hs:(A+num#num#real^3)rfs_history)`) o
    SPEC `k - 1` o
    check (fun th -> try is_conj(snd(dest_imp(snd(dest_forall(concl th))))) with
                     Failure _ -> false)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o C MP (ASSUME `k - 1 <= hs_count (hs:(A+num#num#real^3)rfs_history)`) o
    SPEC `k - 1` o
    check (fun th -> try fst(dest_const(fst(dest_comb(fst(dest_comb(snd(dest_imp(snd
      (dest_forall(concl th)))))))))) = "real_lt" with Failure _ -> false)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC P4_PINCH_EVENT THEN
  MAP_EVERY EXISTS_TAC
   [`hs_event (hs:(A+num#num#real^3)rfs_history) k`; `s:real^3->bool`;
    `D:real^3->bool`; `A0:real`; `PHI:num->real^3->A+num#num#real^3`;
    `XI:num->real^3->real^3`; `EINV:num->A+num#num#real^3->real^3`] THEN
  REWRITE_TAC[ETA_AX] THEN ASM_SIMP_TAC[] THEN
  X_GEN_TAC `t:real` THEN STRIP_TAC THEN
  MATCH_MP_TAC P4_RF_METRIC_AT THEN
  MAP_EVERY EXISTS_TAC
   [`hs_top (hs:(A+num#num#real^3)rfs_history) (k - 1)`;
    `hs_time (hs:(A+num#num#real^3)rfs_history) (k - 1)`;
    `hs_time (hs:(A+num#num#real^3)rfs_history) k`] THEN
  ASM_REWRITE_TAC[]);;

(* Part 4 with the pinch bridge discharged (P4_EXTINCTION_CM3): its         *)
(* hypotheses are the CM analysis, the topology statements and              *)
(* RFS_CUTCAP_SC_STATEMENT, all proved (pc_p4_wire, pc_p4_final).           *)

let P4_EXTINCTION_CM3 = prove
 (`CM_GOOD_SWEEPOUT_STATEMENT (:A+num#num#real^3) /\
   CM_HARMONIC_SPHERE_STATEMENT (:A+num#num#real^3) /\
   P4_DEGREE_ONE_STATEMENT (:A+num#num#real^3) (:A+num#num#real^3) /\
   P4_SC_DEGREE_ONE_STATEMENT (:A) /\ P4_SMOOTHING_STATEMENT (:A) /\
   RFS_CUTCAP_SC_STATEMENT (:A+num#num#real^3) (:A+num#num#real^3)
   ==> P4_EXTINCTION_STATEMENT (:A)`,
  STRIP_TAC THEN MATCH_MP_TAC P4_EXTINCTION_CM2 THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC P4_PINCH_FROM_INV THEN ASM_REWRITE_TAC[]);;

