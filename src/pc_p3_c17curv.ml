(* ========================================================================= *)
(* Unit pc_p3_c17curv: curvature bounds for MT Lemma 17.12.                 *)
(* An event that cuts no neck and discards nothing is impossible after a    *)
(* maximal slab: then Omega is the whole old stage, the slab metrics       *)
(* converge in C^2 on that compact stage, and |Rm| stays bounded on the    *)
(* slab, against rfs_slab_maximal.                                          *)
(*                                                                         *)
(* |Rm| bounds on compact sets for a fixed metric and for a               *)
(* Ricci flow on compact time intervals.                                   *)
(* ========================================================================= *)

needs "src/pc_rfs_history.ml";;
needs "src/pc_rfa_mfd.ml";;
needs "src/pc_rfa_doubling.ml";;
needs "src/pc_rfa_tmaxp.ml";;
needs "src/pc_rfa_shi.ml";;
needs "src/pc_lrg_base.ml";;
needs "src/pc_top_cover.ml";;
needs "src/pc_p3_c17top.ml";;

prioritize_real();;
type_invention_error := true;;

(* Copies, with the proofs unchanged, of P2B9S_RMD2_CONTINUOUS and          *)
(* P2B9S_RMD2_COMPACT_BOUND of pc_p2b_979s, which this unit does not load.  *)

let P3H_RMD2_CONTINUOUS_FIXED = prove
 (`!m top atlas (g:A->real^N^N).
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g
     ==> continuous_map (top,euclideanreal) (rfa_rmd2 m atlas g)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC TOPC_CONTINUOUS_MAP_LOCAL THEN
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`]
                CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  SPEC_TAC(`chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)`,
           `c:(A->bool)#(A->real^N)`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; FST] THEN
  MAP_EVERY X_GEN_TAC [`U:A->bool`; `phi:A->real^N`] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [smooth_manifold_atlas]) THEN
  DISCH_THEN(MP_TAC o SPECL [`U:A->bool`; `phi:A->real^N`]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  EXISTS_TAC `U:A->bool` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_EQ THEN
  EXISTS_TAC `\z:A. lrm_deriv_norm2 m (metric_local atlas (U,phi) (g:A->real^N^N)) (phi z)` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER] THEN X_GEN_TAC `z:A` THEN STRIP_TAC THEN
    BETA_TAC THEN CONV_TAC SYM_CONV THEN
    MP_TAC(ISPECL [`m:num`; `top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `(U:A->bool,phi:A->real^N)`; `z:A`] RFA_RMD2_CHART) THEN
    ASM_REWRITE_TAC[FST; SND];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\z:A. lrm_deriv_norm2 m (metric_local atlas (U,phi) (g:A->real^N^N)) (phi z)) =
    (\y. lrm_deriv_norm2 m (metric_local atlas (U,phi) g) y) o (phi:A->real^N)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
  EXISTS_TAC `subtopology euclidean (IMAGE (phi:A->real^N) U)` THEN CONJ_TAC THENL
   [ASM_MESON_TAC[HOMEOMORPHIC_IMP_CONTINUOUS_MAP]; ALL_TAC] THEN
  REWRITE_TAC[CONTINUOUS_MAP_EQ_LIFT; CONTINUOUS_MAP_EUCLIDEAN; o_DEF] THEN
  MATCH_MP_TAC LRM_DERIV_NORM2_CONTINUOUS THEN
  UNDISCH_TAC `riemannian_metric atlas (g:A->real^N^N)` THEN
  REWRITE_TAC[riemannian_metric] THEN
  DISCH_THEN(MP_TAC o SPEC `(U:A->bool,phi:A->real^N)`) THEN
  ASM_REWRITE_TAC[FST; SND]);;

let P3H_RMD2_COMPACT_BOUND_FIXED = prove
 (`!m top atlas (g:A->real^N^N) K.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\ compact_in top K
     ==> ?B. !y. y IN K ==> rfa_rmd2 m atlas g y <= B`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `euclideanreal`; `rfa_rmd2 m atlas (g:A->real^N^N)`;
                 `K:A->bool`] IMAGE_COMPACT_IN) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[P3H_RMD2_CONTINUOUS_FIXED]; ALL_TAC] THEN
  REWRITE_TAC[COMPACT_IN_EUCLIDEANREAL; MBOUNDED_REAL_EUCLIDEAN_METRIC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1) THEN
  REWRITE_TAC[real_bounded; FORALL_IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_TAC `B:real`) THEN EXISTS_TAC `B:real` THEN
  ASM_MESON_TAC[REAL_ARITH `abs x <= b ==> x <= b`]);;

(* |Rm| (largest absolute sectional curvature) <= the tensor norm of Rm. *)

let P3H_RM_NORM_LE_RMD2 = prove
 (`!top atlas (g:A->real^3^3) x.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        x IN topspace top
        ==> mfd_rm_norm atlas g x <= sqrt(rfa_rmd2 0 atlas g x)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC RFA_MFD_RM_NORM_LE THEN
  REWRITE_TAC[DIMINDEX_3; ARITH_RULE `2 <= 3`] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC RFA_MFD_SECTIONAL_LE_RMD2 THEN
  EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[]);;

(* A Ricci flow on a compact manifold has bounded |Rm| on [a,c], c < b. *)

let P3H_RF_RM_BOUND_COMPACT_TIME = prove
 (`!top atlas a b c (g:real->A->real^3^3).
        ricci_flow_from (top,atlas) a b g /\ compact_space top /\ c < b
        ==> ?B. !t x. a <= t /\ t <= c /\ x IN topspace top
                      ==> mfd_rm_norm atlas (g t) x <= B`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `a:real`; `b:real`; `g:real->A->real^3^3`] RFA_RMD2_CONTINUOUS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL
   [`prod_topology (subtopology euclideanreal {t | a <= t /\ t < b})
                   (subtopology (top:A topology) (topspace top))`;
    `\z:real#A. rfa_rmd2 0 (atlas:((A->bool)#(A->real^3))->bool)
                           ((g:real->A->real^3^3) (FST z)) (SND z)`;
    `{t | a <= t /\ t <= c} CROSS topspace (top:A topology)`] RFA_CMAP_COMPACT_BOUND) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[COMPACT_IN_CROSS] THEN REPEAT DISJ2_TAC THEN CONJ_TAC THENL
     [REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY] THEN CONJ_TAC THENL
       [REWRITE_TAC[GSYM real_interval; COMPACT_IN_EUCLIDEANREAL_INTERVAL];
        REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `s:real` THEN
        UNDISCH_TAC `c:real < b` THEN REAL_ARITH_TAC];
      REWRITE_TAC[COMPACT_IN_ABSOLUTE; GSYM compact_space] THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `B:real`) THEN EXISTS_TAC `sqrt(max B (&0))` THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `a:real`; `b:real`; `g:real->A->real^3^3`; `t:real`]
                RFA_RICCI_FLOW_FROM_METRIC) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `t:real <= c` THEN UNDISCH_TAC `c:real < b` THEN
    REAL_ARITH_TAC;
    STRIP_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sqrt(rfa_rmd2 0 (atlas:((A->bool)#(A->real^3))->bool)
                             ((g:real->A->real^3^3) t) x)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC P3H_RM_NORM_LE_RMD2 THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC SQRT_MONO_LE THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(t:real,x:A)`) THEN
  REWRITE_TAC[IN_CROSS; IN_ELIM_THM; FST; SND] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[]; REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* Near an event time the slab metrics converge in C^2 on                   *)
(* compact subsets of Omega (rfs_limit_metric); if Omega is the whole       *)
(* (compact) old stage, |Rm| is bounded near the event time and hence on    *)
(* the whole slab, which contradicts rfs_slab_maximal.  So an event without *)
(* necks discards something.                                                *)
(* ========================================================================= *)

let P3H_LIMIT_RIEMANNIAN = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) Om ts g gl.
        smooth_manifold_atlas top atlas /\
        rfs_limit_metric (top,atlas) Om ts g gl /\ topspace top SUBSET Om
        ==> riemannian_metric atlas gl`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rfs_limit_metric; riemannian_metric] THEN
  STRIP_TAC THEN X_GEN_TAC `c:(A->bool)#(A->real^3)` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `c:(A->bool)#(A->real^3)` o
    check (fun th -> can (find_term ((=) `metric_field:(real^3->bool)->(real^3->real^3^3)->bool`))
                         (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `FST(c:(A->bool)#(A->real^3)) INTER Om = FST c` (fun th -> REWRITE_TAC[th]) THEN
  SUBGOAL_THEN `FST(c:(A->bool)#(A->real^3)) SUBSET topspace top` MP_TAC THENL
   [ALL_TAC; UNDISCH_TAC `topspace top SUBSET (Om:A->bool)` THEN SET_TAC[]] THEN
  UNDISCH_TAC `smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool)` THEN
  REWRITE_TAC[smooth_manifold_atlas] THEN
  DISCH_THEN(MP_TAC o SPECL [`FST(c:(A->bool)#(A->real^3))`; `SND(c:(A->bool)#(A->real^3))`] o
             CONJUNCT1) THEN
  ASM_REWRITE_TAC[PAIR] THEN STRIP_TAC THEN MATCH_MP_TAC OPEN_IN_SUBSET THEN
  ASM_REWRITE_TAC[]);;

let P3H_LIMIT_RM_BOUND = prove
 (`!top atlas a Om ts (g:real->A->real^3^3) gl.
        smooth_manifold_atlas top atlas /\ compact_space top /\ a < ts /\
        (!t. a <= t /\ t < ts ==> riemannian_metric atlas (g t)) /\
        rfs_limit_metric (top,atlas) Om ts g gl /\ topspace top SUBSET Om
        ==> ?d B. &0 < d /\ d <= ts - a /\
                  !t x. ts - d < t /\ t < ts /\ x IN topspace top
                        ==> mfd_rm_norm atlas (g t) x <= B`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `riemannian_metric atlas (gl:A->real^3^3)` ASSUME_TAC THENL
   [MATCH_MP_TAC P3H_LIMIT_RIEMANNIAN THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `Om:A->bool`; `ts:real`;
                          `g:real->A->real^3^3`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`0`; `top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `gl:A->real^3^3`; `topspace(top:A topology)`]
                P3H_RMD2_COMPACT_BOUND_FIXED) THEN
  ASM_REWRITE_TAC[GSYM compact_space] THEN
  DISCH_THEN(X_CHOOSE_TAC `K0:real`) THEN
  X_CHOOSE_TAC `K:real` (SPEC `K0:real` LRG_RM_NEAR_BOUND) THEN
  UNDISCH_TAC `rfs_limit_metric (top,atlas) (Om:A->bool) ts (g:real->A->real^3^3) gl` THEN
  REWRITE_TAC[rfs_limit_metric] THEN
  DISCH_THEN(MP_TAC o SPECL [`topspace(top:A topology)`; `2`; `&1 / &4`] o CONJUNCT2) THEN
  ASM_REWRITE_TAC[GSYM compact_space] THEN
  ANTS_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d0:real` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`min d0 (ts - a)`; `sqrt(max K (&0))`] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `x:A`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `riemannian_metric atlas ((g:real->A->real^3^3) t)` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sqrt(rfa_rmd2 0 (atlas:((A->bool)#(A->real^3))->bool)
                             ((g:real->A->real^3^3) t) x)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC P3H_RM_NORM_LE_RMD2 THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC SQRT_MONO_LE THEN
  MATCH_MP_TAC(REAL_ARITH `x <= K ==> x <= max K (&0)`) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `x:A`]
                CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[rfa_rmd2] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  EXISTS_TAC `IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)))
                    (FST(chart_at atlas x))` THEN
  EXISTS_TAC `metric_local (atlas:((A->bool)#(A->real^3))->bool)
                           (chart_at atlas (x:A)) (gl:A->real^3^3)` THEN
  REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `riemannian_metric atlas (gl:A->real^3^3)` THEN
    REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    UNDISCH_TAC `riemannian_metric atlas ((g:real->A->real^3^3) t)` THEN
    REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
    FIRST_X_ASSUM(MP_TAC o SPEC `x:A` o
      check (fun th -> can (find_term ((=) `K0:real`)) (concl th))) THEN
    ASM_REWRITE_TAC[rfa_rmd2];
    MATCH_MP_TAC REAL_LT_IMP_LE THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

let P3H_CUT_EMPTY_TOPSPACE = prove
 (`!topX atlasX topZ (atlasZ:((A->bool)#(A->real^3))->bool) e cp cm.
        mfd_cut_cap topX atlasX topZ atlasZ {} e cp cm (\x. x) (\x. x)
        ==> topspace topZ = topspace topX`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP P3H_CUT_SAME_SUBSPACE) THEN
  REWRITE_TAC[mfd_cut_spheres; mfd_cut_cores; NOT_IN_EMPTY; SIMPLE_IMAGE; IMAGE_CLAUSES;
              UNIONS_0; DIFF_EMPTY; EMPTY_GSPEC] THEN
  SIMP_TAC[]);;

(* An event that cuts no neck must discard something (rfs_slab_maximal). *)

let P3H_NECKLESS_EVENT_DISCARDS = prove
 (`!hs:(A)rfs_history k.
        rfs_history_ok hs /\ 1 <= k /\ k <= hs_count hs /\
        rfs_slab_maximal hs (k - 1) /\ ev_index(hs_event hs k) = {}
        ==> ~(ev_disc(hs_event hs k) = {})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [rfs_history_ok]) THEN
  SUBGOAL_THEN `k - 1 <= hs_count (hs:(A)rfs_history) /\ (k - 1) + 1 = k`
  STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `hausdorff_space (hs_top hs (k - 1)) /\
    smooth_manifold_atlas (hs_top hs (k - 1)) (hs_atlas hs (k - 1)) /\
    compact_space (hs_top hs (k - 1)) /\
    ricci_flow_from (hs_top hs (k - 1),hs_atlas hs (k - 1)) (hs_time hs (k - 1))
                    (hs_time (hs:(A)rfs_history) k) (hs_metric hs (k - 1))`
  STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `k - 1` o
      check (fun th -> can (find_term (fun t -> is_const t &&
                                       fst(dest_const t) = "ricci_flow_from")) (concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `rfs_event_ok (hs_top hs (k - 1),hs_atlas hs (k - 1)) (hs_metric hs (k - 1))
                 (hs_time hs k) (hs_top hs k,hs_atlas hs k) (hs_metric hs k)
                 (hs_event (hs:(A)rfs_history) k)`
  MP_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[rfs_event_ok] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `topspace(ev_ztop(hs_event (hs:(A)rfs_history) k)) = topspace(hs_top hs (k - 1))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P3H_CUT_EMPTY_TOPSPACE THEN
    MAP_EVERY EXISTS_TAC [`hs_atlas (hs:(A)rfs_history) (k - 1)`;
                          `ev_zatlas(hs_event (hs:(A)rfs_history) k)`;
                          `ev_neck(hs_event (hs:(A)rfs_history) k)`;
                          `ev_capp(hs_event (hs:(A)rfs_history) k)`;
                          `ev_capm(hs_event (hs:(A)rfs_history) k)`] THEN
    FIRST_X_ASSUM(fun th -> MP_TAC th THEN ASM_REWRITE_TAC[] THEN NO_TAC) ORELSE
    (UNDISCH_TAC `mfd_cut_cap (hs_top hs (k - 1)) (hs_atlas hs (k - 1))
                    (ev_ztop (hs_event hs k)) (ev_zatlas (hs_event hs k))
                    (ev_index (hs_event hs k)) (ev_neck (hs_event hs k))
                    (ev_capp (hs_event hs k)) (ev_capm (hs_event (hs:(A)rfs_history) k))
                    (\x. x) (\x. x)` THEN ASM_REWRITE_TAC[]);
    ALL_TAC] THEN
  SUBGOAL_THEN
   `topspace(hs_top hs (k - 1)) SUBSET ev_omega(hs_event (hs:(A)rfs_history) k)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `topspace (hs_top hs k) INTER topspace (hs_top hs (k - 1)) SUBSET
                 ev_omega (hs_event (hs:(A)rfs_history) k)` THEN
    UNDISCH_TAC `hs_top hs k = subtopology (ev_ztop (hs_event hs k))
                   (topspace (ev_ztop (hs_event hs k)) DIFF ev_disc (hs_event (hs:(A)rfs_history) k))` THEN
    DISCH_THEN SUBST1_TAC THEN
    ASM_REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; DIFF_EMPTY] THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`hs_top (hs:(A)rfs_history) (k - 1)`; `hs_atlas (hs:(A)rfs_history) (k - 1)`;
                 `hs_time (hs:(A)rfs_history) (k - 1)`;
                 `ev_omega(hs_event (hs:(A)rfs_history) k)`; `hs_time (hs:(A)rfs_history) k`;
                 `hs_metric (hs:(A)rfs_history) (k - 1)`;
                 `ev_limit(hs_event (hs:(A)rfs_history) k)`] P3H_LIMIT_RM_BOUND) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MP_TAC(SPEC `k - 1` (CONJUNCT1(CONJUNCT2(REWRITE_RULE[rfs_history_ok]
         (ASSUME `rfs_history_ok (hs:(A)rfs_history)`))))) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[];
      REPEAT STRIP_TAC THEN
      MP_TAC(ISPECL [`hs_top (hs:(A)rfs_history) (k - 1)`; `hs_atlas (hs:(A)rfs_history) (k - 1)`;
                     `hs_time (hs:(A)rfs_history) (k - 1)`; `hs_time (hs:(A)rfs_history) k`;
                     `hs_metric (hs:(A)rfs_history) (k - 1)`; `t:real`]
                    RFA_RICCI_FLOW_FROM_METRIC) THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (X_CHOOSE_THEN `B1:real` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`hs_top (hs:(A)rfs_history) (k - 1)`; `hs_atlas (hs:(A)rfs_history) (k - 1)`;
                 `hs_time (hs:(A)rfs_history) (k - 1)`; `hs_time (hs:(A)rfs_history) k`;
                 `hs_time (hs:(A)rfs_history) k - d / &2`;
                 `hs_metric (hs:(A)rfs_history) (k - 1)`] P3H_RF_RM_BOUND_COMPACT_TIME) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `&0 < d` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `B2:real` (LABEL_TAC "b2")) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `max B1 B2` o REWRITE_RULE[rfs_slab_maximal] o
    check (fun th -> concl th = `rfs_slab_maximal (hs:(A)rfs_history) (k - 1)`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real` (X_CHOOSE_THEN `x:A` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `t < hs_time (hs:(A)rfs_history) k` ASSUME_TAC THENL
   [UNDISCH_TAC `t < hs_time (hs:(A)rfs_history) (k - 1 + 1)` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `max B1 B2 < mfd_rm_norm (hs_atlas hs (k - 1))
                 (hs_metric hs (k - 1) t) (x:A)` THEN
  ASM_CASES_TAC `t <= hs_time (hs:(A)rfs_history) k - d / &2` THENL
   [USE_THEN "b2" (MP_TAC o SPECL [`t:real`; `x:A`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN REAL_ARITH_TAC;
    FIRST_X_ASSUM(MP_TAC o SPECL [`t:real`; `x:A`] o
      check (fun th -> can (find_term ((=) `B1:real`)) (concl th) && is_forall(concl th))) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `~(t <= hs_time (hs:(A)rfs_history) k - d / &2)` THEN
      UNDISCH_TAC `&0 < d` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    REAL_ARITH_TAC]);;

