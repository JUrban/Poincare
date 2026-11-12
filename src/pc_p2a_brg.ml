(* ========================================================================= *)
(* pc_p2a_brg: the history bridge O3, P2A_ROUTE_BRIDGE_X                     *)
(* (P2A_REQ_RLOWER ==> P2A_HIST_VIEW_X), proved clause by clause for the     *)
(* view rfs_view hs of a history with rfs_history_ok hs.                     *)
(* The first part: slices of a history view (smooth view setting, compact    *)
(* slices), regions from persisting sets (any a < b), smooth points,         *)
(* compact boxes and open space-time sets in the view vocabulary.            *)
(* ========================================================================= *)

needs "src/pc_p2a_smx.ml";;
needs "src/pc_p2a_hreg.ml";;
needs "src/pc_rfa_screq.ml";;
needs "src/pc_grg_area.ml";;

prioritize_real();;
type_invention_error := true;;

(* Slices outside [0,horizon) are empty; a live time lies in a stage.        *)

let P2AB_DEAD = prove
 (`!(hs:(A)rfs_history) t.
     ~(&0 <= t /\ t < rfs_horizon hs)
     ==> rfs_top_at hs t = discrete_topology {} /\ rfs_atlas_at hs t = {}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rfs_top_at; rfs_atlas_at; rfs_live; rfs_horizon] THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[]);;

let P2AB_LIVE = prove
 (`!(hs:(A)rfs_history) t.
     rfs_history_ok hs /\ &0 <= t /\ t < rfs_horizon hs
     ==> ?k. k <= hs_count hs /\ hs_time hs k <= t /\ t < hs_time hs (k + 1) /\
             hausdorff_space (hs_top hs k) /\ compact_space (hs_top hs k) /\
             smooth_manifold_atlas (hs_top hs k) (hs_atlas hs k) /\
             ricci_flow_from (hs_top hs k,hs_atlas hs k) (hs_time hs k) (hs_time hs (k + 1))
                             (hs_metric hs k) /\
             rfs_top_at hs t = hs_top hs k /\ rfs_atlas_at hs t = hs_atlas hs k /\
             rfs_metric_at hs t = hs_metric hs k t`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `t:real`] P2AH_SLAB_EXISTS) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC o SPEC `k:num` o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o
    GEN_REWRITE_RULE I [rfs_history_ok]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `k:num`; `t:real`] APX_RFS_SLAB) THEN
  ASM_SIMP_TAC[]);;

(* Clauses 1 and 2 of P2A_HIST_VIEW_X: the smooth view setting and compact  *)
(* slices.                                                                   *)

let P2AB_SVS = prove
 (`!hs:(A)rfs_history. rfs_history_ok hs ==> p2a_svs (rfs_view hs)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[p2a_svs; P2A_VIEW_PROJ_3; P2A_RFS_VIEW_COMPONENTS] THEN
  X_GEN_TAC `t:real` THEN
  ASM_CASES_TAC `&0 <= t /\ t < rfs_horizon (hs:(A)rfs_history)` THENL
   [MP_TAC(ISPECL [`hs:(A)rfs_history`; `t:real`] P2AB_LIVE) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`hs_top (hs:(A)rfs_history) k`; `hs_atlas (hs:(A)rfs_history) k`;
                   `hs_time (hs:(A)rfs_history) k`; `hs_time (hs:(A)rfs_history) (k + 1)`;
                   `hs_metric (hs:(A)rfs_history) k`; `t:real`]
                  RFA_RICCI_FLOW_FROM_METRIC) THEN
    ASM_SIMP_TAC[];
    MP_TAC(ISPECL [`hs:(A)rfs_history`; `t:real`] P2AB_DEAD) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN
    ASM_REWRITE_TAC[HAUSDORFF_SPACE_DISCRETE_TOPOLOGY; TOPSPACE_DISCRETE_TOPOLOGY]]);;

let P2AB_COMPACT = prove
 (`!(hs:(A)rfs_history) t. rfs_history_ok hs ==> compact_space (rfs_top_at hs t)`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `&0 <= t /\ t < rfs_horizon (hs:(A)rfs_history)` THENL
   [MP_TAC(ISPECL [`hs:(A)rfs_history`; `t:real`] P2AB_LIVE) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`hs:(A)rfs_history`; `t:real`] P2AB_DEAD) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[COMPACT_SPACE_DISCRETE_TOPOLOGY; FINITE_EMPTY]]);;

(* Regions: a persisting set over (a,b] is a region of the view (the region *)
(* part of P2C_HISTORY_REGULAR, P2AH_P2C_REGIONS, in the view vocabulary).  *)

let P2AB_RMETRIC_VFAM = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) W b.
     p2a_rmetric V W b = p2c_vfam V W b`,
  REWRITE_TAC[FUN_EQ_THM; p2a_rmetric; p2c_vfam; P2A_VIEW_PROJ_3]);;

let P2AB_REGION = prove
 (`!(hs:(A)rfs_history) W a b.
     rfs_history_ok hs /\ a < b /\ rfs_persists (rfs_view hs) W a b
     ==> p2a_region (rfs_view hs) W a b`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `hs:(A)rfs_history` P2AH_P2C_REGIONS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o SPECL [`W:A->bool`; `a:real`; `b:real`])
    (MP_TAC o SPECL [`W:A->bool`; `a:real`; `b:real`] o CONJUNCT2)) THEN
  ASM_REWRITE_TAC[p2c_vflow] THEN DISCH_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[p2a_region; P2A_PERSISTS_3; P2A_VIEW_PROJ_3; P2AB_RMETRIC_VFAM;
                  P2A_FLOW_UPTO_3]);;

(* Clause 4: smooth points of the history are two-sided smooth points of    *)
(* the view (the persisting set persists until the end of its stage).       *)

let P2AB_SMOOTH_PT = prove
 (`!(hs:(A)rfs_history) y t.
     rfs_history_ok hs /\ &0 < t /\ rfs_smooth_pt hs y t
     ==> p2a_smooth (rfs_view hs) y t`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rfs_smooth_pt; p2a_smooth] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `U:A->bool` (X_CHOOSE_THEN `eta:real` STRIP_ASSUME_TAC)))) THEN
  FIRST_ASSUM(LABEL_TAC "P" o GEN_REWRITE_RULE I [P2AH_PERSISTS]) THEN
  SUBGOAL_THEN `&0 <= t /\ t < rfs_horizon (hs:(A)rfs_history)` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC P2A_TOPSPACE_LIVE THEN EXISTS_TAC `y:A` THEN
    USE_THEN "P" (MP_TAC o SPEC `t:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o MATCH_MP OPEN_IN_SUBSET o CONJUNCT2) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `t:real`] P2AB_LIVE) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`U:A->bool`; `t - eta`;
                        `(t + hs_time (hs:(A)rfs_history) (k + 1)) / &2`] THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
  MATCH_MP_TAC P2AB_REGION THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[P2AH_PERSISTS] THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN
  ASM_CASES_TAC `s <= t` THENL
   [USE_THEN "P" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `k:num`; `s:real`] APX_RFS_SLAB) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  USE_THEN "P" (MP_TAC o SPEC `t:real`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]]);;

(* Clauses 12 and 13: compact boxes and open space-time sets.               *)

let P2AB_CBOX = prove
 (`!(hs:(A)rfs_history) K.
     rfs_history_ok hs /\ p3_st_compact hs K ==> p2a_cbox (rfs_view hs) K`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p3_st_compact; p2a_cbox] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[P2A_VIEW_PROJ_3; P2A_RFS_VIEW_COMPONENTS] THEN
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> try fst(dest_const t) = "rfs_persists" with Failure _ -> false))
        (concl th))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P2AB_REGION THEN ASM_REWRITE_TAC[] THEN
  ASM_REAL_ARITH_TAC);;

let P2AB_ST_OPEN = prove
 (`!(hs:(A)rfs_history) U a b. p3_st_open hs U a b ==> p2a_st_open (rfs_view hs) U a b`,
  REWRITE_TAC[p3_st_open; p2a_st_open; P2A_PERSISTS_3]);;

(* ------------------------------------------------------------------------- *)
(* Curves.  Clause 5 (an admissible curve of the history is an admx curve  *)
(* of the view, with corner set the event times), and clause 8 (a          *)
(* corner-free admissible curve of the view is admissible for the          *)
(* history), using the local nature of C^1 on subsets of real^1 without    *)
(* isolated points (P2AB_CD1_LOCAL).                                       *)
(* ------------------------------------------------------------------------- *)

let P2AB_L_INTEGRAND_VIEW = prove
 (`!(hs:(A)rfs_history) tt gamma b.
     p2a_L_integrand (rfs_view hs) tt gamma b = rfs_L_integrand hs tt gamma b`,
  REWRITE_TAC[FUN_EQ_THM; rfs_L_integrand; p2a_L_integrand;
              rfs_view; p2a_vatlas; p2a_vmetric]);;

let P2AB_STAGE_ATLAS = prove
 (`!(hs:(A)rfs_history) k t.
     rfs_history_ok hs /\ k <= hs_count hs /\ hs_time hs k <= t /\ t < hs_time hs (k + 1)
     ==> rfs_atlas_at hs t = hs_atlas hs k`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `k:num`; `t:real`] APX_RFS_SLAB) THEN
  ASM_SIMP_TAC[]);;

let P2AB_STAGE_CHART_OPEN = prove
 (`!(hs:(A)rfs_history) k t (c:(A->bool)#(A->real^3)).
     rfs_history_ok hs /\ k <= hs_count hs /\ c IN hs_atlas hs k /\
     hs_time hs k <= t /\ t < hs_time hs (k + 1)
     ==> open_in (rfs_top_at hs t) (FST c)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `k:num`; `t:real`] APX_RFS_SLAB) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `k:num`] P2AH_STAGE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`hs_top (hs:(A)rfs_history) k`; `hs_atlas (hs:(A)rfs_history) k`;
                 `c:(A->bool)#(A->real^3)`] MFDM_CHART) THEN
  ASM_SIMP_TAC[]);;

(* Off the event times an admissible curve of the history is C^1 in the     *)
(* charts of its stage on both sides.                                        *)

let P2AB_PC1X = prove
 (`!(hs:(A)rfs_history) tt (gamma:real->A) b.
     rfs_history_ok hs /\ rfs_st_curve hs tt gamma (&0) b
     ==> p2a_pc1x (rfs_view hs) tt gamma (&0) b
           (IMAGE (\k. tt - hs_time hs k) {k | k <= hs_count hs + 1})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[p2a_pc1x; P2A_VIEW_PROJ_3; P2A_RFS_VIEW_COMPONENTS] THEN
  SIMP_TAC[FINITE_IMAGE; FINITE_NUMSEG_LE] THEN
  MAP_EVERY X_GEN_TAC [`s0:real`; `c:(A->bool)#(A->real^3)`] THEN STRIP_TAC THEN
  ASM_CASES_TAC `&0 <= tt - s0 /\ tt - s0 < rfs_horizon (hs:(A)rfs_history)` THENL
   [ALL_TAC;
    MP_TAC(ISPECL [`hs:(A)rfs_history`; `tt - s0`] P2AB_DEAD) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN UNDISCH_TAC `(c:(A->bool)#(A->real^3)) IN rfs_atlas_at hs (tt - s0)` THEN
    ASM_REWRITE_TAC[NOT_IN_EMPTY]] THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `tt - s0`] P2AH_SLAB_EXISTS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(c:(A->bool)#(A->real^3)) IN hs_atlas hs k` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`hs:(A)rfs_history`; `k:num`; `tt - s0`] P2AB_STAGE_ATLAS) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(tt - s0 = hs_time (hs:(A)rfs_history) k)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    UNDISCH_TAC `~((s0:real) IN IMAGE (\k. tt - hs_time (hs:(A)rfs_history) k)
                                      {k | k <= hs_count hs + 1})` THEN
    REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN EXISTS_TAC `k:num` THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM_ARITH_TAC];
    ALL_TAC] THEN
  EXISTS_TAC `min (tt - s0 - hs_time (hs:(A)rfs_history) k)
                  (hs_time hs (k + 1) - (tt - s0)) / &2` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_SUBSET THEN
  EXISTS_TAC `{s | &0 < drop s /\ drop s <= b /\
                   hs_time (hs:(A)rfs_history) k <= tt - drop s /\
                   tt - drop s < hs_time hs (k + 1) /\
                   (gamma:real->A)(drop s) IN FST (c:(A->bool)#(A->real^3))}` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `s:real^1` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    UNDISCH_TAC `rfs_st_curve hs tt (gamma:real->A) (&0) b` THEN
    REWRITE_TAC[rfs_st_curve] THEN
    DISCH_THEN(MP_TAC o SPECL [`k:num`; `c:(A->bool)#(A->real^3)`] o last o CONJUNCTS) THEN
    ASM_REWRITE_TAC[]]);;

(* Clause 5.                                                                 *)

let P2AB_ADMX = prove
 (`!(hs:(A)rfs_history) tt x b gamma.
     rfs_history_ok hs /\ b < tt /\ rfs_L_adm hs tt x b gamma
     ==> p2a_admx (rfs_view hs) tt x b gamma`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rfs_L_adm] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [rfs_st_curve]) THEN
  ASM_REWRITE_TAC[p2a_admx; P2A_VIEW_PROJ_3; P2A_RFS_VIEW_COMPONENTS;
                  P2AB_L_INTEGRAND_VIEW] THEN
  CONJ_TAC THENL
   [EXISTS_TAC `IMAGE (\k. tt - hs_time (hs:(A)rfs_history) k) {k | k <= hs_count hs + 1}` THEN
    MATCH_MP_TAC P2AB_PC1X THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `tau:real` THEN STRIP_TAC THEN MATCH_MP_TAC P2AB_SMOOTH_PT THEN
    ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC]);;

(* Local C^1 on a subset of real^1 without isolated points is C^1.          *)

let P2AB_CD1_LOCAL = prove
 (`!(f:real^1->real^N) S.
     (!x. x IN S
          ==> ?d Q. &0 < d /\ (!y. y IN S /\ dist(y,x) < d ==> y IN Q) /\
                    continuously_differentiable 1 Q f) /\
     (!x e. x IN S /\ &0 < e ==> ?y. y IN S /\ ~(y = x) /\ dist(y,x) < e)
     ==> continuously_differentiable 1 S f`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "L") (LABEL_TAC "N")) THEN
  SUBGOAL_THEN
   `!x. x IN S
        ==> ?d f'. &0 < d /\
                   (!y. y IN S /\ dist(y,x) < d
                        ==> ((f:real^1->real^N) has_derivative f' y) (at y within S)) /\
                   (!h. (\y. f' y h) continuous (at x within S))`
  (LABEL_TAC "A") THENL
   [X_GEN_TAC `x:real^1` THEN DISCH_TAC THEN
    USE_THEN "L" (MP_TAC o SPEC `x:real^1`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` (X_CHOOSE_THEN `Q:real^1->bool`
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)))) THEN
    REWRITE_TAC[CONTINUOUSLY_DIFFERENTIABLE_1] THEN
    DISCH_THEN(X_CHOOSE_THEN `f':real^1->real^1->real^N`
      (CONJUNCTS_THEN2 (LABEL_TAC "D") (LABEL_TAC "C"))) THEN
    MAP_EVERY EXISTS_TAC [`d:real`; `f':real^1->real^1->real^N`] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `open_in (subtopology euclidean S) (S INTER ball(x:real^1,d))` ASSUME_TAC THENL
     [MATCH_MP_TAC OPEN_IN_OPEN_INTER THEN REWRITE_TAC[OPEN_BALL]; ALL_TAC] THEN
    SUBGOAL_THEN `(S INTER ball(x:real^1,d)) SUBSET Q` ASSUME_TAC THENL
     [REWRITE_TAC[SUBSET; IN_INTER; IN_BALL] THEN ASM_MESON_TAC[DIST_SYM]; ALL_TAC] THEN
    CONJ_TAC THENL
     [X_GEN_TAC `y:real^1` THEN STRIP_TAC THEN
      SUBGOAL_THEN `(y:real^1) IN S INTER ball(x,d)` ASSUME_TAC THENL
       [ASM_REWRITE_TAC[IN_INTER; IN_BALL] THEN ASM_MESON_TAC[DIST_SYM]; ALL_TAC] THEN
      MP_TAC(ISPECL [`f:real^1->real^N`; `(f':real^1->real^1->real^N) y`; `y:real^1`;
                     `S INTER ball(x:real^1,d)`; `S:real^1->bool`]
                    HAS_DERIVATIVE_WITHIN_OPEN_IN) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      MATCH_MP_TAC HAS_DERIVATIVE_WITHIN_SUBSET THEN EXISTS_TAC `Q:real^1->bool` THEN
      ASM_REWRITE_TAC[] THEN USE_THEN "D" MATCH_MP_TAC THEN ASM SET_TAC[];
      X_GEN_TAC `h:real^1` THEN
      SUBGOAL_THEN `(x:real^1) IN S INTER ball(x,d)` ASSUME_TAC THENL
       [ASM_REWRITE_TAC[IN_INTER; CENTRE_IN_BALL]; ALL_TAC] THEN
      MP_TAC(ISPECL [`\y. (f':real^1->real^1->real^N) y h`; `x:real^1`; `S:real^1->bool`;
                     `S INTER ball(x:real^1,d)`] CONTINUOUS_WITHIN_OPEN_IN) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      MATCH_MP_TAC CONTINUOUS_WITHIN_SUBSET THEN EXISTS_TAC `Q:real^1->bool` THEN
      ASM_REWRITE_TAC[] THEN
      USE_THEN "C" (MP_TAC o SPEC `h:real^1`) THEN
      REWRITE_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y D1 D2. y IN S /\ ((f:real^1->real^N) has_derivative D1) (at y within S) /\
              (f has_derivative D2) (at y within S) ==> D1 = D2`
  (LABEL_TAC "U") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC FRECHET_DERIVATIVE_UNIQUE_WITHIN THEN
    MAP_EVERY EXISTS_TAC [`f:real^1->real^N`; `y:real^1`; `S:real^1->bool`] THEN
    ASM_REWRITE_TAC[DIMINDEX_1] THEN
    MAP_EVERY X_GEN_TAC [`i:num`; `e:real`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `i = 1` SUBST_ALL_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "N" (MP_TAC o SPECL [`y:real^1`; `e:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `z:real^1` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `drop(z - y)` THEN
    SUBGOAL_THEN `abs(drop(z - y)) = dist(z:real^1,y)` SUBST1_TAC THENL
     [REWRITE_TAC[dist; NORM_REAL; drop]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_MESON_TAC[DIST_POS_LT]; ALL_TAC] THEN
    SUBGOAL_THEN `y + drop(z - y) % basis 1 = z:real^1` SUBST1_TAC THENL
     [SIMP_TAC[CART_EQ; DIMINDEX_1; FORALL_1; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
               BASIS_COMPONENT; drop; VECTOR_SUB_COMPONENT; ARITH] THEN REAL_ARITH_TAC;
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `FD = \y:real^1. @D. ((f:real^1->real^N) has_derivative D) (at y within S)` THEN
  SUBGOAL_THEN `!y. y IN S ==> ((f:real^1->real^N) has_derivative FD y) (at y within S)`
  (LABEL_TAC "FD") THENL
   [X_GEN_TAC `y:real^1` THEN DISCH_TAC THEN EXPAND_TAC "FD" THEN
    CONV_TAC SELECT_CONV THEN
    USE_THEN "A" (MP_TAC o SPEC `y:real^1`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` (X_CHOOSE_THEN `f':real^1->real^1->real^N`
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "DD") (K ALL_TAC))))) THEN
    EXISTS_TAC `(f':real^1->real^1->real^N) y` THEN USE_THEN "DD" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[DIST_REFL];
    ALL_TAC] THEN
  REWRITE_TAC[CONTINUOUSLY_DIFFERENTIABLE_1] THEN
  EXISTS_TAC `FD:real^1->real^1->real^N` THEN
  CONJ_TAC THENL [USE_THEN "FD" ACCEPT_TAC; ALL_TAC] THEN
  X_GEN_TAC `h:real^1` THEN REWRITE_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
  X_GEN_TAC `x:real^1` THEN DISCH_TAC THEN
  USE_THEN "A" (MP_TAC o SPEC `x:real^1`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (X_CHOOSE_THEN `f':real^1->real^1->real^N`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "DD") (LABEL_TAC "CC"))))) THEN
  MATCH_MP_TAC CONTINUOUS_TRANSFORM_WITHIN THEN
  MAP_EVERY EXISTS_TAC [`\y. (f':real^1->real^1->real^N) y h`; `d:real`] THEN
  ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `y:real^1` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  AP_THM_TAC THEN USE_THEN "U" MATCH_MP_TAC THEN EXISTS_TAC `y:real^1` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [USE_THEN "DD" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    USE_THEN "FD" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* A corner-free admissible curve of the view is a space-time curve of the  *)
(* history: C^1 in every chart on the times spent in each stage.             *)

let P2AB_ST_CURVE = prove
 (`!(hs:(A)rfs_history) tt x b (gamma:real->A).
     rfs_history_ok hs /\ p2a_adm (rfs_view hs) tt x b gamma /\
     p2a_pc1 (rfs_view hs) tt gamma (&0) b {}
     ==> rfs_st_curve hs tt gamma (&0) b`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 MP_TAC MP_TAC)) THEN
  REWRITE_TAC[p2a_pc1; NOT_IN_EMPTY; FINITE_EMPTY; P2A_VIEW_PROJ_3;
              P2A_RFS_VIEW_COMPONENTS] THEN
  DISCH_THEN(LABEL_TAC "PC") THEN
  REWRITE_TAC[p2a_adm; P2A_VIEW_PROJ_3; P2A_RFS_VIEW_COMPONENTS] THEN STRIP_TAC THEN
  REWRITE_TAC[rfs_st_curve] THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
  MAP_EVERY X_GEN_TAC [`k:num`; `c:(A->bool)#(A->real^3)`] THEN STRIP_TAC THEN
  MATCH_MP_TAC P2AB_CD1_LOCAL THEN CONJ_TAC THENL
   [X_GEN_TAC `z:real^1` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
    USE_THEN "PC" (MP_TAC o SPECL [`drop z`; `c:(A->bool)#(A->real^3)`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`hs:(A)rfs_history`; `k:num`; `tt - drop z`] P2AB_STAGE_ATLAS) THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC) ASSUME_TAC)))) THEN
    EXISTS_TAC `d:real` THEN
    EXISTS_TAC `{s | drop z - d <= drop s /\ drop s <= drop z + d /\
                     &0 < drop s /\ drop s <= b /\
                     rfs_atlas_at hs (tt - drop s) =
                     rfs_atlas_at (hs:(A)rfs_history) (tt - drop z) /\
                     (gamma:real->A)(drop s) IN FST (c:(A->bool)#(A->real^3))}` THEN
    REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      X_GEN_TAC `y:real^1` THEN REWRITE_TAC[IN_ELIM_THM; DIST_REAL; GSYM drop] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`hs:(A)rfs_history`; `k:num`; `tt - drop y`] P2AB_STAGE_ATLAS) THEN
      MP_TAC(ISPECL [`hs:(A)rfs_history`; `k:num`; `tt - drop z`] P2AB_STAGE_ATLAS) THEN
      ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC;
      FIRST_ASSUM ACCEPT_TAC];
    MAP_EVERY X_GEN_TAC [`z:real^1`; `e:real`] THEN REWRITE_TAC[IN_ELIM_THM] THEN
    STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`drop z`; `FST(c:(A->bool)#(A->real^3))`] o
      check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> try fst(dest_const t) = "open_in" with Failure _ -> false))
            (concl th))) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN MATCH_MP_TAC P2AB_STAGE_CHART_OPEN THEN
      EXISTS_TAC `k:num` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `d':real` STRIP_ASSUME_TAC) THEN
    ABBREV_TAC `r = min (min (min (drop z) (drop z - (tt - hs_time (hs:(A)rfs_history) (k + 1))))
                             e) d' / &2` THEN
    SUBGOAL_THEN `&0 < r /\ r < drop z /\ r < drop z - (tt - hs_time (hs:(A)rfs_history) (k + 1)) /\
                  r < e /\ r < d'` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "r" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    EXISTS_TAC `lift(drop z - r)` THEN
    REWRITE_TAC[IN_ELIM_THM; LIFT_DROP; GSYM DROP_EQ;
                dist; NORM_REAL; GSYM drop; DROP_SUB] THEN
    REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC]);;

(* Clause 8.                                                                 *)

let P2AB_ADM1_LADM = prove
 (`!(hs:(A)rfs_history) tt x b gamma.
     rfs_history_ok hs /\ p2a_adm1 (rfs_view hs) tt x b gamma
     ==> rfs_L_adm hs tt x b gamma`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2a_adm1] THEN STRIP_TAC THEN
  SUBGOAL_THEN `rfs_st_curve hs tt (gamma:real->A) (&0) b` ASSUME_TAC THENL
   [MATCH_MP_TAC P2AB_ST_CURVE THEN EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [p2a_adm]) THEN
  REWRITE_TAC[P2A_VIEW_PROJ_3; P2A_RFS_VIEW_COMPONENTS; P2AB_L_INTEGRAND_VIEW] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[rfs_L_adm] THEN
  X_GEN_TAC `tau:real` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `tau:real` o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> try fst(dest_const t) = "p2a_smooth" with Failure _ -> false))
        (concl th))) THEN
  ASM_REWRITE_TAC[p2a_smooth; rfs_smooth_pt] THEN
  DISCH_THEN(X_CHOOSE_THEN `W:A->bool` (X_CHOOSE_THEN `a:real` (X_CHOOSE_THEN `c:real`
    STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`W:A->bool`; `tt - tau - a`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [p2a_region]) THEN
  REWRITE_TAC[P2A_PERSISTS_3; P2AH_PERSISTS] THEN DISCH_TAC THEN
  X_GEN_TAC `s:real` THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Lengths.  The scalar curvature of a history is bounded below             *)
(* (P2A_REQ_RLOWER on each stage), so L-lengths of curves on [0,b] are      *)
(* bounded below and the infima Lx are attained in the limit.  Clause 7 (Lx *)
(* is at most the length of an admissible curve), clauses 9 and 10 (minimal *)
(* L-geodesics of the history and minimizers of the view), clause 11 (the   *)
(* two infima Lx agree), via the smoothing of admx curves.                  *)
(* ------------------------------------------------------------------------- *)

let P2AB_LE_EPS = prove
 (`!x y. (!e. &0 < e ==> x <= y + e) ==> x <= y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(x - y) / &2`) THEN ASM_REAL_ARITH_TAC);;

let P2AB_INF_APPROX = prove
 (`!s t. ~(s = {}) /\ ~(t = {}) /\
         (?a. !x. x IN s ==> a <= x) /\ (?a. !x. x IN t ==> a <= x) /\
         (!x e. x IN s /\ &0 < e ==> ?y. y IN t /\ y <= x + e) /\
         (!y e. y IN t /\ &0 < e ==> ?x. x IN s /\ x <= y + e)
         ==> inf s = inf t`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "ST") (LABEL_TAC "TS")))))) THEN
  MP_TAC(ISPEC `s:real->bool` INF) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(LABEL_TAC "IS" o CONJUNCT1) THEN
  MP_TAC(ISPEC `t:real->bool` INF) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(LABEL_TAC "IT" o CONJUNCT1) THEN
  REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN CONJ_TAC THEN
  MATCH_MP_TAC REAL_LE_INF THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `z:real` THEN DISCH_TAC THEN MATCH_MP_TAC P2AB_LE_EPS THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THENL
   [USE_THEN "TS" (MP_TAC o SPECL [`z:real`; `e:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `w:real` STRIP_ASSUME_TAC) THEN
    USE_THEN "IS" (MP_TAC o SPEC `w:real`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN ASM_REAL_ARITH_TAC;
    USE_THEN "ST" (MP_TAC o SPECL [`z:real`; `e:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `w:real` STRIP_ASSUME_TAC) THEN
    USE_THEN "IT" (MP_TAC o SPEC `w:real`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN ASM_REAL_ARITH_TAC]);;

(* The lower bound for the scalar curvature over the whole history.          *)

let P2AB_SCALAR_LOWER = prove
 (`!(u:A->bool) (hs:(A)rfs_history).
     P2A_REQ_RLOWER_STATEMENT u /\ rfs_history_ok hs
     ==> ?m. !t y. y IN topspace(rfs_top_at hs t)
                   ==> m <= mfd_scalar (rfs_atlas_at hs t) (rfs_metric_at hs t) y`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\k. min (&0) (inf {mfd_scalar (hs_atlas (hs:(A)rfs_history) k)
                                         (hs_metric hs k (hs_time hs k)) z | z |
                                     z IN topspace(hs_top hs k)})`;
                 `{k:num | k <= hs_count (hs:(A)rfs_history)}`]
                LOWER_BOUND_FINITE_SET_REAL) THEN
  REWRITE_TAC[FINITE_NUMSEG_LE; IN_ELIM_THM] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `m:real` THEN DISCH_THEN(LABEL_TAC "M") THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `y:A`] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= t /\ t < rfs_horizon (hs:(A)rfs_history)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[P2A_TOPSPACE_LIVE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `t:real`] P2AB_LIVE) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC) THEN
  USE_THEN "M" (MP_TAC o SPEC `k:num`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REAL_ARITH `x <= y ==> m <= x ==> m <= y`) THEN
  UNDISCH_TAC `P2A_REQ_RLOWER_STATEMENT (u:A->bool)` THEN
  REWRITE_TAC[P2A_REQ_RLOWER_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPECL [`hs_top (hs:(A)rfs_history) k`; `hs_atlas (hs:(A)rfs_history) k`;
                             `hs_time (hs:(A)rfs_history) k`;
                             `hs_time (hs:(A)rfs_history) (k + 1)`;
                             `hs_metric (hs:(A)rfs_history) k`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  UNDISCH_TAC `(y:A) IN topspace(rfs_top_at hs t)` THEN ASM_REWRITE_TAC[]);;

(* L-lengths of curves in the slices are bounded below.                      *)

let P2AB_LENGTH_LOWER = prove
 (`!(hs:(A)rfs_history) m tt (gamma:real->A) b.
     (!t y. y IN topspace(rfs_top_at hs t)
            ==> m <= mfd_scalar (rfs_atlas_at hs t) (rfs_metric_at hs t) y) /\
     &0 < b /\
     (!tau. &0 <= tau /\ tau <= b ==> gamma tau IN topspace(rfs_top_at hs (tt - tau))) /\
     rfs_L_integrand hs tt gamma b real_integrable_on real_interval[&0,b]
     ==> --(abs m * sqrt b * b) <= rfs_L_length hs tt gamma b`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "M") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "S") ASSUME_TAC))) THEN
  REWRITE_TAC[rfs_L_length] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `real_integral (real_interval[&0,b]) (\tau:real. --(abs m * sqrt b))` THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[REAL_INTEGRAL_CONST; REAL_LT_IMP_LE] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_INTEGRAL_LE THEN ASM_REWRITE_TAC[REAL_INTEGRABLE_CONST] THEN
  X_GEN_TAC `tau:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
  REWRITE_TAC[rfs_L_integrand] THEN
  SUBGOAL_THEN
   `--abs m <= mfd_scalar (rfs_atlas_at hs (tt - tau)) (rfs_metric_at (hs:(A)rfs_history) (tt - tau))
                          ((gamma:real->A) tau) +
               mfd_speed (rfs_atlas_at hs (tt - tau)) (rfs_metric_at hs (tt - tau))
                         gamma (&0) b tau pow 2`
  ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `m <= x /\ &0 <= y ==> --abs m <= x + y`) THEN
    REWRITE_TAC[REAL_LE_POW_2] THEN USE_THEN "M" MATCH_MP_TAC THEN
    USE_THEN "S" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= sqrt tau /\ sqrt tau <= sqrt b` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LE; SQRT_MONO_LE]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt tau * --abs m` THEN CONJ_TAC THENL
   [SUBGOAL_THEN `&0 <= (sqrt b - sqrt tau) * abs m` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_ABS_POS] THEN ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC];
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]]);;

let P2AB_LADM_LOWER = prove
 (`!(hs:(A)rfs_history) m tt x (gamma:real->A) b.
     (!t y. y IN topspace(rfs_top_at hs t)
            ==> m <= mfd_scalar (rfs_atlas_at hs t) (rfs_metric_at hs t) y) /\
     rfs_L_adm hs tt x b gamma
     ==> --(abs m * sqrt b * b) <= rfs_L_length hs tt gamma b`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rfs_L_adm; rfs_st_curve] THEN STRIP_TAC THEN
  MATCH_MP_TAC P2AB_LENGTH_LOWER THEN ASM_REWRITE_TAC[]);;

let P2AB_ADM_LOWER = prove
 (`!(hs:(A)rfs_history) m tt x (gamma:real->A) b.
     (!t y. y IN topspace(rfs_top_at hs t)
            ==> m <= mfd_scalar (rfs_atlas_at hs t) (rfs_metric_at hs t) y) /\
     p2a_adm (rfs_view hs) tt x b gamma
     ==> --(abs m * sqrt b * b) <= p2a_L_length (rfs_view hs) tt gamma b`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[p2a_adm; P2A_VIEW_PROJ_3; P2A_RFS_VIEW_COMPONENTS; P2AB_L_INTEGRAND_VIEW;
              GSYM P2A_L_LENGTH_VIEW] THEN
  STRIP_TAC THEN MATCH_MP_TAC P2AB_LENGTH_LOWER THEN ASM_REWRITE_TAC[]);;

(* Clause 7.                                                                 *)

let P2AB_LX_LE = prove
 (`!(u:A->bool) (hs:(A)rfs_history) tt x b gamma.
     P2A_REQ_RLOWER_STATEMENT u /\ rfs_history_ok hs /\
     p2a_adm (rfs_view hs) tt x b gamma
     ==> p2a_Lx (rfs_view hs) tt x b (gamma b) <= p2a_L_length (rfs_view hs) tt gamma b`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`u:A->bool`; `hs:(A)rfs_history`] P2AB_SCALAR_LOWER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `m:real`) THEN
  REWRITE_TAC[p2a_Lx] THEN MATCH_MP_TAC REAL_INF_LE THEN
  MAP_EVERY EXISTS_TAC [`--(abs m * sqrt b * b)`;
                        `p2a_L_length (rfs_view hs) tt (gamma:real->A) b`] THEN
  REWRITE_TAC[REAL_LE_REFL; IN_ELIM_THM] THEN CONJ_TAC THENL
   [EXISTS_TAC `gamma:real->A` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `l:real` THEN DISCH_THEN(X_CHOOSE_THEN `g:real->A` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P2AB_ADM_LOWER THEN
  EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[]);;

(* Clause 9.                                                                 *)

let P2AB_MIN_LGEOD = prove
 (`!(u:A->bool) (hs:(A)rfs_history) tt x b gamma.
     P2A_REQ_RLOWER_STATEMENT u /\ rfs_history_ok hs /\ b < tt /\
     rfs_min_Lgeod hs tt x b gamma
     ==> p2a_min (rfs_view hs) tt x b gamma`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rfs_min_Lgeod] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`u:A->bool`; `hs:(A)rfs_history`] P2AB_SCALAR_LOWER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `m:real`) THEN
  SUBGOAL_THEN `p2a_svs (rfs_view (hs:(A)rfs_history)) /\ p2a_atlas_lc (rfs_view hs)`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[P2AB_SVS; P2A_ATLAS_LC_HIST]; ALL_TAC] THEN
  SUBGOAL_THEN `p2a_minx (rfs_view hs) tt x b (gamma:real->A)` ASSUME_TAC THENL
   [REWRITE_TAC[p2a_minx] THEN CONJ_TAC THENL
     [MATCH_MP_TAC P2AB_ADMX THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    X_GEN_TAC `g:real->A` THEN STRIP_TAC THEN MATCH_MP_TAC P2AB_LE_EPS THEN
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`rfs_view (hs:(A)rfs_history)`; `tt:real`; `x:A`; `b:real`;
                   `g:real->A`; `e:real`] P2AXS_SMOOTHING_X) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `g':real->A` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `rfs_L_adm hs tt x b (g':real->A)` ASSUME_TAC THENL
     [MATCH_MP_TAC P2AB_ADM1_LADM THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `p2a_L_length (rfs_view hs) tt (g':real->A) b` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM P2A_L_LENGTH_VIEW] THEN ASM_REWRITE_TAC[rfs_Lx] THEN
    MATCH_MP_TAC REAL_INF_LE THEN
    MAP_EVERY EXISTS_TAC [`--(abs m * sqrt b * b)`; `rfs_L_length hs tt (g':real->A) b`] THEN
    REWRITE_TAC[REAL_LE_REFL; IN_ELIM_THM] THEN CONJ_TAC THENL
     [EXISTS_TAC `g':real->A` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    X_GEN_TAC `l:real` THEN DISCH_THEN(X_CHOOSE_THEN `h:real->A` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P2AB_LADM_LOWER THEN
    EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`rfs_view (hs:(A)rfs_history)`; `tt:real`; `x:A`; `b:real`;
                 `gamma:real->A`] P2AXR_MINX_MIN) THEN
  ASM_SIMP_TAC[]);;

(* Clause 10.                                                                *)

let P2AB_LGEOD_MIN = prove
 (`!(u:A->bool) (hs:(A)rfs_history) tt x b gamma.
     P2A_REQ_RLOWER_STATEMENT u /\ rfs_history_ok hs /\ b < tt /\
     p2a_min (rfs_view hs) tt x b gamma /\ p2a_pc1 (rfs_view hs) tt gamma (&0) b {}
     ==> rfs_min_Lgeod hs tt x b gamma`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`u:A->bool`; `hs:(A)rfs_history`] P2AB_SCALAR_LOWER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `m:real`) THEN
  SUBGOAL_THEN `p2a_svs (rfs_view (hs:(A)rfs_history)) /\ p2a_atlas_lc (rfs_view hs)`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[P2AB_SVS; P2A_ATLAS_LC_HIST]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2a_min]) THEN
  SUBGOAL_THEN `rfs_L_adm hs tt x b (gamma:real->A)` ASSUME_TAC THENL
   [MATCH_MP_TAC P2AB_ADM1_LADM THEN ASM_REWRITE_TAC[p2a_adm1]; ALL_TAC] THEN
  ASM_REWRITE_TAC[rfs_min_Lgeod; rfs_Lx] THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC REAL_INF_UNIQUE THEN
  REWRITE_TAC[FORALL_IN_GSPEC; EXISTS_IN_GSPEC] THEN CONJ_TAC THENL
   [X_GEN_TAC `g:real->A` THEN STRIP_TAC THEN MATCH_MP_TAC P2AB_LE_EPS THEN
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`rfs_view (hs:(A)rfs_history)`; `tt:real`; `x:A`; `b:real`;
                   `g:real->A`; `e:real`] P2AXS_SMOOTHING_X) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P2AB_ADMX THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `g':real->A` STRIP_ASSUME_TAC) THEN
    REWRITE_TAC[P2A_L_LENGTH_VIEW] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `p2a_L_length (rfs_view hs) tt (g':real->A) b` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[p2a_adm1];
    X_GEN_TAC `l:real` THEN DISCH_TAC THEN EXISTS_TAC `gamma:real->A` THEN
    ASM_REWRITE_TAC[]]);;

(* Clause 11.                                                                *)

let P2AB_LX_EQ = prove
 (`!(u:A->bool) (hs:(A)rfs_history) tt x b q.
     P2A_REQ_RLOWER_STATEMENT u /\ rfs_history_ok hs /\ b < tt /\
     (?gamma. rfs_L_adm hs tt x b gamma /\ gamma b = q)
     ==> rfs_Lx hs tt x b q = p2a_Lx (rfs_view hs) tt x b q`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `gamma:real->A` STRIP_ASSUME_TAC)))) THEN
  MP_TAC(ISPECL [`u:A->bool`; `hs:(A)rfs_history`] P2AB_SCALAR_LOWER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `m:real`) THEN
  SUBGOAL_THEN `p2a_svs (rfs_view (hs:(A)rfs_history)) /\ p2a_atlas_lc (rfs_view hs)`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[P2AB_SVS; P2A_ATLAS_LC_HIST]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!g e. rfs_L_adm hs tt x b (g:real->A) /\ &0 < e
          ==> ?g'. p2a_adm (rfs_view hs) tt x b g' /\ g' b = g b /\
                   p2a_L_length (rfs_view hs) tt g' b <= rfs_L_length hs tt g b + e`
  (LABEL_TAC "S1") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`rfs_view (hs:(A)rfs_history)`; `tt:real`; `x:A`; `b:real`;
                   `g:real->A`; `e:real`] P2AXS_SMOOTHING_X) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P2AB_ADMX THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `g':real->A` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `g':real->A` THEN ASM_REWRITE_TAC[P2A_L_LENGTH_VIEW] THEN
    ASM_MESON_TAC[p2a_adm1];
    ALL_TAC] THEN
  REWRITE_TAC[rfs_Lx; p2a_Lx] THEN MATCH_MP_TAC P2AB_INF_APPROX THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM; FORALL_IN_GSPEC; EXISTS_IN_GSPEC] THEN
  REPEAT CONJ_TAC THENL
   [EXISTS_TAC `rfs_L_length hs tt (gamma:real->A) b` THEN
    EXISTS_TAC `gamma:real->A` THEN ASM_REWRITE_TAC[];
    USE_THEN "S1" (MP_TAC o SPECL [`gamma:real->A`; `&1`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LT_01]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `g':real->A` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `p2a_L_length (rfs_view hs) tt (g':real->A) b` THEN
    EXISTS_TAC `g':real->A` THEN ASM_REWRITE_TAC[];
    EXISTS_TAC `--(abs m * sqrt b * b)` THEN X_GEN_TAC `g:real->A` THEN STRIP_TAC THEN
    MATCH_MP_TAC P2AB_LADM_LOWER THEN EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[];
    EXISTS_TAC `--(abs m * sqrt b * b)` THEN X_GEN_TAC `g:real->A` THEN STRIP_TAC THEN
    MATCH_MP_TAC P2AB_ADM_LOWER THEN EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`l:real`; `e:real`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `g:real->A` STRIP_ASSUME_TAC) ASSUME_TAC) THEN
    USE_THEN "S1" (MP_TAC o SPECL [`g:real->A`; `e:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `g':real->A` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `g':real->A` THEN ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`l:real`; `e:real`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `g:real->A` STRIP_ASSUME_TAC) ASSUME_TAC) THEN
    MP_TAC(ISPECL [`rfs_view (hs:(A)rfs_history)`; `tt:real`; `x:A`; `b:real`;
                   `g:real->A`; `e:real`] P2AXS_SMOOTHING) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `g':real->A` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `g':real->A` THEN ASM_REWRITE_TAC[P2A_L_LENGTH_VIEW] THEN
    MATCH_MP_TAC P2AB_ADM1_LADM THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Clause 6.  If an admissible curve from x at time tt runs in a compact    *)
(* subset K of the smooth part for tau > 0, then x is a backward- smooth    *)
(* point: for small tau the curve lies in boxes reaching up to tt, and      *)
(* x = gamma(0) lies in one of them (they are closed in the Hausdorff       *)
(* slice at tt and the curve is continuous at 0); that box persists.        *)
(* ------------------------------------------------------------------------- *)

let P2AB_BSMOOTH = prove
 (`!(hs:(A)rfs_history) tt x b gamma K.
     rfs_history_ok hs /\ b < tt /\ rfs_L_adm hs tt x b gamma /\ p3_st_compact hs K /\
     (!tau. &0 < tau /\ tau <= b ==> gamma tau IN K (tt - tau))
     ==> p2a_bsmooth (rfs_view hs) x tt`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 MP_TAC (CONJUNCTS_THEN2 MP_TAC (LABEL_TAC "K"))))) THEN
  REWRITE_TAC[p3_st_compact] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` (X_CHOOSE_THEN `W:num->A->bool`
    (X_CHOOSE_THEN `C:num->A->bool` (X_CHOOSE_THEN `a:num->real`
    (X_CHOOSE_THEN `b':num->real` (X_CHOOSE_THEN `eta:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "BOX") (LABEL_TAC "COV"))))))))) THEN
  REWRITE_TAC[rfs_L_adm; rfs_st_curve] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "SL")
      (CONJUNCTS_THEN2 (LABEL_TAC "CT") ASSUME_TAC)))
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)))) THEN
  (* boxes ending before tt are avoided for small tau *)
  MP_TAC(ISPECL [`tt:real`; `IMAGE (b':num->real) {j | j < n}`] P2A_REAL_FINITE_AVOID) THEN
  SIMP_TAC[FINITE_IMAGE; FINITE_NUMSEG_LT] THEN
  REWRITE_TAC[IMP_CONJ; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `d0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "D0"))) THEN
  SUBGOAL_THEN
   `!tau. &0 < tau /\ tau < min d0 b
          ==> ?j:num. j < n /\ tt <= (b':num->real) j /\ (a:num->real) j < tt /\
                      (gamma:real->A) tau IN (C:num->A->bool) j`
  (LABEL_TAC "G") THENL
   [X_GEN_TAC `tau:real` THEN STRIP_TAC THEN
    USE_THEN "K" (MP_TAC o SPEC `tau:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN DISCH_TAC THEN
    USE_THEN "COV" (MP_TAC o SPECL [`tt - tau`; `(gamma:real->A) tau`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    USE_THEN "D0" (MP_TAC o SPEC `j:num`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* x lies in one of the boxes reaching tt *)
  SUBGOAL_THEN `?j:num. j < n /\ tt <= (b':num->real) j /\ (a:num->real) j < tt /\
                        (x:A) IN (C:num->A->bool) j`
  (X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) THENL
   [ASM_CASES_TAC `?j:num. j < n /\ tt <= (b':num->real) j /\ (a:num->real) j < tt /\
                           (x:A) IN (C:num->A->bool) j` THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[NOT_EXISTS_THM;
      TAUT `~(p /\ q /\ r /\ s) <=> p /\ q /\ r ==> ~s`]) THEN
    DISCH_TAC THEN
    ABBREV_TAC `G = {(C:num->A->bool) j | j | j < n /\ tt <= (b':num->real) j /\
                                               (a:num->real) j < tt}` THEN
    SUBGOAL_THEN `closed_in (rfs_top_at (hs:(A)rfs_history) tt) (UNIONS G)` ASSUME_TAC THENL
     [MATCH_MP_TAC CLOSED_IN_UNIONS THEN CONJ_TAC THENL
       [EXPAND_TAC "G" THEN
        ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN MATCH_MP_TAC FINITE_IMAGE THEN
        MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{j:num | j < n}` THEN
        REWRITE_TAC[FINITE_NUMSEG_LT] THEN SET_TAC[];
        ALL_TAC] THEN
      EXPAND_TAC "G" THEN REWRITE_TAC[FORALL_IN_GSPEC] THEN
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      MATCH_MP_TAC COMPACT_IN_IMP_CLOSED_IN THEN CONJ_TAC THENL
       [MP_TAC(SPEC `hs:(A)rfs_history` P2AB_SVS) THEN
        ASM_REWRITE_TAC[p2a_svs; P2A_VIEW_PROJ_3; P2A_RFS_VIEW_COMPONENTS] THEN
        SIMP_TAC[];
        USE_THEN "BOX" (MP_TAC o SPEC `i:num`) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    USE_THEN "CT" (MP_TAC o REWRITE_RULE[REAL_SUB_RZERO; REAL_LE_REFL] o SPECL
      [`&0`; `topspace(rfs_top_at (hs:(A)rfs_history) tt) DIFF UNIONS G`]) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN CONJ_TAC THENL
       [FIRST_X_ASSUM(ACCEPT_TAC o CONJUNCT2 o GEN_REWRITE_RULE I [closed_in]);
        ALL_TAC] THEN
      REWRITE_TAC[IN_DIFF] THEN CONJ_TAC THENL
       [USE_THEN "SL" (MP_TAC o SPEC `&0`) THEN
        REWRITE_TAC[REAL_LE_REFL; REAL_SUB_RZERO] THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
        EXPAND_TAC "G" THEN REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
        STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_MESON_TAC[]];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `d1:real` STRIP_ASSUME_TAC) THEN
    USE_THEN "G" (MP_TAC o SPEC `min (min d0 b) d1 / &2`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `min (min d0 b) d1 / &2` o check (fun th ->
      is_forall(concl th) &&
      can (find_term (fun t -> try fst(dest_const t) = "DIFF" with Failure _ -> false))
          (concl th))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[IN_DIFF; IN_UNIONS; NOT_EXISTS_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `(C:num->A->bool) i` o CONJUNCT2) THEN
    ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "G" THEN REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `i:num` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the box persists up to tt *)
  USE_THEN "BOX" (MP_TAC o SPEC `j:num`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN STRIP_TAC THEN
  REWRITE_TAC[p2a_bsmooth] THEN
  MAP_EVERY EXISTS_TAC [`(W:num->A->bool) j`; `(a:num->real) j - eta`] THEN
  REPEAT CONJ_TAC THENL
   [ASM SET_TAC[];
    ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC P2AB_REGION THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC P2AH_PERSISTS_MONO THEN
    MAP_EVERY EXISTS_TAC [`(a:num->real) j - eta`; `(b':num->real) j`] THEN
    ASM_REWRITE_TAC[REAL_LE_REFL]]);;

(* ------------------------------------------------------------------------- *)
(* The history bridge O3 (all 13 clauses of P2A_HIST_VIEW_X from             *)
(* P2A_REQ_RLOWER), its unconditional form (with RFA_P2A_REQ_RLOWER of       *)
(* pc_rfa_screq, which proves the statement P2A_REQ_RLOWER), and the         *)
(* one-line bridges P2AB_REQ_AREA and P2AB_REQ_VOLCMP to the theorems        *)
(* MFD_AREA_FORMULA and MFD_HAS_VOLUME_COMPARE_QF (same statement texts).    *)
(* ------------------------------------------------------------------------- *)

let P2A_ROUTE_BRIDGE_X = prove
 (`!u:A->bool. P2A_ROUTE_BRIDGE_X_STATEMENT u`,
  GEN_TAC THEN REWRITE_TAC[P2A_ROUTE_BRIDGE_X_STATEMENT; P2A_HIST_VIEW_X_STATEMENT] THEN
  DISCH_TAC THEN X_GEN_TAC `hs:(A)rfs_history` THEN DISCH_TAC THEN
  REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[P2AB_SVS];
    ASM_SIMP_TAC[P2AB_COMPACT];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC P2AB_REGION THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC P2AB_SMOOTH_PT THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC P2AB_ADMX THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC P2AB_BSMOOTH THEN
    MAP_EVERY EXISTS_TAC [`b:real`; `gamma:real->A`; `K:real->A->bool`] THEN
    ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC P2AB_LX_LE THEN EXISTS_TAC `u:A->bool` THEN
    ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC P2AB_ADM1_LADM THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC P2AB_MIN_LGEOD THEN EXISTS_TAC `u:A->bool` THEN
    ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC P2AB_LGEOD_MIN THEN EXISTS_TAC `u:A->bool` THEN
    ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC P2AB_LX_EQ THEN EXISTS_TAC `u:A->bool` THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC P2AB_CBOX THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC P2AB_ST_OPEN THEN ASM_REWRITE_TAC[]]);;

let P2AB_HIST_VIEW_X = prove
 (`!u:A->bool. P2A_HIST_VIEW_X_STATEMENT u`,
  GEN_TAC THEN MP_TAC(ISPEC `u:A->bool` P2A_ROUTE_BRIDGE_X) THEN
  REWRITE_TAC[P2A_ROUTE_BRIDGE_X_STATEMENT; RFA_P2A_REQ_RLOWER]);;

let P2AB_REQ_AREA = prove
 (`!u:A->bool. P2A_REQ_AREA_STATEMENT u`,
  GEN_TAC THEN REWRITE_TAC[P2A_REQ_AREA_STATEMENT] THEN MATCH_ACCEPT_TAC MFD_AREA_FORMULA);;

let P2AB_REQ_VOLCMP = prove
 (`!u:A->bool. P2A_REQ_VOLCMP_STATEMENT u`,
  GEN_TAC THEN REWRITE_TAC[P2A_REQ_VOLCMP_STATEMENT] THEN
  MATCH_ACCEPT_TAC MFD_HAS_VOLUME_COMPARE_QF);;

