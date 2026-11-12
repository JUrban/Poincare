(* ========================================================================= *)
(* pc_p2a_hreg: sets persisting in a Ricci flow history across any number of *)
(* events are region flows.  Main theorem P2AH_HISTORY_REGION: for           *)
(* rfs_history_ok hs, W persisting over (a,b] with                           *)
(* 0 <= a < b < horizon, p3_region_flow hs W a b holds and the               *)
(* identity of W is a diffeomorphism from every slice s in (a,b] to the      *)
(* slice b.  Chains P3_LEMMA_14_11 (one event) by induction on the stages,   *)
(* with a change of reference slice (pullbacks compose along identity        *)
(* diffeomorphisms) and gluing of overlapping flows.  Second main theorem,   *)
(* P2AH_P2C_REGIONS: conjuncts 2-4 of p2c_regular_view (rfs_view hs), the    *)
(* region part of P2C_HISTORY_REGULAR, including smoothness up to the        *)
(* initial time (P2AH_HISTORY_FROM, transport of ricci_flow_from along       *)
(* identity diffeomorphisms) and the empty sets outside [0,horizon).  Used   *)
(* for P2C_HISTORY_REGULAR and for the history bridge of the P2A layer.      *)
(* The first part: the region family and the stage facts.                    *)
(* ========================================================================= *)

needs "src/pc_p3_s14glue.ml";;

prioritize_real();;
type_invention_error := true;;

(* The family of p3_region_flow with reference slice r: the metric at t    *)
(* moved to the atlas of the slice r and restricted to W.                   *)

let p2ah_fam = new_definition
 `p2ah_fam (hs:(A)rfs_history) (W:A->bool) (r:real) (t:real) =
    restrict_metric (rfs_atlas_at hs r) W
      (\x. if t = r then rfs_metric_at hs r x
           else mfd_pullback_metric (rfs_atlas_at hs r) (rfs_atlas_at hs t) (\y. y)
                                    (rfs_metric_at hs t) x)`;;

let P2AH_REGION_FLOW_ALT = prove
 (`!(hs:(A)rfs_history) W a b.
     p3_region_flow hs W a b <=>
     rfs_persists (rfs_view hs) W a b /\
     rfs_flow_upto (subtopology (rfs_top_at hs b) W,restrict_atlas (rfs_atlas_at hs b) W)
                   a b (p2ah_fam hs W b)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p3_region_flow] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM; p2ah_fam]);;

(* Every live time lies in a stage.                                          *)

let P2AH_SLAB_EXISTS = prove
 (`!(hs:(A)rfs_history) t.
     rfs_history_ok hs /\ &0 <= t /\ t < rfs_horizon hs
     ==> ?k. k <= hs_count hs /\ hs_time hs k <= t /\ t < hs_time hs (k + 1)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rfs_horizon] THEN STRIP_TAC THEN
  SUBGOAL_THEN `?j. t < hs_time (hs:(A)rfs_history) j` MP_TAC THENL
   [EXISTS_TAC `hs_count (hs:(A)rfs_history) + 1` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [num_WOP] THEN
  DISCH_THEN(X_CHOOSE_THEN `j:num` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "min"))) THEN
  SUBGOAL_THEN `~(j = 0)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `rfs_history_ok (hs:(A)rfs_history)` THEN REWRITE_TAC[rfs_history_ok] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `j - 1` THEN
  SUBGOAL_THEN `j - 1 + 1 = j` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[ARITH_RULE `j - 1 <= n <=> j <= n + 1`] THEN
    REWRITE_TAC[GSYM NOT_LT] THEN DISCH_TAC THEN
    USE_THEN "min" (MP_TAC o SPEC `hs_count (hs:(A)rfs_history) + 1`) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ASM_REWRITE_TAC[]];
    REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    USE_THEN "min" (MP_TAC o SPEC `j - 1`) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ASM_REWRITE_TAC[]]]);;

(* The slices of a stage.                                                     *)

let P2AH_STAGE = prove
 (`!(hs:(A)rfs_history) k.
     rfs_history_ok hs /\ k <= hs_count hs
     ==> hausdorff_space (hs_top hs k) /\
         smooth_manifold_atlas (hs_top hs k) (hs_atlas hs k) /\
         ricci_flow_from (hs_top hs k,hs_atlas hs k) (hs_time hs k) (hs_time hs (k + 1))
                         (hs_metric hs k) /\
         hs_time hs k < hs_time hs (k + 1) /\
         (!s. hs_time hs k <= s /\ s < hs_time hs (k + 1)
              ==> rfs_top_at hs s = hs_top hs k /\
                  rfs_atlas_at hs s = hs_atlas hs k /\
                  rfs_metric_at hs s = hs_metric hs k s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [rfs_history_ok]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "TM")
    (CONJUNCTS_THEN2 (LABEL_TAC "ST") (LABEL_TAC "EV")))) THEN
  USE_THEN "ST" (MP_TAC o SPEC `k:num`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  USE_THEN "TM" (MP_TAC o SPEC `k:num`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `k:num`; `s:real`] APX_RFS_SLAB) THEN
  ASM_SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Identity diffeomorphisms of an open set W between two smooth manifolds    *)
(* (restriction of the target, equal subtopologies, composition) and the     *)
(* composition of pullbacks of metrics along them.                           *)
(* ------------------------------------------------------------------------- *)

let P2AH_DIFFEO_FACTS = prove
 (`!top1 atlas1 top2 atlas2 (W:A->bool).
     smooth_manifold_atlas top1 (atlas1:((A->bool)#(A->real^N))->bool) /\
     smooth_manifold_atlas top2 (atlas2:((A->bool)#(A->real^N))->bool) /\
     mfd_diffeo top1 atlas1 W top2 atlas2 W (\y. y) (\y. y)
     ==> open_in top1 W /\ open_in top2 W /\
         subtopology top1 W = subtopology top2 W /\
         mfd_diffeo top2 atlas2 W top1 atlas1 W (\y. y) (\y. y) /\
         mfd_diffeo top1 atlas1 W (subtopology top2 W) (restrict_atlas atlas2 W) W
                    (\y. y) (\y. y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [mfd_diffeo]) THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `homeomorphic_maps (subtopology top1 W,subtopology top2 (W:A->bool))
                   ((\y:A. y),(\y:A. y))` THEN
    REWRITE_TAC[HOMEOMORPHIC_MAPS_ID] THEN MESON_TAC[];
    MATCH_MP_TAC MFD_DIFFEO_SYM THEN ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`top1:A topology`; `atlas1:((A->bool)#(A->real^N))->bool`;
                   `topspace top1:A->bool`; `top2:A topology`;
                   `atlas2:((A->bool)#(A->real^N))->bool`; `W:A->bool`; `W:A->bool`;
                   `W:A->bool`; `\y:A. y`; `\y:A. y`] APX_MFD_DIFFEO_RESTRICT) THEN
    ASM_SIMP_TAC[OPEN_IN_TOPSPACE; OPEN_IN_SUBSET; SUBSET_REFL; SUBTOPOLOGY_TOPSPACE;
                 RESTRICT_ATLAS_TOPSPACE]]);;

let P2AH_DIFFEO_TRANS = prove
 (`!top1 atlas1 top2 atlas2 top3 atlas3 (W:A->bool).
     smooth_manifold_atlas top1 (atlas1:((A->bool)#(A->real^N))->bool) /\
     smooth_manifold_atlas top2 (atlas2:((A->bool)#(A->real^N))->bool) /\
     smooth_manifold_atlas top3 (atlas3:((A->bool)#(A->real^N))->bool) /\
     mfd_diffeo top1 atlas1 W top2 atlas2 W (\y. y) (\y. y) /\
     mfd_diffeo top2 atlas2 W top3 atlas3 W (\y. y) (\y. y)
     ==> mfd_diffeo top1 atlas1 W top3 atlas3 W (\y. y) (\y. y)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top1:A topology`; `atlas1:((A->bool)#(A->real^N))->bool`; `W:A->bool`;
                 `top2:A topology`; `atlas2:((A->bool)#(A->real^N))->bool`; `W:A->bool`;
                 `top3:A topology`; `atlas3:((A->bool)#(A->real^N))->bool`; `W:A->bool`;
                 `\y:A. y`; `\y:A. y`; `\y:A. y`; `\y:A. y`] MFD_DIFFEO_COMPOSE) THEN
  ASM_REWRITE_TAC[o_DEF; ETA_AX]);;

(* Chart transitions of an identity diffeomorphism are differentiable.      *)

let P2AH_TRANS_DIFFERENTIABLE = prove
 (`!top1 atlas1 top2 atlas2 (W:A->bool) (U1:A->bool) (phi1:A->real^N) U2 (phi2:A->real^N) x.
     smooth_manifold_atlas top1 (atlas1:((A->bool)#(A->real^N))->bool) /\
     smooth_manifold_atlas top2 (atlas2:((A->bool)#(A->real^N))->bool) /\
     mfd_diffeo top1 atlas1 W top2 atlas2 W (\y. y) (\y. y) /\
     (U1,phi1) IN atlas1 /\ (U2,phi2) IN atlas2 /\ x IN U1 /\ x IN U2 /\ x IN W
     ==> (phi2 o (\y. y) o chart_inv (U1,phi1)) differentiable at (phi1 x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top1:A topology`; `atlas1:((A->bool)#(A->real^N))->bool`; `W:A->bool`;
                 `top2:A topology`; `atlas2:((A->bool)#(A->real^N))->bool`; `W:A->bool`;
                 `\y:A. y`; `\y:A. y`; `U1:A->bool`; `phi1:A->real^N`; `U2:A->bool`;
                 `phi2:A->real^N`] MFDR_DIFFEO_CHART_REP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC P2A_DIFFEO_ON_DIFFERENTIABLE THEN
  MAP_EVERY EXISTS_TAC
   [`IMAGE (phi1:A->real^N) {y:A | y IN U1 INTER W /\ y IN U2}`;
    `IMAGE (phi2:A->real^N) {y:A | y IN U2 INTER W /\ y IN U1}`;
    `(phi1:A->real^N) o (\y:A. y) o chart_inv (U2:A->bool,phi2:A->real^N)`] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
  ASM_REWRITE_TAC[IN_ELIM_THM; IN_INTER]);;

(* Pullbacks of metrics along identity diffeomorphisms compose.             *)

let P2AH_PB_COMPOSE = prove
 (`!top1 atlas1 top2 atlas2 top3 atlas3 (W:A->bool) (g:A->real^N^N) x.
     smooth_manifold_atlas top1 (atlas1:((A->bool)#(A->real^N))->bool) /\
     smooth_manifold_atlas top2 (atlas2:((A->bool)#(A->real^N))->bool) /\
     smooth_manifold_atlas top3 (atlas3:((A->bool)#(A->real^N))->bool) /\
     mfd_diffeo top1 atlas1 W top2 atlas2 W (\y. y) (\y. y) /\
     mfd_diffeo top2 atlas2 W top3 atlas3 W (\y. y) (\y. y) /\ x IN W
     ==> restrict_metric atlas1 W
           (mfd_pullback_metric atlas1 (restrict_atlas atlas2 W) (\y. y)
              (restrict_metric atlas2 W (mfd_pullback_metric atlas2 atlas3 (\y. y) g))) x =
         restrict_metric atlas1 W (mfd_pullback_metric atlas1 atlas3 (\y. y) g) x`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top1:A topology`; `atlas1:((A->bool)#(A->real^N))->bool`;
                 `top2:A topology`; `atlas2:((A->bool)#(A->real^N))->bool`; `W:A->bool`]
                P2AH_DIFFEO_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top2:A topology`; `atlas2:((A->bool)#(A->real^N))->bool`;
                 `top3:A topology`; `atlas3:((A->bool)#(A->real^N))->bool`; `W:A->bool`]
                P2AH_DIFFEO_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top1:A topology`; `atlas1:((A->bool)#(A->real^N))->bool`;
                 `top2:A topology`; `atlas2:((A->bool)#(A->real^N))->bool`;
                 `top3:A topology`; `atlas3:((A->bool)#(A->real^N))->bool`; `W:A->bool`]
                P2AH_DIFFEO_TRANS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(x:A) IN topspace top1 /\ x IN topspace top2 /\ x IN topspace top3`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC(SET_RULE `!s t (y:A). y IN s /\ s SUBSET t ==> y IN t`) THEN
    EXISTS_TAC `W:A->bool` THEN ASM_SIMP_TAC[OPEN_IN_SUBSET];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top1:A topology`; `atlas1:((A->bool)#(A->real^N))->bool`; `W:A->bool`;
                 `x:A`] MFDR_CHART_AT_RESTRICT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `U1:A->bool` (X_CHOOSE_THEN `phi1:A->real^N` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`top2:A topology`; `atlas2:((A->bool)#(A->real^N))->bool`; `W:A->bool`;
                 `x:A`] MFDR_CHART_AT_RESTRICT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `U2:A->bool` (X_CHOOSE_THEN `phi2:A->real^N` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`top3:A topology`; `atlas3:((A->bool)#(A->real^N))->bool`; `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `chart_at (atlas3:((A->bool)#(A->real^N))->bool) (x:A)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `U3:A->bool` (X_CHOOSE_THEN `phi3:A->real^N` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[FST] THEN STRIP_TAC THEN
  CONV_TAC(BINOP_CONV(RATOR_CONV(REWR_CONV restrict_metric) THENC BETA_CONV)) THEN
  ASM_REWRITE_TAC[SND] THEN
  MP_TAC(ISPECL [`top1:A topology`; `atlas1:((A->bool)#(A->real^N))->bool`; `U1:A->bool`;
                 `phi1:A->real^N`; `W:A->bool`] MFDR_METRIC_LOCAL_RESTRICT_CHART) THEN
  ASM_SIMP_TAC[IN_INTER] THEN DISCH_THEN(K ALL_TAC) THEN
  SUBGOAL_THEN `(U2 INTER W:A->bool,phi2:A->real^N) IN restrict_atlas atlas2 W`
  ASSUME_TAC THENL [REWRITE_TAC[IN_RESTRICT_ATLAS] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `smooth_manifold_atlas (subtopology top2 (W:A->bool))
                  (restrict_atlas (atlas2:((A->bool)#(A->real^N))->bool) W)`
  ASSUME_TAC THENL [ASM_SIMP_TAC[SMOOTH_MANIFOLD_ATLAS_RESTRICT]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top1:A topology`; `atlas1:((A->bool)#(A->real^N))->bool`; `W:A->bool`;
                 `subtopology top2 (W:A->bool)`;
                 `restrict_atlas (atlas2:((A->bool)#(A->real^N))->bool) W`; `W:A->bool`;
                 `\y:A. y`; `\y:A. y`;
                 `restrict_metric (atlas2:((A->bool)#(A->real^N))->bool) W
                    (mfd_pullback_metric atlas2 (atlas3:((A->bool)#(A->real^N))->bool)
                       (\y:A. y) (g:A->real^N^N))`;
                 `U1:A->bool`; `phi1:A->real^N`; `U2 INTER W:A->bool`; `phi2:A->real^N`;
                 `x:A`] P2A_PULLBACK_METRIC_LOCAL_W) THEN
  ASM_REWRITE_TAC[IN_INTER] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`top1:A topology`; `atlas1:((A->bool)#(A->real^N))->bool`; `W:A->bool`;
                 `top3:A topology`; `atlas3:((A->bool)#(A->real^N))->bool`; `W:A->bool`;
                 `\y:A. y`; `\y:A. y`; `g:A->real^N^N`;
                 `U1:A->bool`; `phi1:A->real^N`; `U3:A->bool`; `phi3:A->real^N`;
                 `x:A`] P2A_PULLBACK_METRIC_LOCAL_W) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`top1:A topology`; `atlas1:((A->bool)#(A->real^N))->bool`; `U1:A->bool`;
                 `phi1:A->real^N`] CHART_INV) THEN
  MP_TAC(ISPECL [`top2:A topology`; `atlas2:((A->bool)#(A->real^N))->bool`; `U2:A->bool`;
                 `phi2:A->real^N`] CHART_INV) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(LABEL_TAC "ci2" o CONJUNCT1) THEN DISCH_THEN(LABEL_TAC "ci1" o CONJUNCT1) THEN
  SUBGOAL_THEN `chart_inv (U1:A->bool,phi1:A->real^N) (phi1 x) = x /\
                chart_inv (U2:A->bool,phi2:A->real^N) (phi2 x) = x`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [USE_THEN "ci1" MATCH_MP_TAC; USE_THEN "ci2" MATCH_MP_TAC] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mpullback ((phi2:A->real^N) o (\y:A. y) o chart_inv (U1,phi1:A->real^N))
      (metric_local (restrict_atlas (atlas2:((A->bool)#(A->real^N))->bool) W) (U2 INTER W,phi2)
         (restrict_metric atlas2 W
            (mfd_pullback_metric atlas2 (atlas3:((A->bool)#(A->real^N))->bool) (\y:A. y)
               (g:A->real^N^N)))) (phi1 x) =
    mpullback (phi2 o (\y:A. y) o chart_inv (U1,phi1))
      (mpullback ((phi3:A->real^N) o (\y:A. y) o chart_inv (U2,phi2))
         (metric_local atlas3 (U3,phi3) g)) (phi1 x)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC P2A_MPULLBACK_PT THEN ASM_REWRITE_TAC[o_THM] THEN
    MP_TAC(ISPECL [`top2:A topology`; `atlas2:((A->bool)#(A->real^N))->bool`; `U2:A->bool`;
                   `phi2:A->real^N`; `W:A->bool`;
                   `mfd_pullback_metric (atlas2:((A->bool)#(A->real^N))->bool)
                      (atlas3:((A->bool)#(A->real^N))->bool) (\y:A. y) (g:A->real^N^N)`;
                   `x:A`] METRIC_LOCAL_RESTRICT) THEN
    ASM_REWRITE_TAC[IN_INTER] THEN DISCH_THEN SUBST1_TAC THEN
    MP_TAC(ISPECL [`top2:A topology`; `atlas2:((A->bool)#(A->real^N))->bool`; `W:A->bool`;
                   `top3:A topology`; `atlas3:((A->bool)#(A->real^N))->bool`; `W:A->bool`;
                   `\y:A. y`; `\y:A. y`; `g:A->real^N^N`;
                   `U2:A->bool`; `phi2:A->real^N`; `U3:A->bool`; `phi3:A->real^N`;
                   `x:A`] P2A_PULLBACK_METRIC_LOCAL_W) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(phi2:A->real^N) o (\y:A. y) o chart_inv (U1,phi1:A->real^N)`;
                 `(phi3:A->real^N) o (\y:A. y) o chart_inv (U2,phi2:A->real^N)`;
                 `metric_local (atlas3:((A->bool)#(A->real^N))->bool) (U3,phi3:A->real^N)
                    (g:A->real^N^N)`;
                 `(phi1:A->real^N) x`] P2A_MPULLBACK_COMPOSE) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC P2AH_TRANS_DIFFERENTIABLE THEN
      MAP_EVERY EXISTS_TAC [`top1:A topology`; `atlas1:((A->bool)#(A->real^N))->bool`;
                            `top2:A topology`; `atlas2:((A->bool)#(A->real^N))->bool`;
                            `W:A->bool`; `U2:A->bool`] THEN
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[o_THM] THEN MATCH_MP_TAC P2AH_TRANS_DIFFERENTIABLE THEN
      MAP_EVERY EXISTS_TAC [`top2:A topology`; `atlas2:((A->bool)#(A->real^N))->bool`;
                            `top3:A topology`; `atlas3:((A->bool)#(A->real^N))->bool`;
                            `W:A->bool`; `U3:A->bool`] THEN
      ASM_REWRITE_TAC[]];
    DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC P2A_MPULLBACK_LOCAL THEN
  EXISTS_TAC `IMAGE (phi1:A->real^N) (U1 INTER (U2 INTER W))` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CHART_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`top1:A topology`; `atlas1:((A->bool)#(A->real^N))->bool`;
                          `U1:A->bool`] THEN
    ASM_REWRITE_TAC[INTER_SUBSET] THEN
    MATCH_MP_TAC OPEN_IN_INTER THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`top1:A topology`; `atlas1:((A->bool)#(A->real^N))->bool`;
                     `U1:A->bool`; `phi1:A->real^N`] SMOOTH_MANIFOLD_ATLAS_CHART) THEN
      ASM_SIMP_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC OPEN_IN_TRANS_FULL THEN EXISTS_TAC `W:A->bool` THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[]] THEN
    UNDISCH_TAC `subtopology top1 (W:A->bool) = subtopology top2 W` THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[OPEN_IN_SUBTOPOLOGY] THEN EXISTS_TAC `U2:A->bool` THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`top2:A topology`; `atlas2:((A->bool)#(A->real^N))->bool`;
                     `U2:A->bool`; `phi2:A->real^N`] SMOOTH_MANIFOLD_ATLAS_CHART) THEN
      ASM_SIMP_TAC[]; SET_TAC[]];
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_INTER];
    REWRITE_TAC[FORALL_IN_IMAGE; IN_INTER; o_THM] THEN X_GEN_TAC `z:A` THEN STRIP_TAC THEN
    SUBGOAL_THEN `chart_inv (U1:A->bool,phi1:A->real^N) (phi1 z) = z /\
                  chart_inv (U2:A->bool,phi2:A->real^N) (phi2 z) = z`
     (fun th -> REWRITE_TAC[th]) THEN
    CONJ_TAC THENL [USE_THEN "ci1" MATCH_MP_TAC; USE_THEN "ci2" MATCH_MP_TAC] THEN
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The uniform family p2ah_famx (no special case at the reference slice; it *)
(* agrees with p2ah_fam on W), persistence, identity diffeomorphisms of W   *)
(* within a stage and across one event, and their chaining over any number  *)
(* of events (induction on the stage).                                      *)
(* ------------------------------------------------------------------------- *)

let p2ah_famx = new_definition
 `p2ah_famx (hs:(A)rfs_history) (W:A->bool) (r:real) (t:real) =
    restrict_metric (rfs_atlas_at hs r) W
      (mfd_pullback_metric (rfs_atlas_at hs r) (rfs_atlas_at hs t) (\y. y)
                           (rfs_metric_at hs t))`;;

let P2AH_FAM_FAMX = prove
 (`!(hs:(A)rfs_history) W r t x.
     smooth_manifold_atlas (rfs_top_at hs r) (rfs_atlas_at hs r) /\
     open_in (rfs_top_at hs r) W /\ x IN W
     ==> p2ah_fam hs W r t x = p2ah_famx hs W r t x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p2ah_fam; p2ah_famx] THEN
  ASM_CASES_TAC `t:real = r` THEN ASM_REWRITE_TAC[ETA_AX] THEN
  MATCH_MP_TAC P2CF_RESTRICT_METRIC_CONG THEN
  EXISTS_TAC `rfs_top_at (hs:(A)rfs_history) r` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `y:A` THEN DISCH_TAC THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC P2CF_PULLBACK_ID THEN
  EXISTS_TAC `rfs_top_at (hs:(A)rfs_history) r` THEN ASM_REWRITE_TAC[]);;

let P2AH_FAMX_REF = prove
 (`!(hs:(A)rfs_history) W r r'.
     rfs_atlas_at hs r = rfs_atlas_at hs r'
     ==> p2ah_famx hs W r = p2ah_famx hs W r'`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[FUN_EQ_THM; p2ah_famx] THEN ASM_REWRITE_TAC[]);;

let P2AH_PERSISTS = prove
 (`!(hs:(A)rfs_history) W a b.
     rfs_persists (rfs_view hs) W a b <=>
     !s. a < s /\ s <= b
         ==> smooth_manifold_atlas (rfs_top_at hs s) (rfs_atlas_at hs s) /\
             open_in (rfs_top_at hs s) W`,
  REWRITE_TAC[rfs_view; rfs_persists]);;

let P2AH_PERSISTS_MONO = prove
 (`!(hs:(A)rfs_history) W a b a' b'.
     rfs_persists (rfs_view hs) W a b /\ a <= a' /\ b' <= b
     ==> rfs_persists (rfs_view hs) W a' b'`,
  REWRITE_TAC[P2AH_PERSISTS] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  X_GEN_TAC `s:real` THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REAL_ARITH_TAC);;

(* Identity diffeomorphisms of W between slices of one stage.               *)

let P2AH_STAGE_DIFFEO = prove
 (`!(hs:(A)rfs_history) k W s1 s2.
     rfs_history_ok hs /\ k <= hs_count hs /\
     hs_time hs k <= s1 /\ s1 < hs_time hs (k + 1) /\
     hs_time hs k <= s2 /\ s2 < hs_time hs (k + 1) /\
     open_in (hs_top hs k) W
     ==> mfd_diffeo (rfs_top_at hs s1) (rfs_atlas_at hs s1) W
                    (rfs_top_at hs s2) (rfs_atlas_at hs s2) W (\y. y) (\y. y)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `k:num`] P2AH_STAGE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_SIMP_TAC[] THEN
  MATCH_MP_TAC MFD_DIFFEO_ID THEN ASM_REWRITE_TAC[]);;

(* Across the event k: the retained set W is an identity diffeomorphism     *)
(* from the new stage to the old one (P3S_EVENT_RETAINED).                  *)

let P2AH_EVENT_DIFFEO = prove
 (`!(hs:(A)rfs_history) k W.
     rfs_history_ok hs /\ 1 <= k /\ k <= hs_count hs /\
     open_in (hs_top hs k) W /\ W SUBSET topspace(hs_top hs (k - 1))
     ==> mfd_diffeo (hs_top hs k) (hs_atlas hs k) W
                    (hs_top hs (k - 1)) (hs_atlas hs (k - 1)) W (\y. y) (\y. y)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `k:num`] P3S_STAGE_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`hs_top (hs:(A)rfs_history) (k - 1)`; `hs_atlas (hs:(A)rfs_history) (k - 1)`;
                 `hs_metric (hs:(A)rfs_history) (k - 1)`; `hs_time (hs:(A)rfs_history) k`;
                 `hs_top (hs:(A)rfs_history) k`; `hs_atlas (hs:(A)rfs_history) k`;
                 `hs_metric (hs:(A)rfs_history) k`; `hs_event (hs:(A)rfs_history) k`;
                 `W:A->bool`] P3S_EVENT_RETAINED) THEN
  ASM_SIMP_TAC[]);;

(* Within the stage of b.                                                    *)

let P2AH_DIFFEO_SAME = prove
 (`!(hs:(A)rfs_history) m W a b s.
     rfs_history_ok hs /\ m <= hs_count hs /\
     hs_time hs m <= s /\ s <= b /\ b < hs_time hs (m + 1) /\
     a < s /\ rfs_persists (rfs_view hs) W a b
     ==> mfd_diffeo (rfs_top_at hs s) (rfs_atlas_at hs s) W
                    (rfs_top_at hs b) (rfs_atlas_at hs b) W (\y. y) (\y. y)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open_in (hs_top (hs:(A)rfs_history) m) W` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`hs:(A)rfs_history`; `m:num`] P2AH_STAGE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `b:real` o last o CONJUNCTS) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT1)] THEN
    UNDISCH_TAC `rfs_persists (rfs_view (hs:(A)rfs_history)) W a b` THEN
    REWRITE_TAC[P2AH_PERSISTS] THEN DISCH_THEN(MP_TAC o SPEC `b:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC P2AH_STAGE_DIFFEO THEN EXISTS_TAC `m:num` THEN ASM_REWRITE_TAC[] THEN
  ASM_REAL_ARITH_TAC);;

(* Any number of events: induction on the stage m of b.                      *)

let P2AH_DIFFEO_CHAIN = prove
 (`!(hs:(A)rfs_history) m W a b s.
     rfs_history_ok hs /\ m <= hs_count hs /\
     hs_time hs m <= b /\ b < hs_time hs (m + 1) /\
     &0 <= a /\ a < s /\ s <= b /\ rfs_persists (rfs_view hs) W a b
     ==> mfd_diffeo (rfs_top_at hs s) (rfs_atlas_at hs s) W
                    (rfs_top_at hs b) (rfs_atlas_at hs b) W (\y. y) (\y. y)`,
  GEN_TAC THEN INDUCT_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC P2AH_DIFFEO_SAME THEN
    MAP_EVERY EXISTS_TAC [`0`; `a:real`] THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [rfs_history_ok]) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(LABEL_TAC "IH") THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `hs_time (hs:(A)rfs_history) (SUC m) <= s` THENL
   [MATCH_MP_TAC P2AH_DIFFEO_SAME THEN
    MAP_EVERY EXISTS_TAC [`SUC m`; `a:real`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `m <= hs_count (hs:(A)rfs_history) /\ SUC m - 1 = m /\ m + 1 = SUC m /\
                1 <= SUC m`
  STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `SUC m`] P3S_STAGE_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "S0") (LABEL_TAC "S1"))))))))) THEN
  FIRST_ASSUM(LABEL_TAC "P" o GEN_REWRITE_RULE I [P2AH_PERSISTS]) THEN
  ABBREV_TAC `c = (max s (hs_time (hs:(A)rfs_history) m) + hs_time hs (SUC m)) / &2` THEN
  SUBGOAL_THEN `s <= c /\ hs_time (hs:(A)rfs_history) m <= c /\ c < hs_time hs (SUC m) /\
                c <= b`
  STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "P" (MP_TAC o SPEC `s:real`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN
   `mfd_diffeo (rfs_top_at hs c) (rfs_atlas_at hs c) W
               (rfs_top_at hs b) (rfs_atlas_at (hs:(A)rfs_history) b) W (\y. y) (\y. y) /\
    smooth_manifold_atlas (rfs_top_at hs c) (rfs_atlas_at hs c) /\
    smooth_manifold_atlas (rfs_top_at hs b) (rfs_atlas_at hs b)`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "S1" (MP_TAC o SPEC `b:real`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    USE_THEN "S0" (MP_TAC o SPEC `c:real`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    USE_THEN "P" (MP_TAC o SPEC `b:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[] THEN STRIP_TAC] THEN
    USE_THEN "P" (MP_TAC o SPEC `c:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[] THEN STRIP_TAC] THEN
    MATCH_MP_TAC MFD_DIFFEO_SYM THEN
    MP_TAC(ISPECL [`hs:(A)rfs_history`; `SUC m`; `W:A->bool`] P2AH_EVENT_DIFFEO) THEN
    ASM_SIMP_TAC[OPEN_IN_SUBSET];
    ALL_TAC] THEN
  USE_THEN "IH" (MP_TAC o SPECL [`W:A->bool`; `a:real`; `c:real`; `s:real`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P2AH_PERSISTS_MONO THEN
    MAP_EVERY EXISTS_TAC [`a:real`; `b:real`] THEN ASM_REWRITE_TAC[REAL_LE_REFL];
    DISCH_TAC] THEN
  MATCH_MP_TAC P2AH_DIFFEO_TRANS THEN
  MAP_EVERY EXISTS_TAC [`rfs_top_at (hs:(A)rfs_history) c`; `rfs_atlas_at (hs:(A)rfs_history) c`] THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Ricci flows on persisting regions.  Within a stage (the stage flow        *)
(* restricted), across one event (P3_LEMMA_14_11), change of the reference   *)
(* slice along identity diffeomorphisms (P3S_RFO_TRANSPORT_W and             *)
(* P2AH_PB_COMPOSE), and the induction on the stage gluing overlapping flows *)
(* (PDE_RFO_UNION2).  The main theorem P2AH_HISTORY_REGION.                  *)
(* ------------------------------------------------------------------------- *)

let P2AH_RF_BASE = prove
 (`!(hs:(A)rfs_history) m W a w r.
     rfs_history_ok hs /\ m <= hs_count hs /\
     hs_time hs m <= a /\ a < w /\ w <= hs_time hs (m + 1) /\
     hs_time hs m <= r /\ r < hs_time hs (m + 1) /\ open_in (hs_top hs m) W
     ==> ricci_flow_on (subtopology (rfs_top_at hs r) W,restrict_atlas (rfs_atlas_at hs r) W)
                       a w (p2ah_famx hs W r)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `m:num`] P2AH_STAGE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "SL"))))) THEN
  USE_THEN "SL" (MP_TAC o SPEC `r:real`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC P2CF_RFO_CONG THEN
  EXISTS_TAC `\t. restrict_metric (hs_atlas (hs:(A)rfs_history) m) W (hs_metric hs m t)` THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`hs_top (hs:(A)rfs_history) m`; `hs_atlas (hs:(A)rfs_history) m`;
                   `a:real`; `w:real`; `hs_metric (hs:(A)rfs_history) m`; `W:A->bool`]
                  P2CF_RFO_RESTRICT) THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC RICCI_FLOW_SUBINTERVAL THEN
    MAP_EVERY EXISTS_TAC [`hs_time (hs:(A)rfs_history) m`;
                          `hs_time (hs:(A)rfs_history) (m + 1)`] THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(ACCEPT_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [ricci_flow_from]);
    ALL_TAC] THEN
  REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER] THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `x:A`] THEN STRIP_TAC THEN BETA_TAC THEN
  USE_THEN "SL" (MP_TAC o SPEC `t:real`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  REWRITE_TAC[p2ah_famx] THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC P2CF_RESTRICT_METRIC_CONG THEN EXISTS_TAC `hs_top (hs:(A)rfs_history) m` THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:A` THEN DISCH_TAC THEN
  MATCH_MP_TAC P2CF_PULLBACK_ID THEN EXISTS_TAC `hs_top (hs:(A)rfs_history) m` THEN
  ASM_REWRITE_TAC[]);;

let P2AH_RF_SAME = prove
 (`!(hs:(A)rfs_history) m W a b w.
     rfs_history_ok hs /\ m <= hs_count hs /\
     hs_time hs m <= a /\ a < b /\ b < w /\ w < hs_time hs (m + 1) /\
     rfs_persists (rfs_view hs) W a b
     ==> ricci_flow_on (subtopology (rfs_top_at hs b) W,restrict_atlas (rfs_atlas_at hs b) W)
                       a w (p2ah_famx hs W b)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open_in (hs_top (hs:(A)rfs_history) m) W` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`hs:(A)rfs_history`; `m:num`] P2AH_STAGE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `b:real` o last o CONJUNCTS) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT1)] THEN
    UNDISCH_TAC `rfs_persists (rfs_view (hs:(A)rfs_history)) W a b` THEN
    REWRITE_TAC[P2AH_PERSISTS] THEN DISCH_THEN(MP_TAC o SPEC `b:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC P2AH_RF_BASE THEN EXISTS_TAC `m:num` THEN ASM_REWRITE_TAC[] THEN
  ASM_REAL_ARITH_TAC);;

(* One event: P3_LEMMA_14_11, with the family moved to the uniform form.     *)

let P2AH_RF_EVENT = prove
 (`!(hs:(A)rfs_history) m W a w r.
     rfs_history_ok hs /\ 1 <= m /\ m <= hs_count hs /\
     hs_time hs (m - 1) <= a /\ a < hs_time hs m /\
     hs_time hs m < w /\ w < hs_time hs (m + 1) /\
     hs_time hs m <= r /\ r < hs_time hs (m + 1) /\
     open_in (hs_top hs m) W /\ W SUBSET topspace(hs_top hs (m - 1))
     ==> ricci_flow_on (subtopology (rfs_top_at hs r) W,restrict_atlas (rfs_atlas_at hs r) W)
                       a w (p2ah_famx hs W r)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `UNIV:A->bool` P3_LEMMA_14_11) THEN REWRITE_TAC[P3_LEMMA_14_11_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPECL [`hs:(A)rfs_history`; `m:num`; `W:A->bool`; `a:real`; `w:real`]) THEN
  ASM_REWRITE_TAC[P2AH_REGION_FLOW_ALT; rfs_flow_upto] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (LABEL_TAC "RFO") (K ALL_TAC))) THEN
  SUBGOAL_THEN `p2ah_famx hs W r = p2ah_famx (hs:(A)rfs_history) W w /\
                rfs_top_at hs r = rfs_top_at hs w /\ rfs_atlas_at hs r = rfs_atlas_at hs w /\
                smooth_manifold_atlas (rfs_top_at hs w) (rfs_atlas_at hs w) /\
                open_in (rfs_top_at hs w) W`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`hs:(A)rfs_history`; `m:num`] P2AH_STAGE) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "SL"))))) THEN
    USE_THEN "SL" (MP_TAC o SPEC `r:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    USE_THEN "SL" (MP_TAC o SPEC `w:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P2AH_FAMX_REF THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC P2CF_RFO_CONG THEN EXISTS_TAC `p2ah_fam (hs:(A)rfs_history) W w` THEN
  CONJ_TAC THENL [USE_THEN "RFO" ACCEPT_TAC; ALL_TAC] THEN
  REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER] THEN REPEAT STRIP_TAC THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC P2AH_FAM_FAMX THEN ASM_REWRITE_TAC[]);;

(* Change of the reference slice from c to b along identity                  *)
(* diffeomorphisms of W (slices t -> c and b -> c).                           *)

let P2AH_REF_CHANGE = prove
 (`!(hs:(A)rfs_history) W a w c b.
     smooth_manifold_atlas (rfs_top_at hs b) (rfs_atlas_at hs b) /\
     smooth_manifold_atlas (rfs_top_at hs c) (rfs_atlas_at hs c) /\
     mfd_diffeo (rfs_top_at hs b) (rfs_atlas_at hs b) W
                (rfs_top_at hs c) (rfs_atlas_at hs c) W (\y. y) (\y. y) /\
     (!t. a < t /\ t < w
          ==> smooth_manifold_atlas (rfs_top_at hs t) (rfs_atlas_at hs t) /\
              mfd_diffeo (rfs_top_at hs t) (rfs_atlas_at hs t) W
                         (rfs_top_at hs c) (rfs_atlas_at hs c) W (\y. y) (\y. y)) /\
     ricci_flow_on (subtopology (rfs_top_at hs c) W,restrict_atlas (rfs_atlas_at hs c) W)
                   a w (p2ah_famx hs W c)
     ==> ricci_flow_on (subtopology (rfs_top_at hs b) W,restrict_atlas (rfs_atlas_at hs b) W)
                       a w (p2ah_famx hs W b)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "T") ASSUME_TAC)))) THEN
  MP_TAC(ISPECL [`rfs_top_at (hs:(A)rfs_history) b`; `rfs_atlas_at (hs:(A)rfs_history) b`;
                 `rfs_top_at (hs:(A)rfs_history) c`; `rfs_atlas_at (hs:(A)rfs_history) c`;
                 `W:A->bool`] P2AH_DIFFEO_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`rfs_top_at (hs:(A)rfs_history) b`; `rfs_atlas_at (hs:(A)rfs_history) b`;
                 `subtopology (rfs_top_at (hs:(A)rfs_history) c) W`;
                 `restrict_atlas (rfs_atlas_at (hs:(A)rfs_history) c) W`;
                 `W:A->bool`; `a:real`; `w:real`; `p2ah_famx (hs:(A)rfs_history) W c`]
                P3S_RFO_TRANSPORT_W) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[SUBTOPOLOGY_SUBTOPOLOGY; INTER_IDEMPOT]; DISCH_TAC] THEN
  MATCH_MP_TAC P2CF_RFO_CONG THEN
  EXISTS_TAC `\t. restrict_metric (rfs_atlas_at (hs:(A)rfs_history) b) W
                    (mfd_pullback_metric (rfs_atlas_at hs b)
                       (restrict_atlas (rfs_atlas_at hs c) W) (\x:A. x)
                       (p2ah_famx hs W c t))` THEN
  CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER] THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `x:A`] THEN STRIP_TAC THEN BETA_TAC THEN
  USE_THEN "T" (MP_TAC o SPEC `t:real`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  REWRITE_TAC[p2ah_famx] THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC P2AH_PB_COMPOSE THEN
  MAP_EVERY EXISTS_TAC [`rfs_top_at (hs:(A)rfs_history) b`; `rfs_top_at (hs:(A)rfs_history) c`;
                        `rfs_top_at (hs:(A)rfs_history) t`] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MFD_DIFFEO_SYM THEN ASM_REWRITE_TAC[]);;

(* Any number of events: induction on the stage m of b.                      *)

let P2AH_RF_CHAIN = prove
 (`!(hs:(A)rfs_history) m W a b w.
     rfs_history_ok hs /\ m <= hs_count hs /\
     hs_time hs m <= b /\ b < w /\ w < hs_time hs (m + 1) /\
     &0 <= a /\ a < b /\ rfs_persists (rfs_view hs) W a b
     ==> ricci_flow_on (subtopology (rfs_top_at hs b) W,restrict_atlas (rfs_atlas_at hs b) W)
                       a w (p2ah_famx hs W b)`,
  GEN_TAC THEN INDUCT_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC P2AH_RF_SAME THEN
    EXISTS_TAC `0` THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [rfs_history_ok]) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(LABEL_TAC "IH") THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `hs_time (hs:(A)rfs_history) (SUC m) <= a` THENL
   [MATCH_MP_TAC P2AH_RF_SAME THEN EXISTS_TAC `SUC m` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `m <= hs_count (hs:(A)rfs_history) /\ SUC m - 1 = m /\ m + 1 = SUC m /\
                1 <= SUC m`
  STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `SUC m`] P3S_STAGE_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "S0") (LABEL_TAC "S1"))))))))) THEN
  FIRST_ASSUM(LABEL_TAC "P" o GEN_REWRITE_RULE I [P2AH_PERSISTS]) THEN
  ABBREV_TAC `a' = (max a (hs_time (hs:(A)rfs_history) m) + hs_time hs (SUC m)) / &2` THEN
  ABBREV_TAC `c = (a' + hs_time (hs:(A)rfs_history) (SUC m)) / &2` THEN
  ABBREV_TAC `w' = (c + hs_time (hs:(A)rfs_history) (SUC m)) / &2` THEN
  SUBGOAL_THEN `a < a' /\ hs_time (hs:(A)rfs_history) m <= a' /\ a' < c /\ c < w' /\
                w' < hs_time hs (SUC m) /\ hs_time hs m <= c /\ a < c /\
                a' < hs_time hs (SUC m) /\ c < hs_time hs (SUC m) /\ c <= b /\
                a' < w' /\ w' <= w /\ a <= a'`
  STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_manifold_atlas (rfs_top_at hs b) (rfs_atlas_at (hs:(A)rfs_history) b) /\
    smooth_manifold_atlas (rfs_top_at hs c) (rfs_atlas_at hs c) /\
    mfd_diffeo (rfs_top_at hs b) (rfs_atlas_at hs b) W
               (rfs_top_at hs c) (rfs_atlas_at hs c) W (\y. y) (\y. y) /\
    open_in (hs_top hs (SUC m)) W /\ open_in (hs_top hs m) W`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "S1" (MP_TAC o SPEC `b:real`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    USE_THEN "S0" (MP_TAC o SPEC `c:real`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    USE_THEN "P" (MP_TAC o SPEC `b:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[] THEN STRIP_TAC] THEN
    USE_THEN "P" (MP_TAC o SPEC `c:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[] THEN STRIP_TAC] THEN
    MP_TAC(ISPECL [`hs:(A)rfs_history`; `SUC m`; `W:A->bool`] P2AH_EVENT_DIFFEO) THEN
    ASM_SIMP_TAC[OPEN_IN_SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t. a < t /\ t < w'
        ==> smooth_manifold_atlas (rfs_top_at hs t) (rfs_atlas_at (hs:(A)rfs_history) t) /\
            mfd_diffeo (rfs_top_at hs t) (rfs_atlas_at hs t) W
                       (rfs_top_at hs c) (rfs_atlas_at hs c) W (\y. y) (\y. y)`
  ASSUME_TAC THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN ASM_CASES_TAC `t <= c` THENL
     [CONJ_TAC THENL
       [USE_THEN "P" (MP_TAC o SPEC `t:real`) THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
        MATCH_MP_TAC P2AH_DIFFEO_CHAIN THEN
        MAP_EVERY EXISTS_TAC [`m:num`; `a:real`] THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC P2AH_PERSISTS_MONO THEN MAP_EVERY EXISTS_TAC [`a:real`; `b:real`] THEN
        ASM_REWRITE_TAC[REAL_LE_REFL]];
      USE_THEN "S0" (MP_TAC o SPEC `t:real`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
      USE_THEN "S0" (MP_TAC o SPEC `c:real`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MFD_DIFFEO_ID THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  USE_THEN "IH" (MP_TAC o SPECL [`W:A->bool`; `a:real`; `c:real`; `w':real`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P2AH_PERSISTS_MONO THEN
    MAP_EVERY EXISTS_TAC [`a:real`; `b:real`] THEN ASM_REWRITE_TAC[REAL_LE_REFL];
    DISCH_TAC] THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `W:A->bool`; `a:real`; `w':real`; `c:real`; `b:real`]
                P2AH_REF_CHANGE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `SUC m`; `W:A->bool`; `a':real`; `w:real`; `b:real`]
                P2AH_RF_EVENT) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[OPEN_IN_SUBSET] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  MATCH_MP_TAC PDE_RFO_UNION2 THEN
  MAP_EVERY EXISTS_TAC [`w':real`; `a':real`] THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Main theorem: a set W persisting over (a,b] in a Ricci flow history, with *)
(* 0 <= a < b < horizon, is a region flow (p3_region_flow: the family        *)
(* of the history moved to the atlas of the slice b is a Ricci flow on W     *)
(* over (a,b], smooth up to b), and the identity of W is a diffeomorphism    *)
(* from every slice s in (a,b] to the slice b.                               *)
(* ------------------------------------------------------------------------- *)

let P2AH_HISTORY_REGION_STATEMENT = new_definition
 `P2AH_HISTORY_REGION_STATEMENT (u:A->bool) <=>
    !(hs:(A)rfs_history) W a b.
       rfs_history_ok hs /\ &0 <= a /\ a < b /\ b < rfs_horizon hs /\
       rfs_persists (rfs_view hs) W a b
       ==> p3_region_flow hs W a b /\
           (!s. a < s /\ s <= b
                ==> mfd_diffeo (rfs_top_at hs s) (rfs_atlas_at hs s) W
                               (rfs_top_at hs b) (rfs_atlas_at hs b) W (\y. y) (\y. y))`;;

let P2AH_HISTORY_REGION = prove
 (`!(hs:(A)rfs_history) W a b.
     rfs_history_ok hs /\ &0 <= a /\ a < b /\ b < rfs_horizon hs /\
     rfs_persists (rfs_view hs) W a b
     ==> p3_region_flow hs W a b /\
         (!s. a < s /\ s <= b
              ==> mfd_diffeo (rfs_top_at hs s) (rfs_atlas_at hs s) W
                             (rfs_top_at hs b) (rfs_atlas_at hs b) W (\y. y) (\y. y))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `b:real`] P2AH_SLAB_EXISTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:num` STRIP_ASSUME_TAC) THEN CONJ_TAC THENL
   [ALL_TAC;
    REPEAT STRIP_TAC THEN MATCH_MP_TAC P2AH_DIFFEO_CHAIN THEN
    MAP_EVERY EXISTS_TAC [`m:num`; `a:real`] THEN ASM_REWRITE_TAC[]] THEN
  REWRITE_TAC[P2AH_REGION_FLOW_ALT] THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC P2CF_RFO_UPTO THEN
  MAP_EVERY EXISTS_TAC [`a:real`; `(b + hs_time (hs:(A)rfs_history) (m + 1)) / &2`] THEN
  REWRITE_TAC[REAL_LE_REFL] THEN
  CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
  MATCH_MP_TAC P2CF_RFO_CONG THEN
  EXISTS_TAC `p2ah_famx (hs:(A)rfs_history) W b` THEN CONJ_TAC THENL
   [MATCH_MP_TAC P2AH_RF_CHAIN THEN EXISTS_TAC `m:num` THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC P2AH_FAM_FAMX THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `rfs_persists (rfs_view (hs:(A)rfs_history)) W a b` THEN
  REWRITE_TAC[P2AH_PERSISTS] THEN DISCH_THEN(MP_TAC o SPEC `b:real`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]]);;

let P2AH_HISTORY_REGION_THM = prove
 (`!u:A->bool. P2AH_HISTORY_REGION_STATEMENT u`,
  REWRITE_TAC[P2AH_HISTORY_REGION_STATEMENT] THEN MATCH_ACCEPT_TAC P2AH_HISTORY_REGION);;

(* ------------------------------------------------------------------------- *)
(* Smoothness up to the initial time is transported along an identity       *)
(* diffeomorphism.  The chart condition of ricci_flow_from is               *)
(* pde_tfam_from; in a chart of the new atlas it is local (PDM_UPTO_LOCAL), *)
(* and near each point the representative is the pullback, by a smooth      *)
(* chart transition, of the representative in a chart of the old atlas,     *)
(* whose extension below the initial time pulls back to one of the new      *)
(* representative (PDG_MPULLBACK_SMOOTH_TD, PDG_UPTO_FROM_OPEN).            *)
(* ------------------------------------------------------------------------- *)

let P2AH_RFF_TFAM = prove
 (`!top atlas a b (g:real->A->real^N^N).
     ricci_flow_from (top,atlas) a b g <=>
     ricci_flow_on (top,atlas) a b g /\ riemannian_metric atlas (g a) /\
     pde_tfam_from atlas a b g`,
  REWRITE_TAC[ricci_flow_from; pde_tfam_from]);;

let P2AH_UPTO_PULLBACK_CHART = prove
 (`!top atlas1 atlas2 a b (g:real->A->real^N^N) c.
     smooth_manifold_atlas top atlas1 /\ smooth_manifold_atlas top atlas2 /\
     mfd_diffeo top atlas2 (topspace top) top atlas1 (topspace top) (\x. x) (\x. x) /\
     a < b /\ pde_tfam_from atlas1 a b g /\ c IN atlas2
     ==> pde_upto a b (IMAGE (SND c) (FST c))
           (\t y. (vectorize:real^N^N->real^(N,N)finite_prod)
                  (metric_local atlas2 c (mfd_pullback_metric atlas2 atlas1 (\x. x) (g t)) y))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!t. mfd_isometry (top,atlas2)
          (mfd_pullback_metric atlas2 atlas1 (\x:A. x) ((g:real->A->real^N^N) t))
          (top,atlas1) (g t) (\x. x) (\x. x)`
  (LABEL_TAC "ISO") THENL
   [GEN_TAC THEN MATCH_MP_TAC MFD_ISOMETRY_PULLBACK THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_smooth_map (atlas2:((A->bool)#(A->real^N))->bool)
                   (atlas1:((A->bool)#(A->real^N))->bool) (topspace top) (\x:A. x)`
  (LABEL_TAC "SMAP") THENL [ASM_MESON_TAC[mfd_diffeo]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas2:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `FST(c:(A->bool)#(A->real^N)) SUBSET topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET]; ALL_TAC] THEN
  MATCH_MP_TAC PDM_UPTO_LOCAL THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `y0:real^N` THEN DISCH_TAC THEN
  SUBGOAL_THEN `?x0:A. x0 IN FST(c:(A->bool)#(A->real^N)) /\ SND c x0 = (y0:real^N)`
  (X_CHOOSE_THEN `x0:A` STRIP_ASSUME_TAC) THENL
   [UNDISCH_TAC `(y0:real^N) IN IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)` THEN
    REWRITE_TAC[IN_IMAGE] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas1:((A->bool)#(A->real^N))->bool`; `x0:A`]
                CHART_AT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
  SPEC_TAC(`chart_at (atlas1:((A->bool)#(A->real^N))->bool) (x0:A)`,
           `c1:(A->bool)#(A->real^N)`) THEN
  X_GEN_TAC `c1:(A->bool)#(A->real^N)` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas1:((A->bool)#(A->real^N))->bool`;
                 `c1:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!y. y IN IMAGE (SND(c:(A->bool)#(A->real^N)))
                   (FST c INTER FST(c1:(A->bool)#(A->real^N)))
        ==> chart_inv c y IN FST c /\ chart_inv c y IN FST c1 /\
            SND c (chart_inv c y) = (y:real^N)`
  (LABEL_TAC "N0P") THENL
   [REWRITE_TAC[FORALL_IN_IMAGE; IN_INTER] THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `open (IMAGE (SND(c:(A->bool)#(A->real^N)))
                      (FST c INTER FST(c1:(A->bool)#(A->real^N))))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas2:((A->bool)#(A->real^N))->bool`;
                   `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`;
                   `FST(c1:(A->bool)#(A->real^N))`] MFDR_RESTRICT_IMAGE_OPEN) THEN
    ASM_REWRITE_TAC[PAIR];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on (IMAGE (SND(c:(A->bool)#(A->real^N)))
                         (FST c INTER FST(c1:(A->bool)#(A->real^N))))
                  (SND c1 o (\x:A. x) o chart_inv c)`
  ASSUME_TAC THENL
   [USE_THEN "SMAP" (MP_TAC o SPECL [`c:(A->bool)#(A->real^N)`;
                                      `c1:(A->bool)#(A->real^N)`] o
                     REWRITE_RULE[mfd_smooth_map]) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    AP_TERM_TAC THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INTER] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `c1:(A->bool)#(A->real^N)` o
              GEN_REWRITE_RULE I [pde_tfam_from]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e1:real`
    (X_CHOOSE_THEN `F1:real^(1,N)finite_sum->real^(N,N)finite_prod` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `IMAGE (SND(c:(A->bool)#(A->real^N)))
                    (FST c INTER FST(c1:(A->bool)#(A->real^N)))` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[IN_IMAGE; IN_INTER] THEN EXISTS_TAC `x0:A` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL [MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[INTER_SUBSET]; ALL_TAC] THEN
  MATCH_MP_TAC PDG_UPTO_FROM_OPEN THEN
  MAP_EVERY EXISTS_TAC
   [`interval(lift(a - e1),lift b) PCROSS
       IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c INTER FST(c1:(A->bool)#(A->real^N)))`;
    `\w:real^(1,N)finite_sum.
       (vectorize:real^N^N->real^(N,N)finite_prod)
       (mpullback (SND(c1:(A->bool)#(A->real^N)) o (\x:A. x) o
                   chart_inv (c:(A->bool)#(A->real^N)))
          (\z. (matrify:real^(N,N)finite_prod->real^N^N) (F1(pastecart (fstcart w) z)))
          (sndcart w))`] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL];
    MP_TAC(ISPECL
     [`interval(lift(a - e1),lift b) PCROSS
         IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c INTER FST(c1:(A->bool)#(A->real^N)))`;
      `interval(lift(a - e1),lift b) PCROSS IMAGE (SND(c1:(A->bool)#(A->real^N))) (FST c1)`;
      `\w:real^(1,N)finite_sum.
         (SND(c1:(A->bool)#(A->real^N)) o (\x:A. x) o chart_inv (c:(A->bool)#(A->real^N)))
         (sndcart w)`;
      `F1:real^(1,N)finite_sum->real^(N,N)finite_prod`] PDG_MPULLBACK_SMOOTH_TD) THEN
    REWRITE_TAC[] THEN BETA_TAC THEN REWRITE_TAC[SNDCART_PASTECART; ETA_AX] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL] THEN
    CONJ_TAC THENL
     [SUBGOAL_THEN
       `(\w:real^(1,N)finite_sum.
           (SND(c1:(A->bool)#(A->real^N)) o (\x:A. x) o
            chart_inv (c:(A->bool)#(A->real^N))) (sndcart w)) =
        (SND c1 o (\x:A. x) o chart_inv c) o sndcart`
      SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
      EXISTS_TAC `IMAGE (SND(c:(A->bool)#(A->real^N)))
                        (FST c INTER FST(c1:(A->bool)#(A->real^N)))` THEN
      ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL] THEN CONJ_TAC THENL
       [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_PASTECART;
                    PASTECART_IN_PCROSS; SNDCART_PASTECART] THEN
        MESON_TAC[];
        MP_TAC(ISPECL
         [`interval(lift(a - e1),lift b) PCROSS
             IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c INTER FST(c1:(A->bool)#(A->real^N)))`;
          `\x:real^(1,N)finite_sum. x`] SMOOTH_MAP_ON_SNDCART_OPEN) THEN
        ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; SMOOTH_MAP_ON_ID] THEN
        MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
        REWRITE_TAC[FUN_EQ_THM; o_THM]];
      REWRITE_TAC[FORALL_PASTECART; PASTECART_IN_PCROSS; FSTCART_PASTECART;
                  SNDCART_PASTECART; o_THM] THEN
      MAP_EVERY X_GEN_TAC [`t:real^1`; `y:real^N`] THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
      USE_THEN "N0P" (MP_TAC o SPEC `y:real^N`) THEN ASM_SIMP_TAC[]];
    BETA_TAC THEN
    REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; PASTECART_IN_PCROSS;
                IN_INTERVAL_1; LIFT_DROP] THEN
    MAP_EVERY X_GEN_TAC [`t:real`; `y:real^N`] THEN STRIP_TAC THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    AP_TERM_TAC THEN
    USE_THEN "N0P" (MP_TAC o SPEC `y:real^N`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `mpullback (SND(c1:(A->bool)#(A->real^N)) o (\x:A. x) o
                           chart_inv (c:(A->bool)#(A->real^N)))
                  (metric_local atlas1 c1 ((g:real->A->real^N^N) t)) y` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC PDG_MPULLBACK_AT THEN REWRITE_TAC[o_THM] THEN
      ASM_SIMP_TAC[FUN_IN_IMAGE; MATRIFY_VECTORIZE];
      CONV_TAC SYM_CONV THEN USE_THEN "ISO" (MP_TAC o SPEC `t:real`) THEN
      REWRITE_TAC[mfd_isometry] THEN
      DISCH_THEN(MP_TAC o SPECL [`c:(A->bool)#(A->real^N)`;
                                 `c1:(A->bool)#(A->real^N)`] o CONJUNCT2) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
      REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
      EXISTS_TAC `chart_inv (c:(A->bool)#(A->real^N)) y` THEN
      BETA_TAC THEN ASM_REWRITE_TAC[]]]);;

let P2AH_RFF_ATLAS_CHANGE = prove
 (`!top atlas1 atlas2 a b (g:real->A->real^N^N).
     smooth_manifold_atlas top atlas2 /\
     mfd_diffeo top atlas2 (topspace top) top atlas1 (topspace top) (\x. x) (\x. x) /\
     ricci_flow_from (top,atlas1) a b g
     ==> ricci_flow_from (top,atlas2) a b
           (\t. mfd_pullback_metric atlas2 atlas1 (\x. x) (g t))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[P2AH_RFF_TFAM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
  SUBGOAL_THEN `smooth_manifold_atlas top (atlas1:((A->bool)#(A->real^N))->bool) /\ a < b`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[ricci_flow_on]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC P3S_RFO_ATLAS_CHANGE THEN ASM_REWRITE_TAC[];
    BETA_TAC THEN MATCH_MP_TAC RIEMANNIAN_METRIC_PULLBACK THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `top:A topology`; `\x:A. x`] THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[PDM_TFAM_FROM_UPTO] THEN BETA_TAC THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC P2AH_UPTO_PULLBACK_CHART THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[]]);;

(* The analogue of P3S_RFO_TRANSPORT_W for ricci_flow_from.                  *)

let P2AH_RFF_TRANSPORT_W = prove
 (`!topY atlasY topX atlasX W a b (g:real->A->real^N^N).
     smooth_manifold_atlas topY atlasY /\
     mfd_diffeo topY atlasY W topX atlasX W (\x. x) (\x. x) /\
     subtopology topY W = subtopology topX W /\
     ricci_flow_from (topX,atlasX) a b g
     ==> ricci_flow_from (subtopology topY W,restrict_atlas atlasY W) a b
           (\t. restrict_metric atlasY W
                  (mfd_pullback_metric atlasY atlasX (\x. x) (g t)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `smooth_manifold_atlas topX (atlasX:((A->bool)#(A->real^N))->bool)`
  ASSUME_TAC THENL [ASM_MESON_TAC[ricci_flow_from; ricci_flow_on]; ALL_TAC] THEN
  SUBGOAL_THEN `open_in topY (W:A->bool) /\ open_in topX W` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[mfd_diffeo]; ALL_TAC] THEN
  SUBGOAL_THEN `topspace(subtopology topY (W:A->bool)) = W` ASSUME_TAC THENL
   [REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN
    MP_TAC(ISPECL [`topY:A topology`; `W:A->bool`] OPEN_IN_SUBSET) THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC PDE_RFF_CONG THEN
  EXISTS_TAC
   `\t. mfd_pullback_metric (restrict_atlas atlasY W)
          (restrict_atlas (atlasX:((A->bool)#(A->real^N))->bool) W) (\x:A. x)
          (restrict_metric atlasX W ((g:real->A->real^N^N) t))` THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL
     [`subtopology topY (W:A->bool)`;
      `restrict_atlas (atlasX:((A->bool)#(A->real^N))->bool) W`;
      `restrict_atlas (atlasY:((A->bool)#(A->real^N))->bool) W`;
      `a:real`; `b:real`;
      `\t. restrict_metric (atlasX:((A->bool)#(A->real^N))->bool) W
             ((g:real->A->real^N^N) t)`] P2AH_RFF_ATLAS_CHANGE) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MANIFOLD_ATLAS_RESTRICT THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`topY:A topology`; `atlasY:((A->bool)#(A->real^N))->bool`;
                     `W:A->bool`; `topX:A topology`;
                     `atlasX:((A->bool)#(A->real^N))->bool`; `W:A->bool`;
                     `W:A->bool`; `W:A->bool`; `\x:A. x`; `\x:A. x`]
                    APX_MFD_DIFFEO_RESTRICT) THEN
      ASM_REWRITE_TAC[SUBSET_REFL] THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      UNDISCH_TAC `subtopology topY (W:A->bool) = subtopology topX W` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P2CF_RFF_RESTRICT THEN
      ASM_REWRITE_TAC[]];
    REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC P3S_RESTRICT_PULLBACK_EQ THEN
    MAP_EVERY EXISTS_TAC [`topY:A topology`; `topX:A topology`] THEN
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Smoothness up to the initial time a of a region flow when W is open in   *)
(* the slice a (the stage flow of a is smooth up to its initial time and is *)
(* transported to the atlas of b), the empty slices outside [0,horizon),    *)
(* and the region part of P2C_HISTORY_REGULAR: conjuncts 2-4 of             *)
(* p2c_regular_view (rfs_view hs) (P2AH_P2C_REGIONS).                       *)
(* ------------------------------------------------------------------------- *)

let P2AH_HISTORY_FROM = prove
 (`!(hs:(A)rfs_history) W a b.
     rfs_history_ok hs /\ &0 <= a /\ a < b /\ b < rfs_horizon hs /\
     open_in (rfs_top_at hs a) W /\ rfs_persists (rfs_view hs) W a b
     ==> ricci_flow_from (subtopology (rfs_top_at hs b) W,restrict_atlas (rfs_atlas_at hs b) W)
                         a b (p2ah_fam hs W b)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `b:real`] P2AH_SLAB_EXISTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:num` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `a:real`] P2AH_SLAB_EXISTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `k:num`] P2AH_STAGE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "SL"))))) THEN
  ABBREV_TAC `c = (a + min b (hs_time (hs:(A)rfs_history) (k + 1))) / &2` THEN
  SUBGOAL_THEN `a < c /\ c < b /\ c < hs_time (hs:(A)rfs_history) (k + 1) /\
                hs_time hs k <= c`
  STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `smooth_manifold_atlas (rfs_top_at hs b) (rfs_atlas_at (hs:(A)rfs_history) b)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_persists (rfs_view (hs:(A)rfs_history)) W a b` THEN
    REWRITE_TAC[P2AH_PERSISTS] THEN DISCH_THEN(MP_TAC o SPEC `b:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_diffeo (hs_top hs k) (hs_atlas hs k) W
               (rfs_top_at hs b) (rfs_atlas_at (hs:(A)rfs_history) b) W (\y. y) (\y. y)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`hs:(A)rfs_history`; `m:num`; `W:A->bool`; `a:real`; `b:real`; `c:real`]
                  P2AH_DIFFEO_CHAIN) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "SL" (MP_TAC o SPEC `c:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`hs_top (hs:(A)rfs_history) k`; `hs_atlas (hs:(A)rfs_history) k`;
                 `rfs_top_at (hs:(A)rfs_history) b`; `rfs_atlas_at (hs:(A)rfs_history) b`;
                 `W:A->bool`] P2AH_DIFFEO_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`rfs_top_at (hs:(A)rfs_history) b`; `rfs_atlas_at (hs:(A)rfs_history) b`;
                 `hs_top (hs:(A)rfs_history) k`; `hs_atlas (hs:(A)rfs_history) k`;
                 `W:A->bool`; `a:real`; `hs_time (hs:(A)rfs_history) (k + 1)`;
                 `hs_metric (hs:(A)rfs_history) k`] P2AH_RFF_TRANSPORT_W) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PDE_RFF_RESTRICT THEN
    MAP_EVERY EXISTS_TAC [`hs_time (hs:(A)rfs_history) k`;
                          `hs_time (hs:(A)rfs_history) (k + 1)`] THEN
    ASM_REWRITE_TAC[REAL_LE_REFL];
    DISCH_TAC] THEN
  SUBGOAL_THEN
   `ricci_flow_from (subtopology (rfs_top_at hs b) W,restrict_atlas (rfs_atlas_at hs b) W)
                    a c (p2ah_famx (hs:(A)rfs_history) W b)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC PDE_RFF_CONG THEN
    EXISTS_TAC `\t. restrict_metric (rfs_atlas_at (hs:(A)rfs_history) b) W
                      (mfd_pullback_metric (rfs_atlas_at hs b) (hs_atlas hs k) (\x:A. x)
                                           (hs_metric hs k t))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC PDE_RFF_RESTRICT THEN
      MAP_EVERY EXISTS_TAC [`a:real`; `hs_time (hs:(A)rfs_history) (k + 1)`] THEN
      ASM_REWRITE_TAC[REAL_LE_REFL] THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER] THEN
      MAP_EVERY X_GEN_TAC [`t:real`; `x:A`] THEN STRIP_TAC THEN BETA_TAC THEN
      USE_THEN "SL" (MP_TAC o SPEC `t:real`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
      ASM_REWRITE_TAC[p2ah_famx]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ricci_flow_on (subtopology (rfs_top_at hs b) W,restrict_atlas (rfs_atlas_at hs b) W)
                  a ((b + hs_time hs (m + 1)) / &2) (p2ah_famx (hs:(A)rfs_history) W b)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P2AH_RF_CHAIN THEN EXISTS_TAC `m:num` THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC PDE_RFF_CONG THEN EXISTS_TAC `p2ah_famx (hs:(A)rfs_history) W b` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC PDE_RFF_RESTRICT THEN
    MAP_EVERY EXISTS_TAC [`a:real`; `(b + hs_time (hs:(A)rfs_history) (m + 1)) / &2`] THEN
    REWRITE_TAC[REAL_LE_REFL] THEN CONJ_TAC THENL
     [MATCH_MP_TAC PDE_RFF_FROM_ON THEN EXISTS_TAC `c:real` THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC P2AH_FAM_FAMX THEN ASM_REWRITE_TAC[]]);;

(* The view of a history and its region family in the P2C vocabulary.        *)

let P2AH_VIEW_PARTS = prove
 (`!(hs:(A)rfs_history) t.
     rfs_vtop (rfs_view hs) t = rfs_top_at hs t /\
     rfs_vatlas (rfs_view hs) t = rfs_atlas_at hs t /\
     rfs_vmetric (rfs_view hs) t = rfs_metric_at hs t`,
  REWRITE_TAC[rfs_view; rfs_vtop; rfs_vatlas; rfs_vmetric]);;

let P2AH_VFAM = prove
 (`!(hs:(A)rfs_history) W b. p2c_vfam (rfs_view hs) W b = p2ah_fam hs W b`,
  REWRITE_TAC[FUN_EQ_THM; p2c_vfam; p2ah_fam; P2AH_VIEW_PARTS]);;

(* Slices outside [0,horizon) are empty, so only W = {} is open there.      *)

let P2AH_SLICE_EMPTY = prove
 (`!(hs:(A)rfs_history) s W.
     ~(&0 <= s /\ s < rfs_horizon hs) /\ open_in (rfs_top_at hs s) W ==> W = {}`,
  REWRITE_TAC[rfs_top_at; rfs_live; rfs_horizon] THEN REPEAT GEN_TAC THEN
  ASM_CASES_TAC `&0 <= s /\ s < hs_time (hs:(A)rfs_history) (hs_count hs + 1)` THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o MATCH_MP OPEN_IN_SUBSET) THEN
  REWRITE_TAC[TOPSPACE_DISCRETE_TOPOLOGY] THEN SET_TAC[]);;

let P2AH_PERSISTS_NONEMPTY = prove
 (`!(hs:(A)rfs_history) W a b.
     a < b /\ rfs_persists (rfs_view hs) W a b /\ ~(W = {})
     ==> &0 <= a /\ b < rfs_horizon hs`,
  REWRITE_TAC[P2AH_PERSISTS] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `(a + min b (&0)) / &2`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    UNDISCH_TAC `~(W:A->bool = {})` THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC P2AH_SLICE_EMPTY THEN
    MAP_EVERY EXISTS_TAC [`hs:(A)rfs_history`; `(a + min b (&0)) / &2`] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `b:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    UNDISCH_TAC `~(W:A->bool = {})` THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC P2AH_SLICE_EMPTY THEN
    MAP_EVERY EXISTS_TAC [`hs:(A)rfs_history`; `b:real`] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Second main theorem: the region part of P2C_HISTORY_REGULAR, literally    *)
(* conjuncts 2, 3 and 4 of p2c_regular_view (rfs_view hs) for rfs_history_ok *)
(* hs (no restriction on a and b: a nonempty persisting set lives in         *)
(* [0,horizon)).                                                             *)
(* ------------------------------------------------------------------------- *)

let P2AH_P2C_REGIONS_STATEMENT = new_definition
 `P2AH_P2C_REGIONS_STATEMENT (u:A->bool) <=>
    !hs:(A)rfs_history.
       rfs_history_ok hs
       ==> (!W a b. a < b /\ rfs_persists (rfs_view hs) W a b
                    ==> p2c_vflow (rfs_view hs) W a b) /\
           (!W a b. a < b /\ open_in (rfs_vtop (rfs_view hs) a) W /\
                    rfs_persists (rfs_view hs) W a b
                    ==> p2c_vflow_from (rfs_view hs) W a b) /\
           (!W a b s. a < s /\ s <= b /\ rfs_persists (rfs_view hs) W a b
                      ==> mfd_diffeo (rfs_vtop (rfs_view hs) s) (rfs_vatlas (rfs_view hs) s) W
                                     (rfs_vtop (rfs_view hs) b) (rfs_vatlas (rfs_view hs) b) W
                                     (\y:A. y) (\y. y))`;;

let P2AH_P2C_REGIONS = prove
 (`!hs:(A)rfs_history.
     rfs_history_ok hs
     ==> (!W a b. a < b /\ rfs_persists (rfs_view hs) W a b
                  ==> p2c_vflow (rfs_view hs) W a b) /\
         (!W a b. a < b /\ open_in (rfs_vtop (rfs_view hs) a) W /\
                  rfs_persists (rfs_view hs) W a b
                  ==> p2c_vflow_from (rfs_view hs) W a b) /\
         (!W a b s. a < s /\ s <= b /\ rfs_persists (rfs_view hs) W a b
                    ==> mfd_diffeo (rfs_vtop (rfs_view hs) s) (rfs_vatlas (rfs_view hs) s) W
                                   (rfs_vtop (rfs_view hs) b) (rfs_vatlas (rfs_view hs) b) W
                                   (\y:A. y) (\y. y))`,
  GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[p2c_vflow_from; p2c_vflow; P2AH_VIEW_PARTS; P2AH_VFAM] THEN
  REPEAT CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`W:A->bool`; `a:real`; `b:real`] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `W:A->bool = {}` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN MATCH_MP_TAC P2CF_RFU_EMPTY THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `rfs_persists (rfs_view (hs:(A)rfs_history)) {} a b` THEN
      REWRITE_TAC[P2AH_PERSISTS] THEN DISCH_THEN(MP_TAC o SPEC `b:real`) THEN
      ASM_SIMP_TAC[REAL_LE_REFL];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`hs:(A)rfs_history`; `W:A->bool`; `a:real`; `b:real`]
                  P2AH_PERSISTS_NONEMPTY) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`hs:(A)rfs_history`; `W:A->bool`; `a:real`; `b:real`]
                  P2AH_HISTORY_REGION) THEN
    ASM_REWRITE_TAC[P2AH_REGION_FLOW_ALT] THEN SIMP_TAC[];
    MAP_EVERY X_GEN_TAC [`W:A->bool`; `a:real`; `b:real`] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `W:A->bool = {}` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN
      SUBGOAL_THEN `smooth_manifold_atlas (rfs_top_at hs b)
                      (rfs_atlas_at (hs:(A)rfs_history) b)` ASSUME_TAC THENL
       [UNDISCH_TAC `rfs_persists (rfs_view (hs:(A)rfs_history)) {} a b` THEN
        REWRITE_TAC[P2AH_PERSISTS] THEN DISCH_THEN(MP_TAC o SPEC `b:real`) THEN
        ASM_SIMP_TAC[REAL_LE_REFL];
        ASM_SIMP_TAC[P2CF_RFU_EMPTY; P2CF_RFF_EMPTY]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`hs:(A)rfs_history`; `W:A->bool`; `a:real`; `b:real`]
                  P2AH_PERSISTS_NONEMPTY) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`hs:(A)rfs_history`; `W:A->bool`; `a:real`; `b:real`]
                    P2AH_HISTORY_REGION) THEN
      ASM_REWRITE_TAC[P2AH_REGION_FLOW_ALT] THEN SIMP_TAC[];
      MATCH_MP_TAC P2AH_HISTORY_FROM THEN ASM_REWRITE_TAC[]];
    MAP_EVERY X_GEN_TAC [`W:A->bool`; `a:real`; `b:real`; `s:real`] THEN STRIP_TAC THEN
    ASM_CASES_TAC `W:A->bool = {}` THEN ASM_REWRITE_TAC[P2CF_DIFFEO_EMPTY] THEN
    SUBGOAL_THEN `a < b` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ISPECL [`hs:(A)rfs_history`; `W:A->bool`; `a:real`; `b:real`]
                  P2AH_PERSISTS_NONEMPTY) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`hs:(A)rfs_history`; `W:A->bool`; `a:real`; `b:real`]
                  P2AH_HISTORY_REGION) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `s:real` o CONJUNCT2) THEN
    ASM_REWRITE_TAC[]]);;

let P2AH_P2C_REGIONS_THM = prove
 (`!u:A->bool. P2AH_P2C_REGIONS_STATEMENT u`,
  REWRITE_TAC[P2AH_P2C_REGIONS_STATEMENT] THEN MATCH_ACCEPT_TAC P2AH_P2C_REGIONS);;

