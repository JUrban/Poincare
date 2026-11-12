(* ========================================================================= *)
(* Unit pc_p3e_152h: MT Prop 15.2 (p. 353) for histories.  From a valid      *)
(* history, an evolving beta eps-neck at (x,t) of length t0 and a strong     *)
(* beta eps/2-neck at the earlier time with the image containment, build the *)
(* gluing data p3e_gdata of the abstract core (pc_p3e_152, P3E_GLUE_CORE)    *)
(* and from its conclusion the strong eps-neck e'' = e at (x,t).  Main       *)
(* theorems: P3E_PROP_15_2 (!u. P3_PROP_15_2_STATEMENT u) and                *)
(* P3E_PROP_15_2_ROUTE.                                                      *)
(* ========================================================================= *)

needs "src/pc_p3e_152.ml";;
needs "src/pc_p2c_flseq.ml";;
needs "src/pc_p2c_hreg.ml";;
needs "src/pc_p2a_hreg.ml";;
needs "src/pc_apx_chain.ml";;
needs "src/pc_p2b_979.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Generic regularity in time.  A map F smooth on an open set                *)
(* of real^(1,N) containing {a} x K (K compact) has spatial jets of its time *)
(* slices that converge uniformly on K as the time decreases to a: the     *)
(* uniform jet continuity clause of p3e_gdata at the junction time.          *)
(* ------------------------------------------------------------------------- *)

let P3E_SLICE_JET_UCONT = prove
 (`!(FF:real^(1,N)finite_sum->real^K) S a (K:real^N->bool) m e.
     open S /\ smooth_map_on S FF /\ compact K /\
     (!y. y IN K ==> pastecart (lift a) y IN S) /\ &0 < e
     ==> ?dl. &0 < dl /\
              !s y l. a <= s /\ s < a + dl /\ y IN K /\ l IN pde_index_lists m (:N)
                      ==> norm(iterated_partial l (\y. FF(pastecart (lift s) y)) y -
                               iterated_partial l (\y. FF(pastecart (lift a) y)) y) < e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  (* a uniform neighbourhood of {a} x K inside S *)
  MP_TAC(ISPECL [`IMAGE (\y:real^N. pastecart (lift a) y) K`;
                 `(:real^(1,N)finite_sum) DIFF S`] SEPARATE_COMPACT_CLOSED) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN
      REWRITE_TAC[CONTINUOUS_ON_CONST; CONTINUOUS_ON_ID];
      REWRITE_TAC[GSYM OPEN_CLOSED] THEN ASM_REWRITE_TAC[];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!y s. y IN K /\ abs(s - a) < r ==> pastecart (lift s) (y:real^N) IN S`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`pastecart (lift a) (y:real^N)`;
                                  `pastecart (lift s) (y:real^N)`]) THEN
    REWRITE_TAC[IN_DIFF; IN_UNIV; DIST_PASTECART_CANCEL; DIST_LIFT] THEN
    MATCH_MP_TAC(TAUT `a /\ ~c ==> (a /\ ~b ==> c) ==> b`) THEN CONJ_TAC THENL
     [REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `y:real^N` THEN ASM_REWRITE_TAC[];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `compact (interval[lift a,lift(a + r / &2)] PCROSS (K:real^N->bool)) /\ (interval[lift a,lift(a + r / &2)] PCROSS (K:real^N->bool)) SUBSET S` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[COMPACT_PCROSS; COMPACT_INTERVAL] THEN
    REWRITE_TAC[SUBSET; FORALL_PASTECART; PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP] THEN
    MAP_EVERY X_GEN_TAC [`u:real^1`; `y:real^N`] THEN STRIP_TAC THEN
    SUBST1_TAC(SYM(SPEC `u:real^1` (CONJUNCT1 LIFT_DROP))) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* uniform continuity of each space-time partial on C *)
  SUBGOAL_THEN
   `!l. l IN pde_index_lists m (:N)
        ==> ?d. &0 < d /\
                !z z'. z IN (interval[lift a,lift(a + r / &2)] PCROSS (K:real^N->bool)) /\ z' IN (interval[lift a,lift(a + r / &2)] PCROSS (K:real^N->bool)) /\ dist(z',z) < d
                       ==> dist(iterated_partial (MAP (\k. 1 + k) l)
                                  (FF:real^(1,N)finite_sum->real^K) z',
                                iterated_partial (MAP (\k. 1 + k) l) FF z) < e`
  MP_TAC THENL
   [X_GEN_TAC `l:(num)list` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`iterated_partial (MAP (\k. 1 + k) l) (FF:real^(1,N)finite_sum->real^K)`;
                   `(interval[lift a,lift(a + r / &2)] PCROSS (K:real^N->bool))`] COMPACT_UNIFORMLY_CONTINUOUS) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `S:real^(1,N)finite_sum->bool` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS THEN MATCH_MP_TAC SMOOTH_MAP_ON_ITERATED_PARTIAL THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[uniformly_continuous_on] THEN DISCH_THEN(MP_TAC o SPEC `e:real`) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `dd:(num)list->real` (LABEL_TAC "DD") o
             REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM]) THEN
  SUBGOAL_THEN `FINITE (IMAGE (dd:(num)list->real) (pde_index_lists m (:N))) /\
                ~(IMAGE dd (pde_index_lists m (:N)) = {})` STRIP_ASSUME_TAC THENL
   [SIMP_TAC[FINITE_IMAGE; PDE_INDEX_LISTS_FINITE; IMAGE_EQ_EMPTY] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `[]:(num)list` THEN
    REWRITE_TAC[pde_index_lists; IN_ELIM_THM; LENGTH; ALL; LE_0];
    ALL_TAC] THEN
  EXISTS_TAC `min (r / &2) (inf (IMAGE (dd:(num)list->real) (pde_index_lists m (:N))))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[REAL_LT_MIN] THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_LT_INF_FINITE; FORALL_IN_IMAGE] THEN
      X_GEN_TAC `l:(num)list` THEN DISCH_TAC THEN
      USE_THEN "DD" (MP_TAC o SPEC `l:(num)list`) THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`s:real`; `y:real^N`; `l:(num)list`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `inf (IMAGE (dd:(num)list->real) (pde_index_lists m (:N))) <= dd l`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_INF_LE_FINITE] THEN EXISTS_TAC `(dd:(num)list->real) l` THEN
    REWRITE_TAC[REAL_LE_REFL; IN_IMAGE] THEN EXISTS_TAC `l:(num)list` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `ALL (\k. 1 <= k /\ k <= dimindex(:N)) l` ASSUME_TAC THENL
   [UNDISCH_TAC `l IN pde_index_lists m (:N)` THEN SIMP_TAC[pde_index_lists; IN_ELIM_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN `pastecart (lift s) (y:real^N) IN (interval[lift a,lift(a + r / &2)] PCROSS (K:real^N->bool)) /\ pastecart (lift a) y IN (interval[lift a,lift(a + r / &2)] PCROSS (K:real^N->bool))`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `pastecart (lift s) (y:real^N) IN S /\ pastecart (lift a) y IN S`
  STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`l:(num)list`; `FF:real^(1,N)finite_sum->real^K`;
                 `S:real^(1,N)finite_sum->bool`; `lift s`; `y:real^N`]
                PDE_ST_SLICE_ITERATED) THEN
  MP_TAC(ISPECL [`l:(num)list`; `FF:real^(1,N)finite_sum->real^K`;
                 `S:real^(1,N)finite_sum->bool`; `lift a`; `y:real^N`]
                PDE_ST_SLICE_ITERATED) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN
  REWRITE_TAC[GSYM dist] THEN
  USE_THEN "DD" (MP_TAC o SPEC `l:(num)list`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[DIST_PASTECART_CANCEL; DIST_LIFT] THEN ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* An evolving neck in the view of a valid history.  Its basic               *)
(* facts (the persistence interval lies in [0, horizon)), the slices just    *)
(* after a time (slabs are left closed), the left end of a persistence      *)
(* interval, and the neck map as a parametrization of every slice of the    *)
(* closed persistence interval (identity diffeomorphisms between slices,    *)
(* conjuncts 4 and 5 of p2c_regular_view).                                   *)
(* ------------------------------------------------------------------------- *)

let P3E_HIST_REGULAR = prove
 (`!hs:(A)rfs_history. rfs_history_ok hs ==> p2c_regular_view (rfs_view hs)`,
  MP_TAC(ISPEC `(:A)` P2CY_HISTORY_REGULAR) THEN
  REWRITE_TAC[P2C_HISTORY_REGULAR_STATEMENT]);;

let P3E_EVNECK_BASIC = prove
 (`!(hs:(A)rfs_history) b x t len (e:real^3->A).
     rfs_history_ok hs /\ rfs_evolving_neck (rfs_view hs) b x t len e
     ==> &0 < b /\ &0 < len /\
         &0 < mfd_scalar (rfs_atlas_at hs t) (rfs_metric_at hs t) x /\
         x IN IMAGE e (sphere(vec 0,&1)) /\ x IN IMAGE e (rfs_neck_dom b) /\
         smooth_manifold_atlas (rfs_top_at hs t) (rfs_atlas_at hs t) /\
         mfd_param (rfs_top_at hs t) (rfs_atlas_at hs t) (rfs_neck_dom b) e /\
         &0 <= t - len / mfd_scalar (rfs_atlas_at hs t) (rfs_metric_at hs t) x /\
         t < rfs_horizon hs /\
         rfs_persists (rfs_view hs) (IMAGE e (rfs_neck_dom b))
           (t - len / mfd_scalar (rfs_atlas_at hs t) (rfs_metric_at hs t) x) t /\
         rfs_close_on (rfs_kreg b) b (rfs_neck_dom b) (cylinder_flow (&0))
           (\y. mfd_scalar (rfs_atlas_at hs t) (rfs_metric_at hs t) x %%
                rfs_pullback (rfs_atlas_at hs t) e (rfs_metric_at hs t) y) /\
         rfs_close_fam (rfs_kreg b) b {s | --len < s /\ s <= &0} (rfs_neck_dom b)
           cylinder_flow
           (\s y. mfd_scalar (rfs_atlas_at hs t) (rfs_metric_at hs t) x %%
                  rfs_pullback
                    (rfs_atlas_at hs
                       (t + s / mfd_scalar (rfs_atlas_at hs t) (rfs_metric_at hs t) x)) e
                    (rfs_metric_at hs
                       (t + s / mfd_scalar (rfs_atlas_at hs t) (rfs_metric_at hs t) x)) y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rfs_view; rfs_evolving_neck; rfs_neck] THEN
  ABBREV_TAC `R = mfd_scalar (rfs_atlas_at (hs:(A)rfs_history) t) (rfs_metric_at hs t) x` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `(x:A) IN IMAGE e (rfs_neck_dom b)` ASSUME_TAC THENL
   [MP_TAC(SPEC `b:real` P3E_UNIT_SPHERE_NECK_DOM) THEN ASM_REWRITE_TAC[] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `IMAGE (e:real^3->A) (rfs_neck_dom b)`;
                 `t - len / R`; `t:real`] P2AH_PERSISTS_NONEMPTY) THEN
  REWRITE_TAC[rfs_view] THEN ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&0 < d ==> t - d < t`) THEN MATCH_MP_TAC REAL_LT_DIV THEN
      ASM_REWRITE_TAC[];
      ASM SET_TAC[]];
    STRIP_TAC THEN ASM_REWRITE_TAC[]]);;

let P3E_HIST_SLAB_AFTER = prove
 (`!(hs:(A)rfs_history) t.
     rfs_history_ok hs /\ &0 <= t /\ t < rfs_horizon hs
     ==> ?d. &0 < d /\
             !s. t <= s /\ s <= t + d
                 ==> rfs_top_at hs s = rfs_top_at hs t /\
                     rfs_atlas_at hs s = rfs_atlas_at hs t /\
                     smooth_manifold_atlas (rfs_top_at hs t) (rfs_atlas_at hs t)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `t:real`] P2AH_SLAB_EXISTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `k:num`] P2AH_STAGE) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "SL"))))) THEN
  EXISTS_TAC `(hs_time (hs:(A)rfs_history) (k + 1) - t) / &2` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `s:real` THEN STRIP_TAC THEN
  USE_THEN "SL" (MP_TAC o SPEC `s:real`) THEN
  USE_THEN "SL" (MP_TAC o SPEC `t:real`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  ASM_REWRITE_TAC[]);;

let P3E_PERSISTS_LEFT = prove
 (`!(hs:(A)rfs_history) W a b.
     rfs_history_ok hs /\ &0 <= a /\ a < b /\ b < rfs_horizon hs /\
     rfs_persists (rfs_view hs) W a b
     ==> smooth_manifold_atlas (rfs_top_at hs a) (rfs_atlas_at hs a) /\
         open_in (rfs_top_at hs a) W`,
  REPEAT GEN_TAC THEN REWRITE_TAC[P2AH_PERSISTS] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `a:real`] P2AH_SLAB_EXISTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `k:num`] P2AH_STAGE) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "SL"))))) THEN
  ABBREV_TAC `s1 = min b ((a + hs_time (hs:(A)rfs_history) (k + 1)) / &2)` THEN
  SUBGOAL_THEN `a < s1 /\ s1 <= b /\ s1 < hs_time (hs:(A)rfs_history) (k + 1)`
  STRIP_ASSUME_TAC THENL [EXPAND_TAC "s1" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "SL" (MP_TAC o SPEC `s1:real`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  USE_THEN "SL" (MP_TAC o SPEC `a:real`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s1:real` o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "open_in")) (concl th))) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]]);;

let P3E_EVNECK_SLICE_PARAM = prove
 (`!(hs:(A)rfs_history) b x t len (e:real^3->A) s.
     rfs_history_ok hs /\ rfs_evolving_neck (rfs_view hs) b x t len e /\
     t - len / mfd_scalar (rfs_atlas_at hs t) (rfs_metric_at hs t) x <= s /\ s <= t
     ==> smooth_manifold_atlas (rfs_top_at hs s) (rfs_atlas_at hs s) /\
         open_in (rfs_top_at hs s) (IMAGE e (rfs_neck_dom b)) /\
         mfd_param (rfs_top_at hs s) (rfs_atlas_at hs s) (rfs_neck_dom b) e`,
  REPEAT GEN_TAC THEN
  ABBREV_TAC `R = mfd_scalar (rfs_atlas_at (hs:(A)rfs_history) t) (rfs_metric_at hs t) x` THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `b:real`; `x:A`; `t:real`; `len:real`;
                 `e:real^3->A`] P3E_EVNECK_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP P3E_HIST_REGULAR) THEN
  SUBGOAL_THEN `t - len / R < t` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 < d ==> t - d < t`) THEN MATCH_MP_TAC REAL_LT_DIV THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the slice s: manifold, W open, identity diffeo to the slice t *)
  SUBGOAL_THEN
   `smooth_manifold_atlas (rfs_top_at (hs:(A)rfs_history) s) (rfs_atlas_at hs s) /\
    open_in (rfs_top_at hs s) (IMAGE (e:real^3->A) (rfs_neck_dom b)) /\
    mfd_diffeo (rfs_top_at hs s) (rfs_atlas_at hs s) (IMAGE e (rfs_neck_dom b))
               (rfs_top_at hs t) (rfs_atlas_at hs t) (IMAGE e (rfs_neck_dom b))
               (\y. y) (\y. y)`
  STRIP_ASSUME_TAC THENL
   [ASM_CASES_TAC `s = t - len / R` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN
      MP_TAC(ISPECL [`hs:(A)rfs_history`; `IMAGE (e:real^3->A) (rfs_neck_dom b)`;
                     `t - len / R`; `t:real`] P3E_PERSISTS_LEFT) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `p2c_regular_view (rfs_view (hs:(A)rfs_history))` THEN
      REWRITE_TAC[p2c_regular_view; P2AH_VIEW_PARTS] THEN
      DISCH_THEN(MATCH_MP_TAC o last o CONJUNCTS) THEN ASM_REWRITE_TAC[];
      SUBGOAL_THEN `t - len / R < s` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      UNDISCH_TAC `rfs_persists (rfs_view (hs:(A)rfs_history)) (IMAGE (e:real^3->A)
                     (rfs_neck_dom b)) (t - len / R) t` THEN
      DISCH_THEN(fun th -> MP_TAC th THEN ASSUME_TAC th) THEN
      REWRITE_TAC[P2AH_PERSISTS] THEN DISCH_THEN(MP_TAC o SPEC `s:real`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `p2c_regular_view (rfs_view (hs:(A)rfs_history))` THEN
      REWRITE_TAC[p2c_regular_view; P2AH_VIEW_PARTS] THEN
      DISCH_THEN(MP_TAC o el 3 o CONJUNCTS) THEN
      DISCH_THEN MATCH_MP_TAC THEN EXISTS_TAC `t - len / R` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`rfs_top_at (hs:(A)rfs_history) t`; `rfs_atlas_at (hs:(A)rfs_history) t`;
                 `rfs_top_at (hs:(A)rfs_history) s`; `rfs_atlas_at (hs:(A)rfs_history) s`;
                 `rfs_neck_dom b`; `e:real^3->A`;
                 `IMAGE (e:real^3->A) (rfs_neck_dom b)`; `IMAGE (e:real^3->A) (rfs_neck_dom b)`;
                 `\y:A. y`; `\y:A. y`] MFD_PARAM_COMPOSE_DIFFEO) THEN
  ASM_REWRITE_TAC[SUBSET_REFL] THEN ANTS_TAC THENL
   [MATCH_MP_TAC MFD_DIFFEO_SYM THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[o_DEF; ETA_AX]]);;

(* ------------------------------------------------------------------------- *)
(* The transition map between two parametrizations of one                    *)
(* manifold with nested images: psi = e'^-1 o e is a diffeomorphism of D    *)
(* onto an open subset of D', with e' o psi = e on D.                        *)
(* ------------------------------------------------------------------------- *)

let P3E_TRANSITION_MAP = prove
 (`!(top:A topology) atlas D D' (e:real^3->A) e'.
     smooth_manifold_atlas top atlas /\
     mfd_param top atlas D e /\ mfd_param top atlas D' e' /\
     IMAGE e D SUBSET IMAGE e' D'
     ==> ?psi psi'. diffeomorphism_on D (IMAGE psi D) psi psi' /\
                    IMAGE psi D SUBSET D' /\
                    (!y. y IN D ==> e'(psi y) = e y) /\
                    (!y z. y IN D /\ z IN D' /\ e y = e' z ==> psi y = z)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `D:real^3->bool`; `e:real^3->A`] MFD_PARAM_MAPS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `ei:A->real^3` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `D':real^3->bool`; `e':real^3->A`] MFD_PARAM_MAPS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `ei':A->real^3` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `(ei':A->real^3) o (e:real^3->A)` THEN
  EXISTS_TAC `(ei:A->real^3) o (e':real^3->A)` THEN
  REWRITE_TAC[o_THM] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[GSYM MFD_DIFFEO_EUCLIDEAN; IMAGE_o] THEN
    MATCH_MP_TAC(INST_TYPE [`:real^3`,`:A`; `:A`,`:B`; `:real^3`,`:C`;
                            `:3`,`:M`; `:3`,`:N`; `:3`,`:P`] MFD_DIFFEO_COMPOSE) THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                          `IMAGE (e:real^3->A) D`] THEN
    ASM_REWRITE_TAC[GEOL_EUCLID_FACTS] THEN
    MATCH_MP_TAC MFD_DIFFEO_RESTRICT THEN
    MAP_EVERY EXISTS_TAC [`IMAGE (e':real^3->A) D'`; `D':real^3->bool`] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MFD_DIFFEO_SYM THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; o_THM] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(e:real^3->A) y IN IMAGE (e':real^3->A) D'` MP_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) THEN
    ASM_SIMP_TAC[];
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM SET_TAC[];
    MAP_EVERY X_GEN_TAC [`y:real^3`; `z:real^3`] THEN STRIP_TAC THEN ASM_SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The rescaled family of an evolving neck in coordinates.                   *)
(* p3e_nfam hs x t e s = R e^* G(t + s/R), R the scalar curvature at (x,t).  *)
(* Through the view pullbacks of pc_p2c_flloc with B = euclidean real^3,    *)
(* the identity chart and base time t' = t - len/R: a local Ricci flow from *)
(* t' on the neck domain (rfa_lfrom) and a smooth extension past t' of the  *)
(* family in space-time, for rescaled times up to slightly after t.         *)
(* ------------------------------------------------------------------------- *)

let p3e_nfam = new_definition
 `p3e_nfam (hs:(A)rfs_history) (x:A) (t:real) (e:real^3->A) =
    \s y. mfd_scalar (rfs_atlas_at hs t) (rfs_metric_at hs t) x %%
          rfs_pullback
            (rfs_atlas_at hs (t + s / mfd_scalar (rfs_atlas_at hs t) (rfs_metric_at hs t) x))
            e
            (rfs_metric_at hs (t + s / mfd_scalar (rfs_atlas_at hs t) (rfs_metric_at hs t) x))
            y`;;

(* The statement of P3H_PULLBACK_OPEN_UNIV (unit pc_p3_c17vol, which this    *)
(* unit does not load): the pullback from the flat real^N in its identity    *)
(* chart is the chart-free pullback rfs_pullback.                            *)

let P3E_PULLBACK_OPEN_UNIV = prove
 (`!atlas (e:real^N->A) (g:A->real^N^N) y.
     mfd_pullback_metric (open_set_atlas (:real^N)) atlas e g y = rfs_pullback atlas e g y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mfd_pullback_metric; rfs_pullback; GEOL_EUCLID_FACTS] THEN
  AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; o_THM] THEN SIMP_TAC[MFDM_CHART_INV_ID; IN_UNIV]);;

let P3E_METRIC_LOCAL_UNIV = prove
 (`!g:real^N->real^N^N.
     metric_local (open_set_atlas (:real^N)) ((:real^N),(\x. x)) g = g`,
  GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
  MATCH_MP_TAC RFB_OPEN_SET_METRIC_LOCAL THEN REWRITE_TAC[OPEN_UNIV; IN_UNIV]);;

let P3E_PB_NFAM = prove
 (`!(hs:(A)rfs_history) x t e len.
     &0 < mfd_scalar (rfs_atlas_at hs t) (rfs_metric_at hs t) x
     ==> (\s. metric_local (open_set_atlas (:real^3)) ((:real^3),(\x. x))
                (p2cv_pb (rfs_view hs)
                   (t - len / mfd_scalar (rfs_atlas_at hs t) (rfs_metric_at hs t) x)
                   (mfd_scalar (rfs_atlas_at hs t) (rfs_metric_at hs t) x)
                   (open_set_atlas (:real^3)) e s)) =
         (\r. p3e_nfam hs x t e (r - len))`,
  REPEAT GEN_TAC THEN
  ABBREV_TAC `R = mfd_scalar (rfs_atlas_at (hs:(A)rfs_history) t) (rfs_metric_at hs t) x` THEN
  DISCH_TAC THEN
  REWRITE_TAC[P3E_METRIC_LOCAL_UNIV; p2cv_pb; p3e_nfam; P3E_PULLBACK_OPEN_UNIV;
              P2AH_VIEW_PARTS; FUN_EQ_THM] THEN
  ASM_REWRITE_TAC[] THEN MAP_EVERY X_GEN_TAC [`r:real`; `y:real^3`] THEN
  SUBGOAL_THEN `t - len / R + r / R = t + (r - len) / R` ASSUME_TAC THENL
   [REAL_ARITH_TAC; ASM_REWRITE_TAC[]]);;

let P3E_EVNECK_COORD = prove
 (`!(hs:(A)rfs_history) b x t len (e:real^3->A).
     rfs_history_ok hs /\ rfs_evolving_neck (rfs_view hs) b x t len e
     ==> ?d. &0 < d /\
             rfa_lfrom (rfs_neck_dom b) (&0) (len + d) (\r. p3e_nfam hs x t e (r - len)) /\
             (?ep FF. &0 < ep /\
                smooth_map_on (interval(lift(--ep),lift((len + d) + ep)) PCROSS
                               rfs_neck_dom b) FF /\
                !r y. &0 <= r /\ r <= len + d /\ y IN rfs_neck_dom b
                      ==> FF(pastecart (lift r) y) =
                          (vectorize:real^3^3->real^(3,3)finite_prod)
                            (p3e_nfam hs x t e (r - len) y))`,
  REPEAT GEN_TAC THEN
  ABBREV_TAC `R = mfd_scalar (rfs_atlas_at (hs:(A)rfs_history) t) (rfs_metric_at hs t) x` THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `b:real`; `x:A`; `t:real`; `len:real`;
                 `e:real^3->A`] P3E_EVNECK_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `a = t - len / R` THEN
  POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  SUBGOAL_THEN `a < t` ASSUME_TAC THENL
   [EXPAND_TAC "a" THEN MATCH_MP_TAC(REAL_ARITH `&0 < d ==> t - d < t`) THEN
    MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `t:real`] P3E_HIST_SLAB_AFTER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "AFT"))) THEN
  (* persistence up to t + d0 *)
  SUBGOAL_THEN `rfs_persists (rfs_view (hs:(A)rfs_history)) (IMAGE (e:real^3->A) (rfs_neck_dom b))
                             a (t + d0)` ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_persists (rfs_view (hs:(A)rfs_history)) (IMAGE (e:real^3->A)
                   (rfs_neck_dom b)) a t` THEN
    REWRITE_TAC[P2AH_PERSISTS] THEN DISCH_THEN(LABEL_TAC "PT") THEN
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN ASM_CASES_TAC `s <= t` THENL
     [USE_THEN "PT" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      USE_THEN "AFT" (MP_TAC o SPEC `s:real`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "PT" (MP_TAC o SPEC `t:real`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]]];
    ALL_TAC] THEN
  (* the view pullback hypothesis *)
  SUBGOAL_THEN `p2cv_one (rfs_view (hs:(A)rfs_history))
                  (euclidean,open_set_atlas (:real^3)) (rfs_neck_dom b) (e:real^3->A) a R`
  ASSUME_TAC THENL
   [REWRITE_TAC[p2cv_one; GEOL_EUCLID_FACTS; P2AH_VIEW_PARTS] THEN
    ASM_SIMP_TAC[P3E_HIST_REGULAR; P2CY_HIST_FROM_SMOOTH] THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[GSYM OPEN_IN; rfs_neck_dom; OPEN_ANNULUS];
      ASM SET_TAC[];
      MP_TAC(ISPECL [`hs:(A)rfs_history`; `b:real`; `x:A`; `t:real`; `len:real`;
                     `e:real^3->A`; `a:real`] P3E_EVNECK_SLICE_PARAM) THEN
      ASM_REWRITE_TAC[REAL_LE_REFL] THEN ANTS_TAC THENL
       [ASM_REAL_ARITH_TAC; REWRITE_TAC[mfd_param] THEN SIMP_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `a + &0 / R = a /\ a + (len + R * d0) / R = t + d0` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "a" THEN SUBGOAL_THEN `~(R = &0)` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  EXISTS_TAC `R * d0` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`rfs_view (hs:(A)rfs_history)`; `euclidean:(real^3)topology`;
                   `open_set_atlas (:real^3)`; `rfs_neck_dom b`; `e:real^3->A`; `a:real`;
                   `R:real`; `len + R * d0`; `((:real^3),(\x:real^3. x))`] P2CV_LFROM) THEN
    ASM_REWRITE_TAC[RFB_OPEN_SET_ATLAS_CASES; INTER_UNIV; IMAGE_ID; FST; SND] THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC REAL_LT_ADD THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_MUL THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`hs:(A)rfs_history`; `x:A`; `t:real`; `e:real^3->A`; `len:real`]
                  P3E_PB_NFAM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`rfs_view (hs:(A)rfs_history)`; `euclidean:(real^3)topology`;
                 `open_set_atlas (:real^3)`; `rfs_neck_dom b`; `e:real^3->A`; `a:real`;
                 `R:real`; `&0`; `len + R * d0`; `&0`; `len + R * d0`;
                 `((:real^3),(\x:real^3. x))`] P2CV_EXT) THEN
  ASM_REWRITE_TAC[RFB_OPEN_SET_ATLAS_CASES; INTER_UNIV; IMAGE_ID; REAL_LE_REFL; FST; SND] THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 < x ==> &0 <= x /\ &0 < x`) THEN
    MATCH_MP_TAC REAL_LT_ADD THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_MUL THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `ep:real` (X_CHOOSE_THEN `FF:real^(1,3)finite_sum->real^(3,3)finite_prod`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`ep:real`; `FF:real^(1,3)finite_sum->real^(3,3)finite_prod`] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_SUB_LZERO]) THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`r:real`; `y:real^3`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`r:real`; `y:real^3`] o check (fun th ->
    can (find_term (fun t -> t = `FF:real^(1,3)finite_sum->real^(3,3)finite_prod`)) (concl th) &&
    is_forall (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `x:A`; `t:real`; `e:real^3->A`; `len:real`]
                P3E_PB_NFAM) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o C AP_THM `r:real`) THEN REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Properties of the coordinate family p3e_nfam: Riemannian slices, metric   *)
(* fields, the scalar curvature in a slice where e is a parametrization, the *)
(* gluing identity through a transition map, and the uniform jet continuity  *)
(* at the junction from a smooth space-time extension.                       *)
(* ------------------------------------------------------------------------- *)

let P3E_SLICE_RIEM = prove
 (`!(hs:(A)rfs_history) s W.
     rfs_history_ok hs /\ open_in (rfs_top_at hs s) W /\ ~(W = {})
     ==> smooth_manifold_atlas (rfs_top_at hs s) (rfs_atlas_at hs s) /\
         riemannian_metric (rfs_atlas_at hs s) (rfs_metric_at hs s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP P3E_HIST_REGULAR) THEN
  REWRITE_TAC[p2c_regular_view; P2AH_VIEW_PARTS] THEN
  DISCH_THEN(MP_TAC o SPEC `s:real` o CONJUNCT1) THEN
  ANTS_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o MATCH_MP OPEN_IN_SUBSET) THEN ASM SET_TAC[];
    SIMP_TAC[]]);;

let P3E_NFAM_FIELD = prove
 (`!(hs:(A)rfs_history) x t (e:real^3->A) D s.
     smooth_manifold_atlas
       (rfs_top_at hs (t + s / mfd_scalar (rfs_atlas_at hs t) (rfs_metric_at hs t) x))
       (rfs_atlas_at hs (t + s / mfd_scalar (rfs_atlas_at hs t) (rfs_metric_at hs t) x)) /\
     riemannian_metric
       (rfs_atlas_at hs (t + s / mfd_scalar (rfs_atlas_at hs t) (rfs_metric_at hs t) x))
       (rfs_metric_at hs (t + s / mfd_scalar (rfs_atlas_at hs t) (rfs_metric_at hs t) x)) /\
     mfd_param
       (rfs_top_at hs (t + s / mfd_scalar (rfs_atlas_at hs t) (rfs_metric_at hs t) x))
       (rfs_atlas_at hs (t + s / mfd_scalar (rfs_atlas_at hs t) (rfs_metric_at hs t) x)) D e /\
     &0 < mfd_scalar (rfs_atlas_at hs t) (rfs_metric_at hs t) x
     ==> metric_field D (p3e_nfam hs x t e s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[p3e_nfam] THEN
  MATCH_MP_TAC RFB_METRIC_FIELD_CMUL THEN ASM_REWRITE_TAC[ETA_AX] THEN
  MATCH_MP_TAC APX_RFS_PULLBACK_FIELD THEN ASM_MESON_TAC[]);;

let P3E_NFAM_SCALAR = prove
 (`!(hs:(A)rfs_history) x t (e:real^3->A) D s y.
     smooth_manifold_atlas
       (rfs_top_at hs (t + s / mfd_scalar (rfs_atlas_at hs t) (rfs_metric_at hs t) x))
       (rfs_atlas_at hs (t + s / mfd_scalar (rfs_atlas_at hs t) (rfs_metric_at hs t) x)) /\
     riemannian_metric
       (rfs_atlas_at hs (t + s / mfd_scalar (rfs_atlas_at hs t) (rfs_metric_at hs t) x))
       (rfs_metric_at hs (t + s / mfd_scalar (rfs_atlas_at hs t) (rfs_metric_at hs t) x)) /\
     mfd_param
       (rfs_top_at hs (t + s / mfd_scalar (rfs_atlas_at hs t) (rfs_metric_at hs t) x))
       (rfs_atlas_at hs (t + s / mfd_scalar (rfs_atlas_at hs t) (rfs_metric_at hs t) x)) D e /\
     y IN D /\ &0 < mfd_scalar (rfs_atlas_at hs t) (rfs_metric_at hs t) x
     ==> lscalar (p3e_nfam hs x t e s) y =
         mfd_scalar (rfs_atlas_at hs (t + s / mfd_scalar (rfs_atlas_at hs t) (rfs_metric_at hs t) x))
                    (rfs_metric_at hs (t + s / mfd_scalar (rfs_atlas_at hs t) (rfs_metric_at hs t) x))
                    (e y) /
         mfd_scalar (rfs_atlas_at hs t) (rfs_metric_at hs t) x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[p3e_nfam] THEN
  MATCH_MP_TAC P2B9_PARAM_LSCALAR_SCALED THEN
  EXISTS_TAC `rfs_top_at (hs:(A)rfs_history)
                (t + s / mfd_scalar (rfs_atlas_at hs t) (rfs_metric_at hs t) x)` THEN
  EXISTS_TAC `D:real^3->bool` THEN ASM_REWRITE_TAC[]);;

let P3E_NFAM_GLUE = prove
 (`!(hs:(A)rfs_history) x t t0 (e:real^3->A) (e':real^3->A) D D2 psi psi' sig y.
     &0 < mfd_scalar (rfs_atlas_at hs t) (rfs_metric_at hs t) x /\
     &0 < mfd_scalar
            (rfs_atlas_at hs (t - t0 / mfd_scalar (rfs_atlas_at hs t) (rfs_metric_at hs t) x))
            (rfs_metric_at hs (t - t0 / mfd_scalar (rfs_atlas_at hs t) (rfs_metric_at hs t) x)) x /\
     smooth_manifold_atlas
       (rfs_top_at hs (t - t0 / mfd_scalar (rfs_atlas_at hs t) (rfs_metric_at hs t) x +
          sig / mfd_scalar
                  (rfs_atlas_at hs (t - t0 / mfd_scalar (rfs_atlas_at hs t) (rfs_metric_at hs t) x))
                  (rfs_metric_at hs (t - t0 / mfd_scalar (rfs_atlas_at hs t) (rfs_metric_at hs t) x)) x))
       (rfs_atlas_at hs (t - t0 / mfd_scalar (rfs_atlas_at hs t) (rfs_metric_at hs t) x +
          sig / mfd_scalar
                  (rfs_atlas_at hs (t - t0 / mfd_scalar (rfs_atlas_at hs t) (rfs_metric_at hs t) x))
                  (rfs_metric_at hs (t - t0 / mfd_scalar (rfs_atlas_at hs t) (rfs_metric_at hs t) x)) x)) /\
     mfd_param
       (rfs_top_at hs (t - t0 / mfd_scalar (rfs_atlas_at hs t) (rfs_metric_at hs t) x +
          sig / mfd_scalar
                  (rfs_atlas_at hs (t - t0 / mfd_scalar (rfs_atlas_at hs t) (rfs_metric_at hs t) x))
                  (rfs_metric_at hs (t - t0 / mfd_scalar (rfs_atlas_at hs t) (rfs_metric_at hs t) x)) x))
       (rfs_atlas_at hs (t - t0 / mfd_scalar (rfs_atlas_at hs t) (rfs_metric_at hs t) x +
          sig / mfd_scalar
                  (rfs_atlas_at hs (t - t0 / mfd_scalar (rfs_atlas_at hs t) (rfs_metric_at hs t) x))
                  (rfs_metric_at hs (t - t0 / mfd_scalar (rfs_atlas_at hs t) (rfs_metric_at hs t) x)) x))
       D2 e' /\
     diffeomorphism_on D (IMAGE psi D) psi psi' /\ IMAGE psi D SUBSET D2 /\
     (!y. y IN D ==> e'(psi y) = e y) /\ y IN D
     ==> p3e_nfam hs x t e
           (sig / (mfd_scalar
                     (rfs_atlas_at hs (t - t0 / mfd_scalar (rfs_atlas_at hs t) (rfs_metric_at hs t) x))
                     (rfs_metric_at hs (t - t0 / mfd_scalar (rfs_atlas_at hs t) (rfs_metric_at hs t) x)) x /
                   mfd_scalar (rfs_atlas_at hs t) (rfs_metric_at hs t) x) - t0) y =
         inv(mfd_scalar
               (rfs_atlas_at hs (t - t0 / mfd_scalar (rfs_atlas_at hs t) (rfs_metric_at hs t) x))
               (rfs_metric_at hs (t - t0 / mfd_scalar (rfs_atlas_at hs t) (rfs_metric_at hs t) x)) x /
             mfd_scalar (rfs_atlas_at hs t) (rfs_metric_at hs t) x) %%
         mpullback psi
           (p3e_nfam hs x (t - t0 / mfd_scalar (rfs_atlas_at hs t) (rfs_metric_at hs t) x) e' sig) y`,
  REPEAT GEN_TAC THEN
  ABBREV_TAC `R = mfd_scalar (rfs_atlas_at (hs:(A)rfs_history) t) (rfs_metric_at hs t) x` THEN
  ABBREV_TAC `t' = t - t0 / R` THEN
  ABBREV_TAC `R' = mfd_scalar (rfs_atlas_at (hs:(A)rfs_history) t') (rfs_metric_at hs t') x` THEN
  ABBREV_TAC `tau = t' + sig / R'` THEN
  STRIP_TAC THEN REWRITE_TAC[p3e_nfam] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `t + (sig / (R' / R) - t0) / R = tau` SUBST1_TAC THENL
   [MAP_EVERY EXPAND_TAC ["tau"; "t'"] THEN
    SUBGOAL_THEN `~(R = &0) /\ ~(R' = &0)` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[P3E_MPULLBACK_CMUL; MATRIX_CMUL_ASSOC] THEN
  SUBGOAL_THEN `inv(R' / R) * R' = R` SUBST1_TAC THENL
   [SUBGOAL_THEN `~(R = &0) /\ ~(R' = &0)` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  AP_TERM_TAC THEN REWRITE_TAC[ETA_AX] THEN
  MP_TAC(ISPECL [`rfs_top_at (hs:(A)rfs_history) tau`; `rfs_atlas_at (hs:(A)rfs_history) tau`;
                 `rfs_metric_at (hs:(A)rfs_history) tau`; `IMAGE (psi:real^3->real^3) D`;
                 `e':real^3->A`; `D:real^3->bool`; `psi:real^3->real^3`;
                 `psi':real^3->real^3`; `y:real^3`] APX_RFS_PULLBACK_PRECOMP) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MFD_PARAM_RESTRICT THEN
    EXISTS_TAC `D2:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[diffeomorphism_on];
    DISCH_THEN(SUBST1_TAC o SYM)] THEN
  MATCH_MP_TAC P2CV_RFS_PULLBACK_LOCAL THEN EXISTS_TAC `D:real^3->bool` THEN
  ASM_REWRITE_TAC[o_THM] THEN ASM_MESON_TAC[diffeomorphism_on]);;

let P3E_NFAM_JETS = prove
 (`!(P:real->real^3->real^3^3) FF D t0 dd ep.
     open D /\ &0 < t0 /\ &0 < dd /\ &0 < ep /\
     smooth_map_on (interval(lift(--ep),lift((t0 + dd) + ep)) PCROSS D) FF /\
     (!r y. &0 <= r /\ r <= t0 + dd /\ y IN D
            ==> FF(pastecart (lift r) y) =
                (vectorize:real^3^3->real^(3,3)finite_prod) (P (r - t0) y))
     ==> !K m e. compact K /\ K SUBSET D /\ &0 < e
                 ==> ?dl. &0 < dl /\
                          !s y l. --t0 < s /\ s < --t0 + dl /\ y IN K /\
                                  l IN pde_index_lists m (:3)
                                  ==> norm(iterated_partial l
                                             ((vectorize:real^3^3->real^(3,3)finite_prod) o
                                              P s) y -
                                           iterated_partial l (vectorize o P (--t0)) y) < e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MAP_EVERY X_GEN_TAC [`K:real^3->bool`; `m:num`; `e:real`] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`FF:real^(1,3)finite_sum->real^(3,3)finite_prod`;
                 `interval(lift(--ep),lift((t0 + dd) + ep)) PCROSS (D:real^3->bool)`;
                 `&0`; `K:real^3->bool`; `m:num`; `e:real`] P3E_SLICE_JET_UCONT) THEN
  ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP] THEN
  ANTS_TAC THENL
   [X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN REPEAT CONJ_TAC THEN
    TRY(ASM_REAL_ARITH_TAC THEN NO_TAC) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `dl:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "U"))) THEN
  EXISTS_TAC `min dl (t0 + dd)` THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_LT_MIN] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`s:real`; `y:real^3`; `l:(num)list`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(y:real^3) IN D` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!r. &0 <= r /\ r <= t0 + dd
        ==> iterated_partial l ((vectorize:real^3^3->real^(3,3)finite_prod) o
                                (P:real->real^3->real^3^3) (r - t0)) y =
            iterated_partial l (\y. (FF:real^(1,3)finite_sum->real^(3,3)finite_prod)
                                      (pastecart (lift r) y)) y`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC TEXT_ITERATED_PARTIAL_LOCAL_AT THEN
    EXISTS_TAC `D:real^3->bool` THEN ASM_SIMP_TAC[o_THM];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `s + t0`) THEN
  FIRST_ASSUM(MP_TAC o SPEC `&0`) THEN
  REWRITE_TAC[REAL_ARITH `(s + t0) - t0 = s`; REAL_SUB_LZERO] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  USE_THEN "U" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The gluing data of a history configuration.  From a valid                 *)
(* history, an evolving beta eps-neck e at (x,t) of length t0 < 1, a strong  *)
(* beta eps/2-neck e' at (x,t'), t' = t - t0/R, and the image containment,  *)
(* the coordinate families P = p3e_nfam hs x t e and H = p3e_nfam hs x t' e' *)
(* with psi = e'^-1 o e and r = R'/R are gluing data (p3e_gdata).           *)
(* ------------------------------------------------------------------------- *)

let P3E_VSCALAR_VIEW = prove
 (`!(hs:(A)rfs_history) t x.
     rfs_vscalar (rfs_view hs) t x = mfd_scalar (rfs_atlas_at hs t) (rfs_metric_at hs t) x`,
  REWRITE_TAC[rfs_view; rfs_vscalar]);;

let P3E_TIME_BETWEEN = prove
 (`!R t a s b. &0 < R /\ a <= s /\ s <= b
               ==> t + a / R <= t + s / R /\ t + s / R <= t + b / R`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[REAL_LE_LADD] THEN
  ASM_SIMP_TAC[REAL_LE_DIV2_EQ]);;

let P3E_REAL_CONT_SHIFT = prove
 (`!(f:real->real) a b c.
     (\u. lift(f(drop u - c))) continuous_on interval[lift(a + c),lift(b + c)]
     ==> f real_continuous_on real_interval[a,b]`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[REAL_CONTINUOUS_ON; IMAGE_LIFT_REAL_INTERVAL] THEN
  SUBGOAL_THEN `(lift o f o drop) = (\u. lift(f(drop u - c))) o (\v:real^1. v + lift c)`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; DROP_ADD; LIFT_DROP] THEN
    REWRITE_TAC[REAL_ARITH `(x + c) - c = x`];
    ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_ADD THEN REWRITE_TAC[CONTINUOUS_ON_ID; CONTINUOUS_ON_CONST];
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] CONTINUOUS_ON_SUBSET)) THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTERVAL_1; DROP_ADD; LIFT_DROP] THEN
    REAL_ARITH_TAC]);;

let P3E_GDATA_FROM_HISTORY = prove
 (`!(hs:(A)rfs_history) eps beta x t t0 (e:real^3->A) e' R t' R'.
     rfs_history_ok hs /\ &0 < eps /\ eps < &1 /\ &0 < beta /\ beta < &1 / &2 /\ t0 < &1 /\
     mfd_scalar (rfs_atlas_at hs t) (rfs_metric_at hs t) x = R /\ t - t0 / R = t' /\
     mfd_scalar (rfs_atlas_at hs t') (rfs_metric_at hs t') x = R' /\
     rfs_evolving_neck (rfs_view hs) (beta * eps) x t t0 e /\
     rfs_strong_neck (rfs_view hs) (beta * eps / &2) x t' e' /\
     IMAGE e (rfs_neck_dom (beta * eps)) SUBSET IMAGE e' (rfs_neck_dom (beta * eps / &2))
     ==> ?psi psi' yx.
           p3e_gdata eps beta t0 (R' / R) (p3e_nfam hs x t e) (p3e_nfam hs x t' e')
                     psi psi' yx /\
           (!y. y IN rfs_neck_dom (beta * eps) ==> e'(psi y) = e y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[rfs_strong_neck]) THEN
  ABBREV_TAC `D = rfs_neck_dom (beta * eps)` THEN
  ABBREV_TAC `D' = rfs_neck_dom (beta * eps / &2)` THEN
  POP_ASSUM(fun th -> POP_ASSUM(fun th' ->
    RULE_ASSUM_TAC(REWRITE_RULE[th; th']) THEN ASSUME_TAC th' THEN ASSUME_TAC th)) THEN
  (* the two necks *)
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `beta * eps`; `x:A`; `t:real`; `t0:real`;
                 `e:real^3->A`] P3E_EVNECK_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `beta * eps / &2`; `x:A`; `t':real`; `&1`;
                 `e':real^3->A`] P3E_EVNECK_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!s. t' <= s /\ s <= t
        ==> smooth_manifold_atlas (rfs_top_at (hs:(A)rfs_history) s) (rfs_atlas_at hs s) /\
            open_in (rfs_top_at hs s) (IMAGE (e:real^3->A) D) /\
            mfd_param (rfs_top_at hs s) (rfs_atlas_at hs s) D e`
  (LABEL_TAC "SLE") THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN EXPAND_TAC "D" THEN
    MATCH_MP_TAC P3E_EVNECK_SLICE_PARAM THEN
    MAP_EVERY EXISTS_TAC [`x:A`; `t:real`; `t0:real`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. t' - &1 / R' <= s /\ s <= t'
        ==> smooth_manifold_atlas (rfs_top_at (hs:(A)rfs_history) s) (rfs_atlas_at hs s) /\
            open_in (rfs_top_at hs s) (IMAGE (e':real^3->A) D') /\
            mfd_param (rfs_top_at hs s) (rfs_atlas_at hs s) D' e'`
  (LABEL_TAC "SLE2") THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN EXPAND_TAC "D'" THEN
    MATCH_MP_TAC P3E_EVNECK_SLICE_PARAM THEN
    MAP_EVERY EXISTS_TAC [`x:A`; `t':real`; `&1`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `t' < t` ASSUME_TAC THENL
   [EXPAND_TAC "t'" THEN MATCH_MP_TAC(REAL_ARITH `&0 < d ==> t - d < t`) THEN
    MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the transition map in the slice t' *)
  USE_THEN "SLE" (MP_TAC o SPEC `t':real`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  USE_THEN "SLE2" (MP_TAC o SPEC `t':real`) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 < d ==> t - d <= t`) THEN MATCH_MP_TAC REAL_LT_DIV THEN
    ASM_REWRITE_TAC[REAL_LT_01];
    STRIP_TAC] THEN
  MP_TAC(ISPECL [`rfs_top_at (hs:(A)rfs_history) t'`; `rfs_atlas_at (hs:(A)rfs_history) t'`;
                 `D:real^3->bool`; `D':real^3->bool`; `e:real^3->A`; `e':real^3->A`]
                P3E_TRANSITION_MAP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `psi:real^3->real^3` (X_CHOOSE_THEN `psi':real^3->real^3`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (LABEL_TAC "EPS") (LABEL_TAC "UNQ")))))) THEN
  (* the centre points *)
  UNDISCH_TAC `(x:A) IN IMAGE (e:real^3->A) (sphere(vec 0,&1))` THEN
  REWRITE_TAC[IN_IMAGE; IN_SPHERE_0] THEN
  DISCH_THEN(X_CHOOSE_THEN `yx:real^3` (CONJUNCTS_THEN2 (ASSUME_TAC o SYM) ASSUME_TAC)) THEN
  UNDISCH_TAC `(x:A) IN IMAGE (e':real^3->A) (sphere(vec 0,&1))` THEN
  REWRITE_TAC[IN_IMAGE; IN_SPHERE_0] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:real^3` (CONJUNCTS_THEN2 (ASSUME_TAC o SYM) ASSUME_TAC)) THEN
  SUBGOAL_THEN `(yx:real^3) IN D /\ (z:real^3) IN D'` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["D"; "D'"] THEN
    MP_TAC(SPEC `beta * eps` P3E_UNIT_SPHERE_NECK_DOM) THEN
    MP_TAC(SPEC `beta * eps / &2` P3E_UNIT_SPHERE_NECK_DOM) THEN
    ASM_REWRITE_TAC[SUBSET; IN_SPHERE_0] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(psi:real^3->real^3) yx = z` ASSUME_TAC THENL
   [USE_THEN "UNQ" MATCH_MP_TAC THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  (* the coordinate flow of P *)
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `beta * eps`; `x:A`; `t:real`; `t0:real`;
                 `e:real^3->A`] P3E_EVNECK_COORD) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `dd:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "LF") (X_CHOOSE_THEN `ep:real`
      (X_CHOOSE_THEN `FF:real^(1,3)finite_sum->real^(3,3)finite_prod` STRIP_ASSUME_TAC))))) THEN
  MAP_EVERY EXISTS_TAC [`psi:real^3->real^3`; `psi':real^3->real^3`; `yx:real^3`] THEN
  ASM_REWRITE_TAC[] THEN
  (* the clauses of p3e_gdata *)
  SUBGOAL_THEN `&0 < R' / R` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!tau. t' <= tau /\ tau <= t
          ==> riemannian_metric (rfs_atlas_at (hs:(A)rfs_history) tau) (rfs_metric_at hs tau)`
  (LABEL_TAC "RM") THENL
   [X_GEN_TAC `tau:real` THEN STRIP_TAC THEN
    USE_THEN "SLE" (MP_TAC o SPEC `tau:real`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    MP_TAC(ISPECL [`hs:(A)rfs_history`; `tau:real`; `IMAGE (e:real^3->A) D`]
                  P3E_SLICE_RIEM) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM SET_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!tau. t' - &1 / R' <= tau /\ tau <= t'
          ==> riemannian_metric (rfs_atlas_at (hs:(A)rfs_history) tau) (rfs_metric_at hs tau)`
  (LABEL_TAC "RM2") THENL
   [X_GEN_TAC `tau:real` THEN STRIP_TAC THEN
    USE_THEN "SLE2" (MP_TAC o SPEC `tau:real`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    MP_TAC(ISPECL [`hs:(A)rfs_history`; `tau:real`; `IMAGE (e':real^3->A) D'`]
                  P3E_SLICE_RIEM) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM SET_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  (* times of the two families *)
  SUBGOAL_THEN `!s. --t0 <= s /\ s <= &0 ==> t' <= t + s / R /\ t + s / R <= t`
  (LABEL_TAC "TP") THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`R:real`; `t:real`; `--t0`; `s:real`; `&0`] P3E_TIME_BETWEEN) THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "t'" THEN
    REWRITE_TAC[real_div; REAL_MUL_LZERO; REAL_MUL_LNEG] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!s. --(&1) <= s /\ s <= &0 ==> t' - &1 / R' <= t' + s / R' /\ t' + s / R' <= t'`
  (LABEL_TAC "TH") THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`R':real`; `t':real`; `--(&1)`; `s:real`; `&0`] P3E_TIME_BETWEEN) THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[real_div; REAL_MUL_LZERO; REAL_MUL_LNEG] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* metric fields *)
  SUBGOAL_THEN
   `!s. --t0 <= s /\ s <= &0 ==> metric_field D (p3e_nfam (hs:(A)rfs_history) x t e s)`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    USE_THEN "TP" (MP_TAC o SPEC `s:real`) THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    USE_THEN "SLE" (MP_TAC o SPEC `t + s / R`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    MATCH_MP_TAC P3E_NFAM_FIELD THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "RM" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. --(&1) < s /\ s <= &0 ==> metric_field D' (p3e_nfam (hs:(A)rfs_history) x t' e' s)`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    USE_THEN "TH" (MP_TAC o SPEC `s:real`) THEN ANTS_TAC THENL
     [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    USE_THEN "SLE2" (MP_TAC o SPEC `t' + s / R'`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    MATCH_MP_TAC P3E_NFAM_FIELD THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "RM2" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the closeness of the two necks *)
  SUBGOAL_THEN
   `?d. d < (beta * eps) pow 2 /\
        !s y. --t0 < s /\ s <= &0 /\ y IN D
              ==> lck_dist2 (rfs_kreg (beta * eps)) (cylinder_flow s)
                            (p3e_nfam (hs:(A)rfs_history) x t e s) y <= d`
  ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_close_fam (rfs_kreg (beta * eps)) (beta * eps) {s | --t0 < s /\ s <= &0} D
                   cylinder_flow
                   (\s y. R %% rfs_pullback (rfs_atlas_at (hs:(A)rfs_history) (t + s / R)) e
                                 (rfs_metric_at hs (t + s / R)) y)` THEN
    REWRITE_TAC[rfs_close_fam; IN_ELIM_THM; GSYM CONJ_ASSOC; p3e_nfam] THEN
    ASM_REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?d. d < (beta * eps / &2) pow 2 /\
        !s y. --(&1) < s /\ s <= &0 /\ y IN D'
              ==> lck_dist2 (rfs_kreg (beta * eps / &2)) (cylinder_flow s)
                            (p3e_nfam (hs:(A)rfs_history) x t' e' s) y <= d`
  ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_close_fam (rfs_kreg (beta * eps / &2)) (beta * eps / &2)
                   {s | --(&1) < s /\ s <= &0} D' cylinder_flow
                   (\s y. R' %% rfs_pullback (rfs_atlas_at (hs:(A)rfs_history) (t' + s / R')) e'
                                  (rfs_metric_at hs (t' + s / R')) y)` THEN
    REWRITE_TAC[rfs_close_fam; IN_ELIM_THM; GSYM CONJ_ASSOC; p3e_nfam] THEN
    ASM_REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
  (* the gluing identity *)
  SUBGOAL_THEN
   `!s y. --(&1) < s /\ s <= &0 /\ y IN D
          ==> p3e_nfam (hs:(A)rfs_history) x t e (s / (R' / R) - t0) y =
              inv(R' / R) %% mpullback psi (p3e_nfam hs x t' e' s) y`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`s:real`; `y:real^3`] THEN STRIP_TAC THEN
    USE_THEN "TH" (MP_TAC o SPEC `s:real`) THEN ANTS_TAC THENL
     [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    USE_THEN "SLE2" (MP_TAC o SPEC `t' + s / R'`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    MP_TAC(ISPECL [`hs:(A)rfs_history`; `x:A`; `t:real`; `t0:real`; `e:real^3->A`;
                   `e':real^3->A`; `D:real^3->bool`; `D':real^3->bool`;
                   `psi:real^3->real^3`; `psi':real^3->real^3`; `s:real`; `y:real^3`]
                  P3E_NFAM_GLUE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the jets at the junction *)
  SUBGOAL_THEN
   `!K m ee. compact K /\ K SUBSET D /\ &0 < ee
             ==> ?dl. &0 < dl /\
                      !s y l. --t0 < s /\ s < --t0 + dl /\ y IN K /\
                              l IN pde_index_lists m (:3)
                              ==> norm(iterated_partial l
                                         ((vectorize:real^3^3->real^(3,3)finite_prod) o
                                          p3e_nfam (hs:(A)rfs_history) x t e s) y -
                                       iterated_partial l
                                         (vectorize o p3e_nfam hs x t e (--t0)) y) < ee`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P3E_NFAM_JETS THEN
    MAP_EVERY EXISTS_TAC [`FF:real^(1,3)finite_sum->real^(3,3)finite_prod`; `dd:real`;
                          `ep:real`] THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "D" THEN REWRITE_TAC[rfs_neck_dom; OPEN_ANNULUS];
    ALL_TAC] THEN
  (* the scalar curvature at the centre *)
  SUBGOAL_THEN `lscalar (p3e_nfam (hs:(A)rfs_history) x t e (&0)) yx = &1 /\
                lscalar (p3e_nfam hs x t e (--t0)) yx = R' / R`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "TP" (MP_TAC o SPEC `&0`) THEN USE_THEN "TP" (MP_TAC o SPEC `--t0`) THEN
    REWRITE_TAC[REAL_LE_REFL; REAL_NEG_LE0] THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    REPEAT STRIP_TAC THENL
     [MP_TAC(ISPECL [`hs:(A)rfs_history`; `x:A`; `t:real`; `e:real^3->A`; `D:real^3->bool`;
                     `&0`; `yx:real^3`] P3E_NFAM_SCALAR);
      MP_TAC(ISPECL [`hs:(A)rfs_history`; `x:A`; `t:real`; `e:real^3->A`; `D:real^3->bool`;
                     `--t0`; `yx:real^3`] P3E_NFAM_SCALAR)] THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[REAL_ARITH `t + --t0 / R = t - t0 / R`; real_div; REAL_MUL_LZERO;
                REAL_ADD_RID] THEN
    ASM_REWRITE_TAC[GSYM real_div] THEN
    (ANTS_TAC THENL
      [USE_THEN "SLE" (MP_TAC o SPEC `t:real`) THEN
       USE_THEN "SLE" (MP_TAC o SPEC `t':real`) THEN
       USE_THEN "RM" (MP_TAC o SPEC `t:real`) THEN
       USE_THEN "RM" (MP_TAC o SPEC `t':real`) THEN
       ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LE_REFL];
       DISCH_THEN SUBST1_TAC]) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~(R = &0)` MP_TAC THENL [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  (* the coordinate Ricci flow of P *)
  SUBGOAL_THEN `lricci_flow D (--t0) dd (p3e_nfam (hs:(A)rfs_history) x t e)` ASSUME_TAC THENL
   [USE_THEN "LF" (MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [rfa_lfrom]) THEN
    DISCH_THEN(MP_TAC o SPEC `--t0` o MATCH_MP P2CH_LRICCI_FLOW_SHIFT) THEN
    REWRITE_TAC[REAL_ARITH `&0 + --t0 = --t0`; REAL_ARITH `(t0 + dd) + --t0 = dd`;
                REAL_ARITH `(s - --t0) - t0 = s`; ETA_AX];
    ALL_TAC] THEN
  (* continuity and evolution of the scalar curvature at the centre *)
  SUBGOAL_THEN
   `(\s. lscalar (p3e_nfam (hs:(A)rfs_history) x t e s) yx) real_continuous_on
    real_interval[--t0,&0]`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P3E_REAL_CONT_SHIFT THEN EXISTS_TAC `t0:real` THEN
    REWRITE_TAC[REAL_ARITH `--t0 + t0 = &0`; REAL_ADD_LID] THEN
    MP_TAC(ISPECL [`lscalar:(real^3->real^3^3)->real^3->real`; `D:real^3->bool`; `&0`;
                   `t0 + dd`; `\r. p3e_nfam (hs:(A)rfs_history) x t e (r - t0)`; `yx:real^3`;
                   `t0:real`] RFA_LFROM_SLICE_CONT) THEN
    ASM_REWRITE_TAC[LRG_LSMOOTH_LSCALAR; LSCALAR_LOCAL] THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. --t0 < s /\ s < &0
        ==> ((\s. lscalar (p3e_nfam (hs:(A)rfs_history) x t e s) yx) has_real_derivative
             (llap (p3e_nfam hs x t e s) (lscalar (p3e_nfam hs x t e s)) yx +
              &2 * ltnorm2 2 (p3e_nfam hs x t e s) (lric2 (p3e_nfam hs x t e s)) yx))
            (atreal s)`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN MATCH_MP_TAC LSCALAR_EVOLUTION THEN
    MAP_EVERY EXISTS_TAC [`D:real^3->bool`; `--t0`; `dd:real`] THEN
    ASM_REWRITE_TAC[ETA_AX] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[p3e_gdata]);;

(* ------------------------------------------------------------------------- *)
(* MT Prop 15.2 for valid histories.  For t0 < 1 the gluing data above and   *)
(* the abstract core P3E_GLUE_CORE give r (1 - t0) < 1 (so the later neck    *)
(* reaches back beyond t - 1/R) and the closeness on                         *)
(* (-1,0] x rfs_neck_dom eps; for t0 >= 1 the evolving neck alone suffices.  *)
(* The strong eps-neck at (x,t) is e itself on rfs_neck_dom eps.             *)
(* ------------------------------------------------------------------------- *)

let P3E_LCK_SHRINK = prove
 (`!b eps s (G:real^3->real^3^3) y d.
     &0 < b /\ b <= eps /\ s < &1 /\ metric_field (rfs_neck_dom b) G /\
     y IN rfs_neck_dom eps /\ lck_dist2 (rfs_kreg b) (cylinder_flow s) G y <= d
     ==> lck_dist2 (rfs_kreg eps) (cylinder_flow s) G y <= d`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `lck_dist2 (rfs_kreg b) (cylinder_flow s) (G:real^3->real^3^3) y` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LCK_DIST_MONO THEN EXISTS_TAC `rfs_neck_dom b` THEN
  ASM_SIMP_TAC[P3E_CYL_METRIC_NECK; APX_KREG_MONO] THEN
  MP_TAC(SPECL [`b:real`; `eps:real`] APX_NECK_DOM_MONO) THEN ASM_REWRITE_TAC[] THEN
  ASM SET_TAC[]);;

let P3E_PROP_15_2 = prove
 (`!u:A->bool. P3_PROP_15_2_STATEMENT u`,
  GEN_TAC THEN REWRITE_TAC[P3_PROP_15_2_STATEMENT] THEN
  X_GEN_TAC `eps:real` THEN STRIP_TAC THEN
  MP_TAC(SPEC `eps:real` P3E_GLUE_CORE) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `beta:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "CORE")))) THEN
  EXISTS_TAC `beta:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`hs:(A)rfs_history`; `x:A`; `t:real`; `t0:real`; `e:real^3->A`;
                       `e':real^3->A`] THEN
  REWRITE_TAC[P3E_VSCALAR_VIEW] THEN
  ABBREV_TAC `R = mfd_scalar (rfs_atlas_at (hs:(A)rfs_history) t) (rfs_metric_at hs t) x` THEN
  ABBREV_TAC `t' = t - t0 / R` THEN
  ABBREV_TAC `R' = mfd_scalar (rfs_atlas_at (hs:(A)rfs_history) t') (rfs_metric_at hs t') x` THEN
  STRIP_TAC THEN EXISTS_TAC `e:real^3->A` THEN
  SUBGOAL_THEN `&0 < beta * eps /\ beta * eps <= eps /\ &0 < beta * eps / &2`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(SPECL [`eps:real`; `beta:real`] P3E_BETA_EPS_LT) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `&0 < beta * eps` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `beta * eps <= &1 * eps` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* the evolving neck e *)
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `beta * eps`; `x:A`; `t:real`; `t0:real`;
                 `e:real^3->A`] P3E_EVNECK_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `rfs_neck_dom eps SUBSET rfs_neck_dom (beta * eps) /\ open(rfs_neck_dom eps)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC APX_NECK_DOM_MONO THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[rfs_neck_dom; OPEN_ANNULUS]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. t' <= s /\ s <= t
        ==> smooth_manifold_atlas (rfs_top_at (hs:(A)rfs_history) s) (rfs_atlas_at hs s) /\
            mfd_param (rfs_top_at hs s) (rfs_atlas_at hs s) (rfs_neck_dom (beta * eps)) e`
  (LABEL_TAC "SLE") THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`hs:(A)rfs_history`; `beta * eps`; `x:A`; `t:real`; `t0:real`;
                   `e:real^3->A`; `s:real`] P3E_EVNECK_SLICE_PARAM) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  (* the neck at time t and the closeness on (-1,0], from the core (t0 < 1) *)
  (* or from e alone (t0 >= 1); then the persistence over (t - 1/R, t].     *)
  SUBGOAL_THEN
   `(!s. t - &1 / R < s /\ s <= t
         ==> smooth_manifold_atlas (rfs_top_at (hs:(A)rfs_history) s) (rfs_atlas_at hs s) /\
             mfd_param (rfs_top_at hs s) (rfs_atlas_at hs s) (rfs_neck_dom (beta * eps)) e) /\
    (?d. d < eps pow 2 /\
         !s y. --(&1) < s /\ s <= &0 /\ y IN rfs_neck_dom eps
               ==> lck_dist2 (rfs_kreg eps) (cylinder_flow s)
                             (p3e_nfam hs x t e s) y <= d)`
  STRIP_ASSUME_TAC THENL
   [ASM_CASES_TAC `t0 < &1` THENL
     [(* the gluing data and the core *)
      MP_TAC(ISPECL [`hs:(A)rfs_history`; `eps:real`; `beta:real`; `x:A`; `t:real`;
                     `t0:real`; `e:real^3->A`; `e':real^3->A`; `R:real`; `t':real`;
                     `R':real`] P3E_GDATA_FROM_HISTORY) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `psi:real^3->real^3` (X_CHOOSE_THEN `psi':real^3->real^3`
        (X_CHOOSE_THEN `yx:real^3` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "EPS"))))) THEN
      USE_THEN "CORE" (MP_TAC o SPECL [`t0:real`; `R' / R`;
                                      `p3e_nfam (hs:(A)rfs_history) x t e`;
                                      `p3e_nfam (hs:(A)rfs_history) x t' e'`;
                                      `psi:real^3->real^3`; `psi':real^3->real^3`;
                                      `yx:real^3`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
      CONJ_TAC THENL [ALL_TAC; EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[]] THEN
      (* the later neck *)
      MP_TAC(ISPECL [`hs:(A)rfs_history`; `beta * eps / &2`; `x:A`; `t':real`; `&1`;
                     `e':real^3->A`] P3E_EVNECK_BASIC) THEN
      UNDISCH_TAC `rfs_strong_neck (rfs_view (hs:(A)rfs_history)) (beta * eps / &2) x t' e'` THEN
      REWRITE_TAC[rfs_strong_neck] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      SUBGOAL_THEN `&0 < R` ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `(&1 - t0) / R < &1 / R'` ASSUME_TAC THENL
       [ASM_SIMP_TAC[REAL_LT_RDIV_EQ] THEN
        UNDISCH_TAC `R' / R * (&1 - t0) < &1` THEN
        REWRITE_TAC[real_div] THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      X_GEN_TAC `s:real` THEN STRIP_TAC THEN ASM_CASES_TAC `t' <= s` THENL
       [USE_THEN "SLE" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `t' - &1 / R' <= s /\ s <= t'` STRIP_ASSUME_TAC THENL
       [CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
        UNDISCH_TAC `t - &1 / R < s` THEN UNDISCH_TAC `(&1 - t0) / R < &1 / R'` THEN
        EXPAND_TAC "t'" THEN REWRITE_TAC[real_div] THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      MP_TAC(ISPECL [`hs:(A)rfs_history`; `beta * eps / &2`; `x:A`; `t':real`; `&1`;
                     `e':real^3->A`; `s:real`] P3E_EVNECK_SLICE_PARAM) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC MFD_PARAM_EQ THEN EXISTS_TAC `(e':real^3->A) o (psi:real^3->real^3)` THEN
      REWRITE_TAC[o_THM] THEN REPEAT CONJ_TAC THENL
       [ASM_REWRITE_TAC[];
        MATCH_MP_TAC MFD_PARAM_PRECOMPOSE THEN
        MAP_EVERY EXISTS_TAC [`rfs_neck_dom (beta * eps / &2)`;
                              `IMAGE (psi:real^3->real^3) (rfs_neck_dom (beta * eps))`;
                              `psi':real^3->real^3`] THEN
        UNDISCH_TAC `p3e_gdata eps beta t0 (R' / R) (p3e_nfam (hs:(A)rfs_history) x t e)
                       (p3e_nfam hs x t' e') psi psi' yx` THEN
        REWRITE_TAC[p3e_gdata] THEN SIMP_TAC[] THEN ASM_REWRITE_TAC[];
        X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN CONV_TAC SYM_CONV THEN
        USE_THEN "EPS" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      (* t0 >= 1: the evolving neck alone *)
      SUBGOAL_THEN `t' <= t - &1 / R` ASSUME_TAC THENL
       [EXPAND_TAC "t'" THEN MATCH_MP_TAC(REAL_ARITH `a <= b ==> t - b <= t - a`) THEN
        ASM_SIMP_TAC[REAL_LE_DIV2_EQ] THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      CONJ_TAC THENL
       [X_GEN_TAC `s:real` THEN STRIP_TAC THEN USE_THEN "SLE" MATCH_MP_TAC THEN
        ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      UNDISCH_TAC `rfs_close_fam (rfs_kreg (beta * eps)) (beta * eps) {s | --t0 < s /\ s <= &0}
                     (rfs_neck_dom (beta * eps)) cylinder_flow
                     (\s y. R %% rfs_pullback (rfs_atlas_at (hs:(A)rfs_history) (t + s / R)) e
                                   (rfs_metric_at hs (t + s / R)) y)` THEN
      REWRITE_TAC[rfs_close_fam; IN_ELIM_THM] THEN
      DISCH_THEN(X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "CF"))) THEN
      EXISTS_TAC `d:real` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `(beta * eps) pow 2` THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      MAP_EVERY X_GEN_TAC [`s:real`; `y:real^3`] THEN STRIP_TAC THEN
      MATCH_MP_TAC P3E_LCK_SHRINK THEN EXISTS_TAC `beta * eps` THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC;
        SUBGOAL_THEN `t' <= t + s / R /\ t + s / R <= t` STRIP_ASSUME_TAC THENL
         [MP_TAC(ISPECL [`R:real`; `t:real`; `--t0`; `s:real`; `&0`] P3E_TIME_BETWEEN) THEN
          ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN EXPAND_TAC "t'" THEN
          REWRITE_TAC[real_div; REAL_MUL_LZERO; REAL_MUL_LNEG] THEN REAL_ARITH_TAC;
          ALL_TAC] THEN
        USE_THEN "SLE" (MP_TAC o SPEC `t + s / R`) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
        MATCH_MP_TAC P3E_NFAM_FIELD THEN ASM_REWRITE_TAC[] THEN
        MP_TAC(ISPECL [`hs:(A)rfs_history`; `t + s / R`;
                       `IMAGE (e:real^3->A) (rfs_neck_dom (beta * eps))`] P3E_SLICE_RIEM) THEN
        ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
         [CONJ_TAC THENL
           [MATCH_MP_TAC MFD_PARAM_IMAGE_OPEN THEN
            MAP_EVERY EXISTS_TAC [`rfs_atlas_at (hs:(A)rfs_history) (t + s / R)`;
                                  `rfs_neck_dom (beta * eps)`] THEN
            ASM_REWRITE_TAC[SUBSET_REFL; rfs_neck_dom; OPEN_ANNULUS];
            ASM SET_TAC[]];
          SIMP_TAC[]];
        REWRITE_TAC[p3e_nfam] THEN ASM_REWRITE_TAC[ETA_AX] THEN
        USE_THEN "CF" MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
         [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[];
          UNDISCH_TAC `(y:real^3) IN rfs_neck_dom eps` THEN
          UNDISCH_TAC `rfs_neck_dom eps SUBSET rfs_neck_dom (beta * eps)` THEN SET_TAC[]]]];
    ALL_TAC] THEN
  (* the strong eps-neck e at (x,t) *)
  REWRITE_TAC[rfs_strong_neck; rfs_view; rfs_evolving_neck; rfs_neck] THEN
  ASM_REWRITE_TAC[REAL_LT_01] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MFD_PARAM_RESTRICT THEN EXISTS_TAC `rfs_neck_dom (beta * eps)` THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[rfs_close_on] THEN EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`&0`; `y:real^3`] o check (fun th ->
      can (find_term (fun t -> t = `rfs_kreg eps`)) (concl th) && is_forall(concl th))) THEN
    ASM_REWRITE_TAC[p3e_nfam; REAL_LE_REFL] THEN
    REWRITE_TAC[real_div; REAL_MUL_LZERO; REAL_ADD_RID; ETA_AX] THEN
    ANTS_TAC THENL [REAL_ARITH_TAC; SIMP_TAC[]];
    REWRITE_TAC[rfs_persists] THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_param")) (concl th) &&
      is_forall(concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MFD_PARAM_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`rfs_atlas_at (hs:(A)rfs_history) s`; `rfs_neck_dom (beta * eps)`] THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[rfs_close_fam; IN_ELIM_THM] THEN EXISTS_TAC `d:real` THEN
    ASM_REWRITE_TAC[] THEN MAP_EVERY X_GEN_TAC [`s:real`; `y:real^3`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`s:real`; `y:real^3`] o check (fun th ->
      can (find_term (fun t -> t = `rfs_kreg eps`)) (concl th) && is_forall(concl th))) THEN
    ASM_REWRITE_TAC[p3e_nfam; ETA_AX]]);;

let P3E_PROP_15_2_ROUTE = prove
 (`!u:A->bool. P3_PROP_15_2_ROUTE_STATEMENT u`,
  REWRITE_TAC[P3_PROP_15_2_ROUTE_STATEMENT; P3E_PROP_15_2]);;

