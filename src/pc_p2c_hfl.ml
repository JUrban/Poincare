(* ========================================================================= *)
(* Unit pc_p2c_hfl (Part 2C): P2C_HIST_FLOWLINE_PERSIST of pc_p2c_views.  A  *)
(* backward flow line of a history (y in every slice over [s,t]) has an open *)
(* neighbourhood persisting over (s,t]: the points alive in all stages from  *)
(* the slab of s to the slab of t.  At an event the retained points of the   *)
(* new stage form a set open in the new stage, and their subsets are open in *)
(* the new stage iff they are open in the old one (the identity              *)
(* diffeomorphism of mfd_cut_cap between X minus the cut spheres and Z minus *)
(* the cap cores).  Only pc_p2c_views is loaded (no region flows are needed: *)
(* persistence only asks for smooth atlases and open sets).                  *)
(* ========================================================================= *)

needs "src/pc_p2c_views.ml";;

prioritize_real();;
type_invention_error := true;;

let p2uf_mentions name th =
  can (find_term (fun t -> is_const t && fst(dest_const t) = name)) (concl th);;

(* ------------------------------------------------------------------------- *)
(* Retained points at an event.  P2UF_RETAINED_TOP and P2UF_EVENT_RETAINED   *)
(* are the topological half of P3S_EVENT_RETAINED (pc_p3_s14ftr), derived    *)
(* here from rfs_event_ok so that the unit stays below pc_p2c_iface.         *)
(* ------------------------------------------------------------------------- *)

let P2UF_RETAINED_TOP = prove
 (`!(X:A topology) Z D Sx Cz.
     open_in X (topspace X DIFF Sx) /\ open_in Z (topspace Z DIFF Cz) /\
     subtopology X (topspace X DIFF Sx) = subtopology Z (topspace Z DIFF Cz) /\
     DISJOINT (topspace X) Cz /\ closed_in Z D
     ==> open_in (subtopology Z (topspace Z DIFF D))
                 (topspace(subtopology Z (topspace Z DIFF D)) INTER topspace X) /\
         !V. V SUBSET topspace(subtopology Z (topspace Z DIFF D)) INTER topspace X
             ==> (open_in (subtopology Z (topspace Z DIFF D)) V <=> open_in X V)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 MP_TAC (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)))) THEN
  DISCH_THEN(fun th ->
    ASSUME_TAC(REWRITE_RULE[TOPSPACE_SUBTOPOLOGY]
                 (AP_TERM `topspace:(A)topology->A->bool` th)) THEN
    ASSUME_TAC(GEN `V:A->bool`
                 (AP_THM (AP_TERM `open_in:(A)topology->(A->bool)->bool` th) `V:A->bool`))) THEN
  SUBGOAL_THEN `open_in Z (topspace Z DIFF (D:A->bool))` ASSUME_TAC THENL
   [ASM_MESON_TAC[closed_in]; ALL_TAC] THEN
  REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN
  SUBGOAL_THEN `(topspace Z INTER (topspace Z DIFF D)) INTER topspace X =
                (topspace Z DIFF D) INTER (topspace Z DIFF (Cz:A->bool))`
  SUBST1_TAC THENL
   [UNDISCH_TAC `DISJOINT (topspace X) (Cz:A->bool)` THEN
    UNDISCH_TAC `topspace X INTER (topspace X DIFF Sx) =
                 topspace Z INTER (topspace Z DIFF (Cz:A->bool))` THEN
    SET_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_IN_SUBTOPOLOGY_INTER_OPEN THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `V:A->bool` THEN REWRITE_TAC[SUBSET_INTER] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(V:A->bool) SUBSET topspace X DIFF Sx` ASSUME_TAC THENL
   [UNDISCH_TAC `(V:A->bool) SUBSET topspace Z DIFF Cz` THEN
    UNDISCH_TAC `topspace X INTER (topspace X DIFF Sx) =
                 topspace Z INTER (topspace Z DIFF (Cz:A->bool))` THEN
    SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`Z:A topology`; `topspace Z DIFF (D:A->bool)`; `V:A->bool`]
    OPEN_IN_OPEN_SUBTOPOLOGY) THEN
  MP_TAC(ISPECL [`Z:A topology`; `topspace Z DIFF (Cz:A->bool)`; `V:A->bool`]
    OPEN_IN_OPEN_SUBTOPOLOGY) THEN
  MP_TAC(ISPECL [`X:A topology`; `topspace X DIFF (Sx:A->bool)`; `V:A->bool`]
    OPEN_IN_OPEN_SUBTOPOLOGY) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC TAUT);;

(* The history form: event k, X = stage k - 1, new stage k = Z minus D.      *)

let P2UF_EVENT_RETAINED = prove
 (`!(hs:(A)rfs_history) k.
     rfs_history_ok hs /\ 1 <= k /\ k <= hs_count hs
     ==> open_in (hs_top hs k)
                 (topspace(hs_top hs k) INTER topspace(hs_top hs (k - 1))) /\
         !V. V SUBSET topspace(hs_top hs k) INTER topspace(hs_top hs (k - 1))
             ==> (open_in (hs_top hs k) V <=> open_in (hs_top hs (k - 1)) V)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `rfs_event_ok (hs_top hs (k - 1),hs_atlas hs (k - 1))
                  (hs_metric (hs:(A)rfs_history) (k - 1)) (hs_time hs k)
                  (hs_top hs k,hs_atlas hs k) (hs_metric hs k) (hs_event hs k)`
  MP_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o
                  GEN_REWRITE_RULE I [rfs_history_ok]) THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `X = hs_top (hs:(A)rfs_history) (k - 1)` THEN
  ABBREV_TAC `ev = hs_event (hs:(A)rfs_history) k` THEN
  REWRITE_TAC[rfs_event_ok] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o
                GEN_REWRITE_RULE I [mfd_cut_cap] o
                check (fun th -> p2uf_mentions "mfd_cut_cap" th)) THEN
  REWRITE_TAC[mfd_diffeo; HOMEOMORPHIC_MAPS_ID] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`X:A topology`; `ev_ztop (ev:(A)rfs_event)`; `ev_disc (ev:(A)rfs_event)`;
                 `mfd_cut_spheres (ev_index ev) (ev_neck (ev:(A)rfs_event))`;
                 `mfd_cut_cores (ev_index ev) (ev_capp ev) (ev_capm (ev:(A)rfs_event))`]
    P2UF_RETAINED_TOP) THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Slices and slabs.                                                         *)
(* ------------------------------------------------------------------------- *)

let P2UF_NONEMPTY_LIVE = prove
 (`!(hs:(A)rfs_history) t y.
     y IN topspace(rfs_top_at hs t) ==> &0 <= t /\ t < rfs_horizon hs`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rfs_top_at; rfs_live; rfs_horizon] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[TOPSPACE_DISCRETE_TOPOLOGY; NOT_IN_EMPTY]);;

let P2UF_LIVE_AT = prove
 (`!(hs:(A)rfs_history) t.
     &0 <= t /\ t < rfs_horizon hs
     ==> rfs_top_at hs t = hs_top hs (rfs_slab hs t) /\
         rfs_atlas_at hs t = hs_atlas hs (rfs_slab hs t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rfs_top_at; rfs_atlas_at; rfs_live; rfs_horizon] THEN
  SIMP_TAC[]);;

let P2UF_STAGE_SMA = prove
 (`!(hs:(A)rfs_history) k.
     rfs_history_ok hs /\ k <= hs_count hs
     ==> smooth_manifold_atlas (hs_top hs k) (hs_atlas hs k)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o
                GEN_REWRITE_RULE I [rfs_history_ok]) THEN
  DISCH_THEN(MP_TAC o SPEC `k:num`) THEN ASM_SIMP_TAC[]);;

let P2UF_SLAB_MONO = prove
 (`!(hs:(A)rfs_history) s1 s2.
     rfs_history_ok hs /\ &0 <= s1 /\ s1 <= s2 /\ s2 < rfs_horizon hs
     ==> rfs_slab hs s1 <= rfs_slab hs s2`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `s1:real`] RFS_SLAB) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `s2:real`] RFS_SLAB) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  REWRITE_TAC[GSYM NOT_LT] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `rfs_slab (hs:(A)rfs_history) s2 + 1`;
                 `rfs_slab (hs:(A)rfs_history) s1`] RFS_TIME_MONO) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ASM_REAL_ARITH_TAC]);;

(* Every stage between the slabs of s and t is the slice at some time in [s,t]. *)

let P2UF_STAGE_HIT = prove
 (`!(hs:(A)rfs_history) s t k.
     rfs_history_ok hs /\ &0 <= s /\ s <= t /\ t < rfs_horizon hs /\
     rfs_slab hs s <= k /\ k <= rfs_slab hs t
     ==> ?s'. s <= s' /\ s' <= t /\ rfs_top_at hs s' = hs_top hs k`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `s:real`] RFS_SLAB) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `t:real`] RFS_SLAB) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  ASM_CASES_TAC `k = rfs_slab (hs:(A)rfs_history) s` THENL
   [EXISTS_TAC `s:real` THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN
    MP_TAC(ISPECL [`hs:(A)rfs_history`; `s:real`] P2UF_LIVE_AT) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  EXISTS_TAC `hs_time (hs:(A)rfs_history) k` THEN
  SUBGOAL_THEN `k <= hs_count (hs:(A)rfs_history)` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `hs_time (hs:(A)rfs_history) (rfs_slab hs s + 1) <= hs_time hs k /\
                hs_time hs k <= hs_time hs (rfs_slab hs t) /\
                hs_time hs k < hs_time hs (k + 1)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC RFS_TIME_MONO THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      MATCH_MP_TAC RFS_TIME_MONO THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      FIRST_ASSUM(MP_TAC o CONJUNCT1 o CONJUNCT2 o GEN_REWRITE_RULE I [rfs_history_ok]) THEN
      DISCH_THEN(MP_TAC o SPEC `k:num`) THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `hs_time (hs:(A)rfs_history) k`] P2UF_LIVE_AT) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN(SUBST1_TAC o CONJUNCT1)] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC RFS_SLAB_UNIQUE THEN
  ASM_REWRITE_TAC[REAL_LE_REFL]);;

(* ------------------------------------------------------------------------- *)
(* The points alive in all stages i..j are open in each of                  *)
(* them (forward induction to stage j, then back down along the events),   *)
(* and the headline.                                                        *)
(* ------------------------------------------------------------------------- *)

let p2uf_alive = new_definition
 `p2uf_alive (hs:(A)rfs_history) i j =
    {x | !k. i <= k /\ k <= j ==> x IN topspace(hs_top hs k)}`;;

let P2UF_ALIVE_FORWARD = prove
 (`!(hs:(A)rfs_history) i d.
     rfs_history_ok hs /\ i + d <= hs_count hs
     ==> open_in (hs_top hs (i + d)) (p2uf_alive hs i (i + d))`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[ADD_CLAUSES] THEN STRIP_TAC THEN
    SUBGOAL_THEN `p2uf_alive (hs:(A)rfs_history) i i = topspace(hs_top hs i)`
    SUBST1_TAC THENL
     [REWRITE_TAC[p2uf_alive; EXTENSION; IN_ELIM_THM] THEN
      MESON_TAC[LE_ANTISYM; LE_REFL];
      REWRITE_TAC[OPEN_IN_TOPSPACE]];
    ALL_TAC] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `i + SUC d = (i + d) + 1` SUBST1_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `m = i + d:num` THEN
  SUBGOAL_THEN `open_in (hs_top (hs:(A)rfs_history) m) (p2uf_alive hs i m)` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `m + 1:num`] P2UF_EVENT_RETAINED) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `(m + 1) - 1 = m:num`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "EV")) THEN
  SUBGOAL_THEN `p2uf_alive (hs:(A)rfs_history) i (m + 1) =
                p2uf_alive hs i m INTER
                (topspace(hs_top hs (m + 1)) INTER topspace(hs_top hs m))`
  ASSUME_TAC THENL
   [REWRITE_TAC[p2uf_alive; EXTENSION; IN_ELIM_THM; IN_INTER] THEN
    X_GEN_TAC `x:A` THEN EQ_TAC THENL
     [DISCH_TAC THEN REPEAT CONJ_TAC THENL
       [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC];
      STRIP_TAC THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
      ASM_CASES_TAC `k = m + 1` THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `p2uf_alive (hs:(A)rfs_history) i (m + 1) SUBSET
                topspace(hs_top hs (m + 1)) INTER topspace(hs_top hs m)`
  ASSUME_TAC THENL [ASM_REWRITE_TAC[] THEN SET_TAC[]; ALL_TAC] THEN
  USE_THEN "EV" (MP_TAC o SPEC `p2uf_alive (hs:(A)rfs_history) i (m + 1)`) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN `open_in (hs_top (hs:(A)rfs_history) m)
                  (topspace(hs_top hs (m + 1)) INTER topspace(hs_top hs m))`
  ASSUME_TAC THENL
   [USE_THEN "EV" (MP_TAC o SPEC `topspace(hs_top (hs:(A)rfs_history) (m + 1)) INTER
                                  topspace(hs_top hs m)`) THEN
    REWRITE_TAC[SUBSET_REFL] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC OPEN_IN_INTER THEN ASM_REWRITE_TAC[]);;

let P2UF_ALIVE_BACKWARD = prove
 (`!(hs:(A)rfs_history) i j d.
     rfs_history_ok hs /\ i + d <= j /\ j <= hs_count hs /\
     open_in (hs_top hs j) (p2uf_alive hs i j)
     ==> open_in (hs_top hs (j - d)) (p2uf_alive hs i j)`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL
   [SIMP_TAC[SUB_0]; ALL_TAC] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `open_in (hs_top (hs:(A)rfs_history) (j - d)) (p2uf_alive hs i j)`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `j - d:num`] P2UF_EVENT_RETAINED) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `(j - d) - 1 = j - SUC d`] THEN
  DISCH_THEN(MP_TAC o SPEC `p2uf_alive (hs:(A)rfs_history) i j` o CONJUNCT2) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[p2uf_alive; SUBSET; IN_ELIM_THM; IN_INTER] THEN
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN CONJ_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[]]);;

let P2UF_ALIVE_OPEN = prove
 (`!(hs:(A)rfs_history) i j k.
     rfs_history_ok hs /\ i <= k /\ k <= j /\ j <= hs_count hs
     ==> open_in (hs_top hs k) (p2uf_alive hs i j)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `i:num`; `j - i:num`] P2UF_ALIVE_FORWARD) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `i + (j - i) = j:num` SUBST1_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `i:num`; `j:num`; `j - k:num`]
    P2UF_ALIVE_BACKWARD) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `j - (j - k) = k:num` SUBST1_TAC THENL [ASM_ARITH_TAC; REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The headline.                                                             *)
(* ------------------------------------------------------------------------- *)

let P2UF_HIST_FLOWLINE_PERSIST = prove
 (`!u:A->bool. P2C_HIST_FLOWLINE_PERSIST_STATEMENT u`,
  GEN_TAC THEN REWRITE_TAC[P2C_HIST_FLOWLINE_PERSIST_STATEMENT] THEN
  MAP_EVERY X_GEN_TAC [`hs:(A)rfs_history`; `y:A`; `s:real`; `t:real`] THEN
  REWRITE_TAC[p3_flowline; p2c_local_persist; rfs_view; rfs_persists] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `(&0 <= s /\ s < rfs_horizon (hs:(A)rfs_history)) /\
                (&0 <= t /\ t < rfs_horizon hs)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC P2UF_NONEMPTY_LIVE THEN EXISTS_TAC `y:A` THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `t:real`] RFS_SLAB) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `s:real`; `t:real`] P2UF_SLAB_MONO) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  EXISTS_TAC `p2uf_alive (hs:(A)rfs_history) (rfs_slab hs s) (rfs_slab hs t)` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[p2uf_alive; IN_ELIM_THM] THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`hs:(A)rfs_history`; `s:real`; `t:real`; `k:num`] P2UF_STAGE_HIT) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `s':real` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `r:real` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `r:real`] P2UF_LIVE_AT) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN(CONJUNCTS_THEN SUBST1_TAC)] THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `r:real`] RFS_SLAB) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `s:real`; `r:real`] P2UF_SLAB_MONO) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `r:real`; `t:real`] P2UF_SLAB_MONO) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC P2UF_STAGE_SMA THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC P2UF_ALIVE_OPEN THEN ASM_REWRITE_TAC[]]);;

