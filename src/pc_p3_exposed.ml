(* ========================================================================= *)
(* Unit pc_p3_exposed: exposed points of persisting sets.  A set W open in   *)
(* the slices on (T1,ts] that cannot persist on any (T1 - eta0,ts] meets a   *)
(* surgery cap at the surgery time T1 (P3X_EXPOSED_POINT); an open cap-free  *)
(* set of the new slice lies in the old one (P3X_CAPFREE_RETAINED).  These   *)
(* are copies of P3H_EXPOSED_POINT and P3H_CAPFREE_RETAINED (unit            *)
(* pc_p3_c172d) and of P3S_EVENT_RETAINED (pc_p3_s14ftr); the slab lemma     *)
(* P3X_SLAB_EXISTS is the existence part of RFS_SLAB (pc_p3_assembly).       *)
(* Used by pc_p3_s16small and pc_rfa_histc2c.                                *)
(* ========================================================================= *)

needs "src/pc_apx_event.ml";;
needs "src/pc_mfd_maps.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Slabs, persistence in a history view, retained sets at an                 *)
(* event (copy of P3S_EVENT_RETAINED, pc_p3_s14ftr), cap-free sets (copy of  *)
(* P3H_CAPFREE_RETAINED, pc_p3_c172d), exposed points (copy of P3H_EXPOSED_ *)
(* POINT, pc_p3_c172d, with RFS_SLAB and P2C_VIEW_EXPAND replaced by         *)
(* P3X_SLAB_EXISTS and P3X_PERSISTS_VIEW).                                   *)
(* ------------------------------------------------------------------------- *)

let P3X_SLAB_EXISTS = prove
 (`!hs:(A)rfs_history t.
        rfs_history_ok hs /\ &0 <= t /\ t < rfs_horizon hs
        ==> ?k. k <= hs_count hs /\ hs_time hs k <= t /\ t < hs_time hs (k + 1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `?j. t < hs_time (hs:(A)rfs_history) j /\ !m. m < j ==> ~(t < hs_time hs m)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM num_WOP] THEN EXISTS_TAC `hs_count (hs:(A)rfs_history) + 1` THEN
    ASM_MESON_TAC[rfs_horizon];
    ALL_TAC] THEN
  ASM_CASES_TAC `j = 0` THENL
   [UNDISCH_TAC `t < hs_time (hs:(A)rfs_history) j` THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [rfs_history_ok]) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `j - 1` THEN
  SUBGOAL_THEN `j - 1 + 1 = j` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[ARITH_RULE `(j:num) - 1 <= n <=> j <= n + 1`] THEN
    REWRITE_TAC[GSYM NOT_LT] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `hs_count (hs:(A)rfs_history) + 1`) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[rfs_horizon];
    REWRITE_TAC[GSYM REAL_NOT_LT] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]);;

let P3X_PERSISTS_VIEW = prove
 (`!(hs:(A)rfs_history) W a b.
     rfs_persists (rfs_view hs) W a b <=>
     !s. a < s /\ s <= b
         ==> smooth_manifold_atlas (rfs_top_at hs s) (rfs_atlas_at hs s) /\
             open_in (rfs_top_at hs s) W`,
  REWRITE_TAC[rfs_persists; rfs_view]);;

let P3X_EVENT_RETAINED = prove
 (`!topX atlasX (gX:real->A->real^3^3) ts topY atlasY gY ev W.
     smooth_manifold_atlas topX atlasX /\
     rfs_event_ok (topX,atlasX) gX ts (topY,atlasY) gY ev /\
     open_in topY W /\ W SUBSET topspace topX
     ==> open_in topX W /\ W SUBSET ev_omega ev /\
         smooth_manifold_atlas topY atlasY /\
         mfd_diffeo topY atlasY W topX atlasX W (\x. x) (\x. x) /\
         subtopology topY W = subtopology topX W`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rfs_event_ok] THEN STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_var o lhs o concl))) THEN
  ABBREV_TAC `Z = topspace(ev_ztop (ev:(A)rfs_event)) DIFF ev_disc ev` THEN
  SUBGOAL_THEN `open_in (ev_ztop (ev:(A)rfs_event)) Z` ASSUME_TAC THENL
   [EXPAND_TAC "Z" THEN ASM_MESON_TAC[closed_in]; ALL_TAC] THEN
  SUBGOAL_THEN `smooth_manifold_atlas (subtopology (ev_ztop ev) Z)
                  (restrict_atlas (ev_zatlas (ev:(A)rfs_event)) Z)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MANIFOLD_ATLAS_RESTRICT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `open_in (ev_ztop (ev:(A)rfs_event)) W /\ W SUBSET Z`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `open_in (subtopology (ev_ztop ev) Z) (W:A->bool)` THEN
    ASM_SIMP_TAC[OPEN_IN_OPEN_SUBTOPOLOGY];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o
              GEN_REWRITE_RULE I [mfd_cut_cap]) THEN
  DISCH_TAC THEN
  SUBGOAL_THEN
   `(W:A->bool) SUBSET
    topspace(ev_ztop ev) DIFF
    mfd_cut_cores (ev_index ev) (ev_capp ev) (ev_capm (ev:(A)rfs_event))`
  ASSUME_TAC THENL
   [UNDISCH_TAC `DISJOINT (topspace topX)
                   (mfd_cut_cores (ev_index ev) (ev_capp ev) (ev_capm (ev:(A)rfs_event)))` THEN
    UNDISCH_TAC `(W:A->bool) SUBSET topspace topX` THEN
    UNDISCH_TAC `(W:A->bool) SUBSET Z` THEN EXPAND_TAC "Z" THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_diffeo (ev_ztop ev) (ev_zatlas ev) W topX (atlasX:((A->bool)#(A->real^3))->bool) W (\x:A. x) (\x. x)`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o MATCH_MP MFD_DIFFEO_SYM) THEN
    DISCH_THEN(MP_TAC o SPEC `W:A->bool` o MATCH_MP
      (REWRITE_RULE[IMP_CONJ] MFD_DIFFEO_RESTRICT)) THEN
    ASM_REWRITE_TAC[IMAGE_ID];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_diffeo (subtopology (ev_ztop ev) Z) (restrict_atlas (ev_zatlas ev) Z) W
               topX (atlasX:((A->bool)#(A->real^3))->bool) W (\x:A. x) (\x. x)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_DIFFEO_SYM THEN
    MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`; `W:A->bool`;
                   `ev_ztop (ev:(A)rfs_event)`; `ev_zatlas (ev:(A)rfs_event)`;
                   `Z:A->bool`; `W:A->bool`; `\x:A. x`; `\x:A. x`]
                  APX_MFD_DIFFEO_RESTRICT_TARGET) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC MFD_DIFFEO_SYM THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[mfd_diffeo];
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `topspace (subtopology (ev_ztop ev) Z) INTER topspace topX:A->bool` THEN
    ASM_REWRITE_TAC[SUBSET_INTER] THEN
    ASM_MESON_TAC[OPEN_IN_SUBSET];
    UNDISCH_TAC
     `mfd_diffeo (subtopology (ev_ztop ev) Z) (restrict_atlas (ev_zatlas ev) Z) W
                 topX (atlasX:((A->bool)#(A->real^3))->bool) W (\x:A. x) (\x. x)` THEN
    REWRITE_TAC[mfd_diffeo; HOMEOMORPHIC_MAPS_ID] THEN MESON_TAC[]]);;

let P3X_CAPFREE_RETAINED = prove
 (`!topX atlasX (gX:real->A->real^3^3) ts topY atlasY gY ev W.
     rfs_event_ok (topX,atlasX) gX ts (topY,atlasY) gY ev /\ open_in topY W /\
     (!i. i IN ev_index ev ==> DISJOINT W (IMAGE (ev_capm ev i) (cball(vec 0,&1))))
     ==> W SUBSET topspace topX`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rfs_event_ok] THEN STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_var o lhs o concl))) THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o
              GEN_REWRITE_RULE I [mfd_cut_cap]) THEN
  DISCH_THEN(MP_TAC o MATCH_MP MFD_DIFFEO_MAPS) THEN REWRITE_TAC[IMAGE_ID] THEN
  STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP OPEN_IN_SUBSET o check (fun th ->
    can (find_term (fun t -> t = `W:A->bool`)) (concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "open_in")) (concl th))) THEN
  REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN
  DISCH_THEN(fun th -> SUBGOAL_THEN
   `!p:A. p IN W ==> p IN topspace(ev_ztop ev) /\ ~(p IN ev_disc (ev:(A)rfs_event))`
   (LABEL_TAC "Wz") THENL [MP_TAC th THEN SET_TAC[]; ALL_TAC]) THEN
  SUBGOAL_THEN
   `(W:A->bool) SUBSET topspace(ev_ztop ev) DIFF
                       mfd_cut_cores (ev_index ev) (ev_capp ev) (ev_capm (ev:(A)rfs_event))`
  MP_TAC THENL
   [REWRITE_TAC[SUBSET; IN_DIFF; IN_MFD_CUT_CORES] THEN X_GEN_TAC `p:A` THEN DISCH_TAC THEN
    USE_THEN "Wz" (MP_TAC o SPEC `p:A`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[NOT_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [`i:num`; `y:real^3`] THEN
    STRIP_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th ->
        can (find_term (fun t -> is_const t && fst(dest_const t) = "ev_capp")) (concl th) &&
        is_forall (concl th))) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_CBALL_0] THEN
      DISCH_THEN(MP_TAC o SPEC `y:real^3`) THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `~((p:A) IN ev_disc ev)` THEN ASM_REWRITE_TAC[];
      FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th ->
        can (find_term (fun t -> t = `W:A->bool`)) (concl th) && is_forall (concl th))) THEN
      ASM_REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_IMAGE; NOT_IN_EMPTY; IN_CBALL_0] THEN
      DISCH_THEN(MP_TAC o SPEC `p:A`) THEN ASM_REWRITE_TAC[] THEN
      EXISTS_TAC `y:real^3` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  FIRST_X_ASSUM((fun th -> REWRITE_TAC[th]) o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_cut_spheres")) (concl th) &&
    is_eq (concl th))) THEN
  SET_TAC[]);;

let P3X_EXPOSED_POINT = prove
 (`!(hs:(A)rfs_history) W T1 ts.
     rfs_history_ok hs /\ &0 < T1 /\ T1 < ts /\ ts < rfs_horizon hs /\
     rfs_persists (rfs_view hs) W T1 ts /\
     ~(?eta0. &0 < eta0 /\ rfs_persists (rfs_view hs) W (T1 - eta0) ts)
     ==> ?k i. 1 <= k /\ k <= hs_count hs /\ hs_time hs k = T1 /\
               i IN ev_index(hs_event hs k) /\
               ~DISJOINT W (IMAGE (ev_capm (hs_event hs k) i) (cball(vec 0,&1)))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "pers") (LABEL_TAC "np")))))) THEN
  USE_THEN "pers" (MP_TAC o GEN_REWRITE_RULE I [P3X_PERSISTS_VIEW]) THEN
  DISCH_THEN(LABEL_TAC "pers2") THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `T1:real`] P3X_SLAB_EXISTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC) THEN
  (* a time just after T1 in the slab of T1 *)
  ABBREV_TAC `s1 = (T1 + min ts (hs_time (hs:(A)rfs_history) (k + 1))) / &2` THEN
  SUBGOAL_THEN `T1 < s1 /\ s1 <= ts /\ s1 < hs_time (hs:(A)rfs_history) (k + 1)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "s1" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `k:num`; `s1:real`] APX_RFS_SLAB) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `open_in (hs_top (hs:(A)rfs_history) k) W /\
                smooth_manifold_atlas (hs_top hs k) (hs_atlas hs k)` STRIP_ASSUME_TAC THENL
   [USE_THEN "pers2" (MP_TAC o SPEC `s1:real`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[] THEN SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!a. a < T1 /\
        (!s. a < s /\ s <= T1
             ==> smooth_manifold_atlas (rfs_top_at hs s) (rfs_atlas_at hs s) /\
                 open_in (rfs_top_at (hs:(A)rfs_history) s) W)
        ==> F`
  (LABEL_TAC "contra") THENL
   [X_GEN_TAC `a:real` THEN STRIP_TAC THEN USE_THEN "np" MP_TAC THEN
    REWRITE_TAC[] THEN EXISTS_TAC `T1 - a` THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[P3X_PERSISTS_VIEW] THEN
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN ASM_CASES_TAC `s <= T1` THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      USE_THEN "pers2" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `hs_time (hs:(A)rfs_history) k = T1` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `a <= t /\ ~(a < t) ==> a = t`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN USE_THEN "contra" (MP_TAC o SPEC `hs_time (hs:(A)rfs_history) k`) THEN
    REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`hs:(A)rfs_history`; `k:num`; `s:real`] APX_RFS_SLAB) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `1 <= k` ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `1 <= k <=> ~(k = 0)`] THEN DISCH_TAC THEN
    UNDISCH_TAC `hs_time (hs:(A)rfs_history) k = T1` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `hs_time (hs:(A)rfs_history) 0 = &0` SUBST1_TAC THENL
     [ASM_MESON_TAC[rfs_history_ok]; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`k:num`] THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
  DISCH_THEN(ASSUME_TAC o REWRITE_RULE[NOT_EXISTS_THM; DE_MORGAN_THM]) THEN
  SUBGOAL_THEN
   `rfs_event_ok (hs_top hs (k - 1),hs_atlas hs (k - 1)) (hs_metric hs (k - 1))
                 (hs_time hs k) (hs_top hs k,hs_atlas hs k) (hs_metric hs k)
                 (hs_event (hs:(A)rfs_history) k)` ASSUME_TAC THENL
   [ASM_MESON_TAC[rfs_history_ok]; ALL_TAC] THEN
  SUBGOAL_THEN `k - 1 <= hs_count (hs:(A)rfs_history) /\ (k - 1) + 1 = k` STRIP_ASSUME_TAC
  THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `smooth_manifold_atlas (hs_top hs (k - 1)) (hs_atlas (hs:(A)rfs_history) (k - 1))`
  ASSUME_TAC THENL [ASM_MESON_TAC[rfs_history_ok]; ALL_TAC] THEN
  SUBGOAL_THEN `(W:A->bool) SUBSET topspace(hs_top (hs:(A)rfs_history) (k - 1))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P3X_CAPFREE_RETAINED THEN
    MAP_EVERY EXISTS_TAC [`hs_atlas (hs:(A)rfs_history) (k - 1)`;
                          `hs_metric (hs:(A)rfs_history) (k - 1)`;
                          `hs_time (hs:(A)rfs_history) k`; `hs_top (hs:(A)rfs_history) k`;
                          `hs_atlas (hs:(A)rfs_history) k`; `hs_metric (hs:(A)rfs_history) k`;
                          `hs_event (hs:(A)rfs_history) k`] THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "ev_capm")) (concl th) &&
      is_forall (concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`hs_top (hs:(A)rfs_history) (k - 1)`; `hs_atlas (hs:(A)rfs_history) (k - 1)`;
                 `hs_metric (hs:(A)rfs_history) (k - 1)`; `hs_time (hs:(A)rfs_history) k`;
                 `hs_top (hs:(A)rfs_history) k`; `hs_atlas (hs:(A)rfs_history) k`;
                 `hs_metric (hs:(A)rfs_history) k`; `hs_event (hs:(A)rfs_history) k`;
                 `W:A->bool`] P3X_EVENT_RETAINED) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  USE_THEN "contra" (MP_TAC o SPEC `hs_time (hs:(A)rfs_history) (k - 1)`) THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [SUBGOAL_THEN `hs_time (hs:(A)rfs_history) (k - 1) < hs_time hs ((k - 1) + 1)` MP_TAC THENL
     [ASM_MESON_TAC[rfs_history_ok]; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  X_GEN_TAC `s:real` THEN STRIP_TAC THEN ASM_CASES_TAC `s:real = T1` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    MP_TAC(ISPECL [`hs:(A)rfs_history`; `k:num`; `T1:real`] APX_RFS_SLAB) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL]; STRIP_TAC] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `k - 1`; `s:real`] APX_RFS_SLAB) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  ASM_REWRITE_TAC[]);;

