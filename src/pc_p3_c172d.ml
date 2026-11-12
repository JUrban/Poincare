(* ========================================================================= *)
(* Unit pc_p3_c172d: MT Lemma 17.2, part D (subcase (ii) of                 *)
(* MT p. 397): a strong neck at the first bad time whose sub-neck does not  *)
(* persist before ts - 1/Q meets a surgery cap created at ts - 1/Q, and x   *)
(* lies in the core of a (C,eps)-cap (MT pp. 398-401, with a repair of      *)
(* Claim 17.3).                                                             *)
(*                                                                         *)
(* The exposed point (D1).  A region persisting over (T1, ts]               *)
(* but over no (T1 - eta0, ts] starts at a surgery time T1 = T_k, k >= 1, and *)
(* meets one of the new cap cores of event k (otherwise it is open in the  *)
(* previous stage by P3S_EVENT_RETAINED).                                   *)
(* ========================================================================= *)

needs "src/pc_p3_c172x.ml";;
needs "src/pc_rfa_shiscale.ml";;
needs "src/pc_p3_c17vol.ml";;

prioritize_real();;
type_invention_error := true;;

let P3H_CAPFREE_RETAINED = prove
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

let P3H_EXPOSED_POINT = prove
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
  USE_THEN "pers" (MP_TAC o GEN_REWRITE_RULE I
    [CONJUNCT2(CONJUNCT2(SPEC_ALL P2C_VIEW_EXPAND))]) THEN
  REWRITE_TAC[P2C_RFS_VIEW_PARTS] THEN DISCH_THEN(LABEL_TAC "pers2") THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `T1:real`] RFS_SLAB) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `k = rfs_slab (hs:(A)rfs_history) T1` THEN STRIP_TAC THEN
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
    REWRITE_TAC[CONJUNCT2(CONJUNCT2(SPEC_ALL P2C_VIEW_EXPAND)); P2C_RFS_VIEW_PARTS] THEN
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
   [MATCH_MP_TAC P3H_CAPFREE_RETAINED THEN
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
                 `W:A->bool`] P3S_EVENT_RETAINED) THEN
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

(* ========================================================================= *)
(* Scalar curvature along evolving necks (the part of MT Lemma              *)
(* A.2 used in subcase (ii)).  The shrinking cylinders cyl(s), s <= 0, have *)
(* uniformly bounded curvature (cyl(s) = (1 - s) pw^* cyl(0)); C^2-closeness *)
(* to cyl(s) controls R / Q - 1 / (1 - s).                                   *)
(* ========================================================================= *)

let P3H_CYL_RM_BOUND = prove
 (`?K0. !s (y:real^3). s <= &0 /\ ~(y = vec 0)
                       ==> lrm_deriv_norm2 0 (cylinder_flow s) y <= K0 pow 2`,
  X_CHOOSE_TAC `K0:real` APX_CYL0_RM_BOUND THEN EXISTS_TAC `K0:real` THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &1 - s /\ &1 <= &1 - s` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `p = inv(sqrt(&1 - s))` THEN
  SUBGOAL_THEN `&0 < p /\ p pow 2 = inv(&1 - s)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "p" THEN ASM_SIMP_TAC[REAL_LT_INV_EQ; SQRT_POS_LT; REAL_POW_INV] THEN
    ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  ABBREV_TAC `ee = (p - &1) / &2` THEN
  SUBGOAL_THEN `&2 * ee + &1 = p` ASSUME_TAC THENL [EXPAND_TAC "ee" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `pw = \z:real^3. ((norm z pow 2) rpow ee) % z` THEN
  SUBGOAL_THEN
   `!z:real^3. z IN (:real^3) DELETE vec 0
               ==> cylinder_flow s z = (&1 - s) %% mpullback pw (cylinder_flow (&0)) z`
  ASSUME_TAC THENL
   [REWRITE_TAC[IN_DELETE; IN_UNIV] THEN X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    EXPAND_TAC "pw" THEN
    MP_TAC(SPECL [`ee:real`; `&0`; `z:real^3`] P3H_PW_CYL) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    ASM_REWRITE_TAC[MATRIX_CMUL_ASSOC; REAL_SUB_RZERO] THEN
    SUBGOAL_THEN `&1 - &1 / inv(&1 - s) = s /\ (&1 - s) * inv(&1 - s) = &1`
    (fun th -> REWRITE_TAC[th; MATRIX_CMUL_LID]) THEN
    UNDISCH_TAC `&0 < &1 - s` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `diffeomorphism_on ((:real^3) DELETE vec 0) ((:real^3) DELETE vec 0)
                  (pw:real^3->real^3) (\y. ((norm y pow 2) rpow (--ee / (&2 * ee + &1))) % y)`
  ASSUME_TAC THENL
   [EXPAND_TAC "pw" THEN MATCH_MP_TAC RFB_PW_DIFFEO THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `&0 < p` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `metric_field ((:real^3) DELETE vec 0) (cylinder_flow (&0))` ASSUME_TAC THENL
   [MATCH_MP_TAC RFB_CYL_METRIC_FIELD THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `metric_field ((:real^3) DELETE vec 0) (mpullback pw (cylinder_flow (&0)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC METRIC_FIELD_PULLBACK THEN
    MAP_EVERY EXISTS_TAC [`(:real^3) DELETE vec 0`;
                          `\y:real^3. ((norm y pow 2) rpow (--ee / (&2 * ee + &1))) % y`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^3) IN (:real^3) DELETE vec 0` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[IN_DELETE; IN_UNIV]; ALL_TAC] THEN
  MP_TAC(ISPECL [`0`; `cylinder_flow s`;
                 `\z. (&1 - s) %% mpullback (pw:real^3->real^3) (cylinder_flow (&0)) z`;
                 `(:real^3) DELETE vec 0`; `y:real^3`] LRM_DERIV_NORM2_LOCAL) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[] THEN SIMP_TAC[OPEN_DELETE; OPEN_UNIV];
    DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`(:real^3) DELETE vec 0`; `mpullback (pw:real^3->real^3) (cylinder_flow (&0))`;
                 `&1 - s`; `0`; `y:real^3`] RFA_LRM_DERIV_NORM2_SCALE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`0`; `(:real^3) DELETE vec 0`; `(:real^3) DELETE vec 0`;
                 `pw:real^3->real^3`;
                 `\y:real^3. ((norm y pow 2) rpow (--ee / (&2 * ee + &1))) % y`;
                 `cylinder_flow (&0)`; `y:real^3`] LRM_DERIV_NORM2_PULLBACK) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN `~((pw:real^3->real^3) y = vec 0)` ASSUME_TAC THENL
   [UNDISCH_TAC `diffeomorphism_on ((:real^3) DELETE vec 0) ((:real^3) DELETE vec 0)
                  (pw:real^3->real^3) (\y. ((norm y pow 2) rpow (--ee / (&2 * ee + &1))) % y)` THEN
    REWRITE_TAC[diffeomorphism_on] THEN STRIP_TAC THEN
    UNDISCH_TAC `IMAGE (pw:real^3->real^3) ((:real^3) DELETE vec 0) = (:real^3) DELETE vec 0` THEN
    REWRITE_TAC[EXTENSION; IN_IMAGE; IN_DELETE; IN_UNIV] THEN
    DISCH_THEN(MP_TAC o SPEC `(pw:real^3->real^3) y`) THEN
    MATCH_MP_TAC(TAUT `p ==> (p <=> q) ==> q`) THEN EXISTS_TAC `y:real^3` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1 * K0 pow 2` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE THEN ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE];
      MATCH_MP_TAC REAL_POW_1_LE THEN ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE] THEN
      MATCH_MP_TAC REAL_INV_LE_1 THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC RFA_RMD_POS THEN EXISTS_TAC `(:real^3) DELETE vec 0` THEN
      ASM_REWRITE_TAC[IN_DELETE; IN_UNIV];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    REAL_ARITH_TAC]);;

let P3H_CYL_SCALAR_STAB = prove
 (`!alpha. &0 < alpha
     ==> ?eta. &0 < eta /\
           !s S (G:real^3->real^3^3) y.
              s <= &0 /\ open S /\ S SUBSET ((:real^3) DELETE vec 0) /\ metric_field S G /\
              y IN S /\ lck_dist2 2 (cylinder_flow s) G y < eta pow 2
              ==> abs(lscalar G y - &1 / (&1 - s)) <= alpha`,
  GEN_TAC THEN DISCH_TAC THEN
  X_CHOOSE_TAC `K0:real` P3H_CYL_RM_BOUND THEN
  MP_TAC(INST_TYPE [`:3`,`:N`] (SPECL [`K0:real`; `alpha:real`] LCK_CURVATURE_STABILITY)) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `eta:real` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`s:real`; `S:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `~(y:real^3 = vec 0)` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`S:real^3->bool`; `cylinder_flow s`; `G:real^3->real^3^3`;
                                `y:real^3`]) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[] THEN MATCH_MP_TAC METRIC_FIELD_SUBSET THEN
    EXISTS_TAC `(:real^3) DELETE vec 0` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC RFB_CYL_METRIC_FIELD THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1) THEN
  SUBGOAL_THEN `lscalar (cylinder_flow s) y = &1 / (&1 - s)` SUBST1_TAC THENL
   [MATCH_MP_TAC RFB_CYL_SCALAR THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    SIMP_TAC[]]);;

(* R along an evolving neck: R(e y0, t + s / Q) / Q is within alpha of      *)
(* 1 / (1 - s) for eps small.                                                *)

let P3H_NECK_SCALAR = prove
 (`!alpha. &0 < alpha
     ==> ?eps2. &0 < eps2 /\
           !V eps x t a (e:real^3->A) s y0.
              p2c_regular_view V /\ rfs_evolving_neck V eps x t a e /\ eps <= eps2 /\
              --a < s /\ s <= &0 /\ y0 IN rfs_neck_dom eps
              ==> abs(rfs_vscalar V (t + s / rfs_vscalar V t x) (e y0) / rfs_vscalar V t x -
                      &1 / (&1 - s)) <= alpha`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP P3H_CYL_SCALAR_STAB) THEN
  DISCH_THEN(X_CHOOSE_THEN `eta:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "st"))) THEN
  EXISTS_TAC `min eta (&1 / &2)` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `eps:real`; `x:A`; `t:real`; `a:real`;
                 `e:real^3->A`; `s:real`] P2B9_REGULAR_NECK_SLICE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [P2B9_EVOLVING_NECK_ALT] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_evolving_neck")) (concl th))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o REWRITE_RULE[rfs_close_fam; IN_ELIM_THM])))) THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "cl"))) THEN
  SUBGOAL_THEN `&0 < eps` ASSUME_TAC THENL [ASM_MESON_TAC[rfs_neck]; ALL_TAC] THEN
  ABBREV_TAC `Q = rfs_vscalar (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                 (real->A->real^3^3)) t x` THEN
  ABBREV_TAC `u = t + s / Q` THEN
  ABBREV_TAC `H = \z. Q %% rfs_pullback (rfs_vatlas (V:(real->A topology)#
                     (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) u) (e:real^3->A)
                     (rfs_vmetric V u) z` THEN
  SUBGOAL_THEN `lscalar (H:real^3->real^3^3) y0 = rfs_vscalar (V:(real->A topology)#
                  (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) u (e y0) / Q`
  (SUBST1_TAC o SYM) THENL
   [EXPAND_TAC "H" THEN REWRITE_TAC[P2B9_RFS_VSCALAR] THEN
    MATCH_MP_TAC P2B9_PARAM_LSCALAR_SCALED THEN
    MAP_EVERY EXISTS_TAC [`rfs_vtop (V:(real->A topology)#
                             (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) u`;
                          `rfs_neck_dom eps`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  USE_THEN "st" MATCH_MP_TAC THEN EXISTS_TAC `rfs_neck_dom eps` THEN
  ASM_REWRITE_TAC[APX_NECK_DOM_OPEN; P2BL_NECK_DOM_NZ] THEN CONJ_TAC THENL
   [EXPAND_TAC "H" THEN MATCH_MP_TAC RFB_METRIC_FIELD_CMUL THEN
    ASM_REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC APX_RFS_PULLBACK_FIELD THEN
    EXISTS_TAC `rfs_vtop (V:(real->A topology)#
                  (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) u` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `d:real` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `lck_dist2 (rfs_kreg eps) (cylinder_flow s) (H:real^3->real^3^3) y0` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LCK_DIST_MONO THEN EXISTS_TAC `rfs_neck_dom eps` THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC APX_NECK_CYL_FIELD_GEN THEN ASM_REAL_ARITH_TAC;
        EXPAND_TAC "H" THEN MATCH_MP_TAC RFB_METRIC_FIELD_CMUL THEN
        ASM_REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC APX_RFS_PULLBACK_FIELD THEN
        EXISTS_TAC `rfs_vtop (V:(real->A topology)#
                      (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) u` THEN
        ASM_REWRITE_TAC[];
        MATCH_MP_TAC APX_KREG_TWO THEN ASM_REAL_ARITH_TAC];
      EXPAND_TAC "H" THEN EXPAND_TAC "u" THEN USE_THEN "cl" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[]];
    MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `eps pow 2` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* Curvature on the new cap at its creation time (D3).  Bounds               *)
(* of R and Rm of g0 on {dist <= r} (compactness), scalar curvature under   *)
(* C^2 closeness, and h(T)^2 R(Phi q, T) close to R_g0(q) on the cap         *)
(* (the closeness clause of p3_cap_param).  With an upper bound Dup of R_g0  *)
(* on the closed core this replaces Lemma 12.3's two-sided bound (only       *)
(* Q~ <= 5 Dup is used; Q~ > 1 comes from Claim 17.3).                       *)
(* ========================================================================= *)

let P3H_STD_BOUNDS = prove
 (`!g0 A0 r. p3_std_initial g0 A0
     ==> ?D. &1 <= D /\
             !x. p3_std_dist g0 x <= r
                 ==> abs(lscalar g0 x) <= D /\ lrm_deriv_norm2 0 g0 x <= D pow 2`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP P3S_STD_METRIC_FIELD) THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `r:real`] P3H_STD_REGION_COMPACT) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `K = {x:real^3 | p3_std_dist g0 x <= r}` THEN DISCH_TAC THEN
  SUBGOAL_THEN `bounded (IMAGE (\x:real^3. lift(lscalar g0 x)) K) /\
                bounded (IMAGE (\x:real^3. lift(lrm_deriv_norm2 0 g0 x)) K)` MP_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC COMPACT_IMP_BOUNDED THEN
    MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^3)` THEN
    REWRITE_TAC[SUBSET_UNIV] THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS THEN MATCH_MP_TAC LRG_LSCALAR_SMOOTH THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC LRM_DERIV_NORM2_CONTINUOUS THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE; NORM_LIFT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `B1:real` STRIP_ASSUME_TAC)
                             (X_CHOOSE_THEN `B2:real` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `&1 + B1 + B2` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(x:real^3) IN K` ASSUME_TAC THENL
   [EXPAND_TAC "K" THEN ASM_REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `&1 + B1 + B2 <= (&1 + B1 + B2) pow 2` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 <= (&1 + B1 + B2) * ((&1 + B1 + B2) - &1)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; REWRITE_TAC[REAL_POW_2] THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:real^3`) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:real^3`) THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* Scalar curvature under C^2 closeness: the form of APX_SCALAR_STABILITY_LIP  *)
(* with the closeness of rfs_close_on and rfs_mclose (lck_dist2 at the        *)
(* regularity rfs_kreg dd below dd^2).                                        *)

let P3H_SCALAR_CLOSE = prove
 (`!s (G0:real^3->real^3^3) G y K0 dd.
     metric_field s G0 /\ metric_field s G /\ y IN s /\
     lrm_deriv_norm2 0 G0 y <= K0 pow 2 /\
     &0 < dd /\ dd <= &1 / &10 /\ lck_dist2 (rfs_kreg dd) G0 G y <= dd pow 2
     ==> abs(lscalar G y - lscalar G0 y) <= &72 * (&1 + abs K0) * dd`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `lck_dist2 2 (G0:real^3->real^3^3) G y <= dd pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `lck_dist2 (rfs_kreg dd) (G0:real^3->real^3^3) G y` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LCK_DIST_MONO THEN
    EXISTS_TAC `s:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC APX_KREG_TWO THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(lck_dist2 2 (G0:real^3->real^3^3) G y) <= dd` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt(dd pow 2)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[POW_2_SQRT; REAL_LT_IMP_LE; REAL_LE_REFL]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`K0:real`; `s:real^3->bool`; `G0:real^3->real^3^3`; `G:real^3->real^3^3`;
                 `y:real^3`] APX_SCALAR_STABILITY_LIP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[DIMINDEX_3] THEN
  SUBGOAL_THEN `&8 * &3 pow 2 * (&1 + abs K0) * sqrt(lck_dist2 2 (G0:real^3->real^3^3) G y)
                <= &72 * (&1 + abs K0) * dd` MP_TAC THENL
   [SUBGOAL_THEN `&8 * &3 pow 2 * (&1 + abs K0) * sqrt(lck_dist2 2 (G0:real^3->real^3^3) G y) =
                  (&72 * (&1 + abs K0)) * sqrt(lck_dist2 2 G0 G y) /\
                  &72 * (&1 + abs K0) * dd = (&72 * (&1 + abs K0)) * dd`
    (CONJUNCTS_THEN SUBST1_TAC) THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    REAL_ARITH_TAC]);;

(* R on the new cap at its creation time T = T_k: h(T)^2 R(Phi q, T) is     *)
(* close to R_g0(q) (the closeness clause of p3_cap_param).                  *)

let P3H_CAP_SCALAR_T = prove
 (`!md g0 A0 dl h (hs:(A)rfs_history) k i Phi xi dd K0 q.
     rfs_history_ok hs /\ k <= hs_count hs /\ p3_std_initial g0 A0 /\
     p3_cap_param (md,g0,A0) (dl,h) hs k i Phi xi /\
     &0 < dd /\ dd <= &1 / &10 /\ dl(hs_time hs k) <= md dd /\ &0 < h(hs_time hs k) /\
     p3_std_dist g0 q < inv dd /\
     --(inv(dl(hs_time hs k))) < A0 + &4 - p3_std_dist g0 q /\
     lrm_deriv_norm2 0 g0 q <= K0 pow 2
     ==> abs(h(hs_time hs k) pow 2 *
             mfd_scalar (hs_atlas hs k) (hs_metric hs k (hs_time hs k)) (Phi q) -
             lscalar g0 q) <= &72 * (&1 + abs K0) * dd`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `k:num` o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o
              GEN_REWRITE_RULE I [rfs_history_ok]) THEN
  ASM_REWRITE_TAC[ricci_flow_from] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[p3_cap_param] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p3_cap_param")) (concl th))) THEN
  STRIP_TAC THEN
  ABBREV_TAC `T1 = hs_time (hs:(A)rfs_history) k` THEN
  ABBREV_TAC `Sp = {x:real^3 | --(inv(dl(T1:real))) < A0 + &4 - p3_std_dist g0 x}` THEN
  SUBGOAL_THEN `metric_field Sp (rfs_pullback (hs_atlas hs k) (Phi:real^3->A)
                                  (hs_metric (hs:(A)rfs_history) k T1))` ASSUME_TAC THENL
   [MATCH_MP_TAC APX_RFS_PULLBACK_FIELD THEN EXISTS_TAC `hs_top (hs:(A)rfs_history) k` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `metric_field Sp (g0:real^3->real^3^3)` ASSUME_TAC THENL
   [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `(:real^3)` THEN
    REWRITE_TAC[SUBSET_UNIV] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[P3S_STD_METRIC_FIELD]; ASM_MESON_TAC[metric_field]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(q:real^3) IN Sp` ASSUME_TAC THENL
   [EXPAND_TAC "Sp" THEN ASM_REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < inv(h(T1:real) pow 2)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_INV THEN ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `dd:real` o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_close_on")) (concl th))) THEN
  ASM_REWRITE_TAC[rfs_close_on] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `q:real^3`))) THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`Sp:real^3->bool`; `g0:real^3->real^3^3`;
                 `\x:real^3. inv(h(T1:real) pow 2) %%
                             rfs_pullback (hs_atlas hs k) (Phi:real^3->A)
                                          (hs_metric (hs:(A)rfs_history) k T1) x`;
                 `q:real^3`; `K0:real`; `dd:real`] P3H_SCALAR_CLOSE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC LRG_METRIC_FIELD_SCALE THEN ASM_REWRITE_TAC[ETA_AX]; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`Sp:real^3->bool`;
                 `rfs_pullback (hs_atlas hs k) (Phi:real^3->A)
                               (hs_metric (hs:(A)rfs_history) k T1)`;
                 `inv(h(T1:real) pow 2)`; `q:real^3`] LSCALAR_SCALE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`hs_top (hs:(A)rfs_history) k`; `hs_atlas (hs:(A)rfs_history) k`;
                 `hs_metric (hs:(A)rfs_history) k T1`; `Sp:real^3->bool`;
                 `Phi:real^3->A`; `q:real^3`] APX_PULLBACK_SCALAR_GEN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
  REWRITE_TAC[real_div; REAL_INV_INV] THEN REAL_ARITH_TAC);;

(* ========================================================================= *)
(* The exposed point y on the new cap at T = ts - 1/Q (D2, D3).              *)
(* R along the strong neck at (x,ts) stays in [(1/2 - alpha) Q, (1 + alpha) Q] *)
(* on (T, ts]; the lower bound passes to T by right continuity on slab k;   *)
(* with the cap closeness at T this bounds Q h(T)^2 by the curvature bound   *)
(* D of g0 on the closed core.                                                *)
(* ========================================================================= *)

(* A lower bound for R at a point y of stage k at times just after T_k      *)
(* holds at T_k (P3H_SCALAR_BOX: R is continuous from the right on slab k). *)

let P3H_EXPOSED_SCALAR_LOWER = prove
 (`!(hs:(A)rfs_history) k y ts c.
     rfs_history_ok hs /\ k <= hs_count hs /\ y IN topspace(hs_top hs k) /\
     hs_time hs k < ts /\
     (!tau. hs_time hs k < tau /\ tau <= ts ==> c <= rfs_vscalar (rfs_view hs) tau y)
     ==> c <= mfd_scalar (hs_atlas hs k) (hs_metric hs k (hs_time hs k)) y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  SUBGOAL_THEN `hs_time (hs:(A)rfs_history) k < hs_time hs (k + 1)` ASSUME_TAC THENL
   [FIRST_ASSUM(MATCH_MP_TAC o CONJUNCT1 o CONJUNCT2 o GEN_REWRITE_RULE I [rfs_history_ok]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `k:num`; `hs_time (hs:(A)rfs_history) k`; `y:A`;
                 `c:real`] P3H_SCALAR_BOX) THEN
  ASM_REWRITE_TAC[REAL_LE_REFL] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:A->bool` (X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC)) THEN
  ABBREV_TAC `T1 = hs_time (hs:(A)rfs_history) k` THEN
  ABBREV_TAC `T2 = hs_time (hs:(A)rfs_history) (k + 1)` THEN
  ABBREV_TAC `m = min d (min (ts - T1) (T2 - T1))` THEN
  SUBGOAL_THEN `&0 < m /\ m <= d /\ m <= ts - T1 /\ m <= T2 - T1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "m" THEN REWRITE_TAC[REAL_LT_MIN; REAL_MIN_LE; REAL_LE_REFL] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`T1 + m / &2`; `y:A`] o check (fun th ->
    is_forall(concl th) &&
    can (find_term (fun t -> t = `N:A->bool`)) (concl th))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `T1 + m / &2` o check (fun th ->
    is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_vscalar")) (concl th))) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `k:num`; `T1 + m / &2`] APX_RFS_SLAB) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[P2B9_RFS_VSCALAR; P2C_RFS_VIEW_PARTS] THEN
  REAL_ARITH_TAC);;

(* R along a strong neck at (x,ts) over (ts - 1/Q, ts] (D2): between        *)
(* (1/2 - alpha) Q and (1 + alpha) Q.                                         *)

let P3H_NECK_Y_BOUNDS = prove
 (`!alpha. &0 < alpha
     ==> ?eps3. &0 < eps3 /\
           !V eps x ts (e:real^3->A) y0 tau.
              p2c_regular_view V /\ rfs_strong_neck V eps x ts e /\ eps <= eps3 /\
              y0 IN rfs_neck_dom eps /\
              ts - &1 / rfs_vscalar V ts x < tau /\ tau <= ts
              ==> (&1 / &2 - alpha) * rfs_vscalar V ts x <= rfs_vscalar V tau (e y0) /\
                  rfs_vscalar V tau (e y0) <= (&1 + alpha) * rfs_vscalar V ts x`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP (INST_TYPE [`:A`,`:A`] P3H_NECK_SCALAR)) THEN
  DISCH_THEN(X_CHOOSE_THEN `eps2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ns"))) THEN
  EXISTS_TAC `eps2:real` THEN ASM_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o REWRITE_RULE[rfs_strong_neck] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_strong_neck")) (concl th))) THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `eps:real`; `x:A`; `ts:real`; `&1`;
                 `e:real^3->A`; `&0`] P2B9_REGULAR_NECK_SLICE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; STRIP_TAC] THEN
  ABBREV_TAC `Q = rfs_vscalar (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                 (real->A->real^3^3)) ts x` THEN
  SUBGOAL_THEN `--(&1) < (tau - ts) * Q /\ (tau - ts) * Q <= &0` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [SUBGOAL_THEN `--(&1 / Q) < tau - ts` MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `--(&1 / Q) * Q = --(&1)` (fun th -> REWRITE_TAC[GSYM th]) THENL
       [UNDISCH_TAC `&0 < Q` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LT_RMUL_EQ];
      MATCH_MP_TAC(REAL_ARITH `&0 <= (ts - tau) * Q ==> (tau - ts) * Q <= &0`) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REMOVE_THEN "ns" (MP_TAC o SPECL
    [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
     `eps:real`; `x:A`; `ts:real`; `&1`; `e:real^3->A`; `(tau - ts) * Q`; `y0:real^3`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `ts + ((tau - ts) * Q) / Q = tau` SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < Q` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  ABBREV_TAC `s = (tau - ts) * Q` THEN
  ABBREV_TAC `Ry = rfs_vscalar (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                  (real->A->real^3^3)) tau ((e:real^3->A) (y0:real^3))` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `&1 / &2 <= &1 / (&1 - s) /\ &1 / (&1 - s) <= &1` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < &1 - s` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `r = Ry / Q` THEN
  SUBGOAL_THEN `Ry = r * Q` SUBST1_TAC THENL
   [EXPAND_TAC "r" THEN UNDISCH_TAC `&0 < Q` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  CONJ_TAC THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC);;

(* D3: at the exposed point y = Phi q of the new cap (q in the closed core),  *)
(* (1/2 - alpha) Q <= R(y,T) (D2 and P3H_EXPOSED_SCALAR_LOWER) and           *)
(* h(T)^2 R(y,T) <= R_g0(q) + small (P3H_CAP_SCALAR_T): an upper bound for   *)
(* Q h(T)^2 in terms of D = sup of abs R_g0 on the closed core.               *)

let P3H_QT_UPPER = prove
 (`!(hs:(A)rfs_history) k i Phi xi y md g0 A0 dl h Q ts dd D alpha.
     rfs_history_ok hs /\ k <= hs_count hs /\ p3_std_initial g0 A0 /\
     p3_cap_param (md,g0,A0) (dl,h) hs k i Phi xi /\
     y IN IMAGE (ev_capm (hs_event hs k) i) (cball(vec 0,&1)) /\
     hs_time hs k < ts /\
     (!tau. hs_time hs k < tau /\ tau <= ts
            ==> (&1 / &2 - alpha) * Q <= rfs_vscalar (rfs_view hs) tau y) /\
     &0 < dd /\ dd <= &1 / &10 /\ dl(hs_time hs k) <= md dd /\ &0 < h(hs_time hs k) /\
     &0 < dl(hs_time hs k) /\ A0 + &4 < inv dd /\
     (!q. p3_std_dist g0 q <= A0 + &4
          ==> abs(lscalar g0 q) <= D /\ lrm_deriv_norm2 0 g0 q <= D pow 2)
     ==> (&1 / &2 - alpha) * Q * h(hs_time hs k) pow 2 <= D + &72 * (&1 + abs D) * dd`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o REWRITE_RULE[p3_cap_param] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p3_cap_param")) (concl th))) THEN
  STRIP_TAC THEN
  UNDISCH_TAC `(y:A) IN IMAGE (ev_capm (hs_event hs k) i) (cball(vec 0,&1))` THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq (concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "ev_capm")) (concl th))) THEN
  REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:real^3` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq (concl th) &&
    lhs(concl th) = `y:A`)) THEN
  SUBGOAL_THEN `p3_std_dist g0 q <= A0 + &4` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < inv(dl(hs_time (hs:(A)rfs_history) k))` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_INV THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`md:real->real`; `g0:real^3->real^3^3`; `A0:real`; `dl:real->real`;
                 `h:real->real`; `hs:(A)rfs_history`; `k:num`; `i:num`; `Phi:real^3->A`;
                 `xi:real^3->real^3`; `dd:real`; `D:real`; `q:real^3`] P3H_CAP_SCALAR_T) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `k:num`; `(Phi:real^3->A) q`; `ts:real`;
                 `(&1 / &2 - alpha) * Q`] P3H_EXPOSED_SCALAR_LOWER) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`hs_top (hs:(A)rfs_history) k`; `hs_atlas (hs:(A)rfs_history) k`;
                   `{x:real^3 | --(inv(dl(hs_time (hs:(A)rfs_history) k))) <
                                A0 + &4 - p3_std_dist g0 x}`; `Phi:real^3->A`]
                  GRGD_PARAM_FACTS) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[rfs_history_ok]; ALL_TAC] THEN
    STRIP_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "topspace")) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "IMAGE")) (concl th))) THEN
    REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN EXISTS_TAC `q:real^3` THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `Ry = mfd_scalar (hs_atlas hs k) (hs_metric (hs:(A)rfs_history) k (hs_time hs k))
                              ((Phi:real^3->A) q)` THEN
  ABBREV_TAC `hh = h(hs_time (hs:(A)rfs_history) k) pow 2` THEN
  SUBGOAL_THEN `&0 < hh` ASSUME_TAC THENL
   [EXPAND_TAC "hh" THEN ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `abs(lscalar (g0:real^3->real^3^3) (q:real^3)) <= D` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `((&1 / &2 - alpha) * Q) * hh <= Ry * hh` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* ========================================================================= *)
(* Claim 17.3 (D4), the core inequality.  The instantiation                  *)
(* (Prop 16.5 with the cutoff tc = ts, Prop 12.31, R14 at the exposed point) *)
(* is P3H_CLAIM_17_3_HIST of pc_p3_c172e.                                    *)
(* ========================================================================= *)

(* Claim 17.3 (MT p. 399, repaired), core inequality: if the standard        *)
(* flow has R >= c/(1-s) and the rescaled history metric Gh s stays C^2      *)
(* close to it at q with R(Gh s) <= M for 0 < s < min(theta1, t'), and the   *)
(* normalized curvature of Gs s at q is bounded (R14), then t' < theta1 as   *)
(* soon as c/(1-s) > 2M + 144 dq on [theta0, 1) for some theta0 < theta1.   *)

let P3H_CLAIM_17_3_CORE = prove
 (`!c theta0 theta1 M dq Kr tp (Gs:real->real^3->real^3^3) (Gh:real->real^3->real^3^3)
    (S:real^3->bool) q.
     &0 <= theta0 /\ theta0 < theta1 /\ &0 <= M /\ &0 < dq /\ dq <= &1 / &10 /\
     &0 <= Kr /\ &72 * sqrt Kr * dq <= &1 / &2 /\
     (!s. theta0 <= s /\ s < theta1 ==> &2 * M + &144 * dq < c / (&1 - s)) /\
     (!s. &0 < s /\ s < theta1 /\ s < tp
          ==> metric_field S (Gs s) /\ metric_field S (Gh s) /\ q IN S /\
              c / (&1 - s) <= lscalar (Gs s) q /\ lscalar (Gh s) q <= M /\
              lrm_deriv_norm2 0 (Gs s) q <= Kr * lscalar (Gs s) q pow 2 /\
              lck_dist2 (rfs_kreg dq) (Gs s) (Gh s) q <= dq pow 2)
     ==> tp < theta1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  ABBREV_TAC `s = (theta0 + theta1) / &2` THEN
  SUBGOAL_THEN `theta0 < s /\ s < theta1 /\ &0 < s /\ s < tp` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "lck_dist2")) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s:real`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  ABBREV_TAC `Rs = lscalar ((Gs:real->real^3->real^3^3) s) q` THEN
  ABBREV_TAC `Rh = lscalar ((Gh:real->real^3->real^3^3) s) q` THEN
  SUBGOAL_THEN `&0 < Rs` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^3->bool`; `(Gs:real->real^3->real^3^3) s`;
                 `(Gh:real->real^3->real^3^3) s`; `q:real^3`; `sqrt Kr * Rs`; `dq:real`]
                P3H_SCALAR_CLOSE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_POW_MUL] THEN ASM_SIMP_TAC[SQRT_POW_2]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 <= sqrt Kr * Rs` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[SQRT_POS_LE; REAL_LT_IMP_LE]; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`] THEN
  SUBGOAL_THEN `&72 * (sqrt Kr * Rs) * dq <= Rs / &2` MP_TAC THENL
   [SUBGOAL_THEN `&72 * (sqrt Kr * Rs) * dq = (&72 * sqrt Kr * dq) * Rs` SUBST1_TAC THENL
     [REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `Rs / &2 = (&1 / &2) * Rs` SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

