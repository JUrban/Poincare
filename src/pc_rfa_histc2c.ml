(* ========================================================================= *)
(* Unit pc_rfa_histc2c: R13, the fresh-cap case and the assembly             *)
(* RFA_P3_HIST_C2_BOUND |- !u. P2C_HISTORY_REGULAR_STATEMENT u               *)
(* ==> P3_HIST_C2_BOUND_STATEMENT u.  A deep ball that does not persist over *)
(* the window meets a surgery cap created at T_k in the window               *)
(* (RFA_HC2_EXPOSED_GEN, after P3H_EXPOSED_POINT of pc_p3_c172d); at T_k the *)
(* cap is dd-close to h^2 g0 (p3_cap_param), so the curvature and its        *)
(* derivatives are bounded at scale h there, and h^-2 is at most a multiple  *)
(* of R(x); Shi's estimate with initial data (RFA_P2_THM_3_29, scaled) on    *)
(* the region over [T_k,t] gives the bound at (y,t).                         *)
(* ========================================================================= *)

needs "src/pc_rfa_histc2b.ml";;
needs "src/pc_p2c_hfl.ml";;
needs "src/pc_p2b_vscale.ml";;
needs "src/pc_p2c_stdinit.ml";;
needs "src/pc_p2c_rmdjb.ml";;
needs "src/pc_p2b_979s.ml";;
needs "src/pc_p3_exposed.ml";;

prioritize_real();;
type_invention_error := true;;


(* ------------------------------------------------------------------------- *)
(* The exposed point.  A region W open in the slice at ts that               *)
(* persists over (T1,ts] but over no (T1 - eta0,ts] starts at a surgery time *)
(* T1 = T_k, k >= 1, and meets one of the new caps of event k.               *)
(* RFA_HC2_EXPOSED_GEN is P3H_EXPOSED_POINT of pc_p3_c172d, generalized to   *)
(* T1 <= ts (for T1 = ts, W open in the slice at ts), using                  *)
(* P2UF_EVENT_RETAINED of pc_p2c_hfl (in place of P3S_EVENT_RETAINED) and    *)
(* P3X_CAPFREE_RETAINED of the shared unit pc_p3_exposed.                    *)
(* ------------------------------------------------------------------------- *)

let RFA_HC2_EXPOSED_GEN = prove
 (`!(hs:(A)rfs_history) W T1 ts.
     rfs_history_ok hs /\ &0 < T1 /\ T1 <= ts /\ ts < rfs_horizon hs /\
     open_in (rfs_top_at hs ts) W /\
     rfs_persists (rfs_view hs) W T1 ts /\
     ~(?eta0. &0 < eta0 /\ rfs_persists (rfs_view hs) W (T1 - eta0) ts)
     ==> ?k i. 1 <= k /\ k <= hs_count hs /\ hs_time hs k = T1 /\
               open_in (rfs_top_at hs T1) W /\
               i IN ev_index(hs_event hs k) /\
               ~DISJOINT W (IMAGE (ev_capm (hs_event hs k) i) (cball(vec 0,&1)))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "ots")
    (CONJUNCTS_THEN2 (LABEL_TAC "pers") (LABEL_TAC "np"))))))) THEN
  USE_THEN "pers" (MP_TAC o GEN_REWRITE_RULE I
    [CONJUNCT2(CONJUNCT2(SPEC_ALL P2C_VIEW_EXPAND))]) THEN
  REWRITE_TAC[P2C_RFS_VIEW_PARTS] THEN DISCH_THEN(LABEL_TAC "pers2") THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `T1:real`] RFS_SLAB) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `k = rfs_slab (hs:(A)rfs_history) T1` THEN STRIP_TAC THEN
  SUBGOAL_THEN `open_in (hs_top (hs:(A)rfs_history) k) W /\
                smooth_manifold_atlas (hs_top hs k) (hs_atlas hs k)` STRIP_ASSUME_TAC THENL
   [ASM_CASES_TAC `T1:real = ts` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN
      MP_TAC(ISPECL [`hs:(A)rfs_history`; `k:num`; `ts:real`] APX_RFS_SLAB) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
      REMOVE_THEN "ots" MP_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[rfs_history_ok];
      ALL_TAC] THEN
    ABBREV_TAC `s1 = (T1 + min ts (hs_time (hs:(A)rfs_history) (k + 1))) / &2` THEN
    SUBGOAL_THEN `T1 < s1 /\ s1 <= ts /\ s1 < hs_time (hs:(A)rfs_history) (k + 1)`
    STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "s1" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ISPECL [`hs:(A)rfs_history`; `k:num`; `s1:real`] APX_RFS_SLAB) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    USE_THEN "pers2" (MP_TAC o SPEC `s1:real`) THEN
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
  SUBGOAL_THEN `open_in (rfs_top_at (hs:(A)rfs_history) T1) W` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`hs:(A)rfs_history`; `k:num`; `T1:real`] APX_RFS_SLAB) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL]; STRIP_TAC] THEN ASM_REWRITE_TAC[];
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
  SUBGOAL_THEN `open_in (hs_top (hs:(A)rfs_history) (k - 1)) W` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`hs:(A)rfs_history`; `k:num`] P2UF_EVENT_RETAINED) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `W:A->bool` o CONJUNCT2) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[SUBSET_INTER] THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[OPEN_IN_SUBSET];
      DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
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

(* The first time of persistence: if a property of times fails somewhere on *)
(* (a,b], the infimum T1 of the c >= a with the property on (c,b] has it on *)
(* (T1,b], is > a, and the property fails on every (T1 - eta0,b].           *)

let RFA_HC2_INF_ARG = prove
 (`!P:real->bool a b.
     a < b /\ ~(!s. a < s /\ s <= b ==> P s)
     ==> ?T1. a < T1 /\ T1 <= b /\ (!s. T1 < s /\ s <= b ==> P s) /\
              ~(?eta0. &0 < eta0 /\ !s. T1 - eta0 < s /\ s <= b ==> P s)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "nall")) THEN
  ABBREV_TAC `S = {c | a <= c /\ c <= b /\ !s. c < s /\ s <= b ==> (P:real->bool) s}` THEN
  MP_TAC(ISPEC `S:real->bool` INF) THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `b:real` THEN EXPAND_TAC "S" THEN
      REWRITE_TAC[IN_ELIM_THM] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[REAL_LE_REFL] THEN REAL_ARITH_TAC;
      EXISTS_TAC `a:real` THEN EXPAND_TAC "S" THEN SIMP_TAC[IN_ELIM_THM]];
    ALL_TAC] THEN
  ABBREV_TAC `T1 = inf S` THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "inf1") (LABEL_TAC "inf2")) THEN
  SUBGOAL_THEN `a <= T1 /\ T1 <= b` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [USE_THEN "inf2" MATCH_MP_TAC THEN EXPAND_TAC "S" THEN SIMP_TAC[IN_ELIM_THM];
      USE_THEN "inf1" MATCH_MP_TAC THEN EXPAND_TAC "S" THEN REWRITE_TAC[IN_ELIM_THM] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[REAL_LE_REFL] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s. T1 < s /\ s <= b ==> (P:real->bool) s` (LABEL_TAC "pT") THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `~(!c. c IN S ==> s <= c)` MP_TAC THENL
     [DISCH_TAC THEN SUBGOAL_THEN `s <= T1` MP_TAC THENL
       [USE_THEN "inf2" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    REWRITE_TAC[NOT_FORALL_THM; NOT_IMP; REAL_NOT_LE] THEN
    DISCH_THEN(X_CHOOSE_THEN `c:real` STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC `(c:real) IN S` THEN EXPAND_TAC "S" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `T1:real` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `a <= t /\ ~(t = a) ==> a < t`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN USE_THEN "nall" MP_TAC THEN REWRITE_TAC[] THEN
    UNDISCH_THEN `T1:real = a` (SUBST_ALL_TAC o SYM) THEN USE_THEN "pT" ACCEPT_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `eta0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "pe"))) THEN
  SUBGOAL_THEN `max (T1 - eta0) a IN S` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN REWRITE_TAC[IN_ELIM_THM] THEN REPEAT CONJ_TAC THENL
     [REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      X_GEN_TAC `s:real` THEN STRIP_TAC THEN USE_THEN "pe" MATCH_MP_TAC THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `T1 <= max (T1 - eta0) a` MP_TAC THENL
   [USE_THEN "inf1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~(T1:real = a)` MP_TAC THENL
   [DISCH_TAC THEN USE_THEN "nall" MP_TAC THEN REWRITE_TAC[] THEN
    UNDISCH_THEN `T1:real = a` (SUBST_ALL_TAC o SYM) THEN USE_THEN "pT" ACCEPT_TAC;
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* A region open at ts that does not persist over (a,ts] meets a new cap of  *)
(* an event at a time T_k in (a,ts], and persists over (T_k,ts].            *)

let RFA_HC2_EXPOSED_WINDOW = prove
 (`!(hs:(A)rfs_history) W a ts.
     rfs_history_ok hs /\ &0 <= a /\ a < ts /\ ts < rfs_horizon hs /\
     open_in (rfs_top_at hs ts) W /\ ~rfs_persists (rfs_view hs) W a ts
     ==> ?k i. 1 <= k /\ k <= hs_count hs /\ a < hs_time hs k /\ hs_time hs k <= ts /\
               rfs_persists (rfs_view hs) W (hs_time hs k) ts /\
               open_in (rfs_top_at hs (hs_time hs k)) W /\
               i IN ev_index(hs_event hs k) /\
               ~DISJOINT W (IMAGE (ev_capm (hs_event hs k) i) (cball(vec 0,&1)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`\s. smooth_manifold_atlas (rfs_top_at hs s) (rfs_atlas_at hs s) /\
                      open_in (rfs_top_at (hs:(A)rfs_history) s) W`; `a:real`; `ts:real`]
                RFA_HC2_INF_ARG) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `~rfs_persists (rfs_view (hs:(A)rfs_history)) W a ts` THEN
    REWRITE_TAC[CONJUNCT2(CONJUNCT2(SPEC_ALL P2C_VIEW_EXPAND)); P2C_RFS_VIEW_PARTS];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `T1:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `W:A->bool`; `T1:real`; `ts:real`]
                RFA_HC2_EXPOSED_GEN) THEN
  ASM_REWRITE_TAC[CONJUNCT2(CONJUNCT2(SPEC_ALL P2C_VIEW_EXPAND)); P2C_RFS_VIEW_PARTS] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `k:num` THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `i:num` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[]);;


(* ------------------------------------------------------------------------- *)
(* The surgery cap at its creation time T_k.  Copies of lemmas of the Part 3 *)
(* units, identical up to the names:                                         *)
(*   RFA_HC2_STD_METRIC_FIELD   = P3S_STD_METRIC_FIELD   (pc_p3_s13rot)      *)
(*   RFA_HC2_STD_REGION_COMPACT = P3H_STD_REGION_COMPACT (pc_p3_c17vol)      *)
(*   RFA_HC2_STD_BOUNDS         = P3H_STD_BOUNDS         (pc_p3_c172d)       *)
(*   RFA_HC2_SCALAR_CLOSE       = P3H_SCALAR_CLOSE       (pc_p3_c172d)       *)
(*   RFA_HC2_CAP_SCALAR_T       = P3H_CAP_SCALAR_T       (pc_p3_c172d)       *)
(* ------------------------------------------------------------------------- *)

let RFA_HC2_STD_METRIC_FIELD = prove
 (`!g0 A0. p3_std_initial g0 A0 ==> metric_field (:real^3) g0`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p3_std_initial; riemannian_metric] THEN
  DISCH_THEN(MP_TAC o SPEC `((:real^3),(\x:real^3. x))` o CONJUNCT1) THEN
  REWRITE_TAC[RFB_OPEN_SET_ATLAS_CASES; FST; SND; IMAGE_ID;
              P2C_OPEN_SET_METRIC_LOCAL_UNIV]);;

let RFA_HC2_STD_REGION_COMPACT = prove
 (`!g0 A0 r. p3_std_initial g0 A0 ==> compact {x | p3_std_dist g0 x <= r}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `{x | p3_std_dist g0 x <= r} =
                mfd_cball (euclidean,open_set_atlas (:real^3)) g0 (vec 0) r` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; mfd_cball; IN_ELIM_THM; P2C_RAD_JOINABLE; p3_std_dist] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM COMPACT_IN_EUCLIDEAN] THEN
  UNDISCH_TAC `p3_std_initial g0 A0` THEN REWRITE_TAC[p3_std_initial; mfd_complete] THEN
  DISCH_THEN(MP_TAC o SPECL [`vec 0:real^3`; `r:real`] o CONJUNCT1 o CONJUNCT2) THEN
  REWRITE_TAC[TOPSPACE_EUCLIDEAN; IN_UNIV]);;

let RFA_HC2_STD_BOUNDS = prove
 (`!g0 A0 r. p3_std_initial g0 A0
     ==> ?D. &1 <= D /\
             !x. p3_std_dist g0 x <= r
                 ==> abs(lscalar g0 x) <= D /\ lrm_deriv_norm2 0 g0 x <= D pow 2`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RFA_HC2_STD_METRIC_FIELD) THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `r:real`] RFA_HC2_STD_REGION_COMPACT) THEN
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

let RFA_HC2_SCALAR_CLOSE = prove
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

let RFA_HC2_CAP_SCALAR_T = prove
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
     [ASM_MESON_TAC[RFA_HC2_STD_METRIC_FIELD]; ASM_MESON_TAC[metric_field]];
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
                 `q:real^3`; `K0:real`; `dd:real`] RFA_HC2_SCALAR_CLOSE) THEN
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



(* ------------------------------------------------------------------------- *)
(* Curves near a surgery cap at its creation time.  C^1 curves               *)
(* of real^N that stay in an open set s are curves of s with the same       *)
(* lengths and conversely; closeness of h^-2 Phi^* g to g0 in rfs_close_on   *)
(* compares Phi^* g with h^2 g0 as quadratic forms (RFA_HC2_CAP_QFORM); the  *)
(* tip Phi(0) is within g-distance sqrt(1 + dd) h (d(0,q) + 1) of Phi q      *)
(* (RFA_HC2_CAP_TIP_DIST); a short curve from Phi q stays in the image of   *)
(* the region d_g0 <= m (RFA_HC2_CAP_EXIT).                                  *)
(* ------------------------------------------------------------------------- *)

let RFA_HC2_UNIV_CURVE_TO_OPEN = prove
 (`!s (c:real->real^N) a b.
     open s /\ mfd_c1_curve (euclidean,open_set_atlas (:real^N)) c a b /\
     (!t. t IN real_interval[a,b] ==> c t IN s)
     ==> mfd_c1_curve (subtopology euclidean s,open_set_atlas s) c a b /\
         !G. mfd_length (open_set_atlas s) G c a b =
             mfd_length (open_set_atlas (:real^N)) G c a b`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `mfd_c1_curve (subtopology euclidean s,open_set_atlas s) (c:real->real^N) a b`
  ASSUME_TAC THENL
   [UNDISCH_TAC `mfd_c1_curve (euclidean,open_set_atlas (:real^N)) (c:real->real^N) a b` THEN
    REWRITE_TAC[mfd_c1_curve; CONTINUOUS_MAP_IN_SUBTOPOLOGY;
                TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY; RFB_OPEN_SET_ATLAS_CASES] THEN
    REWRITE_TAC[FORALL_UNWIND_THM2; FORALL_PAIR_THM; PAIR_EQ] THEN
    SIMP_TAC[IN_UNIV] THEN STRIP_TAC THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `{r | r IN interval[lift a,lift b] /\ (c:real->real^N)(drop r) IN s} =
      {r | r IN interval[lift a,lift b]}`
    (fun th -> REWRITE_TAC[th]) THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `r:real^1` THEN
      ASM_CASES_TAC `r IN interval[lift a,lift b]` THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      UNDISCH_TAC `r IN interval[lift a,lift b]` THEN
      REWRITE_TAC[IN_INTERVAL_1; IN_REAL_INTERVAL; LIFT_DROP];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_comb(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "continuously_differentiable"))
          (concl th))) THEN
    REWRITE_TAC[SET_RULE `!s:real^1->bool. {r | r IN s} = s`];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN GEN_TAC THEN
  SUBGOAL_THEN `mfd_c1_curve (subtopology euclidean (:real^N),open_set_atlas (:real^N))
                             (c:real->real^N) a b` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[SUBTOPOLOGY_UNIV]; ALL_TAC] THEN
  ASM_SIMP_TAC[MFD_LENGTH_OPEN_SET_ATLAS; OPEN_UNIV]);;

let RFA_HC2_OPEN_CURVE_TO_UNIV = prove
 (`!s (c:real->real^N) a b.
     open s /\ mfd_c1_curve (subtopology euclidean s,open_set_atlas s) c a b
     ==> mfd_c1_curve (euclidean,open_set_atlas (:real^N)) c a b /\
         (!t. t IN real_interval[a,b] ==> c t IN s) /\
         !G. mfd_length (open_set_atlas (:real^N)) G c a b =
             mfd_length (open_set_atlas s) G c a b`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!t. t IN real_interval[a,b] ==> (c:real->real^N) t IN s` ASSUME_TAC THENL
   [UNDISCH_TAC `mfd_c1_curve (subtopology euclidean s,open_set_atlas s) (c:real->real^N) a b` THEN
    REWRITE_TAC[mfd_c1_curve; CONTINUOUS_MAP_IN_SUBTOPOLOGY;
                TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_c1_curve (euclidean,open_set_atlas (:real^N)) (c:real->real^N) a b`
  ASSUME_TAC THENL
   [UNDISCH_TAC `mfd_c1_curve (subtopology euclidean s,open_set_atlas s) (c:real->real^N) a b` THEN
    REWRITE_TAC[mfd_c1_curve; CONTINUOUS_MAP_IN_SUBTOPOLOGY;
                TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY; RFB_OPEN_SET_ATLAS_CASES] THEN
    REWRITE_TAC[FORALL_UNWIND_THM2; FORALL_PAIR_THM; PAIR_EQ] THEN
    SIMP_TAC[IN_UNIV] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `{r | r IN interval[lift a,lift b] /\ (c:real->real^N)(drop r) IN s} =
      interval[lift a,lift b]`
    (fun th -> FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[th] o check (fun t ->
       can (find_term (fun u -> is_const u && fst(dest_const u) = "continuously_differentiable"))
           (concl t))) THEN
       REWRITE_TAC[SET_RULE `!t:real^1->bool. {r | r IN t} = t`]) THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `r:real^1` THEN
    ASM_CASES_TAC `r IN interval[lift a,lift b]` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `r IN interval[lift a,lift b]` THEN
    REWRITE_TAC[IN_INTERVAL_1; IN_REAL_INTERVAL; LIFT_DROP];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN GEN_TAC THEN
  SUBGOAL_THEN `mfd_c1_curve (subtopology euclidean (:real^N),open_set_atlas (:real^N))
                             (c:real->real^N) a b` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[SUBTOPOLOGY_UNIV]; ALL_TAC] THEN
  ASM_SIMP_TAC[MFD_LENGTH_OPEN_SET_ATLAS; OPEN_UNIV]);;

let RFA_HC2_G0_QFORM_NONNEG = prove
 (`!g0 A0 x w. p3_std_initial g0 A0 ==> &0 <= w dot ((g0:real^3->real^3^3) x ** w)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC P2AP_QFORM_NONNEG THEN
  MAP_EVERY EXISTS_TAC [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`] THEN
  REWRITE_TAC[P2C_EUCLID_FACTS; IN_UNIV] THEN ASM_MESON_TAC[p3_std_initial]);;

let RFA_HC2_CAP_QFORM = prove
 (`!top atlas (g:A->real^3^3) S (Phi:real^3->A) g0 A0 h k dd Sd x w.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_param top atlas S Phi /\ p3_std_initial g0 A0 /\ &0 < h /\ &0 < dd /\
     rfs_close_on k dd Sd g0 (\x. inv(h pow 2) %% rfs_pullback atlas Phi g x) /\
     Sd SUBSET S /\ x IN Sd
     ==> (&1 - dd) * h pow 2 * (w dot (g0 x ** w)) <=
         w dot (rfs_pullback atlas Phi g x ** w) /\
         w dot (rfs_pullback atlas Phi g x ** w) <=
         (&1 + dd) * h pow 2 * (w dot (g0 x ** w))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `metric_field S (rfs_pullback atlas (Phi:real^3->A) (g:A->real^3^3))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC APX_RFS_PULLBACK_FIELD THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `metric_field S (g0:real^3->real^3^3)` ASSUME_TAC THENL
   [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `(:real^3)` THEN
    REWRITE_TAC[SUBSET_UNIV] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[RFA_HC2_STD_METRIC_FIELD]; ASM_MESON_TAC[metric_field]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < inv(h pow 2)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_INV THEN ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `metric_field S (\x. inv(h pow 2) %%
                   rfs_pullback atlas (Phi:real^3->A) (g:A->real^3^3) x)` ASSUME_TAC THENL
   [MATCH_MP_TAC LRG_METRIC_FIELD_SCALE THEN ASM_REWRITE_TAC[ETA_AX]; ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^3) IN S` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `rfs_close_on k dd Sd (g0:real^3->real^3^3)
                 (\x. inv(h pow 2) %% rfs_pullback atlas (Phi:real^3->A) (g:A->real^3^3) x)` THEN
  REWRITE_TAC[rfs_close_on] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `x:real^3`))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`k:num`; `S:real^3->bool`; `g0:real^3->real^3^3`;
                 `\x. inv(h pow 2) %% rfs_pullback atlas (Phi:real^3->A) (g:A->real^3^3) x`;
                 `x:real^3`; `w:real^3`] LCK_DIST_C0) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `sqrt(lck_dist2 k (g0:real^3->real^3^3)
                  (\x. inv(h pow 2) %% rfs_pullback atlas (Phi:real^3->A) (g:A->real^3^3) x) x)
                <= dd` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt d` THEN CONJ_TAC THENL
     [REWRITE_TAC[SQRT_MONO_LE_EQ] THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt(dd pow 2)` THEN CONJ_TAC THENL
       [REWRITE_TAC[SQRT_MONO_LE_EQ] THEN ASM_REAL_ARITH_TAC;
        ASM_SIMP_TAC[POW_2_SQRT; REAL_LT_IMP_LE; REAL_LE_REFL]]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `x:real^3`; `w:real^3`]
                RFA_HC2_G0_QFORM_NONNEG) THEN
  ASM_REWRITE_TAC[MATRIX_VECTOR_LMUL; DOT_RMUL] THEN
  ABBREV_TAC `P = w dot (rfs_pullback atlas (Phi:real^3->A) (g:A->real^3^3) x ** w)` THEN
  ABBREV_TAC `Q = w dot ((g0:real^3->real^3^3) x ** w)` THEN
  ABBREV_TAC `sl = sqrt(lck_dist2 k (g0:real^3->real^3^3)
                  (\x. inv(h pow 2) %% rfs_pullback atlas (Phi:real^3->A) (g:A->real^3^3) x) x)` THEN
  REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `abs(inv(h pow 2) * P - Q) <= dd * Q` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sl * Q` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `P = h pow 2 * (inv(h pow 2) * P)` SUBST1_TAC THENL
   [REWRITE_TAC[REAL_MUL_ASSOC] THEN
    SUBGOAL_THEN `h pow 2 * inv(h pow 2) = &1` SUBST1_TAC THENL
     [MATCH_MP_TAC REAL_MUL_RINV THEN ASM_SIMP_TAC[REAL_POW_LT; REAL_LT_IMP_NZ];
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < h pow 2` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `h pow 2 * ((&1 - dd) * Q)` THEN CONJ_TAC THENL
     [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC];
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `h pow 2 * ((&1 + dd) * Q)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]]);;

let RFA_HC2_LE_INV_MUL = prove
 (`!x a b. &0 < x /\ a <= inv x * b ==> x * a <= b`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `x * inv x * b` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ASM_SIMP_TAC[REAL_MUL_ASSOC; REAL_MUL_RINV; REAL_LT_IMP_NZ; REAL_MUL_LID; REAL_LE_REFL]]);;

let RFA_HC2_CAP_CURVE_LENGTH = prove
 (`!top atlas (g:A->real^3^3) S (Phi:real^3->A) g0 A0 h k dd Sd c a b.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_param top atlas S Phi /\ p3_std_initial g0 A0 /\ &0 < h /\ &0 < dd /\ dd < &1 /\
     rfs_close_on k dd Sd g0 (\x. inv(h pow 2) %% rfs_pullback atlas Phi g x) /\
     Sd SUBSET S /\
     mfd_c1_curve (subtopology euclidean S,open_set_atlas S) c a b /\
     (!t. t IN real_interval[a,b] ==> c t IN Sd)
     ==> mfd_c1_curve (top,atlas) (Phi o c) a b /\
         mfd_length atlas g (Phi o c) a b <=
         sqrt(&1 + dd) * h * mfd_length (open_set_atlas S) g0 c a b /\
         sqrt(&1 - dd) * h * mfd_length (open_set_atlas S) g0 c a b <=
         mfd_length atlas g (Phi o c) a b`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `S:real^3->bool`;
                 `Phi:real^3->A`] GRGD_PARAM_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `Pi:A->real^3` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `S:real^3->bool`; `Phi:real^3->A`;
                 `rfs_pullback atlas (Phi:real^3->A) (g:A->real^3^3)`;
                 `c:real->real^3`; `a:real`; `b:real`] MFD_PARAM_C1_CURVE_LENGTH) THEN
  ASM_REWRITE_TAC[rfs_pullback] THEN REWRITE_TAC[GSYM rfs_pullback] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `smooth_manifold_atlas (subtopology euclidean S) (open_set_atlas (S:real^3->bool))`
  ASSUME_TAC THENL [ASM_SIMP_TAC[OPEN_SET_ATLAS]; ALL_TAC] THEN
  SUBGOAL_THEN `metric_field S (rfs_pullback atlas (Phi:real^3->A) (g:A->real^3^3)) /\
                metric_field S (g0:real^3->real^3^3)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC APX_RFS_PULLBACK_FIELD THEN EXISTS_TAC `top:A topology` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `(:real^3)` THEN
      ASM_REWRITE_TAC[SUBSET_UNIV] THEN ASM_MESON_TAC[RFA_HC2_STD_METRIC_FIELD]];
    ALL_TAC] THEN
  SUBGOAL_THEN `riemannian_metric (open_set_atlas S)
                  (rfs_pullback atlas (Phi:real^3->A) (g:A->real^3^3)) /\
                riemannian_metric (open_set_atlas S) (g0:real^3->real^3^3)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC RFB_OPEN_SET_RIEMANNIAN THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!t v. a <= t /\ t <= b
          ==> (&1 - dd) * h pow 2 * (v dot ((g0:real^3->real^3^3) (c t) ** v)) <=
              v dot (rfs_pullback atlas (Phi:real^3->A) (g:A->real^3^3) (c t) ** v) /\
              v dot (rfs_pullback atlas Phi g (c t) ** v) <=
              (&1 + dd) * h pow 2 * (v dot (g0 (c t) ** v))`
  (LABEL_TAC "qf") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC RFA_HC2_CAP_QFORM THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `S:real^3->bool`; `A0:real`; `k:num`;
                          `Sd:real^3->bool`] THEN
    ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[IN_REAL_INTERVAL];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < h pow 2 /\ &0 < &1 - dd` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_POW_LT] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`subtopology euclidean (S:real^3->bool)`; `open_set_atlas (S:real^3->bool)`;
                   `g0:real^3->real^3^3`;
                   `rfs_pullback atlas (Phi:real^3->A) (g:A->real^3^3)`;
                   `(&1 + dd) * h pow 2`; `c:real->real^3`; `a:real`; `b:real`]
                  MFD_LENGTH_METRIC_COMPARE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
      USE_THEN "qf" (MP_TAC o SPECL [`t:real`; `v:real^3`]) THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[SQRT_MUL] THEN ASM_SIMP_TAC[POW_2_SQRT; REAL_LT_IMP_LE] THEN
    REWRITE_TAC[REAL_MUL_ASSOC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`subtopology euclidean (S:real^3->bool)`; `open_set_atlas (S:real^3->bool)`;
                 `rfs_pullback atlas (Phi:real^3->A) (g:A->real^3^3)`; `g0:real^3->real^3^3`;
                 `inv((&1 - dd) * h pow 2)`; `c:real->real^3`; `a:real`; `b:real`]
                MFD_LENGTH_METRIC_COMPARE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_INV THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REPEAT STRIP_TAC THEN
    REMOVE_THEN "qf" (MP_TAC o SPECL [`t:real`; `v:real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(MP_TAC o CONJUNCT1)] THEN
    SUBGOAL_THEN `&0 < (&1 - dd) * h pow 2` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `inv((&1 - dd) * h pow 2) *
                (((&1 - dd) * h pow 2) *
                 (v dot ((g0:real^3->real^3^3) ((c:real->real^3) t) ** v)))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_EQ_IMP_LE THEN CONV_TAC SYM_CONV THEN
      MATCH_MP_TAC(REAL_FIELD `~(x = &0) ==> inv x * (x * q) = q`) THEN
      ASM_SIMP_TAC[REAL_LT_IMP_NZ];
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LE_INV; REAL_LT_IMP_LE] THEN
      ASM_REWRITE_TAC[GSYM REAL_MUL_ASSOC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt(&1 - dd) * h` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[SQRT_POS_LT]; ALL_TAC] THEN
  REWRITE_TAC[SQRT_INV; SQRT_MUL] THEN ASM_SIMP_TAC[POW_2_SQRT; REAL_LT_IMP_LE] THEN
  REWRITE_TAC[REAL_MUL_ASSOC] THEN
  DISCH_TAC THEN MATCH_MP_TAC RFA_HC2_LE_INV_MUL THEN ASM_REWRITE_TAC[]);;

let RFA_HC2_CAP_TIP_DIST = prove
 (`!top atlas (g:A->real^3^3) S (Phi:real^3->A) g0 A0 h k dd Sd q.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_param top atlas S Phi /\ p3_std_initial g0 A0 /\ &0 < h /\ &0 < dd /\ dd < &1 /\
     rfs_close_on k dd Sd g0 (\x. inv(h pow 2) %% rfs_pullback atlas Phi g x) /\
     Sd SUBSET S /\
     (!y. p3_std_dist g0 y < &2 * p3_std_dist g0 q + &1 ==> y IN Sd)
     ==> mfd_joinable (top,atlas) (Phi q) (Phi(vec 0)) /\
         mfd_dist (top,atlas) g (Phi q) (Phi(vec 0)) <=
         sqrt(&1 + dd) * h * (p3_std_dist g0 q + &1)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "inSd")))))))))) THEN
  SUBGOAL_THEN `riemannian_metric (open_set_atlas (:real^3)) (g0:real^3->real^3^3)`
  ASSUME_TAC THENL [ASM_MESON_TAC[p3_std_initial]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `S:real^3->bool`;
                 `Phi:real^3->A`] GRGD_PARAM_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `Pi:A->real^3` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
                 `g0:real^3->real^3^3`; `q:real^3`; `vec 0:real^3`;
                 `p3_std_dist g0 q + &1`] P2C_BALL_CURVE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[P2C_EUCLID_FACTS; mfd_ball; IN_ELIM_THM; P2C_RAD_JOINABLE] THEN
    REWRITE_TAC[p3_std_dist] THEN
    MP_TAC(ISPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
                   `g0:real^3->real^3^3`; `q:real^3`; `vec 0:real^3`] MFD_DIST_SYM) THEN
    REWRITE_TAC[P2C_EUCLID_FACTS] THEN DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real->real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!t. t IN real_interval[&0,&1] ==> (c:real->real^3) t IN Sd` ASSUME_TAC THENL
   [X_GEN_TAC `t:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
    USE_THEN "inSd" MATCH_MP_TAC THEN
    SUBGOAL_THEN `mfd_c1_curve (euclidean,open_set_atlas (:real^3)) (c:real->real^3) (&0) t`
    ASSUME_TAC THENL
     [MATCH_MP_TAC GRGD_C1_CURVE_SUBINTERVAL THEN
      MAP_EVERY EXISTS_TAC [`&0`; `&1`] THEN ASM_REWRITE_TAC[REAL_LE_REFL];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
                   `g0:real^3->real^3^3`; `c:real->real^3`; `&0`; `t:real`]
                  MFD_DIST_LE_LENGTH) THEN
    ASM_REWRITE_TAC[P2C_EUCLID_FACTS] THEN
    MP_TAC(ISPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
                   `g0:real^3->real^3^3`; `c:real->real^3`; `&0`; `t:real`; `&1`]
                  APX_LENGTH_PREFIX_LE) THEN
    ASM_REWRITE_TAC[P2C_EUCLID_FACTS] THEN
    MP_TAC(ISPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
                   `g0:real^3->real^3^3`; `vec 0:real^3`; `q:real^3`;
                   `(c:real->real^3) t`] MFD_DIST_TRIANGLE) THEN
    ASM_REWRITE_TAC[P2C_EUCLID_FACTS; P2C_RAD_JOINABLE] THEN
    REWRITE_TAC[GSYM p3_std_dist] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^3->bool`; `c:real->real^3`; `&0`; `&1`]
                RFA_HC2_UNIV_CURVE_TO_OPEN) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `S:real^3->bool`; `Phi:real^3->A`; `g0:real^3->real^3^3`; `A0:real`;
                 `h:real`; `k:num`; `dd:real`; `Sd:real^3->bool`; `c:real->real^3`;
                 `&0`; `&1`] RFA_HC2_CAP_CURVE_LENGTH) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(Phi:real^3->A) q = (Phi o c) (&0) /\ Phi(vec 0) = (Phi o c) (&1)`
  (CONJUNCTS_THEN SUBST1_TAC) THENL [ASM_REWRITE_TAC[o_THM]; ALL_TAC] THEN
  CONJ_TAC THENL [MATCH_MP_TAC MFD_C1_CURVE_JOINABLE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `mfd_length atlas (g:A->real^3^3) ((Phi:real^3->A) o c) (&0) (&1)` THEN
  CONJ_TAC THENL [MATCH_MP_TAC MFD_DIST_LE_LENGTH THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sqrt(&1 + dd) * h *
              mfd_length (open_set_atlas S) (g0:real^3->real^3^3) c (&0) (&1)` THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]);;

let RFA_HC2_STD_DIST_OPEN = prove
 (`!g0 A0 m. p3_std_initial g0 A0 ==> open {y:real^3 | p3_std_dist g0 y < m}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `{y:real^3 | p3_std_dist g0 y < m} =
                mfd_ball (euclidean,open_set_atlas (:real^3)) g0 (vec 0) m` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; mfd_ball; IN_ELIM_THM; P2C_RAD_JOINABLE; p3_std_dist]; ALL_TAC] THEN
  REWRITE_TAC[GSYM OPEN_IN_EUCLIDEAN] THEN MATCH_MP_TAC MFD_BALL_OPEN THEN
  REWRITE_TAC[P2C_EUCLID_FACTS] THEN ASM_MESON_TAC[p3_std_initial]);;

let RFA_HC2_CAP_EXIT = prove
 (`!top atlas (g:A->real^3^3) S (Phi:real^3->A) g0 A0 h k dd Sd q m w.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_param top atlas S Phi /\ p3_std_initial g0 A0 /\ &0 < h /\ &0 < dd /\ dd < &1 /\
     rfs_close_on k dd Sd g0 (\x. inv(h pow 2) %% rfs_pullback atlas Phi g x) /\
     Sd SUBSET S /\ (!y. p3_std_dist g0 y <= m ==> y IN Sd) /\ q IN S /\
     mfd_joinable (top,atlas) (Phi q) w /\
     p3_std_dist g0 q + mfd_dist (top,atlas) g (Phi q) w / (sqrt(&1 - dd) * h) < m
     ==> ?v. v IN S /\ p3_std_dist g0 v < m /\ w = Phi v`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (LABEL_TAC "inSd") STRIP_ASSUME_TAC))))))))))) THEN
  ABBREV_TAC `sh = sqrt(&1 - dd) * h` THEN
  SUBGOAL_THEN `&0 < sh` ASSUME_TAC THENL
   [EXPAND_TAC "sh" THEN MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SQRT_POS_LT THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `open (S:real^3->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[GRGD_PARAM_FACTS]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= mfd_dist (top,atlas) (g:A->real^3^3) ((Phi:real^3->A) q) w`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_DIST_POS_LE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `p3_std_dist g0 q < m` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `!a b m:real. &0 <= b /\ a + b < m ==> a < m`) THEN
    EXISTS_TAC `mfd_dist (top,atlas) (g:A->real^3^3) ((Phi:real^3->A) q) w / sh` THEN
    ASM_SIMP_TAC[REAL_LE_DIV; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  ABBREV_TAC `S' = {v:real^3 | v IN S /\ p3_std_dist g0 v < m}` THEN
  SUBGOAL_THEN `open (S':real^3->bool) /\ S' SUBSET S /\ S' SUBSET Sd /\ (q:real^3) IN S'`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [SUBGOAL_THEN `S' = (S:real^3->bool) INTER {v | p3_std_dist g0 v < m}` SUBST1_TAC THENL
       [EXPAND_TAC "S'" THEN SET_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC OPEN_INTER THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC RFA_HC2_STD_DIST_OPEN THEN EXISTS_TAC `A0:real` THEN ASM_REWRITE_TAC[];
      EXPAND_TAC "S'" THEN SET_TAC[];
      EXPAND_TAC "S'" THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
      USE_THEN "inSd" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      EXPAND_TAC "S'" THEN ASM_REWRITE_TAC[IN_ELIM_THM]];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_param top atlas S' (Phi:real^3->A)` ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_PARAM_RESTRICT THEN EXISTS_TAC `S:real^3->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `S':real^3->bool`;
                 `Phi:real^3->A`] GRGD_PARAM_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `Pi:A->real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `rfs_close_on k dd S' g0
                  (\x. inv(h pow 2) %% rfs_pullback atlas (Phi:real^3->A) (g:A->real^3^3) x)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_close_on k dd Sd g0
                   (\x. inv(h pow 2) %% rfs_pullback atlas (Phi:real^3->A) (g:A->real^3^3) x)` THEN
    REWRITE_TAC[rfs_close_on] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
    ALL_TAC] THEN
  (* a short curve to w *)
  SUBGOAL_THEN
   `?gam. mfd_c1_curve (top,atlas:((A->bool)#(A->real^3))->bool) gam (&0) (&1) /\
          gam(&0) = (Phi:real^3->A) q /\
          gam(&1) = w /\
          mfd_length atlas (g:A->real^3^3) gam (&0) (&1) < (m - p3_std_dist g0 q) * sh`
  (X_CHOOSE_THEN `gam:real->A` STRIP_ASSUME_TAC) THENL
   [MATCH_MP_TAC P2C_BALL_CURVE THEN ASM_REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN
    UNDISCH_TAC `p3_std_dist g0 q + mfd_dist (top,atlas) (g:A->real^3^3) ((Phi:real^3->A) q) w /
                 sh < m` THEN
    ASM_SIMP_TAC[REAL_ARITH `a + b < m <=> b < m - a`; REAL_LT_LDIV_EQ];
    ALL_TAC] THEN
  ABBREV_TAC `ell = mfd_length atlas (g:A->real^3^3) gam (&0) (&1)` THEN
  ABBREV_TAC `m1 = p3_std_dist g0 q + ell / sh` THEN
  SUBGOAL_THEN `m1 < m` ASSUME_TAC THENL
   [EXPAND_TAC "m1" THEN
    ASM_SIMP_TAC[REAL_ARITH `a + b < m <=> b < m - a`; REAL_LT_LDIV_EQ];
    ALL_TAC] THEN
  SUBGOAL_THEN `{v:real^3 | p3_std_dist g0 v <= m1} SUBSET S'` ASSUME_TAC THENL
   [EXPAND_TAC "S'" THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `v:real^3` THEN
    DISCH_TAC THEN CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    SUBGOAL_THEN `(v:real^3) IN Sd` MP_TAC THENL
     [USE_THEN "inSd" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `closed_in top (IMAGE (Phi:real^3->A) {v | p3_std_dist g0 v <= m1})`
  ASSUME_TAC THENL
   [MATCH_MP_TAC COMPACT_IN_IMP_CLOSED_IN THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MFD_PARAM_COMPACT_IMAGE THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `S':real^3->bool`] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC RFA_HC2_STD_REGION_COMPACT THEN
    EXISTS_TAC `A0:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the lift of an initial piece staying in IMAGE Phi S' ends in IMAGE Phi K *)
  SUBGOAL_THEN
   `!s. &0 <= s /\ s <= &1 /\
        (!u. &0 <= u /\ u <= s ==> (gam:real->A) u IN IMAGE (Phi:real^3->A) S')
        ==> gam s IN IMAGE Phi {v:real^3 | p3_std_dist g0 v <= m1}`
  (LABEL_TAC "lift") THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `mfd_c1_curve (top,atlas:((A->bool)#(A->real^3))->bool) (gam:real->A) (&0) s`
    ASSUME_TAC THENL
     [MATCH_MP_TAC GRGD_C1_CURVE_SUBINTERVAL THEN
      MAP_EVERY EXISTS_TAC [`&0`; `&1`] THEN ASM_REWRITE_TAC[REAL_LE_REFL];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `S':real^3->bool`;
                   `Phi:real^3->A`; `gam:real->A`; `&0`; `s:real`] MFD_PARAM_C1_CURVE_LIFT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `c:real->real^3` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(c:real->real^3) (&0) = q` ASSUME_TAC THENL
     [MATCH_MP_TAC MFD_PARAM_INJ THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                            `S':real^3->bool`; `Phi:real^3->A`] THEN
      ASM_MESON_TAC[REAL_LE_REFL];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `S':real^3->bool`; `Phi:real^3->A`; `g0:real^3->real^3^3`; `A0:real`;
                   `h:real`; `k:num`; `dd:real`; `S':real^3->bool`; `c:real->real^3`;
                   `&0`; `s:real`] RFA_HC2_CAP_CURVE_LENGTH) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[SUBSET_REFL; IN_REAL_INTERVAL] THEN ASM_MESON_TAC[];
      STRIP_TAC] THEN
    SUBGOAL_THEN `mfd_length atlas (g:A->real^3^3) ((Phi:real^3->A) o c) (&0) s <= ell`
    ASSUME_TAC THENL
     [SUBGOAL_THEN `mfd_length atlas (g:A->real^3^3) ((Phi:real^3->A) o c) (&0) s =
                    mfd_length atlas g gam (&0) s` SUBST1_TAC THENL
       [MATCH_MP_TAC MFD_LENGTH_EQ THEN REWRITE_TAC[IN_REAL_INTERVAL; o_THM] THEN
        ASM_MESON_TAC[];
        EXPAND_TAC "ell" THEN MATCH_MP_TAC APX_LENGTH_PREFIX_LE THEN
        EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`S':real^3->bool`; `c:real->real^3`; `&0`; `s:real`]
                  RFA_HC2_OPEN_CURVE_TO_UNIV) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `riemannian_metric (open_set_atlas (:real^3)) (g0:real^3->real^3^3)`
    ASSUME_TAC THENL [ASM_MESON_TAC[p3_std_initial]; ALL_TAC] THEN
    MP_TAC(ISPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
                   `g0:real^3->real^3^3`; `c:real->real^3`; `&0`; `s:real`]
                  MFD_DIST_LE_LENGTH) THEN
    ASM_REWRITE_TAC[P2C_EUCLID_FACTS] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
                   `g0:real^3->real^3^3`; `vec 0:real^3`; `q:real^3`;
                   `(c:real->real^3) s`] MFD_DIST_TRIANGLE) THEN
    ASM_REWRITE_TAC[P2C_EUCLID_FACTS; P2C_RAD_JOINABLE] THEN
    REWRITE_TAC[GSYM p3_std_dist] THEN DISCH_TAC THEN
    REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN EXISTS_TAC `(c:real->real^3) s` THEN
    CONJ_TAC THENL [ASM_MESON_TAC[REAL_LE_REFL]; ALL_TAC] THEN
    EXPAND_TAC "m1" THEN
    SUBGOAL_THEN `mfd_length (open_set_atlas S') (g0:real^3->real^3^3) c (&0) s <= ell / sh`
    MP_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `mfd_length atlas (g:A->real^3^3) ((Phi:real^3->A) o c) (&0) s` THEN
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "sh" THEN
      FIRST_X_ASSUM(MP_TAC o check (fun th ->
        can (find_term (fun t -> t = `sqrt(&1 - dd)`)) (concl th))) THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(w:A) IN IMAGE (Phi:real^3->A) S'` MP_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `gam:real->A`; `IMAGE (Phi:real^3->A) S'`]
                  GRGD_FIRST_TIME) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [ASM_MESON_TAC[mfd_c1_curve];
        ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
        EXISTS_TAC `&1` THEN ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `t1:real` (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "before"))))) THEN
    SUBGOAL_THEN
     `!s. &0 <= s /\ s < t1 ==> (gam:real->A) s IN IMAGE (Phi:real^3->A)
                                                  {v | p3_std_dist g0 v <= m1}`
    ASSUME_TAC THENL
     [X_GEN_TAC `s:real` THEN STRIP_TAC THEN USE_THEN "lift" MATCH_MP_TAC THEN
      REPEAT CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
        REPEAT STRIP_TAC THEN USE_THEN "before" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `gam:real->A`;
                   `IMAGE (Phi:real^3->A) {v | p3_std_dist g0 v <= m1}`; `t1:real`]
                  GRGD_CLOSED_LEFT_CURVE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[mfd_c1_curve]; ALL_TAC] THEN
    UNDISCH_TAC `~((gam:real->A) t1 IN IMAGE (Phi:real^3->A) S')` THEN
    UNDISCH_TAC `{v:real^3 | p3_std_dist g0 v <= m1} SUBSET S'` THEN SET_TAC[];
    ALL_TAC] THEN
  EXPAND_TAC "S'" THEN REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN MESON_TAC[]);;

let RFA_HC2_KREG4 = prove
 (`!dd. &0 < dd /\ dd <= &1 / &4 ==> 4 <= rfs_kreg dd`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN
  ASM_SIMP_TAC[RFS_KREG; REAL_LE_FLOOR; INTEGER_CLOSED] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(&1 / &4)` THEN CONJ_TAC THENL
   [CONV_TAC REAL_RAT_REDUCE_CONV;
    MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REWRITE_TAC[]]);;

(* |nabla^j Rm|^2 at T_k on the image of the region d_g0 <= A1, j <= 2:      *)
(* closeness in C^kreg(dd), kreg(dd) >= 4, to g0 on a compact neighbourhood   *)
(* (P2CJ_RMD2_FROM_LCK of pc_p2c_rmdjb) and the scaling of lrm_deriv_norm2.   *)

let RFA_HC2_CAP_RMD = prove
 (`!g0 A0 A1 dd j.
     p3_std_initial g0 A0 /\ &0 < dd /\ dd <= &1 / &4 /\ j <= 2
     ==> ?Cj. &0 < Cj /\
              !top atlas (g:A->real^3^3) S (Phi:real^3->A) h Sd v.
                smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
                mfd_param top atlas S Phi /\ &0 < h /\
                rfs_close_on (rfs_kreg dd) dd Sd g0
                  (\x. inv(h pow 2) %% rfs_pullback atlas Phi g x) /\
                Sd SUBSET S /\ (!y. p3_std_dist g0 y < A1 + &1 ==> y IN Sd) /\
                p3_std_dist g0 v <= A1
                ==> rfa_rmd2 j atlas g (Phi v) <= Cj * inv(h pow 2) pow (j + 2)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `K = {v:real^3 | p3_std_dist g0 v <= A1}` THEN
  ABBREV_TAC `V = {v:real^3 | p3_std_dist g0 v < A1 + &1}` THEN
  SUBGOAL_THEN `compact (K:real^3->bool) /\ open (V:real^3->bool) /\ K SUBSET V /\
                metric_field V (g0:real^3->real^3^3)` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["K"; "V"] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC RFA_HC2_STD_REGION_COMPACT THEN EXISTS_TAC `A0:real` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC RFA_HC2_STD_DIST_OPEN THEN EXISTS_TAC `A0:real` THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `(:real^3)` THEN
      REWRITE_TAC[SUBSET_UNIV] THEN CONJ_TAC THENL
       [ASM_MESON_TAC[RFA_HC2_STD_METRIC_FIELD];
        MATCH_MP_TAC RFA_HC2_STD_DIST_OPEN THEN EXISTS_TAC `A0:real` THEN
        ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `j + 2 <= rfs_kreg dd /\ dd pow 2 < &1` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `4` THEN CONJ_TAC THENL
       [ASM_ARITH_TAC; MATCH_MP_TAC RFA_HC2_KREG4 THEN ASM_REWRITE_TAC[]];
      MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `(&1 / &4) pow 2` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC; CONV_TAC REAL_RAT_REDUCE_CONV]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:real^3->bool`; `K:real^3->bool`; `g0:real^3->real^3^3`;
                 `rfs_kreg dd`; `dd pow 2`; `j:num`] P2CJ_RMD2_FROM_LCK) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `C0:real`) THEN
  EXISTS_TAC `max C0 (&1)` THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `G = \x. inv(h pow 2) %% rfs_pullback atlas (Phi:real^3->A) (g:A->real^3^3) x` THEN
  SUBGOAL_THEN `(V:real^3->bool) SUBSET S` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `Sd:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "V" THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(v:real^3) IN K /\ v IN V /\ v IN S` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `(v:real^3) IN K` ASSUME_TAC THENL
     [EXPAND_TAC "K" THEN ASM_REWRITE_TAC[IN_ELIM_THM]; ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `metric_field S (rfs_pullback atlas (Phi:real^3->A) (g:A->real^3^3))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC APX_RFS_PULLBACK_FIELD THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < h pow 2 /\ &0 < inv(h pow 2)` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_POW_LT; REAL_LT_INV]; ALL_TAC] THEN
  SUBGOAL_THEN `metric_field V (G:real^3->real^3^3)` ASSUME_TAC THENL
   [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `S:real^3->bool` THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "G" THEN MATCH_MP_TAC LRG_METRIC_FIELD_SCALE THEN
    ASM_REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
  SUBGOAL_THEN `lrm_deriv_norm2 j (G:real^3->real^3^3) v <= C0` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `z:real^3` THEN
    DISCH_TAC THEN
    UNDISCH_TAC `rfs_close_on (rfs_kreg dd) dd Sd g0 (G:real^3->real^3^3)` THEN
    ASM_REWRITE_TAC[rfs_close_on] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `z:real^3`))) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `rfs_pullback atlas (Phi:real^3->A) (g:A->real^3^3) =
                (\x. h pow 2 %% (G:real^3->real^3^3) x)` ASSUME_TAC THENL
   [EXPAND_TAC "G" THEN REWRITE_TAC[FUN_EQ_THM; MATRIX_CMUL_ASSOC] THEN
    ASM_SIMP_TAC[REAL_MUL_RINV; REAL_LT_IMP_NZ; MATRIX_CMUL_LID];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`j:num`; `top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `S:real^3->bool`; `Phi:real^3->A`; `v:real^3`]
                P2AP_PULLBACK_RMD_GEN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MP_TAC(ISPECL [`V:real^3->bool`; `G:real^3->real^3^3`; `h pow 2`; `j:num`; `v:real^3`]
                RFA_LRM_DERIV_NORM2_SCALE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
  ASM_SIMP_TAC[REAL_POW_LE; REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The surgery cap of event k at its creation time T = T_k, for dd chosen    *)
(* from g0, A0 and a distance factor c3: h(T)^2 R(Phi 0, T) >= R_g0(0)/2 at  *)
(* the tip (R_g0(0) > 0: curvature 1/4 there), every point z of the cap is  *)
(* within 2 (A0 + 5) h(T) of the tip, and every w with d_T(z,w) <= c3 h(T)   *)
(* is Phi v with d0(v) < A0 + 5 + 2 c3 and has abs(nabla^j Rm)^2 <=          *)
(* Cc h(T)^-2(j+2) at T, j <= 2 (RFA_HC2_CAP_TIP_DIST, _CAP_SCALAR_T,        *)
(* _CAP_EXIT, _CAP_RMD).                                                     *)
(* ------------------------------------------------------------------------- *)

let RFA_HC2_TIP_SCALAR = prove
 (`!g0 A0. p3_std_initial g0 A0 ==> &0 < lscalar g0 (vec 0:real^3)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM P2C_OPEN_SET_MFD_SCALAR] THEN
  MATCH_MP_TAC P2B_MFD_SCALAR_POS THEN EXISTS_TAC `euclidean:(real^3)topology` THEN
  REWRITE_TAC[P2C_EUCLID_FACTS; IN_UNIV] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[p3_std_initial]; ALL_TAC] THEN
  UNDISCH_TAC `p3_std_initial g0 A0` THEN REWRITE_TAC[p3_std_initial] THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`u:real^3`; `v:real^3`] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`vec 0:real^3`; `u:real^3`; `v:real^3`] o check (fun th ->
    is_forall(concl th) && can (find_term (fun t -> t = `&1 / &4`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [REWRITE_TAC[p3_std_dist] THEN
    MP_TAC(ISPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
                   `g0:real^3->real^3^3`; `vec 0:real^3`] MFD_DIST_REFL) THEN
    ASM_REWRITE_TAC[P2C_EUCLID_FACTS; IN_UNIV] THEN DISCH_THEN SUBST1_TAC THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC]);;

let RFA_HC2_CAP_STATIC = prove
 (`!g0 A0 c3.
     p3_std_initial g0 A0 /\ &0 <= c3
     ==> ?dd Cc. &0 < dd /\ dd <= &1 / &10 /\ &0 < Cc /\
           !md dl h (hs:(A)rfs_history) k i Phi xi.
             p3_modulus md /\ rfs_history_ok hs /\ k <= hs_count hs /\
             hausdorff_space (hs_top hs k) /\
             smooth_manifold_atlas (hs_top hs k) (hs_atlas hs k) /\
             riemannian_metric (hs_atlas hs k) (hs_metric hs k (hs_time hs k)) /\
             p3_cap_param (md,g0,A0) (dl,h) hs k i Phi xi /\
             &0 < dl(hs_time hs k) /\ dl(hs_time hs k) <= md dd /\ &0 < h(hs_time hs k)
             ==> lscalar g0 (vec 0) / &2 <=
                 h(hs_time hs k) pow 2 *
                 mfd_scalar (hs_atlas hs k) (hs_metric hs k (hs_time hs k)) (Phi(vec 0)) /\
                 !z. z IN IMAGE (ev_capm (hs_event hs k) i) (cball(vec 0,&1))
                     ==> mfd_joinable (hs_top hs k,hs_atlas hs k) z (Phi(vec 0)) /\
                         mfd_dist (hs_top hs k,hs_atlas hs k) (hs_metric hs k (hs_time hs k))
                                  z (Phi(vec 0)) <= &2 * (A0 + &5) * h(hs_time hs k) /\
                         !w j. mfd_joinable (hs_top hs k,hs_atlas hs k) z w /\
                               mfd_dist (hs_top hs k,hs_atlas hs k)
                                        (hs_metric hs k (hs_time hs k)) z w
                               <= c3 * h(hs_time hs k) /\ j <= 2
                               ==> rfa_rmd2 j (hs_atlas hs k) (hs_metric hs k (hs_time hs k)) w
                                   <= Cc * inv(h(hs_time hs k) pow 2) pow (j + 2)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `ct = lscalar g0 (vec 0:real^3)` THEN
  SUBGOAL_THEN `&0 < ct` ASSUME_TAC THENL
   [EXPAND_TAC "ct" THEN MATCH_MP_TAC RFA_HC2_TIP_SCALAR THEN EXISTS_TAC `A0:real` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < A0` ASSUME_TAC THENL [ASM_MESON_TAC[p3_std_initial]; ALL_TAC] THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `&0`] RFA_HC2_STD_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `D:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `p3_std_dist g0 (vec 0:real^3) = &0` ASSUME_TAC THENL
   [REWRITE_TAC[p3_std_dist] THEN MATCH_MP_TAC MFD_DIST_REFL THEN
    REWRITE_TAC[P2C_EUCLID_FACTS; IN_UNIV] THEN ASM_MESON_TAC[p3_std_initial];
    ALL_TAC] THEN
  SUBGOAL_THEN `lrm_deriv_norm2 0 g0 (vec 0:real^3) <= D pow 2` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `vec 0:real^3`) THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `m = A0 + &5 + &2 * c3` THEN
  ABBREV_TAC `dd = min (&1 / &10) (min (inv(&2 * A0 + &10))
                     (min (ct / (&144 * (&1 + D))) (inv(m + &2))))` THEN
  SUBGOAL_THEN `&0 < dd /\ dd <= &1 / &10 /\ (&2 * A0 + &9) < inv dd /\
                &72 * (&1 + D) * dd <= ct / &2 /\ m + &1 < inv dd`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < &2 * A0 + &10 /\ &0 < &144 * (&1 + D) /\ &0 < m + &2`
    STRIP_ASSUME_TAC THENL [EXPAND_TAC "m" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < dd` ASSUME_TAC THENL
     [EXPAND_TAC "dd" THEN REWRITE_TAC[REAL_LT_MIN] THEN
      ASM_SIMP_TAC[REAL_LT_INV; REAL_LT_DIV] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [EXPAND_TAC "dd" THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `&2 * A0 + &10` THEN
      CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM REAL_INV_INV] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "dd" THEN REAL_ARITH_TAC;
      SUBGOAL_THEN `dd <= ct / (&144 * (&1 + D))` MP_TAC THENL
       [EXPAND_TAC "dd" THEN REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `m + &2` THEN
      CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM REAL_INV_INV] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "dd" THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> is_eq(concl th) && rhs(concl th) = `dd:real`)) THEN
  SUBGOAL_THEN `dd <= &1 / &4` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `m:real`; `dd:real`; `0`]
                (INST_TYPE [`:A`,`:A`] RFA_HC2_CAP_RMD)) THEN
  ASM_REWRITE_TAC[ARITH] THEN DISCH_THEN(X_CHOOSE_THEN `C0:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `m:real`; `dd:real`; `1`]
                (INST_TYPE [`:A`,`:A`] RFA_HC2_CAP_RMD)) THEN
  ASM_REWRITE_TAC[ARITH] THEN DISCH_THEN(X_CHOOSE_THEN `C1:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `m:real`; `dd:real`; `2`]
                (INST_TYPE [`:A`,`:A`] RFA_HC2_CAP_RMD)) THEN
  ASM_REWRITE_TAC[ARITH] THEN DISCH_THEN(X_CHOOSE_THEN `C2:real` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`dd:real`; `max C0 (max C1 C2)`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`md:real->real`; `dl:real->real`; `h:real->real`;
                       `hs:(A)rfs_history`; `k:num`; `i:num`; `Phi:real^3->A`;
                       `xi:real^3->real^3`] THEN
  STRIP_TAC THEN
  (* the tip *)
  MP_TAC(ISPECL [`md:real->real`; `g0:real^3->real^3^3`; `A0:real`; `dl:real->real`;
                 `h:real->real`; `hs:(A)rfs_history`; `k:num`; `i:num`; `Phi:real^3->A`;
                 `xi:real^3->real^3`; `dd:real`; `D:real`; `vec 0:real^3`]
                RFA_HC2_CAP_SCALAR_T) THEN
  ASM_REWRITE_TAC[REAL_SUB_RZERO] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_INV THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC(REAL_ARITH `&0 < a /\ &0 <= b ==> --a < b`) THEN
      ASM_SIMP_TAC[REAL_LT_INV] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `abs D = D` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> not(is_forall(concl th)) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "real_abs")) (concl th))) THEN
  (* unpack the cap *)
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [p3_cap_param] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p3_cap_param")) (concl th))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "capim")
    (CONJUNCTS_THEN2 (LABEL_TAC "close") ASSUME_TAC))))) THEN
  USE_THEN "close" (MP_TAC o SPEC `dd:real`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  ABBREV_TAC `T1 = hs_time (hs:(A)rfs_history) k` THEN
  ABBREV_TAC `hT = (h:real->real) T1` THEN
  ABBREV_TAC `S = {x:real^3 | --(inv((dl:real->real) T1)) < A0 + &4 - p3_std_dist g0 x}` THEN
  ABBREV_TAC `Sd = {x:real^3 | p3_std_dist g0 x < inv dd /\
                               --(inv((dl:real->real) T1)) < A0 + &4 - p3_std_dist g0 x}` THEN
  SUBGOAL_THEN `(Sd:real^3->bool) SUBSET S /\
                (!y:real^3. p3_std_dist g0 y < inv dd ==> y IN Sd)` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["S"; "Sd"] THEN CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN REWRITE_TAC[IN_ELIM_THM] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `inv dd <= inv((dl:real->real) T1)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(md:real->real) dd` THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[p3_modulus];
      UNDISCH_TAC `p3_std_dist g0 y < inv dd` THEN UNDISCH_TAC `&0 < A0` THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt(&1 - dd) * hT /\ &1 / &2 <= sqrt(&1 - dd) /\ sqrt(&1 + dd) <= &2`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&1 / &2 <= sqrt(&1 - dd)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_RSQRT THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
        UNDISCH_TAC `dd <= &1 / &10` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN UNDISCH_TAC `&1 / &2 <= sqrt(&1 - dd)` THEN
        UNDISCH_TAC `&0 < hT` THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_LSQRT THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
        UNDISCH_TAC `dd <= &1 / &10` THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  X_GEN_TAC `z:A` THEN USE_THEN "capim" (SUBST1_TAC o SYM) THEN
  REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `qz:real^3` (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC)) THEN
  SUBGOAL_THEN `(qz:real^3) IN S` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 < a /\ &0 <= b ==> --a < b`) THEN
    ASM_SIMP_TAC[REAL_LT_INV];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`hs_top (hs:(A)rfs_history) k`; `hs_atlas (hs:(A)rfs_history) k`;
                 `hs_metric (hs:(A)rfs_history) k T1`; `S:real^3->bool`; `Phi:real^3->A`;
                 `g0:real^3->real^3^3`; `A0:real`; `hT:real`; `rfs_kreg dd`; `dd:real`;
                 `Sd:real^3->bool`; `qz:real^3`] RFA_HC2_CAP_TIP_DIST) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [UNDISCH_TAC `dd <= &1 / &10` THEN
      REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `p3_std_dist g0 y < &2 * p3_std_dist g0 qz + &1` THEN
      UNDISCH_TAC `&0 <= A0 + &4 - p3_std_dist g0 qz` THEN UNDISCH_TAC `&2 * A0 + &9 < inv dd` THEN
      REAL_ARITH_TAC;
    ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sqrt(&1 + dd) * hT * (p3_std_dist g0 qz + &1)` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&0 <= p3_std_dist g0 qz` ASSUME_TAC THENL
     [REWRITE_TAC[p3_std_dist] THEN MATCH_MP_TAC MFD_DIST_POS_LE THEN
      REWRITE_TAC[P2C_EUCLID_FACTS; P2C_RAD_JOINABLE] THEN ASM_MESON_TAC[p3_std_initial];
      ALL_TAC] THEN
    SUBGOAL_THEN `hT * (p3_std_dist g0 qz + &1) <= hT * (A0 + &5)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN UNDISCH_TAC `&0 <= A0 + &4 - p3_std_dist g0 qz` THEN
        UNDISCH_TAC `&0 < hT` THEN REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= hT * (p3_std_dist g0 qz + &1)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN UNDISCH_TAC `&0 <= p3_std_dist g0 qz` THEN
        UNDISCH_TAC `&0 < hT` THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&2 * (hT * (p3_std_dist g0 qz + &1))` THEN
    CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&2 * (hT * (A0 + &5))` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`w:A`; `j:num`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`hs_top (hs:(A)rfs_history) k`; `hs_atlas (hs:(A)rfs_history) k`;
                 `hs_metric (hs:(A)rfs_history) k T1`; `S:real^3->bool`; `Phi:real^3->A`;
                 `g0:real^3->real^3^3`; `A0:real`; `hT:real`; `rfs_kreg dd`; `dd:real`;
                 `Sd:real^3->bool`; `qz:real^3`; `m:real`; `w:A`] RFA_HC2_CAP_EXIT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `dd <= &1 / &10` THEN REAL_ARITH_TAC;
      X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      UNDISCH_TAC `p3_std_dist g0 y <= m` THEN UNDISCH_TAC `m + &1 < inv dd` THEN REAL_ARITH_TAC;
      SUBGOAL_THEN
       `mfd_dist (hs_top hs k,hs_atlas hs k) (hs_metric (hs:(A)rfs_history) k T1)
                 ((Phi:real^3->A) qz) w / (sqrt(&1 - dd) * hT) <= &2 * c3`
      MP_TAC THENL
       [ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `c3 * hT` THEN ASM_REWRITE_TAC[] THEN
        SUBGOAL_THEN `(&2 * c3) * (sqrt(&1 - dd) * hT) = (c3 * hT) * (&2 * sqrt(&1 - dd))`
        SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
        GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
        CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_MUL THEN UNDISCH_TAC `&0 < hT` THEN
          UNDISCH_TAC `&0 <= c3` THEN REAL_ARITH_TAC; UNDISCH_TAC `&1 / &2 <= sqrt(&1 - dd)` THEN
          REAL_ARITH_TAC];
        EXPAND_TAC "m" THEN UNDISCH_TAC `&0 <= A0 + &4 - p3_std_dist g0 qz` THEN REAL_ARITH_TAC]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real^3` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC))) THEN
  SUBGOAL_THEN `p3_std_dist g0 v <= m` ASSUME_TAC THENL [UNDISCH_TAC `p3_std_dist g0 v < m` THEN
    REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^3. p3_std_dist g0 y < m + &1 ==> y IN Sd` ASSUME_TAC THENL
   [X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `p3_std_dist g0 y < m + &1` THEN UNDISCH_TAC `m + &1 < inv dd` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `j = 0 \/ j = 1 \/ j = 2` MP_TAC THENL
   [UNDISCH_TAC `(j:num) <= 2` THEN ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN CONV_TAC NUM_REDUCE_CONV THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `C0 * inv(hT pow 2) pow 2`;
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `C1 * inv(hT pow 2) pow 3`;
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `C2 * inv(hT pow 2) pow 4`] THEN
  (CONJ_TAC THENL
    [FIRST_X_ASSUM(fun th -> MATCH_MP_TAC th THEN
       MAP_EVERY EXISTS_TAC [`hs_top (hs:(A)rfs_history) k`; `S:real^3->bool`;
                             `Sd:real^3->bool`] THEN
       ASM_REWRITE_TAC[] THEN NO_TAC);
     MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
      [REAL_ARITH_TAC;
       MATCH_MP_TAC REAL_POW_LE THEN MATCH_MP_TAC REAL_LE_INV THEN
       REWRITE_TAC[REAL_LE_POW_2]]]));;


(* ------------------------------------------------------------------------- *)
(* A region W of a view, open at its start time a and                        *)
(* persisting over (a,b], read at a in the restricted atlas at b (the region *)
(* family p2c_vfam V W b at s = a): its local representatives are pullbacks *)
(* of the slice a by the inverse charts (RFA_HC2_START_PULLBACK_LOCAL), the  *)
(* inverse charts are parametrisations of the slice a (RFA_HC2_START_PARAM), *)
(* and it has the derivative norms of the slice a (RFA_HC2_START_DERIV).    *)
(* The forms of P2AP_VFAM_PULLBACK_LOCAL, P2AP_VFAM_PARAM, P2AP_VFAM_DERIV   *)
(* (pc_p2a_par, a < s) at s = a, from the identity diffeo of the start time  *)
(* (conjunct 5 of p2c_regular_view).                                         *)
(* ------------------------------------------------------------------------- *)

let RFA_HC2_START_PULLBACK_LOCAL = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    W a b U (phi:A->real^3) z.
     smooth_manifold_atlas (rfs_vtop V a) (rfs_vatlas V a) /\
     smooth_manifold_atlas (rfs_vtop V b) (rfs_vatlas V b) /\
     open_in (rfs_vtop V a) W /\ open_in (rfs_vtop V b) W /\ a < b /\
     mfd_diffeo (rfs_vtop V a) (rfs_vatlas V a) W (rfs_vtop V b) (rfs_vatlas V b) W
                (\y:A. y) (\y. y) /\
     (U,phi) IN rfs_vatlas V b /\ z IN IMAGE phi (U INTER W)
     ==> metric_local (restrict_atlas (rfs_vatlas V b) W) (U INTER W,phi)
                      (p2c_vfam V W b a) z =
         rfs_pullback (rfs_vatlas V a) (chart_inv (U,phi)) (rfs_vmetric V a) z`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `y:A` (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC) o
                REWRITE_RULE[IN_IMAGE]) THEN
  SUBGOAL_THEN `(y:A) IN topspace(rfs_vtop (V:(real->A topology)#
                  (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) a)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `(y:A) IN U INTER W` THEN REWRITE_TAC[IN_INTER] THEN
    ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) a`;
                 `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) a`; `y:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `chart_at (rfs_vatlas (V:(real->A topology)#
                  (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) a) (y:A)`
         PAIR_SURJECTIVE) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`U':A->bool`; `psi:A->real^3`] THEN
  DISCH_THEN(LABEL_TAC "ch") THEN USE_THEN "ch" SUBST1_TAC THEN
  REWRITE_TAC[FST] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(a:real = b)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[p2c_vfam] THEN REWRITE_TAC[ETA_AX] THEN
  MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) b`;
                 `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) b`; `U:A->bool`; `phi:A->real^3`;
                 `W:A->bool`;
                 `mfd_pullback_metric (rfs_vatlas (V:(real->A topology)#
                    (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b)
                    (rfs_vatlas V a) (\y:A. y) (rfs_vmetric V a)`; `y:A`]
         METRIC_LOCAL_RESTRICT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) b`;
                 `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) b`; `W:A->bool`;
                 `rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) a`;
                 `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) a`; `W:A->bool`;
                 `\y:A. y`; `\y:A. y`;
                 `rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                 (real->A->real^3^3)) a`;
                 `U:A->bool`; `phi:A->real^3`; `U':A->bool`; `psi:A->real^3`; `y:A`]
         P2C_PULLBACK_METRIC_LOCAL_W) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC MFD_DIFFEO_SYM THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `(y:A) IN U INTER W` THEN SET_TAC[]];
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[rfs_pullback] THEN
  MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) b`;
                 `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) b`; `U:A->bool`; `phi:A->real^3`;
                 `W:A->bool`; `y:A`] MFDR_CHART_INV_RESTRICT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  USE_THEN "ch" SUBST1_TAC THEN REWRITE_TAC[SND] THEN
  AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[o_DEF]);;

let RFA_HC2_START_PARAM = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    W a b U (phi:A->real^3).
     smooth_manifold_atlas (rfs_vtop V a) (rfs_vatlas V a) /\
     smooth_manifold_atlas (rfs_vtop V b) (rfs_vatlas V b) /\
     open_in (rfs_vtop V b) W /\
     mfd_diffeo (rfs_vtop V a) (rfs_vatlas V a) W (rfs_vtop V b) (rfs_vatlas V b) W
                (\y:A. y) (\y. y) /\
     (U,phi) IN rfs_vatlas V b
     ==> mfd_param (rfs_vtop V a) (rfs_vatlas V a) (IMAGE phi (U INTER W))
                   (chart_inv (U,phi))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open (IMAGE (phi:A->real^3) (U INTER W))` ASSUME_TAC THENL
   [MATCH_MP_TAC MFDR_RESTRICT_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC
     [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                   (real->A->real^3^3)) b`;
      `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                     (real->A->real^3^3)) b`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MFD_PARAM_EQ THEN
  EXISTS_TAC `(\y:A. y) o chart_inv (U:A->bool,phi:A->real^3)` THEN
  ASM_REWRITE_TAC[o_THM] THEN
  MATCH_MP_TAC MFD_PARAM_COMPOSE_DIFFEO THEN
  MAP_EVERY EXISTS_TAC
   [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                 (real->A->real^3^3)) b`;
    `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                   (real->A->real^3^3)) b`;
    `W:A->bool`; `W:A->bool`; `\y:A. y`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MFD_PARAM_RESTRICT THEN
    EXISTS_TAC `IMAGE (phi:A->real^3) U` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC MFD_PARAM_CHART_INV THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC IMAGE_SUBSET THEN SET_TAC[]];
    MATCH_MP_TAC MFD_DIFFEO_SYM THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
    X_GEN_TAC `y:A` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) b`;
                   `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                  (real->A->real^3^3)) b`; `U:A->bool`; `phi:A->real^3`;
                   `W:A->bool`; `y:A`] MFDR_CHART_INV_RESTRICT) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]]);;

let RFA_HC2_START_DERIV = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    W a b l x.
     smooth_manifold_atlas (rfs_vtop V a) (rfs_vatlas V a) /\
     smooth_manifold_atlas (rfs_vtop V b) (rfs_vatlas V b) /\
     riemannian_metric (rfs_vatlas V a) (rfs_vmetric V a) /\
     open_in (rfs_vtop V a) W /\ open_in (rfs_vtop V b) W /\ a < b /\
     mfd_diffeo (rfs_vtop V a) (rfs_vatlas V a) W (rfs_vtop V b) (rfs_vatlas V b) W
                (\y:A. y) (\y. y) /\
     x IN W
     ==> rfa_rmd2 l (restrict_atlas (rfs_vatlas V b) W) (p2c_vfam V W b a) x =
         rfa_rmd2 l (rfs_vatlas V a) (rfs_vmetric V a) x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[rfa_rmd2] THEN
  MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) b`;
                 `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) b`; `W:A->bool`; `x:A`]
         MFDR_CHART_AT_RESTRICT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `U:A->bool` (X_CHOOSE_THEN `phi:A->real^3` STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[SND] THEN
  SUBGOAL_THEN `open (IMAGE (phi:A->real^3) (U INTER W)) /\ phi x IN IMAGE phi (U INTER W)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC MFDR_RESTRICT_IMAGE_OPEN THEN
      MAP_EVERY EXISTS_TAC
       [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                     (real->A->real^3^3)) b`;
        `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                       (real->A->real^3^3)) b`] THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_INTER]];
    ALL_TAC] THEN
  TRANS_TAC EQ_TRANS
   `lrm_deriv_norm2 l (rfs_pullback (rfs_vatlas V a) (chart_inv (U:A->bool,phi:A->real^3))
                                    (rfs_vmetric (V:(real->A topology)#
                                       (real->((A->bool)#(A->real^3))->bool)#
                                       (real->A->real^3^3)) a))
                    ((phi:A->real^3) x)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LRM_DERIV_NORM2_LOCAL THEN
    EXISTS_TAC `IMAGE (phi:A->real^3) (U INTER W)` THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    MATCH_MP_TAC RFA_HC2_START_PULLBACK_LOCAL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `W:A->bool`; `a:real`; `b:real`;
                 `U:A->bool`; `phi:A->real^3`] RFA_HC2_START_PARAM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`l:num`;
                 `rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) a`;
                 `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) a`;
                 `rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                 (real->A->real^3^3)) a`;
                 `IMAGE (phi:A->real^3) (U INTER W)`; `chart_inv (U:A->bool,phi:A->real^3)`;
                 `(phi:A->real^3) x`] P2AP_PULLBACK_RMD_GEN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) b`;
                 `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) b`; `U:A->bool`; `phi:A->real^3`;
                 `W:A->bool`; `x:A`] MFDR_CHART_INV_RESTRICT) THEN
  ASM_REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[rfa_rmd2]);;

(* The metric at the start of a flow smooth from a: a quadratic form of     *)
(* g t x agrees on [a,b) with a function continuous at a.                    *)

let RFA_HC2_CONT_RIGHT_LE = prove
 (`!f t0 d.
     f real_continuous (atreal t0) /\ &0 < d /\
     (!t. t0 < t /\ t < t0 + d ==> f t <= &0)
     ==> f t0 <= &0`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `&0 < (f:real->real) t0` THENL
   [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [REAL_CONTINUOUS_ATREAL]) THEN
  REWRITE_TAC[REALLIM_ATREAL] THEN
  DISCH_THEN(MP_TAC o SPEC `(f:real->real) t0`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `t0 + min e d / &2`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `t0 + min e d / &2`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  POP_ASSUM MP_TAC THEN REAL_ARITH_TAC);;

let RFA_HC2_FROM_QFORM_CONT = prove
 (`!top atlas a b (g:real->A->real^N^N) x w.
     ricci_flow_from (top,atlas) a b g /\ x IN topspace top
     ==> ?phi. phi real_continuous (atreal a) /\
               !t. a <= t /\ t < b ==> phi t = w dot (g t x ** w)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ricci_flow_from] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ext"))) ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [ricci_flow_on]) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`]
         CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  USE_THEN "ext" (fun th -> MP_TAC(MATCH_MP th
    (ASSUME `chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A) IN atlas`))) THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` (X_CHOOSE_THEN
    `FF:real^(1,N)finite_sum->real^(N,N)finite_prod` STRIP_ASSUME_TAC)) THEN
  ABBREV_TAC `y0 = SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)) x` THEN
  SUBGOAL_THEN `y0 IN IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)))
                             (FST(chart_at atlas x))` ASSUME_TAC THENL
   [EXPAND_TAC "y0" THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  EXISTS_TAC
   `\r. drop((\m:real^(N,N)finite_prod. lift(w dot ((matrify m:real^N^N) ** w)))
             ((FF:real^(1,N)finite_sum->real^(N,N)finite_prod)
              (pastecart (lift r) y0)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC RFA_TSLICE_CONTINUOUS THEN
    EXISTS_TAC
     `interval(lift(a - e),lift b) PCROSS
      IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)))
            (FST(chart_at atlas x))` THEN
    ASM_REWRITE_TAC[LRG_LINEAR_MATRIFY_DOT] THEN CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_PCROSS THEN REWRITE_TAC[OPEN_INTERVAL] THEN
      MATCH_MP_TAC RFB_ATLAS_IMAGE_OPEN THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  X_GEN_TAC `t:real` THEN STRIP_TAC THEN REWRITE_TAC[LIFT_DROP] THEN
  SUBGOAL_THEN
   `(FF:real^(1,N)finite_sum->real^(N,N)finite_prod) (pastecart (lift t) y0) =
    vectorize(metric_local atlas (chart_at atlas (x:A)) ((g:real->A->real^N^N) t) y0)`
  SUBST1_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[MATRIFY_VECTORIZE] THEN EXPAND_TAC "y0" THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(g:real->A->real^N^N) t`; `x:A`] METRIC_LOCAL_AT) THEN
  ASM_SIMP_TAC[]);;

(* MT Claim 8.8 down to the start time a of a region open at a: the metric   *)
(* comparison of P2AP_METRIC_COMPARE for a < s, and the limit s -> a+.       *)

let RFA_HC2_START_COMPARE = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    W a b K y w.
     p2c_regular_view V /\ a < b /\ open_in (rfs_vtop V a) W /\ rfs_persists V W a b /\
     &0 <= K /\ (!t z. a < t /\ t <= b /\ z IN W ==> p3_vrm V t z <= K) /\ y IN W
     ==> w dot (p2c_vfam V W b a y ** w) <=
         exp(&4 * K * (b - a)) * (w dot (p2c_vfam V W b b y ** w)) /\
         w dot (p2c_vfam V W b b y ** w) <=
         exp(&4 * K * (b - a)) * (w dot (p2c_vfam V W b a y ** w))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `p2a_region (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) W a b /\ p2a_svs V`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[RFA_HC2_REGULAR_REGION; RFA_HC2_REGULAR_SVS]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. a < s /\ s <= b
        ==> w dot (p2c_vfam (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) W b s y ** w) <=
            exp(&4 * K * (b - s)) * (w dot (p2c_vfam V W b b y ** w)) /\
            w dot (p2c_vfam V W b b y ** w) <=
            exp(&4 * K * (b - s)) * (w dot (p2c_vfam V W b s y ** w))`
  (LABEL_TAC "cmp") THENL
   [GEN_TAC THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                      (real->A->real^3^3)`; `W:A->bool`; `a:real`; `b:real`; `K:real`;
                   `s:real`; `y:A`; `w:real^3`] P2AP_METRIC_COMPARE) THEN
    ASM_REWRITE_TAC[P2AP_RMETRIC_VFAM];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `W:A->bool`; `a:real`; `b:real`]
                P2C_REGULAR_VFLOW_FROM) THEN
  ASM_REWRITE_TAC[p2c_vflow_from] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(y:A) IN topspace(subtopology (rfs_vtop (V:(real->A topology)#
                        (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b) W)`
  ASSUME_TAC THENL
   [REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER] THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `rfs_persists (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                 (real->A->real^3^3)) W a b` THEN
    REWRITE_TAC[CONJUNCT2(CONJUNCT2(SPEC_ALL P2C_VIEW_EXPAND))] THEN
    DISCH_THEN(MP_TAC o SPEC `b:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o MATCH_MP OPEN_IN_SUBSET o CONJUNCT2) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`subtopology (rfs_vtop (V:(real->A topology)#
                    (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b) W`;
                 `restrict_atlas (rfs_vatlas (V:(real->A topology)#
                    (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b) W`;
                 `a:real`; `b:real`;
                 `p2c_vfam (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) W b`; `y:A`; `w:real^3`]
                RFA_HC2_FROM_QFORM_CONT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `phi:real->real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `smooth_manifold_atlas (subtopology (rfs_vtop V b) W)
      (restrict_atlas (rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                    (real->A->real^3^3)) b) W)`
  ASSUME_TAC THENL [ASM_MESON_TAC[ricci_flow_from; ricci_flow_on]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. a < s /\ s <= b
        ==> &0 <= w dot (p2c_vfam (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) W b s y ** w)`
  (LABEL_TAC "nn") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC P2AP_QFORM_NONNEG THEN
    MAP_EVERY EXISTS_TAC
     [`subtopology (rfs_vtop (V:(real->A topology)#
         (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b) W`;
      `restrict_atlas (rfs_vatlas (V:(real->A topology)#
         (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b) W`] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`subtopology (rfs_vtop (V:(real->A topology)#
                      (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b) W`;
                   `restrict_atlas (rfs_vatlas (V:(real->A topology)#
                      (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b) W`;
                   `a:real`; `b:real`;
                   `p2c_vfam (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) W b`; `s:real`] P2AP_UPTO_RIEM) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [MATCH_MP_TAC P2AP_REGION_UPTO THEN ASM_REWRITE_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s. a <= s /\ s <= b ==> exp(&4 * K * (b - s)) <= exp(&4 * K * (b - a))`
  (LABEL_TAC "em") THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_EXP_MONO_LE] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `fb = w dot (p2c_vfam (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                    (real->A->real^3^3)) W b b y ** w)` THEN
  SUBGOAL_THEN `&0 <= fb` ASSUME_TAC THENL
   [EXPAND_TAC "fb" THEN USE_THEN "nn" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `(phi:real->real) a =
    w dot (p2c_vfam (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                      (real->A->real^3^3)) W b a y ** w)`
  (SUBST1_TAC o SYM) THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`\s. (phi:real->real) s - exp(&4 * K * (b - a)) * fb`; `a:real`; `b - a`]
                  RFA_HC2_CONT_RIGHT_LE) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC REAL_CONTINUOUS_SUB THEN ASM_REWRITE_TAC[REAL_CONTINUOUS_CONST];
        ASM_REAL_ARITH_TAC;
        X_GEN_TAC `s:real` THEN STRIP_TAC THEN
        SUBGOAL_THEN
         `(phi:real->real) s =
          w dot (p2c_vfam (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                            (real->A->real^3^3)) W b s y ** w)`
        SUBST1_TAC THENL
         [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        USE_THEN "cmp" (MP_TAC o SPEC `s:real`) THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN(MP_TAC o CONJUNCT1)] THEN
        ASM_REWRITE_TAC[] THEN
        USE_THEN "em" (MP_TAC o SPEC `s:real`) THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
        SUBGOAL_THEN `exp(&4 * K * (b - s)) * fb <= exp(&4 * K * (b - a)) * fb` MP_TAC THENL
         [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]; REAL_ARITH_TAC]];
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\s. fb - exp(&4 * K * (b - a)) * (phi:real->real) s`; `a:real`; `b - a`]
                RFA_HC2_CONT_RIGHT_LE) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_CONTINUOUS_SUB THEN REWRITE_TAC[REAL_CONTINUOUS_CONST] THEN
      MATCH_MP_TAC REAL_CONTINUOUS_LMUL THEN ASM_REWRITE_TAC[ETA_AX];
      ASM_REAL_ARITH_TAC;
      X_GEN_TAC `s:real` THEN STRIP_TAC THEN
      SUBGOAL_THEN
       `(phi:real->real) s =
        w dot (p2c_vfam (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                          (real->A->real^3^3)) W b s y ** w)`
      SUBST1_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      USE_THEN "cmp" (MP_TAC o SPEC `s:real`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN(MP_TAC o CONJUNCT2)] THEN
      ASM_REWRITE_TAC[] THEN
      USE_THEN "em" (MP_TAC o SPEC `s:real`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
      USE_THEN "nn" (MP_TAC o SPEC `s:real`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
      ABBREV_TAC `fs = w dot (p2c_vfam (V:(real->A topology)#
                     (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) W b s y ** w)` THEN
      SUBGOAL_THEN `exp(&4 * K * (b - s)) * fs <= exp(&4 * K * (b - a)) * fs` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]; REAL_ARITH_TAC]];
    REAL_ARITH_TAC]);;

(* A C^1 curve of a manifold that stays in an open W is a C^1 curve of the  *)
(* restricted manifold (the statement of P2CO_C1_CURVE_SUBTOP of             *)
(* pc_p2c_lrestrict, which is outside the load closure of this unit; proved  *)
(* again here).                                                              *)

let RFA_HC2_C1_CURVE_SUBTOP = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) W (gamma:real->A) a b.
     mfd_c1_curve (top,atlas) gamma a b /\
     (!t. t IN real_interval[a,b] ==> gamma t IN W)
     ==> mfd_c1_curve (subtopology top W,restrict_atlas atlas W) gamma a b`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mfd_c1_curve; CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; TOPSPACE_EUCLIDEANREAL; INTER_UNIV] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[FORALL_PAIR_THM; IN_RESTRICT_ATLAS] THEN
  MAP_EVERY X_GEN_TAC [`UW:A->bool`; `phi:A->real^N`] THEN
  DISCH_THEN(X_CHOOSE_THEN `U:A->bool` (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC)) THEN
  REWRITE_TAC[FST; SND] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(U:A->bool,phi:A->real^N)`) THEN ASM_REWRITE_TAC[FST; SND] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INTER] THEN X_GEN_TAC `s:real^1` THEN
  ASM_CASES_TAC `(s:real^1) IN interval[lift a,lift b]` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(gamma:real->A) (drop s) IN W` (fun th -> REWRITE_TAC[th]) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  UNDISCH_TAC `(s:real^1) IN interval[lift a,lift b]` THEN
  REWRITE_TAC[IN_INTERVAL_1; IN_REAL_INTERVAL; LIFT_DROP]);;

(* Curves of a region W at its start time a: a C^1 curve of the restricted   *)
(* manifold at b is a C^1 curve of the slice a, and its length there is its *)
(* length for the region family at a (P2B9S_PB_LENGTH with the identity).   *)

let RFA_HC2_REGION_LENGTH_START = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    W a b (gam:real->A) c0 c1.
     smooth_manifold_atlas (rfs_vtop V a) (rfs_vatlas V a) /\
     smooth_manifold_atlas (rfs_vtop V b) (rfs_vatlas V b) /\
     riemannian_metric (rfs_vatlas V a) (rfs_vmetric V a) /\
     open_in (rfs_vtop V b) W /\ a < b /\
     mfd_diffeo (rfs_vtop V a) (rfs_vatlas V a) W (rfs_vtop V b) (rfs_vatlas V b) W
                (\y:A. y) (\y. y) /\
     mfd_c1_curve (subtopology (rfs_vtop V b) W,restrict_atlas (rfs_vatlas V b) W)
                  gam c0 c1 /\ c0 < c1
     ==> mfd_c1_curve (rfs_vtop V a,rfs_vatlas V a) gam c0 c1 /\
         mfd_length (rfs_vatlas V a) (rfs_vmetric V a) gam c0 c1 =
         mfd_length (restrict_atlas (rfs_vatlas V b) W) (p2c_vfam V W b a) gam c0 c1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) b`;
                 `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) b`; `W:A->bool`; `gam:real->A`;
                 `c0:real`; `c1:real`] P2AP_C1_CURVE_RESTRICT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) b`;
                 `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) b`;
                 `rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) a`;
                 `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) a`;
                 `W:A->bool`; `W:A->bool`; `\y:A. y`; `\y:A. y`;
                 `rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                 (real->A->real^3^3)) a`;
                 `gam:real->A`; `c0:real`; `c1:real`] P2B9S_PB_LENGTH) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MFD_DIFFEO_SYM THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\y:A. y) o (gam:real->A) = gam` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(a:real = b)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[p2c_vfam; ETA_AX] THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC P2AP_LENGTH_RESTRICT THEN
  EXISTS_TAC `rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                          (real->A->real^3^3)) b` THEN
  ASM_REWRITE_TAC[]);;

let RFA_HC2_BALL_CURVE_IN = prove
 (`!top atlas (g:A->real^N^N) y p r.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     p IN mfd_ball (top,atlas) g y r
     ==> ?gam. mfd_c1_curve (top,atlas) gam (&0) (&1) /\ gam(&0) = y /\ gam(&1) = p /\
               mfd_length atlas g gam (&0) (&1) < r /\
               (!t. t IN real_interval[&0,&1] ==> gam t IN mfd_ball (top,atlas) g y r)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `y:A`; `p:A`; `r:real`] P2C_BALL_CURVE) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `gam:real->A` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `t:real` THEN
  REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
  SUBGOAL_THEN `mfd_c1_curve (top,atlas:((A->bool)#(A->real^N))->bool) (gam:real->A) (&0) t`
  ASSUME_TAC THENL
   [MATCH_MP_TAC GRGD_C1_CURVE_SUBINTERVAL THEN
    MAP_EVERY EXISTS_TAC [`&0`; `&1`] THEN ASM_REWRITE_TAC[REAL_LE_REFL];
    ALL_TAC] THEN
  REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o MATCH_MP MFD_C1_CURVE_JOINABLE) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `mfd_length atlas (g:A->real^N^N) (gam:real->A) (&0) t` THEN CONJ_TAC THENL
   [SUBGOAL_THEN `(y:A) = gam(&0)` SUBST1_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC MFD_DIST_LE_LENGTH THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `mfd_length atlas (g:A->real^N^N) (gam:real->A) (&0) (&1)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC APX_LENGTH_PREFIX_LE THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[]]);;

(* Distances at the start time a from the centre y of a region W that is a  *)
(* g(b)-ball of radius rho: at most lam rho if g(a) <= lam^2 g(b) on W.      *)

let RFA_HC2_START_DIST = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    W a b y p rho lam.
     smooth_manifold_atlas (rfs_vtop V a) (rfs_vatlas V a) /\
     smooth_manifold_atlas (rfs_vtop V b) (rfs_vatlas V b) /\
     riemannian_metric (rfs_vatlas V a) (rfs_vmetric V a) /\
     riemannian_metric (rfs_vatlas V b) (rfs_vmetric V b) /\
     open_in (rfs_vtop V b) W /\ a < b /\
     mfd_diffeo (rfs_vtop V a) (rfs_vatlas V a) W (rfs_vtop V b) (rfs_vatlas V b) W
                (\y:A. y) (\y. y) /\
     riemannian_metric (restrict_atlas (rfs_vatlas V b) W) (p2c_vfam V W b a) /\
     mfd_ball (rfs_vtop V b,rfs_vatlas V b) (rfs_vmetric V b) y rho SUBSET W /\ &0 < lam /\
     (!z v. z IN W
            ==> v dot (p2c_vfam V W b a z ** v) <=
                lam pow 2 * (v dot (p2c_vfam V W b b z ** v))) /\
     p IN mfd_ball (rfs_vtop V b,rfs_vatlas V b) (rfs_vmetric V b) y rho
     ==> mfd_joinable (rfs_vtop V a,rfs_vatlas V a) y p /\
         mfd_dist (rfs_vtop V a,rfs_vatlas V a) (rfs_vmetric V a) y p <= lam * rho`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) b`;
                 `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) b`;
                 `rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                 (real->A->real^3^3)) b`;
                 `y:A`; `p:A`; `rho:real`] RFA_HC2_BALL_CURVE_IN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `gam:real->A` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!t. t IN real_interval[&0,&1] ==> (gam:real->A) t IN W` (LABEL_TAC "inW")
  THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_c1_curve (subtopology (rfs_vtop V b) W,
                  restrict_atlas (rfs_vatlas (V:(real->A topology)#
                    (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b) W)
                 (gam:real->A) (&0) (&1)` ASSUME_TAC THENL
   [MATCH_MP_TAC RFA_HC2_C1_CURVE_SUBTOP THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "inW" ACCEPT_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `W:A->bool`; `a:real`; `b:real`; `gam:real->A`;
                 `&0`; `&1`] RFA_HC2_REGION_LENGTH_START) THEN
  ASM_REWRITE_TAC[REAL_LT_01] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `smooth_manifold_atlas (subtopology (rfs_vtop V b) W)
      (restrict_atlas (rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                    (real->A->real^3^3)) b) W)` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MANIFOLD_ATLAS_RESTRICT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `riemannian_metric (restrict_atlas (rfs_vatlas (V:(real->A topology)#
      (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b) W) (p2c_vfam V W b b)`
  ASSUME_TAC THENL
   [REWRITE_TAC[p2c_vfam; ETA_AX] THEN MATCH_MP_TAC RIEMANNIAN_METRIC_RESTRICT THEN
    EXISTS_TAC `rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                            (real->A->real^3^3)) b` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`subtopology (rfs_vtop (V:(real->A topology)#
                    (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b) W`;
                 `restrict_atlas (rfs_vatlas (V:(real->A topology)#
                    (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b) W`;
                 `p2c_vfam (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) W b b`;
                 `p2c_vfam (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) W b a`;
                 `lam pow 2`; `gam:real->A`; `&0`; `&1`] MFD_LENGTH_METRIC_COMPARE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_LE_POW_2] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN USE_THEN "inW" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[IN_REAL_INTERVAL];
    ALL_TAC] THEN
  ASM_SIMP_TAC[POW_2_SQRT; REAL_LT_IMP_LE] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `mfd_length (restrict_atlas (rfs_vatlas V b) W)
      (p2c_vfam (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                   (real->A->real^3^3)) W b b) gam (&0) (&1) =
    mfd_length (rfs_vatlas V b) (rfs_vmetric V b) gam (&0) (&1)`
  ASSUME_TAC THENL
   [REWRITE_TAC[p2c_vfam; ETA_AX] THEN MATCH_MP_TAC P2AP_LENGTH_RESTRICT THEN
    EXISTS_TAC `rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                            (real->A->real^3^3)) b` THEN
    ASM_REWRITE_TAC[REAL_LT_01];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:A) = gam(&0) /\ (p:A) = gam(&1)` (CONJUNCTS_THEN SUBST1_TAC) THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL [MATCH_MP_TAC MFD_C1_CURVE_JOINABLE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `mfd_length (rfs_vatlas V a)
                (rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) a) gam (&0) (&1)` THEN
  CONJ_TAC THENL [MATCH_MP_TAC MFD_DIST_LE_LENGTH THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `lam * mfd_length (rfs_vatlas V b)
                      (rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                      (real->A->real^3^3)) b) gam (&0) (&1)` THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]);;


(* ------------------------------------------------------------------------- *)
(* Shi's estimate with initial bounds in scale-invariant form:               *)
(* RFA_P2_THM_3_29 at (l,K,r,tau) for the rescaled flow q g(a + s / q)       *)
(* (P2BK_RICCI_FLOW_FROM_AFFINE).  If abs Rm <= K q on B(x,a,r / sqrt q)     *)
(* over [a,b), abs(nabla^j Rm)^2 <= K q^(j+2) there at a for j <= l, and     *)
(* q (b - a) <= tau, then abs(nabla^l Rm)^2 <= Cl q^(l+2) at x on [a,b).     *)
(* ------------------------------------------------------------------------- *)

let RFA_HC2_SHI_INIT_SCALED = prove
 (`!l K r tau.
     &0 < K /\ &0 < r /\ &0 < tau
     ==> ?Cl. &0 < Cl /\
              !top atlas a b (g:real->A->real^3^3) x q.
                hausdorff_space top /\ ricci_flow_from (top,atlas) a b g /\
                &0 < q /\ q * (b - a) <= tau /\ x IN topspace top /\
                compact_in top (top closure_of mfd_ball (top,atlas) (g a) x (r / sqrt q)) /\
                (!t y. a <= t /\ t < b /\ y IN mfd_ball (top,atlas) (g a) x (r / sqrt q)
                       ==> mfd_rm_norm atlas (g t) y <= K * q) /\
                (!j y. j <= l /\ y IN mfd_ball (top,atlas) (g a) x (r / sqrt q)
                       ==> rfa_rmd2 j atlas (g a) y <= K * q pow (j + 2))
                ==> !t. a <= t /\ t < b ==> rfa_rmd2 l atlas (g t) x <= Cl * q pow (l + 2)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `(:A)` RFA_P2_THM_3_29) THEN REWRITE_TAC[P2_THM_3_29_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPECL [`l:num`; `K:real`; `r:real`; `tau:real`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `C1:real` (LABEL_TAC "shi")) THEN
  EXISTS_TAC `max C1 (&1)` THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC
   [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
    `g:real->A->real^3^3`; `x:A`; `q:real`] THEN
  STRIP_TAC THEN X_GEN_TAC `t:real` THEN STRIP_TAC THEN
  SUBGOAL_THEN `smooth_manifold_atlas (top:A topology) (atlas:((A->bool)#(A->real^3))->bool) /\
                a < b` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[ricci_flow_from; ricci_flow_on]; ALL_TAC] THEN
  SUBGOAL_THEN `!s. a <= s /\ s < b ==> riemannian_metric atlas ((g:real->A->real^3^3) s)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `ricci_flow_from (top,atlas) a b (g:real->A->real^3^3)` THEN
    REWRITE_TAC[ricci_flow_from; ricci_flow_on] THEN STRIP_TAC THEN
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN ASM_CASES_TAC `s:real = a` THEN
    ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `riemannian_metric atlas ((g:real->A->real^3^3) a)` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!rr. mfd_ball (top,atlas) (\z. q %% (g:real->A->real^3^3) a z) x rr =
                     mfd_ball (top,atlas) (g a) x (rr / sqrt q)` ASSUME_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `(g:real->A->real^3^3) a`; `q:real`; `x:A`; `rr:real`] MFD_BALL_SCALE) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `gs = \s x. q %% (g:real->A->real^3^3) (a + s / q) x` THEN
  SUBGOAL_THEN `ricci_flow_from (top,atlas) (&0) (q * (b - a)) (gs:real->A->real^3^3)`
  ASSUME_TAC THENL
   [EXPAND_TAC "gs" THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`;
                   `b:real`; `g:real->A->real^3^3`; `a:real`; `q:real`]
                  P2BK_RICCI_FLOW_FROM_AFFINE) THEN
    ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_MUL_RZERO];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s. (gs:real->A->real^3^3) s = \z. q %% g (a + s / q) z` ASSUME_TAC THENL
   [EXPAND_TAC "gs" THEN REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(gs:real->A->real^3^3) (&0) = \z. q %% (g:real->A->real^3^3) a z`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[real_div; REAL_MUL_LZERO; REAL_ADD_RID]; ALL_TAC] THEN
  REMOVE_THEN "shi" (MP_TAC o SPECL
   [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `&0`; `q * (b - a)`;
    `gs:real->A->real^3^3`; `x:A`]) THEN
  ASM_REWRITE_TAC[REAL_SUB_RZERO] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MAP_EVERY X_GEN_TAC [`s:real`; `z:A`] THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `a <= a + s / q /\ a + s / q < b` STRIP_ASSUME_TAC THENL
       [CONJ_TAC THENL
         [MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> a <= a + x`) THEN
          MATCH_MP_TAC REAL_LE_DIV THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
          MATCH_MP_TAC(REAL_ARITH `x < b - a ==> a + x < b`) THEN
          ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN ASM_REAL_ARITH_TAC];
        ALL_TAC] THEN
      SUBGOAL_THEN `(z:A) IN topspace top` ASSUME_TAC THENL
       [UNDISCH_TAC `(z:A) IN mfd_ball (top,atlas) ((g:real->A->real^3^3) a) x (r / sqrt q)` THEN
        REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN STRIP_TAC THEN
        FIRST_ASSUM(MP_TAC o MATCH_MP MFD_JOINABLE_IN_TOPSPACE) THEN SIMP_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `K = (K * q) / q` SUBST1_TAC THENL
       [UNDISCH_TAC `&0 < q` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
      MATCH_MP_TAC RFA_MFD_RM_NORM_CMUL_LE THEN EXISTS_TAC `top:A topology` THEN
      ASM_SIMP_TAC[DIMINDEX_3; ARITH] THEN REWRITE_TAC[ETA_AX] THEN ASM_SIMP_TAC[];
      MAP_EVERY X_GEN_TAC [`j:num`; `z:A`] THEN STRIP_TAC THEN
      SUBGOAL_THEN `(z:A) IN topspace top` ASSUME_TAC THENL
       [UNDISCH_TAC `(z:A) IN mfd_ball (top,atlas) ((g:real->A->real^3^3) a) x (r / sqrt q)` THEN
        REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN STRIP_TAC THEN
        FIRST_ASSUM(MP_TAC o MATCH_MP MFD_JOINABLE_IN_TOPSPACE) THEN SIMP_TAC[];
        ALL_TAC] THEN
      REWRITE_TAC[GSYM rfa_rmd2] THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                     `(g:real->A->real^3^3) a`; `q:real`; `j:num`; `z:A`]
                    RFA_HC2_RMD2_CMUL) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`j:num`; `z:A`] o check (fun th ->
        is_forall(concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "rfa_rmd2")) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      SUBGOAL_THEN `&0 < q pow (j + 2)` ASSUME_TAC THENL
       [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv q pow (j + 2) * (K * q pow (j + 2))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_POW_LE; REAL_LE_INV; REAL_LT_IMP_LE];
        REWRITE_TAC[REAL_POW_INV] THEN MATCH_MP_TAC REAL_EQ_IMP_LE THEN
        UNDISCH_TAC `&0 < q pow (j + 2)` THEN CONV_TAC REAL_FIELD]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`l:num`; `q * (t - a)`; `x:A`]) THEN
  REWRITE_TAC[LE_REFL; GSYM rfa_rmd2] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REAL_ARITH_TAC;
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                     `(g:real->A->real^3^3) a`; `x:A`; `(r / &2) / sqrt q`]
                    MFD_CENTRE_IN_BALL) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      MATCH_MP_TAC REAL_LT_DIV THEN ASM_SIMP_TAC[SQRT_POS_LT] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `a + (q * (t - a)) / q = t` SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < q` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `(g:real->A->real^3^3) t`; `q:real`; `l:num`; `x:A`] RFA_HC2_RMD2_CMUL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  SPEC_TAC(`rfa_rmd2 l atlas ((g:real->A->real^3^3) t) x`,`D:real`) THEN GEN_TAC THEN
  SUBGOAL_THEN `&0 < q pow (l + 2)` MP_TAC THENL [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  REWRITE_TAC[REAL_POW_INV] THEN SPEC_TAC(`q pow (l + 2)`,`p:real`) THEN
  GEN_TAC THEN DISCH_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `C1 * p:real` THEN CONJ_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH
     `D = p * (inv p * D) /\ p * (inv p * D) <= p * C1 ==> D <= C1 * p`) THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `&0 < p` THEN CONV_TAC REAL_FIELD;
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]];
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN REAL_ARITH_TAC]);;

(* The gradient bound |grad R| <= max(C,2) R^(3/2) at points of a history   *)
(* before t with R >= rp(t)^-2 (the canonical neighbourhood assumption and   *)
(* P2C_CANON_DERIV; the gradient form of RFA_HC2_HIST_DB, same proof).       *)

let RFA_HC2_HIST_GRAD = prove
 (`?eps1. &0 < eps1 /\
     !C eps (rp:real->real) (hs:(A)rfs_history) t u w.
       &1 < C /\ &0 < eps /\ eps <= eps1 /\ p2c_regular_view (rfs_view hs) /\
       (!s. &0 <= s ==> &0 < rp s) /\ (!s t. &0 <= s /\ s <= t ==> rp t <= rp s) /\
       rfs_canonical_assumption (rfs_trunc (rfs_view hs) t) C eps rp /\
       &0 <= u /\ u < t /\ w IN topspace(rfs_top_at hs u) /\
       inv(rp t pow 2) <= rfs_vscalar (rfs_view hs) u w
       ==> sqrt(rfs_scalar_grad2 (rfs_vatlas (rfs_view hs) u) (rfs_vmetric (rfs_view hs) u) w)
           <= max C (&2) * rfs_vscalar (rfs_view hs) u w *
              sqrt(rfs_vscalar (rfs_view hs) u w)`,
  MP_TAC(ISPEC `(:A)` P2C_CANON_DERIV) THEN REWRITE_TAC[P2C_CANON_DERIV_STATEMENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `e1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "cd"))) THEN
  EXISTS_TAC `e1:real` THEN ASM_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `inv((rp:real->real) u pow 2) <= inv(rp (t:real) pow 2)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_POW_LE2 THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_IMP_LE THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `?U. rfs_canonical_nbhd (rfs_top_at hs u,rfs_atlas_at hs u)
                      (rfs_metric_at (hs:(A)rfs_history) u) C eps (w:A) U`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_canonical_assumption (rfs_trunc (rfs_view (hs:(A)rfs_history)) t)
                   C eps rp` THEN
    REWRITE_TAC[rfs_canonical_assumption; rfs_trunc; rfs_view] THEN
    DISCH_THEN(MP_TAC o SPECL [`u:real`; `w:A`]) THEN ASM_REWRITE_TAC[] THEN
    ANTS_TAC THENL
     [UNDISCH_TAC `inv((rp:real->real) t pow 2) <=
                    rfs_vscalar (rfs_view (hs:(A)rfs_history)) u (w:A)` THEN
      REWRITE_TAC[rfs_vscalar; rfs_view] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[rfs_strong_canonical; rfs_canonical_nbhd; rfs_strong_neck;
                rfs_evolving_neck] THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`rfs_view (hs:(A)rfs_history)`; `u:real`; `w:A`] P2C_REGULAR_SLICE) THEN
  ASM_REWRITE_TAC[rfs_view; rfs_vtop; rfs_vatlas; rfs_vmetric; rfs_vscalar] THEN STRIP_TAC THEN
  REMOVE_THEN "cd" (MP_TAC o SPECL [`rfs_top_at (hs:(A)rfs_history) u`; `rfs_atlas_at (hs:(A)rfs_history) u`;
    `rfs_metric_at (hs:(A)rfs_history) u`; `C:real`; `eps:real`; `w:A`; `U:A->bool`]) THEN
  ASM_REWRITE_TAC[] THEN SIMP_TAC[]);;


(* Shi with initial bounds on a region of a regular view that starts at a   *)
(* (open there) and is the tt-ball B = B(y,tt,rho): abs Rm <= K q on B over *)
(* (a,tt], abs(nabla^j Rm)^2 <= K q^(j+2) on B in the slice a for j <= l,   *)
(* q (tt - a) <= tau, and the Shi ball of radius r / sqrt q at a well inside *)
(* B (4 exp(2 K tau) r / sqrt q <= rho; MT Claim 8.8 down to a,              *)
(* RFA_HC2_START_COMPARE, and P2AP_BALL_COMPACT): then abs(nabla^l Rm)^2 <=   *)
(* Cl q^(l+2) at (y,tt) (RFA_HC2_SHI_INIT_SCALED on [a,tt), and the limit at *)
(* the top time, RFA_UPTO_RMD_LIMIT).  The initial-data form of              *)
(* RFA_HC2_REGION_SHI.                                                       *)

let RFA_HC2_REGION_SHI_INIT = prove
 (`!l K r tau. &0 < K /\ &0 < r /\ &0 < tau
     ==> ?Cl. &0 < Cl /\
           !(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
               (real->A->real^3^3)) a tt y q rho.
             p2c_regular_view V /\ y IN topspace(rfs_vtop V tt) /\ &0 < q /\ a < tt /\
             q * (tt - a) <= tau /\ &4 * exp(&2 * K * tau) * r / sqrt q <= rho /\
             open_in (rfs_vtop V a) (rfs_vball V tt y rho) /\
             rfs_persists V (rfs_vball V tt y rho) a tt /\
             compact_in (rfs_vtop V tt) ((rfs_vtop V tt) closure_of (rfs_vball V tt y rho)) /\
             (!s z. a < s /\ s <= tt /\ z IN rfs_vball V tt y rho
                    ==> p3_vrm V s z <= K * q) /\
             (!j z. j <= l /\ z IN rfs_vball V tt y rho
                    ==> rfa_rmd2 j (rfs_vatlas V a) (rfs_vmetric V a) z <= K * q pow (j + 2))
             ==> rfa_rmd2 l (rfs_vatlas V tt) (rfs_vmetric V tt) y <= Cl * q pow (l + 2)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`l:num`; `max K (sqrt K)`; `r:real`; `tau:real`]
               (INST_TYPE [`:A`,`:A`] RFA_HC2_SHI_INIT_SCALED)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Cl:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "shi"))) THEN
  EXISTS_TAC `Cl:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC
   [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
    `a:real`; `tt:real`; `y:A`; `q:real`; `rho:real`] THEN
  REWRITE_TAC[CONJUNCT1(CONJUNCT2(SPEC_ALL P2C_VIEW_EXPAND))] THEN STRIP_TAC THEN
  ABBREV_TAC `W = mfd_ball (rfs_vtop V tt,rfs_vatlas V tt)
                           (rfs_vmetric (V:(real->A topology)#
                              (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt)
                           y rho` THEN
  SUBGOAL_THEN `p2a_svs (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                           (real->A->real^3^3))` ASSUME_TAC THENL
   [MATCH_MP_TAC RFA_HC2_REGULAR_SVS THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `tt:real`; `y:A`] P2AP_SLICE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < sqrt q /\ &0 < r / sqrt q /\ &1 <= exp(&2 * K * tau) /\ &0 < rho`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < sqrt q` ASSUME_TAC THENL [ASM_SIMP_TAC[SQRT_POS_LT]; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < r / sqrt q` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_LT_DIV]; ALL_TAC] THEN
    SUBGOAL_THEN `&1 <= exp(&2 * K * tau)` ASSUME_TAC THENL
     [MP_TAC(SPEC `&2 * K * tau` REAL_EXP_LE_X) THEN
      SUBGOAL_THEN `&0 <= K * tau` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LTE_TRANS THEN
    EXISTS_TAC `&4 * exp(&2 * K * tau) * r / sqrt q` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `open_in (rfs_vtop V tt) (W:A->bool) /\ (y:A) IN W /\
                W SUBSET topspace(rfs_vtop (V:(real->A topology)#
                   (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "W" THEN REWRITE_TAC[P2AP_BALL_SUBSET] THEN CONJ_TAC THENL
     [MATCH_MP_TAC MFD_BALL_OPEN THEN ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[MFD_CENTRE_IN_BALL]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:A) IN topspace(rfs_vtop (V:(real->A topology)#
                  (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) a)`
  ASSUME_TAC THENL [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `a:real`; `y:A`] P2AP_SLICE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `p2a_region (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                  (real->A->real^3^3)) W a tt /\
    mfd_diffeo (rfs_vtop V a) (rfs_vatlas V a) W (rfs_vtop V tt) (rfs_vatlas V tt) W
               (\y:A. y) (\y. y) /\
    p2c_vflow_from V W a tt`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC RFA_HC2_REGULAR_REGION THEN ASM_REWRITE_TAC[];
      FIRST_X_ASSUM(MP_TAC o el 4 o CONJUNCTS o GEN_REWRITE_RULE I [p2c_regular_view] o
        check (fun th -> can (find_term (fun t -> is_const t &&
          fst(dest_const t) = "p2c_regular_view")) (concl th))) THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC P2C_REGULAR_VFLOW_FROM THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [p2c_vflow_from] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p2c_vflow_from")) (concl th))) THEN
  REWRITE_TAC[p2c_vflow; RFA_RFS_FLOW_UPTO] THEN STRIP_TAC THEN
  ABBREV_TAC `MT = subtopology (rfs_vtop V tt) (W:A->bool)` THEN
  ABBREV_TAC `MA = restrict_atlas (rfs_vatlas (V:(real->A topology)#
                     (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt) W` THEN
  ABBREV_TAC `G = p2c_vfam (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) W tt` THEN
  SUBGOAL_THEN `topspace MT = (W:A->bool) /\ hausdorff_space MT /\
                smooth_manifold_atlas MT (MA:((A->bool)#(A->real^3))->bool) /\
                riemannian_metric MA ((G:real->A->real^3^3) a)` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["MT"; "MA"] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN ASM SET_TAC[];
      MATCH_MP_TAC HAUSDORFF_SPACE_SUBTOPOLOGY THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC SMOOTH_MANIFOLD_ATLAS_RESTRICT THEN ASM_REWRITE_TAC[];
      ASM_MESON_TAC[ricci_flow_from]];
    ALL_TAC] THEN
  (* the comparison g(tt) <= lam^2 g(a) on W *)
  SUBGOAL_THEN
   `!z v. (z:A) IN W
          ==> v dot ((G:real->A->real^3^3) tt z ** v) <=
              exp(&2 * K * tau) pow 2 * (v dot (G a z ** v))`
  (LABEL_TAC "cmp") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                      (real->A->real^3^3)`; `W:A->bool`; `a:real`; `tt:real`; `K * q`;
                   `z:A`; `v:real^3`] RFA_HC2_START_COMPARE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
      TRY(MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC) THEN
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o CONJUNCT2) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `b <= c ==> a <= b ==> a <= c`) THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
     [REWRITE_TAC[GSYM REAL_EXP_N; REAL_EXP_MONO_LE] THEN
      MATCH_MP_TAC(REAL_ARITH
       `(&4 * K) * (q * (tt - a)) <= (&4 * K) * tau
        ==> &4 * (K * q) * (tt - a) <= &2 * &2 * K * tau`) THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC P2AP_QFORM_NONNEG THEN
      MAP_EVERY EXISTS_TAC [`MT:A topology`; `MA:((A->bool)#(A->real^3))->bool`] THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(G:real->A->real^3^3) tt =
                restrict_metric (rfs_vatlas V tt) W
                  (rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                  (real->A->real^3^3)) tt)`
  ASSUME_TAC THENL [EXPAND_TAC "G" THEN REWRITE_TAC[p2c_vfam; ETA_AX]; ALL_TAC] THEN
  (* compactness of the closure of the Shi ball at a *)
  SUBGOAL_THEN
   `compact_in MT (MT closure_of mfd_ball (MT,MA) ((G:real->A->real^3^3) a) y (r / sqrt q))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) tt`;
                   `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                  (real->A->real^3^3)) tt`;
                   `rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                   (real->A->real^3^3)) tt`;
                   `y:A`; `rho:real`; `(G:real->A->real^3^3) a`; `y:A`; `r / sqrt q`;
                   `exp(&2 * K * tau)`] P2AP_BALL_COMPACT) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [ASM_SIMP_TAC[MFD_CENTRE_IN_BALL] THEN ASM_REAL_ARITH_TAC;
        REWRITE_TAC[REAL_EXP_POS_LT];
        ASM_REAL_ARITH_TAC;
        UNDISCH_THEN `(G:real->A->real^3^3) tt =
                      restrict_metric (rfs_vatlas V tt) W
                        (rfs_vmetric (V:(real->A topology)#
                          (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt)`
          (SUBST1_TAC o SYM) THEN
        USE_THEN "cmp" ACCEPT_TAC];
      SIMP_TAC[]];
    ALL_TAC] THEN
  REMOVE_THEN "shi" (MP_TAC o SPECL
   [`MT:A topology`; `MA:((A->bool)#(A->real^3))->bool`; `a:real`; `tt:real`;
    `G:real->A->real^3^3`; `y:A`; `q:real`]) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [MAP_EVERY X_GEN_TAC [`s:real`; `z:A`] THEN STRIP_TAC THEN
      SUBGOAL_THEN `(z:A) IN W` ASSUME_TAC THENL
       [UNDISCH_TAC `(z:A) IN mfd_ball (MT,MA) ((G:real->A->real^3^3) a) y (r / sqrt q)` THEN
        MP_TAC(ISPECL [`MT:A topology`; `MA:((A->bool)#(A->real^3))->bool`;
                       `(G:real->A->real^3^3) a`; `y:A`; `r / sqrt q`] P2AP_BALL_SUBSET) THEN
        ASM_REWRITE_TAC[] THEN SET_TAC[];
        ALL_TAC] THEN
      ASM_CASES_TAC `s:real = a` THENL
       [FIRST_X_ASSUM SUBST_ALL_TAC THEN
        SUBGOAL_THEN `rfa_rmd2 0 MA ((G:real->A->real^3^3) a) z <= K * q pow 2` ASSUME_TAC THENL
         [MAP_EVERY EXPAND_TAC ["G"; "MA"] THEN
          MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                            (real->A->real^3^3)`; `W:A->bool`; `a:real`; `tt:real`; `0`;
                         `z:A`] RFA_HC2_START_DERIV) THEN
          ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
          FIRST_X_ASSUM(MP_TAC o SPECL [`0`; `z:A`] o check (fun th -> is_forall(concl th) &&
            can (find_term (fun t -> is_const t && fst(dest_const t) = "rfa_rmd2")) (concl th))) THEN
          ASM_REWRITE_TAC[LE_0] THEN CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[];
          ALL_TAC] THEN
        MP_TAC(ISPECL [`MT:A topology`; `MA:((A->bool)#(A->real^3))->bool`;
                       `(G:real->A->real^3^3) a`; `z:A`; `K * q pow 2`]
                      RFA_HC2_RMD0_BOUNDS) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        DISCH_THEN(MP_TAC o CONJUNCT1) THEN
        REWRITE_TAC[SQRT_MUL] THEN ASM_SIMP_TAC[POW_2_SQRT; REAL_LT_IMP_LE] THEN
        MATCH_MP_TAC(REAL_ARITH `b <= c ==> a <= b ==> a <= c`) THEN
        MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                        (real->A->real^3^3)`; `W:A->bool`; `a:real`; `tt:real`; `s:real`;
                     `z:A`] P2AP_VFAM_RM_NORM_LE) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(REAL_ARITH `b <= c ==> a <= b ==> a <= c`) THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `K * q` THEN CONJ_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN REAL_ARITH_TAC];
      MAP_EVERY X_GEN_TAC [`j:num`; `z:A`] THEN STRIP_TAC THEN
      SUBGOAL_THEN `(z:A) IN W` ASSUME_TAC THENL
       [UNDISCH_TAC `(z:A) IN mfd_ball (MT,MA) ((G:real->A->real^3^3) a) y (r / sqrt q)` THEN
        MP_TAC(ISPECL [`MT:A topology`; `MA:((A->bool)#(A->real^3))->bool`;
                       `(G:real->A->real^3^3) a`; `y:A`; `r / sqrt q`] P2AP_BALL_SUBSET) THEN
        ASM_REWRITE_TAC[] THEN SET_TAC[];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                        (real->A->real^3^3)`; `W:A->bool`; `a:real`; `tt:real`; `j:num`;
                     `z:A`] RFA_HC2_START_DERIV) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `K * q pow (j + 2)` THEN CONJ_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_POW_LE; REAL_LT_IMP_LE] THEN
        REAL_ARITH_TAC]];
    ALL_TAC] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`MT:A topology`; `MA:((A->bool)#(A->real^3))->bool`; `a:real`; `tt:real`;
                 `G:real->A->real^3^3`; `y:A`; `l:num`; `Cl * q pow (l + 2)`; `tt - a`]
                RFA_UPTO_RMD_LIMIT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `W:A->bool`; `a:real`; `tt:real`; `tt:real`;
                 `l:num`; `y:A`] P2AP_VFAM_DERIV) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL]; ALL_TAC] THEN
  ASM_REWRITE_TAC[rfa_rmd2; p3_vderiv2] THEN DISCH_THEN SUBST1_TAC THEN SIMP_TAC[]);;

let RFA_HC2_CONTON_RIGHT_LE = prove
 (`!f t0 t1 c.
     f real_continuous_on real_interval[t0,t1] /\ t0 < t1 /\
     (!t. t0 < t /\ t <= t1 ==> f t <= c)
     ==> f t0 <= c`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `t0:real` o GEN_REWRITE_RULE I [real_continuous_on]) THEN
  ANTS_TAC THENL [REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `(f:real->real) t0 - c`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o
    SPEC `t0 + min d (t1 - t0) / &2`))) THEN
  ANTS_TAC THENL [REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `t0 + min d (t1 - t0) / &2`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  POP_ASSUM MP_TAC THEN ASM_REAL_ARITH_TAC);;

let RFA_HC2_SCALE_ARITH1 = prove
 (`!hT rho L. &0 < hT /\ &0 < rho /\ rho <= L * hT ==> inv(hT pow 2) <= L pow 2 * inv(rho pow 2)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < hT pow 2 /\ &0 < rho pow 2 /\ rho pow 2 <= L pow 2 * hT pow 2`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_POW_LT; GSYM REAL_POW_MUL] THEN MATCH_MP_TAC REAL_POW_LE2 THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM real_div] THEN ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[GSYM real_div] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ]);;

let RFA_HC2_SCALE_ARITH2 = prove
 (`!hT R ct. &0 < hT /\ &0 < ct /\ ct / &2 <= hT pow 2 * R ==> inv(hT pow 2) <= &2 / ct * R`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < hT pow 2` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `inv(hT pow 2) = (&2 / ct) * (inv(hT pow 2) * (ct / &2))` SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < ct` THEN UNDISCH_TAC `&0 < hT pow 2` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(hT pow 2) * (hT pow 2 * R)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LE_INV; REAL_LT_IMP_LE];
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN UNDISCH_TAC `&0 < hT pow 2` THEN CONV_TAC REAL_FIELD]);;

(* ------------------------------------------------------------------------- *)
(* The fresh-cap case of R13 (RFA_HC2_FRESH_RMD).  The half                  *)
(* ball W = B(y,t,1/(4 sqrt(C q))), q = R(x), does not persist over          *)
(* (t - tau0/q, t]: it persists over (T_k,t] for an event time T_k in the    *)
(* window and meets a new cap of event k at a point z (RFA_HC2_EXPOSED_      *)
(* WINDOW).  At T_k the cap is h^2-close to g0, h = h(T_k)                   *)
(* (RFA_HC2_CAP_STATIC).  Scale: h^-2 <= Kp q, from the tip, with           *)
(* h^2 R(tip) >= R_g0(0)/2 and d(z,tip) <= 2 (A0 + 5) h: for T_k = t the     *)
(* tip lies in B(z,t,1/(4 sqrt(C q))), inside U, where R <= 2 C q; for       *)
(* T_k < t, R(z,T_k) <= 4 C q (RFA_HC2_HIST_BACK and right continuity) and   *)
(* the spatial step of Lemma 11.2 (P2C_DB_SPATIAL, gradient bound            *)
(* RFA_HC2_HIST_GRAD) bounds R at the tip; otherwise h is large.  Then      *)
(* W lies near the cap at T_k (RFA_HC2_START_DIST), where abs(nabla^j Rm)^2 <= *)
(* Cc h^-2(j+2) <= Cc Kp^4 q^(j+2); for T_k = t this is the bound at y, and  *)
(* for T_k < t Shi with initial data on W (RFA_HC2_REGION_SHI_INIT) gives    *)
(* it.  One constant Cf serves l <= 2.                                        *)
(* ------------------------------------------------------------------------- *)

let RFA_HC2_FRESH_RMD = prove
 (`?eps1. &0 < eps1 /\
     !C md g0 A0. &1 < C /\ p3_modulus md /\ p3_std_initial g0 A0
       ==> ?d0 Cf. &0 < d0 /\ &0 < Cf /\
             !eps hf rp dl (hs:(A)rfs_history) t x U y l.
               P2C_HISTORY_REGULAR_STATEMENT (:A) /\ &0 < eps /\ eps <= eps1 /\
               p3_hfun C hf /\ p3_struct (C,eps,hf,md,g0,A0) (rp,dl) hs /\
               (!s. &0 <= s /\ t - &1 / &32 <= s /\ s <= t ==> rp s <= eps /\ dl s <= d0) /\
               rfs_canonical_assumption (rfs_trunc (rfs_view hs) t) C eps rp /\
               &0 <= t /\ t < rfs_horizon hs /\ x IN topspace(rfs_top_at hs t) /\
               inv(rp t pow 2) <= mfd_scalar (rfs_atlas_at hs t) (rfs_metric_at hs t) x /\
               rfs_canonical_nbhd (rfs_top_at hs t,rfs_atlas_at hs t) (rfs_metric_at hs t)
                                  C eps x U /\
               y IN U /\
               mfd_ball (rfs_top_at hs t,rfs_atlas_at hs t) (rfs_metric_at hs t) y
                 (inv(&2 * sqrt(C * mfd_scalar (rfs_atlas_at hs t) (rfs_metric_at hs t) x)))
               SUBSET U /\
               ~rfs_persists (rfs_view hs)
                  (mfd_ball (rfs_top_at hs t,rfs_atlas_at hs t) (rfs_metric_at hs t) y
                    (inv(&4 * sqrt(C * mfd_scalar (rfs_atlas_at hs t) (rfs_metric_at hs t) x))))
                  (t - inv(&32 * C * max C (&2)) /
                       mfd_scalar (rfs_atlas_at hs t) (rfs_metric_at hs t) x) t /\
               l <= 2
               ==> rfa_rmd2 l (rfs_atlas_at hs t) (rfs_metric_at hs t) y <=
                   Cf * mfd_scalar (rfs_atlas_at hs t) (rfs_metric_at hs t) x pow (l + 2)`,
  X_CHOOSE_THEN `Tst:real` (X_CHOOSE_THEN `e1:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "early")))) (INST_TYPE [`:A`,`:A`] RFA_HC2_EARLY) THEN
  X_CHOOSE_THEN `e2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "back"))
    (INST_TYPE [`:A`,`:A`] RFA_HC2_HIST_BACK) THEN
  X_CHOOSE_THEN `e3:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ratio"))
    (INST_TYPE [`:A`,`:A`] RFA_C2_RATIO) THEN
  X_CHOOSE_THEN `e4:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "grad"))
    (INST_TYPE [`:A`,`:A`] RFA_HC2_HIST_GRAD) THEN
  EXISTS_TAC `min (min (&1 / &2) (sqrt Tst)) (min e1 (min e2 (min e3 e4)))` THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_LT_MIN] THEN ASM_SIMP_TAC[SQRT_POS_LT] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`C:real`; `md:real->real`; `g0:real^3->real^3^3`; `A0:real`] THEN
  STRIP_TAC THEN
  (* the constants *)
  ABBREV_TAC `C2 = max C (&2)` THEN
  SUBGOAL_THEN `&1 < C2 /\ C <= C2 /\ &2 <= C2` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "C2" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(ASSUME_TAC o GEN `spd_v:real` o
    check (fun th -> is_eq(concl th) && rhs(concl th) = `C2:real`)) THEN
  ABBREV_TAC `tau0 = inv(&32 * C * C2)` THEN
  ABBREV_TAC `Krm = &8 * C + &12 + &2 * exp(&4)` THEN
  ABBREV_TAC `lam = exp(&2 * Krm * tau0)` THEN
  ABBREV_TAC `ct = lscalar g0 (vec 0:real^3)` THEN
  ABBREV_TAC `L = &2 * (A0 + &5)` THEN
  ABBREV_TAC `Kp = &16 * C * (C2 pow 2 * L pow 2 + inv ct)` THEN
  ABBREV_TAC `c3 = lam * sqrt Kp / (&2 * sqrt C)` THEN
  SUBGOAL_THEN `&0 < tau0 /\ tau0 <= &1 / &64` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "tau0" THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_INV THEN REPEAT(MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC) THEN
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(&32 * &1 * &2)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC;
        CONV_TAC REAL_RAT_REDUCE_CONV]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < Krm` ASSUME_TAC THENL
   [EXPAND_TAC "Krm" THEN MP_TAC(SPEC `&4` REAL_EXP_POS_LT) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= lam` ASSUME_TAC THENL
   [EXPAND_TAC "lam" THEN MP_TAC(SPEC `&2 * Krm * tau0` REAL_EXP_LE_X) THEN
    SUBGOAL_THEN `&0 <= Krm * tau0` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < ct /\ &0 < A0` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [EXPAND_TAC "ct" THEN MATCH_MP_TAC RFA_HC2_TIP_SCALAR THEN EXISTS_TAC `A0:real` THEN
      ASM_REWRITE_TAC[];
      UNDISCH_TAC `p3_std_initial g0 A0` THEN SIMP_TAC[p3_std_initial]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&10 <= L` ASSUME_TAC THENL [EXPAND_TAC "L" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= Kp` ASSUME_TAC THENL
   [EXPAND_TAC "Kp" THEN
    SUBGOAL_THEN `&1 <= C2 pow 2 * L pow 2 /\ &0 <= inv ct` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
        REWRITE_TAC[REAL_POS] THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1 pow 2` THEN CONJ_TAC THENL
           [REAL_ARITH_TAC; MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC];
          MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1 pow 2` THEN CONJ_TAC THENL
           [REAL_ARITH_TAC; MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC]];
        MATCH_MP_TAC REAL_LE_INV THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&16 * &1 * &1` THEN CONJ_TAC THENL
     [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt C /\ &0 < sqrt Kp` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SQRT_POS_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= c3` ASSUME_TAC THENL
   [EXPAND_TAC "c3" THEN MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `c3:real`]
               (INST_TYPE [`:A`,`:A`] RFA_HC2_CAP_STATIC)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `dd:real` (X_CHOOSE_THEN `Cc:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "cap")))))) THEN
  ABBREV_TAC `Ksh = max Krm (Cc * Kp pow 4)` THEN
  ABBREV_TAC `rs = inv(&16 * exp(&2 * Ksh * tau0) * sqrt C)` THEN
  SUBGOAL_THEN `&0 < Ksh /\ Krm <= Ksh /\ Cc * Kp pow 4 <= Ksh /\ &0 < rs` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["rs"; "Ksh"] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC; REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC REAL_LT_MUL THEN
      CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[REAL_EXP_POS_LT]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> is_eq(concl th) && rhs(concl th) = `Ksh:real`)) THEN
  MP_TAC(SPECL [`0`; `Ksh:real`; `rs:real`; `tau0:real`]
               (INST_TYPE [`:A`,`:A`] RFA_HC2_REGION_SHI_INIT)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `S0:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (LABEL_TAC "shi0"))) THEN
  MP_TAC(SPECL [`1`; `Ksh:real`; `rs:real`; `tau0:real`]
               (INST_TYPE [`:A`,`:A`] RFA_HC2_REGION_SHI_INIT)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `S1:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (LABEL_TAC "shi1"))) THEN
  MP_TAC(SPECL [`2`; `Ksh:real`; `rs:real`; `tau0:real`]
               (INST_TYPE [`:A`,`:A`] RFA_HC2_REGION_SHI_INIT)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `S2:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (LABEL_TAC "shi2"))) THEN
  MAP_EVERY EXISTS_TAC [`(md:real->real) dd`; `max (Cc * Kp pow 4) (max S0 (max S1 S2))`] THEN
  CONJ_TAC THENL
   [UNDISCH_TAC `p3_modulus md` THEN REWRITE_TAC[p3_modulus] THEN
    DISCH_THEN(MP_TAC o SPEC `dd:real`) THEN ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`eps:real`; `hf:real->real->real`; `rp:real->real`; `dl:real->real`;
                       `hs:(A)rfs_history`; `t:real`; `x:A`; `U:A->bool`; `y:A`; `l:num`] THEN
  STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [p3_struct]) THEN STRIP_TAC THEN
  SUBGOAL_THEN `p2c_regular_view (rfs_view (hs:(A)rfs_history))` ASSUME_TAC THENL
   [UNDISCH_TAC `P2C_HISTORY_REGULAR_STATEMENT (:A)` THEN
    REWRITE_TAC[P2C_HISTORY_REGULAR_STATEMENT] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(!s. &0 <= s ==> &0 < (rp:real->real) s) /\
                (!s t. &0 <= s /\ s <= t ==> (rp:real->real) t <= rp s)`
  STRIP_ASSUME_TAC THENL
   [MESON_TAC[ASSUME `!t. &0 <= t ==> &0 < (rp:real->real) t /\ &0 < (dl:real->real) t`;
              ASSUME `!s t. &0 <= s /\ s <= t
                            ==> (rp:real->real) t <= rp s /\ (dl:real->real) t <= dl s`];
    ALL_TAC] THEN
  SUBGOAL_THEN `(rp:real->real) t <= eps` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPEC `t:real` o check (fun th -> is_forall(concl th) &&
      can (find_term (let tm = `(md:real->real) dd` in fun t -> t = tm)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL] THEN REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (rp:real->real) t` ASSUME_TAC THENL
   [MATCH_MP_TAC(ASSUME `!s. &0 <= s ==> &0 < (rp:real->real) s`) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `eps <= &1 / &2 /\ eps <= sqrt Tst /\ eps <= e1 /\ eps <= e2 /\ eps <= e3 /\
                eps <= e4` STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> not(is_forall(concl th)) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "real_min")) (concl th))) THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `t:real`] RFA_HC2_SLICE_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  USE_THEN "ratio" (MP_TAC o SPECL [`rfs_top_at (hs:(A)rfs_history) t`;
    `rfs_atlas_at (hs:(A)rfs_history) t`; `rfs_metric_at (hs:(A)rfs_history) t`; `C:real`;
    `eps:real`; `x:A`; `U:A->bool`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_neg(concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `q = mfd_scalar (rfs_atlas_at hs t) (rfs_metric_at (hs:(A)rfs_history) t) x` THEN
  ABBREV_TAC `rho = inv(&4 * sqrt(C * q))` THEN
  ABBREV_TAC `W = mfd_ball (rfs_top_at hs t,rfs_atlas_at hs t)
                           (rfs_metric_at (hs:(A)rfs_history) t) y rho` THEN
  (* q >= eps^-2 >= 4, early times *)
  SUBGOAL_THEN `inv(eps pow 2) <= q` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv((rp:real->real) t pow 2)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&4 <= inv(eps pow 2) /\ eps pow 2 <= Tst` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv((&1 / &2) pow 2)` THEN CONJ_TAC THENL
       [CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC];
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt Tst pow 2` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
        ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE; REAL_LE_REFL]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= q /\ &0 < q` STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `Tst <= t` ASSUME_TAC THENL
   [USE_THEN "early" MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`;
                          `g0:real^3->real^3^3`; `A0:real`; `rp:real->real`; `dl:real->real`;
                          `hs:(A)rfs_history`; `x:A`] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `tau0 / q <= t /\ &0 < tau0 / q /\ tau0 / q <= &1 / &64` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `tau0 * eps pow 2` THEN CONJ_TAC THENL
       [REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
        ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(inv(eps pow 2))` THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REWRITE_TAC[] THEN
          MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[];
          REWRITE_TAC[REAL_INV_INV; REAL_LE_REFL]];
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1 * Tst` THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
          CONJ_TAC THENL [ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC];
          ASM_REAL_ARITH_TAC]];
      ASM_SIMP_TAC[REAL_LT_DIV];
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `tau0:real` THEN ASM_REWRITE_TAC[] THEN
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt q /\ &0 < sqrt(C * q) /\ &0 < rho /\
                &2 * rho = inv(&2 * sqrt(C * q))` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < sqrt q /\ &0 < sqrt(C * q)` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC SQRT_POS_LT THEN
      TRY(MATCH_MP_TAC REAL_LT_MUL) THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "rho" THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC;
      UNDISCH_TAC `&0 < sqrt(C * q)` THEN CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_ball (rfs_top_at hs t,rfs_atlas_at hs t)
                  (rfs_metric_at (hs:(A)rfs_history) t) y (&2 * rho) SUBSET U /\
                (W:A->bool) SUBSET U /\ open_in (rfs_top_at hs t) W /\ (y:A) IN W`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `mfd_ball (rfs_top_at hs t,rfs_atlas_at hs t)
                    (rfs_metric_at (hs:(A)rfs_history) t) y (&2 * rho) SUBSET U`
    ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `mfd_ball (rfs_top_at hs t,rfs_atlas_at hs t)
                    (rfs_metric_at (hs:(A)rfs_history) t) y (&2 * rho)` THEN
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "W" THEN MATCH_MP_TAC RFA_MFD_BALL_MONO THEN
      ASM_REAL_ARITH_TAC;
      EXPAND_TAC "W" THEN MATCH_MP_TAC MFD_BALL_OPEN THEN ASM_REWRITE_TAC[];
      EXPAND_TAC "W" THEN ASM_SIMP_TAC[MFD_CENTRE_IN_BALL] THEN
      UNDISCH_TAC `(y:A) IN U` THEN
      UNDISCH_TAC `(U:A->bool) SUBSET topspace(rfs_top_at (hs:(A)rfs_history) t)` THEN
      SET_TAC[]];
    ALL_TAC] THEN
  (* the exposed point *)
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `W:A->bool`; `t - tau0 / q`; `t:real`]
                RFA_HC2_EXPOSED_WINDOW) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `z:A` STRIP_ASSUME_TAC o
    REWRITE_RULE[DISJOINT; GSYM MEMBER_NOT_EMPTY; IN_INTER]) THEN
  ABBREV_TAC `T1 = hs_time (hs:(A)rfs_history) k` THEN
  SUBGOAL_THEN `&0 <= T1 /\ t - &1 / &32 <= T1 /\ t - T1 < tau0 / q /\
                T1 < rfs_horizon (hs:(A)rfs_history)`
  STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `T1 < hs_time (hs:(A)rfs_history) (k + 1)` ASSUME_TAC THENL
   [EXPAND_TAC "T1" THEN
    FIRST_ASSUM(MATCH_MP_TAC o CONJUNCT1 o CONJUNCT2 o GEN_REWRITE_RULE I [rfs_history_ok] o
      check (fun th -> can (find_term (fun t -> is_const t &&
        fst(dest_const t) = "rfs_history_ok")) (concl th) && not(is_imp(concl th)))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `k:num`; `T1:real`] APX_RFS_SLAB) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `T1:real`] RFA_HC2_SLICE_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `?Phi xi. p3_cap_param (md,g0,A0) (dl,p3_hscale hf rp dl)
                           (hs:(A)rfs_history) k i (Phi:real^3->A) (xi:real^3->real^3)`
  (X_CHOOSE_THEN `Phi:real^3->A` (X_CHOOSE_THEN `xi:real^3->real^3` ASSUME_TAC)) THENL
   [REWRITE_TAC[GSYM p3_cap_ok] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "p3_cap_ok")) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MATCH_MP_TAC o last o CONJUNCTS) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `h = p3_hscale hf rp dl` THEN
  SUBGOAL_THEN `&0 < (dl:real->real) T1 /\ &0 < (h:real->real) T1 /\
                dl T1 <= (md:real->real) dd` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < (rp:real->real) T1 /\ &0 < (dl:real->real) T1` STRIP_ASSUME_TAC THENL
     [MATCH_MP_TAC(ASSUME `!t. &0 <= t ==> &0 < (rp:real->real) t /\ &0 < (dl:real->real) t`) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [EXPAND_TAC "h" THEN REWRITE_TAC[p3_hscale] THEN
      UNDISCH_TAC `p3_hfun C (hf:real->real->real)` THEN REWRITE_TAC[p3_hfun] THEN
      DISCH_THEN(MP_TAC o SPECL [`(dl:real->real) T1 * rp T1`; `(dl:real->real) T1`]) THEN
      ASM_SIMP_TAC[REAL_LT_MUL];
      FIRST_X_ASSUM(MP_TAC o SPEC `T1:real` o check (fun th -> is_forall(concl th) &&
        can (find_term (let tm = `(md:real->real) dd` in fun t -> t = tm)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[]];
    ALL_TAC] THEN
  USE_THEN "cap" (MP_TAC o SPECL [`md:real->real`; `dl:real->real`; `h:real->real`;
    `hs:(A)rfs_history`; `k:num`; `i:num`; `Phi:real^3->A`; `xi:real^3->real^3`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; ASM_REWRITE_TAC[]] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "tip") (MP_TAC o SPEC `z:A`)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "near"))) THEN
  ABBREV_TAC `hT = (h:real->real) T1` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `lscalar g0 (vec 0:real^3) = ct`]) THEN
  SUBGOAL_THEN `mfd_dist (hs_top hs k,hs_atlas hs k) (hs_metric (hs:(A)rfs_history) k T1)
                         z ((Phi:real^3->A)(vec 0)) <= L * hT` (LABEL_TAC "tipd") THENL
   [SUBGOAL_THEN `L * hT = &2 * (A0 + &5) * hT` SUBST1_TAC THENL
     [EXPAND_TAC "L" THEN REAL_ARITH_TAC; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&16 * C * L pow 2 <= Kp /\ &16 * C * C2 pow 2 * L pow 2 <= Kp /\
                &16 * C / ct <= Kp /\ inv(rho pow 2) = &16 * C * q`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 <= inv ct /\ &0 <= L pow 2 /\ &1 <= C2 pow 2` STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[REAL_LE_POW_2] THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_INV THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1 pow 2` THEN CONJ_TAC THENL
         [REAL_ARITH_TAC; MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC]];
      ALL_TAC] THEN
    SUBGOAL_THEN `L pow 2 <= C2 pow 2 * L pow 2` ASSUME_TAC THENL
     [GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= C2 pow 2 * L pow 2` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN UNDISCH_TAC `&1 <= C2 pow 2` THEN
        UNDISCH_TAC `&0 <= L pow 2` THEN REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [EXPAND_TAC "Kp" THEN MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_LMUL THEN
          UNDISCH_TAC `L pow 2 <= C2 pow 2 * L pow 2` THEN UNDISCH_TAC `&0 <= inv ct` THEN
          UNDISCH_TAC `&1 < C` THEN REAL_ARITH_TAC];
      EXPAND_TAC "Kp" THEN MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_LMUL THEN UNDISCH_TAC `&0 <= inv ct` THEN
          UNDISCH_TAC `&1 < C` THEN REAL_ARITH_TAC];
      EXPAND_TAC "Kp" THEN REWRITE_TAC[real_div] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_LMUL THEN
          UNDISCH_TAC `L pow 2 <= C2 pow 2 * L pow 2` THEN UNDISCH_TAC `&0 <= L pow 2` THEN
          UNDISCH_TAC `&1 < C` THEN REAL_ARITH_TAC];
      EXPAND_TAC "rho" THEN REWRITE_TAC[REAL_POW_INV; REAL_INV_INV; REAL_POW_MUL] THEN
      SUBGOAL_THEN `sqrt(C * q) pow 2 = C * q` SUBST1_TAC THENL
       [MATCH_MP_TAC SQRT_POW_2 THEN MATCH_MP_TAC REAL_LE_MUL THEN UNDISCH_TAC `&1 < C` THEN
          UNDISCH_TAC `&0 < q` THEN REAL_ARITH_TAC;
        REAL_ARITH_TAC]];
    ALL_TAC] THEN
  (* R <= 4 C q and abs Rm <= Krm q on W over (T1,t] *)
  SUBGOAL_THEN
   `!s w. T1 < s /\ s <= t /\ (w:A) IN W
          ==> rfs_vscalar (rfs_view (hs:(A)rfs_history)) s w <= &2 * (&2 * C * q)`
  (LABEL_TAC "rbound") THENL
   [REPEAT STRIP_TAC THEN USE_THEN "back" MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`C:real`; `eps:real`; `rp:real->real`; `t:real`; `W:A->bool`;
                          `T1:real`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      REWRITE_TAC[rfs_vscalar; rfs_view] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term (let tm = `U:A->bool` in fun t -> t = tm)) (concl th) &&
        can (find_term (let tm = `&2 * C * q` in fun t -> t = tm)) (concl th))) THEN
      UNDISCH_TAC `(w:A) IN W` THEN UNDISCH_TAC `(W:A->bool) SUBSET U` THEN SET_TAC[];
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `q:real` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(REAL_ARITH `&1 * q <= &2 * C * q ==> q <= &2 * C * q`) THEN
      REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN UNDISCH_TAC `&1 < C` THEN
        UNDISCH_TAC `&0 < q` THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_IMP_LE THEN MATCH_MP_TAC REAL_LTE_TRANS THEN
      EXISTS_TAC `tau0 / q` THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "tau0" THEN
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN UNDISCH_TAC `&0 < q` THEN UNDISCH_TAC `&1 < C` THEN
      UNDISCH_TAC `&1 < C2` THEN CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s w. T1 < s /\ s <= t /\ (w:A) IN W
          ==> p3_vrm (rfs_view (hs:(A)rfs_history)) s w <= Krm * q`
  (LABEL_TAC "rm") THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `&0 <= s /\ s < rfs_horizon (hs:(A)rfs_history)` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `s <= t` THEN UNDISCH_TAC `T1 < s` THEN UNDISCH_TAC `t - tau0 / q < T1` THEN
        UNDISCH_TAC `tau0 / q <= t` THEN UNDISCH_TAC `t < rfs_horizon (hs:(A)rfs_history)` THEN
        REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ISPECL [`hs:(A)rfs_history`; `s:real`] RFA_HC2_SLICE_FACTS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(w:A) IN topspace(rfs_top_at hs s)` ASSUME_TAC THENL
     [UNDISCH_TAC `rfs_persists (rfs_view (hs:(A)rfs_history)) W T1 t` THEN
      REWRITE_TAC[rfs_persists; rfs_view] THEN
      DISCH_THEN(MP_TAC o SPEC `s:real`) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o MATCH_MP OPEN_IN_SUBSET) THEN UNDISCH_TAC `(w:A) IN W` THEN
      SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `rfs_pinched_at (rfs_atlas_at hs s) (rfs_metric_at (hs:(A)rfs_history) s) s w`
    ASSUME_TAC THENL
     [UNDISCH_TAC `rfs_pinched (rfs_view (hs:(A)rfs_history))` THEN
      REWRITE_TAC[rfs_pinched; rfs_view] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`rfs_top_at (hs:(A)rfs_history) s`; `rfs_atlas_at (hs:(A)rfs_history) s`;
                   `rfs_metric_at (hs:(A)rfs_history) s`; `s:real`; `w:A`] RFA_PINCH_RM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    USE_THEN "rbound" (MP_TAC o SPECL [`s:real`; `w:A`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[rfs_vscalar; rfs_view] THEN DISCH_TAC] THEN
    SUBGOAL_THEN `-- &6 <= mfd_scalar (rfs_atlas_at hs s) (rfs_metric_at (hs:(A)rfs_history) s) w`
    ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `--(&6) / (&4 * s + &1)` THEN CONJ_TAC THENL
       [REWRITE_TAC[real_div; REAL_MUL_LNEG; REAL_LE_NEG2] THEN
        GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
        CONJ_TAC THENL [REAL_ARITH_TAC; MATCH_MP_TAC REAL_INV_LE_1 THEN UNDISCH_TAC `T1 < s` THEN
          UNDISCH_TAC `t - tau0 / q < T1` THEN UNDISCH_TAC `tau0 / q <= t` THEN REAL_ARITH_TAC];
        UNDISCH_TAC `rfs_pinched_at (rfs_atlas_at hs s) (rfs_metric_at (hs:(A)rfs_history) s) s w` THEN
        SIMP_TAC[rfs_pinched_at]];
      ALL_TAC] THEN
    SUBGOAL_THEN `(&12 + &2 * exp(&4)) * &1 <= (&12 + &2 * exp(&4)) * q` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN MP_TAC(SPEC `&4` REAL_EXP_POS_LT) THEN
        UNDISCH_TAC `&4 <= inv(eps pow 2)` THEN UNDISCH_TAC `inv(eps pow 2) <= q` THEN
        REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= C * q` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN UNDISCH_TAC `&1 < C` THEN UNDISCH_TAC `&0 < q` THEN
        REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[p3_vrm; rfs_view; rfs_vatlas; rfs_vmetric] THEN EXPAND_TAC "Krm" THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the scale bound h^-2 <= Kp q *)
  SUBGOAL_THEN `inv(hT pow 2) <= Kp * q` ASSUME_TAC THENL
   [ASM_CASES_TAC `T1:real = t` THENL
     [FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `T1:real = t`)) THEN
      ASM_CASES_TAC `rho <= L * hT` THENL
       [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `L pow 2 * inv(rho pow 2)` THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC RFA_HC2_SCALE_ARITH1 THEN ASM_REWRITE_TAC[];
          ASM_REWRITE_TAC[] THEN
          MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&16 * C * L pow 2) * q` THEN
          CONJ_TAC THENL
           [MATCH_MP_TAC REAL_EQ_IMP_LE THEN REAL_ARITH_TAC;
            MATCH_MP_TAC REAL_LE_RMUL THEN UNDISCH_TAC `&16 * C * L pow 2 <= Kp` THEN
              UNDISCH_TAC `&0 < q` THEN REAL_ARITH_TAC]];
        ALL_TAC] THEN
      SUBGOAL_THEN `(Phi:real^3->A)(vec 0) IN U` ASSUME_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
          can (find_term (let tm = `&2 * rho` in fun t -> t = tm)) (concl th) &&
          can (find_term (fun t -> is_const t && fst(dest_const t) = "SUBSET")) (concl th))) THEN
        MP_TAC(ISPECL [`rfs_top_at (hs:(A)rfs_history) t`; `rfs_atlas_at (hs:(A)rfs_history) t`;
                       `rfs_metric_at (hs:(A)rfs_history) t`; `y:A`; `z:A`; `rho:real`;
                       `rho:real`] P2AP_BALL_SHIFT) THEN
        ANTS_TAC THENL
         [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(z:A) IN W` THEN EXPAND_TAC "W" THEN
          SIMP_TAC[];
          ALL_TAC] THEN
        REWRITE_TAC[SUBSET; REAL_ARITH `rho + rho = &2 * rho`] THEN
        DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN
        ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `&2 / ct * mfd_scalar (hs_atlas hs k) (hs_metric (hs:(A)rfs_history) k t)
                                       ((Phi:real^3->A)(vec 0))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC RFA_HC2_SCALE_ARITH2 THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `(Phi:real^3->A)(vec 0)` o check (fun th ->
        is_forall(concl th) &&
        can (find_term (let tm = `U:A->bool` in fun t -> t = tm)) (concl th) &&
        can (find_term (let tm = `&2 * C * q` in fun t -> t = tm)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&2 / ct * (&2 * C * q)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC REAL_LE_DIV THEN UNDISCH_TAC `&0 < ct` THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&16 * C / ct) * q` THEN CONJ_TAC THENL
       [REWRITE_TAC[real_div] THEN
        SUBGOAL_THEN `&0 <= C * inv ct * q` MP_TAC THENL
         [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [UNDISCH_TAC `&1 < C` THEN
            REAL_ARITH_TAC; ALL_TAC] THEN
          MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
           [MATCH_MP_TAC REAL_LE_INV THEN ASM_REAL_ARITH_TAC; UNDISCH_TAC `&0 < q` THEN
              REAL_ARITH_TAC];
          REAL_ARITH_TAC];
        MATCH_MP_TAC REAL_LE_RMUL THEN UNDISCH_TAC `&16 * C / ct <= Kp` THEN
          UNDISCH_TAC `&0 < q` THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    (* T1 < t: R(z,T1) <= 4 C q, the gradient bound at T1, and the spatial step *)
    SUBGOAL_THEN `T1 < t` ASSUME_TAC THENL [UNDISCH_TAC `~(T1:real = t)` THEN
      UNDISCH_TAC `T1:real <= t` THEN REAL_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(K ALL_TAC o check (fun th -> concl th = `~(T1:real = t)`)) THEN
    SUBGOAL_THEN
     `mfd_diffeo (rfs_top_at hs T1) (rfs_atlas_at hs T1) W
                 (rfs_top_at hs t) (rfs_atlas_at (hs:(A)rfs_history) t) W (\y:A. y) (\y. y)`
    ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o el 4 o CONJUNCTS o GEN_REWRITE_RULE I [p2c_regular_view] o
        check (fun th -> can (find_term (fun t -> is_const t &&
          fst(dest_const t) = "p2c_regular_view")) (concl th))) THEN
      REWRITE_TAC[P2C_RFS_VIEW_PARTS] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `mfd_scalar (hs_atlas hs k) (hs_metric (hs:(A)rfs_history) k T1) z <=
                  &4 * C * q` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`rfs_view (hs:(A)rfs_history)`; `W:A->bool`; `T1:real`; `t:real`; `z:A`;
                     `(T1 + t) / &2`] P2C_VIEW_SCALAR_CONT_FROM) THEN
      REWRITE_TAC[P2C_RFS_VIEW_PARTS] THEN ASM_REWRITE_TAC[] THEN
      ANTS_TAC THENL [UNDISCH_TAC `T1:real < t` THEN REAL_ARITH_TAC; DISCH_TAC] THEN
      MP_TAC(ISPECL [`\u. rfs_vscalar (rfs_view (hs:(A)rfs_history)) u z`; `T1:real`;
                     `(T1 + t) / &2`; `&4 * C * q`] RFA_HC2_CONTON_RIGHT_LE) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
       [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        X_GEN_TAC `s:real` THEN STRIP_TAC THEN
        USE_THEN "rbound" (MP_TAC o SPECL [`s:real`; `z:A`]) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `s <= (T1 + t) / &2` THEN
          UNDISCH_TAC `T1:real <= t` THEN REAL_ARITH_TAC; REAL_ARITH_TAC];
        ASM_REWRITE_TAC[rfs_vscalar; rfs_view]];
      ALL_TAC] THEN
    SUBGOAL_THEN `inv((rp:real->real) t pow 2) <= q` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < inv((rp:real->real) t pow 2)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_INV THEN ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
    ABBREV_TAC `rr = inv(&2 * C2 * sqrt(&4 * C * q))` THEN
    SUBGOAL_THEN `&0 < sqrt(&4 * C * q) /\ &0 < rr` STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN `&0 < sqrt(&4 * C * q)` ASSUME_TAC THENL
       [MATCH_MP_TAC SQRT_POS_LT THEN MATCH_MP_TAC REAL_LT_MUL THEN
        CONJ_TAC THENL [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LT_MUL THEN UNDISCH_TAC `&1 < C` THEN
          UNDISCH_TAC `&0 < q` THEN REAL_ARITH_TAC];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "rr" THEN MATCH_MP_TAC REAL_LT_INV THEN
      MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
       [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LT_MUL THEN UNDISCH_TAC `&0 < sqrt(&4 * C * q)` THEN
          UNDISCH_TAC `&1 < C2` THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    ASM_CASES_TAC `rr <= L * hT` THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `L pow 2 * inv(rr pow 2)` THEN
      CONJ_TAC THENL [MATCH_MP_TAC RFA_HC2_SCALE_ARITH1 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `inv(rr pow 2) = &16 * C2 pow 2 * C * q` SUBST1_TAC THENL
       [EXPAND_TAC "rr" THEN REWRITE_TAC[REAL_POW_INV; REAL_INV_INV; REAL_POW_MUL] THEN
        SUBGOAL_THEN `sqrt(&4 * C * q) pow 2 = &4 * C * q` SUBST1_TAC THENL
         [MATCH_MP_TAC SQRT_POW_2 THEN MATCH_MP_TAC REAL_LE_MUL THEN
          CONJ_TAC THENL [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_MUL THEN UNDISCH_TAC `&1 < C` THEN
            UNDISCH_TAC `&0 < q` THEN REAL_ARITH_TAC];
          REAL_ARITH_TAC];
        ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&16 * C * C2 pow 2 * L pow 2) * q` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_EQ_IMP_LE THEN REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_RMUL THEN UNDISCH_TAC `&16 * C * C2 pow 2 * L pow 2 <= Kp` THEN
          UNDISCH_TAC `&0 < q` THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    (* the tip is within rr of z at T1: the spatial step bounds R there *)
    MP_TAC(ISPECL [`rfs_view (hs:(A)rfs_history)`; `C2:real`; `(rp:real->real) t`; `z:A`;
                   `T1:real`; `rr:real`; `(Phi:real^3->A)(vec 0)`] P2C_DB_SPATIAL) THEN
    REWRITE_TAC[P2C_VIEW_EXPAND; P2C_RFS_VIEW_PARTS] THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [ASM_REWRITE_TAC[];
        ASM_REAL_ARITH_TAC;
        ASM_REWRITE_TAC[];
        X_GEN_TAC `w:A` THEN STRIP_TAC THEN
        USE_THEN "grad" (MP_TAC o SPECL [`C:real`; `eps:real`; `rp:real->real`;
          `hs:(A)rfs_history`; `t:real`; `T1:real`; `w:A`]) THEN
        ANTS_TAC THENL
         [REWRITE_TAC[P2C_VIEW_EXPAND; P2C_RFS_VIEW_PARTS] THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
          REWRITE_TAC[P2C_VIEW_EXPAND; P2C_RFS_VIEW_PARTS] THEN ASM_REWRITE_TAC[] THEN SIMP_TAC[]];
        UNDISCH_TAC `open_in (rfs_top_at (hs:(A)rfs_history) T1) W` THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o MATCH_MP OPEN_IN_SUBSET) THEN
        UNDISCH_TAC `(z:A) IN W` THEN SET_TAC[];
        ASM_REWRITE_TAC[] THEN EXPAND_TAC "rr" THEN MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
          MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
          MATCH_MP_TAC SQRT_POS_LT THEN UNDISCH_TAC `&0 < inv((rp:real->real) t pow 2)` THEN
            REAL_ARITH_TAC;
          MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
          MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
          MATCH_MP_TAC SQRT_MONO_LE THEN
          SUBGOAL_THEN `q <= &4 * C * q` MP_TAC THENL
           [MATCH_MP_TAC(REAL_ARITH `&1 * q <= (&4 * C) * q ==> q <= &4 * C * q`) THEN
            MATCH_MP_TAC REAL_LE_RMUL THEN UNDISCH_TAC `&1 < C` THEN UNDISCH_TAC `&0 < q` THEN
              REAL_ARITH_TAC;
            UNDISCH_TAC `mfd_scalar (hs_atlas hs k) (hs_metric (hs:(A)rfs_history) k T1) (z:A)
                         <= &4 * C * q` THEN
            UNDISCH_TAC `inv((rp:real->real) t pow 2) <= q` THEN REAL_ARITH_TAC]];
        REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&2 / ct * mfd_scalar (hs_atlas hs k) (hs_metric (hs:(A)rfs_history) k T1)
                                     ((Phi:real^3->A)(vec 0))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC RFA_HC2_SCALE_ARITH2 THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&2 / ct * (&16 / &9 * (&4 * C * q))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_DIV THEN UNDISCH_TAC `&0 < ct` THEN REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `&16 / &9 * max (mfd_scalar (hs_atlas hs k)
                                    (hs_metric (hs:(A)rfs_history) k T1) z)
                                 (inv((rp:real->real) t pow 2))` THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `q <= &4 * C * q` MP_TAC THENL
       [MATCH_MP_TAC(REAL_ARITH `&1 * q <= (&4 * C) * q ==> q <= &4 * C * q`) THEN
        MATCH_MP_TAC REAL_LE_RMUL THEN UNDISCH_TAC `&1 < C` THEN UNDISCH_TAC `&0 < q` THEN
          REAL_ARITH_TAC;
        UNDISCH_TAC `mfd_scalar (hs_atlas hs k) (hs_metric (hs:(A)rfs_history) k T1) (z:A)
                     <= &4 * C * q` THEN
        UNDISCH_TAC `inv((rp:real->real) t pow 2) <= q` THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&16 * C / ct) * q` THEN CONJ_TAC THENL
     [REWRITE_TAC[real_div] THEN
      SUBGOAL_THEN `&0 <= C * inv ct * q` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [UNDISCH_TAC `&1 < C` THEN
          REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_INV THEN UNDISCH_TAC `&0 < ct` THEN
            REAL_ARITH_TAC; UNDISCH_TAC `&0 < q` THEN REAL_ARITH_TAC];
        REAL_ARITH_TAC];
      MATCH_MP_TAC REAL_LE_RMUL THEN UNDISCH_TAC `&16 * C / ct <= Kp` THEN
        UNDISCH_TAC `&0 < q` THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* the cap bounds in units of q *)
  SUBGOAL_THEN `!j. j <= 2 ==> Cc * inv(hT pow 2) pow (j + 2) <= (Cc * Kp pow 4) * q pow (j + 2)`
  (LABEL_TAC "kq") THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(Kp * q) pow (j + 2)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_INV THEN
      REWRITE_TAC[REAL_LE_POW_2];
      REWRITE_TAC[REAL_POW_MUL] THEN MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `(j:num) <= 2` THEN ARITH_TAC;
        MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `rho <= c3 * hT /\ &2 * lam * rho <= c3 * hT` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < hT pow 2` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
    SUBGOAL_THEN `&1 <= (Kp * q) * hT pow 2` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(hT pow 2) * hT pow 2` THEN CONJ_TAC THENL
       [ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ; REAL_LE_REFL];
        MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]];
      ALL_TAC] THEN
    SUBGOAL_THEN `&1 <= sqrt Kp * sqrt q * hT` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt((Kp * q) * hT pow 2)` THEN CONJ_TAC THENL
       [GEN_REWRITE_TAC LAND_CONV [GSYM SQRT_1] THEN MATCH_MP_TAC SQRT_MONO_LE THEN
        ASM_REWRITE_TAC[];
        REWRITE_TAC[SQRT_MUL] THEN ASM_SIMP_TAC[POW_2_SQRT; REAL_LT_IMP_LE] THEN
        REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `&2 * lam * rho <= c3 * hT` ASSUME_TAC THENL
     [SUBGOAL_THEN `&2 * lam * rho = (lam / (&2 * sqrt C * sqrt q)) * &1 /\
                    c3 * hT = (lam / (&2 * sqrt C * sqrt q)) * (sqrt Kp * sqrt q * hT)`
      (CONJUNCTS_THEN SUBST1_TAC) THENL
       [MAP_EVERY EXPAND_TAC ["rho"; "c3"] THEN REWRITE_TAC[SQRT_MUL] THEN
        CONJ_TAC THEN UNDISCH_TAC `&0 < sqrt C` THEN UNDISCH_TAC `&0 < sqrt q` THEN
        UNDISCH_TAC `&0 < sqrt Kp` THEN CONV_TAC REAL_FIELD;
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_DIV THEN
        CONJ_TAC THENL [UNDISCH_TAC `&1 <= lam` THEN REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LE_MUL THEN UNDISCH_TAC `&0 < sqrt q` THEN UNDISCH_TAC `&0 < sqrt C` THEN
          REAL_ARITH_TAC];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&2 * lam * rho` THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `rho * &1 <= rho * (&2 * lam) ==> rho <= &2 * lam * rho`) THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN UNDISCH_TAC `&0 < rho` THEN UNDISCH_TAC `&1 <= lam` THEN
      REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `T1:real = t` THENL
   [(* surgery at t: the bound at y is the cap bound *)
    FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `T1:real = t`)) THEN
    SUBGOAL_THEN `mfd_joinable (hs_top hs k,hs_atlas hs k) (z:A) y /\
                  mfd_dist (hs_top hs k,hs_atlas hs k) (hs_metric (hs:(A)rfs_history) k T1) z y
                  <= c3 * hT` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(z:A) IN W` THEN EXPAND_TAC "W" THEN REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN CONJ_TAC THENL
       [MP_TAC(ISPECL [`hs_top (hs:(A)rfs_history) k`; `hs_atlas (hs:(A)rfs_history) k`;
                       `z:A`; `y:A`] MFD_JOINABLE_SYM) THEN ASM_REWRITE_TAC[];
        MP_TAC(ISPECL [`hs_top (hs:(A)rfs_history) k`; `hs_atlas (hs:(A)rfs_history) k`;
                       `hs_metric (hs:(A)rfs_history) k T1`; `z:A`; `y:A`] MFD_DIST_SYM) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    REMOVE_THEN "near" (MP_TAC o SPECL [`y:A`; `l:num`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(Cc * Kp pow 4) * q pow (l + 2)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `Cc * inv(hT pow 2) pow (l + 2)` THEN
      ASM_REWRITE_TAC[] THEN USE_THEN "kq" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_POW_LE; REAL_LT_IMP_LE] THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* T_k < t: Shi with initial data on W from T_k *)
  SUBGOAL_THEN `T1 < t` ASSUME_TAC THENL [UNDISCH_TAC `~(T1:real = t)` THEN
    UNDISCH_TAC `T1:real <= t` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> concl th = `~(T1:real = t)`)) THEN
  SUBGOAL_THEN
   `mfd_diffeo (rfs_top_at hs T1) (rfs_atlas_at hs T1) W
               (rfs_top_at hs t) (rfs_atlas_at (hs:(A)rfs_history) t) W (\y:A. y) (\y. y) /\
    p2c_vflow_from (rfs_view hs) W T1 t`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o el 4 o CONJUNCTS o GEN_REWRITE_RULE I [p2c_regular_view] o
        check (fun th -> can (find_term (fun t -> is_const t &&
          fst(dest_const t) = "p2c_regular_view")) (concl th))) THEN
      REWRITE_TAC[P2C_RFS_VIEW_PARTS] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC P2C_REGULAR_VFLOW_FROM THEN REWRITE_TAC[P2C_RFS_VIEW_PARTS] THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `riemannian_metric (restrict_atlas (rfs_atlas_at hs t) W)
      (p2c_vfam (rfs_view (hs:(A)rfs_history)) W t T1)` ASSUME_TAC THENL
   [UNDISCH_TAC `p2c_vflow_from (rfs_view (hs:(A)rfs_history)) W T1 t` THEN
    REWRITE_TAC[p2c_vflow_from; ricci_flow_from; P2C_RFS_VIEW_PARTS] THEN SIMP_TAC[];
    ALL_TAC] THEN
  (* the metric comparison down to T1 *)
  SUBGOAL_THEN
   `!w v. (w:A) IN W
          ==> v dot (p2c_vfam (rfs_view (hs:(A)rfs_history)) W t T1 w ** v) <=
              lam pow 2 * (v dot (p2c_vfam (rfs_view hs) W t t w ** v))`
  (LABEL_TAC "scmp") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`rfs_view (hs:(A)rfs_history)`; `W:A->bool`; `T1:real`; `t:real`;
                   `Krm * q`; `w:A`; `v:real^3`] RFA_HC2_START_COMPARE) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[P2C_RFS_VIEW_PARTS] THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
      TRY(MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC) THEN
      REPEAT STRIP_TAC THEN USE_THEN "rm" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      DISCH_THEN(MP_TAC o CONJUNCT1)] THEN
    MATCH_MP_TAC(REAL_ARITH `b <= c ==> a <= b ==> a <= c`) THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
     [EXPAND_TAC "lam" THEN REWRITE_TAC[GSYM REAL_EXP_N; REAL_EXP_MONO_LE] THEN
      MATCH_MP_TAC(REAL_ARITH
       `(&4 * Krm) * (q * (t - T1)) <= (&4 * Krm) * tau0
        ==> &4 * (Krm * q) * (t - T1) <= &2 * &2 * Krm * tau0`) THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [UNDISCH_TAC `&0 < Krm` THEN
        REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LT_IMP_LE THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
      ASM_SIMP_TAC[GSYM REAL_LT_RDIV_EQ];
      MATCH_MP_TAC P2AP_QFORM_NONNEG THEN
      MAP_EVERY EXISTS_TAC
       [`subtopology (rfs_top_at (hs:(A)rfs_history) t) W`;
        `restrict_atlas (rfs_atlas_at (hs:(A)rfs_history) t) W`] THEN
      REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER] THEN
      SUBGOAL_THEN `(w:A) IN topspace(rfs_top_at hs t)` ASSUME_TAC THENL
       [MP_TAC(ISPECL [`rfs_top_at (hs:(A)rfs_history) t`; `W:A->bool`] OPEN_IN_SUBSET) THEN
        ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(w:A) IN W` THEN SET_TAC[];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC SMOOTH_MANIFOLD_ATLAS_RESTRICT THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[p2c_vfam; ETA_AX; P2C_RFS_VIEW_PARTS] THEN
        MATCH_MP_TAC RIEMANNIAN_METRIC_RESTRICT THEN
        EXISTS_TAC `rfs_top_at (hs:(A)rfs_history) t` THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  (* distances at T1 from y *)
  SUBGOAL_THEN
   `!p. (p:A) IN W
        ==> mfd_joinable (hs_top hs k,hs_atlas hs k) y p /\
            mfd_dist (hs_top hs k,hs_atlas hs k) (hs_metric (hs:(A)rfs_history) k T1) y p
            <= lam * rho`
  (LABEL_TAC "sdist") THENL
   [X_GEN_TAC `p:A` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`rfs_view (hs:(A)rfs_history)`; `W:A->bool`; `T1:real`; `t:real`; `y:A`;
                   `p:A`; `rho:real`; `lam:real`] RFA_HC2_START_DIST) THEN
    REWRITE_TAC[P2C_RFS_VIEW_PARTS] THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[SUBSET_REFL] THEN REPEAT CONJ_TAC THEN
      FIRST [FIRST_ASSUM ACCEPT_TAC;
             REPEAT STRIP_TAC THEN USE_THEN "scmp" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
             NO_TAC;
             UNDISCH_TAC `&1 <= lam` THEN REAL_ARITH_TAC];
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* the initial bounds on W at T1 *)
  SUBGOAL_THEN
   `!j p. j <= 2 /\ (p:A) IN W
          ==> rfa_rmd2 j (rfs_atlas_at hs T1) (rfs_metric_at (hs:(A)rfs_history) T1) p <=
              Ksh * q pow (j + 2)`
  (LABEL_TAC "init") THENL
   [MAP_EVERY X_GEN_TAC [`j:num`; `p:A`] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "sdist" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(z:A) IN W`))) THEN STRIP_TAC THEN
    USE_THEN "sdist" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(p:A) IN W`))) THEN STRIP_TAC THEN
    SUBGOAL_THEN `smooth_manifold_atlas (hs_top hs k) (hs_atlas (hs:(A)rfs_history) k) /\
                  riemannian_metric (hs_atlas hs k) (hs_metric (hs:(A)rfs_history) k T1)`
    STRIP_ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `mfd_joinable (hs_top hs k,hs_atlas hs k) (z:A) p /\
      mfd_dist (hs_top hs k,hs_atlas hs k) (hs_metric (hs:(A)rfs_history) k T1) z p
      <= c3 * hT` STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN `mfd_joinable (hs_top hs k,hs_atlas hs k) (z:A) y` ASSUME_TAC THENL
       [MP_TAC(ISPECL [`hs_top (hs:(A)rfs_history) k`; `hs_atlas (hs:(A)rfs_history) k`;
                       `z:A`; `y:A`] MFD_JOINABLE_SYM) THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC MFD_JOINABLE_TRANS THEN EXISTS_TAC `y:A` THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `mfd_dist (hs_top hs k,hs_atlas hs k) (hs_metric (hs:(A)rfs_history) k T1) z y +
                  mfd_dist (hs_top hs k,hs_atlas hs k) (hs_metric hs k T1) y p` THEN
      CONJ_TAC THENL [MATCH_MP_TAC MFD_DIST_TRIANGLE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      MP_TAC(ISPECL [`hs_top (hs:(A)rfs_history) k`; `hs_atlas (hs:(A)rfs_history) k`;
                     `hs_metric (hs:(A)rfs_history) k T1`; `z:A`; `y:A`] MFD_DIST_SYM) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REMOVE_THEN "near" (MP_TAC o SPECL [`p:A`; `j:num`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `Cc * inv(hT pow 2) pow (j + 2)` THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(Cc * Kp pow 4) * q pow (j + 2)` THEN
    CONJ_TAC THENL
     [USE_THEN "kq" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_POW_LE; REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  (* Shi with initial data *)
  SUBGOAL_THEN
   `(y:A) IN topspace(rfs_top_at hs t) /\ q * (t - T1) <= tau0 /\
    &4 * exp(&2 * Ksh * tau0) * rs / sqrt q <= rho /\
    compact_in (rfs_top_at hs t) ((rfs_top_at (hs:(A)rfs_history) t) closure_of W) /\
    (!s w. T1 < s /\ s <= t /\ (w:A) IN W ==> p3_vrm (rfs_view hs) s w <= Ksh * q)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL [`rfs_top_at (hs:(A)rfs_history) t`; `W:A->bool`] OPEN_IN_SUBSET) THEN
      ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(y:A) IN W` THEN SET_TAC[];
      MATCH_MP_TAC REAL_LT_IMP_LE THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
      ASM_SIMP_TAC[GSYM REAL_LT_RDIV_EQ];
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN MAP_EVERY EXPAND_TAC ["rs"; "rho"] THEN
      REWRITE_TAC[SQRT_MUL] THEN
      MP_TAC(SPEC `&2 * Ksh * tau0` REAL_EXP_POS_LT) THEN
      UNDISCH_TAC `&0 < sqrt C` THEN UNDISCH_TAC `&0 < sqrt q` THEN CONV_TAC REAL_FIELD;
      MATCH_MP_TAC CLOSED_IN_COMPACT_SPACE THEN ASM_REWRITE_TAC[CLOSED_IN_CLOSURE_OF];
      REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `Krm * q` THEN
      CONJ_TAC THENL
       [USE_THEN "rm" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC REAL_LE_RMUL THEN UNDISCH_TAC `Krm <= Ksh` THEN UNDISCH_TAC `&0 < q` THEN
          REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `l = 0 \/ l = 1 \/ l = 2` MP_TAC THENL
   [UNDISCH_TAC `(l:num) <= 2` THEN ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THENL
   [REMOVE_THEN "shi0" (MP_TAC o SPECL [`rfs_view (hs:(A)rfs_history)`; `T1:real`; `t:real`;
                                        `y:A`; `q:real`; `rho:real`]);
    REMOVE_THEN "shi1" (MP_TAC o SPECL [`rfs_view (hs:(A)rfs_history)`; `T1:real`; `t:real`;
                                        `y:A`; `q:real`; `rho:real`]);
    REMOVE_THEN "shi2" (MP_TAC o SPECL [`rfs_view (hs:(A)rfs_history)`; `T1:real`; `t:real`;
                                        `y:A`; `q:real`; `rho:real`])] THEN
  REWRITE_TAC[CONJUNCT1(CONJUNCT2(SPEC_ALL P2C_VIEW_EXPAND)); P2C_RFS_VIEW_PARTS] THEN
  FIRST_ASSUM(SUBST1_TAC o check (fun th -> is_eq(concl th) &&
    rhs(concl th) = `W:A->bool`)) THEN
  (ANTS_TAC THENL
    [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
     REPEAT STRIP_TAC THEN USE_THEN "init" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
     ASM_ARITH_TAC;
     ALL_TAC]) THEN
  MATCH_MP_TAC(REAL_ARITH `b <= c ==> a <= b ==> a <= c`) THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_POW_LE; REAL_LT_IMP_LE] THEN
  REAL_ARITH_TAC);;


(* ------------------------------------------------------------------------- *)
(* The headline R13.  At y in U: the static dichotomy                        *)
(* (RFA_HC2_STATIC); in the deep case the persisting case                    *)
(* (RFA_HC2_PERSIST_RMD) or the fresh-cap case (RFA_HC2_FRESH_RMD), each a   *)
(* bound Cl R(x)^(l+2) for rfa_rmd2 l of g, i.e. Cl for R(x) g               *)
(* (RFA_HC2_RMD2_CMUL); the constants for l = 0, 1, 2 of the persisting   *)
(* case are combined (RFA_HC2_UPTO2).                                        *)
(* ------------------------------------------------------------------------- *)

let RFA_HC2_UPTO2 = prove
 (`!P:num->real->bool.
     (!l. ?C. &0 < C /\ P l C) /\ (!l C C'. P l C /\ C <= C' ==> P l C')
     ==> ?C. &0 < C /\ !l. l <= 2 ==> P l C`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(fun th -> X_CHOOSE_THEN `C0:real` STRIP_ASSUME_TAC (SPEC `0` th) THEN
                          X_CHOOSE_THEN `C1:real` STRIP_ASSUME_TAC (SPEC `1` th) THEN
                          X_CHOOSE_THEN `C2:real` STRIP_ASSUME_TAC (SPEC `2` th)) THEN
  EXISTS_TAC `max C0 (max C1 C2)` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `l:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `l = 0 \/ l = 1 \/ l = 2` MP_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_MESON_TAC[REAL_ARITH `a <= max a (max b c) /\ b <= max a (max b c) /\
                            c <= max a (max b c)`]);;

let RFA_P3_HIST_C2_BOUND = prove
 (`!u:A->bool. P2C_HISTORY_REGULAR_STATEMENT u ==> P3_HIST_C2_BOUND_STATEMENT u`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `P2C_HISTORY_REGULAR_STATEMENT (:A)` ASSUME_TAC THENL
   [UNDISCH_TAC `P2C_HISTORY_REGULAR_STATEMENT (u:A->bool)` THEN
    REWRITE_TAC[P2C_HISTORY_REGULAR_STATEMENT];
    ALL_TAC] THEN
  REWRITE_TAC[P3_HIST_C2_BOUND_STATEMENT] THEN
  X_CHOOSE_THEN `es:real` (X_CHOOSE_THEN `Ks:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "static")))) (INST_TYPE [`:A`,`:A`] RFA_HC2_STATIC) THEN
  X_CHOOSE_THEN `ep:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "persist"))
    (INST_TYPE [`:A`,`:A`] RFA_HC2_PERSIST_RMD) THEN
  X_CHOOSE_THEN `ef:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "fresh"))
    (INST_TYPE [`:A`,`:A`] RFA_HC2_FRESH_RMD) THEN
  X_CHOOSE_THEN `er:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ratio"))
    (INST_TYPE [`:A`,`:A`] RFA_C2_RATIO) THEN
  EXISTS_TAC `min es (min ep (min ef er))` THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_LT_MIN] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`;
                       `g0:real^3->real^3^3`; `A0:real`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `eps <= es /\ eps <= ep /\ eps <= ef /\ eps <= er` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REMOVE_THEN "persist" (MP_TAC o SPEC `C:real`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(ISPEC
   `\l Cl. !eps hf md g0 A0 rp dl (hs:(A)rfs_history) t x U y.
       P2C_HISTORY_REGULAR_STATEMENT (:A) /\ &0 < eps /\ eps <= ep /\
       p3_struct (C,eps,hf,md,g0,A0) (rp,dl) hs /\ rp t <= eps /\
       rfs_canonical_assumption (rfs_trunc (rfs_view hs) t) C eps rp /\
       &0 <= t /\ t < rfs_horizon hs /\ x IN topspace(rfs_top_at hs t) /\
       inv(rp t pow 2) <= mfd_scalar (rfs_atlas_at hs t) (rfs_metric_at hs t) x /\
       rfs_canonical_nbhd (rfs_top_at hs t,rfs_atlas_at hs t) (rfs_metric_at hs t) C eps x U /\
       y IN U /\
       mfd_ball (rfs_top_at hs t,rfs_atlas_at hs t) (rfs_metric_at hs t) y
         (inv(&2 * sqrt(C * mfd_scalar (rfs_atlas_at hs t) (rfs_metric_at hs t) x)))
       SUBSET U /\
       rfs_persists (rfs_view hs)
         (mfd_ball (rfs_top_at hs t,rfs_atlas_at hs t) (rfs_metric_at hs t) y
           (inv(&4 * sqrt(C * mfd_scalar (rfs_atlas_at hs t) (rfs_metric_at hs t) x))))
         (t - inv(&32 * C * max C (&2)) / mfd_scalar (rfs_atlas_at hs t) (rfs_metric_at hs t) x) t
       ==> rfa_rmd2 l (rfs_atlas_at hs t) (rfs_metric_at hs t) y <=
           Cl * mfd_scalar (rfs_atlas_at hs t) (rfs_metric_at hs t) x pow (l + 2)`
   RFA_HC2_UPTO2) THEN
  ANTS_TAC THENL
   [BETA_TAC THEN CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`l:num`; `C1:real`; `C1':real`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "P1") ASSUME_TAC) THEN
    REPEAT GEN_TAC THEN
    DISCH_THEN(fun h -> STRIP_ASSUME_TAC h THEN
      USE_THEN "P1" (fun p -> MP_TAC(MATCH_MP (SPEC_ALL p) h))) THEN
    MATCH_MP_TAC(REAL_ARITH `a <= b ==> x <= a ==> x <= b`) THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_POW_LE THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv((rp:real->real) t pow 2)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_INV THEN REWRITE_TAC[REAL_LE_POW_2];
    BETA_TAC THEN DISCH_THEN(X_CHOOSE_THEN `Cp:real` (CONJUNCTS_THEN2 ASSUME_TAC
      (LABEL_TAC "PA")))] THEN
  REMOVE_THEN "fresh" (MP_TAC o SPECL [`C:real`; `md:real->real`; `g0:real^3->real^3^3`;
                                      `A0:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d0:real` (X_CHOOSE_THEN `Cf:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "FA"))))) THEN
  EXISTS_TAC `max (C pow 4 * Ks) (max Cp Cf)` THEN CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `r0:real` THEN DISCH_TAC THEN EXISTS_TAC `d0:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`rp:real->real`; `dl:real->real`; `hs:(A)rfs_history`; `t:real`;
                       `x:A`; `U:A->bool`] THEN
  STRIP_TAC THEN MAP_EVERY X_GEN_TAC [`y:A`; `l:num`] THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM rfa_rmd2] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [p3_struct]) THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `t:real`] RFA_HC2_SLICE_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(rp:real->real) t <= eps` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `t:real` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> t = `d0:real`)) (concl th))) THEN
    ASM_REWRITE_TAC[REAL_LE_REFL] THEN ANTS_TAC THENL [REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (rp:real->real) t` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < mfd_scalar (rfs_atlas_at hs t) (rfs_metric_at (hs:(A)rfs_history) t) x`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `inv((rp:real->real) t pow 2)` THEN
    ASM_SIMP_TAC[REAL_LT_INV; REAL_POW_LT];
    ALL_TAC] THEN
  USE_THEN "static" (MP_TAC o SPECL [`rfs_top_at (hs:(A)rfs_history) t`;
    `rfs_atlas_at (hs:(A)rfs_history) t`; `rfs_metric_at (hs:(A)rfs_history) t`; `C:real`;
    `eps:real`; `x:A`; `U:A->bool`; `y:A`; `l:num`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  STRIP_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `C pow 4 * Ks` THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:A) IN topspace(rfs_top_at hs t)` ASSUME_TAC THENL
   [USE_THEN "ratio" (MP_TAC o SPECL [`rfs_top_at (hs:(A)rfs_history) t`;
      `rfs_atlas_at (hs:(A)rfs_history) t`; `rfs_metric_at (hs:(A)rfs_history) t`; `C:real`;
      `eps:real`; `x:A`; `U:A->bool`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[];
      DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2) THEN UNDISCH_TAC `(y:A) IN U` THEN
      SET_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[rfa_rmd2] THEN MATCH_MP_TAC RFA_C2_NORMALIZE THEN
  EXISTS_TAC `rfs_top_at (hs:(A)rfs_history) t` THEN ASM_REWRITE_TAC[GSYM rfa_rmd2] THEN
  ASM_CASES_TAC
   `rfs_persists (rfs_view (hs:(A)rfs_history))
      (mfd_ball (rfs_top_at hs t,rfs_atlas_at hs t) (rfs_metric_at hs t) y
        (inv(&4 * sqrt(C * mfd_scalar (rfs_atlas_at hs t) (rfs_metric_at hs t) x))))
      (t - inv(&32 * C * max C (&2)) / mfd_scalar (rfs_atlas_at hs t) (rfs_metric_at hs t) x)
      t` THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `Cp * mfd_scalar (rfs_atlas_at hs t) (rfs_metric_at (hs:(A)rfs_history) t) x
                     pow (l + 2)` THEN
    CONJ_TAC THENL
     [REMOVE_THEN "PA" (MP_TAC o SPEC `l:num`) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN MATCH_MP_TAC THEN
      MAP_EVERY EXISTS_TAC [`eps:real`; `hf:real->real->real`; `md:real->real`;
                            `g0:real^3->real^3^3`; `A0:real`; `rp:real->real`; `dl:real->real`;
                            `U:A->bool`] THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_RMUL THEN
      ASM_SIMP_TAC[REAL_POW_LE; REAL_LT_IMP_LE] THEN REAL_ARITH_TAC];
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `Cf * mfd_scalar (rfs_atlas_at hs t) (rfs_metric_at (hs:(A)rfs_history) t) x
                     pow (l + 2)` THEN
    CONJ_TAC THENL
     [REMOVE_THEN "FA" MATCH_MP_TAC THEN
      MAP_EVERY EXISTS_TAC [`eps:real`; `hf:real->real->real`; `rp:real->real`;
                            `dl:real->real`; `U:A->bool`] THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_RMUL THEN
      ASM_SIMP_TAC[REAL_POW_LE; REAL_LT_IMP_LE] THEN REAL_ARITH_TAC]]);;

