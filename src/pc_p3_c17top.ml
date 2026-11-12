(* ========================================================================= *)
(* Unit pc_p3_c17top: topology of the events of a history,                 *)
(* for MT Lemma 17.12 (the count of components through surgery, MT p. 410: *)
(* #components <= N0 + S(t) - D(t)).  A component of the cut-and-capped    *)
(* manifold Z that meets no cap chart is a component of the old stage X;   *)
(* hence #components(Z) <= #components(X) + 2 #necks, and the new stage    *)
(* Y = Z minus the clopen discarded part D has #components(Z) minus the    *)
(* number of discarded components.                                         *)
(*                                                                         *)
(* Generic point-set lemmas.                                                *)
(* ========================================================================= *)

needs "src/pc_rfs_history.ml";;
needs "src/pc_mfd_diff.ml";;

prioritize_real();;
type_invention_error := true;;

(* An identity homeomorphism identifies the two topologies. *)

let P3H_HOMEO_ID_EQ = prove
 (`!top1 top2:A topology.
        homeomorphic_maps (top1,top2) ((\x. x),(\x. x)) ==> top1 = top2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[homeomorphic_maps; continuous_map] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `topspace top1 = topspace (top2:A topology)` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[TOPOLOGY_EQ] THEN X_GEN_TAC `u:A->bool` THEN EQ_TAC THEN DISCH_TAC THENL
   [SUBGOAL_THEN `{x | x IN topspace top2 /\ (x:A) IN u} = u` (fun th ->
      ASM_MESON_TAC[th]) THEN
    MP_TAC(ISPECL [`top1:A topology`; `u:A->bool`] OPEN_IN_SUBSET) THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    SUBGOAL_THEN `{x | x IN topspace top1 /\ (x:A) IN u} = u` (fun th ->
      ASM_MESON_TAC[th]) THEN
    MP_TAC(ISPECL [`top2:A topology`; `u:A->bool`] OPEN_IN_SUBSET) THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[]]);;

(* A nonempty connected clopen set is a connected component. *)

let P3H_CLOPEN_COMPONENT = prove
 (`!top c:A->bool.
        connected_in top c /\ open_in top c /\ closed_in top c /\ ~(c = {})
        ==> c IN connected_components_of top`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `x:A` o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  REWRITE_TAC[connected_components_of; IN_ELIM_THM] THEN EXISTS_TAC `x:A` THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `c:A->bool`] OPEN_IN_SUBSET) THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC CONNECTED_COMPONENT_OF_UNIQUE THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `d:A->bool` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `d:A->bool`; `c:A->bool`]
                CONNECTED_IN_CLOPEN_CASES) THEN
  ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

(* Components of a smooth manifold are open. *)

let P3H_MFD_COMPONENT_OPEN = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) c.
        smooth_manifold_atlas top atlas /\ c IN connected_components_of top
        ==> open_in top c`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC OPEN_IN_CONNECTED_COMPONENTS_OF_LOCALLY_CONNECTED_SPACE THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC LOCALLY_PATH_CONNECTED_IMP_LOCALLY_CONNECTED_SPACE THEN
  MATCH_MP_TAC GEO_MANIFOLD_LOCALLY_PATH_CONNECTED THEN
  EXISTS_TAC `atlas:((A->bool)#(A->real^N))->bool` THEN ASM_REWRITE_TAC[]);;

(* A compact smooth manifold has finitely many components. *)

let P3H_MFD_COMPONENTS_FINITE = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool).
        smooth_manifold_atlas top atlas /\ compact_space top
        ==> FINITE(connected_components_of top)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [compact_space]) THEN
  REWRITE_TAC[compact_in; SUBSET_REFL] THEN
  DISCH_THEN(MP_TAC o SPEC `connected_components_of (top:A topology)`) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [ASM_MESON_TAC[P3H_MFD_COMPONENT_OPEN];
      REWRITE_TAC[UNIONS_CONNECTED_COMPONENTS_OF; SUBSET_REFL]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:(A->bool)->bool` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `f:(A->bool)->bool` THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET] THEN X_GEN_TAC `c:A->bool` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `?x:A. x IN c` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[NONEMPTY_CONNECTED_COMPONENTS_OF; MEMBER_NOT_EMPTY]; ALL_TAC] THEN
  SUBGOAL_THEN `(x:A) IN UNIONS f` MP_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
    ASM_MESON_TAC[CONNECTED_COMPONENTS_OF_SUBSET; SUBSET];
    ALL_TAC] THEN
  REWRITE_TAC[IN_UNIONS] THEN DISCH_THEN(X_CHOOSE_THEN `d:A->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(c:A->bool) = d` (fun th -> ASM_MESON_TAC[th]) THEN
  ASM_MESON_TAC[CONNECTED_COMPONENTS_OF_OVERLAP; SUBSET; MEMBER_NOT_EMPTY;
                IN_INTER]);;

(* ========================================================================= *)
(* Components of a cut-and-capped manifold.  With the identity              *)
(* maps of rfs_event_ok, the old stage minus the cut spheres and the new    *)
(* manifold minus the cap cores are the same open subspace, so a component *)
(* of Z that meets no cap chart image cp i (ball 2), cm i (ball 2) is clopen *)
(* and connected in X: a point of a cut sphere in its closure would put a   *)
(* nearby neck point, i.e. a cap chart point, into it.                      *)
(* ========================================================================= *)

let P3H_CUT_SAME_SUBSPACE = prove
 (`!topX atlasX topZ (atlasZ:((A->bool)#(A->real^3))->bool) J e cp cm.
        mfd_cut_cap topX atlasX topZ atlasZ J e cp cm (\x. x) (\x. x)
        ==> open_in topX (topspace topX DIFF mfd_cut_spheres J e) /\
            open_in topZ (topspace topZ DIFF mfd_cut_cores J cp cm) /\
            topspace topZ DIFF mfd_cut_cores J cp cm =
            topspace topX DIFF mfd_cut_spheres J e /\
            subtopology topZ (topspace topX DIFF mfd_cut_spheres J e) =
            subtopology topX (topspace topX DIFF mfd_cut_spheres J e)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mfd_cut_cap; mfd_diffeo] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `subtopology topX (topspace topX DIFF mfd_cut_spheres J (e:num->real^3->A)) =
    subtopology topZ (topspace topZ DIFF mfd_cut_cores J cp cm)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P3H_HOMEO_ID_EQ THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `topspace topZ DIFF mfd_cut_cores J cp cm =
    topspace topX DIFF mfd_cut_spheres J (e:num->real^3->A)`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o AP_TERM `topspace:A topology->A->bool`) THEN
    REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

let P3H_CORES_SUBSET_CAPS = prove
 (`!J (cp:num->real^3->A) cm.
        mfd_cut_cores J cp cm SUBSET
        UNIONS {IMAGE (cp i) (ball(vec 0,&2)) UNION IMAGE (cm i) (ball(vec 0,&2)) |
                i IN J}`,
  REWRITE_TAC[SUBSET; IN_MFD_CUT_CORES; UNIONS_GSPEC; IN_ELIM_THM; IN_UNION; IN_IMAGE;
              IN_BALL_0] THEN
  MESON_TAC[REAL_ARITH `x <= &1 ==> x < &2`]);;

let P3H_CUT_NEAR_SPHERE = prove
 (`!topX atlasX topZ (atlasZ:((A->bool)#(A->real^3))->bool) J e cp cm i y.
        mfd_cut_cap topX atlasX topZ atlasZ J e cp cm (\x. x) (\x. x) /\
        i IN J /\ y IN annulus (&1 / &2) (&2) /\ ~(norm y = &1)
        ==> e i y IN IMAGE (cp i) (ball(vec 0,&2)) \/
            e i y IN IMAGE (cm i) (ball(vec 0,&2))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mfd_cut_cap] THEN STRIP_TAC THEN
  RULE_ASSUM_TAC BETA_RULE THEN
  UNDISCH_TAC `(y:real^3) IN annulus (&1 / &2) (&2)` THEN
  REWRITE_TAC[annulus; IN_ELIM_THM] THEN STRIP_TAC THEN
  ASM_CASES_TAC `&1 < norm(y:real^3)` THENL
   [DISJ1_TAC THEN REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `y:real^3` THEN
    CONJ_TAC THENL [ALL_TAC; REWRITE_TAC[IN_BALL_0] THEN ASM_REAL_ARITH_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`i:num`; `y:real^3`] o
      check (fun th -> can (find_term ((=) `annulus (&1) (&2):real^3->bool`)) (concl th))) THEN
    ASM_REWRITE_TAC[annulus; IN_ELIM_THM];
    ALL_TAC] THEN
  DISJ2_TAC THEN REWRITE_TAC[IN_IMAGE] THEN
  EXISTS_TAC `inv(norm(y:real^3) pow 2) % y` THEN
  SUBGOAL_THEN `&0 < norm(y:real^3) /\ norm y < &1` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`i:num`; `y:real^3`] o
      check (fun th -> can (find_term ((=) `annulus (&1 / &2) (&1):real^3->bool`)) (concl th))) THEN
    REWRITE_TAC[annulus; IN_ELIM_THM] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[IN_BALL_0; NORM_MUL; REAL_ABS_INV; REAL_ABS_POW; REAL_ABS_NORM] THEN
  SUBGOAL_THEN `inv(norm(y:real^3) pow 2) * norm y = inv(norm y)` SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < norm(y:real^3)` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LT_LINV THEN ASM_REAL_ARITH_TAC);;

let P3H_CUT_CAPFREE_COMPONENT = prove
 (`!topX atlasX topZ (atlasZ:((A->bool)#(A->real^3))->bool) J e cp cm C.
        mfd_cut_cap topX atlasX topZ atlasZ J e cp cm (\x. x) (\x. x) /\
        smooth_manifold_atlas topZ atlasZ /\
        C IN connected_components_of topZ /\
        (!i. i IN J ==> DISJOINT C (IMAGE (cp i) (ball(vec 0,&2))) /\
                        DISJOINT C (IMAGE (cm i) (ball(vec 0,&2))))
        ==> C IN connected_components_of topX`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "cut") (CONJUNCTS_THEN2 (LABEL_TAC "smz")
    (CONJUNCTS_THEN2 (LABEL_TAC "comp") (LABEL_TAC "dj")))) THEN
  USE_THEN "cut" (fun th ->
    let cs = CONJUNCTS(BETA_RULE(REWRITE_RULE[mfd_cut_cap] th)) in
    LABEL_TAC "nk" (el 1 cs) THEN LABEL_TAC "cpx" (el 5 cs) THEN
    LABEL_TAC "cmx" (el 6 cs)) THEN
  USE_THEN "cut" (MP_TAC o MATCH_MP P3H_CUT_SAME_SUBSPACE) THEN
  ABBREV_TAC `W = topspace topX DIFF mfd_cut_spheres J (e:num->real^3->A)` THEN
  POP_ASSUM(LABEL_TAC "Wdef") THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "Wo") (CONJUNCTS_THEN2 (LABEL_TAC "Wzo")
    (CONJUNCTS_THEN2 (LABEL_TAC "Weq") (LABEL_TAC "seq0")))) THEN
  SUBGOAL_THEN `subtopology topX W = subtopology topZ (W:A->bool)` (LABEL_TAC "seq") THENL
   [USE_THEN "seq0" (ACCEPT_TAC o SYM); ALL_TAC] THEN
  SUBGOAL_THEN `(C:A->bool) SUBSET topspace topZ` ASSUME_TAC THENL
   [MATCH_MP_TAC CONNECTED_COMPONENTS_OF_SUBSET THEN USE_THEN "comp" ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `DISJOINT (C:A->bool) (mfd_cut_cores J cp cm)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`J:num->bool`; `cp:num->real^3->A`; `cm:num->real^3->A`]
                  P3H_CORES_SUBSET_CAPS) THEN
    USE_THEN "dj" MP_TAC THEN
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; SUBSET; UNIONS_GSPEC;
                IN_ELIM_THM; IN_UNION] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(C:A->bool) SUBSET W` ASSUME_TAC THENL
   [USE_THEN "Weq" (SUBST1_TAC o SYM) THEN
    UNDISCH_TAC `(C:A->bool) SUBSET topspace topZ` THEN
    UNDISCH_TAC `DISJOINT (C:A->bool) (mfd_cut_cores J cp cm)` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(W:A->bool) SUBSET topspace topX` ASSUME_TAC THENL
   [USE_THEN "Wdef" (SUBST1_TAC o SYM) THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `connected_in topX (C:A->bool)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`topZ:A topology`; `C:A->bool`]
                  CONNECTED_IN_CONNECTED_COMPONENTS_OF) THEN
    USE_THEN "comp" (fun th -> REWRITE_TAC[th]) THEN DISCH_TAC THEN
    SUBGOAL_THEN `connected_in (subtopology topZ W) (C:A->bool)` MP_TAC THENL
     [ASM_REWRITE_TAC[CONNECTED_IN_SUBTOPOLOGY]; ALL_TAC] THEN
    USE_THEN "seq" (SUBST1_TAC o SYM) THEN
    REWRITE_TAC[CONNECTED_IN_SUBTOPOLOGY] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `open_in topX (C:A->bool)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`topZ:A topology`; `atlasZ:((A->bool)#(A->real^3))->bool`;
                   `C:A->bool`] P3H_MFD_COMPONENT_OPEN) THEN
    USE_THEN "smz" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "comp" (fun th -> REWRITE_TAC[th]) THEN DISCH_TAC THEN
    MATCH_MP_TAC OPEN_IN_TRANS_FULL THEN EXISTS_TAC `W:A->bool` THEN
    USE_THEN "Wo" (fun th -> REWRITE_TAC[th]) THEN
    SUBGOAL_THEN `(C:A->bool) = W INTER C` SUBST1_TAC THENL
     [UNDISCH_TAC `(C:A->bool) SUBSET W` THEN SET_TAC[]; ALL_TAC] THEN
    USE_THEN "seq" SUBST1_TAC THEN
    MATCH_MP_TAC OPEN_IN_SUBTOPOLOGY_INTER_OPEN THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `closed_in topX (C:A->bool)` ASSUME_TAC THENL
   [SUBGOAL_THEN `closed_in (subtopology topX W) (C:A->bool)` MP_TAC THENL
     [SUBGOAL_THEN `(C:A->bool) = W INTER C` SUBST1_TAC THENL
       [UNDISCH_TAC `(C:A->bool) SUBSET W` THEN SET_TAC[]; ALL_TAC] THEN
      USE_THEN "seq" SUBST1_TAC THEN
      MATCH_MP_TAC CLOSED_IN_SUBTOPOLOGY_INTER_CLOSED THEN
      MATCH_MP_TAC CLOSED_IN_CONNECTED_COMPONENTS_OF THEN USE_THEN "comp" ACCEPT_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[CLOSED_IN_SUBTOPOLOGY] THEN
    DISCH_THEN(X_CHOOSE_THEN `K:A->bool` STRIP_ASSUME_TAC) THEN
    REWRITE_TAC[GSYM CLOSURE_OF_SUBSET_EQ] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `W:A->bool` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[SUBSET] THEN X_GEN_TAC `p:A` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(p:A) IN K` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`topX:A topology`; `C:A->bool`; `K:A->bool`] CLOSURE_OF_MONO) THEN
      ANTS_TAC THENL [UNDISCH_TAC `(C:A->bool) = K INTER W` THEN SET_TAC[]; ALL_TAC] THEN
      SIMP_TAC[CLOSURE_OF_CLOSED_IN; ASSUME `closed_in topX (K:A->bool)`] THEN
      UNDISCH_TAC `(p:A) IN topX closure_of C` THEN SET_TAC[];
      ALL_TAC] THEN
    ASM_CASES_TAC `(p:A) IN W` THENL
     [UNDISCH_TAC `(C:A->bool) = K INTER W` THEN UNDISCH_TAC `(p:A) IN K` THEN
      UNDISCH_TAC `(p:A) IN W` THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(p:A) IN mfd_cut_spheres J e` MP_TAC THENL
     [UNDISCH_TAC `~((p:A) IN W)` THEN USE_THEN "Wdef" (SUBST1_TAC o SYM) THEN
      UNDISCH_TAC `(p:A) IN topX closure_of C` THEN
      REWRITE_TAC[IN_CLOSURE_OF] THEN SET_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[IN_MFD_CUT_SPHERES] THEN
    DISCH_THEN(X_CHOOSE_THEN `i:num` (X_CHOOSE_THEN `x0:real^3` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `mfd_neck_chart topX atlasX ((e:num->real^3->A) i)` MP_TAC THENL
     [USE_THEN "nk" (MP_TAC o SPEC `i:num`) THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[mfd_neck_chart; mfd_param; mfd_diffeo] THEN
    DISCH_THEN(X_CHOOSE_THEN `e':A->real^3` STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC `(p:A) IN topX closure_of C` THEN REWRITE_TAC[IN_CLOSURE_OF] THEN
    DISCH_THEN(MP_TAC o SPEC `IMAGE ((e:num->real^3->A) i) (annulus (&1 / &2) (&2))` o
               CONJUNCT2) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `x0:real^3` THEN
      ASM_REWRITE_TAC[annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `q:A` STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC `(q:A) IN IMAGE ((e:num->real^3->A) i) (annulus (&1 / &2) (&2))` THEN
    REWRITE_TAC[IN_IMAGE; annulus; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
    USE_THEN "dj" (fun th -> MP_TAC(MP (SPEC `i:num` th) (ASSUME `(i:num) IN J`))) THEN
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o SPEC `q:A`) (MP_TAC o SPEC `q:A`)) THEN
    MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                   `topZ:A topology`; `atlasZ:((A->bool)#(A->real^3))->bool`;
                   `J:num->bool`; `e:num->real^3->A`; `cp:num->real^3->A`;
                   `cm:num->real^3->A`; `i:num`; `y:real^3`] P3H_CUT_NEAR_SPHERE) THEN
    USE_THEN "cut" (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[annulus; IN_ELIM_THM] THEN
    SUBGOAL_THEN `~(norm(y:real^3) = &1)` (fun th -> REWRITE_TAC[th]) THENL
     [DISCH_TAC THEN
      SUBGOAL_THEN `(q:A) IN mfd_cut_spheres J e` MP_TAC THENL
       [REWRITE_TAC[IN_MFD_CUT_SPHERES] THEN
        MAP_EVERY EXISTS_TAC [`i:num`; `y:real^3`] THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      UNDISCH_TAC `(C:A->bool) SUBSET W` THEN USE_THEN "Wdef" (SUBST1_TAC o SYM) THEN
      UNDISCH_TAC `(q:A) IN C` THEN SET_TAC[];
      ALL_TAC] THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `(q:A) IN C` THEN UNDISCH_TAC `(q:A) = e (i:num) (y:real^3)` THEN
    MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC P3H_CLOPEN_COMPONENT THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`topZ:A topology`; `C:A->bool`] NONEMPTY_CONNECTED_COMPONENTS_OF) THEN
  USE_THEN "comp" (fun th -> REWRITE_TAC[th]));;

(* ========================================================================= *)
(* Counting components.  #comp(Z) <= #comp(X) + 2 #necks; the               *)
(* complement of a clopen set keeps exactly the components disjoint from it. *)
(* ========================================================================= *)

let P3H_PARAM_IMAGE_CONNECTED = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) s (e:real^N->A).
        mfd_param top atlas s e /\ connected s
        ==> connected_in top (IMAGE e s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mfd_param; mfd_diffeo; homeomorphic_maps] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `connected_in (subtopology top (IMAGE (e:real^N->A) s)) (IMAGE e s)`
  MP_TAC THENL
   [MATCH_MP_TAC CONNECTED_IN_CONTINUOUS_MAP_IMAGE THEN
    EXISTS_TAC `subtopology euclidean (s:real^N->bool)` THEN ASM_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[CONNECTED_IN_ABSOLUTE; CONNECTED_IN_EUCLIDEAN];
    SIMP_TAC[CONNECTED_IN_SUBTOPOLOGY]]);;

let P3H_COMPONENT_EQ_OF = prove
 (`!top c (x:A). c IN connected_components_of top /\ x IN c
                 ==> c = connected_component_of top x`,
  REWRITE_TAC[connected_components_of; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  ASM_MESON_TAC[CONNECTED_COMPONENT_OF_EQUIV; IN]);;

let P3H_COMPONENT_CAP_POINT = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) b C.
        C IN connected_components_of top /\ mfd_ball_chart top atlas b /\
        ~DISJOINT C (IMAGE b (ball(vec 0,&2)))
        ==> C = connected_component_of top (b(vec 0))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC P3H_COMPONENT_EQ_OF THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `connected_in top (IMAGE (b:real^N->A) (ball(vec 0,&2)))` ASSUME_TAC THENL
   [MATCH_MP_TAC P3H_PARAM_IMAGE_CONNECTED THEN
    EXISTS_TAC `atlas:((A->bool)#(A->real^N))->bool` THEN
    ASM_REWRITE_TAC[GSYM mfd_ball_chart; CONNECTED_BALL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `IMAGE (b:real^N->A) (ball(vec 0,&2))`; `C:A->bool`]
                CONNECTED_COMPONENTS_OF_MAXIMAL) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
  DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[CENTRE_IN_BALL] THEN REAL_ARITH_TAC);;

let P3H_CUT_COMPONENTS_CARD = prove
 (`!topX atlasX topZ (atlasZ:((A->bool)#(A->real^3))->bool) J e cp cm.
        mfd_cut_cap topX atlasX topZ atlasZ J e cp cm (\x. x) (\x. x) /\
        smooth_manifold_atlas topZ atlasZ /\ compact_space topZ /\
        FINITE(connected_components_of topX)
        ==> FINITE(connected_components_of topZ) /\
            CARD(connected_components_of topZ) <=
            CARD(connected_components_of topX) + 2 * CARD J`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `FINITE(connected_components_of (topZ:A topology))` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`topZ:A topology`; `atlasZ:((A->bool)#(A->real^3))->bool`]
                  P3H_MFD_COMPONENTS_FINITE) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(fun th ->
    let cs = CONJUNCTS(REWRITE_RULE[mfd_cut_cap] th) in
    ASSUME_TAC (el 0 cs) THEN LABEL_TAC "ch" (el 1 cs)) THEN
  ABBREV_TAC
   `CF = {C | C IN connected_components_of (topZ:A topology) /\
              !i. i IN J ==> DISJOINT C (IMAGE ((cp:num->real^3->A) i) (ball(vec 0,&2))) /\
                             DISJOINT C (IMAGE ((cm:num->real^3->A) i) (ball(vec 0,&2)))}` THEN
  SUBGOAL_THEN `CF SUBSET connected_components_of (topX:A topology)` ASSUME_TAC THENL
   [EXPAND_TAC "CF" THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
    X_GEN_TAC `C:A->bool` THEN STRIP_TAC THEN
    MATCH_MP_TAC P3H_CUT_CAPFREE_COMPONENT THEN
    MAP_EVERY EXISTS_TAC [`atlasX:((A->bool)#(A->real^3))->bool`; `topZ:A topology`;
                          `atlasZ:((A->bool)#(A->real^3))->bool`; `J:num->bool`;
                          `e:num->real^3->A`; `cp:num->real^3->A`; `cm:num->real^3->A`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC
   `f = \p:num#bool. connected_component_of (topZ:A topology)
                           (if SND p then (cp:num->real^3->A) (FST p) (vec 0)
                            else (cm:num->real^3->A) (FST p) (vec 0))` THEN
  SUBGOAL_THEN
   `connected_components_of (topZ:A topology) DIFF CF SUBSET
    IMAGE (f:num#bool->A->bool) ((J:num->bool) CROSS (:bool))`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_DIFF; IN_IMAGE; EXISTS_PAIR_THM; IN_CROSS; IN_UNIV] THEN
    X_GEN_TAC `C:A->bool` THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `?i. i IN J /\ (~DISJOINT C (IMAGE ((cp:num->real^3->A) i) (ball(vec 0,&2))) \/
                     ~DISJOINT C (IMAGE ((cm:num->real^3->A) i) (ball(vec 0,&2))))`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `~((C:A->bool) IN CF)` THEN EXPAND_TAC "CF" THEN
      REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN MESON_TAC[];
      MAP_EVERY EXISTS_TAC [`i:num`; `T`] THEN ASM_REWRITE_TAC[] THEN
      EXPAND_TAC "f" THEN REWRITE_TAC[FST; SND] THEN
      MATCH_MP_TAC (INST_TYPE [`:3`,`:N`] P3H_COMPONENT_CAP_POINT) THEN
      EXISTS_TAC `atlasZ:((A->bool)#(A->real^3))->bool` THEN
      REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "ch" (MP_TAC o SPEC `i:num`) THEN ASM_SIMP_TAC[];
      MAP_EVERY EXISTS_TAC [`i:num`; `F`] THEN ASM_REWRITE_TAC[] THEN
      EXPAND_TAC "f" THEN REWRITE_TAC[FST; SND] THEN
      MATCH_MP_TAC (INST_TYPE [`:3`,`:N`] P3H_COMPONENT_CAP_POINT) THEN
      EXISTS_TAC `atlasZ:((A->bool)#(A->real^3))->bool` THEN
      REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "ch" (MP_TAC o SPEC `i:num`) THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE(CF:(A->bool)->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `connected_components_of (topX:A topology)` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `CARD(connected_components_of (topZ:A topology) DIFF CF) <= 2 * CARD(J:num->bool)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC `CARD(IMAGE (f:num#bool->A->bool) ((J:num->bool) CROSS (:bool)))` THEN CONJ_TAC THENL
     [MATCH_MP_TAC CARD_SUBSET THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC FINITE_IMAGE THEN ASM_SIMP_TAC[FINITE_CROSS; FINITE_BOOL];
      ALL_TAC] THEN
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `CARD((J:num->bool) CROSS (:bool))` THEN CONJ_TAC THENL
     [MATCH_MP_TAC CARD_IMAGE_LE THEN ASM_SIMP_TAC[FINITE_CROSS; FINITE_BOOL];
      ASM_SIMP_TAC[CARD_CROSS; FINITE_BOOL; CARD_BOOL] THEN ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `CARD(CF:(A->bool)->bool) <= CARD(connected_components_of (topX:A topology))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CARD_SUBSET THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `CARD(connected_components_of (topZ:A topology)) =
    CARD(CF:(A->bool)->bool) + CARD(connected_components_of topZ DIFF CF)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC(ARITH_RULE `a + b = c:num ==> c = a + b`) THEN
    MATCH_MP_TAC CARD_UNION_EQ THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "CF" THEN SET_TAC[];
    ASM_ARITH_TAC]);;

(* The complement of a clopen set: its components are the components of the *)
(* space that miss the set. *)

let P3H_CLOPEN_COMPLEMENT_COMPONENTS = prove
 (`!top (D:A->bool).
        open_in top D /\ closed_in top D
        ==> connected_components_of (subtopology top (topspace top DIFF D)) =
            {C | C IN connected_components_of top /\ DISJOINT C D}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
  X_GEN_TAC `C:A->bool` THEN EQ_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `(C:A->bool) SUBSET topspace top DIFF D` ASSUME_TAC THENL
     [FIRST_ASSUM(MP_TAC o MATCH_MP CONNECTED_COMPONENTS_OF_SUBSET) THEN
      REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN SET_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL [ALL_TAC; UNDISCH_TAC `(C:A->bool) SUBSET topspace top DIFF D` THEN
                    SET_TAC[]] THEN
    SUBGOAL_THEN `connected_in top (C:A->bool)` ASSUME_TAC THENL
     [FIRST_ASSUM(MP_TAC o MATCH_MP CONNECTED_IN_CONNECTED_COMPONENTS_OF) THEN
      SIMP_TAC[CONNECTED_IN_SUBTOPOLOGY];
      ALL_TAC] THEN
    SUBGOAL_THEN `?x:A. x IN C` STRIP_ASSUME_TAC THENL
     [FIRST_ASSUM(MP_TAC o MATCH_MP NONEMPTY_CONNECTED_COMPONENTS_OF) THEN
      SET_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[connected_components_of; IN_ELIM_THM] THEN EXISTS_TAC `x:A` THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `(C:A->bool) SUBSET topspace top DIFF D` THEN
      UNDISCH_TAC `(x:A) IN C` THEN SET_TAC[];
      ALL_TAC] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC CONNECTED_COMPONENT_OF_UNIQUE THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `C':A->bool` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `C':A->bool`; `D:A->bool`]
                  CONNECTED_IN_CLOPEN_CASES) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
     [UNDISCH_TAC `(C:A->bool) SUBSET topspace top DIFF D` THEN
      UNDISCH_TAC `(x:A) IN C` THEN UNDISCH_TAC `(x:A) IN C'` THEN
      UNDISCH_TAC `(C':A->bool) SUBSET D` THEN SET_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`subtopology top (topspace top DIFF D:A->bool)`; `C':A->bool`;
                   `C:A->bool`] CONNECTED_COMPONENTS_OF_MAXIMAL) THEN
    ASM_REWRITE_TAC[CONNECTED_IN_SUBTOPOLOGY] THEN DISCH_THEN MATCH_MP_TAC THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `C':A->bool`] CONNECTED_IN_SUBSET_TOPSPACE) THEN
      ASM_REWRITE_TAC[] THEN UNDISCH_TAC `DISJOINT (C':A->bool) D` THEN SET_TAC[];
      UNDISCH_TAC `(x:A) IN C` THEN UNDISCH_TAC `(x:A) IN C'` THEN SET_TAC[]];
    STRIP_TAC THEN MATCH_MP_TAC CONNECTED_COMPONENTS_OF_SUBTOPOLOGY THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP CONNECTED_COMPONENTS_OF_SUBSET) THEN
    UNDISCH_TAC `DISJOINT (C:A->bool) D` THEN SET_TAC[]]);;

(* ========================================================================= *)
(* Components through one event of a history.  With X the old              *)
(* stage, Z the cut-and-capped manifold, D the discarded part and Y = Z - D: *)
(* #comp(Y) + #(components of Z inside D) <= #comp(X) + 2 #necks; D contains *)
(* a component as soon as it is nonempty, in particular when there is a    *)
(* neck (its plus cap is discarded).                                        *)
(* ========================================================================= *)

let P3H_EVENT_COMPONENTS = prove
 (`!topX atlasX (gX:real->A->real^3^3) ts topY atlasY gY ev.
        rfs_event_ok (topX,atlasX) gX ts (topY,atlasY) gY ev /\
        FINITE(connected_components_of topX)
        ==> FINITE(connected_components_of topY) /\
            FINITE {C | C IN connected_components_of (ev_ztop ev) /\ C SUBSET ev_disc ev} /\
            CARD(connected_components_of topY) +
            CARD {C | C IN connected_components_of (ev_ztop ev) /\ C SUBSET ev_disc ev}
            <= CARD(connected_components_of topX) + 2 * CARD(ev_index ev) /\
            (~(ev_disc ev = {})
             ==> 1 <= CARD {C | C IN connected_components_of (ev_ztop ev) /\
                                C SUBSET ev_disc ev}) /\
            (~(ev_index ev = {}) ==> ~(ev_disc ev = {}))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rfs_event_ok] THEN STRIP_TAC THEN
  ABBREV_TAC `Z = ev_ztop (ev:(A)rfs_event)` THEN
  ABBREV_TAC `D = ev_disc (ev:(A)rfs_event)` THEN
  MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                 `Z:A topology`; `ev_zatlas (ev:(A)rfs_event)`; `ev_index (ev:(A)rfs_event)`;
                 `ev_neck (ev:(A)rfs_event)`; `ev_capp (ev:(A)rfs_event)`;
                 `ev_capm (ev:(A)rfs_event)`] P3H_CUT_COMPONENTS_CARD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `connected_components_of (subtopology Z (topspace Z DIFF D:A->bool)) =
    {C | C IN connected_components_of Z /\ DISJOINT C D}`
  (LABEL_TAC "cy") THENL
   [MATCH_MP_TAC P3H_CLOPEN_COMPLEMENT_COMPONENTS THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!C:A->bool. C IN connected_components_of Z ==> C SUBSET D \/ DISJOINT C D`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`Z:A topology`; `C:A->bool`; `D:A->bool`] CONNECTED_IN_CLOPEN_CASES) THEN
    ASM_SIMP_TAC[CONNECTED_IN_CONNECTED_COMPONENTS_OF];
    ALL_TAC] THEN
  ABBREV_TAC `CY = {C | C IN connected_components_of Z /\ DISJOINT C (D:A->bool)}` THEN
  ABBREV_TAC `CD = {C | C IN connected_components_of Z /\ C SUBSET (D:A->bool)}` THEN
  SUBGOAL_THEN `FINITE(CY:(A->bool)->bool) /\ FINITE(CD:(A->bool)->bool)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `connected_components_of (Z:A topology)` THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY EXPAND_TAC ["CY"; "CD"] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `CARD(CY:(A->bool)->bool) + CARD(CD:(A->bool)->bool) =
    CARD(connected_components_of (Z:A topology))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CARD_UNION_EQ THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY EXPAND_TAC ["CY"; "CD"] THEN CONJ_TAC THEN
   (REWRITE_TAC[EXTENSION; IN_INTER; IN_UNION; IN_ELIM_THM; NOT_IN_EMPTY] THEN
    X_GEN_TAC `C:A->bool` THEN
    ASM_CASES_TAC `(C:A->bool) IN connected_components_of Z` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~((C:A->bool) = {})` MP_TAC THENL
     [ASM_MESON_TAC[NONEMPTY_CONNECTED_COMPONENTS_OF]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `C:A->bool` o
      check (fun th -> can (find_term ((=) `DISJOINT:(A->bool)->(A->bool)->bool`))
                           (concl th) && is_forall(concl th))) THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[]);
    ALL_TAC] THEN
  SUBGOAL_THEN `~(ev_index (ev:(A)rfs_event) = {}) ==> ~(D:A->bool = {})`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    DISCH_THEN(X_CHOOSE_TAC `i:num`) THEN
    EXISTS_TAC `ev_capp (ev:(A)rfs_event) i (vec 0)` THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o
      check (fun th -> can (find_term ((=) `ev_capp (ev:(A)rfs_event)`)) (concl th) &&
                       can (find_term ((=) `cball(vec 0:real^3,&1)`)) (concl th) &&
                       is_forall(concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1) THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[CENTRE_IN_CBALL] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(D:A->bool = {}) ==> 1 <= CARD(CD:(A->bool)->bool)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN DISCH_THEN(X_CHOOSE_TAC `p:A`) THEN
    REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`] THEN
    ASM_SIMP_TAC[CARD_EQ_0] THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    EXISTS_TAC `connected_component_of Z (p:A)` THEN EXPAND_TAC "CD" THEN
    REWRITE_TAC[IN_ELIM_THM] THEN
    SUBGOAL_THEN `(p:A) IN topspace Z` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL
     [ASM_SIMP_TAC[CONNECTED_COMPONENT_IN_CONNECTED_COMPONENTS_OF]; ALL_TAC] THEN
    MP_TAC(ISPECL [`Z:A topology`; `connected_component_of Z (p:A)`; `D:A->bool`]
                  CONNECTED_IN_CLOPEN_CASES) THEN
    ASM_REWRITE_TAC[CONNECTED_IN_CONNECTED_COMPONENT_OF] THEN
    MATCH_MP_TAC(TAUT `~q ==> p \/ q ==> p`) THEN
    REWRITE_TAC[DISJOINT; GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
    EXISTS_TAC `p:A` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[IN] THEN ASM_SIMP_TAC[CONNECTED_COMPONENT_OF_REFL];
    ALL_TAC] THEN
  USE_THEN "cy" (fun th -> REWRITE_TAC[th]) THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
  UNDISCH_TAC
   `CARD(CY:(A->bool)->bool) + CARD(CD:(A->bool)->bool) =
    CARD(connected_components_of (Z:A topology))` THEN
  UNDISCH_TAC
   `CARD(connected_components_of (Z:A topology)) <=
    CARD(connected_components_of (topX:A topology)) + 2 * CARD(ev_index (ev:(A)rfs_event))` THEN
  ARITH_TAC);;

(* ========================================================================= *)
(* The component count over a history (MT p. 410:                          *)
(* #components <= N0 + S(t) - D(t)).  If every event discards something,   *)
(* the number of events is at most #comp(stage 0) + 2 x (number of necks).  *)
(* ========================================================================= *)

let P3H_HIST_COMPONENTS_COUNT = prove
 (`!hs:(A)rfs_history.
        rfs_history_ok hs /\
        (!k. 1 <= k /\ k <= hs_count hs ==> ~(ev_disc(hs_event hs k) = {}))
        ==> hs_count hs <=
            CARD(connected_components_of (hs_top hs 0)) +
            2 * nsum(1..hs_count hs) (\k. CARD(ev_index(hs_event hs k)))`,
  GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "nd")) THEN
  SUBGOAL_THEN
   `!n. n <= hs_count (hs:(A)rfs_history)
        ==> FINITE(connected_components_of (hs_top hs n)) /\
            CARD(connected_components_of (hs_top hs n)) + n <=
            CARD(connected_components_of (hs_top hs 0)) +
            2 * nsum(1..n) (\k. CARD(ev_index(hs_event hs k)))`
  (fun th -> MP_TAC(SPEC `hs_count (hs:(A)rfs_history)` th) THEN
             REWRITE_TAC[LE_REFL] THEN ARITH_TAC) THEN
  SUBGOAL_THEN
   `!k. k <= hs_count (hs:(A)rfs_history)
        ==> smooth_manifold_atlas (hs_top hs k) (hs_atlas hs k) /\
            compact_space (hs_top hs k)`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[rfs_history_ok]; ALL_TAC] THEN
  INDUCT_TAC THENL
   [DISCH_TAC THEN REWRITE_TAC[NSUM_CLAUSES_NUMSEG; ARITH_RULE `~(1 = 0)`] THEN
    CONJ_TAC THENL [ALL_TAC; ARITH_TAC] THEN
    MP_TAC(ISPECL [`hs_top (hs:(A)rfs_history) 0`; `hs_atlas (hs:(A)rfs_history) 0`]
                  P3H_MFD_COMPONENTS_FINITE) THEN
    ASM_SIMP_TAC[LE_0];
    ALL_TAC] THEN
  DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `SUC n <= hs_count (hs:(A)rfs_history)` THEN ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `rfs_event_ok (hs_top hs n,hs_atlas hs n) (hs_metric hs n) (hs_time hs (SUC n))
                 (hs_top hs (SUC n),hs_atlas hs (SUC n)) (hs_metric hs (SUC n))
                 (hs_event (hs:(A)rfs_history) (SUC n))`
  MP_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPEC `SUC n` o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o
                GEN_REWRITE_RULE I [rfs_history_ok]) THEN
    ASM_REWRITE_TAC[ARITH_RULE `1 <= SUC n`; ARITH_RULE `SUC n - 1 = n`];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] P3H_EVENT_COMPONENTS)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `1 <= CARD {C | C IN connected_components_of (ev_ztop (hs_event hs (SUC n))) /\
                   C SUBSET ev_disc (hs_event (hs:(A)rfs_history) (SUC n))}`
  MP_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN USE_THEN "nd" MATCH_MP_TAC THEN
    UNDISCH_TAC `SUC n <= hs_count (hs:(A)rfs_history)` THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[NSUM_CLAUSES_NUMSEG; ARITH_RULE `1 <= SUC n`] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (fun th ->
    let c = concl th in
    not(is_forall c) && not(is_imp c) &&
    can (find_term (fun t -> t = `(<=):num->num->bool`)) c))) THEN
  ARITH_TAC);;

(* ========================================================================= *)
(* The new stage of an event is the retained old part plus the              *)
(* closed cores of the minus caps, all pairwise disjoint; the positive cap  *)
(* charts lie in the discarded part.                                        *)
(* ========================================================================= *)

let P3H_CUT_CORES_SPLIT = prove
 (`!J (cp:num->real^3->A) cm.
        mfd_cut_cores J cp cm =
        UNIONS {IMAGE (cp i) (cball(vec 0,&1)) | i IN J} UNION
        UNIONS {IMAGE (cm i) (cball(vec 0,&1)) | i IN J}`,
  REWRITE_TAC[mfd_cut_cores; UNIONS_GSPEC; EXTENSION; IN_ELIM_THM; IN_UNION] THEN
  MESON_TAC[]);;

let P3H_DECOMP_SETS = prove
 (`!TX TZ D Co S CP CM:A->bool.
        TZ DIFF Co = TX DIFF S /\ DISJOINT TX Co /\ Co = CP UNION CM /\
        CP SUBSET D /\ DISJOINT CM D /\ CM SUBSET TZ
        ==> TZ DIFF D = ((TZ DIFF D) INTER TX) UNION CM /\
            DISJOINT ((TZ DIFF D) INTER TX) CM`,
  SET_TAC[]);;

let P3H_EVENT_STAGE_DECOMP = prove
 (`!topX atlasX (gX:real->A->real^3^3) ts topY atlasY gY ev.
        rfs_event_ok (topX,atlasX) gX ts (topY,atlasY) gY ev
        ==> topspace topY =
            (topspace topY INTER topspace topX) UNION
            UNIONS {IMAGE (ev_capm ev i) (cball(vec 0,&1)) | i | i IN ev_index ev} /\
            DISJOINT (topspace topY INTER topspace topX)
                     (UNIONS {IMAGE (ev_capm ev i) (cball(vec 0,&1)) | i | i IN ev_index ev}) /\
            (!i j. i IN ev_index ev /\ j IN ev_index ev /\ ~(i = j)
                   ==> DISJOINT (IMAGE (ev_capm ev i) (cball(vec 0,&1)))
                                (IMAGE (ev_capm ev j) (cball(vec 0,&1)))) /\
            (!i. i IN ev_index ev
                 ==> IMAGE (ev_capm ev i) (cball(vec 0,&1)) SUBSET topspace topY)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rfs_event_ok] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                 `ev_ztop (ev:(A)rfs_event)`; `ev_zatlas (ev:(A)rfs_event)`;
                 `ev_index (ev:(A)rfs_event)`; `ev_neck (ev:(A)rfs_event)`;
                 `ev_capp (ev:(A)rfs_event)`; `ev_capm (ev:(A)rfs_event)`]
                P3H_CUT_SAME_SUBSPACE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(fun th ->
    let cs = CONJUNCTS(REWRITE_RULE[mfd_cut_cap] th) in
    LABEL_TAC "ch" (el 1 cs) THEN LABEL_TAC "dj" (el 3 cs)) THEN
  SUBGOAL_THEN
   `!i. i IN ev_index ev
        ==> IMAGE (ev_capm (ev:(A)rfs_event) i) (cball(vec 0,&1)) SUBSET
            topspace(ev_ztop ev)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    USE_THEN "ch" (fun th -> MP_TAC(MP (SPEC `i:num` th)
                                       (ASSUME `i IN ev_index (ev:(A)rfs_event)`))) THEN
    REWRITE_TAC[mfd_ball_chart; mfd_param; mfd_diffeo] THEN STRIP_TAC THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `IMAGE (ev_capm (ev:(A)rfs_event) i) (ball(vec 0,&2))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[SUBSET; IN_CBALL_0; IN_BALL_0] THEN
      REAL_ARITH_TAC;
      MATCH_MP_TAC OPEN_IN_SUBSET THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_cut_cores (ev_index ev) (ev_capp ev) (ev_capm (ev:(A)rfs_event)) =
    UNIONS {IMAGE (ev_capp ev i) (cball(vec 0,&1)) | i | i IN ev_index ev} UNION
    UNIONS {IMAGE (ev_capm ev i) (cball(vec 0,&1)) | i | i IN ev_index ev}`
  ASSUME_TAC THENL
   [REWRITE_TAC[P3H_CUT_CORES_SPLIT];
    ALL_TAC] THEN
  FIRST_X_ASSUM(fun th ->
    if can (find_term ((=) `ev_capp (ev:(A)rfs_event)`)) (concl th) &&
       can (find_term ((=) `ev_disc (ev:(A)rfs_event)`)) (concl th) &&
       is_forall(concl th)
    then LABEL_TAC "cd" th else failwith "no") THEN
  SUBGOAL_THEN
   `UNIONS {IMAGE (ev_capp ev i) (cball(vec 0,&1)) | i | i IN ev_index ev} SUBSET
    ev_disc (ev:(A)rfs_event)`
  ASSUME_TAC THENL
   [REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC] THEN
    USE_THEN "cd" (fun th -> MESON_TAC[th]);
    ALL_TAC] THEN
  SUBGOAL_THEN
   `DISJOINT (UNIONS {IMAGE (ev_capm ev i) (cball(vec 0,&1)) | i | i IN ev_index ev})
             (ev_disc (ev:(A)rfs_event))`
  ASSUME_TAC THENL
   [REWRITE_TAC[FORALL_IN_GSPEC;
                SET_RULE `DISJOINT (UNIONS f) (s:A->bool) <=> !t. t IN f ==> DISJOINT t s`] THEN
    USE_THEN "cd" (fun th -> MESON_TAC[th]);
    ALL_TAC] THEN
  SUBGOAL_THEN
   `UNIONS {IMAGE (ev_capm ev i) (cball(vec 0,&1)) | i | i IN ev_index ev} SUBSET
    topspace(ev_ztop (ev:(A)rfs_event))`
  ASSUME_TAC THENL
   [REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`topspace(topX:A topology)`; `topspace(ev_ztop (ev:(A)rfs_event))`;
                 `ev_disc (ev:(A)rfs_event)`;
                 `mfd_cut_cores (ev_index ev) (ev_capp ev) (ev_capm (ev:(A)rfs_event))`;
                 `mfd_cut_spheres (ev_index ev) (ev_neck (ev:(A)rfs_event))`;
                 `UNIONS {IMAGE (ev_capp ev i) (cball(vec 0,&1)) | i | i IN ev_index (ev:(A)rfs_event)}`;
                 `UNIONS {IMAGE (ev_capm ev i) (cball(vec 0,&1)) | i | i IN ev_index (ev:(A)rfs_event)}`]
                P3H_DECOMP_SETS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN
  SUBGOAL_THEN `topspace(ev_ztop (ev:(A)rfs_event)) INTER
                (topspace(ev_ztop ev) DIFF ev_disc ev) =
                topspace(ev_ztop ev) DIFF ev_disc ev` SUBST1_TAC THENL
   [SET_TAC[]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    REPEAT STRIP_TAC THEN
    USE_THEN "dj" (fun th -> MP_TAC(MP (SPECL [`i:num`; `j:num`] th)
       (CONJ (ASSUME `i IN ev_index (ev:(A)rfs_event)`)
             (ASSUME `j IN ev_index (ev:(A)rfs_event)`)))) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o CONJUNCT2 o CONJUNCT2) THEN
    MATCH_MP_TAC(SET_RULE `(s:A->bool) SUBSET s' /\ (t:A->bool) SUBSET t' ==> DISJOINT s' t' ==> DISJOINT s t`) THEN
    CONJ_TAC THEN MATCH_MP_TAC IMAGE_SUBSET THEN
    REWRITE_TAC[SUBSET; IN_CBALL_0; IN_BALL_0] THEN REAL_ARITH_TAC;
    REPEAT STRIP_TAC THEN
    UNDISCH_TAC `!i. i IN ev_index (ev:(A)rfs_event)
                     ==> IMAGE (ev_capp ev i) (cball (vec 0,&1)) SUBSET ev_disc ev /\
                         DISJOINT (IMAGE (ev_capm ev i) (cball (vec 0,&1))) (ev_disc ev)` THEN
    DISCH_THEN(MP_TAC o SPEC `i:num`) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o
      check (fun th -> can (find_term ((=) `topspace(ev_ztop (ev:(A)rfs_event))`)) (concl th) &&
                       is_forall(concl th))) THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[]]);;

