(* ========================================================================= *)
(* Unit pc_p3e_orient: a smooth manifold whose connected components are all  *)
(* simply connected is orientable (the oriented atlases of the components,   *)
(* SMT_ORIENTABLE, combine because the components are open and disjoint).    *)
(* Used for the new stage of MT Lemma 15.11 (its components are simply       *)
(* connected by RFS_EVENT_SC).                                               *)
(* ========================================================================= *)

needs "src/pc_smt_orient.ml";;
needs "src/pc_rfs_history.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* The charts of the components and their union.                             *)
(* ------------------------------------------------------------------------- *)

let P3E_COMPONENT_CHARTS = prove
 (`!(top:A topology) C (A:((A->bool)#(A->real^3))->bool) U phi.
     open_in top C /\ smooth_manifold_atlas (subtopology top C) A /\ (U,phi) IN A
     ==> U SUBSET C /\ open_in top U /\ open (IMAGE phi U) /\
         homeomorphic_map (subtopology top U,subtopology euclidean (IMAGE phi U)) phi`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`subtopology top (C:A->bool)`; `A:((A->bool)#(A->real^3))->bool`;
                 `U:A->bool`; `phi:A->real^3`] SMOOTH_MANIFOLD_ATLAS_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(U:A->bool) SUBSET C` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP OPEN_IN_SUBSET) THEN
    REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_TRANS_FULL];
    UNDISCH_TAC `homeomorphic_map (subtopology (subtopology top C) U,
                                   subtopology euclidean (IMAGE (phi:A->real^3) U)) phi` THEN
    REWRITE_TAC[SUBTOPOLOGY_SUBTOPOLOGY] THEN
    SUBGOAL_THEN `(C:A->bool) INTER U = U` (fun th -> REWRITE_TAC[th]) THEN ASM SET_TAC[]]);;

let P3E_ORIENTABLE_COMPONENTS = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^3))->bool).
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ rfs_components_sc top
     ==> mfd_orientable top atlas`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!C. C IN connected_components_of top ==> open_in top (C:A->bool)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MATCH_MP_TAC OPEN_IN_CONNECTED_COMPONENTS_OF_LOCALLY_CONNECTED_SPACE THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC LOCALLY_PATH_CONNECTED_IMP_LOCALLY_CONNECTED_SPACE THEN
    ASM_MESON_TAC[GEO_MANIFOLD_LOCALLY_PATH_CONNECTED];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!C. C IN connected_components_of top
        ==> ?A. smooth_manifold_atlas (subtopology top (C:A->bool)) A /\
                smooth_manifold_atlas (subtopology top C)
                  (restrict_atlas (atlas:((A->bool)#(A->real^3))->bool) C UNION A) /\
                mfd_oriented_atlas A`
  MP_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`(:A)`; `(:3)`] SMT_ORIENTABLE) THEN
    REWRITE_TAC[SMT_ORIENTABLE_STATEMENT] THEN
    DISCH_THEN(MP_TAC o SPECL [`subtopology top (C:A->bool)`;
                               `restrict_atlas (atlas:((A->bool)#(A->real^3))->bool) C`]) THEN
    REWRITE_TAC[mfd_orientable] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_SIMP_TAC[HAUSDORFF_SPACE_SUBTOPOLOGY; SMOOTH_MANIFOLD_ATLAS_RESTRICT] THEN
    ASM_MESON_TAC[rfs_components_sc];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM]) THEN
  DISCH_THEN(X_CHOOSE_THEN `AC:(A->bool)->((A->bool)#(A->real^3))->bool`
    (LABEL_TAC "AC")) THEN
  ABBREV_TAC `A' = UNIONS {(AC:(A->bool)->((A->bool)#(A->real^3))->bool) C |
                          C IN connected_components_of (top:A topology)}` THEN
  SUBGOAL_THEN
   `!U phi. (U,phi) IN A' <=>
            ?C. C IN connected_components_of (top:A topology) /\
                ((U:A->bool),(phi:A->real^3)) IN
                (AC:(A->bool)->((A->bool)#(A->real^3))->bool) C`
  ASSUME_TAC THENL
   [EXPAND_TAC "A'" THEN REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!U phi C. C IN connected_components_of (top:A topology) /\
              ((U:A->bool),(phi:A->real^3)) IN
              (AC:(A->bool)->((A->bool)#(A->real^3))->bool) C
              ==> U SUBSET C /\ open_in top U /\ open (IMAGE phi U) /\
                  homeomorphic_map (subtopology top U,subtopology euclidean (IMAGE phi U)) phi`
  (LABEL_TAC "CH") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC P3E_COMPONENT_CHARTS THEN
    EXISTS_TAC `(AC:(A->bool)->((A->bool)#(A->real^3))->bool) C` THEN
    ASM_SIMP_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!C C' x. C IN connected_components_of (top:A topology) /\
             C' IN connected_components_of top /\
             (x:A) IN C /\ x IN C' ==> C = C'`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `C:A->bool`; `C':A->bool`]
      CONNECTED_COMPONENTS_OF_DISJOINT) THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  (* the union A' is a smooth atlas of top *)
  SUBGOAL_THEN `smooth_manifold_atlas (top:A topology)
                 (A':((A->bool)#(A->real^3))->bool)` ASSUME_TAC THENL
   [REWRITE_TAC[smooth_manifold_atlas] THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MAP_EVERY X_GEN_TAC [`U:A->bool`; `phi:A->real^3`] THEN
      DISCH_THEN(X_CHOOSE_THEN `C:A->bool` STRIP_ASSUME_TAC) THEN
      USE_THEN "CH" (MP_TAC o SPECL [`U:A->bool`; `phi:A->real^3`; `C:A->bool`]) THEN
      ASM_SIMP_TAC[];
      X_GEN_TAC `x:A` THEN DISCH_TAC THEN
      SUBGOAL_THEN `?C. C IN connected_components_of top /\ (x:A) IN C`
      STRIP_ASSUME_TAC THENL
       [MP_TAC(ISPEC `top:A topology` UNIONS_CONNECTED_COMPONENTS_OF) THEN
        ASM SET_TAC[];
        ALL_TAC] THEN
      USE_THEN "AC" (MP_TAC o SPEC `C:A->bool`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o SPEC `x:A` o CONJUNCT1 o CONJUNCT2 o CONJUNCT1 o
                 REWRITE_RULE[smooth_manifold_atlas]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `U:A->bool` (X_CHOOSE_THEN `phi:A->real^3`
        STRIP_ASSUME_TAC)) THEN
      MAP_EVERY EXISTS_TAC [`U:A->bool`; `phi:A->real^3`] THEN ASM_MESON_TAC[];
      MAP_EVERY X_GEN_TAC [`U:A->bool`; `phi:A->real^3`; `V:A->bool`; `psi:A->real^3`] THEN
      DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `C:A->bool` STRIP_ASSUME_TAC)
                                 (X_CHOOSE_THEN `C':A->bool` STRIP_ASSUME_TAC)) THEN
      ASM_CASES_TAC `C:A->bool = C'` THENL
       [FIRST_X_ASSUM SUBST_ALL_TAC THEN
        USE_THEN "AC" (MP_TAC o SPEC `C':A->bool`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        DISCH_THEN(MP_TAC o SPECL [`U:A->bool`; `phi:A->real^3`; `V:A->bool`;
                                   `psi:A->real^3`] o CONJUNCT2 o CONJUNCT2 o CONJUNCT1 o
                   REWRITE_RULE[smooth_manifold_atlas]) THEN
        ASM_REWRITE_TAC[];
        EXISTS_TAC `\y:real^3. y` THEN
        SUBGOAL_THEN `(U:A->bool) INTER V = {}` SUBST1_TAC THENL
         [USE_THEN "CH" (MP_TAC o SPECL [`U:A->bool`; `phi:A->real^3`; `C:A->bool`]) THEN
          ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
          USE_THEN "CH" (MP_TAC o SPECL [`V:A->bool`; `psi:A->real^3`; `C':A->bool`]) THEN
          ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
          MP_TAC(ISPECL [`top:A topology`; `C:A->bool`; `C':A->bool`]
            CONNECTED_COMPONENTS_OF_DISJOINT) THEN
          ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
          REWRITE_TAC[IMAGE_CLAUSES; NOT_IN_EMPTY; SMOOTH_MAP_ON_ID]]]];
    ALL_TAC] THEN
  REWRITE_TAC[mfd_orientable] THEN EXISTS_TAC `A':((A->bool)#(A->real^3))->bool` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [(* atlas UNION A' *)
    REWRITE_TAC[smooth_manifold_atlas; IN_UNION] THEN REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[smooth_manifold_atlas];
      ASM_MESON_TAC[smooth_manifold_atlas];
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`U:A->bool`; `phi:A->real^3`; `V:A->bool`; `psi:A->real^3`] THEN
    ASM_CASES_TAC `((U:A->bool),(phi:A->real^3)) IN atlas` THEN
    ASM_CASES_TAC `((V:A->bool),(psi:A->real^3)) IN atlas` THEN
    ASM_REWRITE_TAC[] THENL
     [ASM_MESON_TAC[smooth_manifold_atlas];
      DISCH_THEN(X_CHOOSE_THEN `C:A->bool` STRIP_ASSUME_TAC) THEN
      USE_THEN "CH" (MP_TAC o SPECL [`V:A->bool`; `psi:A->real^3`; `C:A->bool`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
      USE_THEN "AC" (MP_TAC o SPEC `C:A->bool`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o SPECL [`U INTER (C:A->bool)`; `phi:A->real^3`; `V:A->bool`;
                                 `psi:A->real^3`] o CONJUNCT2 o CONJUNCT2 o CONJUNCT1 o
                 CONJUNCT2 o REWRITE_RULE[smooth_manifold_atlas]) THEN
      ASM_REWRITE_TAC[IN_UNION; IN_RESTRICT_ATLAS] THEN
      ANTS_TAC THENL [DISJ1_TAC THEN EXISTS_TAC `U:A->bool` THEN ASM_REWRITE_TAC[];
                      ALL_TAC] THEN
      SUBGOAL_THEN `(U INTER C) INTER V = (U:A->bool) INTER V` SUBST1_TAC THENL
       [ASM SET_TAC[]; REWRITE_TAC[]];
      DISCH_THEN(X_CHOOSE_THEN `C:A->bool` STRIP_ASSUME_TAC) THEN
      USE_THEN "CH" (MP_TAC o SPECL [`U:A->bool`; `phi:A->real^3`; `C:A->bool`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
      USE_THEN "AC" (MP_TAC o SPEC `C:A->bool`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o SPECL [`U:A->bool`; `phi:A->real^3`; `V INTER (C:A->bool)`;
                                 `psi:A->real^3`] o CONJUNCT2 o CONJUNCT2 o CONJUNCT1 o
                 CONJUNCT2 o REWRITE_RULE[smooth_manifold_atlas]) THEN
      ASM_REWRITE_TAC[IN_UNION; IN_RESTRICT_ATLAS] THEN
      ANTS_TAC THENL [DISJ1_TAC THEN EXISTS_TAC `V:A->bool` THEN ASM_REWRITE_TAC[];
                      ALL_TAC] THEN
      SUBGOAL_THEN `(U:A->bool) INTER (V INTER C) = U INTER V` SUBST1_TAC THENL
       [ASM SET_TAC[]; REWRITE_TAC[]];
      ASM_MESON_TAC[smooth_manifold_atlas]];
    (* A' is oriented *)
    REWRITE_TAC[mfd_oriented_atlas; FORALL_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [`U:A->bool`; `phi:A->real^3`; `V:A->bool`; `psi:A->real^3`;
                         `x:A`] THEN
    ASM_REWRITE_TAC[FST; SND; IN_INTER] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `C:A->bool` STRIP_ASSUME_TAC)
      (CONJUNCTS_THEN2 (X_CHOOSE_THEN `C':A->bool` STRIP_ASSUME_TAC) STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `C:A->bool = C'` SUBST_ALL_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "CH" (MP_TAC o SPECL [`U:A->bool`; `phi:A->real^3`; `C:A->bool`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
      USE_THEN "CH" (MP_TAC o SPECL [`V:A->bool`; `psi:A->real^3`; `C':A->bool`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
      ASM SET_TAC[];
      ALL_TAC] THEN
    USE_THEN "AC" (MP_TAC o SPEC `C':A->bool`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[mfd_oriented_atlas]] THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT2 o CONJUNCT2) THEN ASM_REWRITE_TAC[IN_INTER; FST]]);;

