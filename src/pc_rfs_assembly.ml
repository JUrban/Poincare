(* ========================================================================= *)
(* Unit pc_rfs_assembly: the assembly of the smooth Poincare theorem.  From  *)
(* the top statement constants of pc_rfs_top (as hypotheses) and the         *)
(* smooth-topology conversion statement SMT_POINCARE_CONVERSION_STATEMENT,   *)
(* the smooth Poincare statement POINCARE_SMOOTH_STATEMENT (:A) for every    *)
(* type A (RFS_POINCARE_SMOOTH).  Route: metric existence, a controlled      *)
(* extinct history on A + num#num#real^3 (RFS_EXTINCTION_STATEMENT), forward *)
(* induction: all components of all stages and capped manifolds stay simply  *)
(* connected (RFS_CUTCAP_SC_STATEMENT); discarded components are listed      *)
(* (EVENT_TOPOLOGY_STATEMENT), hence S^3 (RFS_LISTED_SC_S3_STATEMENT);       *)
(* backward induction from the empty last stage with the componentwise       *)
(* sphere-system statement (RFS_SPHERE_SYSTEM_STATEMENT); stage 0 is S^3,    *)
(* and so is the initial manifold.                                           *)
(* ========================================================================= *)

needs "src/pc_rfs_top.ml";;
needs "src/pc_audit_sanity.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Restricted atlases, components of clopen subspaces, connected spaces.     *)
(* ------------------------------------------------------------------------- *)

let RFS_RESTRICT_ATLAS_RESTRICT = prove
 (`!(atlas:((A->bool)#(A->real^N))->bool) W U.
        restrict_atlas (restrict_atlas atlas W) U = restrict_atlas atlas (W INTER U)`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN
  REWRITE_TAC[FORALL_PAIR_THM; IN_RESTRICT_ATLAS] THEN
  MAP_EVERY X_GEN_TAC [`V:A->bool`; `psi:A->real^N`] THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `V1:A->bool` (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `V2:A->bool` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
    EXISTS_TAC `V2:A->bool` THEN ASM_REWRITE_TAC[INTER_ASSOC];
    DISCH_THEN(X_CHOOSE_THEN `V2:A->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `V2 INTER (W:A->bool)` THEN CONJ_TAC THENL
     [EXISTS_TAC `V2:A->bool` THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[INTER_ASSOC]]]);;

let RFS_COMPONENTS_CLOPEN = prove
 (`!top (W:A->bool) U.
        open_in top W /\ closed_in top W /\
        U IN connected_components_of (subtopology top W)
        ==> U IN connected_components_of top`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[connected_components_of; IN_ELIM_THM; TOPSPACE_SUBTOPOLOGY; IN_INTER] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `x:A` STRIP_ASSUME_TAC))) THEN
  EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[CONNECTED_COMPONENT_OF_SUBTOPOLOGY_EQ] THEN
  SUBGOAL_THEN `(x:A) IN connected_component_of top x` ASSUME_TAC THENL
   [REWRITE_TAC[IN] THEN ASM_REWRITE_TAC[CONNECTED_COMPONENT_OF_REFL]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `connected_component_of top (x:A)`; `W:A->bool`]
         CONNECTED_IN_CLOPEN_CASES) THEN
  ASM_REWRITE_TAC[CONNECTED_IN_CONNECTED_COMPONENT_OF] THEN ASM SET_TAC[]);;

let RFS_COMPONENTS_SC_CLOPEN = prove
 (`!top (W:A->bool).
        rfs_components_sc top /\ open_in top W /\ closed_in top W
        ==> rfs_components_sc (subtopology top W)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rfs_components_sc] THEN
  X_GEN_TAC `U:A->bool` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(U:A->bool) SUBSET W` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP CONNECTED_COMPONENTS_OF_SUBSET) THEN
    REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[SUBTOPOLOGY_SUBTOPOLOGY] THEN
  SUBGOAL_THEN `W INTER U = (U:A->bool)` SUBST1_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[rfs_components_sc] o
    check (fun th -> is_comb(concl th) &&
                     fst(dest_const(rator(concl th))) = "rfs_components_sc")) THEN
  MATCH_MP_TAC RFS_COMPONENTS_CLOPEN THEN EXISTS_TAC `W:A->bool` THEN
  ASM_REWRITE_TAC[]);;

let RFS_COMPONENTS_SC_CONNECTED = prove
 (`!top:A topology.
        simply_connected_space top /\ connected_space top
        ==> rfs_components_sc top`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rfs_components_sc] THEN
  ASM_SIMP_TAC[CONNECTED_COMPONENTS_OF_CONNECTED_SPACE] THEN
  COND_CASES_TAC THEN REWRITE_TAC[NOT_IN_EMPTY; IN_SING] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[SUBTOPOLOGY_TOPSPACE]);;

let RFS_COMPONENTS_S3_CONNECTED = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool).
        smooth_manifold_atlas top atlas /\ connected_space top /\
        ~(topspace top = {}) /\ rfs_components_s3 top atlas
        ==> mfd_diffeomorphic top atlas
              (subtopology euclidean (sphere(vec 0:real^4,&1))) sphere3_atlas`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `topspace top:A->bool` o
    REWRITE_RULE[rfs_components_s3]) THEN
  ASM_SIMP_TAC[CONNECTED_COMPONENTS_OF_CONNECTED_SPACE; IN_SING;
               SUBTOPOLOGY_TOPSPACE; RESTRICT_ATLAS_TOPSPACE]);;

(* ------------------------------------------------------------------------- *)
(* The initial stage of a history identified with a closed simply connected  *)
(* manifold.                                                                 *)
(* ------------------------------------------------------------------------- *)

let RFS_INITIAL_STAGE = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) g (hs:(B)rfs_history) iota iota'.
        rfs_initial (top,atlas) g hs iota iota' /\
        simply_connected_space top /\ ~(topspace top = {})
        ==> mfd_diffeomorphic top atlas (hs_top hs 0) (hs_atlas hs 0) /\
            simply_connected_space (hs_top hs 0) /\
            connected_space (hs_top hs 0) /\
            ~(topspace (hs_top hs 0) = {})`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rfs_initial] THEN STRIP_TAC THEN
  CONJ_TAC THENL [REWRITE_TAC[mfd_diffeomorphic] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(top:A topology) homeomorphic_space (hs_top (hs:(B)rfs_history) 0)`
  ASSUME_TAC THENL
   [REWRITE_TAC[homeomorphic_space] THEN
    MAP_EVERY EXISTS_TAC [`iota:A->B`; `iota':B->A`] THEN
    FIRST_ASSUM(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o
      GEN_REWRITE_RULE I [mfd_diffeo]) THEN
    REWRITE_TAC[SUBTOPOLOGY_TOPSPACE]; ALL_TAC] THEN
  SUBGOAL_THEN `simply_connected_space (hs_top (hs:(B)rfs_history) 0)` ASSUME_TAC THENL
   [ASM_MESON_TAC[SIMPLY_CONNECTED_SPACE_HOMEOMORPHIC]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[SIMPLY_CONNECTED_SPACE_IMP_PATH_CONNECTED_SPACE;
                  PATH_CONNECTED_IMP_CONNECTED_SPACE];
    FIRST_ASSUM(MP_TAC o MATCH_MP MFD_DIFFEO_MAPS) THEN ASM SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Forward induction: components stay simply connected.                      *)
(* ------------------------------------------------------------------------- *)

let RFS_EVENT_SC = prove
 (`!hs:(A)rfs_history k.
        RFS_CUTCAP_SC_STATEMENT (:A) (:A) /\ rfs_history_ok hs /\
        1 <= k /\ k <= hs_count hs /\ rfs_components_sc (hs_top hs (k - 1))
        ==> rfs_components_sc (ev_ztop(hs_event hs k)) /\
            rfs_components_sc (hs_top hs k)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `k:num` o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o
    GEN_REWRITE_RULE I [rfs_history_ok]) THEN
  ASM_REWRITE_TAC[rfs_event_ok] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `k - 1` o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o
    GEN_REWRITE_RULE I [rfs_history_ok]) THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `k <= hs_count (hs:(A)rfs_history)` THEN ARITH_TAC;
    STRIP_TAC] THEN
  SUBGOAL_THEN `rfs_components_sc (ev_ztop(hs_event (hs:(A)rfs_history) k))`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [RFS_CUTCAP_SC_STATEMENT]) THEN
    DISCH_THEN MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC
     [`hs_top (hs:(A)rfs_history) (k - 1)`; `hs_atlas (hs:(A)rfs_history) (k - 1)`;
      `ev_zatlas(hs_event (hs:(A)rfs_history) k)`;
      `ev_index(hs_event (hs:(A)rfs_history) k)`;
      `ev_neck(hs_event (hs:(A)rfs_history) k)`;
      `ev_capp(hs_event (hs:(A)rfs_history) k)`;
      `ev_capm(hs_event (hs:(A)rfs_history) k)`; `\x:A. x`; `\x:A. x`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC RFS_COMPONENTS_SC_CLOPEN THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_IN_DIFF THEN ASM_REWRITE_TAC[OPEN_IN_TOPSPACE];
    MATCH_MP_TAC CLOSED_IN_DIFF THEN ASM_REWRITE_TAC[CLOSED_IN_TOPSPACE]]);;

let RFS_HISTORY_SC = prove
 (`!hs:(A)rfs_history.
        RFS_CUTCAP_SC_STATEMENT (:A) (:A) /\
        rfs_history_ok hs /\ rfs_components_sc (hs_top hs 0)
        ==> (!k. k <= hs_count hs ==> rfs_components_sc (hs_top hs k)) /\
            (!k. 1 <= k /\ k <= hs_count hs
                 ==> rfs_components_sc (ev_ztop(hs_event hs k)))`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!k. k <= hs_count hs ==> rfs_components_sc (hs_top (hs:(A)rfs_history) k)`
  ASSUME_TAC THENL
   [INDUCT_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(SPECL [`hs:(A)rfs_history`; `SUC k`] RFS_EVENT_SC) THEN
    ASM_REWRITE_TAC[ARITH_RULE `1 <= SUC k`; ARITH_RULE `SUC k - 1 = k`] THEN
    ANTS_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN
      UNDISCH_TAC `SUC k <= hs_count (hs:(A)rfs_history)` THEN ARITH_TAC;
      SIMP_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`hs:(A)rfs_history`; `k:num`] RFS_EVENT_SC) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `k <= hs_count (hs:(A)rfs_history)` THEN ARITH_TAC;
    SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Backward induction from the empty last stage.                             *)
(* ------------------------------------------------------------------------- *)

let RFS_EVENT_S3 = prove
 (`!hs:(A)rfs_history k.
        RFS_SPHERE_SYSTEM_STATEMENT (:A) (:A) /\ rfs_history_ok hs /\
        1 <= k /\ k <= hs_count hs /\
        rfs_components_sc (hs_top hs (k - 1)) /\
        (!U. U IN connected_components_of (ev_ztop(hs_event hs k)) /\
             U SUBSET ev_disc(hs_event hs k)
             ==> mfd_diffeomorphic (subtopology (ev_ztop(hs_event hs k)) U)
                                   (restrict_atlas (ev_zatlas(hs_event hs k)) U)
                   (subtopology euclidean (sphere(vec 0:real^4,&1))) sphere3_atlas) /\
        rfs_components_s3 (hs_top hs k) (hs_atlas hs k)
        ==> rfs_components_s3 (hs_top hs (k - 1)) (hs_atlas hs (k - 1))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `k:num` o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o
    GEN_REWRITE_RULE I [rfs_history_ok]) THEN
  ASM_REWRITE_TAC[rfs_event_ok] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `k - 1` o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o
    GEN_REWRITE_RULE I [rfs_history_ok]) THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `k <= hs_count (hs:(A)rfs_history)` THEN ARITH_TAC;
    STRIP_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [RFS_SPHERE_SYSTEM_STATEMENT]) THEN
  DISCH_THEN MATCH_MP_TAC THEN
  MAP_EVERY EXISTS_TAC
   [`ev_ztop(hs_event (hs:(A)rfs_history) k)`;
    `ev_zatlas(hs_event (hs:(A)rfs_history) k)`;
    `ev_index(hs_event (hs:(A)rfs_history) k)`;
    `ev_neck(hs_event (hs:(A)rfs_history) k)`;
    `ev_capp(hs_event (hs:(A)rfs_history) k)`;
    `ev_capm(hs_event (hs:(A)rfs_history) k)`; `\x:A. x`; `\x:A. x`] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[rfs_components_s3] THEN X_GEN_TAC `U:A->bool` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`ev_ztop(hs_event (hs:(A)rfs_history) k)`; `U:A->bool`;
                 `ev_disc(hs_event (hs:(A)rfs_history) k)`]
                CONNECTED_IN_CLOPEN_CASES) THEN
  ASM_SIMP_TAC[CONNECTED_IN_CONNECTED_COMPONENTS_OF] THEN STRIP_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `U SUBSET topspace(ev_ztop(hs_event (hs:(A)rfs_history) k)) DIFF
             ev_disc(hs_event hs k)`
  ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP CONNECTED_COMPONENTS_OF_SUBSET) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `rfs_components_s3 (hs_top (hs:(A)rfs_history) k) (hs_atlas hs k)` THEN
  ASM_REWRITE_TAC[rfs_components_s3] THEN
  DISCH_THEN(MP_TAC o SPEC `U:A->bool`) THEN ANTS_TAC THENL
   [MATCH_MP_TAC CONNECTED_COMPONENTS_OF_SUBTOPOLOGY THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SUBTOPOLOGY_SUBTOPOLOGY; RFS_RESTRICT_ATLAS_RESTRICT] THEN
  SUBGOAL_THEN
   `(topspace(ev_ztop(hs_event (hs:(A)rfs_history) k)) DIFF
     ev_disc(hs_event hs k)) INTER U = U`
  SUBST1_TAC THENL [ASM SET_TAC[]; REWRITE_TAC[]]);;

let RFS_HISTORY_S3 = prove
 (`!hs:(A)rfs_history.
        RFS_SPHERE_SYSTEM_STATEMENT (:A) (:A) /\
        rfs_history_ok hs /\ rfs_extinct hs /\
        (!k. k <= hs_count hs ==> rfs_components_sc (hs_top hs k)) /\
        (!k U. 1 <= k /\ k <= hs_count hs /\
               U IN connected_components_of (ev_ztop(hs_event hs k)) /\
               U SUBSET ev_disc(hs_event hs k)
               ==> mfd_diffeomorphic (subtopology (ev_ztop(hs_event hs k)) U)
                                     (restrict_atlas (ev_zatlas(hs_event hs k)) U)
                     (subtopology euclidean (sphere(vec 0:real^4,&1))) sphere3_atlas)
        ==> rfs_components_s3 (hs_top hs 0) (hs_atlas hs 0)`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!j. j <= hs_count hs
        ==> rfs_components_s3 (hs_top (hs:(A)rfs_history) (hs_count hs - j))
                              (hs_atlas hs (hs_count hs - j))`
  (MP_TAC o SPEC `hs_count (hs:(A)rfs_history)`) THENL
   [ALL_TAC; REWRITE_TAC[LE_REFL; SUB_REFL]] THEN
  INDUCT_TAC THENL
   [DISCH_TAC THEN REWRITE_TAC[SUB_0; rfs_components_s3] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[rfs_extinct]) THEN
    ASM_SIMP_TAC[CONNECTED_COMPONENTS_OF_EMPTY_SPACE; NOT_IN_EMPTY];
    ALL_TAC] THEN
  DISCH_TAC THEN
  MP_TAC(SPECL [`hs:(A)rfs_history`; `hs_count (hs:(A)rfs_history) - j`]
               RFS_EVENT_S3) THEN
  SUBGOAL_THEN `hs_count (hs:(A)rfs_history) - j - 1 = hs_count hs - SUC j`
  SUBST1_TAC THENL
   [UNDISCH_TAC `SUC j <= hs_count (hs:(A)rfs_history)` THEN ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `1 <= hs_count (hs:(A)rfs_history) - j /\
                hs_count hs - j <= hs_count hs /\
                hs_count hs - SUC j <= hs_count hs /\ j <= hs_count hs`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `SUC j <= hs_count (hs:(A)rfs_history)` THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Discarded components, and the assembly theorem.                           *)
(* ------------------------------------------------------------------------- *)

let RFS_DISCARDED_S3 = prove
 (`!hs:(A)rfs_history k U.
        RFS_LISTED_SC_S3_STATEMENT (:A) /\ rfs_history_ok hs /\
        1 <= k /\ k <= hs_count hs /\
        rfs_components_sc (ev_ztop(hs_event hs k)) /\
        U IN connected_components_of (ev_ztop(hs_event hs k)) /\
        rfs_listed_piece (subtopology (ev_ztop(hs_event hs k)) U)
                         (restrict_atlas (ev_zatlas(hs_event hs k)) U)
        ==> mfd_diffeomorphic (subtopology (ev_ztop(hs_event hs k)) U)
                              (restrict_atlas (ev_zatlas(hs_event hs k)) U)
              (subtopology euclidean (sphere(vec 0:real^4,&1))) sphere3_atlas`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `k:num` o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o
    GEN_REWRITE_RULE I [rfs_history_ok]) THEN
  ASM_REWRITE_TAC[rfs_event_ok] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o GEN_REWRITE_RULE I [RFS_LISTED_SC_S3_STATEMENT]) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o GEN_REWRITE_RULE I [rfs_components_sc]) THEN
  ASM_REWRITE_TAC[]);;

let RFS_POINCARE_SMOOTH = prove
 (`!u:A->bool.
        METRIC_EXISTENCE_STATEMENT u (:3) /\
        RFS_EXTINCTION_STATEMENT u /\
        EVENT_TOPOLOGY_STATEMENT (:A+num#num#real^3) /\
        RFS_CUTCAP_SC_STATEMENT (:A+num#num#real^3) (:A+num#num#real^3) /\
        RFS_LISTED_SC_S3_STATEMENT (:A+num#num#real^3) /\
        RFS_SPHERE_SYSTEM_STATEMENT (:A+num#num#real^3) (:A+num#num#real^3) /\
        SMT_POINCARE_CONVERSION_STATEMENT u
        ==> POINCARE_SMOOTH_STATEMENT u`,
  GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[POINCARE_SMOOTH_STATEMENT] THEN
  MAP_EVERY X_GEN_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`] THEN
  STRIP_TAC THEN
  MP_TAC(REWRITE_RULE[SMT_POINCARE_CONVERSION_STATEMENT]
    (ASSUME `SMT_POINCARE_CONVERSION_STATEMENT (u:A->bool)`)) THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`]
    (REWRITE_RULE[METRIC_EXISTENCE_STATEMENT]
      (ASSUME `METRIC_EXISTENCE_STATEMENT (u:A->bool) (:3)`))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `g0:A->real^3^3`) THEN
  MP_TAC(REWRITE_RULE[EVENT_TOPOLOGY_STATEMENT]
    (ASSUME `EVENT_TOPOLOGY_STATEMENT (:A+num#num#real^3)`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `eps0:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "evt"))) THEN
  MP_TAC(SPEC `eps0:real` (REWRITE_RULE[RFS_EXTINCTION_STATEMENT]
    (ASSUME `RFS_EXTINCTION_STATEMENT (u:A->bool)`))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `C:real` (X_CHOOSE_THEN `eps:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ext")))))) THEN
  REMOVE_THEN "evt" (MP_TAC o SPECL [`C:real`; `eps:real`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `dl0:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "evt"))) THEN
  REMOVE_THEN "ext" (MP_TAC o SPEC `dl0:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`top:A topology`;
    `atlas:((A->bool)#(A->real^3))->bool`; `g0:A->real^3^3`]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [rfs_controlled]) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `\x:A. q %% (g0:A->real^3^3) x`;
                 `hs:(A+num#num#real^3)rfs_history`;
                 `iota:A->A+num#num#real^3`; `iota':A+num#num#real^3->A`]
                RFS_INITIAL_STAGE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `smooth_manifold_atlas (hs_top (hs:(A+num#num#real^3)rfs_history) 0)
                                      (hs_atlas hs 0)`
  ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPEC `0` o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o
      GEN_REWRITE_RULE I [rfs_history_ok]) THEN
    SIMP_TAC[LE_0];
    ALL_TAC] THEN
  MP_TAC(ISPEC `hs:(A+num#num#real^3)rfs_history` RFS_HISTORY_SC) THEN
  ASM_SIMP_TAC[RFS_COMPONENTS_SC_CONNECTED] THEN STRIP_TAC THEN
  MATCH_MP_TAC(ISPECL
   [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
    `hs_top (hs:(A+num#num#real^3)rfs_history) 0`;
    `hs_atlas (hs:(A+num#num#real^3)rfs_history) 0`;
    `subtopology euclidean (sphere(vec 0:real^4,&1))`; `sphere3_atlas`]
   MFD_DIFFEOMORPHIC_TRANS) THEN
  ASM_REWRITE_TAC[SPHERE3_ATLAS] THEN
  MATCH_MP_TAC RFS_COMPONENTS_S3_CONNECTED THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC RFS_HISTORY_S3 THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`k:num`; `U:A+num#num#real^3->bool`] THEN STRIP_TAC THEN
  MATCH_MP_TAC RFS_DISCARDED_S3 THEN ASM_SIMP_TAC[] THEN
  SUBGOAL_THEN `k - 1 <= hs_count (hs:(A+num#num#real^3)rfs_history)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `k <= hs_count (hs:(A+num#num#real^3)rfs_history)` THEN
    ARITH_TAC;
    ALL_TAC] THEN
  REMOVE_THEN "evt" (MP_TAC o SPECL
   [`hs:(A+num#num#real^3)rfs_history`; `rp:real->real`; `dl:real->real`;
    `kp:real->real`; `h:real->real`; `k:num`]) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[];
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

