(* ========================================================================= *)
(* pc_top_p4: the algebraic topology layer under Part 4. The three topology  *)
(* statements of Part 4 (P4_DEGREE_ONE_STATEMENT, P4_SC_DEGREE_ONE_STATEMENT *)
(* and P4_SMOOTHING_STATEMENT of pc_p4_defs) are derived from the algebraic  *)
(* topology statements (pc_top_iface, pc_top_smooth) and then proved from    *)
(* the files that prove those: G1 pc_top_mv; G2, G3, M2 pc_top_lochom; M1    *)
(* pc_top_fclass; M4 pc_top_orient; M5 pc_top_genpos; M7 pc_top_sc3; G4      *)
(* pc_top_hurewicz; S1, S2 pc_top_smooth. M3 (fundamental class, injectivity *)
(* on top homology) and M6 (the null-homotopic ball sphere) are proved here: *)
(* M3 from M1 (and M2 for injectivity), M6 from the M3 fundamental class, M5 *)
(* and G4.                                                                   *)
(*                                                                           *)
(* The reductions, in the sections A1-A8.                                    *)
(* ========================================================================= *)

needs "src/pc_p4_defs.ml";;
needs "src/pc_audit_sanity.ml";;
needs "src/pc_mfd_examples.ml";;
needs "src/pc_top_iface.ml";;
needs "src/pc_top_mv.ml";;
needs "src/pc_top_lochom.ml";;
needs "src/pc_top_fclass.ml";;
needs "src/pc_top_orient.ml";;
needs "src/pc_top_genpos.ml";;
needs "src/pc_top_sc3.ml";;
needs "src/pc_top_hurewicz.ml";;
needs "src/pc_top_smooth.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* A1. Topological manifolds: open subsets and components of closed        *)
(* manifolds (local path-connectedness is in pc_top_orient).                *)
(* ------------------------------------------------------------------------- *)

let ATOP_LOCALLY_EUCLIDEAN_OPEN_SUBSET = prove
 (`!(top:A topology) w.
        locally_euclidean_space (:N) top /\ open_in top w
        ==> locally_euclidean_space (:N) (subtopology top w)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[locally_euclidean_space] THEN STRIP_TAC THEN
  X_GEN_TAC `x:A` THEN REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:A->bool` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `f:A->real^N` o GEN_REWRITE_RULE I [HOMEOMORPHIC_SPACE]) THEN
  SUBGOAL_THEN `(u:A->bool) SUBSET topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `topspace(subtopology top (u:A->bool)) = u` ASSUME_TAC THENL
   [REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `open (IMAGE (f:A->real^N) (u INTER w))` MP_TAC THENL
   [REWRITE_TAC[OPEN_IN] THEN
    MP_TAC(ISPECL [`f:A->real^N`; `subtopology top (u:A->bool)`;
                   `euclidean:(real^N)topology`; `u INTER w:A->bool`]
                  HOMEOMORPHIC_MAP_OPENNESS) THEN
    ASM_REWRITE_TAC[INTER_SUBSET] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[OPEN_IN_SUBTOPOLOGY] THEN EXISTS_TAC `w:A->bool` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[OPEN_CONTAINS_BALL] THEN
  DISCH_THEN(MP_TAC o SPEC `(f:A->real^N) x`) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP HOMEOMORPHIC_IMP_INJECTIVE_MAP) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP HOMEOMORPHIC_IMP_CONTINUOUS_MAP) THEN
  ABBREV_TAC `v = {y:A | y IN u /\ (f:A->real^N) y IN ball(f x,r)}` THEN
  SUBGOAL_THEN `(v:A->bool) SUBSET u /\ v SUBSET w /\ (x:A) IN v` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "v" THEN REWRITE_TAC[SUBSET; IN_ELIM_THM; CENTRE_IN_BALL] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [SIMP_TAC[]; ALL_TAC] THEN
    X_GEN_TAC `y:A` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(f:A->real^N) y IN IMAGE f (u INTER w)` MP_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE; IN_INTER] THEN
    DISCH_THEN(X_CHOOSE_THEN `z:A` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(y:A) = z` (fun th -> ASM_REWRITE_TAC[th]) THEN
    UNDISCH_TAC `!x y. x IN topspace (subtopology top (u:A->bool)) /\
                       y IN topspace (subtopology top u)
                       ==> ((f:A->real^N) x = f y <=> x = y)` THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPECL [`y:A`; `z:A`]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `open_in top (v:A->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC OPEN_IN_TRANS_FULL THEN EXISTS_TAC `u:A->bool` THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`f:A->real^N`; `subtopology top (u:A->bool)`;
                   `euclidean:(real^N)topology`; `ball((f:A->real^N) x,r)`]
                  OPEN_IN_CONTINUOUS_MAP_PREIMAGE) THEN
    ASM_REWRITE_TAC[GSYM OPEN_IN; OPEN_BALL] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN EXPAND_TAC "v" THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `v:A->bool` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[OPEN_IN_SUBTOPOLOGY] THEN EXISTS_TAC `v:A->bool` THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SUBTOPOLOGY_SUBTOPOLOGY] THEN
  SUBGOAL_THEN `w INTER v:A->bool = v` SUBST1_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  TRANS_TAC HOMEOMORPHIC_SPACE_TRANS
    `subtopology euclidean (ball((f:A->real^N) x,r))` THEN CONJ_TAC THENL
   [REWRITE_TAC[HOMEOMORPHIC_SPACE] THEN EXISTS_TAC `f:A->real^N` THEN
    SUBGOAL_THEN `subtopology top (v:A->bool) = subtopology (subtopology top u) v`
    SUBST1_TAC THENL
     [REWRITE_TAC[SUBTOPOLOGY_SUBTOPOLOGY] THEN AP_TERM_TAC THEN
      UNDISCH_TAC `(v:A->bool) SUBSET u` THEN SET_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC HOMEOMORPHIC_MAP_SUBTOPOLOGIES THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[TOPSPACE_EUCLIDEAN; INTER_UNIV] THEN
    SUBGOAL_THEN `u INTER v:A->bool = v` SUBST1_TAC THENL
     [UNDISCH_TAC `(v:A->bool) SUBSET u` THEN SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [EXPAND_TAC "v" THEN SET_TAC[];
      REWRITE_TAC[SUBSET] THEN X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(z:real^N) IN IMAGE (f:A->real^N) (u INTER w)` MP_TAC THENL
       [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
      EXPAND_TAC "v" THEN REWRITE_TAC[IN_IMAGE; IN_INTER; IN_ELIM_THM] THEN
      ASM_MESON_TAC[]];
    MP_TAC(ISPECL [`(f:A->real^N) x`; `r:real`] HOMEOMORPHIC_BALL_UNIV) THEN
    ASM_REWRITE_TAC[GSYM HOMEOMORPHIC_SPACE_EUCLIDEAN; SUBTOPOLOGY_UNIV]]);;

let ATOP_COMPONENT_CLOSED_MANIFOLD = prove
 (`!top:A topology c.
        hausdorff_space top /\ locally_euclidean_space (:N) top /\
        compact_space top /\ c IN connected_components_of top
        ==> open_in top c /\ closed_in top c /\ ~(c = {}) /\
            topspace(subtopology top c) = c /\
            hausdorff_space (subtopology top c) /\
            locally_euclidean_space (:N) (subtopology top c) /\
            compact_space (subtopology top c) /\
            connected_space (subtopology top c)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `open_in top (c:A->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC OPEN_IN_CONNECTED_COMPONENTS_OF_LOCALLY_CONNECTED_SPACE THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC LOCALLY_PATH_CONNECTED_IMP_LOCALLY_CONNECTED_SPACE THEN
    MATCH_ACCEPT_TAC(MATCH_MP ATOP_LOCALLY_EUCLIDEAN_IMP_LOCALLY_PATH_CONNECTED
      (ASSUME `locally_euclidean_space (:N) (top:A topology)`));
    ALL_TAC] THEN
  SUBGOAL_THEN `closed_in top (c:A->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[CLOSED_IN_CONNECTED_COMPONENTS_OF]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[NONEMPTY_CONNECTED_COMPONENTS_OF];
    REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP CONNECTED_COMPONENTS_OF_SUBSET) THEN SET_TAC[];
    ASM_SIMP_TAC[HAUSDORFF_SPACE_SUBTOPOLOGY];
    MATCH_MP_TAC ATOP_LOCALLY_EUCLIDEAN_OPEN_SUBSET THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC COMPACT_SPACE_SUBTOPOLOGY THEN
    MATCH_MP_TAC CLOSED_IN_COMPACT_SPACE THEN ASM_REWRITE_TAC[];
    FIRST_ASSUM(MP_TAC o MATCH_MP CONNECTED_IN_CONNECTED_COMPONENTS_OF) THEN
    SIMP_TAC[connected_in]]);;

(* ------------------------------------------------------------------------- *)
(* A2. Degree-one maps are injective on top homology (from the injectivity  *)
(* of H_n(M) -> H_n(M|x) and the local isomorphism), and P4_DEGREE_ONE.     *)
(* ------------------------------------------------------------------------- *)

let ATOP_DEGREE_ONE_ESSENTIAL = prove
 (`ATOP_TOP_HOMOLOGY_INJECTIVE_STATEMENT (:A) (:N) /\
   ATOP_DEGREE_ONE_LOCAL_STATEMENT (:A) (:B)
   ==> !top top' (p:A->B) w z.
        hausdorff_space top /\ locally_euclidean_space (:N) top /\
        compact_space top /\ connected_space top /\
        t1_space top' /\ continuous_map (top,top') p /\
        open_in top w /\ ~(w = {}) /\ open_in top' (IMAGE p w) /\
        homeomorphic_map (subtopology top w,subtopology top' (IMAGE p w)) p /\
        (!y. y IN topspace top /\ p y IN IMAGE p w ==> y IN w) /\
        z IN group_carrier(homology_group(&(dimindex(:N)),top)) /\
        ~(z = group_id(homology_group(&(dimindex(:N)),top)))
        ==> ~(hom_induced (&(dimindex(:N))) (top,{}) (top',{}) p z =
              group_id(homology_group(&(dimindex(:N)),top')))`,
  REWRITE_TAC[ATOP_TOP_HOMOLOGY_INJECTIVE_STATEMENT;
              ATOP_DEGREE_ONE_LOCAL_STATEMENT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "inj") (LABEL_TAC "loc")) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `x:A` o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  SUBGOAL_THEN `(w:A->bool) SUBSET topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `t1_space (top:A topology)` ASSUME_TAC THENL
   [ASM_MESON_TAC[HAUSDORFF_IMP_T1_SPACE]; ALL_TAC] THEN
  ABBREV_TAC `n = &(dimindex(:N)):int` THEN
  REMOVE_THEN "inj" (MP_TAC o SPECL [`top:A topology`; `x:A`]) THEN
  ASM_REWRITE_TAC[GROUP_MONOMORPHISM_ALT_EQ] THEN
  DISCH_THEN(MP_TAC o SPEC `z:((num->real)->A)frag->bool` o CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REMOVE_THEN "loc" (MP_TAC o SPECL
   [`n:int`; `top:A topology`; `top':B topology`; `p:A->B`; `w:A->bool`; `x:A`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o MATCH_MP GROUP_ISOMORPHISM_IMP_MONOMORPHISM) THEN
  REWRITE_TAC[GROUP_MONOMORPHISM_ALT_EQ] THEN
  DISCH_THEN(MP_TAC o SPEC
   `hom_induced n (top,{}) (top,topspace top DELETE x) (\x:A. x) z` o CONJUNCT2) THEN
  ASM_REWRITE_TAC[HOM_INDUCED] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `IMAGE (p:A->B) (topspace top DELETE x) SUBSET topspace top' DELETE p x`
  ASSUME_TAC THENL
   [MATCH_MP_TAC ATOP_DEGREE_ONE_IMAGE_SUBSET THEN EXISTS_TAC `w:A->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `hom_induced n (top,topspace top DELETE x) (top',topspace top' DELETE (p:A->B) x) p o
    hom_induced n (top,{}) (top,topspace top DELETE x) (\x:A. x) =
    hom_induced n (top',{}) (top',topspace top' DELETE p x) (\x:B. x) o
    hom_induced n (top,{}) (top',{}) p`
  MP_TAC THENL
   [MP_TAC(ISPECL [`n:int`; `top:A topology`; `{}:A->bool`; `top:A topology`;
                   `topspace top DELETE (x:A)`; `top':B topology`;
                   `topspace top' DELETE (p:A->B) x`; `\x:A. x`; `p:A->B`]
                  HOM_INDUCED_COMPOSE) THEN
    MP_TAC(ISPECL [`n:int`; `top:A topology`; `{}:A->bool`; `top':B topology`;
                   `{}:B->bool`; `top':B topology`;
                   `topspace top' DELETE (p:A->B) x`; `p:A->B`; `\x:B. x`]
                  HOM_INDUCED_COMPOSE) THEN
    ASM_REWRITE_TAC[CONTINUOUS_MAP_ID; IMAGE_CLAUSES; EMPTY_SUBSET] THEN
    SUBGOAL_THEN `(\x:B. x) o (p:A->B) = p /\ p o (\x:A. x) = p`
      (fun th -> REWRITE_TAC[th]) THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o C AP_THM `z:((num->real)->A)frag->bool`) THEN
  REWRITE_TAC[o_THM] THEN DISCH_THEN SUBST_ALL_TAC THEN
  DISCH_TAC THEN UNDISCH_TAC
   `~(hom_induced n (top',{}) (top',topspace top' DELETE (p:A->B) x) (\x:B. x)
        (hom_induced n (top,{}) (top',{}) p z) =
      group_id (relative_homology_group (n,top',topspace top' DELETE p x)))` THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`n:int`; `top':B topology`; `{}:B->bool`; `top':B topology`;
                 `topspace top' DELETE (p:A->B) x`; `\x:B. x`]
                GROUP_HOMOMORPHISM_HOM_INDUCED) THEN
  REWRITE_TAC[group_homomorphism; GSYM homology_group] THEN MESON_TAC[]);;

let ATOP_P4_DEGREE_ONE = prove
 (`ATOP_TOP_HOMOLOGY_INJECTIVE_STATEMENT (:A) (:3) /\
   ATOP_DEGREE_ONE_LOCAL_STATEMENT (:A) (:B)
   ==> P4_DEGREE_ONE_STATEMENT (:A) (:B)`,
  DISCH_THEN(ASSUME_TAC o MATCH_MP ATOP_DEGREE_ONE_ESSENTIAL) THEN
  REWRITE_TAC[P4_DEGREE_ONE_STATEMENT] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `p4_essential (subtopology topX (X:A->bool)) (f:real^4->A)` THEN
  REWRITE_TAC[p4_essential] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `z:((num->real)->real^4)frag->bool` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`topX:A topology`; `X:A->bool`]
    (INST_TYPE [`:3`,`:N`] ATOP_COMPONENT_CLOSED_MANIFOLD)) THEN
  ANTS_TAC THENL
   [ASM_MESON_TAC[SMOOTH_MANIFOLD_ATLAS_IMP_LOCALLY_EUCLIDEAN]; STRIP_TAC] THEN
  SUBGOAL_THEN `topspace(subtopology topY (Y:B->bool)) = Y` ASSUME_TAC THENL
   [REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN
    MP_TAC(MATCH_MP CONNECTED_COMPONENTS_OF_SUBSET
      (ASSUME `(Y:B->bool) IN connected_components_of topY`)) THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (p:A->B) U SUBSET Y` ASSUME_TAC THENL
   [MP_TAC(MATCH_MP CONTINUOUS_MAP_IMAGE_SUBSET_TOPSPACE
      (ASSUME `continuous_map (subtopology topX X,subtopology topY Y) (p:A->B)`)) THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
    EXISTS_TAC `subtopology topX (X:A->bool)` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `z:((num->real)->real^4)frag->bool` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL
   [`&3:int`; `subtopology euclidean (sphere(vec 0:real^4,&1))`; `{}:real^4->bool`;
    `subtopology topX (X:A->bool)`; `{}:A->bool`;
    `subtopology topY (Y:B->bool)`; `{}:B->bool`; `f:real^4->A`; `p:A->B`]
   HOM_INDUCED_COMPOSE) THEN
  ASM_REWRITE_TAC[IMAGE_CLAUSES; EMPTY_SUBSET] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[o_THM] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`subtopology topX (X:A->bool)`; `subtopology topY (Y:B->bool)`; `p:A->B`;
    `U:A->bool`;
    `hom_induced (&3) (subtopology euclidean (sphere(vec 0:real^4,&1)),{})
                      (subtopology topX X,{}) (f:real^4->A) z`]) THEN
  REWRITE_TAC[DIMINDEX_3] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[homology_group; HOM_INDUCED] THEN
  REWRITE_TAC[SUBTOPOLOGY_SUBTOPOLOGY] THEN
  SUBGOAL_THEN `(X:A->bool) INTER U = U /\ (Y:B->bool) INTER IMAGE p U = IMAGE p U`
    (fun th -> REWRITE_TAC[th]) THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[HAUSDORFF_IMP_T1_SPACE; HAUSDORFF_SPACE_SUBTOPOLOGY];
    MATCH_MP_TAC OPEN_IN_SUBSET_TOPSPACE THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC OPEN_IN_SUBSET_TOPSPACE THEN ASM_REWRITE_TAC[]]);;

let ATOP_S3_HOMOLOGY = prove
 (`ATOP_S3_HOMOLOGY_STATEMENT`,
  REWRITE_TAC[ATOP_S3_HOMOLOGY_STATEMENT] THEN
  SUBGOAL_THEN
   `nsphere 3 homeomorphic_space subtopology euclidean (sphere(vec 0:real^4,&1))`
  ASSUME_TAC THENL
   [REWRITE_TAC[homeomorphic_space] THEN
    MP_TAC(ISPEC `4` (INST_TYPE [`:4`,`:N`] HOMEOMORPHIC_MAPS_NSPHERE_EUCLIDEAN_SPHERE)) THEN
    REWRITE_TAC[DIMINDEX_4; ARITH] THEN
    SUBGOAL_THEN `span(IMAGE basis (1..4)) = (:real^4)` SUBST1_TAC THENL
     [MP_TAC(INST_TYPE [`:4`,`:N`] SPAN_STDBASIS) THEN
      REWRITE_TAC[DIMINDEX_4; GSYM IN_NUMSEG; SIMPLE_IMAGE];
      REWRITE_TAC[INTER_UNIV] THEN MESON_TAC[]];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `&3:int` o
    MATCH_MP HOMEOMORPHIC_SPACE_IMP_ISOMORPHIC_HOMOLOGY_GROUPS) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM(MATCH_MP ISOMORPHIC_GROUP_TRIVIALITY th)]) THEN
  MP_TAC(INT_ARITH `~(&3:int = &0)`) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM(MATCH_MP UN_REDUCED_HOMOLOGY_GROUP th)]) THEN
  MP_TAC(SPEC `3` (CONJUNCT1 REDUCED_HOMOLOGY_GROUP_NSPHERE)) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP ISOMORPHIC_GROUP_TRIVIALITY th]) THEN
  REWRITE_TAC[NON_TRIVIAL_INTEGER_GROUP]);;

(* ------------------------------------------------------------------------- *)
(* A3. P4_SC_DEGREE_ONE: orientability (pc_top_orient),                    *)
(* the null-homotopic ball sphere, the degree-one map S^3 -> M and its      *)
(* essentialness through the local homology at a point of the witness.     *)
(* ------------------------------------------------------------------------- *)

let ATOP_SPHERE3_CLOSED_MANIFOLD = prove
 (`hausdorff_space (subtopology euclidean (sphere(vec 0:real^4,&1))) /\
   locally_euclidean_space (:3) (subtopology euclidean (sphere(vec 0:real^4,&1))) /\
   compact_space (subtopology euclidean (sphere(vec 0:real^4,&1))) /\
   connected_space (subtopology euclidean (sphere(vec 0:real^4,&1)))`,
  MP_TAC POINCARE_SMOOTH_HYPOTHESES_SPHERE_3 THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MANIFOLD_ATLAS_IMP_LOCALLY_EUCLIDEAN THEN
    EXISTS_TAC `sphere3_atlas` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC PATH_CONNECTED_IMP_CONNECTED_SPACE THEN
    MATCH_MP_TAC SIMPLY_CONNECTED_SPACE_IMP_PATH_CONNECTED_SPACE THEN
    ASM_REWRITE_TAC[]]);;

let ATOP_HOMOLOGY_ORIENTABLE_SC3 = prove
 (`ATOP_SC_ORIENTABLE_STATEMENT (:A) (:3)
   ==> !top atlas.
         hausdorff_space top /\
         smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool) /\
         simply_connected_space top
         ==> homology_orientable 3 top`,
  REWRITE_TAC[ATOP_SC_ORIENTABLE_STATEMENT; DIMINDEX_3] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC SMOOTH_MANIFOLD_ATLAS_IMP_LOCALLY_EUCLIDEAN THEN
  EXISTS_TAC `atlas:((A->bool)#(A->real^3))->bool` THEN ASM_REWRITE_TAC[]);;

let ATOP_P4_SC_DEGREE_ONE = prove
 (`ATOP_NULL_SPHERE_STATEMENT (:A) /\ ATOP_S3_FROM_NULL_SPHERE_STATEMENT (:A) /\
   ATOP_DEGREE_ONE_LOCAL_STATEMENT (:real^4) (:A) /\
   ATOP_TOP_HOMOLOGY_INJECTIVE_STATEMENT (:real^4) (:3) /\
   ATOP_SC_ORIENTABLE_STATEMENT (:A) (:3)
   ==> P4_SC_DEGREE_ONE_STATEMENT (:A)`,
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "null") (CONJUNCTS_THEN2 (LABEL_TAC "s3")
   (CONJUNCTS_THEN2 (LABEL_TAC "loc") (CONJUNCTS_THEN2 (LABEL_TAC "inj")
    (LABEL_TAC "or"))))) THEN
  REWRITE_TAC[P4_SC_DEGREE_ONE_STATEMENT] THEN
  MAP_EVERY X_GEN_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `locally_euclidean_space (:3) (top:A topology)` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MANIFOLD_ATLAS_IMP_LOCALLY_EUCLIDEAN THEN
    EXISTS_TAC `atlas:((A->bool)#(A->real^3))->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `homology_orientable 3 (top:A topology)` ASSUME_TAC THENL
   [MP_TAC(MATCH_MP ATOP_HOMOLOGY_ORIENTABLE_SC3 (ASSUME
     `ATOP_SC_ORIENTABLE_STATEMENT (:A) (:3)`)) THEN
    DISCH_THEN MATCH_MP_TAC THEN
    EXISTS_TAC `atlas:((A->bool)#(A->real^3))->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(X_CHOOSE_TAC `x:A` o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  FIRST_ASSUM(MP_TAC o SPEC `x:A` o GEN_REWRITE_RULE I [locally_euclidean_space]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:A->bool` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `e:real^3->A` o GEN_REWRITE_RULE I [HOMEOMORPHIC_SPACE] o
    ONCE_REWRITE_RULE[HOMEOMORPHIC_SPACE_SYM]) THEN
  REMOVE_THEN "null" (MP_TAC o SPECL [`top:A topology`; `w:A->bool`; `e:real^3->A`] o
    REWRITE_RULE[ATOP_NULL_SPHERE_STATEMENT]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `a:A`) THEN
  REMOVE_THEN "s3" (MP_TAC o SPECL [`top:A topology`; `w:A->bool`; `e:real^3->A`; `a:A`] o
    REWRITE_RULE[ATOP_S3_FROM_NULL_SPHERE_STATEMENT]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^4->A` (X_CHOOSE_THEN `v:real^4->bool`
    STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `f:real^4->A` THEN REWRITE_TAC[p4_essential] THEN ASM_REWRITE_TAC[] THEN
  MP_TAC ATOP_S3_HOMOLOGY THEN
  REWRITE_TAC[ATOP_S3_HOMOLOGY_STATEMENT; trivial_group] THEN
  MATCH_MP_TAC(SET_RULE `(a:C) IN s /\ (!z. z IN s /\ ~(z = a) ==> P z)
                         ==> ~(s = {a}) ==> ?z. z IN s /\ P z`) THEN
  REWRITE_TAC[GROUP_ID] THEN X_GEN_TAC `z:((num->real)->real^4)frag->bool` THEN
  STRIP_TAC THEN
  MP_TAC(MATCH_MP ATOP_DEGREE_ONE_ESSENTIAL (CONJ
    (ASSUME `ATOP_TOP_HOMOLOGY_INJECTIVE_STATEMENT (:real^4) (:3)`)
    (ASSUME `ATOP_DEGREE_ONE_LOCAL_STATEMENT (:real^4) (:A)`))) THEN
  DISCH_THEN(MP_TAC o SPECL
   [`subtopology euclidean (sphere(vec 0:real^4,&1))`; `top:A topology`;
    `f:real^4->A`; `v:real^4->bool`; `z:((num->real)->real^4)frag->bool`]) THEN
  REWRITE_TAC[DIMINDEX_3; ATOP_SPHERE3_CLOSED_MANIFOLD;
              TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[HAUSDORFF_IMP_T1_SPACE]);;

(* ------------------------------------------------------------------------- *)
(* A4. P4_SMOOTHING: desuspension, smoothing of the family, the homotopy     *)
(* stays in the component (connectedness), suspension of the homotopy and   *)
(* homotopy invariance of hom_induced.                                       *)
(* ------------------------------------------------------------------------- *)

let ATOP_HOMOTOPIC_WITH_COMPONENT = prove
 (`!P (X:B topology) (top:A topology) U p q.
        connected_space X /\ U IN connected_components_of top /\
        homotopic_with P (X,top) p q /\
        (?x. x IN topspace X /\ p x IN U)
        ==> homotopic_with P (X,subtopology top U) p q`,
  REPEAT GEN_TAC THEN REWRITE_TAC[homotopic_with] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (X_CHOOSE_THEN `h:real#B->A` STRIP_ASSUME_TAC)
     (X_CHOOSE_THEN `x0:B` STRIP_ASSUME_TAC)))) THEN
  EXISTS_TAC `h:real#B->A` THEN ASM_REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN
  MATCH_MP_TAC CONNECTED_COMPONENTS_OF_MAXIMAL THEN EXISTS_TAC `top:A topology` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONNECTED_IN_CONTINUOUS_MAP_IMAGE THEN
    EXISTS_TAC `prod_topology (subtopology euclideanreal (real_interval [&0,&1]))
                              (X:B topology)` THEN
    ASM_REWRITE_TAC[CONNECTED_IN_TOPSPACE; CONNECTED_SPACE_PROD_TOPOLOGY] THEN
    DISJ2_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM CONNECTED_IN_TOPSPACE; CONNECTED_IN_SUBTOPOLOGY] THEN
    REWRITE_TAC[TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY; SUBSET_REFL;
                CONNECTED_IN_EUCLIDEANREAL_INTERVAL];
    REWRITE_TAC[DISJOINT; GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
    EXISTS_TAC `(p:B->A) x0` THEN ASM_REWRITE_TAC[IN_IMAGE] THEN
    EXISTS_TAC `(&0,x0):real#B` THEN
    ASM_REWRITE_TAC[TOPSPACE_PROD_TOPOLOGY; IN_CROSS;
                    TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY; IN_REAL_INTERVAL] THEN
    REAL_ARITH_TAC]);;

let ATOP_P4_SMOOTHING = prove
 (`ATOP_SWEEPOUT_SMOOTHING_STATEMENT (:A) (:3) /\ ATOP_SUSPENSION_STATEMENT (:A)
   ==> P4_SMOOTHING_STATEMENT (:A)`,
  REWRITE_TAC[ATOP_SWEEPOUT_SMOOTHING_STATEMENT; ATOP_SUSPENSION_STATEMENT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "sm")
    (CONJUNCTS_THEN2 (LABEL_TAC "de") (LABEL_TAC "su"))) THEN
  REWRITE_TAC[P4_SMOOTHING_STATEMENT] THEN
  MAP_EVERY X_GEN_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                       `U:A->bool`; `f:real^4->A`] THEN
  STRIP_TAC THEN
  UNDISCH_TAC `p4_essential (subtopology top (U:A->bool)) (f:real^4->A)` THEN
  REWRITE_TAC[p4_essential] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `z:((num->real)->real^4)frag->bool` STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [CONTINUOUS_MAP_IN_SUBTOPOLOGY]) THEN
  REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN STRIP_TAC THEN
  REMOVE_THEN "de" (MP_TAC o SPECL [`top:A topology`; `f:real^4->A`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `sigma0:real^3->real->A` STRIP_ASSUME_TAC) THEN
  REMOVE_THEN "sm" (MP_TAC o SPECL
   [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
    `sigma0:real^3->real->A`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `sigma:real^3->real->A` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `connected_space
      (prod_topology (subtopology euclidean (sphere(vec 0:real^3,&1)))
                     (subtopology euclideanreal (real_interval[&0,&1])))`
  ASSUME_TAC THENL
   [REWRITE_TAC[CONNECTED_SPACE_PROD_TOPOLOGY] THEN DISJ2_TAC THEN
    REWRITE_TAC[GSYM CONNECTED_IN_TOPSPACE; CONNECTED_IN_SUBTOPOLOGY] THEN
    REWRITE_TAC[TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY;
                SUBSET_REFL; CONNECTED_IN_EUCLIDEANREAL_INTERVAL;
                CONNECTED_IN_EUCLIDEAN] THEN
    MATCH_MP_TAC CONNECTED_SPHERE THEN REWRITE_TAC[DIMINDEX_3] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(sigma0:real^3->real->A) (basis 1) (&0) IN U` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`basis 1:real^3`; `&0`]) THEN
    SIMP_TAC[IN_SPHERE_0; NORM_BASIS; DIMINDEX_3; ARITH; IN_REAL_INTERVAL;
             REAL_LE_REFL; REAL_POS] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:real^4` STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `IMAGE (f:real^4->A) (sphere(vec 0,&1)) SUBSET U` THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[IN_SPHERE_0];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\f:real^3#real->A. !y y'. y IN sphere(vec 0,&1) /\ y' IN sphere(vec 0,&1)
                               ==> f(y,&0) = f(y',&0) /\ f(y,&1) = f(y',&1)`;
    `prod_topology (subtopology euclidean (sphere(vec 0:real^3,&1)))
                   (subtopology euclideanreal (real_interval[&0,&1]))`;
    `top:A topology`; `U:A->bool`;
    `\(y,t). (sigma0:real^3->real->A) y t`; `\(y,t). (sigma:real^3->real->A) y t`]
   ATOP_HOMOTOPIC_WITH_COMPONENT) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [EXISTS_TAC `(basis 1:real^3,&0)` THEN
    ASM_REWRITE_TAC[TOPSPACE_PROD_TOPOLOGY; IN_CROSS; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY;
                    TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY; IN_REAL_INTERVAL;
                    IN_SPHERE_0] THEN
    SIMP_TAC[NORM_BASIS; DIMINDEX_3; ARITH] THEN REAL_ARITH_TAC;
    DISCH_THEN(LABEL_TAC "hU")] THEN
  REWRITE_TAC[p4_cm_adm; p4_sweepout_in] THEN
  EXISTS_TAC `sigma:real^3->real->A` THEN ASM_REWRITE_TAC[] THEN
  USE_THEN "hU" (MP_TAC o CONJUNCT2 o MATCH_MP HOMOTOPIC_WITH_IMP_CONTINUOUS_MAPS) THEN
  REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY; TOPSPACE_PROD_TOPOLOGY;
              TOPSPACE_EUCLIDEAN_SUBTOPOLOGY; TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_PAIR_THM; IN_CROSS] THEN
  STRIP_TAC THEN CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  REMOVE_THEN "su" (MP_TAC o SPECL
   [`subtopology top (U:A->bool)`; `sigma0:real^3->real->A`;
    `sigma:real^3->real->A`]) THEN
  USE_THEN "hU" (fun th -> REWRITE_TAC[th]) THEN DISCH_THEN(LABEL_TAC "hS") THEN
  REWRITE_TAC[p4_essential] THEN
  USE_THEN "hS" (fun th ->
    REWRITE_TAC[CONJUNCT2(MATCH_MP HOMOTOPIC_WITH_IMP_CONTINUOUS_MAPS th)]) THEN
  EXISTS_TAC `z:((num->real)->real^4)frag->bool` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`&3:int`; `subtopology euclidean (sphere(vec 0:real^4,&1))`;
                 `{}:real^4->bool`; `subtopology top (U:A->bool)`; `{}:A->bool`;
                 `p4_susp (sigma0:real^3->real->A)`; `p4_susp (sigma:real^3->real->A)`]
                HOMOLOGY_HOMOTOPY_AXIOM) THEN
  REWRITE_TAC[IMAGE_CLAUSES; EMPTY_SUBSET] THEN ANTS_TAC THENL
   [USE_THEN "hS" (fun th -> REWRITE_TAC[th]); DISCH_THEN(SUBST1_TAC o SYM)] THEN
  MP_TAC(ISPECL [`&3:int`; `subtopology euclidean (sphere(vec 0:real^4,&1))`;
                 `{}:real^4->bool`; `subtopology top (U:A->bool)`; `{}:A->bool`;
                 `p4_susp (sigma0:real^3->real->A)`; `f:real^4->A`]
                HOM_INDUCED_EQ) THEN
  ASM_SIMP_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* A5. The manifold corollaries of Hatcher Lemma 3.27: the fundamental      *)
(* class of a closed oriented manifold, and injectivity of                  *)
(* H_n(M) -> H_n(M|x) for closed connected manifolds (local constancy of   *)
(* the restrictions on chart balls, connectedness).                         *)
(* ------------------------------------------------------------------------- *)

let ATOP_FUNDAMENTAL_CLASS = prove
 (`ATOP_LOCAL_HOMOLOGY_COMPACT_STATEMENT (:A) (:N)
   ==> ATOP_FUNDAMENTAL_CLASS_STATEMENT (:A) (:N)`,
  REWRITE_TAC[ATOP_LOCAL_HOMOLOGY_COMPACT_STATEMENT;
              ATOP_FUNDAMENTAL_CLASS_STATEMENT; homology_orientation] THEN
  DISCH_TAC THEN MAP_EVERY X_GEN_TAC [`top:A topology`; `mu:A->((num->real)->A)frag->bool`] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`top:A topology`; `topspace top:A->bool`]) THEN
  ASM_REWRITE_TAC[GSYM compact_space; DIFF_EQ_EMPTY; GSYM homology_group] THEN
  DISCH_THEN(MP_TAC o SPEC `mu:A->((num->real)->A)frag->bool` o CONJUNCT2 o CONJUNCT2) THEN
  ANTS_TAC THENL [ALL_TAC; MESON_TAC[]] THEN
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `w:A->bool` THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `b:((num->real)->A)frag->bool` THEN
  SIMP_TAC[IN_INTER]);;

let ATOP_TOP_HOMOLOGY_INJECTIVE = prove
 (`ATOP_LOCAL_HOMOLOGY_COMPACT_STATEMENT (:A) (:N) /\
   ATOP_MANIFOLD_LOCAL_HOMOLOGY_STATEMENT (:A) (:N)
   ==> ATOP_TOP_HOMOLOGY_INJECTIVE_STATEMENT (:A) (:N)`,
  REWRITE_TAC[ATOP_LOCAL_HOMOLOGY_COMPACT_STATEMENT;
              ATOP_MANIFOLD_LOCAL_HOMOLOGY_STATEMENT;
              ATOP_TOP_HOMOLOGY_INJECTIVE_STATEMENT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "cpt") (LABEL_TAC "loc")) THEN
  MAP_EVERY X_GEN_TAC [`top:A topology`; `x:A`] THEN STRIP_TAC THEN
  ABBREV_TAC `n = &(dimindex(:N)):int` THEN
  REWRITE_TAC[GROUP_MONOMORPHISM_ALT; homology_group; GROUP_HOMOMORPHISM_HOM_INDUCED] THEN
  X_GEN_TAC `c:((num->real)->A)frag->bool` THEN STRIP_TAC THEN
  ABBREV_TAC
   `z = {y | y IN topspace top /\
             hom_induced n (top,{}) (top,topspace top DELETE y) (\x:A. x) c =
             group_id(relative_homology_group(n,top,topspace top DELETE y))}` THEN
  SUBGOAL_THEN
   `!y:A. y IN topspace top
          ==> ?v. open_in top v /\ y IN v /\
                  !y'. y' IN v ==> y' IN topspace top /\ (y' IN z <=> y IN z)`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:A` THEN DISCH_TAC THEN
    REMOVE_THEN "loc" (MP_TAC o SPECL [`top:A topology`; `y:A`]) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `v:A->bool` (X_CHOOSE_THEN `k:A->bool`
      STRIP_ASSUME_TAC) o CONJUNCT2 o CONJUNCT2) THEN
    EXISTS_TAC `v:A->bool` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `!y':A. y' IN k
             ==> (hom_induced n (top,{}) (top,topspace top DELETE y') (\x:A. x) c =
                  group_id(relative_homology_group(n,top,topspace top DELETE y')) <=>
                  hom_induced n (top,{}) (top,topspace top DIFF k) (\x:A. x) c =
                  group_id(relative_homology_group(n,top,topspace top DIFF k)))`
    ASSUME_TAC THENL
     [X_GEN_TAC `y':A` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`n:int`; `top:A topology`; `{}:A->bool`; `top:A topology`;
                     `topspace top DIFF k:A->bool`; `top:A topology`;
                     `topspace top DELETE (y':A)`; `\x:A. x`; `\x:A. x`]
                    HOM_INDUCED_COMPOSE) THEN
      REWRITE_TAC[CONTINUOUS_MAP_ID; IMAGE_CLAUSES; EMPTY_SUBSET; IMAGE_ID] THEN
      ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `(\x:A. x) o (\x:A. x) = (\x. x)` SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th; o_THM]) THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`n:int`; `y':A`]) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o MATCH_MP GROUP_ISOMORPHISM_IMP_MONOMORPHISM) THEN
      REWRITE_TAC[GROUP_MONOMORPHISM_ALT_EQ] THEN
      DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN REWRITE_TAC[HOM_INDUCED];
      ALL_TAC] THEN
    X_GEN_TAC `y':A` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(y':A) IN topspace top` ASSUME_TAC THENL
     [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "z" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(y':A) IN k /\ (y:A) IN k` STRIP_ASSUME_TAC THENL
     [ASM SET_TAC[]; ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `z:A->bool = topspace top` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `z:A->bool` o GEN_REWRITE_RULE I
      [CONNECTED_SPACE_CLOPEN_IN]) THEN
    MATCH_MP_TAC(TAUT `p /\ ~q ==> (p ==> q \/ r) ==> r`) THEN CONJ_TAC THENL
     [REWRITE_TAC[closed_in] THEN
      SUBGOAL_THEN `z SUBSET topspace (top:A topology)` ASSUME_TAC THENL
       [EXPAND_TAC "z" THEN SET_TAC[]; ASM_REWRITE_TAC[]] THEN
      CONJ_TAC THEN ONCE_REWRITE_TAC[OPEN_IN_SUBOPEN] THEN
      X_GEN_TAC `y:A` THEN REWRITE_TAC[IN_DIFF] THEN STRIP_TAC THENL
       [ALL_TAC; ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `y:A`) THEN
      (ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC]) THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `v:A->bool` THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `x:A` THEN
      EXPAND_TAC "z" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REMOVE_THEN "cpt" (MP_TAC o SPECL [`top:A topology`; `topspace top:A->bool`]) THEN
  ASM_REWRITE_TAC[GSYM compact_space; DIFF_EQ_EMPTY] THEN
  DISCH_THEN(MATCH_MP_TAC o CONJUNCT1 o CONJUNCT2) THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `y:A` THEN DISCH_TAC THEN
  UNDISCH_TAC `z:A->bool = topspace top` THEN EXPAND_TAC "z" THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* A6. The radial retraction of M - e(0) onto M - e(ball(0,1)) for the      *)
(* inverse e of a chart (pasting on the closed sets e(cball) and the        *)
(* complement of e(ball)).                                                   *)
(* ------------------------------------------------------------------------- *)

let ATOP_CONTINUOUS_ON_NORMALIZE = prove
 (`!s:real^N->bool. ~(vec 0 IN s) ==> (\x. inv(norm x) % x) continuous_on s`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
  REWRITE_TAC[CONTINUOUS_ON_ID; o_DEF] THEN
  MATCH_MP_TAC(REWRITE_RULE[o_DEF] CONTINUOUS_ON_INV) THEN
  REWRITE_TAC[REWRITE_RULE[o_DEF] CONTINUOUS_ON_LIFT_NORM; NORM_EQ_0] THEN
  ASM_MESON_TAC[]);;

let ATOP_BALL_IMAGES = prove
 (`!top w (e:real^N->A) r.
        hausdorff_space top /\ open_in top w /\
        homeomorphic_map (euclidean,subtopology top w) e
        ==> open_in top (IMAGE e (ball(vec 0,r))) /\
            closed_in top (IMAGE e (cball(vec 0,r))) /\
            IMAGE e (:real^N) = w /\ w SUBSET topspace top /\
            (!x y. e x = e y <=> x = y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(w:A->bool) SUBSET topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP HOMEOMORPHIC_IMP_SURJECTIVE_MAP) THEN
  REWRITE_TAC[TOPSPACE_EUCLIDEAN; TOPSPACE_SUBTOPOLOGY] THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `topspace top INTER w:A->bool = w` (SUBST_ALL_TAC) THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_IN_TRANS_FULL THEN EXISTS_TAC `w:A->bool` THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`e:real^N->A`; `euclidean:(real^N)topology`;
                   `subtopology top (w:A->bool)`; `ball(vec 0:real^N,r)`]
                  HOMEOMORPHIC_MAP_OPENNESS) THEN
    ASM_REWRITE_TAC[TOPSPACE_EUCLIDEAN; SUBSET_UNIV; GSYM OPEN_IN; OPEN_BALL];
    MATCH_MP_TAC COMPACT_IN_IMP_CLOSED_IN THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC IMAGE_COMPACT_IN THEN EXISTS_TAC `euclidean:(real^N)topology` THEN
    REWRITE_TAC[COMPACT_IN_EUCLIDEAN; COMPACT_CBALL] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_INTO_FULLTOPOLOGY THEN
    EXISTS_TAC `w:A->bool` THEN ASM_MESON_TAC[HOMEOMORPHIC_IMP_CONTINUOUS_MAP];
    FIRST_ASSUM(MP_TAC o MATCH_MP HOMEOMORPHIC_IMP_INJECTIVE_MAP) THEN
    REWRITE_TAC[TOPSPACE_EUCLIDEAN; IN_UNIV]]);;

let ATOP_BALL_RETRACTION = prove
 (`!top w (e:real^N->A).
        hausdorff_space top /\ open_in top w /\
        homeomorphic_map (euclidean,subtopology top w) e
        ==> ?r. continuous_map
                  (subtopology top (topspace top DELETE e(vec 0)),
                   subtopology top (topspace top DIFF IMAGE e (ball(vec 0,&1)))) r /\
                !y. y IN topspace top DIFF IMAGE e (ball(vec 0,&1)) ==> r y = y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `w:A->bool`; `e:real^N->A`; `&1`]
                ATOP_BALL_IMAGES) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_TAC `g:A->real^N` o GEN_REWRITE_RULE I [HOMEOMORPHIC_MAP_MAPS]) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphic_maps]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[TOPSPACE_EUCLIDEAN; IN_UNIV; TOPSPACE_SUBTOPOLOGY]) THEN
  SUBGOAL_THEN `topspace top INTER w:A->bool = w`
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))
  THENL [ASM SET_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `m = topspace top DELETE (e:real^N->A)(vec 0)` THEN
  EXISTS_TAC `\y:A. if y IN IMAGE (e:real^N->A) (ball(vec 0,&1))
                    then e(inv(norm((g:A->real^N) y)) % g y) else y` THEN
  CONJ_TAC THENL [ALL_TAC; SIMP_TAC[IN_DIFF]] THEN
  SUBGOAL_THEN `!u:real^N. (e:real^N->A) u IN topspace top` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN CONJ_TAC THENL
   [ALL_TAC;
    EXPAND_TAC "m" THEN REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; SUBSET; FORALL_IN_IMAGE] THEN
    X_GEN_TAC `y:A` THEN REWRITE_TAC[IN_INTER; IN_DELETE] THEN STRIP_TAC THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[IN_DIFF] THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `u:real^N` STRIP_ASSUME_TAC o
      GEN_REWRITE_RULE I [IN_IMAGE]) THEN
    ASM_REWRITE_TAC[IN_IMAGE; IN_BALL_0] THEN
    DISCH_THEN(X_CHOOSE_THEN `v:real^N` STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC `norm(v:real^N) < &1` THEN
    FIRST_X_ASSUM(MP_TAC o check (is_eq o concl)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM] THEN
    SUBGOAL_THEN `~(u:real^N = vec 0)` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ASM_SIMP_TAC[REAL_MUL_LINV; NORM_EQ_0; REAL_LT_REFL]]] THEN
  SUBGOAL_THEN `(m:A->bool) SUBSET topspace top` ASSUME_TAC THENL
   [EXPAND_TAC "m" THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `closed_in (subtopology top m) (m INTER IMAGE (e:real^N->A) (cball(vec 0,&1))) /\
    closed_in (subtopology top m)
              (m INTER (topspace top DIFF IMAGE (e:real^N->A) (ball(vec 0,&1))))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC CLOSED_IN_SUBTOPOLOGY_INTER_CLOSED THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CLOSED_IN_DIFF THEN
    ASM_REWRITE_TAC[CLOSED_IN_TOPSPACE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `subtopology top (m:A->bool) closure_of
      {x | x IN topspace (subtopology top m) /\
           x IN IMAGE (e:real^N->A) (ball(vec 0,&1))}
    SUBSET m INTER IMAGE e (cball(vec 0,&1)) /\
    subtopology top (m:A->bool) closure_of
      {x | x IN topspace (subtopology top m) /\
           ~(x IN IMAGE (e:real^N->A) (ball(vec 0,&1)))}
    SUBSET m INTER (topspace top DIFF IMAGE e (ball(vec 0,&1)))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC CLOSURE_OF_MINIMAL THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN
    MP_TAC(ISPECL [`vec 0:real^N`; `&1`] BALL_SUBSET_CBALL) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`subtopology top (m:A->bool)`; `top:A topology`;
    `\y:A. y IN IMAGE (e:real^N->A) (ball(vec 0,&1))`;
    `\y:A. (e:real^N->A)(inv(norm((g:A->real^N) y)) % g y)`; `\y:A. y`]
   CONTINUOUS_MAP_CASES_ALT) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY_MONO THEN
    EXISTS_TAC `m INTER IMAGE (e:real^N->A) (cball(vec 0,&1))` THEN
    ASM_REWRITE_TAC[SUBTOPOLOGY_SUBTOPOLOGY] THEN
    SUBGOAL_THEN `m INTER m INTER IMAGE (e:real^N->A) (cball(vec 0,&1)) =
                  m INTER IMAGE e (cball(vec 0,&1))` SUBST1_TAC THENL
     [SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(\y:A. (e:real^N->A)(inv(norm((g:A->real^N) y)) % g y)) =
                  (e o (\x. inv(norm x) % x)) o g` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
    EXISTS_TAC `subtopology euclidean ((:real^N) DELETE vec 0)` THEN CONJ_TAC THENL
     [REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY_MONO THEN
        EXISTS_TAC `w:A->bool` THEN ASM_REWRITE_TAC[] THEN
        MP_TAC(ISPECL [`vec 0:real^N`; `&1`] BALL_SUBSET_CBALL) THEN ASM SET_TAC[];
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; TOPSPACE_SUBTOPOLOGY; IN_DELETE;
                    IN_UNIV; IN_INTER] THEN
        EXPAND_TAC "m" THEN REWRITE_TAC[IN_DELETE; IN_IMAGE] THEN
        X_GEN_TAC `y:A` THEN STRIP_TAC THEN
        ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]];
      MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
      EXISTS_TAC `euclidean:(real^N)topology` THEN CONJ_TAC THENL
       [REWRITE_TAC[CONTINUOUS_MAP_EUCLIDEAN] THEN
        MATCH_MP_TAC ATOP_CONTINUOUS_ON_NORMALIZE THEN SET_TAC[];
        ASM_MESON_TAC[CONTINUOUS_MAP_INTO_FULLTOPOLOGY]]];
    REWRITE_TAC[SUBTOPOLOGY_SUBTOPOLOGY] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY THEN
    REWRITE_TAC[CONTINUOUS_MAP_ID];
    X_GEN_TAC `y:A` THEN REWRITE_TAC[FRONTIER_OF_CLOSURES; IN_INTER] THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `(y:A) IN IMAGE (e:real^N->A) (cball(vec 0,&1)) /\
      ~(y IN IMAGE e (ball(vec 0,&1)))`
    MP_TAC THENL
     [CONJ_TAC THENL
       [UNDISCH_TAC
         `(y:A) IN subtopology top m closure_of
            {x | x IN topspace (subtopology top m) /\
                 x IN IMAGE (e:real^N->A) (ball(vec 0,&1))}` THEN
        UNDISCH_TAC
         `subtopology top (m:A->bool) closure_of
            {x | x IN topspace (subtopology top m) /\
                 x IN IMAGE (e:real^N->A) (ball(vec 0,&1))}
          SUBSET m INTER IMAGE e (cball(vec 0,&1))` THEN
        SET_TAC[];
        UNDISCH_TAC
         `(y:A) IN subtopology top m closure_of
            (topspace (subtopology top m) DIFF
             {x | x IN topspace (subtopology top m) /\
                  x IN IMAGE (e:real^N->A) (ball(vec 0,&1))})` THEN
        SUBGOAL_THEN
         `topspace (subtopology top m) DIFF
          {x | x IN topspace (subtopology top m) /\
               x IN IMAGE (e:real^N->A) (ball(vec 0,&1))} =
          {x | x IN topspace (subtopology top m) /\
               ~(x IN IMAGE (e:real^N->A) (ball(vec 0,&1)))}`
        SUBST1_TAC THENL [SET_TAC[]; ALL_TAC] THEN
        UNDISCH_TAC
         `subtopology top (m:A->bool) closure_of
            {x | x IN topspace (subtopology top m) /\
                 ~(x IN IMAGE (e:real^N->A) (ball(vec 0,&1)))}
          SUBSET m INTER (topspace top DIFF IMAGE e (ball(vec 0,&1)))` THEN
        SET_TAC[]];
      REWRITE_TAC[IN_IMAGE; IN_BALL_0; IN_CBALL_0] THEN
      DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `u:real^N` STRIP_ASSUME_TAC)
        ASSUME_TAC) THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `norm(u:real^N) = &1`
        (fun th -> REWRITE_TAC[th; REAL_INV_1; VECTOR_MUL_LID]) THEN
      ASM_MESON_TAC[REAL_LE_LT]]]);;

(* ------------------------------------------------------------------------- *)
(* A7. The ball sphere is null-homotopic in M - e(ball): a lifted local     *)
(* orientation kills the boundary map of (M, M - e(0)); the contractible   *)
(* ball makes H_2(e(cball) - e(0)) -> H_2(M - e(0)) zero, so the sphere is  *)
(* zero on H_2; Hurewicz in M - e(0) (simply connected by general          *)
(* position); radial retraction.  No Poincare duality, no H_2(M) = 0.        *)
(* ------------------------------------------------------------------------- *)

let ATOP_GENERATOR_IMAGE_KILLS_BOUNDARY = prove
 (`!top:A topology x c a.
        a IN group_carrier(relative_homology_group(&3,top,topspace top DELETE x)) /\
        subgroup_generated (relative_homology_group(&3,top,topspace top DELETE x)) {a} =
        relative_homology_group(&3,top,topspace top DELETE x) /\
        c IN group_carrier(homology_group(&3,top)) /\
        hom_induced (&3) (top,{}) (top,topspace top DELETE x) (\x. x) c = a
        ==> !u. u IN group_carrier(relative_homology_group(&3,top,topspace top DELETE x))
                ==> hom_boundary (&3) (top,topspace top DELETE x) u =
                    group_id(homology_group(&2,subtopology top (topspace top DELETE x)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`&3:int`; `top:A topology`; `topspace top DELETE (x:A)`]
                HOMOLOGY_EXACTNESS_AXIOM_1) THEN
  REWRITE_TAC[group_exactness; INT_ARITH `&3:int - &1 = &2`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `group_carrier(relative_homology_group(&3,top,topspace top DELETE (x:A))) SUBSET
    group_image (homology_group(&3,top),
                 relative_homology_group(&3,top,topspace top DELETE x))
                (hom_induced (&3) (top,{}) (top,topspace top DELETE x) (\x. x))`
  MP_TAC THENL
   [FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [SYM th]) THEN
    MATCH_MP_TAC SUBGROUP_GENERATED_MINIMAL THEN CONJ_TAC THENL
     [REWRITE_TAC[SING_SUBSET; group_image; IN_IMAGE] THEN ASM_MESON_TAC[];
      MATCH_MP_TAC SUBGROUP_GROUP_IMAGE THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[group_kernel; SUBSET; IN_ELIM_THM] THEN MESON_TAC[]);;

let ATOP_BALL_CONTRACTIBLE = prove
 (`!top w (e:real^N->A) r.
        open_in top w /\ homeomorphic_map (euclidean,subtopology top w) e
        ==> contractible_space (subtopology top (IMAGE e (cball(vec 0,r))))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `IMAGE (e:real^N->A) (:real^N) = w /\ w SUBSET topspace top`
  STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP HOMEOMORPHIC_IMP_SURJECTIVE_MAP) THEN
    REWRITE_TAC[TOPSPACE_EUCLIDEAN; TOPSPACE_SUBTOPOLOGY] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP OPEN_IN_SUBSET) THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `subtopology euclidean (cball(vec 0:real^N,r)) homeomorphic_space
    subtopology top (IMAGE (e:real^N->A) (cball(vec 0,r)))`
  MP_TAC THENL
   [REWRITE_TAC[HOMEOMORPHIC_SPACE] THEN EXISTS_TAC `e:real^N->A` THEN
    SUBGOAL_THEN
     `subtopology top (IMAGE (e:real^N->A) (cball(vec 0,r))) =
      subtopology (subtopology top w) (IMAGE e (cball(vec 0,r)))`
    SUBST1_TAC THENL
     [REWRITE_TAC[SUBTOPOLOGY_SUBTOPOLOGY] THEN AP_TERM_TAC THEN ASM SET_TAC[];
      MATCH_MP_TAC HOMEOMORPHIC_MAP_SUBTOPOLOGIES THEN
      ASM_REWRITE_TAC[TOPSPACE_EUCLIDEAN; TOPSPACE_SUBTOPOLOGY] THEN ASM SET_TAC[]];
    DISCH_THEN(SUBST1_TAC o SYM o MATCH_MP HOMEOMORPHIC_SPACE_CONTRACTIBILITY) THEN
    REWRITE_TAC[CONTRACTIBLE_SPACE_EUCLIDEAN] THEN
    MATCH_MP_TAC CONVEX_IMP_CONTRACTIBLE THEN REWRITE_TAC[CONVEX_CBALL]]);;

let ATOP_SPHERE_H2_ZERO = prove
 (`!top w (e:real^3->A) a c.
        hausdorff_space top /\ open_in top w /\
        homeomorphic_map (euclidean,subtopology top w) e /\
        a IN group_carrier(relative_homology_group(&3,top,topspace top DELETE e(vec 0))) /\
        subgroup_generated (relative_homology_group(&3,top,topspace top DELETE e(vec 0))) {a} =
        relative_homology_group(&3,top,topspace top DELETE e(vec 0)) /\
        c IN group_carrier(homology_group(&3,top)) /\
        hom_induced (&3) (top,{}) (top,topspace top DELETE e(vec 0)) (\x. x) c = a
        ==> !z. z IN group_carrier
                       (homology_group(&2,subtopology euclidean (sphere(vec 0:real^3,&1))))
                ==> hom_induced (&2) (subtopology euclidean (sphere(vec 0,&1)),{})
                       (subtopology top (topspace top DELETE e(vec 0)),{}) e z =
                    group_id(homology_group(&2,subtopology top (topspace top DELETE e(vec 0))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `(e:real^3->A)(vec 0)`; `c:((num->real)->A)frag->bool`;
                 `a:((num->real)->A)frag->bool`] ATOP_GENERATOR_IMAGE_KILLS_BOUNDARY) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `w:A->bool`; `e:real^3->A`; `&1`]
                ATOP_BALL_IMAGES) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `b = IMAGE (e:real^3->A) (cball(vec 0,&1))` THEN
  ABBREV_TAC `m = topspace top DELETE (e:real^3->A)(vec 0)` THEN
  SUBGOAL_THEN `b SUBSET topspace (top:A topology) /\ (e:real^3->A)(vec 0) IN b`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "b" THEN CONJ_TAC THENL
     [UNDISCH_TAC `IMAGE (e:real^3->A) (:real^3) = w` THEN
      UNDISCH_TAC `(w:A->bool) SUBSET topspace top` THEN SET_TAC[];
      REWRITE_TAC[IN_IMAGE] THEN MESON_TAC[CENTRE_IN_CBALL; REAL_POS]];
    ALL_TAC] THEN
  SUBGOAL_THEN `trivial_group(homology_group(&2,subtopology top (b:A->bool)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC TRIVIAL_HOMOLOGY_GROUP_CONTRACTIBLE_SPACE THEN
    CONV_TAC INT_REDUCE_CONV THEN EXPAND_TAC "b" THEN
    MATCH_MP_TAC ATOP_BALL_CONTRACTIBLE THEN EXISTS_TAC `w:A->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!u. u IN group_carrier(homology_group(&2,subtopology top (b DELETE (e:real^3->A)(vec 0))))
        ==> hom_induced (&2) (subtopology top (b DELETE e(vec 0)),{})
                             (subtopology top m,{}) (\x. x) u =
            group_id(homology_group(&2,subtopology top (m:A->bool)))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`&3:int`; `subtopology top (b:A->bool)`;
                   `b DELETE (e:real^3->A)(vec 0)`] HOMOLOGY_EXACTNESS_AXIOM_2) THEN
    REWRITE_TAC[group_exactness; SUBTOPOLOGY_SUBTOPOLOGY; INT_ARITH `&3:int - &1 = &2`] THEN
    SUBGOAL_THEN `b INTER (b DELETE (e:real^3->A)(vec 0)) = b DELETE e(vec 0)` SUBST1_TAC
    THENL [SET_TAC[]; ALL_TAC] THEN
    STRIP_TAC THEN X_GEN_TAC `u:((num->real)->A)frag->bool` THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `u IN group_image (relative_homology_group (&3,subtopology top b,b DELETE (e:real^3->A)(vec 0)),
                        homology_group (&2,subtopology top (b DELETE e(vec 0))))
                       (hom_boundary (&3) (subtopology top b,b DELETE e(vec 0)))`
    MP_TAC THENL
     [ASM_REWRITE_TAC[group_kernel; IN_ELIM_THM] THEN
      UNDISCH_TAC `trivial_group(homology_group(&2,subtopology top (b:A->bool)))` THEN
      REWRITE_TAC[trivial_group] THEN DISCH_THEN(MP_TAC o MATCH_MP (SET_RULE
        `s = {a:C} ==> !x. x IN s ==> x = a`)) THEN
      DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[homology_group; HOM_INDUCED];
      ALL_TAC] THEN
    REWRITE_TAC[group_image; IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `v:((num->real)->A)frag->bool` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`&3:int`; `subtopology top (b:A->bool)`; `b DELETE (e:real^3->A)(vec 0)`;
                   `top:A topology`; `m:A->bool`; `\x:A. x`] NATURALITY_HOM_INDUCED) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[CONTINUOUS_MAP_ID; IMAGE_ID] THEN
      ASM_SIMP_TAC[CONTINUOUS_MAP_FROM_SUBTOPOLOGY; CONTINUOUS_MAP_ID] THEN
      EXPAND_TAC "m" THEN ASM SET_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o C AP_THM `v:((num->real)->A)frag->bool`) THEN
    REWRITE_TAC[o_THM; SUBTOPOLOGY_SUBTOPOLOGY; INT_ARITH `&3:int - &1 = &2`] THEN
    SUBGOAL_THEN `b INTER (b DELETE (e:real^3->A)(vec 0)) = b DELETE e(vec 0)` SUBST1_TAC
    THENL [SET_TAC[]; ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[HOM_INDUCED];
    ALL_TAC] THEN
  X_GEN_TAC `z:((num->real)->real^3)frag->bool` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `continuous_map (subtopology euclidean (sphere(vec 0:real^3,&1)),
                    subtopology top (b DELETE (e:real^3->A)(vec 0))) e`
  ASSUME_TAC THENL
   [REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY THEN
      MATCH_MP_TAC CONTINUOUS_MAP_INTO_FULLTOPOLOGY THEN EXISTS_TAC `w:A->bool` THEN
      ASM_MESON_TAC[HOMEOMORPHIC_IMP_CONTINUOUS_MAP];
      REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY; SUBSET; FORALL_IN_IMAGE; IN_DELETE] THEN
      X_GEN_TAC `u:real^3` THEN REWRITE_TAC[IN_SPHERE_0] THEN DISCH_TAC THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [EXPAND_TAC "b" THEN REWRITE_TAC[IN_IMAGE; IN_CBALL_0] THEN
        EXISTS_TAC `u:real^3` THEN ASM_REWRITE_TAC[REAL_LE_REFL];
        DISCH_THEN(SUBST_ALL_TAC) THEN
        RULE_ASSUM_TAC(REWRITE_RULE[NORM_0]) THEN ASM_MESON_TAC[REAL_OF_NUM_EQ; ARITH_EQ]]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`&2:int`; `subtopology euclidean (sphere(vec 0:real^3,&1))`;
                 `{}:real^3->bool`; `subtopology top (b DELETE (e:real^3->A)(vec 0))`;
                 `{}:A->bool`; `subtopology top (m:A->bool)`; `{}:A->bool`;
                 `e:real^3->A`; `\x:A. x`] HOM_INDUCED_COMPOSE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IMAGE_CLAUSES; EMPTY_SUBSET; CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN
    SIMP_TAC[CONTINUOUS_MAP_FROM_SUBTOPOLOGY; CONTINUOUS_MAP_ID; IMAGE_ID] THEN
    EXPAND_TAC "m" THEN REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\x:A. x) o (e:real^3->A) = e` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[o_THM] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[homology_group; HOM_INDUCED]);;

let ATOP_NULL_SPHERE = prove
 (`ATOP_FUNDAMENTAL_CLASS_STATEMENT (:A) (:3) /\
   ATOP_PUNCTURED_SIMPLY_CONNECTED_STATEMENT (:A) (:3) /\
   ATOP_HUREWICZ2_STATEMENT (:A)
   ==> ATOP_NULL_SPHERE_STATEMENT (:A)`,
  REWRITE_TAC[ATOP_FUNDAMENTAL_CLASS_STATEMENT;
              ATOP_PUNCTURED_SIMPLY_CONNECTED_STATEMENT;
              ATOP_HUREWICZ2_STATEMENT; ATOP_NULL_SPHERE_STATEMENT; DIMINDEX_3] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "fc")
    (CONJUNCTS_THEN2 (LABEL_TAC "pu") (LABEL_TAC "hu"))) THEN
  MAP_EVERY X_GEN_TAC [`top:A topology`; `w:A->bool`; `e:real^3->A`] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `mu:A->((num->real)->A)frag->bool` o
    REWRITE_RULE[homology_orientable]) THEN
  MP_TAC(ISPECL [`top:A topology`; `w:A->bool`; `e:real^3->A`; `&1`]
                ATOP_BALL_IMAGES) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(e:real^3->A)(vec 0) IN topspace top` ASSUME_TAC THENL
   [UNDISCH_TAC `IMAGE (e:real^3->A) (:real^3) = w` THEN
    UNDISCH_TAC `(w:A->bool) SUBSET topspace top` THEN SET_TAC[];
    ALL_TAC] THEN
  REMOVE_THEN "fc" (MP_TAC o SPECL [`top:A topology`; `mu:A->((num->real)->A)frag->bool`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:((num->real)->A)frag->bool` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(MP_TAC o SPEC `(e:real^3->A)(vec 0)` o CONJUNCT1 o
    GEN_REWRITE_RULE I [homology_orientation]) THEN
  ASM_REWRITE_TAC[homology_local_orientation] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `w:A->bool`; `e:real^3->A`;
                 `(mu:A->((num->real)->A)frag->bool) ((e:real^3->A)(vec 0))`;
                 `c:((num->real)->A)frag->bool`] ATOP_SPHERE_H2_ZERO) THEN
  ASM_SIMP_TAC[] THEN DISCH_TAC THEN
  REMOVE_THEN "pu" (MP_TAC o SPECL [`top:A topology`; `(e:real^3->A)(vec 0)`]) THEN
  ASM_REWRITE_TAC[ARITH_LE] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `continuous_map (subtopology euclidean (sphere(vec 0:real^3,&1)),
                    subtopology top (topspace top DELETE (e:real^3->A)(vec 0))) e`
  ASSUME_TAC THENL
   [REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY THEN
      MATCH_MP_TAC CONTINUOUS_MAP_INTO_FULLTOPOLOGY THEN EXISTS_TAC `w:A->bool` THEN
      ASM_MESON_TAC[HOMEOMORPHIC_IMP_CONTINUOUS_MAP];
      REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY; SUBSET; FORALL_IN_IMAGE;
                  IN_DELETE; IN_SPHERE_0] THEN
      X_GEN_TAC `u:real^3` THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL
       [UNDISCH_TAC `IMAGE (e:real^3->A) (:real^3) = w` THEN
        UNDISCH_TAC `(w:A->bool) SUBSET topspace top` THEN SET_TAC[];
        DISCH_THEN SUBST_ALL_TAC THEN
        RULE_ASSUM_TAC(REWRITE_RULE[NORM_0]) THEN ASM_MESON_TAC[REAL_OF_NUM_EQ; ARITH_EQ]]];
    ALL_TAC] THEN
  REMOVE_THEN "hu" (MP_TAC o SPECL
   [`subtopology top (topspace top DELETE (e:real^3->A)(vec 0))`; `e:real^3->A`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `a:A`) THEN
  MP_TAC(ISPECL [`top:A topology`; `w:A->bool`; `e:real^3->A`] ATOP_BALL_RETRACTION) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `r:A->A` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `(r:A->A) a` THEN
  MP_TAC(ISPECL
   [`\h:real^3->A. T`; `\h:real^3->A. T`; `e:real^3->A`; `(\x. a):real^3->A`;
    `r:A->A`; `subtopology euclidean (sphere(vec 0:real^3,&1))`;
    `subtopology top (topspace top DELETE (e:real^3->A)(vec 0))`;
    `subtopology top (topspace top DIFF IMAGE (e:real^3->A) (ball(vec 0,&1)))`]
   HOMOTOPIC_WITH_COMPOSE_CONTINUOUS_MAP_LEFT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC HOMOTOPIC_WITH_EQ THEN
  MAP_EVERY EXISTS_TAC [`(r:A->A) o (e:real^3->A)`; `(r:A->A) o (\x:real^3. a)`] THEN
  ASM_REWRITE_TAC[o_THM; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY; IN_SPHERE_0] THEN
  X_GEN_TAC `u:real^3` THEN DISCH_TAC THEN CONV_TAC SYM_CONV THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_DIFF; IN_IMAGE; IN_BALL_0] THEN
  CONJ_TAC THENL
   [UNDISCH_TAC `IMAGE (e:real^3->A) (:real^3) = w` THEN
    UNDISCH_TAC `(w:A->bool) SUBSET topspace top` THEN SET_TAC[];
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[REAL_LT_REFL]]);;

(* ------------------------------------------------------------------------- *)
(* A8. Everything together: the three topology statements of Part 4 from the *)
(* algebraic topology statements (instances at the types Part 4 uses).       *)
(* ------------------------------------------------------------------------- *)

let ATOP_P4_TOPOLOGY_FROM_LEAVES = prove
 (`ATOP_LOCAL_HOMOLOGY_COMPACT_STATEMENT (:A) (:3) /\
   ATOP_LOCAL_HOMOLOGY_COMPACT_STATEMENT (:B) (:3) /\
   ATOP_LOCAL_HOMOLOGY_COMPACT_STATEMENT (:real^4) (:3) /\
   ATOP_MANIFOLD_LOCAL_HOMOLOGY_STATEMENT (:B) (:3) /\
   ATOP_MANIFOLD_LOCAL_HOMOLOGY_STATEMENT (:real^4) (:3) /\
   ATOP_DEGREE_ONE_LOCAL_STATEMENT (:B) (:B) /\
   ATOP_DEGREE_ONE_LOCAL_STATEMENT (:real^4) (:A) /\
   ATOP_PUNCTURED_SIMPLY_CONNECTED_STATEMENT (:A) (:3) /\
   ATOP_HUREWICZ2_STATEMENT (:A) /\
   ATOP_S3_FROM_NULL_SPHERE_STATEMENT (:A) /\
   ATOP_SC_ORIENTABLE_STATEMENT (:A) (:3) /\
   ATOP_SWEEPOUT_SMOOTHING_STATEMENT (:A) (:3) /\
   ATOP_SUSPENSION_STATEMENT (:A)
   ==> P4_DEGREE_ONE_STATEMENT (:B) (:B) /\
       P4_SC_DEGREE_ONE_STATEMENT (:A) /\
       P4_SMOOTHING_STATEMENT (:A)`,
  DISCH_TAC THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC ATOP_P4_DEGREE_ONE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC ATOP_TOP_HOMOLOGY_INJECTIVE THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC ATOP_P4_SC_DEGREE_ONE THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC ATOP_NULL_SPHERE THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC ATOP_FUNDAMENTAL_CLASS THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC ATOP_TOP_HOMOLOGY_INJECTIVE THEN ASM_REWRITE_TAC[]];
    MATCH_MP_TAC ATOP_P4_SMOOTHING THEN ASM_REWRITE_TAC[]]);;


(* ------------------------------------------------------------------------- *)
(* The combined reduction, and the three Part 4 topology statements proved   *)
(* from the results of the other pc_top files.                               *)
(* ------------------------------------------------------------------------- *)

let ATOP_P4_TOPOLOGY = prove
 (`ATOP_LOCAL_HOMOLOGY_COMPACT_STATEMENT (:A) (:3) /\
   ATOP_LOCAL_HOMOLOGY_COMPACT_STATEMENT (:B) (:3) /\
   ATOP_LOCAL_HOMOLOGY_COMPACT_STATEMENT (:real^4) (:3) /\
   ATOP_MANIFOLD_LOCAL_HOMOLOGY_STATEMENT (:B) (:3) /\
   ATOP_MANIFOLD_LOCAL_HOMOLOGY_STATEMENT (:real^4) (:3) /\
   ATOP_PUNCTURED_SIMPLY_CONNECTED_STATEMENT (:A) (:3) /\
   ATOP_HUREWICZ2_STATEMENT (:A) /\
   ATOP_S3_FROM_NULL_SPHERE_STATEMENT (:A) /\
   ATOP_SC_ORIENTABLE_STATEMENT (:A) (:3) /\
   ATOP_SWEEPOUT_SMOOTHING_STATEMENT (:A) (:3) /\
   ATOP_SUSPENSION_STATEMENT (:A)
   ==> P4_DEGREE_ONE_STATEMENT (:B) (:B) /\
       P4_SC_DEGREE_ONE_STATEMENT (:A) /\
       P4_SMOOTHING_STATEMENT (:A)`,
  DISCH_TAC THEN MATCH_MP_TAC ATOP_P4_TOPOLOGY_FROM_LEAVES THEN
  ASM_REWRITE_TAC[ATOP_DEGREE_ONE_LOCAL]);;

let ATOP_P4_DEGREE_ONE_PROVED = prove
 (`P4_DEGREE_ONE_STATEMENT (:A) (:B)`,
  MATCH_MP_TAC ATOP_P4_DEGREE_ONE THEN REWRITE_TAC[ATOP_DEGREE_ONE_LOCAL] THEN
  MATCH_MP_TAC ATOP_TOP_HOMOLOGY_INJECTIVE THEN
  REWRITE_TAC[ATOP_LOCAL_HOMOLOGY_COMPACT; ATOP_MANIFOLD_LOCAL_HOMOLOGY]);;

let ATOP_P4_SC_DEGREE_ONE_PROVED = prove
 (`P4_SC_DEGREE_ONE_STATEMENT (:A)`,
  MP_TAC ATOP_P4_TOPOLOGY THEN
  REWRITE_TAC[ATOP_LOCAL_HOMOLOGY_COMPACT; ATOP_MANIFOLD_LOCAL_HOMOLOGY;
              ATOP_PUNCTURED_SIMPLY_CONNECTED; ATOP_HUREWICZ2; ATOP_S3_FROM_NULL_SPHERE;
              ATOP_SC_ORIENTABLE; ATOP_SWEEPOUT_SMOOTHING; ATOP_SUSPENSION] THEN
  SIMP_TAC[]);;

let ATOP_P4_SMOOTHING_PROVED = prove
 (`P4_SMOOTHING_STATEMENT (:A)`,
  MATCH_MP_TAC ATOP_P4_SMOOTHING THEN
  REWRITE_TAC[ATOP_SWEEPOUT_SMOOTHING; ATOP_SUSPENSION]);;

(* The instances consumed by the Part 4 assembly (pc_p4_align, pc_p4_cm).   *)

let ATOP_P4_TOPOLOGY_INSTANCES = prove
 (`P4_DEGREE_ONE_STATEMENT (:A+num#num#real^3) (:A+num#num#real^3) /\
   P4_SC_DEGREE_ONE_STATEMENT (:A) /\ P4_SMOOTHING_STATEMENT (:A)`,
  REWRITE_TAC[ATOP_P4_DEGREE_ONE_PROVED; ATOP_P4_SC_DEGREE_ONE_PROVED;
              ATOP_P4_SMOOTHING_PROVED]);;

