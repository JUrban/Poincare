(* ========================================================================= *)
(* pc_smt_leafsep: the leaf sphere of a cut system (M11, part 1).  In a     *)
(* smooth 3-manifold whose components are simply connected every neck      *)
(* sphere separates (SMT_SC_SPHERE_SEP, pc_smt_sep); the sides of a neck   *)
(* sphere are the components of its complement through the two collar     *)
(* halves.  For finitely many disjoint necks some side meets no other      *)
(* neck: a side containing a neck j contains a side of j that contains     *)
(* fewer necks (minimal counterexample, num_WOP).                          *)
(*                                                                           *)
(* Neck facts and sides as components.                                      *)
(* ========================================================================= *)

needs "src/pc_smt_sep.ml";;

prioritize_real();;
type_invention_error := true;;

let LSP_NECK_FACTS = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) e.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\ mfd_neck_chart top atlas e
        ==> open_in top (IMAGE e (annulus (&1 / &2) (&2))) /\
            connected_in top (IMAGE e (annulus (&1 / &2) (&2))) /\
            closed_in top (IMAGE e (sphere(vec 0,&1))) /\
            connected_in top (IMAGE e (sphere(vec 0,&1))) /\
            ~(IMAGE e (sphere(vec 0,&1)) = {}) /\
            IMAGE e (sphere(vec 0,&1)) SUBSET IMAGE e (annulus (&1 / &2) (&2)) /\
            IMAGE e (annulus (&1 / &2) (&2)) SUBSET topspace top /\
            (!r. &1 / &2 < r /\ r < &2 /\ ~(r = &1)
                 ==> e(r % basis 1) IN
                     IMAGE e (annulus (&1 / &2) (&2)) DIFF IMAGE e (sphere(vec 0,&1)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mfd_neck_chart] THEN STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `e':A->real^3` STRIP_ASSUME_TAC o MATCH_MP MFD_PARAM_MAPS) THEN
  SUBGOAL_THEN `sphere(vec 0:real^3,&1) SUBSET annulus (&1 / &2) (&2)` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_SPHERE_0; annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `connected(annulus (&1 / &2) (&2):real^3->bool) /\
                connected(sphere(vec 0:real^3,&1))` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`vec 0:real^3`; `&1 / &2`; `&2`] (CONJUNCT1 CONNECTED_ANNULUS)) THEN
      REWRITE_TAC[DIMINDEX_3; ARITH; VECTOR_SUB_RZERO; annulus];
      MATCH_MP_TAC CONNECTED_SPHERE THEN REWRITE_TAC[DIMINDEX_3; ARITH]];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    MATCH_MP_TAC CONNECTED_IN_CONTINUOUS_MAP_IMAGE THEN
    EXISTS_TAC `subtopology euclidean (annulus (&1 / &2) (&2):real^3->bool)` THEN
    ASM_REWRITE_TAC[CONNECTED_IN_ABSOLUTE; CONNECTED_IN_EUCLIDEAN];
    MATCH_MP_TAC COMPACT_IN_IMP_CLOSED_IN THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MFD_PARAM_COMPACT_IMAGE THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`;
                          `annulus (&1 / &2) (&2):real^3->bool`] THEN
    ASM_REWRITE_TAC[COMPACT_SPHERE];
    MATCH_MP_TAC CONNECTED_IN_CONTINUOUS_MAP_IMAGE THEN
    EXISTS_TAC `subtopology euclidean (sphere(vec 0:real^3,&1))` THEN
    ASM_REWRITE_TAC[CONNECTED_IN_ABSOLUTE; CONNECTED_IN_EUCLIDEAN] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY_MONO THEN
    EXISTS_TAC `annulus (&1 / &2) (&2):real^3->bool` THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[IMAGE_EQ_EMPTY] THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    EXISTS_TAC `basis 1:real^3` THEN
    SIMP_TAC[IN_SPHERE_0; NORM_BASIS; DIMINDEX_3; ARITH];
    MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC OPEN_IN_SUBSET THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `r:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `norm(r % basis 1:real^3) = r` ASSUME_TAC THENL
     [SIMP_TAC[NORM_MUL; NORM_BASIS; DIMINDEX_3; ARITH] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(r % basis 1:real^3) IN annulus (&1 / &2) (&2)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[annulus; IN_ELIM_THM]; ALL_TAC] THEN
    REWRITE_TAC[IN_DIFF] THEN CONJ_TAC THENL
     [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE; IN_SPHERE_0] THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real^3` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(r % basis 1:real^3) = u` MP_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o AP_TERM `e':A->real^3`) THEN
      SUBGOAL_THEN `(u:real^3) IN annulus (&1 / &2) (&2)` ASSUME_TAC THENL
       [ASM_REWRITE_TAC[annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[];
      DISCH_THEN(MP_TAC o AP_TERM `norm:real^3->real`) THEN ASM_REWRITE_TAC[]]]);;

(* Sides: components of the complement of a closed set, open and maximal.   *)

let LSP_SIDE = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) S (p:A).
        smooth_manifold_atlas top atlas /\ closed_in top S /\ p IN topspace top DIFF S
        ==> open_in top (connected_component_of (subtopology top (topspace top DIFF S)) p) /\
            connected_in top (connected_component_of (subtopology top (topspace top DIFF S)) p) /\
            p IN connected_component_of (subtopology top (topspace top DIFF S)) p /\
            connected_component_of (subtopology top (topspace top DIFF S)) p SUBSET
            topspace top DIFF S /\
            (!K. connected_in top K /\ K SUBSET topspace top DIFF S /\
                 ~(K INTER connected_component_of (subtopology top (topspace top DIFF S)) p = {})
                 ==> K SUBSET connected_component_of (subtopology top (topspace top DIFF S)) p)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `O = topspace top DIFF (S:A->bool)` THEN
  SUBGOAL_THEN `open_in top (O:A->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "O" THEN MATCH_MP_TAC OPEN_IN_DIFF THEN
    ASM_REWRITE_TAC[OPEN_IN_TOPSPACE];
    ALL_TAC] THEN
  SUBGOAL_THEN `locally_connected_space (subtopology top (O:A->bool))` ASSUME_TAC THENL
   [MATCH_MP_TAC LOCALLY_CONNECTED_SPACE_OPEN_SUBSET THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC LOCALLY_PATH_CONNECTED_IMP_LOCALLY_CONNECTED_SPACE THEN
    MATCH_MP_TAC GEO_MANIFOLD_LOCALLY_PATH_CONNECTED THEN
    EXISTS_TAC `atlas:((A->bool)#(A->real^N))->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `topspace(subtopology top (O:A->bool)) = O` ASSUME_TAC THENL
   [REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN EXPAND_TAC "O" THEN SET_TAC[]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_IN_TRANS_FULL THEN EXISTS_TAC `O:A->bool` THEN
    ASM_SIMP_TAC[OPEN_IN_CONNECTED_COMPONENT_OF_LOCALLY_CONNECTED_SPACE];
    MP_TAC(ISPECL [`subtopology top (O:A->bool)`; `p:A`]
      CONNECTED_IN_CONNECTED_COMPONENT_OF) THEN
    SIMP_TAC[CONNECTED_IN_SUBTOPOLOGY];
    REWRITE_TAC[IN] THEN REWRITE_TAC[CONNECTED_COMPONENT_OF_REFL] THEN ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`subtopology top (O:A->bool)`; `p:A`]
      CONNECTED_COMPONENT_OF_SUBSET_TOPSPACE) THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `K:A->bool` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `x:A` MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
    REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `connected_component_of (subtopology top O) (p:A) =
      connected_component_of (subtopology top O) x`
    SUBST1_TAC THENL
     [REWRITE_TAC[CONNECTED_COMPONENT_OF_EQ] THEN DISJ2_TAC THEN
      ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [ASM SET_TAC[]; ASM_MESON_TAC[IN]];
      MATCH_MP_TAC CONNECTED_COMPONENT_OF_MAXIMAL THEN
      ASM_REWRITE_TAC[CONNECTED_IN_SUBTOPOLOGY]]]);;

(* The two sides of a neck sphere.                                           *)

let lsp_side = new_definition
 `lsp_side (top:A topology) (e:real^3->A) (r:real) =
    connected_component_of (subtopology top (topspace top DIFF IMAGE e (sphere(vec 0,&1))))
                           (e(r % basis 1))`;;

let LSP_SIDES = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) e.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        mfd_neck_chart top atlas e /\ apx_sphere_sep top atlas
        ==> DISJOINT (lsp_side top e (&3 / &4)) (lsp_side top e (&4 / &3)) /\
            !r. (r = &3 / &4 \/ r = &4 / &3)
                ==> open_in top (lsp_side top e r) /\ connected_in top (lsp_side top e r) /\
                    e(r % basis 1) IN lsp_side top e r /\
                    lsp_side top e r SUBSET topspace top DIFF IMAGE e (sphere(vec 0,&1)) /\
                    (!K. connected_in top K /\
                         K SUBSET topspace top DIFF IMAGE e (sphere(vec 0,&1)) /\
                         ~(K INTER lsp_side top e r = {})
                         ==> K SUBSET lsp_side top e r)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `e:real^3->A`]
    LSP_NECK_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN CONJ_TAC THENL
   [REWRITE_TAC[lsp_side; CONNECTED_COMPONENT_OF_DISJOINT] THEN
    UNDISCH_TAC `apx_sphere_sep top (atlas:((A->bool)#(A->real^3))->bool)` THEN
    REWRITE_TAC[apx_sphere_sep; apx_separates] THEN
    DISCH_THEN(MP_TAC o SPEC `e:real^3->A`) THEN ASM_SIMP_TAC[];
    X_GEN_TAC `r:real` THEN DISCH_TAC THEN REWRITE_TAC[lsp_side] THEN
    MATCH_MP_TAC(INST_TYPE [`:3`,`:N`] LSP_SIDE) THEN
    EXISTS_TAC `atlas:((A->bool)#(A->real^3))->bool` THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(e:real^3->A)(r % basis 1) IN
                  IMAGE e (annulus (&1 / &2) (&2)) DIFF IMAGE e (sphere(vec 0,&1))`
    MP_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN
      FIRST_X_ASSUM(DISJ_CASES_THEN SUBST1_TAC) THEN REAL_ARITH_TAC;
      UNDISCH_TAC `IMAGE (e:real^3->A) (annulus (&1 / &2) (&2)) SUBSET topspace top` THEN
      SET_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* The leaf.  A side of neck i containing neck j contains the                *)
(* side of j away from the sphere of i, which contains fewer necks; so a    *)
(* side with the fewest necks meets no other neck.                          *)
(* ------------------------------------------------------------------------- *)

let LSP_LEAF = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) J (e:num->real^3->A).
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\ apx_sphere_sep top atlas /\
        FINITE J /\ ~(J = {}) /\
        (!i. i IN J ==> mfd_neck_chart top atlas (e i)) /\
        (!i j. i IN J /\ j IN J /\ ~(i = j)
               ==> DISJOINT (IMAGE (e i) (annulus (&1 / &2) (&2)))
                            (IMAGE (e j) (annulus (&1 / &2) (&2))))
        ==> ?i r. i IN J /\ (r = &3 / &4 \/ r = &4 / &3) /\
                  !j. j IN J /\ ~(j = i)
                      ==> DISJOINT (IMAGE (e j) (annulus (&1 / &2) (&2)))
                                   (lsp_side top (e i) r)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "neck")
    (LABEL_TAC "disj"))))))) THEN
  SUBGOAL_THEN
   `!i. i IN J
        ==> open_in top (IMAGE ((e:num->real^3->A) i) (annulus (&1 / &2) (&2))) /\
            connected_in top (IMAGE (e i) (annulus (&1 / &2) (&2))) /\
            closed_in top (IMAGE (e i) (sphere(vec 0,&1))) /\
            connected_in top (IMAGE (e i) (sphere(vec 0,&1))) /\
            ~(IMAGE (e i) (sphere(vec 0,&1)) = {}) /\
            IMAGE (e i) (sphere(vec 0,&1)) SUBSET IMAGE (e i) (annulus (&1 / &2) (&2)) /\
            IMAGE (e i) (annulus (&1 / &2) (&2)) SUBSET topspace top /\
            (!r. &1 / &2 < r /\ r < &2 /\ ~(r = &1)
                 ==> e i (r % basis 1) IN
                     IMAGE (e i) (annulus (&1 / &2) (&2)) DIFF IMAGE (e i) (sphere(vec 0,&1)))`
  (LABEL_TAC "nf") THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN MATCH_MP_TAC LSP_NECK_FACTS THEN
    EXISTS_TAC `atlas:((A->bool)#(A->real^3))->bool` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. i IN J
        ==> DISJOINT (lsp_side top ((e:num->real^3->A) i) (&3 / &4))
                     (lsp_side top (e i) (&4 / &3)) /\
            !r. (r = &3 / &4 \/ r = &4 / &3)
                ==> open_in top (lsp_side top (e i) r) /\
                    connected_in top (lsp_side top (e i) r) /\
                    e i (r % basis 1) IN lsp_side top (e i) r /\
                    lsp_side top (e i) r SUBSET
                    topspace top DIFF IMAGE (e i) (sphere(vec 0,&1)) /\
                    (!K. connected_in top K /\
                         K SUBSET topspace top DIFF IMAGE (e i) (sphere(vec 0,&1)) /\
                         ~(K INTER lsp_side top (e i) r = {})
                         ==> K SUBSET lsp_side top (e i) r)`
  (LABEL_TAC "sf") THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN MATCH_MP_TAC LSP_SIDES THEN
    EXISTS_TAC `atlas:((A->bool)#(A->real^3))->bool` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  (* a neck j of another index avoids the sphere of i *)
  SUBGOAL_THEN
   `!i j. i IN J /\ j IN J /\ ~(i = j)
          ==> IMAGE ((e:num->real^3->A) j) (annulus (&1 / &2) (&2)) SUBSET
              topspace top DIFF IMAGE (e i) (sphere(vec 0,&1))`
  (LABEL_TAC "avoid") THENL
   [REPEAT STRIP_TAC THEN
    USE_THEN "nf" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th (ASSUME `(i:num) IN J`))) THEN
    USE_THEN "nf" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th (ASSUME `(j:num) IN J`))) THEN
    USE_THEN "disj" (MP_TAC o SPECL [`i:num`; `j:num`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MAP_EVERY UNDISCH_TAC
     [`IMAGE ((e:num->real^3->A) i) (sphere(vec 0,&1)) SUBSET
       IMAGE (e i) (annulus (&1 / &2) (&2))`;
      `IMAGE ((e:num->real^3->A) j) (annulus (&1 / &2) (&2)) SUBSET topspace top`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  (* dichotomy: such a neck lies in a side of i or misses it *)
  SUBGOAL_THEN
   `!i j r. i IN J /\ j IN J /\ ~(i = j) /\ (r = &3 / &4 \/ r = &4 / &3)
            ==> IMAGE ((e:num->real^3->A) j) (annulus (&1 / &2) (&2)) SUBSET
                lsp_side top (e i) r \/
                DISJOINT (IMAGE (e j) (annulus (&1 / &2) (&2))) (lsp_side top (e i) r)`
  (LABEL_TAC "dich") THENL
   [REPEAT GEN_TAC THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC))) THEN
    ASM_CASES_TAC `DISJOINT (IMAGE ((e:num->real^3->A) j) (annulus (&1 / &2) (&2)))
                            (lsp_side top (e i) r)` THEN
    ASM_REWRITE_TAC[] THEN
    USE_THEN "sf" (fun th -> MP_TAC(SPEC `r:real` (CONJUNCT2(MATCH_MP th
      (ASSUME `(i:num) IN J`))))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    USE_THEN "nf" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th (ASSUME `(j:num) IN J`))) THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [USE_THEN "avoid" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `~DISJOINT (IMAGE ((e:num->real^3->A) j) (annulus (&1 / &2) (&2)))
                             (lsp_side top (e i) r)` THEN
      REWRITE_TAC[DISJOINT]];
    ALL_TAC] THEN
  ABBREV_TAC
   `m = \i r. CARD {j | j IN J /\ ~(j = i) /\
                        IMAGE ((e:num->real^3->A) j) (annulus (&1 / &2) (&2)) SUBSET
                        lsp_side top (e i) r}` THEN
  SUBGOAL_THEN
   `!i r. (m:num->real->num) i r =
          CARD {j | j IN J /\ ~(j = i) /\
                    IMAGE ((e:num->real^3->A) j) (annulus (&1 / &2) (&2)) SUBSET
                    lsp_side top (e i) r}`
  (LABEL_TAC "mdef") THENL [EXPAND_TAC "m" THEN REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPEC `\n. ?i r. i IN J /\ (r = &3 / &4 \/ r = &4 / &3) /\
                          (m:num->real->num) i r = n` num_WOP) THEN
  REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `p /\ (q ==> r) ==> (p <=> q) ==> r`) THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(X_CHOOSE_TAC `i0:num` o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY] o
      check (fun th -> concl th = `~(J:num->bool = {})`)) THEN
    MAP_EVERY EXISTS_TAC [`(m:num->real->num) i0 (&3 / &4)`; `i0:num`; `&3 / &4`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `i:num` (X_CHOOSE_THEN `r:real` (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)))) (LABEL_TAC "min"))) THEN
  MAP_EVERY EXISTS_TAC [`i:num`; `r:real`] THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  USE_THEN "dich" (MP_TAC o SPECL [`i:num`; `j:num`; `r:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `~p ==> (p \/ q ==> q)`) THEN DISCH_TAC THEN
  USE_THEN "nf" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th (ASSUME `(i:num) IN J`))) THEN
  USE_THEN "sf" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th (ASSUME `(j:num) IN J`))) THEN
  (* the sphere of i misses one side of j *)
  SUBGOAL_THEN
   `?r'. (r' = &3 / &4 \/ r' = &4 / &3) /\
         DISJOINT (IMAGE ((e:num->real^3->A) i) (sphere(vec 0,&1))) (lsp_side top (e j) r')`
  (X_CHOOSE_THEN `r':real` (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THENL
   [ASM_CASES_TAC `DISJOINT (IMAGE ((e:num->real^3->A) i) (sphere(vec 0,&1)))
                            (lsp_side top (e j) (&3 / &4))` THENL
     [EXISTS_TAC `&3 / &4` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    EXISTS_TAC `&4 / &3` THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `IMAGE ((e:num->real^3->A) i) (sphere(vec 0,&1)) SUBSET
                  lsp_side top (e j) (&3 / &4)` MP_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `&3 / &4` o check (fun th -> is_forall(concl th) &&
        can (find_term (fun u -> is_const u && fst(dest_const u) = "open_in")) (concl th))) THEN
      REWRITE_TAC[] THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC SUBSET_TRANS THEN
        EXISTS_TAC `IMAGE ((e:num->real^3->A) i) (annulus (&1 / &2) (&2))` THEN
        ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `IMAGE ((e:num->real^3->A) i) (annulus (&1 / &2) (&2)) SUBSET
                     topspace top` THEN
        USE_THEN "disj" (MP_TAC o SPECL [`i:num`; `j:num`]) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        USE_THEN "nf" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th (ASSUME `(j:num) IN J`))) THEN
        UNDISCH_TAC `IMAGE ((e:num->real^3->A) j) (sphere(vec 0,&1)) SUBSET
                     IMAGE (e j) (annulus (&1 / &2) (&2))` THEN
        SET_TAC[];
        UNDISCH_TAC `~DISJOINT (IMAGE ((e:num->real^3->A) i) (sphere(vec 0,&1)))
                               (lsp_side top (e j) (&3 / &4))` THEN
        REWRITE_TAC[DISJOINT]];
      UNDISCH_TAC `DISJOINT (lsp_side top ((e:num->real^3->A) j) (&3 / &4))
                            (lsp_side top (e j) (&4 / &3))` THEN
      SET_TAC[]];
    ALL_TAC] THEN
  (* that side of j lies in the side of i *)
  FIRST_X_ASSUM(MP_TAC o SPEC `r':real` o check (fun th -> is_forall(concl th) &&
    can (find_term (fun u -> is_const u && fst(dest_const u) = "open_in")) (concl th) &&
    can (find_term ((=) `(e:num->real^3->A) j`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  USE_THEN "sf" (fun th -> MP_TAC(SPEC `r:real` (CONJUNCT2(MATCH_MP th
    (ASSUME `(i:num) IN J`))))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `lsp_side top ((e:num->real^3->A) j) r' SUBSET lsp_side top (e i) r`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [UNDISCH_TAC `lsp_side top ((e:num->real^3->A) j) r' SUBSET
                   topspace top DIFF IMAGE (e j) (sphere(vec 0,&1))` THEN
      UNDISCH_TAC `DISJOINT (IMAGE ((e:num->real^3->A) i) (sphere(vec 0,&1)))
                            (lsp_side top (e j) r')` THEN
      SET_TAC[];
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
      EXISTS_TAC `(e:num->real^3->A) j (r' % basis 1)` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `IMAGE ((e:num->real^3->A) j) (annulus (&1 / &2) (&2)) SUBSET
                   lsp_side top (e i) r` THEN
      REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
      USE_THEN "nf" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(j:num) IN J`))) THEN
      DISCH_THEN(MP_TAC o SPEC `r':real` o last o CONJUNCTS) THEN
      ANTS_TAC THENL
       [FIRST_X_ASSUM(DISJ_CASES_THEN SUBST1_TAC o check (fun th ->
          is_disj(concl th) && can (find_term ((=) `r':real`)) (concl th))) THEN
        REAL_ARITH_TAC;
        SIMP_TAC[IN_DIFF]]];
    ALL_TAC] THEN
  (* fewer necks in that side: contradiction with minimality *)
  SUBGOAL_THEN `(m:num->real->num) j r' < n` ASSUME_TAC THENL
   [USE_THEN "mdef" (fun th -> REWRITE_TAC[th]) THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `(m:num->real->num) i r = n`)) THEN
    USE_THEN "mdef" (fun th -> REWRITE_TAC[th]) THEN
    MATCH_MP_TAC CARD_PSUBSET THEN CONJ_TAC THENL
     [REWRITE_TAC[PSUBSET] THEN CONJ_TAC THENL
       [GEN_REWRITE_TAC I [SUBSET] THEN REWRITE_TAC[IN_ELIM_THM] THEN
        X_GEN_TAC `k:num` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
         [DISCH_THEN SUBST_ALL_TAC THEN
          UNDISCH_TAC `IMAGE ((e:num->real^3->A) i) (annulus (&1 / &2) (&2)) SUBSET
                       lsp_side top (e j) r'` THEN
          UNDISCH_TAC `DISJOINT (IMAGE ((e:num->real^3->A) i) (sphere(vec 0,&1)))
                                (lsp_side top (e j) r')` THEN
          UNDISCH_TAC `IMAGE ((e:num->real^3->A) i) (sphere(vec 0,&1)) SUBSET
                       IMAGE (e i) (annulus (&1 / &2) (&2))` THEN
          UNDISCH_TAC `~(IMAGE ((e:num->real^3->A) i) (sphere(vec 0,&1)) = {})` THEN
          SET_TAC[];
          MATCH_MP_TAC SUBSET_TRANS THEN
          EXISTS_TAC `lsp_side top ((e:num->real^3->A) j) r'` THEN ASM_REWRITE_TAC[]];
        REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
        DISCH_THEN(MP_TAC o SPEC `j:num`) THEN ASM_REWRITE_TAC[]];
      MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `J:num->bool` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[]];
    ALL_TAC] THEN
  USE_THEN "min" (fun th -> MP_TAC(MATCH_MP th
    (ASSUME `(m:num->real->num) j r' < n`))) THEN
  REWRITE_TAC[] THEN MAP_EVERY EXISTS_TAC [`j:num`; `r':real`] THEN ASM_REWRITE_TAC[]);;

(* The collar halves lie in their sides.                                     *)

let LSP_SIDE_HALVES = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) e.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        mfd_neck_chart top atlas e /\ apx_sphere_sep top atlas
        ==> IMAGE e (annulus (&1 / &2) (&1)) SUBSET lsp_side top e (&3 / &4) /\
            IMAGE e (annulus (&1) (&2)) SUBSET lsp_side top e (&4 / &3) /\
            DISJOINT (IMAGE e (annulus (&1) (&2))) (lsp_side top e (&3 / &4)) /\
            DISJOINT (IMAGE e (annulus (&1 / &2) (&1))) (lsp_side top e (&4 / &3))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `e:real^3->A`]
    LSP_SIDES) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "sd")) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `e:real^3->A`]
    LSP_NECK_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `mfd_neck_chart top (atlas:((A->bool)#(A->real^3))->bool) e` THEN
  REWRITE_TAC[mfd_neck_chart] THEN DISCH_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `e':A->real^3` STRIP_ASSUME_TAC o MATCH_MP MFD_PARAM_MAPS) THEN
  SUBGOAL_THEN
   `!r1 r2 r. &1 / &2 <= r1 /\ r1 < r /\ r < r2 /\ r2 <= &2 /\
              (r2 <= &1 \/ &1 <= r1) /\ (r = &3 / &4 \/ r = &4 / &3)
              ==> IMAGE (e:real^3->A) (annulus r1 r2) SUBSET lsp_side top e r`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC))))) THEN
    USE_THEN "sd" (fun th -> MP_TAC(MATCH_MP th
      (ASSUME `r = &3 / &4 \/ r = &4 / &3`))) THEN
    STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    SUBGOAL_THEN `annulus r1 r2 SUBSET annulus (&1 / &2) (&2):real^3->bool` ASSUME_TAC THENL
     [REWRITE_TAC[SUBSET; annulus; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONNECTED_IN_CONTINUOUS_MAP_IMAGE THEN
      EXISTS_TAC `subtopology euclidean (annulus r1 r2:real^3->bool)` THEN
      REWRITE_TAC[CONNECTED_IN_ABSOLUTE; CONNECTED_IN_EUCLIDEAN] THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY_MONO THEN
        EXISTS_TAC `annulus (&1 / &2) (&2):real^3->bool` THEN ASM_REWRITE_TAC[];
        MP_TAC(ISPECL [`vec 0:real^3`; `r1:real`; `r2:real`]
          (CONJUNCT1 CONNECTED_ANNULUS)) THEN
        REWRITE_TAC[DIMINDEX_3; ARITH; VECTOR_SUB_RZERO; annulus]];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_DIFF] THEN X_GEN_TAC `x:real^3` THEN
      DISCH_TAC THEN CONJ_TAC THENL
       [UNDISCH_TAC `IMAGE (e:real^3->A) (annulus (&1 / &2) (&2)) SUBSET topspace top` THEN
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN DISCH_THEN MATCH_MP_TAC THEN
        ASM SET_TAC[];
        REWRITE_TAC[IN_IMAGE; IN_SPHERE_0] THEN
        DISCH_THEN(X_CHOOSE_THEN `u:real^3` STRIP_ASSUME_TAC) THEN
        SUBGOAL_THEN `(x:real^3) = u` MP_TAC THENL
         [FIRST_X_ASSUM(MP_TAC o AP_TERM `e':A->real^3`) THEN
          SUBGOAL_THEN `(u:real^3) IN annulus (&1 / &2) (&2) /\
                        (x:real^3) IN annulus (&1 / &2) (&2)` STRIP_ASSUME_TAC THENL
           [CONJ_TAC THENL
             [ASM_REWRITE_TAC[annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC; ASM SET_TAC[]];
            ASM_SIMP_TAC[]];
          DISCH_THEN SUBST_ALL_TAC THEN
          UNDISCH_TAC `(u:real^3) IN annulus r1 r2` THEN
          ASM_REWRITE_TAC[annulus; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC]];
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
      EXISTS_TAC `(e:real^3->A)(r % basis 1)` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC FUN_IN_IMAGE THEN
      SIMP_TAC[annulus; IN_ELIM_THM; NORM_MUL; NORM_BASIS; DIMINDEX_3; ARITH] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (e:real^3->A) (annulus (&1 / &2) (&1)) SUBSET lsp_side top e (&3 / &4) /\
    IMAGE (e:real^3->A) (annulus (&1) (&2)) SUBSET lsp_side top e (&4 / &3)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `DISJOINT (lsp_side top (e:real^3->A) (&3 / &4)) (lsp_side top e (&4 / &3))` THEN
  MAP_EVERY UNDISCH_TAC
   [`IMAGE (e:real^3->A) (annulus (&1 / &2) (&1)) SUBSET lsp_side top e (&3 / &4)`;
    `IMAGE (e:real^3->A) (annulus (&1) (&2)) SUBSET lsp_side top e (&4 / &3)`] THEN
  SET_TAC[]);;

