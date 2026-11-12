(* ========================================================================= *)
(* Unit pc_p2c_cglim (Part 2C, used in the pc_p2c_cg route): a smooth        *)
(* Riemannian manifold glued from a countable chart system.  Data: open sets *)
(* Dm i of real^N, open overlap domains Om i j in Dm i, transition maps Tr i *)
(* j (identity on Dm i for i = j, inverse pairs, the cocycle condition,      *)
(* smooth), separated (closed graphs), and metric fields G i compatible with *)
(* the transitions.  For any gluing map kp i z identifying exactly the       *)
(* related pairs, the carrier IMAGE kp with the quotient topology, the       *)
(* charts (IMAGE (kp i) (Dm i), kp i inverse) and the induced metric form a  *)
(* Hausdorff Riemannian manifold whose local representatives in the charts   *)
(* are the G i.  A gluing map into real^N exists by cardinality; smooth maps *)
(* out of the glued manifold are tested in the coordinates of the pieces;    *)
(* main theorem P2CL_GLUED_MANIFOLD.                                         *)
(* ========================================================================= *)

needs "src/pc_mfd_restrict.ml";;
needs "src/pc_lrg.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Chart systems, gluing maps, the quotient topology.                        *)
(* ------------------------------------------------------------------------- *)

let p2cl_system = new_definition
 `p2cl_system (Dm:num->real^N->bool) (Om:num->num->real^N->bool)
              (Tr:num->num->real^N->real^N) <=>
    (!i. open (Dm i)) /\
    (!i j. open (Om i j) /\ Om i j SUBSET Dm i) /\
    (!i. Om i i = Dm i) /\
    (!i z. z IN Dm i ==> Tr i i z = z) /\
    (!i j z. z IN Om i j ==> Tr i j z IN Om j i /\ Tr j i (Tr i j z) = z) /\
    (!i j k z. z IN Om i j /\ z IN Om i k
               ==> Tr i j z IN Om j k /\ Tr j k (Tr i j z) = Tr i k z) /\
    (!i j. smooth_map_on (Om i j) (Tr i j))`;;

let p2cl_separated = new_definition
 `p2cl_separated (Dm:num->real^N->bool) (Om:num->num->real^N->bool)
                 (Tr:num->num->real^N->real^N) <=>
    !i j z w. z IN Dm i /\ w IN Dm j /\ ~(z IN Om i j /\ Tr i j z = w)
              ==> ?u v. open u /\ open v /\ z IN u /\ w IN v /\
                        !y. y IN u INTER Om i j ==> ~(Tr i j y IN v)`;;

let p2cl_glue = new_definition
 `p2cl_glue (Dm:num->real^N->bool) (Om:num->num->real^N->bool)
            (Tr:num->num->real^N->real^N) (kp:num->real^N->B) <=>
    !i j z w. z IN Dm i /\ w IN Dm j
              ==> (kp i z = kp j w <=> z IN Om i j /\ Tr i j z = w)`;;

let p2cl_space = new_definition
 `p2cl_space (Dm:num->real^N->bool) (kp:num->real^N->B) =
    UNIONS {IMAGE (kp i) (Dm i) | i IN (:num)}`;;

let p2cl_top = new_definition
 `p2cl_top (Dm:num->real^N->bool) (kp:num->real^N->B) =
    topology {S | S SUBSET p2cl_space Dm kp /\
                  !i. open {z | z IN Dm i /\ kp i z IN S}}`;;

let P2CL_ISTOPOLOGY = prove
 (`!(Dm:num->real^N->bool) (kp:num->real^N->B).
     istopology {S | S SUBSET p2cl_space Dm kp /\
                     !i. open {z | z IN Dm i /\ kp i z IN S}}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[istopology; IN_ELIM_THM] THEN
  REWRITE_TAC[EMPTY_SUBSET; NOT_IN_EMPTY; EMPTY_GSPEC; OPEN_EMPTY] THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`S:B->bool`; `S':B->bool`] THEN STRIP_TAC THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN GEN_TAC THEN
    SUBGOAL_THEN
     `{z | z IN (Dm:num->real^N->bool) i /\ (kp:num->real^N->B) i z IN S INTER S'} =
      {z | z IN Dm i /\ kp i z IN S} INTER {z | z IN Dm i /\ kp i z IN S'}`
    SUBST1_TAC THENL [SET_TAC[]; MATCH_MP_TAC OPEN_INTER THEN ASM_REWRITE_TAC[]];
    X_GEN_TAC `k:(B->bool)->bool` THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
    DISCH_TAC THEN CONJ_TAC THENL
     [REWRITE_TAC[IN_UNIONS] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    GEN_TAC THEN
    SUBGOAL_THEN
     `{z | z IN (Dm:num->real^N->bool) i /\ (kp:num->real^N->B) i z IN UNIONS k} =
      UNIONS {{z | z IN Dm i /\ kp i z IN S} | S IN k}`
    SUBST1_TAC THENL
     [REWRITE_TAC[UNIONS_GSPEC] THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_UNIONS] THEN
      MESON_TAC[];
      MATCH_MP_TAC OPEN_UNIONS THEN REWRITE_TAC[FORALL_IN_GSPEC] THEN ASM_MESON_TAC[]]]);;

let P2CL_OPEN_IN = prove
 (`!(Dm:num->real^N->bool) (kp:num->real^N->B) S.
     open_in (p2cl_top Dm kp) S <=>
     S SUBSET p2cl_space Dm kp /\ !i. open {z | z IN Dm i /\ kp i z IN S}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2cl_top] THEN
  SIMP_TAC[REWRITE_RULE[CONJUNCT2 topology_tybij] P2CL_ISTOPOLOGY] THEN
  REWRITE_TAC[IN_ELIM_THM]);;

let P2CL_TOPSPACE = prove
 (`!(Dm:num->real^N->bool) (kp:num->real^N->B).
     (!i. open (Dm i)) ==> topspace(p2cl_top Dm kp) = p2cl_space Dm kp`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open_in (p2cl_top Dm kp) (p2cl_space (Dm:num->real^N->bool) (kp:num->real^N->B))`
  ASSUME_TAC THENL
   [REWRITE_TAC[P2CL_OPEN_IN; SUBSET_REFL] THEN GEN_TAC THEN
    SUBGOAL_THEN `{z | z IN (Dm:num->real^N->bool) i /\
                       (kp:num->real^N->B) i z IN p2cl_space Dm kp} = Dm i`
    (fun th -> ASM_REWRITE_TAC[th]) THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; p2cl_space; IN_UNIONS; EXISTS_IN_GSPEC; IN_UNIV;
                IN_IMAGE] THEN MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [REWRITE_TAC[topspace; UNIONS_SUBSET; IN_ELIM_THM; P2CL_OPEN_IN] THEN MESON_TAC[];
    FIRST_ASSUM(ACCEPT_TAC o MATCH_MP OPEN_IN_SUBSET)]);;

(* ------------------------------------------------------------------------- *)
(* The charts IMAGE (kp i) (Dm i) with the inverse of kp i:                  *)
(* open domains, homeomorphisms onto Dm i, transitions Tr i j.              *)
(* ------------------------------------------------------------------------- *)

let p2cl_chart = new_definition
 `p2cl_chart (Dm:num->real^N->bool) (kp:num->real^N->B) i =
    (IMAGE (kp i) (Dm i), \p. @z. z IN Dm i /\ kp i z = p)`;;

let p2cl_atlas = new_definition
 `p2cl_atlas (Dm:num->real^N->bool) (kp:num->real^N->B) =
    {p2cl_chart Dm kp i | i IN (:num)}`;;

let P2CL_KP_INJ = prove
 (`!Dm Om Tr (kp:num->real^N->B) i z z'.
     p2cl_system Dm Om Tr /\ p2cl_glue Dm Om Tr kp /\ z IN Dm i /\ z' IN Dm i /\
     kp i z = kp i z'
     ==> z = z'`,
  REWRITE_TAC[p2cl_system; p2cl_glue] THEN MESON_TAC[]);;

let P2CL_CHART_INV = prove
 (`!Dm Om Tr (kp:num->real^N->B) i z.
     p2cl_system Dm Om Tr /\ p2cl_glue Dm Om Tr kp /\ z IN Dm i
     ==> SND(p2cl_chart Dm kp i) (kp i z) = z`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p2cl_chart] THEN
  MATCH_MP_TAC SELECT_UNIQUE THEN X_GEN_TAC `w:real^N` THEN REWRITE_TAC[] THEN
  EQ_TAC THENL [STRIP_TAC; ASM_MESON_TAC[]] THEN
  MATCH_MP_TAC P2CL_KP_INJ THEN
  MAP_EVERY EXISTS_TAC [`Dm:num->real^N->bool`; `Om:num->num->real^N->bool`;
                        `Tr:num->num->real^N->real^N`; `kp:num->real^N->B`; `i:num`] THEN
  ASM_REWRITE_TAC[]);;

(* The trace on Dm j of the image under kp i of a part V of Dm i.           *)

let P2CL_PREIMAGE = prove
 (`!Dm Om Tr (kp:num->real^N->B) i j V.
     p2cl_system Dm Om Tr /\ p2cl_glue Dm Om Tr kp /\ V SUBSET Dm i
     ==> {w | w IN Dm j /\ kp j w IN IMAGE (kp i) V} = {w | w IN Om j i /\ Tr j i w IN V}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2cl_system; p2cl_glue] THEN STRIP_TAC THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_IMAGE] THEN X_GEN_TAC `w:real^N` THEN
  EQ_TAC THENL
   [DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `z:real^N` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `(z:real^N) IN Dm (i:num)` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(w:real^N) IN Om (j:num) (i:num) /\ Tr j i w = (z:real^N)`
      (fun th -> ASM_MESON_TAC[th]) THEN
    ASM_MESON_TAC[];
    STRIP_TAC THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    EXISTS_TAC `(Tr:num->num->real^N->real^N) j i w` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(Tr:num->num->real^N->real^N) j i w IN Dm (i:num)` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(w:real^N) IN Dm (j:num)` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_MESON_TAC[]]);;

let P2CL_OPEN_IMAGE = prove
 (`!Dm Om Tr (kp:num->real^N->B) i V.
     p2cl_system Dm Om Tr /\ p2cl_glue Dm Om Tr kp /\ open V /\ V SUBSET Dm i
     ==> open_in (p2cl_top Dm kp) (IMAGE (kp i) V)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[P2CL_OPEN_IN] THEN CONJ_TAC THENL
   [REWRITE_TAC[p2cl_space; SUBSET; IN_UNIONS; IN_IMAGE; EXISTS_IN_GSPEC; IN_UNIV] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `j:num` THEN
  MP_TAC(ISPECL [`Dm:num->real^N->bool`; `Om:num->num->real^N->bool`;
                 `Tr:num->num->real^N->real^N`; `kp:num->real^N->B`;
                 `i:num`; `j:num`; `V:real^N->bool`] P2CL_PREIMAGE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2cl_system]) THEN
  MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN ASM_REWRITE_TAC[ETA_AX]);;

let P2CL_CHART_IMAGE = prove
 (`!Dm Om Tr (kp:num->real^N->B) i.
     p2cl_system Dm Om Tr /\ p2cl_glue Dm Om Tr kp
     ==> IMAGE (SND(p2cl_chart Dm kp i)) (FST(p2cl_chart Dm kp i)) = Dm i`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!z. z IN (Dm:num->real^N->bool) i
                    ==> SND(p2cl_chart Dm (kp:num->real^N->B) i) (kp i z) = z`
  MP_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC P2CL_CHART_INV THEN
    MAP_EVERY EXISTS_TAC [`Om:num->num->real^N->bool`; `Tr:num->num->real^N->real^N`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[p2cl_chart; GSYM IMAGE_o; o_DEF] THEN DISCH_TAC THEN
  MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `IMAGE (\z:real^N. z) (Dm (i:num))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC IMAGE_EQ THEN ASM_SIMP_TAC[]; REWRITE_TAC[IMAGE_ID]]);;

let P2CL_CHART_FST = prove
 (`!(Dm:num->real^N->bool) (kp:num->real^N->B) i.
     FST(p2cl_chart Dm kp i) = IMAGE (kp i) (Dm i)`,
  REWRITE_TAC[p2cl_chart]);;

let P2CL_CHART_HOMEO = prove
 (`!Dm Om Tr (kp:num->real^N->B) i.
     p2cl_system Dm Om Tr /\ p2cl_glue Dm Om Tr kp
     ==> open_in (p2cl_top Dm kp) (FST(p2cl_chart Dm kp i)) /\
         homeomorphic_map (subtopology (p2cl_top Dm kp) (FST(p2cl_chart Dm kp i)),
                           subtopology euclidean (Dm i))
                          (SND(p2cl_chart Dm kp i))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2cl_system]) THEN
  REWRITE_TAC[P2CL_CHART_FST] THEN
  ABBREV_TAC `phi = SND(p2cl_chart (Dm:num->real^N->bool) (kp:num->real^N->B) i)` THEN
  SUBGOAL_THEN `!z. z IN (Dm:num->real^N->bool) i ==> (phi:B->real^N) ((kp:num->real^N->B) i z) = z`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "phi" THEN MATCH_MP_TAC P2CL_CHART_INV THEN
    MAP_EVERY EXISTS_TAC [`Om:num->num->real^N->bool`; `Tr:num->num->real^N->real^N`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!V. open V /\ V SUBSET (Dm:num->real^N->bool) i
                    ==> open_in (p2cl_top (Dm:num->real^N->bool) (kp:num->real^N->B))
                                (IMAGE ((kp:num->real^N->B) i) V)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC P2CL_OPEN_IMAGE THEN
    MAP_EVERY EXISTS_TAC [`Om:num->num->real^N->bool`; `Tr:num->num->real^N->real^N`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `open_in (p2cl_top (Dm:num->real^N->bool) (kp:num->real^N->B))
                        (IMAGE ((kp:num->real^N->B) i) (Dm i))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[SUBSET_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN `topspace(subtopology (p2cl_top (Dm:num->real^N->bool) (kp:num->real^N->B))
                                     (IMAGE ((kp:num->real^N->B) i) (Dm i))) =
                IMAGE (kp i) (Dm i)` ASSUME_TAC THENL
   [REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP OPEN_IN_SUBSET) THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[HOMEOMORPHIC_MAP_MAPS] THEN
  EXISTS_TAC `(kp:num->real^N->B) i` THEN REWRITE_TAC[homeomorphic_maps] THEN
  ASM_REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[continuous_map; TOPSPACE_EUCLIDEAN; IN_UNIV; GSYM OPEN_IN] THEN
      ASM_REWRITE_TAC[] THEN X_GEN_TAC `u:real^N->bool` THEN DISCH_TAC THEN
      SUBGOAL_THEN
       `{x | x IN IMAGE ((kp:num->real^N->B) i) (Dm i) /\ (phi:B->real^N) x IN u} =
        IMAGE ((kp:num->real^N->B) i) (u INTER Dm i)`
      SUBST1_TAC THENL
       [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INTER; IN_IMAGE] THEN
        X_GEN_TAC `p:B` THEN EQ_TAC THENL
         [DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `z:real^N` STRIP_ASSUME_TAC)
                                     ASSUME_TAC) THEN
          EXISTS_TAC `z:real^N` THEN ASM_MESON_TAC[];
          DISCH_THEN(X_CHOOSE_THEN `z:real^N` STRIP_ASSUME_TAC) THEN
          ASM_SIMP_TAC[] THEN ASM_MESON_TAC[]];
        ASM_SIMP_TAC[OPEN_IN_OPEN_SUBTOPOLOGY] THEN CONJ_TAC THENL
         [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[OPEN_INTER; INTER_SUBSET];
          ASM SET_TAC[]]];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM_SIMP_TAC[]];
    REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN
    REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY; SUBSET_REFL] THEN
    REWRITE_TAC[continuous_map; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[P2CL_TOPSPACE] THEN REWRITE_TAC[p2cl_space] THEN
      REWRITE_TAC[IN_UNIONS; EXISTS_IN_GSPEC; IN_UNIV] THEN SET_TAC[];
      X_GEN_TAC `S:B->bool` THEN DISCH_TAC THEN
      SUBGOAL_THEN `open_in euclidean ((Dm:num->real^N->bool) i)` ASSUME_TAC THENL
       [ASM_REWRITE_TAC[GSYM OPEN_IN]; ALL_TAC] THEN
      ASM_SIMP_TAC[OPEN_IN_OPEN_SUBTOPOLOGY] THEN
      REWRITE_TAC[GSYM OPEN_IN] THEN CONJ_TAC THENL
       [RULE_ASSUM_TAC(REWRITE_RULE[P2CL_OPEN_IN]) THEN ASM_REWRITE_TAC[];
        SET_TAC[]]];
    REWRITE_TAC[FORALL_IN_IMAGE] THEN ASM_SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The glued space is a Hausdorff smooth manifold.                          *)
(* ------------------------------------------------------------------------- *)

let P2CL_IN_ATLAS = prove
 (`!(Dm:num->real^N->bool) (kp:num->real^N->B) U phi.
     (U,phi) IN p2cl_atlas Dm kp <=> ?i. (U,phi) = p2cl_chart Dm kp i`,
  REWRITE_TAC[p2cl_atlas; IN_ELIM_THM; IN_UNIV] THEN MESON_TAC[]);;

let P2CL_OVERLAP_IMAGE = prove
 (`!Dm Om Tr (kp:num->real^N->B) i j.
     p2cl_system Dm Om Tr /\ p2cl_glue Dm Om Tr kp
     ==> IMAGE (SND(p2cl_chart Dm kp i))
               (FST(p2cl_chart Dm kp i) INTER FST(p2cl_chart Dm kp j)) = Om i j /\
         !p. p IN FST(p2cl_chart Dm kp i) INTER FST(p2cl_chart Dm kp j)
             ==> Tr i j (SND(p2cl_chart Dm kp i) p) = SND(p2cl_chart Dm kp j) p`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2cl_system]) THEN
  SUBGOAL_THEN `!k z. z IN (Dm:num->real^N->bool) k
                      ==> SND(p2cl_chart Dm (kp:num->real^N->B) k) (kp k z) = z`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC P2CL_CHART_INV THEN
    MAP_EVERY EXISTS_TAC [`Om:num->num->real^N->bool`; `Tr:num->num->real^N->real^N`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [p2cl_glue]) THEN DISCH_TAC THEN
  REWRITE_TAC[P2CL_CHART_FST] THEN CONJ_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_INTER] THEN X_GEN_TAC `z:real^N` THEN
    EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `p:B` (CONJUNCTS_THEN2 SUBST1_TAC
        (CONJUNCTS_THEN2 (X_CHOOSE_THEN `z1:real^N` STRIP_ASSUME_TAC)
                         (X_CHOOSE_THEN `w1:real^N` STRIP_ASSUME_TAC)))) THEN
      FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_SIMP_TAC[] THEN ASM_MESON_TAC[];
      DISCH_TAC THEN
      SUBGOAL_THEN `(z:real^N) IN Dm (i:num)` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      EXISTS_TAC `(kp:num->real^N->B) i z` THEN ASM_SIMP_TAC[] THEN
      CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      EXISTS_TAC `(Tr:num->num->real^N->real^N) i j z` THEN
      SUBGOAL_THEN `(Tr:num->num->real^N->real^N) i j z IN Dm j` ASSUME_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      ASM_MESON_TAC[]];
    REWRITE_TAC[IN_INTER; IN_IMAGE] THEN X_GEN_TAC `p:B` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `z:real^N` STRIP_ASSUME_TAC)
                               (X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC)) THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_SIMP_TAC[] THEN ASM_MESON_TAC[]]);;

let P2CL_SMOOTH_ATLAS = prove
 (`!Dm Om Tr (kp:num->real^N->B).
     p2cl_system Dm Om Tr /\ p2cl_glue Dm Om Tr kp
     ==> smooth_manifold_atlas (p2cl_top Dm kp) (p2cl_atlas Dm kp)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2cl_system]) THEN
  REWRITE_TAC[smooth_manifold_atlas; P2CL_IN_ATLAS] THEN REPEAT CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`U:B->bool`; `phi:B->real^N`] THEN
    DISCH_THEN(X_CHOOSE_TAC `i:num`) THEN
    SUBGOAL_THEN `U = FST(p2cl_chart (Dm:num->real^N->bool) (kp:num->real^N->B) i) /\
                  phi = SND(p2cl_chart Dm kp i)` STRIP_ASSUME_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`Dm:num->real^N->bool`; `Om:num->num->real^N->bool`;
                   `Tr:num->num->real^N->real^N`; `kp:num->real^N->B`; `i:num`]
                  P2CL_CHART_IMAGE) THEN
    MP_TAC(ISPECL [`Dm:num->real^N->bool`; `Om:num->num->real^N->bool`;
                   `Tr:num->num->real^N->real^N`; `kp:num->real^N->B`; `i:num`]
                  P2CL_CHART_HOMEO) THEN
    ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[];
    X_GEN_TAC `p:B` THEN ASM_SIMP_TAC[P2CL_TOPSPACE] THEN
    REWRITE_TAC[p2cl_space; IN_UNIONS; EXISTS_IN_GSPEC; IN_UNIV] THEN
    DISCH_THEN(X_CHOOSE_THEN `i:num` ASSUME_TAC) THEN
    MAP_EVERY EXISTS_TAC [`FST(p2cl_chart (Dm:num->real^N->bool) (kp:num->real^N->B) i)`;
                          `SND(p2cl_chart (Dm:num->real^N->bool) (kp:num->real^N->B) i)`] THEN
    REWRITE_TAC[PAIR] THEN CONJ_TAC THENL [MESON_TAC[]; ASM_REWRITE_TAC[P2CL_CHART_FST]];
    MAP_EVERY X_GEN_TAC [`U:B->bool`; `phi:B->real^N`; `V:B->bool`; `psi:B->real^N`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `i:num`) (X_CHOOSE_TAC `j:num`)) THEN
    SUBGOAL_THEN `U = FST(p2cl_chart (Dm:num->real^N->bool) (kp:num->real^N->B) i) /\
                  phi = SND(p2cl_chart Dm kp i) /\
                  V = FST(p2cl_chart Dm kp j) /\ psi = SND(p2cl_chart Dm kp j)`
    STRIP_ASSUME_TAC THENL
     [REPEAT(FIRST_X_ASSUM(SUBST1_TAC o SYM o check (is_eq o concl))) THEN REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN EXISTS_TAC `(Tr:num->num->real^N->real^N) i j` THEN
    MP_TAC(ISPECL [`Dm:num->real^N->bool`; `Om:num->num->real^N->bool`;
                   `Tr:num->num->real^N->real^N`; `kp:num->real^N->B`; `i:num`; `j:num`]
                  P2CL_OVERLAP_IMAGE) THEN
    ASM_SIMP_TAC[]]);;

let P2CL_HAUSDORFF = prove
 (`!Dm Om Tr (kp:num->real^N->B).
     p2cl_system Dm Om Tr /\ p2cl_glue Dm Om Tr kp /\ p2cl_separated Dm Om Tr
     ==> hausdorff_space (p2cl_top Dm kp)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2cl_system]) THEN
  REWRITE_TAC[hausdorff_space] THEN ASM_SIMP_TAC[P2CL_TOPSPACE] THEN
  MAP_EVERY X_GEN_TAC [`p:B`; `q:B`] THEN
  REWRITE_TAC[p2cl_space; IN_UNIONS; EXISTS_IN_GSPEC; IN_UNIV; IN_IMAGE] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `i:num` (X_CHOOSE_THEN `z:real^N` STRIP_ASSUME_TAC))
    (CONJUNCTS_THEN2 (X_CHOOSE_THEN `j:num` (X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC))
                     ASSUME_TAC)) THEN
  SUBGOAL_THEN `~((z:real^N) IN Om (i:num) (j:num) /\ (Tr:num->num->real^N->real^N) i j z = w)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `~(p:B = q)` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `p2cl_glue (Dm:num->real^N->bool) Om Tr (kp:num->real^N->B)` THEN
    REWRITE_TAC[p2cl_glue] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `p2cl_separated (Dm:num->real^N->bool) Om Tr` THEN
  REWRITE_TAC[p2cl_separated] THEN
  DISCH_THEN(MP_TAC o SPECL [`i:num`; `j:num`; `z:real^N`; `w:real^N`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N->bool` (X_CHOOSE_THEN `v:real^N->bool` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`IMAGE ((kp:num->real^N->B) i) (u INTER Dm i)`;
                        `IMAGE ((kp:num->real^N->B) j) (v INTER Dm j)`] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC P2CL_OPEN_IMAGE THEN
    MAP_EVERY EXISTS_TAC [`Om:num->num->real^N->bool`; `Tr:num->num->real^N->real^N`] THEN
    ASM_SIMP_TAC[OPEN_INTER; INTER_SUBSET];
    MATCH_MP_TAC P2CL_OPEN_IMAGE THEN
    MAP_EVERY EXISTS_TAC [`Om:num->num->real^N->bool`; `Tr:num->num->real^N->real^N`] THEN
    ASM_SIMP_TAC[OPEN_INTER; INTER_SUBSET];
    ASM_REWRITE_TAC[IN_IMAGE; IN_INTER] THEN ASM_MESON_TAC[];
    ASM_REWRITE_TAC[IN_IMAGE; IN_INTER] THEN ASM_MESON_TAC[];
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_IMAGE] THEN
    X_GEN_TAC `r:B` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `y1:real^N` STRIP_ASSUME_TAC)
                               (X_CHOOSE_THEN `y2:real^N` STRIP_ASSUME_TAC)) THEN
    UNDISCH_TAC `p2cl_glue (Dm:num->real^N->bool) Om Tr (kp:num->real^N->B)` THEN
    REWRITE_TAC[p2cl_glue] THEN
    DISCH_THEN(MP_TAC o SPECL [`i:num`; `j:num`; `y1:real^N`; `y2:real^N`]) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[IN_INTER]]);;

(* ------------------------------------------------------------------------- *)
(* The induced Riemannian metric.  With metric fields G i on                 *)
(* Dm i compatible with the transitions (G i = Tr i j pulled back G j on     *)
(* Om i j), the metric in the preferred chart has the representative G i in *)
(* the chart i.                                                              *)
(* ------------------------------------------------------------------------- *)

let p2cl_metric = new_definition
 `p2cl_metric (Dm:num->real^N->bool) (kp:num->real^N->B) (G:num->real^N->real^N^N) =
    \p. G (@i. chart_at (p2cl_atlas Dm kp) p = p2cl_chart Dm kp i)
          (SND(chart_at (p2cl_atlas Dm kp) p) p)`;;

let P2CL_CHART_INVERSE = prove
 (`!Dm Om Tr (kp:num->real^N->B) i y.
     p2cl_system Dm Om Tr /\ p2cl_glue Dm Om Tr kp /\ y IN Dm i
     ==> chart_inv (p2cl_chart Dm kp i) y = kp i y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[chart_inv] THEN
  MATCH_MP_TAC SELECT_UNIQUE THEN X_GEN_TAC `p:B` THEN
  REWRITE_TAC[P2CL_CHART_FST; IN_IMAGE] THEN EQ_TAC THENL
   [DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `z:real^N` STRIP_ASSUME_TAC) MP_TAC) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`Dm:num->real^N->bool`; `Om:num->num->real^N->bool`;
                   `Tr:num->num->real^N->real^N`; `kp:num->real^N->B`; `i:num`; `z:real^N`]
                  P2CL_CHART_INV) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN MESON_TAC[];
    DISCH_THEN SUBST1_TAC THEN CONJ_TAC THENL
     [ASM_MESON_TAC[];
      MATCH_MP_TAC P2CL_CHART_INV THEN
      MAP_EVERY EXISTS_TAC [`Om:num->num->real^N->bool`; `Tr:num->num->real^N->real^N`] THEN
      ASM_REWRITE_TAC[]]]);;

let P2CL_CHART_AT = prove
 (`!Dm Om Tr (kp:num->real^N->B) i y.
     p2cl_system Dm Om Tr /\ p2cl_glue Dm Om Tr kp /\ y IN Dm i
     ==> ?i'. chart_at (p2cl_atlas Dm kp) (kp i y) = p2cl_chart Dm kp i' /\
              y IN Om i i' /\
              SND(p2cl_chart Dm kp i') (kp i y) = Tr i i' y`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`p2cl_top (Dm:num->real^N->bool) (kp:num->real^N->B)`;
                 `p2cl_atlas (Dm:num->real^N->bool) (kp:num->real^N->B)`;
                 `(kp:num->real^N->B) i y`] CHART_AT) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC P2CL_SMOOTH_ATLAS THEN
      MAP_EVERY EXISTS_TAC [`Om:num->num->real^N->bool`; `Tr:num->num->real^N->real^N`] THEN
      ASM_REWRITE_TAC[];
      FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2cl_system]) THEN
      ASM_SIMP_TAC[P2CL_TOPSPACE] THEN
      REWRITE_TAC[p2cl_space; IN_UNIONS; EXISTS_IN_GSPEC; IN_UNIV] THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[GSYM PAIR] THEN REWRITE_TAC[P2CL_IN_ATLAS] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `i':num`) MP_TAC) THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[REWRITE_RULE[PAIR] th]) THEN
  REWRITE_TAC[P2CL_CHART_FST; IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `i':num` THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC o SPECL [`i:num`; `i':num`; `y:real^N`; `w:real^N`] o
              GEN_REWRITE_RULE I [p2cl_glue]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC P2CL_CHART_INV THEN
  MAP_EVERY EXISTS_TAC [`Om:num->num->real^N->bool`; `Tr:num->num->real^N->real^N`] THEN
  ASM_REWRITE_TAC[]);;

let P2CL_CHART_TRANS_LOCAL = prove
 (`!Dm Om Tr (kp:num->real^N->B) i i' y.
     p2cl_system Dm Om Tr /\ p2cl_glue Dm Om Tr kp /\ y IN Om i i'
     ==> chart_trans (p2cl_chart Dm kp i) (p2cl_chart Dm kp i') y = Tr i i' y`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2cl_system]) THEN
  SUBGOAL_THEN `(y:real^N) IN Dm (i:num) /\ (Tr:num->num->real^N->real^N) i i' y IN Dm i'`
  STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[chart_trans] THEN
  MP_TAC(ISPECL [`Dm:num->real^N->bool`; `Om:num->num->real^N->bool`;
                 `Tr:num->num->real^N->real^N`; `kp:num->real^N->B`; `i:num`; `y:real^N`]
                P2CL_CHART_INVERSE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `(kp:num->real^N->B) i y = kp i' ((Tr:num->num->real^N->real^N) i i' y)`
  SUBST1_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPECL [`i:num`; `i':num`; `y:real^N`;
                                `(Tr:num->num->real^N->real^N) i i' y`] o
                GEN_REWRITE_RULE I [p2cl_glue]) THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC P2CL_CHART_INV THEN
    MAP_EVERY EXISTS_TAC [`Om:num->num->real^N->bool`; `Tr:num->num->real^N->real^N`] THEN
    ASM_REWRITE_TAC[]]);;

let P2CL_CHART_JAC = prove
 (`!Dm Om Tr (kp:num->real^N->B) i i' y.
     p2cl_system Dm Om Tr /\ p2cl_glue Dm Om Tr kp /\ y IN Om i i'
     ==> chart_jac (p2cl_chart Dm kp i) (p2cl_chart Dm kp i') (kp i y) =
         frechet_derivative (Tr i i') (at y)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2cl_system]) THEN
  SUBGOAL_THEN `(y:real^N) IN Dm (i:num)` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[chart_jac] THEN
  MP_TAC(ISPECL [`Dm:num->real^N->bool`; `Om:num->num->real^N->bool`;
                 `Tr:num->num->real^N->real^N`; `kp:num->real^N->B`; `i:num`; `y:real^N`]
                P2CL_CHART_INV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
  MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_AT THEN
  MP_TAC(ISPEC `(Om:num->num->real^N->bool) i i'` OPEN_CONTAINS_BALL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `y:real^N`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`(Tr:num->num->real^N->real^N) i i'`; `d:real`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC P2CL_CHART_TRANS_LOCAL THEN
    EXISTS_TAC `Om:num->num->real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `ball(y:real^N,d) SUBSET Om (i:num) (i':num)` THEN
    REWRITE_TAC[SUBSET; IN_BALL] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_MESON_TAC[DIST_SYM];
    REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `(Om:num->num->real^N->bool) i i'` THEN ASM_REWRITE_TAC[]]);;

let P2CL_FRECHET_LOCAL_ID = prove
 (`!(f:real^N->real^N) s y.
     open s /\ y IN s /\ (!z. z IN s ==> f z = z)
     ==> frechet_derivative f (at y) = (\x. x)`,
  REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
  MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_AT THEN
  MP_TAC(ISPEC `s:real^N->bool` OPEN_CONTAINS_BALL) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `y:real^N`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`\x:real^N. x`; `d:real`] THEN
  ASM_REWRITE_TAC[HAS_DERIVATIVE_ID] THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  UNDISCH_TAC `ball(y:real^N,d) SUBSET s` THEN REWRITE_TAC[SUBSET; IN_BALL] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_MESON_TAC[DIST_SYM]);;

let P2CL_CHART_EQ_G = prove
 (`!Dm Om Tr (kp:num->real^N->B) (G:num->real^N->real^N^N) i j y.
     p2cl_system Dm Om Tr /\ p2cl_glue Dm Om Tr kp /\
     (!i j z. z IN Om i j ==> G i z = mpullback (Tr i j) (G j) z) /\
     p2cl_chart Dm kp i = p2cl_chart Dm kp j /\ y IN Dm i
     ==> G i y = G j y`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "compat") (CONJUNCTS_THEN2 (LABEL_TAC "ceq") ASSUME_TAC)))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2cl_system]) THEN
  SUBGOAL_THEN `IMAGE ((kp:num->real^N->B) i) (Dm i) = IMAGE (kp j) (Dm j) /\
                SND(p2cl_chart Dm kp j) = SND(p2cl_chart Dm kp i)`
  STRIP_ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[GSYM P2CL_CHART_FST] THEN REMOVE_THEN "ceq" (fun th -> REWRITE_TAC[th]);
    REMOVE_THEN "ceq" (K ALL_TAC)] THEN
  SUBGOAL_THEN `!z. z IN (Dm:num->real^N->bool) i
                    ==> z IN (Om:num->num->real^N->bool) i j /\
                        (Tr:num->num->real^N->real^N) i j z = z`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(kp:num->real^N->B) i z IN IMAGE (kp j) (Dm j)` MP_TAC THENL
     [UNDISCH_TAC `IMAGE ((kp:num->real^N->B) i) (Dm i) = IMAGE (kp j) (Dm j)` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `w:real^N = z` SUBST_ALL_TAC THENL
     [MP_TAC(ISPECL [`Dm:num->real^N->bool`; `Om:num->num->real^N->bool`;
                     `Tr:num->num->real^N->real^N`; `kp:num->real^N->B`; `j:num`; `w:real^N`]
                    P2CL_CHART_INV) THEN
      MP_TAC(ISPECL [`Dm:num->real^N->bool`; `Om:num->num->real^N->bool`;
                     `Tr:num->num->real^N->real^N`; `kp:num->real^N->B`; `i:num`; `z:real^N`]
                    P2CL_CHART_INV) THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(kp:num->real^N->B) i z = kp j w` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      UNDISCH_TAC `SND(p2cl_chart (Dm:num->real^N->bool) (kp:num->real^N->B) j) =
                   SND(p2cl_chart Dm kp i)` THEN
      DISCH_THEN SUBST1_TAC THEN MESON_TAC[];
      ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o SPECL [`i:num`; `j:num`; `z:real^N`; `z:real^N`] o
                GEN_REWRITE_RULE I [p2cl_glue]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REMOVE_THEN "compat" (MP_TAC o SPECL [`i:num`; `j:num`; `y:real^N`]) THEN
  ASM_SIMP_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[mpullback] THEN
  SUBGOAL_THEN `frechet_derivative ((Tr:num->num->real^N->real^N) i j) (at y) = (\x. x)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC P2CL_FRECHET_LOCAL_ID THEN EXISTS_TAC `(Dm:num->real^N->bool) i` THEN
    ASM_SIMP_TAC[];
    ASM_SIMP_TAC[MATRIX_ID; TRANSP_MAT; MATRIX_MUL_LID; MATRIX_MUL_RID]]);;

let P2CL_TR_IN = prove
 (`!(Dm:num->real^N->bool) Om Tr i j y.
     p2cl_system Dm Om Tr /\ y IN Om i j
     ==> y IN Dm i /\ Tr i j y IN Om j i /\ Tr i j y IN Dm j`,
  REWRITE_TAC[p2cl_system; SUBSET] THEN MESON_TAC[]);;

let P2CL_IN_ATLAS_ALT = prove
 (`!(Dm:num->real^N->bool) (kp:num->real^N->B) c.
     c IN p2cl_atlas Dm kp <=> ?i. c = p2cl_chart Dm kp i`,
  REWRITE_TAC[p2cl_atlas; IN_ELIM_THM; IN_UNIV]);;

(* The representative of the glued metric in the chart i is G i. *)

let P2CL_METRIC_LOCAL = prove
 (`!Dm Om Tr (kp:num->real^N->B) (G:num->real^N->real^N^N) i y.
     p2cl_system Dm Om Tr /\ p2cl_glue Dm Om Tr kp /\
     (!i j z. z IN Om i j ==> G i z = mpullback (Tr i j) (G j) z) /\
     y IN Dm i
     ==> metric_local (p2cl_atlas Dm kp) (p2cl_chart Dm kp i) (p2cl_metric Dm kp G) y =
         G i y`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "compat") ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`Dm:num->real^N->bool`; `Om:num->num->real^N->bool`;
                 `Tr:num->num->real^N->real^N`; `kp:num->real^N->B`; `i:num`; `y:real^N`]
                P2CL_CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `i':num` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`Dm:num->real^N->bool`; `Om:num->num->real^N->bool`;
                 `Tr:num->num->real^N->real^N`; `i:num`; `i':num`; `y:real^N`] P2CL_TR_IN) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`Dm:num->real^N->bool`; `Om:num->num->real^N->bool`;
                 `Tr:num->num->real^N->real^N`; `kp:num->real^N->B`; `i:num`; `y:real^N`]
                P2CL_CHART_INVERSE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`Dm:num->real^N->bool`; `Om:num->num->real^N->bool`;
                 `Tr:num->num->real^N->real^N`; `kp:num->real^N->B`; `i:num`; `i':num`;
                 `y:real^N`] P2CL_CHART_JAC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `p2cl_metric Dm kp G ((kp:num->real^N->B) i y) =
                (G:num->real^N->real^N^N) i' ((Tr:num->num->real^N->real^N) i i' y)`
  ASSUME_TAC THENL
   [REWRITE_TAC[p2cl_metric] THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC P2CL_CHART_EQ_G THEN
    MAP_EVERY EXISTS_TAC [`Dm:num->real^N->bool`; `Om:num->num->real^N->bool`;
                          `Tr:num->num->real^N->real^N`; `kp:num->real^N->B`] THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC SELECT_CONV THEN MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[metric_local] THEN ASM_REWRITE_TAC[] THEN
  REMOVE_THEN "compat" (MP_TAC o SPECL [`i:num`; `i':num`; `y:real^N`]) THEN
  ASM_REWRITE_TAC[mpullback] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]));;

(* The glued metric is riemannian. *)

let P2CL_RIEMANNIAN = prove
 (`!Dm Om Tr (kp:num->real^N->B) (G:num->real^N->real^N^N).
     p2cl_system Dm Om Tr /\ p2cl_glue Dm Om Tr kp /\
     (!i. metric_field (Dm i) (G i)) /\
     (!i j z. z IN Om i j ==> G i z = mpullback (Tr i j) (G j) z)
     ==> riemannian_metric (p2cl_atlas Dm kp) (p2cl_metric Dm kp G)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[riemannian_metric; P2CL_IN_ATLAS_ALT] THEN
  X_GEN_TAC `c:(B->bool)#(B->real^N)` THEN
  DISCH_THEN(X_CHOOSE_THEN `i:num` SUBST1_TAC) THEN
  MP_TAC(ISPECL [`Dm:num->real^N->bool`; `Om:num->num->real^N->bool`;
                 `Tr:num->num->real^N->real^N`; `kp:num->real^N->B`; `i:num`]
                P2CL_CHART_IMAGE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC MFDR_METRIC_FIELD_EQ THEN EXISTS_TAC `(G:num->real^N->real^N^N) i` THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
  MATCH_MP_TAC P2CL_METRIC_LOCAL THEN
  MAP_EVERY EXISTS_TAC [`Om:num->num->real^N->bool`; `Tr:num->num->real^N->real^N`] THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Every system has a gluing map into real^N.  The pair (i,z)                *)
(* goes to its canonical representative (the least index k with z in        *)
(* Om i k, and Tr i k z), and the pairs inject into real^N by cardinality.  *)
(* ------------------------------------------------------------------------- *)

let P2CL_TRANS = prove
 (`!(Dm:num->real^N->bool) Om Tr i j k z.
     p2cl_system Dm Om Tr /\ z IN Om i j /\ Tr i j z IN Om j k
     ==> z IN Om i k /\ Tr i k z = Tr j k (Tr i j z)`,
  REWRITE_TAC[p2cl_system] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(Tr:num->num->real^N->real^N) i j z IN Om j i /\ Tr j i (Tr i j z) = z`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`j:num`; `i:num`; `k:num`;
                                `(Tr:num->num->real^N->real^N) i j z`]) THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

let P2CL_OM_IFF = prove
 (`!(Dm:num->real^N->bool) Om Tr i j k z.
     p2cl_system Dm Om Tr /\ z IN Om i j
     ==> (z IN Om i k <=> Tr i j z IN Om j k)`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN DISCH_TAC THENL
   [UNDISCH_TAC `p2cl_system (Dm:num->real^N->bool) Om Tr` THEN
    REWRITE_TAC[p2cl_system] THEN STRIP_TAC THEN ASM_MESON_TAC[];
    MP_TAC(ISPECL [`Dm:num->real^N->bool`; `Om:num->num->real^N->bool`;
                   `Tr:num->num->real^N->real^N`; `i:num`; `j:num`; `k:num`; `z:real^N`]
                  P2CL_TRANS) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[]]);;

let p2cl_rep = new_definition
 `p2cl_rep (Om:num->num->real^N->bool) (Tr:num->num->real^N->real^N) i z =
    (minimal k. z IN Om i k), Tr i (minimal k. z IN Om i k) z`;;

let P2CL_MINIMAL_IN = prove
 (`!(Dm:num->real^N->bool) Om Tr i z.
     p2cl_system Dm Om Tr /\ z IN Dm i
     ==> z IN Om i (minimal k. z IN Om i k) /\
         !m. m < (minimal k. z IN Om i k) ==> ~(z IN Om i m)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2cl_system] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `\k. (z:real^N) IN (Om:num->num->real^N->bool) i k` MINIMAL) THEN
  REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[]);;

let P2CL_REP_EQ = prove
 (`!(Dm:num->real^N->bool) Om Tr i j z w.
     p2cl_system Dm Om Tr /\ z IN Dm i /\ w IN Dm j
     ==> (p2cl_rep Om Tr i z = p2cl_rep Om Tr j w <=> z IN Om i j /\ Tr i j z = w)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p2cl_rep; PAIR_EQ] THEN
  MP_TAC(ISPECL [`Dm:num->real^N->bool`; `Om:num->num->real^N->bool`;
                 `Tr:num->num->real^N->real^N`; `j:num`; `w:real^N`] P2CL_MINIMAL_IN) THEN
  MP_TAC(ISPECL [`Dm:num->real^N->bool`; `Om:num->num->real^N->bool`;
                 `Tr:num->num->real^N->real^N`; `i:num`; `z:real^N`] P2CL_MINIMAL_IN) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `k0 = minimal k. (z:real^N) IN (Om:num->num->real^N->bool) i k` THEN
  ABBREV_TAC `k1 = minimal k. (w:real^N) IN (Om:num->num->real^N->bool) j k` THEN
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2cl_system]) THEN
  EQ_TAC THENL
   [DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `(Tr:num->num->real^N->real^N) j k1 w IN Om k1 j /\ Tr k1 j (Tr j k1 w) = w`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`Dm:num->real^N->bool`; `Om:num->num->real^N->bool`;
                   `Tr:num->num->real^N->real^N`; `i:num`; `k1:num`; `j:num`; `z:real^N`]
                  P2CL_TRANS) THEN
    ASM_REWRITE_TAC[];
    STRIP_TAC THEN
    SUBGOAL_THEN `k1:num = k0` SUBST_ALL_TAC THENL
     [MAP_EVERY EXPAND_TAC ["k0"; "k1"] THEN AP_TERM_TAC THEN
      REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `k:num` THEN
      MP_TAC(ISPECL [`Dm:num->real^N->bool`; `Om:num->num->real^N->bool`;
                     `Tr:num->num->real^N->real^N`; `i:num`; `j:num`; `k:num`; `z:real^N`]
                    P2CL_OM_IFF) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]);
      ALL_TAC] THEN
    REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`i:num`; `j:num`; `k0:num`; `z:real^N`]) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[]]);;

let P2CL_INJ_EXISTS = prove
 (`?f:num#real^N->real^N. !x y. f x = f y ==> x = y`,
  MP_TAC(ISPECL [`(:num)`; `(:real^N)`] CARD_MUL_ABSORB_LE) THEN
  REWRITE_TAC[MUL_C_UNIV; EUCLIDEAN_SPACE_INFINITE; GSYM INFINITE_CARD_LE] THEN
  REWRITE_TAC[le_c; IN_UNIV] THEN MESON_TAC[]);;

let P2CL_GLUE_EXISTS = prove
 (`!(Dm:num->real^N->bool) Om Tr.
     p2cl_system Dm Om Tr ==> ?kp:num->real^N->real^N. p2cl_glue Dm Om Tr kp`,
  REPEAT STRIP_TAC THEN
  X_CHOOSE_TAC `f:num#real^N->real^N` P2CL_INJ_EXISTS THEN
  EXISTS_TAC `\i z. (f:num#real^N->real^N) (p2cl_rep Om Tr i z)` THEN
  REWRITE_TAC[p2cl_glue] THEN REPEAT STRIP_TAC THEN
  TRANS_TAC EQ_TRANS
   `p2cl_rep (Om:num->num->real^N->bool) Tr i z = p2cl_rep Om Tr j w` THEN
  CONJ_TAC THENL
   [ASM_MESON_TAC[];
    MATCH_MP_TAC P2CL_REP_EQ THEN EXISTS_TAC `Dm:num->real^N->bool` THEN
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Smooth maps out of the glued manifold are the maps that are               *)
(* smooth in the coordinates z of the pieces Dm i (through kp i).           *)
(* ------------------------------------------------------------------------- *)

let P2CL_CHART_COORDS = prove
 (`!Dm Om Tr (kp:num->real^N->B) (W:B->bool) (f:B->C) (c':(C->bool)#(C->real^M)) i.
     p2cl_system Dm Om Tr /\ p2cl_glue Dm Om Tr kp
     ==> IMAGE (SND(p2cl_chart Dm kp i))
               {x | x IN FST(p2cl_chart Dm kp i) INTER W /\ f x IN FST c'} =
         {z | z IN Dm i /\ kp i z IN W /\ f(kp i z) IN FST c'} /\
         (!z. z IN Dm i
              ==> (SND c' o f o chart_inv (p2cl_chart Dm kp i)) z = (SND c' o f o kp i) z)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!z. z IN (Dm:num->real^N->bool) i
                    ==> SND(p2cl_chart Dm (kp:num->real^N->B) i) (kp i z) = z /\
                        chart_inv (p2cl_chart Dm kp i) z = kp i z`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THENL
     [MATCH_MP_TAC P2CL_CHART_INV; MATCH_MP_TAC P2CL_CHART_INVERSE] THEN
    MAP_EVERY EXISTS_TAC [`Om:num->num->real^N->bool`; `Tr:num->num->real^N->real^N`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[P2CL_CHART_FST; EXTENSION; IN_IMAGE; IN_ELIM_THM; IN_INTER] THEN
    X_GEN_TAC `y:real^N` THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `p:B` STRIP_ASSUME_TAC) THEN
      FIRST_X_ASSUM SUBST_ALL_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
      ASM_SIMP_TAC[];
      STRIP_TAC THEN EXISTS_TAC `(kp:num->real^N->B) i y` THEN ASM_SIMP_TAC[] THEN
      EXISTS_TAC `y:real^N` THEN ASM_REWRITE_TAC[]];
    ASM_SIMP_TAC[o_THM]]);;

let P2CL_SMOOTH_MAP_FROM = prove
 (`!Dm Om Tr (kp:num->real^N->B) (atlas':((C->bool)#(C->real^M))->bool) W (f:B->C).
     p2cl_system Dm Om Tr /\ p2cl_glue Dm Om Tr kp
     ==> (mfd_smooth_map (p2cl_atlas Dm kp) atlas' W f <=>
          !i c'. c' IN atlas'
                 ==> smooth_map_on {z | z IN Dm i /\ kp i z IN W /\ f(kp i z) IN FST c'}
                                   (SND c' o f o kp i))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`Dm:num->real^N->bool`; `Om:num->num->real^N->bool`;
                 `Tr:num->num->real^N->real^N`; `kp:num->real^N->B`; `W:B->bool`; `f:B->C`]
                P2CL_CHART_COORDS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "key") THEN
  REWRITE_TAC[mfd_smooth_map; P2CL_IN_ATLAS_ALT] THEN EQ_TAC THENL
   [DISCH_TAC THEN MAP_EVERY X_GEN_TAC [`i:num`; `c':(C->bool)#(C->real^M)`] THEN
    DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`p2cl_chart (Dm:num->real^N->bool) (kp:num->real^N->B) i`;
                                  `c':(C->bool)#(C->real^M)`]) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    USE_THEN "key" (MP_TAC o SPECL [`c':(C->bool)#(C->real^M)`; `i:num`]) THEN
    DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC) THEN DISCH_TAC THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
    EXISTS_TAC `SND(c':(C->bool)#(C->real^M)) o (f:B->C) o
                chart_inv (p2cl_chart (Dm:num->real^N->bool) (kp:num->real^N->B) i)` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[];
    DISCH_TAC THEN MAP_EVERY X_GEN_TAC [`c:(B->bool)#(B->real^N)`; `c':(C->bool)#(C->real^M)`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `i:num` SUBST1_TAC) ASSUME_TAC) THEN
    USE_THEN "key" (MP_TAC o SPECL [`c':(C->bool)#(C->real^M)`; `i:num`]) THEN
    DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC) THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
    EXISTS_TAC `SND(c':(C->bool)#(C->real^M)) o (f:B->C) o (kp:num->real^N->B) i` THEN
    ASM_SIMP_TAC[] THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The headline.  A separated system of chart domains Dm i with              *)
(* smooth transitions Tr i j on Om i j and compatible metric fields G i     *)
(* (G i is the pullback of G j by Tr i j) glues, along any gluing map kp,   *)
(* to a Hausdorff smooth manifold with a riemannian metric whose            *)
(* representative in the chart i is G i; a gluing map into real^N exists.   *)
(* ------------------------------------------------------------------------- *)

let P2CL_GLUED_MANIFOLD = prove
 (`!Dm Om Tr (kp:num->real^N->B) (G:num->real^N->real^N^N).
     p2cl_system Dm Om Tr /\ p2cl_separated Dm Om Tr /\ p2cl_glue Dm Om Tr kp /\
     (!i. metric_field (Dm i) (G i)) /\
     (!i j z. z IN Om i j ==> G i z = mpullback (Tr i j) (G j) z)
     ==> hausdorff_space (p2cl_top Dm kp) /\
         smooth_manifold_atlas (p2cl_top Dm kp) (p2cl_atlas Dm kp) /\
         riemannian_metric (p2cl_atlas Dm kp) (p2cl_metric Dm kp G) /\
         topspace (p2cl_top Dm kp) = UNIONS {IMAGE (kp i) (Dm i) | i IN (:num)} /\
         (!i. p2cl_chart Dm kp i IN p2cl_atlas Dm kp /\
              FST(p2cl_chart Dm kp i) = IMAGE (kp i) (Dm i) /\
              !z. z IN Dm i ==> SND(p2cl_chart Dm kp i) (kp i z) = z) /\
         (!i y. y IN Dm i
                ==> metric_local (p2cl_atlas Dm kp) (p2cl_chart Dm kp i)
                                 (p2cl_metric Dm kp G) y = G i y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC P2CL_HAUSDORFF THEN
    MAP_EVERY EXISTS_TAC [`Om:num->num->real^N->bool`; `Tr:num->num->real^N->real^N`] THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC P2CL_SMOOTH_ATLAS THEN
    MAP_EVERY EXISTS_TAC [`Om:num->num->real^N->bool`; `Tr:num->num->real^N->real^N`] THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC P2CL_RIEMANNIAN THEN
    MAP_EVERY EXISTS_TAC [`Om:num->num->real^N->bool`; `Tr:num->num->real^N->real^N`] THEN
    ASM_REWRITE_TAC[];
    FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2cl_system]) THEN
    ASM_SIMP_TAC[P2CL_TOPSPACE; p2cl_space];
    X_GEN_TAC `i:num` THEN REWRITE_TAC[P2CL_CHART_FST; P2CL_IN_ATLAS_ALT] THEN
    CONJ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC P2CL_CHART_INV THEN
    MAP_EVERY EXISTS_TAC [`Om:num->num->real^N->bool`; `Tr:num->num->real^N->real^N`] THEN
    ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC P2CL_METRIC_LOCAL THEN
    MAP_EVERY EXISTS_TAC [`Om:num->num->real^N->bool`; `Tr:num->num->real^N->real^N`] THEN
    ASM_REWRITE_TAC[]]);;

