(* ========================================================================= *)
(* pc_smt_orient: M7, simply connected smooth manifolds are orientable      *)
(* (SMT_ORIENTABLE_STATEMENT).  Route (as in pc_top_orient, Hatcher 3.3 and *)
(* Lee, Introduction to Smooth Manifolds, 2nd ed., Theorem 15.41 and        *)
(* Corollary 15.42 on the orientation covering): a Z/2 cocycle (here the    *)
(* sign of the Jacobian determinant of chart transitions) on a simply       *)
(* connected, locally path connected space is a coboundary.  Its points are *)
(* (x,b), b the orientation relative to a reference index k x; the sheets   *)
(* over the U i are the graphs y |-> (y, P i (k y) y <=> e); FST is a two-   *)
(* sheeted covering map (pc_top_cover covering_map), a continuous section   *)
(* (COVERING_MAP_SECTION) splits every U i into the open parts where the    *)
(* index agrees or disagrees with the section.  Charts reflected on the     *)
(* disagreeing parts form an oriented atlas compatible with the given one.  *)
(*                                                                           *)
(* Z/2 cocycles and the topology of the double cover.                       *)
(* ========================================================================= *)

needs "src/pc_mfd_diff.ml";;
needs "src/pc_smt_defs.ml";;

prioritize_real();;
type_invention_error := true;;

(* A Z/2 cocycle: open sets U i, a reference index k x with x IN U (k x),    *)
(* P i j x (x in U i and U j) locally constant, reflexive and with           *)
(* P i l <=> (P i j <=> P j l).                                              *)

let smt_zcocycle = new_definition
 `smt_zcocycle (top:A topology) (U:C->A->bool) (P:C->C->A->bool) (k:A->C) <=>
    (!i. open_in top (U i)) /\
    (!x. x IN topspace top ==> x IN U (k x)) /\
    (!i x. x IN U i ==> P i i x) /\
    (!i j l x. x IN U i /\ x IN U j /\ x IN U l
               ==> (P i l x <=> (P i j x <=> P j l x))) /\
    (!i j. open_in top {x | x IN U i /\ x IN U j /\ P i j x}) /\
    (!i j. open_in top {x | x IN U i /\ x IN U j /\ ~P i j x})`;;

(* The double cover: sheets are graphs over open subsets of the U i.         *)

let smt_zcover_basic = new_definition
 `smt_zcover_basic (top:A topology) (U:C->A->bool) (P:C->C->A->bool) (k:A->C) s <=>
    ?i e V. open_in top V /\ V SUBSET U i /\
            s = IMAGE (\y. y,(P i (k y) y <=> e)) V`;;

let smt_zcover = new_definition
 `smt_zcover (top:A topology) (U:C->A->bool) (P:C->C->A->bool) (k:A->C) =
    topology (ARBITRARY UNION_OF smt_zcover_basic top U P k)`;;

let SMT_ZCOVER_IN_GRAPH = prove
 (`!(f:A->bool) v y b. (y,b) IN IMAGE (\y. y,f y) v <=> y IN v /\ b = f y`,
  REWRITE_TAC[IN_IMAGE; PAIR_EQ] THEN MESON_TAC[]);;

let SMT_ZCOVER_FST_GRAPH = prove
 (`!(f:A->bool) v. IMAGE FST (IMAGE (\y. y,f y) v) = v`,
  REWRITE_TAC[GSYM IMAGE_o; o_DEF; FST; IMAGE_ID]);;

let SMT_ZCOCYCLE_SUBSET = prove
 (`!(top:A topology) (U:C->A->bool) P k i.
        smt_zcocycle top U P k ==> U i SUBSET topspace top`,
  REWRITE_TAC[smt_zcocycle] THEN MESON_TAC[OPEN_IN_SUBSET]);;

let SMT_ZCOVER_AGREE = prove
 (`!(top:A topology) (U:C->A->bool) P k i j e e' y.
        smt_zcocycle top U P k /\ y IN U i /\ y IN U j
        ==> (((P i (k y) y <=> e) <=> (P j (k y) y <=> e')) <=>
             (P i j y <=> (e <=> e')))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(y:A) IN U((k:A->C) y)` ASSUME_TAC THENL
   [UNDISCH_TAC `smt_zcocycle (top:A topology) (U:C->A->bool) P k` THEN
    REWRITE_TAC[smt_zcocycle] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o MATCH_MP OPEN_IN_SUBSET o SPEC `i:C`)
      (MP_TAC o CONJUNCT1)) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `smt_zcocycle (top:A topology) (U:C->A->bool) P k` THEN
  REWRITE_TAC[smt_zcocycle] THEN
  DISCH_THEN(MP_TAC o SPECL [`i:C`; `j:C`; `(k:A->C) y`; `y:A`] o
             CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC TAUT);;

let SMT_ZCOVER_BASIC_INTER = prove
 (`!(top:A topology) (U:C->A->bool) P k s t.
        smt_zcocycle top U P k /\
        smt_zcover_basic top U P k s /\ smt_zcover_basic top U P k t
        ==> smt_zcover_basic top U P k (s INTER t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[smt_zcover_basic] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `i:C` (X_CHOOSE_THEN `e:bool`
      (X_CHOOSE_THEN `V:A->bool` STRIP_ASSUME_TAC)))
    (X_CHOOSE_THEN `j:C` (X_CHOOSE_THEN `e':bool`
      (X_CHOOSE_THEN `V':A->bool` STRIP_ASSUME_TAC))))) THEN
  SUBGOAL_THEN
   `!y:A. y IN V /\ y IN V'
          ==> ((((P:C->C->A->bool) i ((k:A->C) y) y <=> e) <=> (P j (k y) y <=> e')) <=>
               (P i j y <=> (e <=> e')))`
  (LABEL_TAC "agree") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `U:C->A->bool`; `P:C->C->A->bool`; `k:A->C`;
                   `i:C`; `j:C`; `e:bool`; `e':bool`; `y:A`] SMT_ZCOVER_AGREE) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; REWRITE_TAC[]];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`i:C`; `e:bool`;
    `V INTER V' INTER {y:A | y IN U i /\ y IN U j /\
                             ((P:C->C->A->bool) i j y <=> (e <=> e'))}`] THEN
  REPEAT CONJ_TAC THENL
   [REPEAT(MATCH_MP_TAC OPEN_IN_INTER THEN ASM_REWRITE_TAC[] THEN TRY CONJ_TAC) THEN
    UNDISCH_TAC `smt_zcocycle (top:A topology) (U:C->A->bool) P k` THEN
    REWRITE_TAC[smt_zcocycle] THEN STRIP_TAC THEN
    ASM_CASES_TAC `e:bool <=> e'` THEN ASM_REWRITE_TAC[];
    ASM SET_TAC[];
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[EXTENSION; FORALL_PAIR_THM; IN_INTER; SMT_ZCOVER_IN_GRAPH; IN_ELIM_THM] THEN
    MAP_EVERY X_GEN_TAC [`y:A`; `b:bool`] THEN
    ASM_CASES_TAC `(y:A) IN V` THEN ASM_CASES_TAC `(y:A) IN V'` THEN
    ASM_REWRITE_TAC[] THEN
    USE_THEN "agree" (MP_TAC o SPEC `y:A`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(y:A) IN U(i:C) /\ y IN U(j:C)` (fun th -> REWRITE_TAC[th]) THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    CONV_TAC TAUT]);;

let SMT_ZCOVER_OPEN_IN = prove
 (`!(top:A topology) (U:C->A->bool) P k.
        smt_zcocycle top U P k
        ==> open_in (smt_zcover top U P k) =
            ARBITRARY UNION_OF smt_zcover_basic top U P k`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[smt_zcover] THEN
  REWRITE_TAC[GSYM(CONJUNCT2 topology_tybij)] THEN
  MATCH_MP_TAC ISTOPOLOGY_BASE THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC SMT_ZCOVER_BASIC_INTER THEN ASM_REWRITE_TAC[]);;

let SMT_ZCOVER_SHEET_OPEN = prove
 (`!(top:A topology) (U:C->A->bool) P k i e V.
        smt_zcocycle top U P k /\ open_in top V /\ V SUBSET U i
        ==> open_in (smt_zcover top U P k) (IMAGE (\y. y,(P i (k y) y <=> e)) V)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[SMT_ZCOVER_OPEN_IN] THEN
  MATCH_MP_TAC ARBITRARY_UNION_OF_INC THEN REWRITE_TAC[smt_zcover_basic] THEN
  MAP_EVERY EXISTS_TAC [`i:C`; `e:bool`; `V:A->bool`] THEN ASM_REWRITE_TAC[]);;

let SMT_ZCOVER_IN_TOPSPACE = prove
 (`!(top:A topology) (U:C->A->bool) P k x b.
        smt_zcocycle top U P k
        ==> ((x,b) IN topspace(smt_zcover top U P k) <=> x IN topspace top)`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN
    MP_TAC(ISPEC `smt_zcover (top:A topology) (U:C->A->bool) P k` OPEN_IN_TOPSPACE) THEN
    ASM_SIMP_TAC[SMT_ZCOVER_OPEN_IN; ARBITRARY_UNION_OF_ALT] THEN
    DISCH_THEN(MP_TAC o SPEC `(x:A,b:bool)`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:A#bool->bool` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [smt_zcover_basic] o
                  GEN_REWRITE_RULE I [IN]) THEN
    DISCH_THEN(X_CHOOSE_THEN `i:C` (X_CHOOSE_THEN `e:bool`
      (X_CHOOSE_THEN `V:A->bool` STRIP_ASSUME_TAC))) THEN
    UNDISCH_TAC `(x:A,b:bool) IN t` THEN ASM_REWRITE_TAC[SMT_ZCOVER_IN_GRAPH] THEN
    STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `U:C->A->bool`; `P:C->C->A->bool`; `k:A->C`;
                   `i:C`] SMT_ZCOCYCLE_SUBSET) THEN
    ASM SET_TAC[];
    DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `U:C->A->bool`; `P:C->C->A->bool`; `k:A->C`;
                   `(k:A->C) x`; `b:bool`; `U((k:A->C) x):A->bool`] SMT_ZCOVER_SHEET_OPEN) THEN
    UNDISCH_TAC `smt_zcocycle (top:A topology) (U:C->A->bool) P k` THEN
    REWRITE_TAC[smt_zcocycle] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[SUBSET_REFL] THEN
    DISCH_THEN(MP_TAC o MATCH_MP OPEN_IN_SUBSET) THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[SMT_ZCOVER_IN_GRAPH] THEN ASM_SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* FST is a two-sheeted covering map, and a Z/2 cocycle on a                *)
(* simply connected, locally path connected space is trivial: a continuous *)
(* section eps splits every U i into the open sets where eps agrees or      *)
(* disagrees with P i (k x) x.                                               *)
(* ------------------------------------------------------------------------- *)

let SMT_ZCOVER_FST_CONTINUOUS = prove
 (`!(top:A topology) (U:C->A->bool) P k.
        smt_zcocycle top U P k ==> continuous_map (smt_zcover top U P k,top) FST`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[continuous_map; FORALL_PAIR_THM] THEN
  ASM_SIMP_TAC[SMT_ZCOVER_IN_TOPSPACE; FST] THEN
  X_GEN_TAC `u:A->bool` THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[OPEN_IN_SUBOPEN] THEN
  REWRITE_TAC[FORALL_PAIR_THM; IN_ELIM_THM] THEN
  MAP_EVERY X_GEN_TAC [`x:A`; `b:bool`] THEN
  ASM_SIMP_TAC[SMT_ZCOVER_IN_TOPSPACE; FST] THEN STRIP_TAC THEN
  SUBGOAL_THEN `open_in top (U((k:A->C) x):A->bool) /\ x IN U(k x) /\
                (P:C->C->A->bool) (k x) (k x) x`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `smt_zcocycle (top:A topology) (U:C->A->bool) P k` THEN
    REWRITE_TAC[smt_zcocycle] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `IMAGE (\y:A. y,((P:C->C->A->bool) ((k:A->C) x) (k y) y <=> b))
                    (U(k x) INTER u)` THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `U:C->A->bool`; `P:C->C->A->bool`; `k:A->C`;
                   `(k:A->C) x`; `b:bool`; `U((k:A->C) x) INTER u:A->bool`]
      SMT_ZCOVER_SHEET_OPEN) THEN
    ASM_SIMP_TAC[OPEN_IN_INTER; INTER_SUBSET];
    ASM_REWRITE_TAC[SMT_ZCOVER_IN_GRAPH; IN_INTER];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; IN_INTER] THEN
    ASM_SIMP_TAC[SMT_ZCOVER_IN_TOPSPACE; FST] THEN
    MP_TAC(ISPECL [`top:A topology`; `U:C->A->bool`; `P:C->C->A->bool`; `k:A->C`;
                   `(k:A->C) x`] SMT_ZCOCYCLE_SUBSET) THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[]]);;

let SMT_ZCOVER_FST_OPEN_MAP = prove
 (`!(top:A topology) (U:C->A->bool) P k.
        smt_zcocycle top U P k ==> open_map (smt_zcover top U P k,top) FST`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[open_map] THEN
  ASM_SIMP_TAC[SMT_ZCOVER_OPEN_IN; ARBITRARY_UNION_OF_ALT] THEN
  X_GEN_TAC `w:A#bool->bool` THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[OPEN_IN_SUBOPEN] THEN
  REWRITE_TAC[FORALL_IN_IMAGE; FORALL_PAIR_THM; FST] THEN
  MAP_EVERY X_GEN_TAC [`x:A`; `b:bool`] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:A,b:bool`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:A#bool->bool` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [smt_zcover_basic] o
                GEN_REWRITE_RULE I [IN]) THEN
  DISCH_THEN(X_CHOOSE_THEN `i:C` (X_CHOOSE_THEN `e:bool`
    (X_CHOOSE_THEN `V:A->bool` STRIP_ASSUME_TAC))) THEN
  EXISTS_TAC `V:A->bool` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [UNDISCH_TAC `(x:A,b:bool) IN t` THEN ASM_REWRITE_TAC[SMT_ZCOVER_IN_GRAPH] THEN
    SIMP_TAC[];
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `IMAGE FST (t:A#bool->bool)` THEN
    CONJ_TAC THENL
     [ASM_REWRITE_TAC[SMT_ZCOVER_FST_GRAPH; SUBSET_REFL];
      MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[]]]);;

let SMT_ZCOVER_SHEET_HOMEOMORPHIC = prove
 (`!(top:A topology) (U:C->A->bool) P k i e V.
        smt_zcocycle top U P k /\ open_in top V /\ V SUBSET U i
        ==> homeomorphic_map
             (subtopology (smt_zcover top U P k) (IMAGE (\y. y,(P i (k y) y <=> e)) V),
              subtopology top V) FST`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `U:C->A->bool`; `P:C->C->A->bool`; `k:A->C`;
                 `i:C`; `e:bool`; `V:A->bool`] SMT_ZCOVER_SHEET_OPEN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`\y:A. ((P:C->C->A->bool) i ((k:A->C) y) y <=> e)`; `V:A->bool`]
    SMT_ZCOVER_FST_GRAPH) THEN
  REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `S = IMAGE (\y:A. y,((P:C->C->A->bool) i ((k:A->C) y) y <=> e)) V` THEN
  SUBGOAL_THEN `!z1 z2:A#bool. z1 IN S /\ z2 IN S ==> (FST z1 = FST z2 <=> z1 = z2)`
  ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN
    REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE; FST; PAIR_EQ] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `topspace(subtopology (smt_zcover (top:A topology) (U:C->A->bool) P k) S) = S`
  ASSUME_TAC THENL
   [MATCH_MP_TAC TOPSPACE_SUBTOPOLOGY_SUBSET THEN ASM_SIMP_TAC[OPEN_IN_SUBSET];
    ALL_TAC] THEN
  MATCH_MP_TAC BIJECTIVE_OPEN_IMP_HOMEOMORPHIC_MAP THEN REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY; SUBSET_REFL] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY THEN
    ASM_SIMP_TAC[SMT_ZCOVER_FST_CONTINUOUS];
    ASM_SIMP_TAC[OPEN_MAP_IN_SUBTOPOLOGY; SUBSET_REFL] THEN
    MATCH_MP_TAC OPEN_MAP_FROM_SUBTOPOLOGY THEN
    ASM_SIMP_TAC[SMT_ZCOVER_FST_OPEN_MAP];
    ASM_REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC TOPSPACE_SUBTOPOLOGY_SUBSET THEN ASM_SIMP_TAC[OPEN_IN_SUBSET];
    ASM_REWRITE_TAC[]]);;

let SMT_ZCOVER_COVERING_MAP = prove
 (`!(top:A topology) (U:C->A->bool) P k.
        smt_zcocycle top U P k ==> covering_map (smt_zcover top U P k,top) FST`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[covering_map] THEN
  ASM_SIMP_TAC[SMT_ZCOVER_FST_CONTINUOUS] THEN CONJ_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:A` THEN
    REWRITE_TAC[IN_IMAGE; EXISTS_PAIR_THM; FST] THEN
    ASM_SIMP_TAC[SMT_ZCOVER_IN_TOPSPACE] THEN MESON_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `y0:A` THEN DISCH_TAC THEN
  SUBGOAL_THEN `open_in top (U((k:A->C) y0):A->bool) /\ y0 IN U(k y0)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `smt_zcocycle (top:A topology) (U:C->A->bool) P k` THEN
    REWRITE_TAC[smt_zcocycle] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `U:C->A->bool`; `P:C->C->A->bool`; `k:A->C`;
                 `(k:A->C) y0`] SMT_ZCOCYCLE_SUBSET) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  EXISTS_TAC `U((k:A->C) y0):A->bool` THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `sh = \e. IMAGE (\y:A. y,((P:C->C->A->bool) ((k:A->C) y0) (k y) y <=> e))
                             (U(k y0))` THEN
  SUBGOAL_THEN
   `!e. open_in (smt_zcover (top:A topology) (U:C->A->bool) P k)
                ((sh:bool->A#bool->bool) e) /\
        homeomorphic_map (subtopology (smt_zcover top U P k) (sh e),
                          subtopology top (U((k:A->C) y0))) FST`
  ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "sh" THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `U:C->A->bool`; `P:C->C->A->bool`; `k:A->C`;
                     `(k:A->C) y0`; `e:bool`; `U((k:A->C) y0):A->bool`]
        SMT_ZCOVER_SHEET_OPEN);
      MP_TAC(ISPECL [`top:A topology`; `U:C->A->bool`; `P:C->C->A->bool`; `k:A->C`;
                     `(k:A->C) y0`; `e:bool`; `U((k:A->C) y0):A->bool`]
        SMT_ZCOVER_SHEET_HOMEOMORPHIC)] THEN
    ASM_REWRITE_TAC[SUBSET_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `DISJOINT ((sh:bool->A#bool->bool) T) (sh F)` ASSUME_TAC THENL
   [EXPAND_TAC "sh" THEN
    REWRITE_TAC[IN_DISJOINT; NOT_EXISTS_THM; FORALL_PAIR_THM; SMT_ZCOVER_IN_GRAPH] THEN
    REPEAT GEN_TAC THEN CONV_TAC TAUT;
    ALL_TAC] THEN
  EXISTS_TAC `{(sh:bool->A#bool->bool) T, sh F}` THEN
  ASM_REWRITE_TAC[FORALL_IN_INSERT; NOT_IN_EMPTY; PAIRWISE_INSERT; PAIRWISE_SING;
                  IN_SING] THEN
  CONJ_TAC THENL
   [EXPAND_TAC "sh" THEN REWRITE_TAC[UNIONS_2] THEN GEN_REWRITE_TAC I [EXTENSION] THEN
    REWRITE_TAC[FORALL_PAIR_THM; IN_UNION; SMT_ZCOVER_IN_GRAPH; IN_ELIM_THM; FST] THEN
    ASM_SIMP_TAC[SMT_ZCOVER_IN_TOPSPACE] THEN
    MAP_EVERY X_GEN_TAC [`y:A`; `b:bool`] THEN
    ASM_CASES_TAC `(y:A) IN U((k:A->C) y0)` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(y:A) IN topspace top` (fun th -> REWRITE_TAC[th]) THENL
     [ASM SET_TAC[]; CONV_TAC TAUT];
    ASM_MESON_TAC[DISJOINT_SYM]]);;

(* A Z/2 cocycle on a simply connected, locally path connected space is a   *)
(* coboundary.                                                               *)

let SMT_ZCOCYCLE_TRIVIAL = prove
 (`!(top:A topology) (U:C->A->bool) P k.
        smt_zcocycle top U P k /\ simply_connected_space top /\
        locally_path_connected_space top
        ==> ?eps. !i. open_in top {x | x IN U i /\ (eps x <=> P i (k x) x)} /\
                      open_in top {x | x IN U i /\ ~(eps x <=> P i (k x) x)}`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `topspace top:A->bool = {}` THENL
   [EXISTS_TAC `\x:A. T` THEN X_GEN_TAC `i:C` THEN
    SUBGOAL_THEN `U(i:C):A->bool = {}` (fun th ->
      REWRITE_TAC[th; NOT_IN_EMPTY; EMPTY_GSPEC; OPEN_IN_EMPTY]) THEN
    MP_TAC(ISPECL [`top:A topology`; `U:C->A->bool`; `P:C->C->A->bool`; `k:A->C`;
                   `i:C`] SMT_ZCOCYCLE_SUBSET) THEN
    ASM_REWRITE_TAC[SUBSET_EMPTY];
    ALL_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `x0:A` o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  MP_TAC(ISPECL [`smt_zcover (top:A topology) (U:C->A->bool) P k`; `top:A topology`;
                 `FST:A#bool->A`; `(x0:A,T)`] COVERING_MAP_SECTION) THEN
  ASM_SIMP_TAC[SMT_ZCOVER_COVERING_MAP; SMT_ZCOVER_IN_TOPSPACE] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:A->A#bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `\x:A. SND((s:A->A#bool) x)` THEN X_GEN_TAC `i:C` THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `!x:A. x IN topspace top ==> (s:A->A#bool) x = (x,SND(s x))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [GSYM PAIR] THEN
    ASM_SIMP_TAC[PAIR_EQ];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `U:C->A->bool`; `P:C->C->A->bool`; `k:A->C`;
                 `i:C`] SMT_ZCOCYCLE_SUBSET) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `open_in top (U(i:C):A->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `smt_zcocycle (top:A topology) (U:C->A->bool) P k` THEN
    SIMP_TAC[smt_zcocycle];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!e. open_in top {x:A | x IN U i /\
                           ((SND((s:A->A#bool) x) <=> (P:C->C->A->bool) i (k x) x) <=> e)}`
  (fun th -> MP_TAC(SPEC `T` th) THEN MP_TAC(SPEC `F` th) THEN SIMP_TAC[]) THEN
  X_GEN_TAC `e:bool` THEN
  SUBGOAL_THEN
   `{x:A | x IN U i /\ ((SND((s:A->A#bool) x) <=> (P:C->C->A->bool) i (k x) x) <=> e)} =
    {x | x IN topspace top /\ s x IN IMAGE (\y. y,(P i (k y) y <=> e)) (U i)}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `x:A` THEN
    ASM_CASES_TAC `(x:A) IN topspace top` THENL
     [MP_TAC(MATCH_MP (ASSUME `!x:A. x IN topspace top ==> (s:A->A#bool) x = (x,SND(s x))`)
                       (ASSUME `(x:A) IN topspace top`)) THEN
      SPEC_TAC(`SND((s:A->A#bool) x)`,`b:bool`) THEN GEN_TAC THEN
      DISCH_THEN SUBST1_TAC THEN
      ASM_REWRITE_TAC[SMT_ZCOVER_IN_GRAPH] THEN CONV_TAC TAUT;
      ASM SET_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC OPEN_IN_CONTINUOUS_MAP_PREIMAGE THEN
  EXISTS_TAC `smt_zcover (top:A topology) (U:C->A->bool) P k` THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `U:C->A->bool`; `P:C->C->A->bool`; `k:A->C`;
                 `i:C`; `e:bool`; `U(i:C):A->bool`] SMT_ZCOVER_SHEET_OPEN) THEN
  ASM_REWRITE_TAC[SUBSET_REFL]);;

(* ------------------------------------------------------------------------- *)
(* The Jacobian determinant of chart transitions is                         *)
(* multiplicative, nonzero, 1 on the diagonal and of locally constant sign, *)
(* so its sign is a Z/2 cocycle over the chart domains (reference index the *)
(* chart chart_at atlas x).                                                  *)
(* ------------------------------------------------------------------------- *)

let SMT_ORI_JAC_LINEAR = prove
 (`!top atlas (U:A->bool) (phi:A->real^N) V psi x.
        smooth_manifold_atlas top atlas /\ (U,phi) IN atlas /\ (V,psi) IN atlas /\
        x IN U INTER V
        ==> linear(chart_jac (U,phi) (V,psi) x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                `U:A->bool`; `phi:A->real^N`; `V:A->bool`; `psi:A->real^N`; `x:A`]
    CHART_TRANS_HAS_DERIVATIVE) THEN
  ASM_REWRITE_TAC[] THEN SIMP_TAC[has_derivative]);;

let SMT_ORI_DET_SELF = prove
 (`!top atlas (U:A->bool) (phi:A->real^N) x.
        smooth_manifold_atlas top atlas /\ (U,phi) IN atlas /\ x IN U
        ==> det(matrix(chart_jac (U,phi) (U,phi) x)) = &1`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                `U:A->bool`; `phi:A->real^N`; `x:A`] CHART_JAC_SELF) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[MATRIX_ID; DET_I]);;

let SMT_ORI_DET_CHAIN = prove
 (`!top atlas (U:A->bool) (phi:A->real^N) V psi W chi x.
        smooth_manifold_atlas top atlas /\ (U,phi) IN atlas /\ (V,psi) IN atlas /\
        (W,chi) IN atlas /\ x IN U INTER V INTER W
        ==> det(matrix(chart_jac (U,phi) (W,chi) x)) =
            det(matrix(chart_jac (V,psi) (W,chi) x)) *
            det(matrix(chart_jac (U,phi) (V,psi) x))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `linear(chart_jac (U,phi) (V,psi) (x:A)) /\
                linear(chart_jac (V:A->bool,psi:A->real^N) (W,chi) x)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SMT_ORI_JAC_LINEAR THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                `U:A->bool`; `phi:A->real^N`; `V:A->bool`; `psi:A->real^N`;
                `W:A->bool`; `chi:A->real^N`; `x:A`] CHART_JAC_CHAIN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  ASM_SIMP_TAC[MATRIX_COMPOSE; DET_MUL]);;

let SMT_ORI_DET_NZ = prove
 (`!top atlas (U:A->bool) (phi:A->real^N) V psi x.
        smooth_manifold_atlas top atlas /\ (U,phi) IN atlas /\ (V,psi) IN atlas /\
        x IN U INTER V
        ==> ~(det(matrix(chart_jac (U,phi) (V,psi) x)) = &0)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                `U:A->bool`; `phi:A->real^N`; `V:A->bool`; `psi:A->real^N`;
                `U:A->bool`; `phi:A->real^N`; `x:A`] SMT_ORI_DET_CHAIN) THEN
  MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                `U:A->bool`; `phi:A->real^N`; `x:A`] SMT_ORI_DET_SELF) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[REAL_MUL_RZERO] THEN REAL_ARITH_TAC);;

let SMT_ORI_DET_OPEN = prove
 (`!top atlas (U:A->bool) (phi:A->real^N) V psi.
        smooth_manifold_atlas top atlas /\ (U,phi) IN atlas /\ (V,psi) IN atlas
        ==> open_in top {x | x IN U /\ x IN V /\
                             &0 < det(matrix(chart_jac (U,phi) (V,psi) x))} /\
            open_in top {x | x IN U /\ x IN V /\
                             ~(&0 < det(matrix(chart_jac (U,phi) (V,psi) x)))}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `O = IMAGE (phi:A->real^N) (U INTER V)` THEN
  SUBGOAL_THEN `open(O:real^N->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "O" THEN MATCH_MP_TAC CHART_OVERLAP_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                          `psi:A->real^N`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on O (chart_trans (U:A->bool,phi:A->real^N) (V,psi))`
  ASSUME_TAC THENL
   [EXPAND_TAC "O" THEN MATCH_MP_TAC CHART_TRANS_SMOOTH THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\y. lift(det(matrix(frechet_derivative
                (chart_trans (U:A->bool,phi:A->real^N) (V,psi)) (at y)))))
    continuous_on O`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_LIFT_DET THEN
    MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[MATRIX_COMPONENT] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_LIFT_COMPONENT THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_FRECHET_DERIVATIVE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `continuous_map (subtopology top (U INTER V),euclidean) (phi:A->real^N)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY_MONO THEN EXISTS_TAC `U:A->bool` THEN
    REWRITE_TAC[INTER_SUBSET] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `(U:A->bool,phi:A->real^N)`] MFDD_CHART_CONTINUOUS) THEN
    ASM_REWRITE_TAC[FST; SND];
    ALL_TAC] THEN
  SUBGOAL_THEN `open_in top (U INTER V:A->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC OPEN_IN_INTER THEN
    ASM_MESON_TAC[SMOOTH_MANIFOLD_ATLAS_CHART];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x:A. x IN U /\ x IN V
          ==> phi x IN O /\
              (lift(det(matrix(frechet_derivative
                 (chart_trans (U:A->bool,phi:A->real^N) (V,psi)) (at (phi x))))))$1 =
              det(matrix(chart_jac (U,phi) (V,psi) x))`
  (LABEL_TAC "pt") THENL
   [REPEAT STRIP_TAC THENL
     [EXPAND_TAC "O" THEN ASM SET_TAC[];
      REWRITE_TAC[LIFT_COMPONENT; chart_jac; SND]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL
     [`\y. lift(det(matrix(frechet_derivative
             (chart_trans (U:A->bool,phi:A->real^N) (V,psi)) (at y))))`;
      `O:real^N->bool`; `{z:real^1 | z$1 > &0}`] CONTINUOUS_OPEN_PREIMAGE);
    MP_TAC(ISPECL
     [`\y. lift(det(matrix(frechet_derivative
             (chart_trans (U:A->bool,phi:A->real^N) (V,psi)) (at y))))`;
      `O:real^N->bool`; `{z:real^1 | z$1 < &0}`] CONTINUOUS_OPEN_PREIMAGE)] THEN
  ASM_REWRITE_TAC[OPEN_HALFSPACE_COMPONENT_GT; OPEN_HALFSPACE_COMPONENT_LT] THEN
  DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MFDM_OPEN_IN_PREIMAGE o
    CONJ (ASSUME `open_in top (U INTER V:A->bool)`) o
    CONJ (ASSUME `continuous_map (subtopology top (U INTER V),euclidean) (phi:A->real^N)`) o
    REWRITE_RULE[GSYM OPEN_IN_EUCLIDEAN]) THEN
  MATCH_MP_TAC(TAUT `(a <=> b) ==> a ==> b`) THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INTER] THEN X_GEN_TAC `x:A` THEN
  ASM_CASES_TAC `(x:A) IN U` THEN ASM_CASES_TAC `(x:A) IN V` THEN ASM_REWRITE_TAC[] THEN
  USE_THEN "pt" (MP_TAC o SPEC `x:A`) THEN
  (ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC]) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[real_gt] THEN
  MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                `U:A->bool`; `phi:A->real^N`; `V:A->bool`; `psi:A->real^N`; `x:A`]
    SMT_ORI_DET_NZ) THEN
  ASM_REWRITE_TAC[IN_INTER] THEN REAL_ARITH_TAC);;

(* The sign of the Jacobian determinant is a Z/2 cocycle.                    *)

let SMT_ORI_ZCOCYCLE = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool).
        smooth_manifold_atlas top atlas
        ==> smt_zcocycle top (\c. if c IN atlas then FST c else {})
                         (\c c' x. &0 < det(matrix(chart_jac c c' x)))
                         (chart_at atlas)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[smt_zcocycle; FORALL_PAIR_THM] THEN
  REPEAT CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`U:A->bool`; `phi:A->real^N`] THEN
    COND_CASES_TAC THEN REWRITE_TAC[OPEN_IN_EMPTY; FST] THEN
    ASM_MESON_TAC[SMOOTH_MANIFOLD_ATLAS_CHART];
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`]
      CHART_AT) THEN
    ASM_SIMP_TAC[];
    MAP_EVERY X_GEN_TAC [`U:A->bool`; `phi:A->real^N`; `x:A`] THEN
    COND_CASES_TAC THEN REWRITE_TAC[NOT_IN_EMPTY; FST] THEN DISCH_TAC THEN
    MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                  `U:A->bool`; `phi:A->real^N`; `x:A`] SMT_ORI_DET_SELF) THEN
    ASM_SIMP_TAC[] THEN REAL_ARITH_TAC;
    MAP_EVERY X_GEN_TAC [`U:A->bool`; `phi:A->real^N`; `V:A->bool`; `psi:A->real^N`;
                         `W:A->bool`; `chi:A->real^N`; `x:A`] THEN
    ASM_CASES_TAC `(U:A->bool,phi:A->real^N) IN atlas` THEN
    ASM_CASES_TAC `(V:A->bool,psi:A->real^N) IN atlas` THEN
    ASM_CASES_TAC `(W:A->bool,chi:A->real^N) IN atlas` THEN
    ASM_REWRITE_TAC[NOT_IN_EMPTY; FST] THEN STRIP_TAC THEN
    MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                  `U:A->bool`; `phi:A->real^N`; `V:A->bool`; `psi:A->real^N`;
                  `W:A->bool`; `chi:A->real^N`; `x:A`] SMT_ORI_DET_CHAIN) THEN
    ASM_REWRITE_TAC[IN_INTER] THEN DISCH_THEN SUBST1_TAC THEN
    MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                  `U:A->bool`; `phi:A->real^N`; `V:A->bool`; `psi:A->real^N`; `x:A`]
      SMT_ORI_DET_NZ) THEN
    MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                  `V:A->bool`; `psi:A->real^N`; `W:A->bool`; `chi:A->real^N`; `x:A`]
      SMT_ORI_DET_NZ) THEN
    ASM_REWRITE_TAC[IN_INTER; REAL_MUL_POS_LT] THEN REAL_ARITH_TAC;
    MAP_EVERY X_GEN_TAC [`U:A->bool`; `phi:A->real^N`; `V:A->bool`; `psi:A->real^N`] THEN
    ASM_CASES_TAC `(U:A->bool,phi:A->real^N) IN atlas` THEN
    ASM_CASES_TAC `(V:A->bool,psi:A->real^N) IN atlas` THEN
    ASM_REWRITE_TAC[NOT_IN_EMPTY; FST; EMPTY_GSPEC; OPEN_IN_EMPTY] THEN
    MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                  `U:A->bool`; `phi:A->real^N`; `V:A->bool`; `psi:A->real^N`]
      SMT_ORI_DET_OPEN) THEN
    ASM_SIMP_TAC[];
    MAP_EVERY X_GEN_TAC [`U:A->bool`; `phi:A->real^N`; `V:A->bool`; `psi:A->real^N`] THEN
    ASM_CASES_TAC `(U:A->bool,phi:A->real^N) IN atlas` THEN
    ASM_CASES_TAC `(V:A->bool,psi:A->real^N) IN atlas` THEN
    ASM_REWRITE_TAC[NOT_IN_EMPTY; FST; EMPTY_GSPEC; OPEN_IN_EMPTY] THEN
    MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                  `U:A->bool`; `phi:A->real^N`; `V:A->bool`; `psi:A->real^N`]
      SMT_ORI_DET_OPEN) THEN
    ASM_SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Modified charts.  Restricting charts of an atlas to open                 *)
(* subsets of their domains and composing them with linear involutions L   *)
(* (the identity or the reflection in the first coordinate) gives atlases  *)
(* compatible with the original one; the Jacobian of transitions between   *)
(* modified charts is L2 o J o L1.                                           *)
(* ------------------------------------------------------------------------- *)

let smt_ori_flip = new_definition
 `smt_ori_flip (s:bool) =
    if s then (\y:real^N. y) else reflect_along (basis 1:real^N)`;;

let SMT_ORI_FLIP = prove
 (`!s. linear(smt_ori_flip s:real^N->real^N) /\
       (!y. smt_ori_flip s (smt_ori_flip s y):real^N = y) /\
       det(matrix(smt_ori_flip s:real^N->real^N)) = if s then &1 else -- &1`,
  GEN_TAC THEN REWRITE_TAC[smt_ori_flip] THEN COND_CASES_TAC THEN
  REWRITE_TAC[LINEAR_ID; MATRIX_ID; DET_I; LINEAR_REFLECT_ALONG;
              REFLECT_ALONG_INVOLUTION] THEN
  SIMP_TAC[DET_MATRIX_REFLECT_ALONG; BASIS_NONZERO; DIMINDEX_GE_1; LE_REFL]);;

let SMT_ORI_INVOLUTION = prove
 (`!L:real^N->real^N.
        linear L /\ (!y. L(L y) = y)
        ==> (!s. open s ==> open(IMAGE L s)) /\
            (!s. IMAGE L (IMAGE L s) = s) /\
            (!s. homeomorphic_map (subtopology euclidean s,
                                   subtopology euclidean (IMAGE L s)) L) /\
            (!s. open s ==> smooth_map_on s L)`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!s. IMAGE (L:real^N->real^N) (IMAGE L s) = s` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM IMAGE_o; o_DEF] THEN ASM_REWRITE_TAC[IMAGE_ID];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`L:real^N->real^N`; `s:real^N->bool`]
      OPEN_BIJECTIVE_LINEAR_IMAGE_EQ) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_MESON_TAC[]; SIMP_TAC[]];
    GEN_TAC THEN REWRITE_TAC[TOPC_HOMEOMORPHIC_MAP_EUCLIDEAN] THEN
    EXISTS_TAC `L:real^N->real^N` THEN
    ASM_SIMP_TAC[homeomorphism; LINEAR_CONTINUOUS_ON] THEN
    REWRITE_TAC[FORALL_IN_IMAGE] THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(L:real^N->real^N) = L o (\x. x)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_LINEAR_O THEN ASM_REWRITE_TAC[SMOOTH_MAP_ON_ID]]);;

(* A set of modified charts covering the space is a smooth atlas.            *)

let SMT_ORI_MOD_ATLAS = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) S.
        smooth_manifold_atlas top atlas /\
        (!W chi. (W,chi) IN S
                 ==> ?U phi L. (U,phi) IN atlas /\ open_in top W /\ W SUBSET U /\
                               linear L /\ (!y. L(L y) = y) /\ chi = L o phi) /\
        (!x. x IN topspace top ==> ?W chi. (W,chi) IN S /\ x IN W)
        ==> smooth_manifold_atlas top S`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "mod") ASSUME_TAC)) THEN
  REWRITE_TAC[smooth_manifold_atlas] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`W:A->bool`; `chi:A->real^N`] THEN DISCH_TAC THEN
    USE_THEN "mod" (MP_TAC o SPECL [`W:A->bool`; `chi:A->real^N`]) THEN
    (ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC]) THEN
    DISCH_THEN(X_CHOOSE_THEN `U:A->bool` (X_CHOOSE_THEN `phi:A->real^N`
      (X_CHOOSE_THEN `L:real^N->real^N` STRIP_ASSUME_TAC))) THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    MP_TAC(ISPEC `L:real^N->real^N` SMT_ORI_INVOLUTION) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `W:A->bool`; `U:A->bool`; `phi:A->real^N`] MFDM_RESTRICT_CHART) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `U INTER W:A->bool = W` SUBST1_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[SUBTOPOLOGY_SUBTOPOLOGY; INTER_IDEMPOT] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[IMAGE_o] THEN
    MATCH_MP_TAC HOMEOMORPHIC_MAP_COMPOSE THEN
    EXISTS_TAC `subtopology euclidean (IMAGE (phi:A->real^N) W)` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`W1:A->bool`; `chi1:A->real^N`; `W2:A->bool`; `chi2:A->real^N`] THEN
  STRIP_TAC THEN
  USE_THEN "mod" (MP_TAC o SPECL [`W1:A->bool`; `chi1:A->real^N`]) THEN
  (ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC]) THEN
  DISCH_THEN(X_CHOOSE_THEN `U1:A->bool` (X_CHOOSE_THEN `phi1:A->real^N`
    (X_CHOOSE_THEN `L1:real^N->real^N` STRIP_ASSUME_TAC))) THEN
  USE_THEN "mod" (MP_TAC o SPECL [`W2:A->bool`; `chi2:A->real^N`]) THEN
  (ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC]) THEN
  DISCH_THEN(X_CHOOSE_THEN `U2:A->bool` (X_CHOOSE_THEN `phi2:A->real^N`
    (X_CHOOSE_THEN `L2:real^N->real^N` STRIP_ASSUME_TAC))) THEN
  UNDISCH_TAC `chi1:A->real^N = (L1:real^N->real^N) o (phi1:A->real^N)` THEN DISCH_THEN SUBST_ALL_TAC THEN
  UNDISCH_TAC `chi2:A->real^N = (L2:real^N->real^N) o (phi2:A->real^N)` THEN DISCH_THEN SUBST_ALL_TAC THEN
  FIRST_ASSUM(MP_TAC o SPECL [`U1:A->bool`; `phi1:A->real^N`; `U2:A->bool`; `phi2:A->real^N`] o
    CONJUNCT2 o CONJUNCT2 o GEN_REWRITE_RULE I [smooth_manifold_atlas]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPEC `L1:real^N->real^N` SMT_ORI_INVOLUTION) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `open(IMAGE (phi1:A->real^N) (U1 INTER U2))` ASSUME_TAC THENL
   [MATCH_MP_TAC CHART_OVERLAP_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                          `phi2:A->real^N`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `(L2:real^N->real^N) o (g:real^N->real^N) o (L1:real^N->real^N)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
    EXISTS_TAC `IMAGE (L1:real^N->real^N) (IMAGE (phi1:A->real^N) (U1 INTER U2))` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[IMAGE_o] THEN MATCH_MP_TAC IMAGE_SUBSET THEN
      MATCH_MP_TAC IMAGE_SUBSET THEN ASM SET_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_LINEAR_O THEN ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
    EXISTS_TAC `IMAGE (phi1:A->real^N) (U1 INTER U2)` THEN
    ASM_SIMP_TAC[SUBSET_REFL];
    REWRITE_TAC[o_THM; IN_INTER] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    AP_TERM_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]]);;

(* The Jacobian of transitions between modified charts.                      *)

let SMT_ORI_MOD_JAC = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) U1 phi1 W1 L1 U2 phi2 W2 L2 x.
        smooth_manifold_atlas top atlas /\ (U1,phi1) IN atlas /\ (U2,phi2) IN atlas /\
        open_in top W1 /\ W1 SUBSET U1 /\ open_in top W2 /\ W2 SUBSET U2 /\
        linear L1 /\ (!y. L1(L1 y) = y) /\ linear L2 /\ (!y. L2(L2 y) = y) /\
        x IN W1 INTER W2
        ==> chart_jac (W1,L1 o phi1) (W2,L2 o phi2) x =
            L2 o chart_jac (U1,phi1) (U2,phi2) x o L1`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[chart_jac; SND; o_THM] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
  MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_WITHIN_OPEN THEN
  EXISTS_TAC `(L2:real^N->real^N) o chart_trans (U1:A->bool,phi1:A->real^N) (U2,phi2) o (L1:real^N->real^N)` THEN
  EXISTS_TAC `IMAGE ((L1:real^N->real^N) o (phi1:A->real^N)) (W1 INTER W2)` THEN
  MP_TAC(ISPEC `L1:real^N->real^N` SMT_ORI_INVOLUTION) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[IMAGE_o] THEN FIRST_ASSUM MATCH_MP_TAC THEN
    MATCH_MP_TAC CHART_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                          `U1:A->bool`] THEN
    ASM_SIMP_TAC[OPEN_IN_INTER] THEN ASM SET_TAC[];
    REWRITE_TAC[IN_IMAGE; o_THM] THEN EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[FORALL_IN_IMAGE; o_THM; IN_INTER] THEN X_GEN_TAC `z:A` THEN STRIP_TAC THEN
    SUBGOAL_THEN `chart_inv (W1,(L1:real^N->real^N) o (phi1:A->real^N)) (L1(phi1 z)) = z`
    ASSUME_TAC THENL
     [REWRITE_TAC[chart_inv; FST; SND; o_THM] THEN MATCH_MP_TAC SELECT_UNIQUE THEN
      X_GEN_TAC `w:A` THEN REWRITE_TAC[] THEN EQ_TAC THENL
       [STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MANIFOLD_ATLAS_CHART_INJ THEN
        MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                              `U1:A->bool`; `phi1:A->real^N`] THEN
        ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
        CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
        FIRST_X_ASSUM(MP_TAC o AP_TERM `L1:real^N->real^N`) THEN ASM_REWRITE_TAC[];
        DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    GEN_REWRITE_TAC (RAND_CONV o RATOR_CONV) [chart_trans] THEN
    ASM_REWRITE_TAC[SND; o_THM] THEN AP_TERM_TAC THEN
    MATCH_MP_TAC CHART_TRANS_AT THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    MATCH_MP_TAC DIFF_CHAIN_AT THEN CONJ_TAC THENL
     [MATCH_MP_TAC DIFF_CHAIN_AT THEN ASM_SIMP_TAC[HAS_DERIVATIVE_LINEAR] THEN
      MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                    `U1:A->bool`; `phi1:A->real^N`; `U2:A->bool`; `phi2:A->real^N`;
                    `x:A`] CHART_TRANS_HAS_DERIVATIVE) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[chart_jac; SND];
      ASM_SIMP_TAC[HAS_DERIVATIVE_LINEAR]]]);;

let SMT_ORI_MOD_DET = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) U1 phi1 W1 L1 U2 phi2 W2 L2 x.
        smooth_manifold_atlas top atlas /\ (U1,phi1) IN atlas /\ (U2,phi2) IN atlas /\
        open_in top W1 /\ W1 SUBSET U1 /\ open_in top W2 /\ W2 SUBSET U2 /\
        linear L1 /\ (!y. L1(L1 y) = y) /\ linear L2 /\ (!y. L2(L2 y) = y) /\
        x IN W1 INTER W2
        ==> det(matrix(chart_jac (W1,L1 o phi1) (W2,L2 o phi2) x)) =
            det(matrix L2) * det(matrix(chart_jac (U1,phi1) (U2,phi2) x)) *
            det(matrix L1)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                `U1:A->bool`; `phi1:A->real^N`; `W1:A->bool`; `L1:real^N->real^N`;
                `U2:A->bool`; `phi2:A->real^N`; `W2:A->bool`; `L2:real^N->real^N`; `x:A`]
    SMT_ORI_MOD_JAC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `linear(chart_jac (U1:A->bool,phi1:A->real^N) (U2,phi2) x)` ASSUME_TAC THENL
   [MATCH_MP_TAC SMT_ORI_JAC_LINEAR THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[MATRIX_COMPOSE; LINEAR_COMPOSE; DET_MUL]);;

(* ------------------------------------------------------------------------- *)
(* M7.  The trivialization eps of the Jacobian sign cocycle                 *)
(* splits each chart domain U into the open parts D U phi s where the sign  *)
(* of the chart relative to the reference chart agrees with eps exactly     *)
(* when s holds; the charts (D U phi s, flip s o phi) form an oriented      *)
(* atlas compatible with the given one.                                      *)
(* ------------------------------------------------------------------------- *)

let SMT_ORIENTABLE = prove
 (`!(u:A->bool) (n:N->bool). SMT_ORIENTABLE_STATEMENT u n`,
  REWRITE_TAC[SMT_ORIENTABLE_STATEMENT; mfd_orientable] THEN
  MAP_EVERY X_GEN_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`]
    SMT_ORI_ZCOCYCLE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "coc") THEN
  MP_TAC(ISPECL [`top:A topology`;
                 `\c:(A->bool)#(A->real^N). if c IN atlas then FST c else {}`;
                 `\c c' (x:A). &0 < det(matrix(chart_jac (c:(A->bool)#(A->real^N)) c' x))`;
                 `chart_at (atlas:((A->bool)#(A->real^N))->bool)`] SMT_ZCOCYCLE_TRIVIAL) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [ASM_MESON_TAC[GEO_MANIFOLD_LOCALLY_PATH_CONNECTED]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `eps:A->bool` (LABEL_TAC "eps")) THEN
  ABBREV_TAC
   `D = \(U:A->bool) (phi:A->real^N) (s:bool).
          {x | x IN U /\
               ((eps x <=> &0 < det(matrix(chart_jac (U,phi) (chart_at atlas x) x))) <=> s)}` THEN
  SUBGOAL_THEN
   `!(U:A->bool) (phi:A->real^N) (s:bool).
        (U,phi) IN atlas
        ==> open_in top ((D:(A->bool)->(A->real^N)->bool->A->bool) U phi s) /\
            D U phi s SUBSET U`
  (LABEL_TAC "dom") THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN EXPAND_TAC "D" THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN SIMP_TAC[] THEN
    USE_THEN "eps" (MP_TAC o
      REWRITE_RULE[FST; ASSUME `(U:A->bool,phi:A->real^N) IN atlas`] o
      SPEC `(U:A->bool,phi:A->real^N)`) THEN
    BOOL_CASES_TAC `s:bool` THEN SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC
   `atlas' = {c | ?(U:A->bool) (phi:A->real^N) s.
                    (U,phi) IN atlas /\
                    c = ((D:(A->bool)->(A->real^N)->bool->A->bool) U phi s,
                         smt_ori_flip s o phi)}` THEN
  SUBGOAL_THEN
   `!(W:A->bool) (chi:A->real^N).
        (W,chi) IN atlas'
        ==> ?U phi L. (U,phi) IN atlas /\ open_in top W /\ W SUBSET U /\
                      linear L /\ (!y. L(L y) = y) /\ chi = L o phi`
  (LABEL_TAC "mem") THENL
   [REPEAT GEN_TAC THEN EXPAND_TAC "atlas'" THEN
    REWRITE_TAC[IN_ELIM_THM; PAIR_EQ] THEN
    DISCH_THEN(X_CHOOSE_THEN `U:A->bool` (X_CHOOSE_THEN `phi:A->real^N`
      (X_CHOOSE_THEN `s:bool` STRIP_ASSUME_TAC))) THEN
    MAP_EVERY EXISTS_TAC
     [`U:A->bool`; `phi:A->real^N`; `smt_ori_flip s:real^N->real^N`] THEN
    ASM_SIMP_TAC[SMT_ORI_FLIP];
    ALL_TAC] THEN
  EXISTS_TAC `atlas':((A->bool)#(A->real^N))->bool` THEN
  REPEAT CONJ_TAC THENL
   [(* an atlas *)
    MATCH_MP_TAC SMT_ORI_MOD_ATLAS THEN EXISTS_TAC `atlas:((A->bool)#(A->real^N))->bool` THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`]
      CHART_AT) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC
     [`(D:(A->bool)->(A->real^N)->bool->A->bool)
         (FST(chart_at atlas (x:A))) (SND(chart_at atlas x))
         (eps x <=> &0 < det(matrix(chart_jac (FST(chart_at atlas x),SND(chart_at atlas x))
                                              (chart_at atlas x) x)))`;
      `smt_ori_flip (eps x <=> &0 < det(matrix(chart_jac (FST(chart_at atlas (x:A)),
                                                          SND(chart_at atlas x))
                                                         (chart_at atlas x) x))) o
       SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) x)`] THEN
    CONJ_TAC THENL
     [EXPAND_TAC "atlas'" THEN REWRITE_TAC[IN_ELIM_THM; PAIR_EQ] THEN
      MAP_EVERY EXISTS_TAC
       [`FST(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A))`;
        `SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A))`;
        `(eps:A->bool) x <=>
         &0 < det(matrix(chart_jac (FST(chart_at (atlas:((A->bool)#(A->real^N))->bool) x),
                                    SND(chart_at atlas x))
                                   (chart_at atlas x) x))`] THEN
      ASM_REWRITE_TAC[PAIR];
      EXPAND_TAC "D" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[]];
    (* compatible with the given atlas *)
    MATCH_MP_TAC SMT_ORI_MOD_ATLAS THEN EXISTS_TAC `atlas:((A->bool)#(A->real^N))->bool` THEN
    ASM_REWRITE_TAC[IN_UNION] THEN CONJ_TAC THENL
     [MAP_EVERY X_GEN_TAC [`W:A->bool`; `chi:A->real^N`] THEN STRIP_TAC THENL
       [MAP_EVERY EXISTS_TAC [`W:A->bool`; `chi:A->real^N`; `\y:real^N. y`] THEN
        ASM_REWRITE_TAC[SUBSET_REFL; LINEAR_ID] THEN
        CONJ_TAC THENL
         [ASM_MESON_TAC[SMOOTH_MANIFOLD_ATLAS_CHART];
          REWRITE_TAC[FUN_EQ_THM; o_THM]];
        USE_THEN "mem" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      X_GEN_TAC `x:A` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`]
        CHART_AT) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      MAP_EVERY EXISTS_TAC
       [`FST(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A))`;
        `SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A))`] THEN
      ASM_REWRITE_TAC[PAIR]];
    ALL_TAC] THEN
  (* oriented *)
  REWRITE_TAC[mfd_oriented_atlas; FORALL_PAIR_THM; FST] THEN
  MAP_EVERY X_GEN_TAC [`W1:A->bool`; `chi1:A->real^N`; `W2:A->bool`; `chi2:A->real^N`;
                       `x:A`] THEN
  EXPAND_TAC "atlas'" THEN REWRITE_TAC[IN_ELIM_THM; PAIR_EQ; IN_INTER] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `U1:A->bool` (X_CHOOSE_THEN `phi1:A->real^N`
      (X_CHOOSE_THEN `s1:bool` STRIP_ASSUME_TAC)))
    (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `U2:A->bool` (X_CHOOSE_THEN `phi2:A->real^N`
        (X_CHOOSE_THEN `s2:bool` STRIP_ASSUME_TAC)))
      STRIP_ASSUME_TAC)) THEN
  SUBST_ALL_TAC(ASSUME
   `(W1:A->bool) = (D:(A->bool)->(A->real^N)->bool->A->bool) U1 phi1 s1`) THEN
  SUBST_ALL_TAC(ASSUME
   `(chi1:A->real^N) = smt_ori_flip (s1:bool) o (phi1:A->real^N)`) THEN
  SUBST_ALL_TAC(ASSUME
   `(W2:A->bool) = (D:(A->bool)->(A->real^N)->bool->A->bool) U2 phi2 s2`) THEN
  SUBST_ALL_TAC(ASSUME
   `(chi2:A->real^N) = smt_ori_flip (s2:bool) o (phi2:A->real^N)`) THEN
  USE_THEN "dom" (MP_TAC o SPECL [`U1:A->bool`; `phi1:A->real^N`; `s1:bool`]) THEN
  (ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC]) THEN
  USE_THEN "dom" (MP_TAC o SPECL [`U2:A->bool`; `phi2:A->real^N`; `s2:bool`]) THEN
  (ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC]) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `U1:A->bool`; `phi1:A->real^N`;
                 `(D:(A->bool)->(A->real^N)->bool->A->bool) U1 phi1 s1`;
                 `smt_ori_flip s1:real^N->real^N`;
                 `U2:A->bool`; `phi2:A->real^N`;
                 `(D:(A->bool)->(A->real^N)->bool->A->bool) U2 phi2 s2`;
                 `smt_ori_flip s2:real^N->real^N`; `x:A`] SMT_ORI_MOD_DET) THEN
  ASM_REWRITE_TAC[SMT_ORI_FLIP; IN_INTER] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `(x:A) IN U1 /\ x IN U2` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[SMOOTH_MANIFOLD_ATLAS_CHART; OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`]
    CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  (* the cocycle relation at x *)
  USE_THEN "coc" (MP_TAC o SPECL
    [`(U1:A->bool,phi1:A->real^N)`; `(U2:A->bool,phi2:A->real^N)`;
     `chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)`; `x:A`] o
    CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o REWRITE_RULE[smt_zcocycle]) THEN
  ASM_REWRITE_TAC[FST] THEN DISCH_THEN(LABEL_TAC "c3") THEN
  (* the signs at x *)
  SUBGOAL_THEN
   `((eps:A->bool) x <=> &0 < det(matrix(chart_jac (U1:A->bool,phi1:A->real^N)
                                                    (chart_at atlas x) x))) <=>
    s1`
  (LABEL_TAC "sg1") THENL
   [UNDISCH_TAC `(x:A) IN (D:(A->bool)->(A->real^N)->bool->A->bool) U1 phi1 s1` THEN
    EXPAND_TAC "D" THEN REWRITE_TAC[IN_ELIM_THM] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((eps:A->bool) x <=> &0 < det(matrix(chart_jac (U2:A->bool,phi2:A->real^N)
                                                    (chart_at atlas x) x))) <=>
    s2`
  (LABEL_TAC "sg2") THENL
   [UNDISCH_TAC `(x:A) IN (D:(A->bool)->(A->real^N)->bool->A->bool) U2 phi2 s2` THEN
    EXPAND_TAC "D" THEN REWRITE_TAC[IN_ELIM_THM] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(&0 < det(matrix(chart_jac (U1:A->bool,phi1:A->real^N) (U2,phi2) x))) <=> (s1 <=> s2)`
  MP_TAC THENL
   [USE_THEN "c3" MP_TAC THEN USE_THEN "sg1" MP_TAC THEN USE_THEN "sg2" MP_TAC THEN
    CONV_TAC TAUT;
    ALL_TAC] THEN
  MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                `U1:A->bool`; `phi1:A->real^N`; `U2:A->bool`; `phi2:A->real^N`; `x:A`]
    SMT_ORI_DET_NZ) THEN
  ASM_REWRITE_TAC[IN_INTER] THEN
  BOOL_CASES_TAC `s1:bool` THEN BOOL_CASES_TAC `s2:bool` THEN REWRITE_TAC[] THEN
  REAL_ARITH_TAC);;

