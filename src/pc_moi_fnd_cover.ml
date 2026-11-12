(* ========================================================================= *)
(* pc_moi_fnd_cover: Moise GTM 47, 24.6-24.8 (pp.177-178), for the           *)
(* foundations of the PL core.  Main theorem DOUBLE_COVER_OF_COCYCLE (the    *)
(* term MOI_FND_DOUBLE_COVER_OF_COCYCLE of pc_moi_fnd_stmt.ml).  Route: the  *)
(* double cover of a finite complex of dimension at most 3 given by a Z/2    *)
(* cocycle z is built abstractly on the vertices x bool (the two lifts of a  *)
(* vertex set t are the graphs of the two sheet functions on t, consistent   *)
(* by the cocycle relation) and re-realized in real^N (pc_moi_real,          *)
(* 7 <= dimindex(:N)); the projection is a covering map by a generic         *)
(* converse of the sheet lemmas of pc_moi_lt_cova; it is connected because   *)
(* z is no coboundary, and links, boundary and orientations lift along the   *)
(* covering.                                                                 *)
(* ========================================================================= *)

needs "src/pc_moi_fnd_stmt.ml";;
needs "src/pc_moi_fnd_m3a.ml";;
needs "src/pc_moi_real.ml";;
needs "src/pc_moi_lt_cova.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* A simplicial map q of finite complexes c' -> c that is injective on each  *)
(* simplex, with lifts of simplices unique through each point (two simplices *)
(* of c' with the same image that meet are equal) and through every point    *)
(* over a simplex, and onto, is a covering map (the converse of the sheet    *)
(* lemmas MOI_LCA_ of pc_moi_lt_cova).  The part of a simplex L over a       *)
(* simplex of c inside q L is a face of L (MOI_FCV_FACE_LIFT); q is          *)
(* injective on the closed star of each point (MOI_FCV_STAR_INJ) and maps    *)
(* its open star onto the open star of the image point                       *)
(* (MOI_FCV_OPEN_STAR_IMAGE); then                                           *)
(* PROPER_LOCAL_HOMEOMORPHISM_IMP_COVERING_MAP (paths.ml).                   *)
(* ------------------------------------------------------------------------- *)

let MOI_FCV_SC_SIMPLEX = prove
 (`!(c:(real^N->bool)->bool) s.
     simplicial_complex c /\ s IN c
     ==> polytope s /\ compact s /\ closed s /\ convex s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[simplicial_complex] THEN STRIP_TAC THEN
  SUBGOAL_THEN `polytope (s:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[SIMPLEX_IMP_POLYTOPE]; ALL_TAC] THEN
  ASM_SIMP_TAC[POLYTOPE_IMP_COMPACT; POLYTOPE_IMP_CONVEX; POLYTOPE_IMP_CLOSED]);;

let MOI_FCV_FACE_LIFT = prove
 (`!(c':(real^M->bool)->bool) (c:(real^N->bool)->bool) q L s.
     simplicial_complex c' /\ simplicial_complex c /\ simplicial_map_on c' c q /\
     L IN c' /\ (!x y. x IN L /\ y IN L /\ q x = q y ==> x = y) /\
     s IN c /\ s SUBSET IMAGE q L
     ==> {y | y IN L /\ q y IN s} IN c' /\
         IMAGE q {y | y IN L /\ q y IN s} = s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `IMAGE (q:real^M->real^N) L IN c /\
                ?l y. linear l /\ !x. x IN L ==> q x = l x + y`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_map_on]; ALL_TAC] THEN
  SUBGOAL_THEN `(s:real^N->bool) face_of IMAGE (q:real^M->real^N) L` ASSUME_TAC THENL
   [SUBGOAL_THEN `(s:real^N->bool) = s INTER IMAGE (q:real^M->real^N) L` SUBST1_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_MESON_TAC[simplicial_complex];
    ALL_TAC] THEN
  SUBGOAL_THEN `convex (L:real^M->bool) /\ convex (s:real^N->bool)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FCV_SC_SIMPLEX]; ALL_TAC] THEN
  CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
  SUBGOAL_THEN `{y | y IN L /\ (q:real^M->real^N) y IN s} face_of L` MP_TAC THENL
   [ALL_TAC; ASM_MESON_TAC[simplicial_complex]] THEN
  REWRITE_TAC[face_of] THEN REPEAT CONJ_TAC THENL
   [SET_TAC[];
    REWRITE_TAC[CONVEX_ALT; IN_ELIM_THM] THEN
    MAP_EVERY X_GEN_TAC [`a:real^M`; `b:real^M`; `u:real`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(&1 - u) % a + u % b IN (L:real^M->bool)` ASSUME_TAC THENL
     [ASM_MESON_TAC[CONVEX_ALT]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`q:real^M->real^N`; `l:real^M->real^N`; `y:real^N`; `L:real^M->bool`;
                   `a:real^M`; `b:real^M`; `u:real`] MOI_LCA_AFFINE_COMB) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    UNDISCH_TAC `convex (s:real^N->bool)` THEN REWRITE_TAC[CONVEX_ALT] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`a:real^M`; `b:real^M`; `x:real^M`] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(q:real^M->real^N) x IN segment(q a,q b)` ASSUME_TAC THENL
     [UNDISCH_TAC `(x:real^M) IN segment(a,b)` THEN REWRITE_TAC[IN_SEGMENT] THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `u:real` STRIP_ASSUME_TAC)) THEN
      CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      EXISTS_TAC `u:real` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC MOI_LCA_AFFINE_COMB THEN
      MAP_EVERY EXISTS_TAC [`l:real^M->real^N`; `y:real^N`; `L:real^M->bool`] THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `(s:real^N->bool) face_of IMAGE (q:real^M->real^N) L` THEN
    REWRITE_TAC[face_of] THEN
    DISCH_THEN(MP_TAC o SPECL [`(q:real^M->real^N) a`; `(q:real^M->real^N) b`;
                               `(q:real^M->real^N) x`] o CONJUNCT2 o CONJUNCT2) THEN
    ASM_SIMP_TAC[FUN_IN_IMAGE]]);;

let MOI_FCV_STAR_INJ = prove
 (`!(c':(real^M->bool)->bool) (c:(real^N->bool)->bool) q x y1 y2.
     simplicial_complex c' /\ simplicial_complex c /\ simplicial_map_on c' c q /\
     (!L. L IN c' ==> !x y. x IN L /\ y IN L /\ q x = q y ==> x = y) /\
     (!L1 L2. L1 IN c' /\ L2 IN c' /\ IMAGE q L1 = IMAGE q L2 /\ ~DISJOINT L1 L2
              ==> L1 = L2) /\
     y1 IN UNIONS {L | L IN c' /\ x IN L} /\ y2 IN UNIONS {L | L IN c' /\ x IN L} /\
     q y1 = q y2
     ==> y1 = y2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "inj")
   (CONJUNCTS_THEN2 (LABEL_TAC "uniq") (CONJUNCTS_THEN2
     (X_CHOOSE_THEN `L1:real^M->bool` STRIP_ASSUME_TAC)
     (CONJUNCTS_THEN2 (X_CHOOSE_THEN `L2:real^M->bool` STRIP_ASSUME_TAC)
        ASSUME_TAC))))))) THEN
  SUBGOAL_THEN `IMAGE (q:real^M->real^N) L1 IN c /\ IMAGE q L2 IN c` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_map_on]; ALL_TAC] THEN
  ABBREV_TAC `s3 = IMAGE (q:real^M->real^N) L1 INTER IMAGE q L2` THEN
  SUBGOAL_THEN `(s3:real^N->bool) IN c` ASSUME_TAC THENL
   [EXPAND_TAC "s3" THEN ASM_MESON_TAC[simplicial_complex]; ALL_TAC] THEN
  SUBGOAL_THEN `(!x y. x IN L1 /\ y IN L1 /\ (q:real^M->real^N) x = q y ==> x = y) /\
                (!x y. x IN L2 /\ y IN L2 /\ (q:real^M->real^N) x = q y ==> x = y)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN USE_THEN "inj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(s3:real^N->bool) SUBSET IMAGE (q:real^M->real^N) L1 /\
                s3 SUBSET IMAGE q L2 /\
                q x IN s3 /\ q y1 IN s3 /\ q y2 IN s3`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "s3" THEN REWRITE_TAC[IN_INTER; INTER_SUBSET] THEN
    ASM_MESON_TAC[FUN_IN_IMAGE];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c':(real^M->bool)->bool`; `c:(real^N->bool)->bool`; `q:real^M->real^N`;
                 `L1:real^M->bool`; `s3:real^N->bool`] MOI_FCV_FACE_LIFT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`c':(real^M->bool)->bool`; `c:(real^N->bool)->bool`; `q:real^M->real^N`;
                 `L2:real^M->bool`; `s3:real^N->bool`] MOI_FCV_FACE_LIFT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `{y | y IN L1 /\ (q:real^M->real^N) y IN s3} =
                {y | y IN L2 /\ q y IN s3}` ASSUME_TAC THENL
   [USE_THEN "uniq" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[DISJOINT; GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `x:real^M` THEN
    ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y1:real^M) IN {y | y IN L1 /\ (q:real^M->real^N) y IN s3} /\
                (y2:real^M) IN {y | y IN L1 /\ (q:real^M->real^N) y IN s3}`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ALL_TAC; FIRST_X_ASSUM SUBST1_TAC] THEN
    ASM_REWRITE_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  UNDISCH_TAC `(y1:real^M) IN {y | y IN L1 /\ (q:real^M->real^N) y IN s3}` THEN
  UNDISCH_TAC `(y2:real^M) IN {y | y IN L1 /\ (q:real^M->real^N) y IN s3}` THEN
  UNDISCH_TAC `(q:real^M->real^N) y1 = q y2` THEN
  UNDISCH_TAC `!x y. x IN L1 /\ y IN L1 /\ (q:real^M->real^N) x = q y ==> x = y` THEN
  REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[]);;

let MOI_FCV_OPEN_STAR_IMAGE = prove
 (`!(c':(real^M->bool)->bool) (c:(real^N->bool)->bool) q x.
     simplicial_complex c' /\ simplicial_complex c /\ simplicial_map_on c' c q /\
     (!L. L IN c' ==> !x y. x IN L /\ y IN L /\ q x = q y ==> x = y) /\
     (!L1 L2. L1 IN c' /\ L2 IN c' /\ IMAGE q L1 = IMAGE q L2 /\ ~DISJOINT L1 L2
              ==> L1 = L2) /\
     (!y s. y IN UNIONS c' /\ s IN c /\ q y IN s
            ==> ?L. L IN c' /\ IMAGE q L = s /\ y IN L) /\
     x IN UNIONS c'
     ==> IMAGE q (UNIONS c' DIFF UNIONS {L | L IN c' /\ ~(x IN L)}) =
         UNIONS c DIFF UNIONS {s | s IN c /\ ~(q x IN s)}`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "inj")
   (CONJUNCTS_THEN2 (LABEL_TAC "uniq") (CONJUNCTS_THEN2 (LABEL_TAC "pl")
      ASSUME_TAC)))))) THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `z:real^N` THEN
  REWRITE_TAC[IN_IMAGE; IN_DIFF; IN_UNIONS; IN_ELIM_THM] THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `y:real^M` (CONJUNCTS_THEN2 SUBST1_TAC
      (CONJUNCTS_THEN2 (X_CHOOSE_THEN `L0:real^M->bool` STRIP_ASSUME_TAC)
                       ASSUME_TAC))) THEN
    CONJ_TAC THENL
     [EXISTS_TAC `IMAGE (q:real^M->real^N) L0` THEN
      ASM_MESON_TAC[simplicial_map_on; FUN_IN_IMAGE];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
    USE_THEN "pl" (MP_TAC o SPECL [`y:real^M`; `s:real^N->bool`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[IN_UNIONS] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `L:real^M->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(x:real^M) IN L` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `~((q:real^M->real^N) x IN s)` THEN EXPAND_TAC "s" THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `s0:real^N->bool` STRIP_ASSUME_TAC)
    (LABEL_TAC "nos")) THEN
  SUBGOAL_THEN `(q:real^M->real^N) x IN s0` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  USE_THEN "pl" (MP_TAC o SPECL [`x:real^M`; `s0:real^N->bool`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `L:real^M->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `?y:real^M. y IN L /\ (q:real^M->real^N) y = z` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(z:real^N) IN s0` THEN EXPAND_TAC "s0" THEN
    REWRITE_TAC[IN_IMAGE] THEN MESON_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `y:real^M` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `L':real^M->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `IMAGE (q:real^M->real^N) L IN c /\ IMAGE q L' IN c` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_map_on]; ALL_TAC] THEN
  SUBGOAL_THEN `(q:real^M->real^N) x IN IMAGE q L'` ASSUME_TAC THENL
   [SUBGOAL_THEN `(z:real^N) IN IMAGE (q:real^M->real^N) L'` ASSUME_TAC THENL
     [EXPAND_TAC "z" THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    USE_THEN "nos" MP_TAC THEN REWRITE_TAC[NOT_EXISTS_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `IMAGE (q:real^M->real^N) L'`) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `s2 = IMAGE (q:real^M->real^N) L INTER IMAGE q L'` THEN
  SUBGOAL_THEN `(s2:real^N->bool) IN c` ASSUME_TAC THENL
   [EXPAND_TAC "s2" THEN ASM_MESON_TAC[simplicial_complex]; ALL_TAC] THEN
  SUBGOAL_THEN `(!x y. x IN L /\ y IN L /\ (q:real^M->real^N) x = q y ==> x = y) /\
                (!x y. x IN L' /\ y IN L' /\ (q:real^M->real^N) x = q y ==> x = y)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN USE_THEN "inj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(s2:real^N->bool) SUBSET IMAGE (q:real^M->real^N) L /\
                s2 SUBSET IMAGE q L' /\ q x IN s2 /\ q y IN s2`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "s2" THEN REWRITE_TAC[IN_INTER; INTER_SUBSET] THEN
    ASM_MESON_TAC[FUN_IN_IMAGE];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c':(real^M->bool)->bool`; `c:(real^N->bool)->bool`; `q:real^M->real^N`;
                 `L:real^M->bool`; `s2:real^N->bool`] MOI_FCV_FACE_LIFT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`c':(real^M->bool)->bool`; `c:(real^N->bool)->bool`; `q:real^M->real^N`;
                 `L':real^M->bool`; `s2:real^N->bool`] MOI_FCV_FACE_LIFT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `{w | w IN L /\ (q:real^M->real^N) w IN s2} =
                {w | w IN L' /\ q w IN s2}` MP_TAC THENL
   [USE_THEN "uniq" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[DISJOINT; GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `y:real^M` THEN
    ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM];
    ALL_TAC] THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN DISCH_THEN(MP_TAC o SPEC `x:real^M`) THEN
  ASM_REWRITE_TAC[]);;

let MOI_FCV_COVERING_FROM_SHEETS = prove
 (`!(c':(real^M->bool)->bool) (c:(real^N->bool)->bool) q.
     simplicial_complex c' /\ simplicial_complex c /\ simplicial_map_on c' c q /\
     (!L. L IN c' ==> !x y. x IN L /\ y IN L /\ q x = q y ==> x = y) /\
     (!L1 L2. L1 IN c' /\ L2 IN c' /\ IMAGE q L1 = IMAGE q L2 /\ ~DISJOINT L1 L2
              ==> L1 = L2) /\
     (!y s. y IN UNIONS c' /\ s IN c /\ q y IN s
            ==> ?L. L IN c' /\ IMAGE q L = s /\ y IN L) /\
     IMAGE q (UNIONS c') = UNIONS c
     ==> covering_space (UNIONS c',q) (UNIONS c)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `FINITE (c':(real^M->bool)->bool) /\ FINITE (c:(real^N->bool)->bool)`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_complex]; ALL_TAC] THEN
  SUBGOAL_THEN `(q:real^M->real^N) continuous_on UNIONS c'` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`q:real^M->real^N`; `c':(real^M->bool)->bool`]
      MOI_REAL_PIECEWISE_AFFINE_UNIONS) THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `L:real^M->bool` THEN DISCH_TAC THEN
    CONJ_TAC THENL [ASM_MESON_TAC[MOI_FCV_SC_SIMPLEX]; ASM_MESON_TAC[simplicial_map_on]];
    ALL_TAC] THEN
  SUBGOAL_THEN `compact (UNIONS c':real^M->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC COMPACT_UNIONS THEN ASM_MESON_TAC[MOI_FCV_SC_SIMPLEX]; ALL_TAC] THEN
  MATCH_MP_TAC PROPER_LOCAL_HOMEOMORPHISM_IMP_COVERING_MAP THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `k:real^N->bool` THEN STRIP_TAC THEN
    MATCH_MP_TAC PROPER_MAP_FROM_COMPACT THEN
    EXISTS_TAC `UNIONS c:real^N->bool` THEN ASM_REWRITE_TAC[SUBSET_REFL] THEN
    MATCH_MP_TAC CLOSED_SUBSET THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED];
    ALL_TAC] THEN
  X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
  ABBREV_TAC `St = UNIONS {L | L IN c' /\ (x:real^M) IN L}` THEN
  SUBGOAL_THEN `compact (St:real^M->bool) /\ St SUBSET UNIONS c'` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "St" THEN CONJ_TAC THENL [ALL_TAC; SET_TAC[]] THEN
    MATCH_MP_TAC COMPACT_UNIONS THEN CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `c':(real^M->bool)->bool` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[MOI_FCV_SC_SIMPLEX]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`St:real^M->bool`; `q:real^M->real^N`; `IMAGE (q:real^M->real^N) St`]
    HOMEOMORPHISM_COMPACT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET]; ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`y1:real^M`; `y2:real^M`] THEN STRIP_TAC THEN
    MATCH_MP_TAC MOI_FCV_STAR_INJ THEN
    MAP_EVERY EXISTS_TAC [`c':(real^M->bool)->bool`; `c:(real^N->bool)->bool`;
                          `q:real^M->real^N`; `x:real^M`] THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN(X_CHOOSE_TAC `q':real^N->real^M`)] THEN
  MAP_EVERY EXISTS_TAC
   [`UNIONS c' DIFF UNIONS {L | L IN c' /\ ~((x:real^M) IN L)}`;
    `UNIONS c DIFF UNIONS {s | s IN c /\ ~((q:real^M->real^N) x IN s)}`;
    `q':real^N->real^M`] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[IN_DIFF; IN_UNIONS; IN_ELIM_THM] THEN ASM_MESON_TAC[IN_UNIONS];
    MATCH_MP_TAC OPEN_IN_DIFF THEN REWRITE_TAC[OPEN_IN_REFL] THEN
    MATCH_MP_TAC CLOSED_SUBSET THEN CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC CLOSED_UNIONS THEN CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `c':(real^M->bool)->bool` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[MOI_FCV_SC_SIMPLEX]];
    MATCH_MP_TAC OPEN_IN_DIFF THEN REWRITE_TAC[OPEN_IN_REFL] THEN
    MATCH_MP_TAC CLOSED_SUBSET THEN CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC CLOSED_UNIONS THEN CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `c:(real^N->bool)->bool` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[MOI_FCV_SC_SIMPLEX]];
    ALL_TAC] THEN
  SUBGOAL_THEN `UNIONS c' DIFF UNIONS {L | L IN c' /\ ~((x:real^M) IN L)} SUBSET St`
  ASSUME_TAC THENL
   [EXPAND_TAC "St" THEN REWRITE_TAC[SUBSET; IN_DIFF; IN_UNIONS; IN_ELIM_THM] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c':(real^M->bool)->bool`; `c:(real^N->bool)->bool`; `q:real^M->real^N`;
                 `x:real^M`] MOI_FCV_OPEN_STAR_IMAGE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(ASSUME_TAC o SYM)] THEN
  MATCH_MP_TAC HOMEOMORPHISM_OF_SUBSETS THEN
  MAP_EVERY EXISTS_TAC [`St:real^M->bool`; `IMAGE (q:real^M->real^N) St`] THEN
  ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[IMAGE_SUBSET]);;

(* ------------------------------------------------------------------------- *)
(* The abstract double cover.  Edges are vertex pairs with convex hull {u,v} *)
(* IN z; on a vertex set t of c the cocycle condition on the triangles gives *)
(* zz(u,w) = zz(u,v) + zz(v,w) mod 2 (MOI_FCV_COCYCLE_REL).  The sheet       *)
(* function based at (v0,b) is moi_fcv_sheet z v0 b, and the lifts of t are  *)
(* the graphs of the sheet functions on t (moi_fcv_lifts, on the vertex type *)
(* real^N # bool); a lift is determined by its value at any vertex of t      *)
(* (MOI_FCV_LIFT_REBASE). The lifts form a finite abstract complex with at   *)
(* most 4 vertices per simplex, so it is realized in real^N when 7 <=        *)
(* dimindex(:N) (MOI_FCV_REALIZES, by ABSTRACT_REALIZES_EXISTS of            *)
(* pc_moi_real).                                                             *)
(* ------------------------------------------------------------------------- *)

let moi_fcv_sheet = new_definition
 `moi_fcv_sheet (z:(real^N->bool)->bool) (v0:real^N) (b:bool) (v:real^N) =
    if convex hull {v0,v} IN z then ~b else b`;;

let moi_fcv_lifts = new_definition
 `moi_fcv_lifts (c:(real^N->bool)->bool) (z:(real^N->bool)->bool) =
    {IMAGE (\v. v,moi_fcv_sheet z v0 b v) t | t,v0,b |
       t IN moi_real_vertex_sets c /\ v0 IN t}`;;

let MOI_FCV_PARITY3 = prove
 (`!(z:A->bool) e1 e2 e3.
     ~(e1 = e2) /\ ~(e1 = e3) /\ ~(e2 = e3) /\ EVEN (CARD ({e1,e2,e3} INTER z))
     ==> (e3 IN z <=> ~(e1 IN z <=> e2 IN z))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `EVEN (CARD ({e1:A,e2,e3} INTER z))` THEN
  REWRITE_TAC[INSERT_INTER; INTER_EMPTY] THEN
  MAP_EVERY ASM_CASES_TAC [`(e1:A) IN z`; `(e2:A) IN z`; `(e3:A) IN z`] THEN
  ASM_REWRITE_TAC[] THEN SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN
  ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY; EVEN]);;

let MOI_FCV_EDGE_NOT_SING = prove
 (`!(c:(real^N->bool)->bool) z u.
     z2_cocycle c z ==> ~(convex hull {u,u} IN z)`,
  REWRITE_TAC[z2_cocycle; INSERT_AC; CONVEX_HULL_SING] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o SPEC `{u:real^N}` o CONJUNCT1) THEN
  REWRITE_TAC[AFF_DIM_SING] THEN CONV_TAC INT_REDUCE_CONV THEN MESON_TAC[]);;

let MOI_FCV_PAIR_SUBSET3 = prove
 (`!(u:A) v w c0.
     c0 SUBSET {u,v,w} /\ c0 HAS_SIZE 2
     ==> c0 = {u,v} \/ c0 = {v,w} \/ c0 = {u,w}`,
  REPEAT GEN_TAC THEN CONV_TAC(LAND_CONV(RAND_CONV HAS_SIZE_CONV)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (X_CHOOSE_THEN `a:A` (X_CHOOSE_THEN `a':A`
    (CONJUNCTS_THEN2 MP_TAC SUBST1_TAC)))) THEN
  REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET; IN_INSERT; NOT_IN_EMPTY] THEN
  DISCH_TAC THEN STRIP_TAC THEN REPEAT(FIRST_X_ASSUM SUBST_ALL_TAC) THEN
  ASM_REWRITE_TAC[INSERT_AC] THEN ASM_MESON_TAC[]);;

let MOI_FCV_TRIANGLE_EDGES = prove
 (`!(c:(real^N->bool)->bool) z u v w.
     simplicial_complex c /\ z2_cocycle c z /\
     ~affine_dependent {u,v,w} /\ convex hull {u,v,w} IN c /\
     ~(u = v) /\ ~(u = w) /\ ~(v = w)
     ==> (convex hull {u,w} IN z <=>
          ~(convex hull {u,v} IN z <=> convex hull {v,w} IN z))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!a b:real^N. a IN {u,v,w} /\ b IN {u,v,w} ==> ~affine_dependent {a,b}`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC AFFINE_INDEPENDENT_SUBSET THEN
    EXISTS_TAC `{u:real^N,v,w}` THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(convex hull {u:real^N,v} = convex hull {v,w}) /\
                ~(convex hull {u:real^N,v} = convex hull {u,w}) /\
                ~(convex hull {v:real^N,w} = convex hull {u,w})`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN DISCH_TAC THENL
     [SUBGOAL_THEN `{u:real^N,v} = {v,w}` MP_TAC THENL
       [ALL_TAC; ASM SET_TAC[]];
      SUBGOAL_THEN `{u:real^N,v} = {u,w}` MP_TAC THENL
       [ALL_TAC; ASM SET_TAC[]];
      SUBGOAL_THEN `{v:real^N,w} = {u,w}` MP_TAC THENL
       [ALL_TAC; ASM SET_TAC[]]] THEN
    MATCH_MP_TAC SIMPLEX_VERTICES_UNIQUE THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_INSERT];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_FCV_PARITY3 THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `aff_dim (convex hull {u:real^N,v,w}) = &2` ASSUME_TAC THENL
   [ASM_SIMP_TAC[AFF_DIM_CONVEX_HULL; AFF_DIM_AFFINE_INDEPENDENT] THEN
    SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN
    ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN CONV_TAC NUM_REDUCE_CONV THEN
    CONV_TAC INT_REDUCE_CONV;
    ALL_TAC] THEN
  UNDISCH_TAC `z2_cocycle (c:(real^N->bool)->bool) z` THEN REWRITE_TAC[z2_cocycle] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "zc")
    (MP_TAC o SPEC `convex hull {u:real^N,v,w}`)) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(MESON[] `(s:(real^N->bool)->bool) = t ==> EVEN (CARD s) ==> EVEN (CARD t)`) THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `e:real^N->bool` THEN
  REWRITE_TAC[IN_ELIM_THM; IN_INTER; IN_INSERT; NOT_IN_EMPTY] THEN EQ_TAC THENL
   [ALL_TAC;
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HULL_MONO THEN SET_TAC[]] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(e:real^N->bool) IN c /\ aff_dim e = &1` STRIP_ASSUME_TAC THENL
   [USE_THEN "zc" (MP_TAC o SPEC `e:real^N->bool`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(e:real^N->bool) face_of convex hull {u,v,w}` MP_TAC THENL
   [SUBGOAL_THEN `(e:real^N->bool) = e INTER convex hull {u,v,w}` SUBST1_TAC THENL
     [ASM SET_TAC[]; ASM_MESON_TAC[simplicial_complex]];
    ALL_TAC] THEN
  ASM_SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `c0:real^N->bool` (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC)) THEN
  SUBGOAL_THEN `(c0:real^N->bool) HAS_SIZE 2` ASSUME_TAC THENL
   [SUBGOAL_THEN `~affine_dependent (c0:real^N->bool)` ASSUME_TAC THENL
     [MATCH_MP_TAC AFFINE_INDEPENDENT_SUBSET THEN EXISTS_TAC `{u:real^N,v,w}` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[HAS_SIZE] THEN ASM_SIMP_TAC[AFFINE_INDEPENDENT_IMP_FINITE] THEN
    UNDISCH_TAC `aff_dim (convex hull (c0:real^N->bool)) = &1` THEN
    ASM_SIMP_TAC[AFF_DIM_CONVEX_HULL; AFF_DIM_AFFINE_INDEPENDENT] THEN
    REWRITE_TAC[GSYM INT_OF_NUM_EQ] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`u:real^N`; `v:real^N`; `w:real^N`; `c0:real^N->bool`]
    MOI_FCV_PAIR_SUBSET3) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[]);;

let MOI_FCV_COCYCLE_REL = prove
 (`!(c:(real^N->bool)->bool) z t u v w.
     simplicial_complex c /\ z2_cocycle c z /\ t IN moi_real_vertex_sets c /\
     u IN t /\ v IN t /\ w IN t
     ==> (convex hull {u,w} IN z <=>
          ~(convex hull {u,v} IN z <=> convex hull {v,w} IN z))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!a:real^N. ~(convex hull {a,a} IN z)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FCV_EDGE_NOT_SING]; ALL_TAC] THEN
  ASM_CASES_TAC `u:real^N = v` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `v:real^N = w` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `u:real^N = w` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[INSERT_AC];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_FCV_TRIANGLE_EDGES THEN EXISTS_TAC `c:(real^N->bool)->bool` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `{u:real^N,v,w} IN moi_real_vertex_sets c` MP_TAC THENL
   [MP_TAC(ISPEC `c:(real^N->bool)->bool` MOI_REAL_VERTEX_SETS_ABSTRACT_COMPLEX) THEN
    ASM_REWRITE_TAC[abstract_complex] THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN EXISTS_TAC `t:real^N->bool` THEN
    ASM_REWRITE_TAC[NOT_INSERT_EMPTY] THEN ASM SET_TAC[];
    SIMP_TAC[MOI_REAL_IN_VERTEX_SETS]]);;

let MOI_FCV_SHEET_REBASE = prove
 (`!(c:(real^N->bool)->bool) z t v0 v1 b v.
     simplicial_complex c /\ z2_cocycle c z /\ t IN moi_real_vertex_sets c /\
     v0 IN t /\ v1 IN t /\ v IN t
     ==> moi_fcv_sheet z v1 (moi_fcv_sheet z v0 b v1) v = moi_fcv_sheet z v0 b v`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[moi_fcv_sheet] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `z:(real^N->bool)->bool`; `t:real^N->bool`;
                 `v0:real^N`; `v1:real^N`; `v:real^N`] MOI_FCV_COCYCLE_REL) THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY ASM_CASES_TAC [`convex hull {v0:real^N,v1} IN z`;
                           `convex hull {v1:real^N,v} IN z`] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[]);;

let MOI_FCV_LIFT_REBASE = prove
 (`!(c:(real^N->bool)->bool) z t t' v0 v1 b.
     simplicial_complex c /\ z2_cocycle c z /\ t IN moi_real_vertex_sets c /\
     v0 IN t /\ v1 IN t /\ t' SUBSET t
     ==> IMAGE (\v. v,moi_fcv_sheet z v0 b v) t' =
         IMAGE (\v. v,moi_fcv_sheet z v1 (moi_fcv_sheet z v0 b v1) v) t'`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(SET_RULE `(!x:real^N. x IN s ==> (f:real^N->real^N#bool) x = g x)
                           ==> IMAGE f s = IMAGE g s`) THEN
  X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN REWRITE_TAC[PAIR_EQ] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOI_FCV_SHEET_REBASE THEN
  MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `t:real^N->bool`] THEN
  ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

let MOI_FCV_IN_LIFTS = prove
 (`!(c:(real^N->bool)->bool) z s.
     s IN moi_fcv_lifts c z <=>
     ?t v0 b. t IN moi_real_vertex_sets c /\ v0 IN t /\
              s = IMAGE (\v. v,moi_fcv_sheet z v0 b v) t`,
  REWRITE_TAC[moi_fcv_lifts; IN_ELIM_THM] THEN MESON_TAC[]);;

let MOI_FCV_GRAPH_FST = prove
 (`!(f:A->B) t. IMAGE FST (IMAGE (\v. v,f v) t) = t`,
  REWRITE_TAC[GSYM IMAGE_o; o_DEF; IMAGE_ID]);;

let MOI_FCV_GRAPH_FST_INJ = prove
 (`!(f:A->B) t x y.
     x IN IMAGE (\v. v,f v) t /\ y IN IMAGE (\v. v,f v) t /\ FST x = FST y
     ==> x = y`,
  REWRITE_TAC[IN_IMAGE] THEN MESON_TAC[FST]);;

let MOI_FCV_GRAPH_SUBSET = prove
 (`!(f:A->B) t s'.
     s' SUBSET IMAGE (\v. v,f v) t
     ==> s' = IMAGE (\v. v,f v) (IMAGE FST s') /\ IMAGE FST s' SUBSET t`,
  REWRITE_TAC[SUBSET; EXTENSION; IN_IMAGE; FORALL_PAIR_THM; EXISTS_PAIR_THM;
              PAIR_EQ] THEN
  MESON_TAC[]);;

let MOI_FCV_LIFTS_ABSTRACT = prove
 (`!(c:(real^N->bool)->bool) z.
     simplicial_complex c /\ z2_cocycle c z ==> abstract_complex (moi_fcv_lifts c z)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[abstract_complex; MOI_FCV_IN_LIFTS] THEN
  CONJ_TAC THENL
   [REPEAT GEN_TAC THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` (X_CHOOSE_THEN `v0:real^N`
      (X_CHOOSE_THEN `b:bool` STRIP_ASSUME_TAC))) THEN
    UNDISCH_TAC `(t:real^N->bool) IN moi_real_vertex_sets c` THEN
    REWRITE_TAC[MOI_REAL_IN_VERTEX_SETS] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[FINITE_IMAGE; AFFINE_INDEPENDENT_IMP_FINITE; IMAGE_EQ_EMPTY];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`s:real^N#bool->bool`; `s':real^N#bool->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `t:real^N->bool` (X_CHOOSE_THEN `v0:real^N`
      (X_CHOOSE_THEN `b:bool` STRIP_ASSUME_TAC))) STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`moi_fcv_sheet z (v0:real^N) b`; `t:real^N->bool`; `s':real^N#bool->bool`]
    MOI_FCV_GRAPH_SUBSET) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; STRIP_TAC] THEN
  ABBREV_TAC `t' = IMAGE FST (s':real^N#bool->bool)` THEN
  SUBGOAL_THEN `~(t':real^N->bool = {})` ASSUME_TAC THENL
   [EXPAND_TAC "t'" THEN ASM_REWRITE_TAC[IMAGE_EQ_EMPTY]; ALL_TAC] THEN
  SUBGOAL_THEN `(t':real^N->bool) IN moi_real_vertex_sets c` ASSUME_TAC THENL
   [MP_TAC(ISPEC `c:(real^N->bool)->bool` MOI_REAL_VERTEX_SETS_ABSTRACT_COMPLEX) THEN
    ASM_REWRITE_TAC[abstract_complex] THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN EXISTS_TAC `t:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `v1:real^N` o REWRITE_RULE[GSYM MEMBER_NOT_EMPTY]) THEN
  MAP_EVERY EXISTS_TAC [`t':real^N->bool`; `v1:real^N`;
                        `moi_fcv_sheet z (v0:real^N) b v1`] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `IMAGE (\v. v,moi_fcv_sheet z (v0:real^N) b v) t'` THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC MOI_FCV_LIFT_REBASE THEN
  MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `t:real^N->bool`] THEN
  ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

let MOI_FCV_LIFTS_FINITE = prove
 (`!(c:(real^N->bool)->bool) z.
     simplicial_complex c ==> FINITE (moi_fcv_lifts c z)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `{s | s SUBSET (UNIONS (moi_real_vertex_sets (c:(real^N->bool)->bool)))
                            CROSS (:bool)}` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_POWERSET THEN MATCH_MP_TAC FINITE_CROSS THEN
    REWRITE_TAC[FINITE_BOOL; FINITE_UNIONS] THEN CONJ_TAC THENL
     [MATCH_MP_TAC MOI_REAL_VERTEX_SETS_FINITE THEN ASM_MESON_TAC[simplicial_complex];
      SIMP_TAC[MOI_REAL_IN_VERTEX_SETS; AFFINE_INDEPENDENT_IMP_FINITE]];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM; MOI_FCV_IN_LIFTS] THEN
  X_GEN_TAC `s:real^N#bool->bool` THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` (X_CHOOSE_THEN `v0:real^N`
    (X_CHOOSE_THEN `b:bool` STRIP_ASSUME_TAC))) THEN
  ASM_REWRITE_TAC[FORALL_IN_IMAGE; IN_CROSS; IN_UNIV; IN_UNIONS] THEN
  ASM_MESON_TAC[]);;

let MOI_FCV_LIFTS_CARD = prove
 (`!(c:(real^N->bool)->bool) z.
     (!s. s IN c ==> aff_dim s <= &3)
     ==> !s. s IN moi_fcv_lifts c z ==> CARD s <= 3 + 1`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[MOI_FCV_IN_LIFTS] THEN
  X_GEN_TAC `s:real^N#bool->bool` THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` (X_CHOOSE_THEN `v0:real^N`
    (X_CHOOSE_THEN `b:bool` STRIP_ASSUME_TAC))) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `FINITE (t:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_REAL_IN_VERTEX_SETS; AFFINE_INDEPENDENT_IMP_FINITE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`\v:real^N. v,moi_fcv_sheet z v0 b v`; `t:real^N->bool`]
    CARD_IMAGE_INJ) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[PAIR_EQ] THEN MESON_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `3`] MOI_REAL_VERTEX_SETS_CARD) THEN
  ASM_SIMP_TAC[]);;

let MOI_FCV_REALIZES = prove
 (`!(c:(real^N->bool)->bool) z.
     7 <= dimindex(:N) /\ simplicial_complex c /\ z2_cocycle c z /\
     (!s. s IN c ==> aff_dim s <= &3)
     ==> ?f:real^N#bool->real^N. abstract_realizes f (moi_fcv_lifts c z)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC ABSTRACT_REALIZES_EXISTS THEN
  EXISTS_TAC `3` THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MOI_FCV_LIFTS_FINITE THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOI_FCV_LIFTS_ABSTRACT THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOI_FCV_LIFTS_CARD THEN ASM_REWRITE_TAC[];
    ASM_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The realized double cover.  With f realizing the lifts in real^N and q    *)
(* simplexwise affine with q (f (v,b)) = v (both from pc_moi_real), each     *)
(* simplex of c' = abstract_realization f (lifts) over a vertex set t maps   *)
(* onto convex hull t with an affine inverse (MOI_FCV_LIFT_PROPS); q is      *)
(* simplicial, injective on simplices, lifts are unique where they meet      *)
(* (MOI_FCV_LIFTS_MEET, rebasing at a common vertex) and exist through every *)
(* point (MOI_FCV_POINT_LIFT), and q is onto, so q is a covering map         *)
(* (MOI_FCV_COVERING).                                                       *)
(* ------------------------------------------------------------------------- *)

let MOI_FCV_IN_REALIZATION = prove
 (`!(f:A->real^N) k L.
     L IN abstract_realization f k <=>
     L = {} \/ ?s. s IN k /\ L = convex hull (IMAGE f s)`,
  REWRITE_TAC[abstract_realization; IN_INSERT; IN_ELIM_THM] THEN MESON_TAC[]);;

let MOI_FCV_LIFT_PROPS = prove
 (`!(c:(real^N->bool)->bool) z (f:real^N#bool->real^N) (q:real^N->real^N) t v0 b.
     simplicial_complex c /\ z2_cocycle c z /\
     abstract_realizes f (moi_fcv_lifts c z) /\
     (!s. s IN moi_fcv_lifts c z
          ==> ?l y. linear l /\ (!w. w IN s ==> l (f w) + y = FST w) /\
                    (!x. x IN convex hull (IMAGE f s) ==> q x = l x + y)) /\
     t IN moi_real_vertex_sets c /\ v0 IN t
     ==> IMAGE (\v. v,moi_fcv_sheet z v0 b v) t IN moi_fcv_lifts c z /\
         IMAGE q (convex hull (IMAGE f (IMAGE (\v. v,moi_fcv_sheet z v0 b v) t))) =
         convex hull t /\
         (?l y. linear l /\
                !x. x IN convex hull (IMAGE f (IMAGE (\v. v,moi_fcv_sheet z v0 b v) t))
                    ==> q x = l x + y) /\
         (?l' y'. linear l' /\
                  (!x. x IN convex hull (IMAGE f (IMAGE (\v. v,moi_fcv_sheet z v0 b v) t))
                       ==> l' (q x) + y' = x) /\
                  (!v. v IN t ==> l' v + y' = f (v,moi_fcv_sheet z v0 b v)))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "aff")
      STRIP_ASSUME_TAC)))) THEN
  ABBREV_TAC `s = IMAGE (\v. v,moi_fcv_sheet z (v0:real^N) b v) t` THEN
  SUBGOAL_THEN `(s:real^N#bool->bool) IN moi_fcv_lifts c z` ASSUME_TAC THENL
   [REWRITE_TAC[MOI_FCV_IN_LIFTS] THEN
    MAP_EVERY EXISTS_TAC [`t:real^N->bool`; `v0:real^N`; `b:bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE FST (s:real^N#bool->bool) = t` ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN REWRITE_TAC[MOI_FCV_GRAPH_FST]; ALL_TAC] THEN
  SUBGOAL_THEN `~affine_dependent (t:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_REAL_IN_VERTEX_SETS]; ALL_TAC] THEN
  USE_THEN "aff" (MP_TAC o SPEC `s:real^N#bool->bool`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `l:real^N->real^N` (X_CHOOSE_THEN `y:real^N`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`FST:real^N#bool->real^N`; `f:real^N#bool->real^N`;
                 `s:real^N#bool->bool`] MOI_REAL_AFFINE_EXTEND) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN EXPAND_TAC "s" THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
    MATCH_MP_TAC MOI_FCV_GRAPH_FST_INJ THEN
    MAP_EVERY EXISTS_TAC [`moi_fcv_sheet z (v0:real^N) b`; `t:real^N->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `l':real^N->real^N` (X_CHOOSE_THEN `y':real^N`
    STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN `convex hull t = convex hull (IMAGE FST (s:real^N#bool->bool))`
    SUBST1_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC MOI_REAL_IMAGE_SIMPLEX THEN
    MAP_EVERY EXISTS_TAC [`l:real^N->real^N`; `y:real^N`] THEN ASM_REWRITE_TAC[];
    MAP_EVERY EXISTS_TAC [`l:real^N->real^N`; `y:real^N`] THEN ASM_REWRITE_TAC[];
    MAP_EVERY EXISTS_TAC [`l':real^N->real^N`; `y':real^N`] THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`f:real^N#bool->real^N`; `FST:real^N#bool->real^N`;
                     `q:real^N->real^N`; `\x:real^N. (l':real^N->real^N) x + y'`;
                     `l:real^N->real^N`; `y:real^N`; `l':real^N->real^N`; `y':real^N`;
                     `s:real^N#bool->bool`] MOI_REAL_AFFINE_INVERSE_ON_SIMPLEX) THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[];
      X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `(v:real^N),moi_fcv_sheet z (v0:real^N) b v` o
        check (fun th -> try fst(dest_var(fst(dest_forall(concl th)))) = "v"
                         with Failure _ -> false)) THEN
      ANTS_TAC THENL
       [EXPAND_TAC "s" THEN REWRITE_TAC[IN_IMAGE] THEN ASM_MESON_TAC[];
        REWRITE_TAC[FST]]]]);;

let MOI_FCV_SIMPLICIAL_MAP = prove
 (`!(c:(real^N->bool)->bool) z (f:real^N#bool->real^N) (q:real^N->real^N).
     simplicial_complex c /\ z2_cocycle c z /\
     abstract_realizes f (moi_fcv_lifts c z) /\
     (!s. s IN moi_fcv_lifts c z
          ==> ?l y. linear l /\ (!w. w IN s ==> l (f w) + y = FST w) /\
                    (!x. x IN convex hull (IMAGE f s) ==> q x = l x + y)) /\
     {} IN c
     ==> simplicial_map_on (abstract_realization f (moi_fcv_lifts c z)) c q`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "aff")
      ASSUME_TAC)))) THEN
  REWRITE_TAC[simplicial_map_on; MOI_FCV_IN_REALIZATION] THEN
  X_GEN_TAC `L:real^N->bool` THEN STRIP_TAC THENL
   [ASM_REWRITE_TAC[IMAGE_CLAUSES; NOT_IN_EMPTY] THEN MESON_TAC[LINEAR_ZERO];
    ALL_TAC] THEN
  UNDISCH_TAC `(s:real^N#bool->bool) IN moi_fcv_lifts (c:(real^N->bool)->bool) z` THEN
  REWRITE_TAC[MOI_FCV_IN_LIFTS] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` (X_CHOOSE_THEN `v0:real^N`
    (X_CHOOSE_THEN `b:bool` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `z:(real^N->bool)->bool`;
                 `f:real^N#bool->real^N`; `q:real^N->real^N`; `t:real^N->bool`;
                 `v0:real^N`; `b:bool`] MOI_FCV_LIFT_PROPS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[MOI_REAL_IN_VERTEX_SETS]; ASM_MESON_TAC[]]);;

let MOI_FCV_INJECTIVE = prove
 (`!(c:(real^N->bool)->bool) z (f:real^N#bool->real^N) (q:real^N->real^N).
     simplicial_complex c /\ z2_cocycle c z /\
     abstract_realizes f (moi_fcv_lifts c z) /\
     (!s. s IN moi_fcv_lifts c z
          ==> ?l y. linear l /\ (!w. w IN s ==> l (f w) + y = FST w) /\
                    (!x. x IN convex hull (IMAGE f s) ==> q x = l x + y))
     ==> !L. L IN abstract_realization f (moi_fcv_lifts c z)
             ==> !x y. x IN L /\ y IN L /\ q x = q y ==> x = y`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "aff")))) THEN
  REWRITE_TAC[MOI_FCV_IN_REALIZATION] THEN
  X_GEN_TAC `L:real^N->bool` THEN STRIP_TAC THENL
   [ASM_REWRITE_TAC[NOT_IN_EMPTY]; ALL_TAC] THEN
  UNDISCH_TAC `(s:real^N#bool->bool) IN moi_fcv_lifts (c:(real^N->bool)->bool) z` THEN
  REWRITE_TAC[MOI_FCV_IN_LIFTS] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` (X_CHOOSE_THEN `v0:real^N`
    (X_CHOOSE_THEN `b:bool` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `z:(real^N->bool)->bool`;
                 `f:real^N#bool->real^N`; `q:real^N->real^N`; `t:real^N->bool`;
                 `v0:real^N`; `b:bool`] MOI_FCV_LIFT_PROPS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `l':real^N->real^N` (X_CHOOSE_THEN `y':real^N`
    STRIP_ASSUME_TAC) o last o CONJUNCTS) THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

let MOI_FCV_LIFTS_MEET = prove
 (`!(c:(real^N->bool)->bool) z t v1 b1 v2 b2.
     simplicial_complex c /\ z2_cocycle c z /\ t IN moi_real_vertex_sets c /\
     v1 IN t /\ v2 IN t /\
     ~(IMAGE (\v. v,moi_fcv_sheet z v1 b1 v) t INTER
       IMAGE (\v. v,moi_fcv_sheet z v2 b2 v) t = {})
     ==> IMAGE (\v. v,moi_fcv_sheet z v1 b1 v) t =
         IMAGE (\v. v,moi_fcv_sheet z v2 b2 v) t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `?u:real^N. u IN t /\ moi_fcv_sheet z v1 b1 u = moi_fcv_sheet z v2 b2 u`
  STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[GSYM MEMBER_NOT_EMPTY]) THEN
    REWRITE_TAC[IN_INTER; IN_IMAGE; EXISTS_PAIR_THM; PAIR_EQ] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `z:(real^N->bool)->bool`; `t:real^N->bool`;
                 `t:real^N->bool`; `v1:real^N`; `u:real^N`; `b1:bool`]
    MOI_FCV_LIFT_REBASE) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `z:(real^N->bool)->bool`; `t:real^N->bool`;
                 `t:real^N->bool`; `v2:real^N`; `u:real^N`; `b2:bool`]
    MOI_FCV_LIFT_REBASE) THEN
  ASM_REWRITE_TAC[SUBSET_REFL] THEN
  DISCH_THEN SUBST1_TAC THEN DISCH_THEN SUBST1_TAC THEN REFL_TAC);;

let MOI_FCV_UNIQUE = prove
 (`!(c:(real^N->bool)->bool) z (f:real^N#bool->real^N) (q:real^N->real^N).
     simplicial_complex c /\ z2_cocycle c z /\
     abstract_realizes f (moi_fcv_lifts c z) /\
     (!s. s IN moi_fcv_lifts c z
          ==> ?l y. linear l /\ (!w. w IN s ==> l (f w) + y = FST w) /\
                    (!x. x IN convex hull (IMAGE f s) ==> q x = l x + y))
     ==> !L1 L2. L1 IN abstract_realization f (moi_fcv_lifts c z) /\ L2 IN abstract_realization f (moi_fcv_lifts c z) /\
                 IMAGE q L1 = IMAGE q L2 /\ ~DISJOINT L1 L2
                 ==> L1 = L2`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "aff")))) THEN
  REWRITE_TAC[MOI_FCV_IN_REALIZATION] THEN
  MAP_EVERY X_GEN_TAC [`L1:real^N->bool`; `L2:real^N->bool`] THEN
  ASM_CASES_TAC `L1:real^N->bool = {}` THEN ASM_REWRITE_TAC[DISJOINT_EMPTY] THEN
  ASM_CASES_TAC `L2:real^N->bool = {}` THEN ASM_REWRITE_TAC[DISJOINT_EMPTY] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> lhs(concl th) = `L1:real^N->bool`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> lhs(concl th) = `L2:real^N->bool`)) THEN
  UNDISCH_TAC `(s:real^N#bool->bool) IN moi_fcv_lifts (c:(real^N->bool)->bool) z` THEN
  UNDISCH_TAC `(s':real^N#bool->bool) IN moi_fcv_lifts (c:(real^N->bool)->bool) z` THEN
  REWRITE_TAC[MOI_FCV_IN_LIFTS] THEN
  DISCH_THEN(X_CHOOSE_THEN `t2:real^N->bool` (X_CHOOSE_THEN `v2:real^N`
    (X_CHOOSE_THEN `b2:bool` STRIP_ASSUME_TAC))) THEN
  DISCH_THEN(X_CHOOSE_THEN `t1:real^N->bool` (X_CHOOSE_THEN `v1:real^N`
    (X_CHOOSE_THEN `b1:bool` STRIP_ASSUME_TAC))) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> lhs(concl th) = `s:real^N#bool->bool`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> lhs(concl th) = `s':real^N#bool->bool`)) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `z:(real^N->bool)->bool`;
                 `f:real^N#bool->real^N`; `q:real^N->real^N`; `t1:real^N->bool`;
                 `v1:real^N`; `b1:bool`] MOI_FCV_LIFT_PROPS) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `z:(real^N->bool)->bool`;
                 `f:real^N#bool->real^N`; `q:real^N->real^N`; `t2:real^N->bool`;
                 `v2:real^N`; `b2:bool`] MOI_FCV_LIFT_PROPS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC))) THEN
  SUBGOAL_THEN `t1:real^N->bool = t2` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC SIMPLEX_VERTICES_UNIQUE THEN
    REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[MOI_REAL_IN_VERTEX_SETS]; ASM_MESON_TAC[MOI_REAL_IN_VERTEX_SETS];
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC MOI_FCV_LIFTS_MEET THEN EXISTS_TAC `c:(real^N->bool)->bool` THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  UNDISCH_TAC `abstract_realizes (f:real^N#bool->real^N) (moi_fcv_lifts c z)` THEN
  REWRITE_TAC[abstract_realizes] THEN
  DISCH_THEN(MP_TAC o SPECL
   [`IMAGE (\v. v,moi_fcv_sheet z (v1:real^N) b1 v) t2`;
    `IMAGE (\v. v,moi_fcv_sheet z (v2:real^N) b2 v) t2`] o CONJUNCT2 o CONJUNCT2) THEN
  ASM_REWRITE_TAC[IMAGE_CLAUSES; CONVEX_HULL_EMPTY] THEN
  ASM_REWRITE_TAC[GSYM DISJOINT]);;

let MOI_FCV_POINT_LIFT = prove
 (`!(c:(real^N->bool)->bool) z (f:real^N#bool->real^N) (q:real^N->real^N).
     simplicial_complex c /\ z2_cocycle c z /\
     abstract_realizes f (moi_fcv_lifts c z) /\
     (!s. s IN moi_fcv_lifts c z
          ==> ?l y. linear l /\ (!w. w IN s ==> l (f w) + y = FST w) /\
                    (!x. x IN convex hull (IMAGE f s) ==> q x = l x + y))
     ==> !y s. y IN UNIONS (abstract_realization f (moi_fcv_lifts c z)) /\ s IN c /\ q y IN s
               ==> ?L. L IN abstract_realization f (moi_fcv_lifts c z) /\ IMAGE q L = s /\ y IN L`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "aff")))) THEN
  MAP_EVERY X_GEN_TAC [`y:real^N`; `s:real^N->bool`] THEN REWRITE_TAC[IN_UNIONS] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `L1:real^N->bool` STRIP_ASSUME_TAC)
    STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `(L1:real^N->bool) IN abstract_realization (f:real^N#bool->real^N)
                (moi_fcv_lifts (c:(real^N->bool)->bool) z)` THEN
  GEN_REWRITE_TAC LAND_CONV [MOI_FCV_IN_REALIZATION] THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC
    (X_CHOOSE_THEN `s1:real^N#bool->bool` STRIP_ASSUME_TAC)) THENL
   [ASM_MESON_TAC[NOT_IN_EMPTY]; ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> lhs(concl th) = `L1:real^N->bool`)) THEN
  UNDISCH_TAC `(s1:real^N#bool->bool) IN moi_fcv_lifts (c:(real^N->bool)->bool) z` THEN
  GEN_REWRITE_TAC LAND_CONV [MOI_FCV_IN_LIFTS] THEN
  DISCH_THEN(X_CHOOSE_THEN `t1:real^N->bool` (X_CHOOSE_THEN `v1:real^N`
    (X_CHOOSE_THEN `b1:bool` STRIP_ASSUME_TAC))) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> lhs(concl th) = `s1:real^N#bool->bool`)) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `z:(real^N->bool)->bool`;
                 `f:real^N#bool->real^N`; `q:real^N->real^N`; `t1:real^N->bool`;
                 `v1:real^N`; `b1:bool`] MOI_FCV_LIFT_PROPS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (K ALL_TAC) (X_CHOOSE_THEN `l1:real^N->real^N`
       (X_CHOOSE_THEN `y1:real^N` STRIP_ASSUME_TAC))))) THEN
  SUBGOAL_THEN `~(s:real^N->bool = {})` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `s:real^N->bool`] MOI_REAL_SIMPLEX_VERTICES) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> lhs(concl th) = `s:real^N->bool`)) THEN
  SUBGOAL_THEN `(q:real^N->real^N) y IN convex hull (t1 INTER t)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `t1:real^N->bool`; `t:real^N->bool`]
      MOI_REAL_SIMPLICIAL_COMPLEX_INTER_HULL) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[MOI_REAL_IN_VERTEX_SETS]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
    REWRITE_TAC[IN_INTER] THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[FUN_IN_IMAGE];
    ALL_TAC] THEN
  SUBGOAL_THEN `?w:real^N. w IN t1 /\ w IN t` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(SET_RULE `~(s INTER t:real^N->bool = {}) ==> ?v. v IN s /\ v IN t`) THEN
    DISCH_TAC THEN UNDISCH_TAC `(q:real^N->real^N) y IN convex hull (t1 INTER t)` THEN
    ASM_REWRITE_TAC[CONVEX_HULL_EMPTY; NOT_IN_EMPTY];
    ALL_TAC] THEN
  ABBREV_TAC `bb = moi_fcv_sheet z (v1:real^N) b1 w` THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `z:(real^N->bool)->bool`;
                 `f:real^N#bool->real^N`; `q:real^N->real^N`; `t:real^N->bool`;
                 `w:real^N`; `bb:bool`] MOI_FCV_LIFT_PROPS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o CONJUNCT1)) THEN
  EXISTS_TAC `convex hull (IMAGE (f:real^N#bool->real^N)
                           (IMAGE (\u. u,moi_fcv_sheet z w bb u) t))` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[MOI_FCV_IN_REALIZATION] THEN DISJ2_TAC THEN
    EXISTS_TAC `IMAGE (\u. u,moi_fcv_sheet z (w:real^N) bb u) t` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^N) = (\x. (l1:real^N->real^N) x + y1) ((q:real^N->real^N) y)`
  SUBST1_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (\x. (l1:real^N->real^N) x + y1) (convex hull (t1 INTER t)) SUBSET
    convex hull (IMAGE (f:real^N#bool->real^N) (IMAGE (\u. u,moi_fcv_sheet z w bb u) t))`
  MP_TAC THENL
   [ASM_SIMP_TAC[MOI_REAL_AFFINE_IMAGE_CONVEX_HULL] THEN MATCH_MP_TAC HULL_MONO THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTER] THEN X_GEN_TAC `u:real^N` THEN
    STRIP_TAC THEN REWRITE_TAC[IN_IMAGE] THEN
    EXISTS_TAC `(u:real^N),moi_fcv_sheet z w bb u` THEN CONJ_TAC THENL
     [ALL_TAC; EXISTS_TAC `u:real^N` THEN ASM_REWRITE_TAC[]] THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `(f:real^N#bool->real^N) (u,moi_fcv_sheet z v1 b1 u)` THEN
    CONJ_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    AP_TERM_TAC THEN REWRITE_TAC[PAIR_EQ] THEN EXPAND_TAC "bb" THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOI_FCV_SHEET_REBASE THEN
    MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `t1:real^N->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[]);;

let MOI_FCV_ONTO = prove
 (`!(c:(real^N->bool)->bool) z (f:real^N#bool->real^N) (q:real^N->real^N).
     simplicial_complex c /\ z2_cocycle c z /\
     abstract_realizes f (moi_fcv_lifts c z) /\
     (!s. s IN moi_fcv_lifts c z
          ==> ?l y. linear l /\ (!w. w IN s ==> l (f w) + y = FST w) /\
                    (!x. x IN convex hull (IMAGE f s) ==> q x = l x + y))
     ==> IMAGE q (UNIONS (abstract_realization f (moi_fcv_lifts c z))) = UNIONS c`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "aff")))) THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_UNIONS] THEN X_GEN_TAC `y:real^N` THEN
    DISCH_THEN(X_CHOOSE_THEN `L:real^N->bool` (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)) THEN
    REWRITE_TAC[MOI_FCV_IN_REALIZATION] THEN
    DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC
      (X_CHOOSE_THEN `s:real^N#bool->bool` STRIP_ASSUME_TAC)) THENL
     [ASM_MESON_TAC[NOT_IN_EMPTY]; ALL_TAC] THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> lhs(concl th) = `L:real^N->bool`)) THEN
    UNDISCH_TAC `(s:real^N#bool->bool) IN moi_fcv_lifts (c:(real^N->bool)->bool) z` THEN
    REWRITE_TAC[MOI_FCV_IN_LIFTS] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` (X_CHOOSE_THEN `v0:real^N`
      (X_CHOOSE_THEN `b:bool` STRIP_ASSUME_TAC))) THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> lhs(concl th) = `s:real^N#bool->bool`)) THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `z:(real^N->bool)->bool`;
                   `f:real^N#bool->real^N`; `q:real^N->real^N`; `t:real^N->bool`;
                   `v0:real^N`; `b:bool`] MOI_FCV_LIFT_PROPS) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1 o CONJUNCT2) THEN
    EXISTS_TAC `convex hull t:real^N->bool` THEN CONJ_TAC THENL
     [ASM_MESON_TAC[MOI_REAL_IN_VERTEX_SETS]; ASM_MESON_TAC[FUN_IN_IMAGE]];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET; IN_UNIONS] THEN X_GEN_TAC `x:real^N` THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `~(s:real^N->bool = {})` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `s:real^N->bool`] MOI_REAL_SIMPLEX_VERTICES) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> lhs(concl th) = `s:real^N->bool`)) THEN
  SUBGOAL_THEN `?v0:real^N. v0 IN t` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_REAL_IN_VERTEX_SETS; MEMBER_NOT_EMPTY]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `z:(real^N->bool)->bool`;
                 `f:real^N#bool->real^N`; `q:real^N->real^N`; `t:real^N->bool`;
                 `v0:real^N`; `T`] MOI_FCV_LIFT_PROPS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o CONJUNCT1)) THEN
  SUBGOAL_THEN `convex hull (IMAGE (f:real^N#bool->real^N)
                  (IMAGE (\v. v,moi_fcv_sheet z v0 T v) t)) IN
                abstract_realization f (moi_fcv_lifts (c:(real^N->bool)->bool) z)`
  ASSUME_TAC THENL
   [REWRITE_TAC[MOI_FCV_IN_REALIZATION] THEN DISJ2_TAC THEN
    EXISTS_TAC `IMAGE (\v. v,moi_fcv_sheet z (v0:real^N) T v) t` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `(x:real^N) IN convex hull t` THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
    rhs(concl th) = `convex hull t:real^N->bool`)) THEN
  REWRITE_TAC[IN_IMAGE; IN_UNIONS] THEN ASM_MESON_TAC[]);;

let MOI_FCV_COVERING = prove
 (`!(c:(real^N->bool)->bool) z (f:real^N#bool->real^N) (q:real^N->real^N).
     simplicial_complex c /\ z2_cocycle c z /\
     abstract_realizes f (moi_fcv_lifts c z) /\
     (!s. s IN moi_fcv_lifts c z
          ==> ?l y. linear l /\ (!w. w IN s ==> l (f w) + y = FST w) /\
                    (!x. x IN convex hull (IMAGE f s) ==> q x = l x + y)) /\
     {} IN c
     ==> covering_space (UNIONS (abstract_realization f (moi_fcv_lifts c z)),q) (UNIONS c)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_FCV_COVERING_FROM_SHEETS THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC ABSTRACT_REALIZATION_SIMPLICIAL_COMPLEX THEN
    ASM_SIMP_TAC[MOI_FCV_LIFTS_FINITE; MOI_FCV_LIFTS_ABSTRACT];
    MATCH_MP_TAC MOI_FCV_SIMPLICIAL_MAP THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOI_FCV_INJECTIVE THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOI_FCV_UNIQUE THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOI_FCV_POINT_LIFT THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOI_FCV_ONTO THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The fibres of q have exactly two points.  Over a point of convex hull t   *)
(* the two lifts of t based at a vertex v0 (sheets T and F) are disjoint     *)
(* (MOI_FCV_LIFTS_DISJOINT), every lift of t is one of them after rebasing   *)
(* at v0, and q is injective on each (MOI_FCV_FIBRE2).                       *)
(* ------------------------------------------------------------------------- *)

let MOI_FCV_SHEET_FLIP = prove
 (`!(z:(real^N->bool)->bool) v0 u.
     moi_fcv_sheet z v0 F u <=> ~(moi_fcv_sheet z v0 T u)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_fcv_sheet] THEN
  COND_CASES_TAC THEN REWRITE_TAC[]);;

let MOI_FCV_LIFTS_DISJOINT = prove
 (`!(z:(real^N->bool)->bool) v0 t.
     IMAGE (\v. v,moi_fcv_sheet z v0 T v) t INTER
     IMAGE (\v. v,moi_fcv_sheet z v0 F v) t = {}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[EXTENSION; IN_INTER; IN_IMAGE; NOT_IN_EMPTY] THEN
  X_GEN_TAC `p:real^N#bool` THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `u1:real^N` STRIP_ASSUME_TAC)
    (X_CHOOSE_THEN `u2:real^N` STRIP_ASSUME_TAC)) THEN
  UNDISCH_TAC `p = (u2:real^N),moi_fcv_sheet z v0 F u2` THEN
  ASM_REWRITE_TAC[PAIR_EQ; MOI_FCV_SHEET_FLIP] THEN MESON_TAC[]);;

let MOI_FCV_FIBRE2 = prove
 (`!(c:(real^N->bool)->bool) z (f:real^N#bool->real^N) (q:real^N->real^N).
     simplicial_complex c /\ z2_cocycle c z /\
     abstract_realizes f (moi_fcv_lifts c z) /\
     (!s. s IN moi_fcv_lifts c z
          ==> ?l y. linear l /\ (!w. w IN s ==> l (f w) + y = FST w) /\
                    (!x. x IN convex hull (IMAGE f s) ==> q x = l x + y))
     ==> !y. y IN UNIONS c ==> {x | x IN UNIONS (abstract_realization f (moi_fcv_lifts c z)) /\ q x = y} HAS_SIZE 2`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "aff")))) THEN
  X_GEN_TAC `y:real^N` THEN REWRITE_TAC[IN_UNIONS] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `~(s:real^N->bool = {})` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `s:real^N->bool`] MOI_REAL_SIMPLEX_VERTICES) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> lhs(concl th) = `s:real^N->bool`)) THEN
  SUBGOAL_THEN `?v0:real^N. v0 IN t` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_REAL_IN_VERTEX_SETS; MEMBER_NOT_EMPTY]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!b. IMAGE (\v. v,moi_fcv_sheet z v0 b v) t IN
        moi_fcv_lifts (c:(real^N->bool)->bool) z /\
        convex hull (IMAGE (f:real^N#bool->real^N)
                       (IMAGE (\v. v,moi_fcv_sheet z v0 b v) t)) IN
        abstract_realization f (moi_fcv_lifts (c:(real^N->bool)->bool) z) /\
        IMAGE (q:real^N->real^N)
         (convex hull (IMAGE f (IMAGE (\v. v,moi_fcv_sheet z v0 b v) t))) =
        convex hull t`
  ASSUME_TAC THENL
   [X_GEN_TAC `b:bool` THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `z:(real^N->bool)->bool`;
                   `f:real^N#bool->real^N`; `q:real^N->real^N`; `t:real^N->bool`;
                   `v0:real^N`; `b:bool`] MOI_FCV_LIFT_PROPS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MOI_FCV_IN_REALIZATION] THEN DISJ2_TAC THEN
    EXISTS_TAC `IMAGE (\v. v,moi_fcv_sheet z (v0:real^N) b v) t` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!b. ?x:real^N. x IN convex hull (IMAGE (f:real^N#bool->real^N)
                                      (IMAGE (\v. v,moi_fcv_sheet z v0 b v) t)) /\
                   (q:real^N->real^N) x = y`
  MP_TAC THENL
   [X_GEN_TAC `b:bool` THEN
    FIRST_X_ASSUM(MP_TAC o CONJUNCT2 o CONJUNCT2 o SPEC `b:bool`) THEN
    REWRITE_TAC[EXTENSION; IN_IMAGE] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `xx:bool->real^N` (LABEL_TAC "xx")) THEN
  SUBGOAL_THEN
   `!L. L IN abstract_realization (f:real^N#bool->real^N)
               (moi_fcv_lifts (c:(real^N->bool)->bool) z) /\
        IMAGE (q:real^N->real^N) L = convex hull t
        ==> ?b. L = convex hull (IMAGE f (IMAGE (\v. v,moi_fcv_sheet z v0 b v) t))`
  (LABEL_TAC "sheets") THENL
   [X_GEN_TAC `L:real^N->bool` THEN
    GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [MOI_FCV_IN_REALIZATION] THEN
    DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
    DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC
      (X_CHOOSE_THEN `s1:real^N#bool->bool` STRIP_ASSUME_TAC)) THENL
     [UNDISCH_TAC `IMAGE (q:real^N->real^N) {} = convex hull t` THEN
      REWRITE_TAC[IMAGE_CLAUSES] THEN CONV_TAC(LAND_CONV SYM_CONV) THEN
      REWRITE_TAC[CONVEX_HULL_EQ_EMPTY] THEN ASM_MESON_TAC[MOI_REAL_IN_VERTEX_SETS];
      ALL_TAC] THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> lhs(concl th) = `L:real^N->bool`)) THEN
    UNDISCH_TAC `(s1:real^N#bool->bool) IN moi_fcv_lifts (c:(real^N->bool)->bool) z` THEN
    GEN_REWRITE_TAC LAND_CONV [MOI_FCV_IN_LIFTS] THEN
    DISCH_THEN(X_CHOOSE_THEN `t1:real^N->bool` (X_CHOOSE_THEN `v1:real^N`
      (X_CHOOSE_THEN `b1:bool` STRIP_ASSUME_TAC))) THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> lhs(concl th) = `s1:real^N#bool->bool`)) THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `z:(real^N->bool)->bool`;
                   `f:real^N#bool->real^N`; `q:real^N->real^N`; `t1:real^N->bool`;
                   `v1:real^N`; `b1:bool`] MOI_FCV_LIFT_PROPS) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `t1:real^N->bool = t` SUBST_ALL_TAC THENL
     [MATCH_MP_TAC SIMPLEX_VERTICES_UNIQUE THEN
      ASM_MESON_TAC[MOI_REAL_IN_VERTEX_SETS];
      ALL_TAC] THEN
    EXISTS_TAC `moi_fcv_sheet z (v1:real^N) b1 v0` THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC MOI_FCV_LIFT_REBASE THEN
    MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `t:real^N->bool`] THEN
    ASM_REWRITE_TAC[SUBSET_REFL];
    ALL_TAC] THEN
  CONV_TAC HAS_SIZE_CONV THEN
  MAP_EVERY EXISTS_TAC [`(xx:bool->real^N) T`; `(xx:bool->real^N) F`] THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN
     `convex hull (IMAGE (f:real^N#bool->real^N)
                    (IMAGE (\v. v,moi_fcv_sheet z (v0:real^N) T v) t)) INTER
      convex hull (IMAGE f (IMAGE (\v. v,moi_fcv_sheet z v0 F v) t)) = {}`
    MP_TAC THENL
     [UNDISCH_TAC `abstract_realizes (f:real^N#bool->real^N) (moi_fcv_lifts c z)` THEN
      REWRITE_TAC[abstract_realizes] THEN
      DISCH_THEN(MP_TAC o SPECL
       [`IMAGE (\v. v,moi_fcv_sheet z (v0:real^N) T v) t`;
        `IMAGE (\v. v,moi_fcv_sheet z (v0:real^N) F v) t`] o CONJUNCT2 o CONJUNCT2) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
      REWRITE_TAC[MOI_FCV_LIFTS_DISJOINT; IMAGE_CLAUSES; CONVEX_HULL_EMPTY];
      ALL_TAC] THEN
    REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
    DISCH_THEN(MP_TAC o SPEC `(xx:bool->real^N) T`) THEN
    USE_THEN "xx" (fun th -> MP_TAC(SPEC `T` th) THEN MP_TAC(SPEC `F` th)) THEN
    MESON_TAC[];
    ALL_TAC] THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:real^N` THEN
  REWRITE_TAC[IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY] THEN EQ_TAC THENL
   [STRIP_TAC THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `z:(real^N->bool)->bool`;
                   `f:real^N#bool->real^N`; `q:real^N->real^N`] MOI_FCV_POINT_LIFT) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL [`x:real^N`; `convex hull t:real^N->bool`]) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[IN_UNIONS] THEN ASM_MESON_TAC[MOI_REAL_IN_VERTEX_SETS]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `L:real^N->bool` STRIP_ASSUME_TAC) THEN
    USE_THEN "sheets" (MP_TAC o SPEC `L:real^N->bool`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `bb:bool` SUBST_ALL_TAC) THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `z:(real^N->bool)->bool`;
                   `f:real^N#bool->real^N`; `q:real^N->real^N`] MOI_FCV_INJECTIVE) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC
     `convex hull (IMAGE (f:real^N#bool->real^N)
                    (IMAGE (\v. v,moi_fcv_sheet z (v0:real^N) bb v) t))`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPECL [`x:real^N`; `(xx:bool->real^N) bb`]) THEN
    USE_THEN "xx" (MP_TAC o SPEC `bb:bool`) THEN
    ASM_CASES_TAC `bb:bool` THEN ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(DISJ_CASES_THEN SUBST1_TAC) THEN
  (USE_THEN "xx" (MP_TAC o SPEC `T`) ORELSE ALL_TAC) THEN
  REWRITE_TAC[IN_UNIONS] THEN ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The cover is connected because z is no coboundary.  A function on the     *)
(* vertices that is constant on each vertex set is constant when UNIONS c is *)
(* connected (MOI_FCV_VERTEX_CONST).  For a clopen set A of UNIONS c' every  *)
(* simplex of c' lies in A or misses it, so the set of the two memberships   *)
(* of the lifts of a vertex is constant; if A is a proper nonempty clopen    *)
(* set then exactly one lift of each vertex lies in A                        *)
(* (MOI_FCV_CLOPEN_SPLIT), and the vertices whose T-lift lies in A form a    *)
(* coboundary of z (MOI_FCV_CONNECTED).                                      *)
(* ------------------------------------------------------------------------- *)

let MOI_FCV_SING_VERTEX_SET = prove
 (`!(c:(real^N->bool)->bool) v.
     {v} IN c ==> {v} IN moi_real_vertex_sets c`,
  REWRITE_TAC[MOI_REAL_IN_VERTEX_SETS; NOT_INSERT_EMPTY; AFFINE_INDEPENDENT_1;
              CONVEX_HULL_SING]);;

let MOI_FCV_VERTEX_CONST = prove
 (`!(c:(real^N->bool)->bool) (g:real^N->A).
     simplicial_complex c /\ connected (UNIONS c) /\
     (!t u v. t IN moi_real_vertex_sets c /\ u IN t /\ v IN t ==> g u = g v)
     ==> !u v. {u} IN c /\ {v} IN c ==> g u = g v`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 MP_TAC (LABEL_TAC "inv"))) THEN
  REWRITE_TAC[CONNECTED_CLOSED; NOT_EXISTS_THM] THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`u:real^N`; `v:real^N`] THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`UNIONS {convex hull t | t IN moi_real_vertex_sets c /\
                             !w:real^N. w IN t ==> (g:real^N->A) w = g u}`;
    `UNIONS {convex hull t | t IN moi_real_vertex_sets c /\
                             !w:real^N. w IN t ==> ~((g:real^N->A) w = g u)}`]) THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN `FINITE (moi_real_vertex_sets (c:(real^N->bool)->bool))` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_REAL_VERTEX_SETS_FINITE THEN ASM_MESON_TAC[simplicial_complex];
    ALL_TAC] THEN
  SUBGOAL_THEN `!t. t IN moi_real_vertex_sets c ==> closed (convex hull t:real^N->bool)`
  ASSUME_TAC THENL
   [REWRITE_TAC[MOI_REAL_IN_VERTEX_SETS] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC COMPACT_IMP_CLOSED THEN MATCH_MP_TAC FINITE_IMP_COMPACT_CONVEX_HULL THEN
    ASM_SIMP_TAC[AFFINE_INDEPENDENT_IMP_FINITE];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CLOSED_UNIONS THEN CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `IMAGE (\t:real^N->bool. convex hull t) (moi_real_vertex_sets c)` THEN
      CONJ_TAC THENL [MATCH_MP_TAC FINITE_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_IMAGE] THEN MESON_TAC[];
      REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[]];
    MATCH_MP_TAC CLOSED_UNIONS THEN CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `IMAGE (\t:real^N->bool. convex hull t) (moi_real_vertex_sets c)` THEN
      CONJ_TAC THENL [MATCH_MP_TAC FINITE_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_IMAGE] THEN MESON_TAC[];
      REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[]];
    REWRITE_TAC[SUBSET; IN_UNIONS; IN_UNION; IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^N` THEN
    DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `~(s:real^N->bool = {})` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `s:real^N->bool`]
      MOI_REAL_SIMPLEX_VERTICES) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `?w0:real^N. w0 IN t` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[MOI_REAL_IN_VERTEX_SETS; MEMBER_NOT_EMPTY]; ALL_TAC] THEN
    ASM_CASES_TAC `(g:real^N->A) w0 = g u` THENL
     [DISJ1_TAC; DISJ2_TAC] THEN
    EXISTS_TAC `convex hull t:real^N->bool` THEN
    (CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[]]) THEN
    EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `w:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(g:real^N->A) w = g w0` (fun th -> ASM_REWRITE_TAC[th]) THEN
    USE_THEN "inv" MATCH_MP_TAC THEN EXISTS_TAC `t:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:real^N` THEN
    REWRITE_TAC[IN_INTER; NOT_IN_EMPTY; IN_UNIONS; IN_ELIM_THM] THEN
    DISCH_THEN(CONJUNCTS_THEN2
      (X_CHOOSE_THEN `h1:real^N->bool` (CONJUNCTS_THEN2
         (X_CHOOSE_THEN `t1:real^N->bool` STRIP_ASSUME_TAC) ASSUME_TAC))
      (CONJUNCTS_THEN2
        (X_CHOOSE_THEN `h2:real^N->bool` (CONJUNCTS_THEN2
           (X_CHOOSE_THEN `t2:real^N->bool` STRIP_ASSUME_TAC) ASSUME_TAC))
        (K ALL_TAC))) THEN
    SUBGOAL_THEN `(x:real^N) IN convex hull (t1 INTER t2)` MP_TAC THENL
     [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `t1:real^N->bool`; `t2:real^N->bool`]
        MOI_REAL_SIMPLICIAL_COMPLEX_INTER_HULL) THEN
      ANTS_TAC THENL [ASM_MESON_TAC[MOI_REAL_IN_VERTEX_SETS]; ALL_TAC] THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_MESON_TAC[IN_INTER];
      ALL_TAC] THEN
    ASM_CASES_TAC `t1 INTER t2:real^N->bool = {}` THEN
    ASM_REWRITE_TAC[CONVEX_HULL_EMPTY; NOT_IN_EMPTY] THEN
    FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[GSYM MEMBER_NOT_EMPTY; IN_INTER]) THEN
    ASM_MESON_TAC[];
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_UNIONS; IN_ELIM_THM] THEN
    EXISTS_TAC `u:real^N` THEN CONJ_TAC THENL
     [EXISTS_TAC `{u:real^N}` THEN REWRITE_TAC[IN_SING] THEN
      EXISTS_TAC `{u:real^N}` THEN REWRITE_TAC[CONVEX_HULL_SING; IN_SING] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC MOI_FCV_SING_VERTEX_SET THEN ASM_REWRITE_TAC[]; MESON_TAC[]];
      EXISTS_TAC `{u:real^N}` THEN ASM_REWRITE_TAC[IN_SING]];
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_UNIONS; IN_ELIM_THM] THEN
    EXISTS_TAC `v:real^N` THEN CONJ_TAC THENL
     [EXISTS_TAC `{v:real^N}` THEN REWRITE_TAC[IN_SING] THEN
      EXISTS_TAC `{v:real^N}` THEN REWRITE_TAC[CONVEX_HULL_SING; IN_SING] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC MOI_FCV_SING_VERTEX_SET THEN ASM_REWRITE_TAC[];
        ASM_MESON_TAC[]];
      EXISTS_TAC `{v:real^N}` THEN ASM_REWRITE_TAC[IN_SING]]]);;

let MOI_FCV_ODD2 = prove
 (`!(P:A->bool) u v.
     ~(u = v) ==> (ODD (CARD {x | x IN {u,v} /\ P x}) <=> ~(P u <=> P v))`,
  REPEAT STRIP_TAC THEN
  MAP_EVERY ASM_CASES_TAC [`(P:A->bool) u`; `(P:A->bool) v`] THEN
  ASM_REWRITE_TAC[] THENL
   [SUBGOAL_THEN `{x | x IN {u,v} /\ (P:A->bool) x} = {u,v}` SUBST1_TAC THENL
     [ASM SET_TAC[]; ALL_TAC];
    SUBGOAL_THEN `{x | x IN {u,v} /\ (P:A->bool) x} = {u}` SUBST1_TAC THENL
     [ASM SET_TAC[]; ALL_TAC];
    SUBGOAL_THEN `{x | x IN {u,v} /\ (P:A->bool) x} = {v}` SUBST1_TAC THENL
     [ASM SET_TAC[]; ALL_TAC];
    SUBGOAL_THEN `{x | x IN {u,v} /\ (P:A->bool) x} = {}` SUBST1_TAC THENL
     [ASM SET_TAC[]; ALL_TAC]] THEN
  SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN
  ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY; ODD]);;

let MOI_FCV_SUBSET_VERTEX_SET = prove
 (`!(c:(real^N->bool)->bool) t t'.
     simplicial_complex c /\ t IN moi_real_vertex_sets c /\ ~(t' = {}) /\ t' SUBSET t
     ==> t' IN moi_real_vertex_sets c`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `c:(real^N->bool)->bool` MOI_REAL_VERTEX_SETS_ABSTRACT_COMPLEX) THEN
  ASM_REWRITE_TAC[abstract_complex] THEN
  DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN EXISTS_TAC `t:real^N->bool` THEN
  ASM_REWRITE_TAC[]);;

let MOI_FCV_VERTEX_OF_SET = prove
 (`!(c:(real^N->bool)->bool) t v.
     simplicial_complex c /\ t IN moi_real_vertex_sets c /\ v IN t ==> {v} IN c`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `{v:real^N} IN moi_real_vertex_sets c` MP_TAC THENL
   [MATCH_MP_TAC MOI_FCV_SUBSET_VERTEX_SET THEN EXISTS_TAC `t:real^N->bool` THEN
    ASM_REWRITE_TAC[NOT_INSERT_EMPTY] THEN ASM SET_TAC[];
    SIMP_TAC[MOI_REAL_IN_VERTEX_SETS; CONVEX_HULL_SING]]);;

let MOI_FCV_EDGE_FORM = prove
 (`!(c:(real^N->bool)->bool) e.
     simplicial_complex c /\ e IN c /\ aff_dim e = &1
     ==> ?u v. ~(u = v) /\ {u,v} IN moi_real_vertex_sets c /\ e = convex hull {u,v}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(e:real^N->bool = {})` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `aff_dim (e:real^N->bool) = &1` THEN
    ASM_REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `e:real^N->bool`] MOI_REAL_SIMPLEX_VERTICES) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(t:real^N->bool) HAS_SIZE 2` MP_TAC THENL
   [SUBGOAL_THEN `~affine_dependent (t:real^N->bool)` ASSUME_TAC THENL
     [ASM_MESON_TAC[MOI_REAL_IN_VERTEX_SETS]; ALL_TAC] THEN
    REWRITE_TAC[HAS_SIZE] THEN ASM_SIMP_TAC[AFFINE_INDEPENDENT_IMP_FINITE] THEN
    UNDISCH_TAC `aff_dim (e:real^N->bool) = &1` THEN
    ASM_SIMP_TAC[AFF_DIM_CONVEX_HULL; AFF_DIM_AFFINE_INDEPENDENT] THEN
    REWRITE_TAC[GSYM INT_OF_NUM_EQ] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  CONV_TAC(LAND_CONV HAS_SIZE_CONV) THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N` (X_CHOOSE_THEN `v:real^N` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`u:real^N`; `v:real^N`] THEN
  UNDISCH_TAC `(t:real^N->bool) IN moi_real_vertex_sets c` THEN
  ASM_REWRITE_TAC[] THEN SIMP_TAC[]);;

let MOI_FCV_EDGE_VERTICES = prove
 (`!(c:(real^N->bool)->bool) u v x.
     simplicial_complex c /\ {u,v} IN moi_real_vertex_sets c
     ==> ({x} IN c /\ x IN convex hull {u,v} <=> x = u \/ x = v)`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [STRIP_TAC THEN
    SUBGOAL_THEN `{x:real^N} face_of convex hull {u,v}` MP_TAC THENL
     [SUBGOAL_THEN `{x:real^N} = {x} INTER convex hull {u,v}` SUBST1_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `simplicial_complex (c:(real^N->bool)->bool)` THEN
      REWRITE_TAC[simplicial_complex] THEN
      DISCH_THEN(MP_TAC o SPECL [`{x:real^N}`; `convex hull {u:real^N,v}`] o
                 CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
      ANTS_TAC THENL [ASM_MESON_TAC[MOI_REAL_IN_VERTEX_SETS]; SIMP_TAC[]];
      ALL_TAC] THEN
    REWRITE_TAC[FACE_OF_SING] THEN
    DISCH_THEN(MP_TAC o MATCH_MP EXTREME_POINT_OF_CONVEX_HULL) THEN
    REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY];
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    (CONJ_TAC THENL
      [MATCH_MP_TAC MOI_FCV_VERTEX_OF_SET THEN EXISTS_TAC `{u:real^N,v}` THEN
       ASM_REWRITE_TAC[IN_INSERT];
       MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_INSERT]])]);;

let MOI_FCV_CLOPEN_SIMPLEX = prove
 (`!(k:(real^N->bool)->bool) A L.
     open_in (subtopology euclidean (UNIONS k)) A /\
     closed_in (subtopology euclidean (UNIONS k)) A /\
     L IN k /\ convex L
     ==> L SUBSET A \/ L INTER A = {}`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `L INTER A:real^N->bool = {}` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONNECTED_SUBSET_CLOPEN THEN
  EXISTS_TAC `UNIONS k:real^N->bool` THEN ASM_SIMP_TAC[CONVEX_CONNECTED] THEN
  ASM SET_TAC[]);;

let MOI_FCV_SHEET_BASE = prove
 (`!(c:(real^N->bool)->bool) z v0 b.
     z2_cocycle c z ==> moi_fcv_sheet z v0 b v0 = b`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[moi_fcv_sheet] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `z:(real^N->bool)->bool`; `v0:real^N`]
    MOI_FCV_EDGE_NOT_SING) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[]);;

let MOI_FCV_LIFT_VERTEX = prove
 (`!(c:(real^N->bool)->bool) z (f:real^N#bool->real^N) (q:real^N->real^N) t v0 b v.
     simplicial_complex c /\ z2_cocycle c z /\
     abstract_realizes f (moi_fcv_lifts c z) /\
     (!s. s IN moi_fcv_lifts c z
          ==> ?l y. linear l /\ (!w. w IN s ==> l (f w) + y = FST w) /\
                    (!x. x IN convex hull (IMAGE f s) ==> q x = l x + y)) /\
     t IN moi_real_vertex_sets c /\ v0 IN t /\ v IN t
     ==> convex hull (IMAGE f (IMAGE (\u. u,moi_fcv_sheet z v0 b u) t)) IN abstract_realization f (moi_fcv_lifts c z) /\
         f (v,moi_fcv_sheet z v0 b v) IN
         convex hull (IMAGE f (IMAGE (\u. u,moi_fcv_sheet z v0 b u) t))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [REWRITE_TAC[MOI_FCV_IN_REALIZATION] THEN DISJ2_TAC THEN
    EXISTS_TAC `IMAGE (\u. u,moi_fcv_sheet z (v0:real^N) b u) t` THEN
    REWRITE_TAC[MOI_FCV_IN_LIFTS] THEN
    MAP_EVERY EXISTS_TAC [`t:real^N->bool`; `v0:real^N`; `b:bool`] THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_IMAGE] THEN
    EXISTS_TAC `(v:real^N),moi_fcv_sheet z v0 b v` THEN REWRITE_TAC[] THEN
    EXISTS_TAC `v:real^N` THEN ASM_REWRITE_TAC[]]);;

let MOI_FCV_CLOPEN_EDGE = prove
 (`!(c:(real^N->bool)->bool) z (f:real^N#bool->real^N) (q:real^N->real^N) A t u v b.
     simplicial_complex c /\ z2_cocycle c z /\
     abstract_realizes f (moi_fcv_lifts c z) /\
     (!s. s IN moi_fcv_lifts c z
          ==> ?l y. linear l /\ (!w. w IN s ==> l (f w) + y = FST w) /\
                    (!x. x IN convex hull (IMAGE f s) ==> q x = l x + y)) /\
     open_in (subtopology euclidean (UNIONS (abstract_realization f (moi_fcv_lifts c z)))) A /\
     closed_in (subtopology euclidean (UNIONS (abstract_realization f (moi_fcv_lifts c z)))) A /\
     t IN moi_real_vertex_sets c /\ u IN t /\ v IN t
     ==> (f(u,b) IN A <=> f(v,moi_fcv_sheet z u b v) IN A)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `z:(real^N->bool)->bool`;
                 `f:real^N#bool->real^N`; `q:real^N->real^N`; `t:real^N->bool`;
                 `u:real^N`; `b:bool`; `v:real^N`] MOI_FCV_LIFT_VERTEX) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `z:(real^N->bool)->bool`;
                 `f:real^N#bool->real^N`; `q:real^N->real^N`; `t:real^N->bool`;
                 `u:real^N`; `b:bool`; `u:real^N`] MOI_FCV_LIFT_VERTEX) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `z:(real^N->bool)->bool`; `u:real^N`; `b:bool`]
    MOI_FCV_SHEET_BASE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  ABBREV_TAC `L = convex hull (IMAGE (f:real^N#bool->real^N)
                    (IMAGE (\u'. u',moi_fcv_sheet z u b u') t))` THEN
  STRIP_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`abstract_realization (f:real^N#bool->real^N) (moi_fcv_lifts c z)`;
                 `A:real^N->bool`; `L:real^N->bool`] MOI_FCV_CLOPEN_SIMPLEX) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN EXPAND_TAC "L" THEN REWRITE_TAC[CONVEX_CONVEX_HULL];
    ASM SET_TAC[]]);;

let MOI_FCV_CLOPEN_SPLIT = prove
 (`!(c:(real^N->bool)->bool) z (f:real^N#bool->real^N) (q:real^N->real^N) A.
     simplicial_complex c /\ z2_cocycle c z /\
     abstract_realizes f (moi_fcv_lifts c z) /\
     (!s. s IN moi_fcv_lifts c z
          ==> ?l y. linear l /\ (!w. w IN s ==> l (f w) + y = FST w) /\
                    (!x. x IN convex hull (IMAGE f s) ==> q x = l x + y)) /\
     connected (UNIONS c) /\
     open_in (subtopology euclidean (UNIONS (abstract_realization f (moi_fcv_lifts c z)))) A /\
     closed_in (subtopology euclidean (UNIONS (abstract_realization f (moi_fcv_lifts c z)))) A /\
     ~(A = {}) /\ ~(A = UNIONS (abstract_realization f (moi_fcv_lifts c z)))
     ==> !v. {v} IN c ==> (f(v,T) IN A <=> ~(f(v,F) IN A))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!t u v. t IN moi_real_vertex_sets c /\ u IN t /\ v IN t
            ==> {(f:real^N#bool->real^N)(u,T) IN A, f(u,F) IN A} =
                {f(v,T) IN A, f(v,F) IN A}`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `z:(real^N->bool)->bool`;
                   `f:real^N#bool->real^N`; `q:real^N->real^N`; `A:real^N->bool`;
                   `t:real^N->bool`; `u:real^N`; `v:real^N`; `T`] MOI_FCV_CLOPEN_EDGE) THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `z:(real^N->bool)->bool`;
                   `f:real^N#bool->real^N`; `q:real^N->real^N`; `A:real^N->bool`;
                   `t:real^N->bool`; `u:real^N`; `v:real^N`; `F`] MOI_FCV_CLOPEN_EDGE) THEN
    ASM_REWRITE_TAC[MOI_FCV_SHEET_FLIP] THEN
    ASM_CASES_TAC `moi_fcv_sheet z (u:real^N) T v` THEN ASM_REWRITE_TAC[] THEN
    REPEAT(DISCH_THEN SUBST1_TAC) THEN REWRITE_TAC[INSERT_AC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`;
                 `\v:real^N. {(f:real^N#bool->real^N)(v,T) IN A, f(v,F) IN A}`]
    MOI_FCV_VERTEX_CONST) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "const") THEN
  SUBGOAL_THEN `(A:real^N->bool) SUBSET UNIONS (abstract_realization (f:real^N#bool->real^N) (moi_fcv_lifts (c:(real^N->bool)->bool) z))` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_IMP_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN UNIONS (abstract_realization (f:real^N#bool->real^N) (moi_fcv_lifts (c:(real^N->bool)->bool) z))
        ==> ?v0 b. {v0} IN c /\
                   (x IN A ==> (f:real^N#bool->real^N)(v0,b) IN A) /\
                   (~(x IN A) ==> ~(f(v0,b) IN A))`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^N` THEN REWRITE_TAC[IN_UNIONS] THEN
    DISCH_THEN(X_CHOOSE_THEN `L:real^N->bool` STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC `(L:real^N->bool) IN abstract_realization (f:real^N#bool->real^N)
                  (moi_fcv_lifts (c:(real^N->bool)->bool) z)` THEN
    GEN_REWRITE_TAC LAND_CONV [MOI_FCV_IN_REALIZATION] THEN
    DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC
      (X_CHOOSE_THEN `s:real^N#bool->bool` STRIP_ASSUME_TAC)) THENL
     [ASM_MESON_TAC[NOT_IN_EMPTY]; ALL_TAC] THEN
    UNDISCH_TAC `(s:real^N#bool->bool) IN moi_fcv_lifts (c:(real^N->bool)->bool) z` THEN
    GEN_REWRITE_TAC LAND_CONV [MOI_FCV_IN_LIFTS] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` (X_CHOOSE_THEN `v0:real^N`
      (X_CHOOSE_THEN `b:bool` STRIP_ASSUME_TAC))) THEN
    MAP_EVERY EXISTS_TAC [`v0:real^N`; `b:bool`] THEN CONJ_TAC THENL
     [MATCH_MP_TAC MOI_FCV_VERTEX_OF_SET THEN EXISTS_TAC `t:real^N->bool` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `z:(real^N->bool)->bool`;
                   `f:real^N#bool->real^N`; `q:real^N->real^N`; `t:real^N->bool`;
                   `v0:real^N`; `b:bool`; `v0:real^N`] MOI_FCV_LIFT_VERTEX) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `z:(real^N->bool)->bool`; `v0:real^N`;
                   `b:bool`] MOI_FCV_SHEET_BASE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`abstract_realization (f:real^N#bool->real^N) (moi_fcv_lifts c z)`;
                   `A:real^N->bool`; `L:real^N->bool`] MOI_FCV_CLOPEN_SIMPLEX) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[CONVEX_CONVEX_HULL];
      UNDISCH_TAC `(x:real^N) IN L` THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `?x:real^N. x IN A` (X_CHOOSE_TAC `x1:real^N`) THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `?x:real^N. x IN UNIONS (abstract_realization (f:real^N#bool->real^N) (moi_fcv_lifts (c:(real^N->bool)->bool) z)) /\ ~(x IN A)`
    (X_CHOOSE_TAC `x2:real^N`) THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `x1:real^N`) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x2:real^N`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `v2:real^N` (X_CHOOSE_THEN `b2:bool` STRIP_ASSUME_TAC)) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `v1:real^N` (X_CHOOSE_THEN `b1:bool` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `(f:real^N#bool->real^N)(v1,b1) IN A /\ ~(f(v2,b2) IN A)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `{(f:real^N#bool->real^N)(v,T) IN A, f(v,F) IN A} = {f(v1,T) IN A, f(v1,F) IN A} /\
    {(f:real^N#bool->real^N)(v,T) IN A, f(v,F) IN A} = {f(v2,T) IN A, f(v2,F) IN A}`
  MP_TAC THENL
   [CONJ_TAC THEN USE_THEN "const" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[EXTENSION; IN_INSERT; NOT_IN_EMPTY] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o SPEC `T`) (MP_TAC o SPEC `F`)) THEN
  UNDISCH_TAC `(f:real^N#bool->real^N)(v1,b1) IN A` THEN
  UNDISCH_TAC `~((f:real^N#bool->real^N)(v2,b2) IN A)` THEN
  MAP_EVERY BOOL_CASES_TAC [`b1:bool`; `b2:bool`] THEN CONV_TAC TAUT);;

let MOI_FCV_CONNECTED = prove
 (`!(c:(real^N->bool)->bool) z (f:real^N#bool->real^N) (q:real^N->real^N).
     simplicial_complex c /\ z2_cocycle c z /\
     abstract_realizes f (moi_fcv_lifts c z) /\
     (!s. s IN moi_fcv_lifts c z
          ==> ?l y. linear l /\ (!w. w IN s ==> l (f w) + y = FST w) /\
                    (!x. x IN convex hull (IMAGE f s) ==> q x = l x + y)) /\
     connected (UNIONS c) /\ ~z2_coboundary c z
     ==> connected (UNIONS (abstract_realization f (moi_fcv_lifts c z)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[CONNECTED_CLOPEN] THEN X_GEN_TAC `A:real^N->bool` THEN STRIP_TAC THEN
  ASM_CASES_TAC `A:real^N->bool = {}` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `z:(real^N->bool)->bool`;
                 `f:real^N#bool->real^N`; `q:real^N->real^N`; `A:real^N->bool`]
    MOI_FCV_CLOPEN_SPLIT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(LABEL_TAC "split")] THEN
  UNDISCH_TAC `~z2_coboundary (c:(real^N->bool)->bool) z` THEN
  REWRITE_TAC[z2_coboundary] THEN
  EXISTS_TAC `{v:real^N | {v} IN c /\ (f:real^N#bool->real^N)(v,T) IN A}` THEN
  X_GEN_TAC `e:real^N->bool` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `e:real^N->bool`] MOI_FCV_EDGE_FORM) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N` (X_CHOOSE_THEN `v:real^N` STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> lhs(concl th) = `e:real^N->bool`)) THEN
  SUBGOAL_THEN
   `{x | x IN {v:real^N | {v} IN c /\ (f:real^N#bool->real^N)(v,T) IN A} /\
         x IN convex hull {u,v} /\ {x} IN c} =
    {x | x IN {u,v} /\ (\x. f(x,T) IN A) x}`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:real^N` THEN
    REWRITE_TAC[IN_ELIM_THM] THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `u:real^N`; `v:real^N`; `x:real^N`]
      MOI_FCV_EDGE_VERTICES) THEN
    ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\x:real^N. (f:real^N#bool->real^N)(x,T) IN A`; `u:real^N`; `v:real^N`]
    MOI_FCV_ODD2) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN `{v:real^N} IN c` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FCV_VERTEX_OF_SET THEN EXISTS_TAC `{u:real^N,v}` THEN
    ASM_REWRITE_TAC[IN_INSERT];
    ALL_TAC] THEN
  USE_THEN "split" (MP_TAC o C MATCH_MP (ASSUME `{v:real^N} IN c`)) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `z:(real^N->bool)->bool`;
                 `f:real^N#bool->real^N`; `q:real^N->real^N`; `A:real^N->bool`;
                 `{u:real^N,v}`; `u:real^N`; `v:real^N`; `T`] MOI_FCV_CLOPEN_EDGE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[IN_INSERT]; ALL_TAC] THEN
  REWRITE_TAC[moi_fcv_sheet] THEN
  ASM_CASES_TAC `convex hull {u:real^N,v} IN z` THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC TAUT);;

(* ------------------------------------------------------------------------- *)
(* Lifts along a finite simplicial covering q: c' -> c (generic, from the    *)
(* sheet lemmas of pc_moi_lt_cova).  q maps the link of a vertex v of c' PL  *)
(* homeomorphically onto the link of q v (MOI_FCV_LINK_IMAGE,                *)
(* MOI_FCV_LINK_HOMEO: injective on the closed star, compact, piecewise      *)
(* affine), so combinatorial manifolds with boundary lift                    *)
(* (MOI_FCV_CMWB_LIFT); a coherent orientation sg of c lifts to sg o q       *)
(* (MOI_FCV_ORIENT_LIFT: a 3-simplex maps onto a 3-simplex, and the fourth   *)
(* vertices of two 3-simplices on a common 2-face have different images).    *)
(* ------------------------------------------------------------------------- *)

let MOI_FCV_IMAGE_HULL_AFFINE = prove
 (`!(q:real^M->real^N) l y s.
     linear l /\ (!x. x IN convex hull s ==> q x = l x + y)
     ==> IMAGE q (convex hull s) = convex hull (IMAGE q s)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `IMAGE (q:real^M->real^N) (convex hull s) =
                IMAGE (\x. l x + y) (convex hull s) /\
                IMAGE (q:real^M->real^N) s = IMAGE (\x. l x + y) s`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [CONJ_TAC THEN MATCH_MP_TAC(SET_RULE
     `(!x:real^M. x IN t ==> (q:real^M->real^N) x = g x) ==> IMAGE q t = IMAGE g t`) THEN
    ASM_SIMP_TAC[] THEN ASM_MESON_TAC[HULL_INC];
    ASM_SIMP_TAC[MOI_REAL_AFFINE_IMAGE_CONVEX_HULL]]);;

let MOI_FCV_CARD3_LE = prove
 (`!a b d e:A. CARD {a,b,d} <= 3 /\ CARD {a,b,d,e} <= 4`,
  REPEAT GEN_TAC THEN SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN
  REPEAT COND_CASES_TAC THEN REWRITE_TAC[NOT_IN_EMPTY] THEN ARITH_TAC);;

let MOI_FCV_AFF3_INDEP = prove
 (`!a b d e:real^N.
     aff_dim (convex hull {a,b,d,e}) = &3
     ==> ~affine_dependent {a,b,d,e} /\ ~(e IN {a,b,d})`,
  REPEAT GEN_TAC THEN REWRITE_TAC[AFF_DIM_CONVEX_HULL] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`a:real^N`; `b:real^N`; `d:real^N`; `e:real^N`] MOI_FCV_CARD3_LE) THEN
  STRIP_TAC THEN
  MP_TAC(ISPEC `{a:real^N,b,d,e}` AFF_DIM_LE_CARD) THEN
  MP_TAC(ISPEC `{a:real^N,b,d}` AFF_DIM_LE_CARD) THEN
  REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY] THEN ASM_REWRITE_TAC[] THEN
  REPEAT DISCH_TAC THEN CONJ_TAC THENL
   [REWRITE_TAC[AFFINE_INDEPENDENT_IFF_CARD; FINITE_INSERT; FINITE_EMPTY] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `CARD {a:real^N,b,d,e} <= 4` THEN
    UNDISCH_TAC `&3:int <= &(CARD {a:real^N,b,d,e}) - &1` THEN
    REWRITE_TAC[GSYM INT_OF_NUM_LE] THEN INT_ARITH_TAC;
    DISCH_TAC THEN
    SUBGOAL_THEN `{a:real^N,b,d,e} = {a,b,d}` SUBST_ALL_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `CARD {a:real^N,b,d} <= 3` THEN
    UNDISCH_TAC `aff_dim {a:real^N,b,d} <= &(CARD {a,b,d}) - &1` THEN
    UNDISCH_TAC `aff_dim {a:real^N,b,d} = &3` THEN
    REWRITE_TAC[GSYM INT_OF_NUM_LE] THEN INT_ARITH_TAC]);;

let MOI_FCV_COVER_SHEETS = prove
 (`!(c':(real^N->bool)->bool) (c:(real^N->bool)->bool) q.
     FINITE c' /\ lf_simplicial_complex c' /\ FINITE c /\ lf_simplicial_complex c /\
     simplicial_map_on c' c q /\ covering_space (UNIONS c',q) (UNIONS c)
     ==> simplicial_complex c' /\ simplicial_complex c /\
         (!L. L IN c' ==> !x y. x IN L /\ y IN L /\ q x = q y ==> x = y) /\
         (!L1 L2. L1 IN c' /\ L2 IN c' /\ IMAGE q L1 = IMAGE q L2 /\ ~DISJOINT L1 L2
                  ==> L1 = L2) /\
         (!y s. y IN UNIONS c' /\ s IN c /\ q y IN s
                ==> ?L. L IN c' /\ IMAGE q L = s /\ y IN L)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[MOI_SIMPLICIAL_COMPLEX_LF] THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `L:real^N->bool` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`c':(real^N->bool)->bool`; `c:(real^N->bool)->bool`; `q:real^N->real^N`;
                   `L:real^N->bool`] MOI_LCA_SIMPLEX_INJ) THEN
    ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_LCA_LIFT_UNIQUE THEN
    MAP_EVERY EXISTS_TAC [`c':(real^N->bool)->bool`; `c:(real^N->bool)->bool`;
                          `q:real^N->real^N`] THEN
    ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_LCA_POINT_LIFT THEN
    EXISTS_TAC `c:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[]]);;

let MOI_FCV_LINK_IMAGE = prove
 (`!(c':(real^N->bool)->bool) (c:(real^N->bool)->bool) q v.
     simplicial_complex c' /\ simplicial_complex c /\ simplicial_map_on c' c q /\
     (!L. L IN c' ==> !x y. x IN L /\ y IN L /\ q x = q y ==> x = y) /\
     (!L1 L2. L1 IN c' /\ L2 IN c' /\ IMAGE q L1 = IMAGE q L2 /\ ~DISJOINT L1 L2
              ==> L1 = L2) /\
     (!y s. y IN UNIONS c' /\ s IN c /\ q y IN s
            ==> ?L. L IN c' /\ IMAGE q L = s /\ y IN L) /\
     {v} IN c'
     ==> IMAGE q (UNIONS (simplicial_link c' v)) = UNIONS (simplicial_link c (q v))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "inj")
   (CONJUNCTS_THEN2 (LABEL_TAC "uniq") (CONJUNCTS_THEN2 (LABEL_TAC "pl")
      ASSUME_TAC)))))) THEN
  REWRITE_TAC[simplicial_link] THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_UNIONS; IN_ELIM_THM] THEN
    X_GEN_TAC `y:real^N` THEN
    DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` (CONJUNCTS_THEN2
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
        (X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC))) ASSUME_TAC)) THEN
    SUBGOAL_THEN `(s:real^N->bool) SUBSET t` ASSUME_TAC THENL
     [ASM_MESON_TAC[FACE_OF_IMP_SUBSET]; ALL_TAC] THEN
    SUBGOAL_THEN `IMAGE (q:real^N->real^N) s IN c /\ IMAGE q t IN c` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[simplicial_map_on]; ALL_TAC] THEN
    EXISTS_TAC `IMAGE (q:real^N->real^N) s` THEN ASM_SIMP_TAC[FUN_IN_IMAGE] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `y':real^N` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `(v:real^N) = y'` (fun th -> ASM_MESON_TAC[th]) THEN
      USE_THEN "inj" (MP_TAC o SPEC `t:real^N->bool`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    EXISTS_TAC `IMAGE (q:real^N->real^N) t` THEN ASM_SIMP_TAC[FUN_IN_IMAGE] THEN
    SUBGOAL_THEN `IMAGE (q:real^N->real^N) s = IMAGE q s INTER IMAGE q t` SUBST1_TAC THENL
     [ASM SET_TAC[]; ASM_MESON_TAC[simplicial_complex]];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM; IN_IMAGE] THEN
  X_GEN_TAC `z:real^N` THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` (CONJUNCTS_THEN2
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC))) ASSUME_TAC)) THEN
  USE_THEN "pl" (MP_TAC o SPECL [`v:real^N`; `t:real^N->bool`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_UNIONS] THEN ASM_MESON_TAC[IN_SING]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `L:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!x y. x IN L /\ y IN L /\ (q:real^N->real^N) x = q y ==> x = y`
  ASSUME_TAC THENL
   [USE_THEN "inj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c':(real^N->bool)->bool`; `c:(real^N->bool)->bool`; `q:real^N->real^N`;
                 `L:real^N->bool`; `s:real^N->bool`] MOI_FCV_FACE_LIFT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[FACE_OF_IMP_SUBSET]; ALL_TAC] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `?y:real^N. y IN {w | w IN L /\ (q:real^N->real^N) w IN s} /\ q y = z`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `IMAGE (q:real^N->real^N) {w | w IN L /\ q w IN s} = s` THEN
    REWRITE_TAC[EXTENSION; IN_IMAGE] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `y:real^N` THEN ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `{w | w IN L /\ (q:real^N->real^N) w IN s}` THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  EXISTS_TAC `L:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `{w | w IN L /\ (q:real^N->real^N) w IN s} =
                {w | w IN L /\ q w IN s} INTER L` SUBST1_TAC THENL
   [SET_TAC[]; ASM_MESON_TAC[simplicial_complex]]);;

let MOI_FCV_LINK_HOMEO = prove
 (`!(c':(real^N->bool)->bool) (c:(real^N->bool)->bool) q v.
     simplicial_complex c' /\ simplicial_complex c /\ simplicial_map_on c' c q /\
     (!L. L IN c' ==> !x y. x IN L /\ y IN L /\ q x = q y ==> x = y) /\
     (!L1 L2. L1 IN c' /\ L2 IN c' /\ IMAGE q L1 = IMAGE q L2 /\ ~DISJOINT L1 L2
              ==> L1 = L2) /\
     (!y s. y IN UNIONS c' /\ s IN c /\ q y IN s
            ==> ?L. L IN c' /\ IMAGE q L = s /\ y IN L) /\
     {v} IN c'
     ==> ?q'. pl_homeomorphism (UNIONS (simplicial_link c' v),
                                UNIONS (simplicial_link c (q v))) (q,q')`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `FINITE (simplicial_link (c':(real^N->bool)->bool) v) /\
                simplicial_link c' v SUBSET c'` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `q /\ (q ==> p) ==> p /\ q`) THEN CONJ_TAC THENL
     [REWRITE_TAC[simplicial_link] THEN SET_TAC[];
      DISCH_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `c':(real^N->bool)->bool` THEN ASM_MESON_TAC[simplicial_complex]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`q:real^N->real^N`; `simplicial_link (c':(real^N->bool)->bool) v`]
    MOI_REAL_PIECEWISE_AFFINE_UNIONS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `L:real^N->bool` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(L:real^N->bool) IN c'` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[MOI_FCV_SC_SIMPLEX]; ASM_MESON_TAC[simplicial_map_on]];
    STRIP_TAC] THEN
  MP_TAC(ISPECL [`UNIONS (simplicial_link (c':(real^N->bool)->bool) (v:real^N))`;
                 `q:real^N->real^N`;
                 `UNIONS (simplicial_link (c:(real^N->bool)->bool) ((q:real^N->real^N) v))`]
    HOMEOMORPHISM_COMPACT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_UNIONS THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[MOI_FCV_SC_SIMPLEX; SUBSET];
      MATCH_MP_TAC MOI_FCV_LINK_IMAGE THEN ASM_REWRITE_TAC[];
      MAP_EVERY X_GEN_TAC [`y1:real^N`; `y2:real^N`] THEN STRIP_TAC THEN
      MATCH_MP_TAC MOI_FCV_STAR_INJ THEN
      MAP_EVERY EXISTS_TAC [`c':(real^N->bool)->bool`; `c:(real^N->bool)->bool`;
                            `q:real^N->real^N`; `v:real^N`] THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(y1:real^N) IN UNIONS (simplicial_link c' (v:real^N))` THEN
      UNDISCH_TAC `(y2:real^N) IN UNIONS (simplicial_link c' (v:real^N))` THEN
      REWRITE_TAC[simplicial_link; IN_UNIONS; IN_ELIM_THM] THEN
      MESON_TAC[FACE_OF_IMP_SUBSET; SUBSET]];
    DISCH_THEN(X_CHOOSE_TAC `q':real^N->real^N`)] THEN
  EXISTS_TAC `q':real^N->real^N` THEN
  MATCH_MP_TAC HOMEOMORPHISM_IMP_PL_HOMEOMORPHISM THEN ASM_REWRITE_TAC[]);;

let MOI_FCV_CMWB_LIFT = prove
 (`!(c':(real^N->bool)->bool) (c:(real^N->bool)->bool) q n.
     FINITE c' /\ lf_simplicial_complex c' /\ FINITE c /\ lf_simplicial_complex c /\
     simplicial_map_on c' c q /\ covering_space (UNIONS c',q) (UNIONS c) /\
     combinatorial_manifold_with_boundary n c
     ==> combinatorial_manifold_with_boundary n c'`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)))))) THEN
  MP_TAC(ISPECL [`c':(real^N->bool)->bool`; `c:(real^N->bool)->bool`; `q:real^N->real^N`]
    MOI_FCV_COVER_SHEETS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  REWRITE_TAC[combinatorial_manifold_with_boundary] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "lk")) THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN
  SUBGOAL_THEN `{(q:real^N->real^N) v} IN c` ASSUME_TAC THENL
   [SUBGOAL_THEN `{(q:real^N->real^N) v} = IMAGE q {v}` SUBST1_TAC THENL
     [REWRITE_TAC[IMAGE_CLAUSES]; ASM_MESON_TAC[simplicial_map_on]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c':(real^N->bool)->bool`; `c:(real^N->bool)->bool`; `q:real^N->real^N`;
                 `v:real^N`] MOI_FCV_LINK_HOMEO) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `q':real^N->real^N` MP_TAC) THEN
  ONCE_REWRITE_TAC[PL_HOMEOMORPHISM_SYM] THEN DISCH_TAC THEN
  USE_THEN "lk" (MP_TAC o C MATCH_MP (ASSUME `{(q:real^N->real^N) v} IN c`)) THEN
  ASM_MESON_TAC[PL_SPHERE_PL_HOMEOMORPHIC; PL_BALL_PL_HOMEOMORPHIC]);;

let MOI_FCV_ORIENT_LIFT = prove
 (`!(c':(real^N->bool)->bool) (c:(real^N->bool)->bool) q.
     FINITE c' /\ lf_simplicial_complex c' /\ FINITE c /\ lf_simplicial_complex c /\
     simplicial_map_on c' c q /\ covering_space (UNIONS c',q) (UNIONS c) /\
     orientable_complex c
     ==> orientable_complex c'`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)))))) THEN
  REWRITE_TAC[orientable_complex] THEN
  DISCH_THEN(X_CHOOSE_THEN `sg:real^N->real^N->real^N->real^N->real`
    (CONJUNCTS_THEN2 (LABEL_TAC "s1") (LABEL_TAC "s2"))) THEN
  SUBGOAL_THEN
   `!a b d e:real^N.
      convex hull {a,b,d,e} IN c' /\ aff_dim (convex hull {a,b,d,e}) = &3
      ==> IMAGE (q:real^N->real^N) (convex hull {a,b,d,e}) =
          convex hull {q a,q b,q d,q e} /\
          convex hull {q a,q b,q d,q e} IN c /\
          aff_dim (convex hull {q a,q b,q d,q e}) = &3`
  (LABEL_TAC "img") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `IMAGE (q:real^N->real^N) (convex hull {a,b,d,e}) =
                  convex hull {q a,q b,q d,q e}` ASSUME_TAC THENL
     [SUBGOAL_THEN `?l y. linear l /\
                          !x. x IN convex hull {a,b,d,e} ==> (q:real^N->real^N) x = l x + y`
      STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[simplicial_map_on]; ALL_TAC] THEN
      MP_TAC(ISPECL [`q:real^N->real^N`; `l:real^N->real^N`; `y:real^N`;
                     `{a:real^N,b,d,e}`] MOI_FCV_IMAGE_HULL_AFFINE) THEN
      ASM_REWRITE_TAC[IMAGE_CLAUSES];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN CONJ_TAC THENL
     [ASM_MESON_TAC[simplicial_map_on];
      MP_TAC(ISPECL [`c':(real^N->bool)->bool`; `c:(real^N->bool)->bool`;
                     `q:real^N->real^N`; `convex hull {a:real^N,b,d,e}`] MOI_LCA_AFF_DIM) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  EXISTS_TAC `\a b d e. (sg:real^N->real^N->real^N->real^N->real)
                          ((q:real^N->real^N) a) (q b) (q d) (q e)` THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN USE_THEN "s1" MATCH_MP_TAC THEN
    USE_THEN "img" (MP_TAC o C MATCH_MP (ASSUME
     `convex hull {a:real^N,b,d,e} IN c' /\ aff_dim (convex hull {a,b,d,e}) = &3`)) THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real^N`; `d:real^N`; `e:real^N`; `e':real^N`] THEN
  STRIP_TAC THEN USE_THEN "s2" MATCH_MP_TAC THEN
  USE_THEN "img" (MP_TAC o C MATCH_MP (CONJ
    (ASSUME `convex hull {a:real^N,b,d,e} IN c'`)
    (ASSUME `aff_dim (convex hull {a:real^N,b,d,e}) = &3`))) THEN
  USE_THEN "img" (MP_TAC o C MATCH_MP (CONJ
    (ASSUME `convex hull {a:real^N,b,d,e'} IN c'`)
    (ASSUME `aff_dim (convex hull {a:real^N,b,d,e'}) = &3`))) THEN
  DISCH_THEN STRIP_ASSUME_TAC THEN DISCH_THEN STRIP_ASSUME_TAC THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `convex hull {a:real^N,b,d,e} = convex hull {a,b,d,e'}` MP_TAC THENL
   [MATCH_MP_TAC MOI_LCA_LIFT_UNIQUE THEN
    MAP_EVERY EXISTS_TAC [`c':(real^N->bool)->bool`; `c:(real^N->bool)->bool`;
                          `q:real^N->real^N`] THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[DISJOINT; GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
    EXISTS_TAC `a:real^N` THEN CONJ_TAC THEN MATCH_MP_TAC HULL_INC THEN
    REWRITE_TAC[IN_INSERT];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`a:real^N`; `b:real^N`; `d:real^N`; `e:real^N`] MOI_FCV_AFF3_INDEP) THEN
  MP_TAC(ISPECL [`a:real^N`; `b:real^N`; `d:real^N`; `e':real^N`] MOI_FCV_AFF3_INDEP) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `{a:real^N,b,d,e} = {a,b,d,e'}` MP_TAC THENL
   [MATCH_MP_TAC SIMPLEX_VERTICES_UNIQUE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `~((e:real^N) IN {a,b,d})` THEN UNDISCH_TAC `~((e:real^N) = e')` THEN
  SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* DOUBLE_COVER_OF_COCYCLE (Moise 24.6).  c is a finite simplicial complex   *)
(* with {} IN c (z is no coboundary, so c is nonempty); realize the lifts    *)
(* (MOI_FCV_REALIZES), take q simplexwise affine with q (f (v,b)) = v, and   *)
(* collect the results above; the boundary clause is COVER_BOUNDARY of       *)
(* pc_moi_lt_cova.                                                           *)
(* ------------------------------------------------------------------------- *)

let DOUBLE_COVER_OF_COCYCLE = prove
 (MOI_FND_DOUBLE_COVER_OF_COCYCLE,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `simplicial_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[MOI_SIMPLICIAL_COMPLEX_LF]; ALL_TAC] THEN
  SUBGOAL_THEN `{} IN (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_CASES_TAC `c:(real^N->bool)->bool = {}` THENL
     [UNDISCH_TAC `~z2_coboundary (c:(real^N->bool)->bool) z` THEN
      ASM_REWRITE_TAC[z2_coboundary; NOT_IN_EMPTY];
      FIRST_X_ASSUM(X_CHOOSE_TAC `s:real^N->bool` o REWRITE_RULE[GSYM MEMBER_NOT_EMPTY]) THEN
      ASM_MESON_TAC[simplicial_complex; EMPTY_FACE_OF]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `z:(real^N->bool)->bool`] MOI_FCV_REALIZES) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `f:real^N#bool->real^N`) THEN
  MP_TAC(ISPECL [`f:real^N#bool->real^N`; `FST:real^N#bool->real^N`;
                 `moi_fcv_lifts (c:(real^N->bool)->bool) z`] MOI_REAL_SIMPLEXWISE_AFFINE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `q:real^N->real^N`) THEN
  MAP_EVERY EXISTS_TAC
   [`abstract_realization (f:real^N#bool->real^N) (moi_fcv_lifts c z)`;
    `q:real^N->real^N`] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `z:(real^N->bool)->bool`;
                 `f:real^N#bool->real^N`; `q:real^N->real^N`] MOI_FCV_SIMPLICIAL_MAP) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `z:(real^N->bool)->bool`;
                 `f:real^N#bool->real^N`; `q:real^N->real^N`] MOI_FCV_INJECTIVE) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `z:(real^N->bool)->bool`;
                 `f:real^N#bool->real^N`; `q:real^N->real^N`] MOI_FCV_COVERING) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `z:(real^N->bool)->bool`;
                 `f:real^N#bool->real^N`; `q:real^N->real^N`] MOI_FCV_FIBRE2) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `z:(real^N->bool)->bool`;
                 `f:real^N#bool->real^N`; `q:real^N->real^N`] MOI_FCV_CONNECTED) THEN
  SUBGOAL_THEN `simplicial_complex (abstract_realization (f:real^N#bool->real^N)
                  (moi_fcv_lifts (c:(real^N->bool)->bool) z))` MP_TAC THENL
   [MATCH_MP_TAC ABSTRACT_REALIZATION_SIMPLICIAL_COMPLEX THEN
    ASM_SIMP_TAC[MOI_FCV_LIFTS_FINITE; MOI_FCV_LIFTS_ABSTRACT];
    ALL_TAC] THEN
  ABBREV_TAC `c' = abstract_realization (f:real^N#bool->real^N)
                     (moi_fcv_lifts (c:(real^N->bool)->bool) z)` THEN
  REWRITE_TAC[MOI_SIMPLICIAL_COMPLEX_LF] THEN ASM_REWRITE_TAC[] THEN
  REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `combinatorial_manifold_with_boundary 3 (c':(real^N->bool)->bool)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_FCV_CMWB_LIFT THEN
      MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `q:real^N->real^N`] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC COVER_BOUNDARY THEN ASM_REWRITE_TAC[];
    DISCH_TAC THEN MATCH_MP_TAC MOI_FCV_ORIENT_LIFT THEN
    MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `q:real^N->real^N`] THEN
    ASM_REWRITE_TAC[]]);;

