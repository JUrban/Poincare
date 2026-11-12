(* ========================================================================= *)
(* pc_moi_fnd1: small foundations of the Moise PL core: finiteness of        *)
(* subdivisions of finite complexes, connectedness of the 1-skeleton, vertex *)
(* degree at least 3 in combinatorial 3-manifolds with boundary, PL inverses *)
(* of injective PL maps on compact polyhedra, and pushing a PL 3-ball into   *)
(* its interior.  These prove the terms MOI_FND_FINITE_SUBDIVISION,          *)
(* MOI_FND_CONNECTED_SKELETON, MOI_FND_DEGREE_3, MOI_FND_PL_INVERSE and      *)
(* MOI_FND_PUSH_IN of pc_moi_core_stmt.ml.  Moise, Geometric Topology in     *)
(* Dimensions 2 and 3 (GTM 47): complexes p.3, subdivisions p.4, PL inverses *)
(* p.4, the no-end-point hypothesis of 33.1 (p.230), the start of the proof  *)
(* of 34.1 (p.239).                                                          *)
(* ========================================================================= *)

needs "src/pc_moi_core_stmt.ml";;
needs "src/pc_moi_assembly.ml";;
needs "src/pc_moi_polytope.ml";;
needs "src/pc_moi_cone.ml";;
needs "src/pc_moi_comb.ml";;
needs "src/pc_moi_star.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* 1. A PL injection of a compact polyhedron is a PL homeomorphism onto its *)
(* image (Moise p.4: the inverse of a PLH is PL).                            *)
(* ------------------------------------------------------------------------- *)

let PL_INJECTIVE_INVERSE = prove
 (`!(c:real^M->bool) (f:real^M->real^N).
     pl_polyhedron c /\ pl_map_on c f /\
     (!x y. x IN c /\ y IN c /\ f x = f y ==> x = y)
     ==> ?g. pl_homeomorphism (c,IMAGE f c) (f,g)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:real^M->bool`; `f:real^M->real^N`;
                 `IMAGE (f:real^M->real^N) c`] HOMEOMORPHISM_COMPACT) THEN
  ANTS_TAC THENL
   [ASM_MESON_TAC[PL_POLYHEDRON_IMP_COMPACT; PL_MAP_ON_IMP_CONTINUOUS_ON];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `g:real^N->real^M`) THEN
  EXISTS_TAC `g:real^N->real^M` THEN
  MATCH_MP_TAC HOMEOMORPHISM_IMP_PL_HOMEOMORPHISM THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* 2. A family of sets that is locally finite at the points of its union,   *)
(* with compact union, is finite; hence a locally finite subdivision of a   *)
(* finite complex is finite.                                                 *)
(* ------------------------------------------------------------------------- *)

let MOI_FN1_LF_COMPACT_FINITE = prove
 (`!c:(real^N->bool)->bool.
     compact (UNIONS c) /\
     (!x. x IN UNIONS c
          ==> ?u. open u /\ x IN u /\
                  FINITE {s | s IN c /\ ~(s INTER u = {})})
     ==> FINITE c`,
  GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [COMPACT_EQ_HEINE_BOREL]) THEN
  DISCH_THEN(MP_TAC o SPEC
   `{u:real^N->bool | open u /\
                      FINITE {s:real^N->bool | s IN c /\ ~(s INTER u = {})}}`) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM] THEN CONJ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N`) THEN
    ASM_REWRITE_TAC[IN_UNIONS] THEN MESON_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC
   `({}:real^N->bool) INSERT
    UNIONS (IMAGE (\u:real^N->bool.
                     {s:real^N->bool | s IN c /\ ~(s INTER u = {})}) f)` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[FINITE_INSERT; FINITE_UNIONS] THEN
    ASM_SIMP_TAC[FINITE_IMAGE; FORALL_IN_IMAGE] THEN
    X_GEN_TAC `u:real^N->bool` THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `(u:real^N->bool) IN
      {u:real^N->bool | open u /\
                        FINITE {s:real^N->bool | s IN c /\ ~(s INTER u = {})}}`
    MP_TAC THENL [ASM SET_TAC[]; SIMP_TAC[IN_ELIM_THM]];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET; IN_INSERT; IN_UNIONS; EXISTS_IN_IMAGE] THEN
  X_GEN_TAC `s:real^N->bool` THEN DISCH_TAC THEN
  ASM_CASES_TAC `s:real^N->bool = {}` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  DISCH_THEN(X_CHOOSE_TAC `x:real^N`) THEN
  SUBGOAL_THEN `(x:real^N) IN UNIONS f` MP_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
    REWRITE_TAC[IN_UNIONS] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[IN_UNIONS] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `u:real^N->bool` THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
  ASM SET_TAC[]);;

let SUBDIVISION_FINITE = prove
 (`!c c':(real^N->bool)->bool.
     FINITE c /\ lf_simplicial_complex c /\ lf_simplicial_complex c' /\
     subdivides c' c ==> FINITE c'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC MOI_FN1_LF_COMPACT_FINITE THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(fun th ->
      REWRITE_TAC[CONJUNCT1(GEN_REWRITE_RULE I [subdivides] th)]) THEN
    MATCH_MP_TAC COMPACT_UNIONS THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `lf_simplicial_complex (c:(real^N->bool)->bool)` THEN
    REWRITE_TAC[lf_simplicial_complex] THEN MESON_TAC[SIMPLEX_IMP_COMPACT];
    UNDISCH_TAC `lf_simplicial_complex (c':(real^N->bool)->bool)` THEN
    REWRITE_TAC[lf_simplicial_complex] THEN MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* 3. The 1-skeleton of a locally finite complex with connected polyhedron  *)
(* is connected.  The edges between the vertices of a simplex lie in the    *)
(* 1-skeleton, so a separation of the 1-skeleton puts all vertices of each  *)
(* simplex on one side; the simplices of the two sides then give a          *)
(* separation of the polyhedron by relatively closed sets (local            *)
(* finiteness).                                                              *)
(* ------------------------------------------------------------------------- *)

let MOI_FN1_SIMPLEX_HULL_FACE = prove
 (`!n (t:real^N->bool) a.
     n simplex t /\ (!x. x IN a ==> x extreme_point_of t)
     ==> (convex hull a) face_of t`,
  REPEAT GEN_TAC THEN REWRITE_TAC[simplex] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `v:real^N->bool` STRIP_ASSUME_TAC) ASSUME_TAC) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  ASM_SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
  EXISTS_TAC `a:real^N->bool` THEN REWRITE_TAC[SUBSET] THEN
  ASM_MESON_TAC[EXTREME_POINT_OF_CONVEX_HULL_AFFINE_INDEPENDENT]);;

let MOI_FN1_LF_EDGE_IN_SKELETON = prove
 (`!c s (w:real^N) w'.
     lf_simplicial_complex c /\ s IN c /\
     w extreme_point_of s /\ w' extreme_point_of s
     ==> segment[w,w'] IN skeleton 1 c`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[skeleton; IN_ELIM_THM] THEN CONJ_TAC THENL
   [SUBGOAL_THEN `?n. n simplex (s:real^N->bool)` (X_CHOOSE_TAC `n:int`) THENL
     [UNDISCH_TAC `lf_simplicial_complex (c:(real^N->bool)->bool)` THEN
      REWRITE_TAC[lf_simplicial_complex] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `segment[w:real^N,w'] face_of s` MP_TAC THENL
     [REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN
      MATCH_MP_TAC MOI_FN1_SIMPLEX_HULL_FACE THEN
      EXISTS_TAC `n:int` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN ASM_MESON_TAC[];
      UNDISCH_TAC `lf_simplicial_complex (c:(real^N->bool)->bool)` THEN
      REWRITE_TAC[lf_simplicial_complex] THEN ASM_MESON_TAC[]];
    REWRITE_TAC[AFF_DIM_SEGMENT] THEN COND_CASES_TAC THEN INT_ARITH_TAC]);;

let MOI_FN1_LF_CLOSED_IN_UNIONS = prove
 (`!c d:(real^N->bool)->bool.
     lf_simplicial_complex c /\ d SUBSET c
     ==> closed_in (subtopology euclidean (UNIONS c)) (UNIONS d)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC CLOSED_IN_LOCALLY_FINITE_UNIONS THEN CONJ_TAC THENL
   [X_GEN_TAC `s:real^N->bool` THEN DISCH_TAC THEN
    MATCH_MP_TAC CLOSED_SUBSET THEN CONJ_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `lf_simplicial_complex (c:(real^N->bool)->bool)` THEN
    REWRITE_TAC[lf_simplicial_complex] THEN
    ASM_MESON_TAC[SIMPLEX_IMP_CLOSED; SUBSET];
    ALL_TAC] THEN
  REWRITE_TAC[locally_finite_in; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
  CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  UNDISCH_TAC `lf_simplicial_complex (c:(real^N->bool)->bool)` THEN
  REWRITE_TAC[lf_simplicial_complex] THEN
  DISCH_THEN(MP_TAC o SPEC `x:real^N` o last o CONJUNCTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `UNIONS c INTER (u:real^N->bool)` THEN
  ASM_SIMP_TAC[OPEN_IN_OPEN_INTER; IN_INTER] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] FINITE_SUBSET)) THEN
  ASM SET_TAC[]);;

let MOI_FN1_CONNECTED_SEPARATION = prove
 (`!s t e1 e2:real^N->bool.
     connected t /\ t SUBSET s /\ open e1 /\ open e2 /\
     s SUBSET e1 UNION e2 /\ e1 INTER e2 INTER s = {}
     ==> e1 INTER t = {} \/ e2 INTER t = {}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[connected; NOT_EXISTS_THM] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`e1:real^N->bool`; `e2:real^N->bool`]) THEN
  ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

let MOI_FN1_SKEL_SIDE = prove
 (`!c e1 e2 s (w:real^N) w'.
     lf_simplicial_complex c /\ open e1 /\ open e2 /\
     UNIONS (skeleton 1 c) SUBSET e1 UNION e2 /\
     e1 INTER e2 INTER UNIONS (skeleton 1 c) = {} /\
     s IN c /\ w extreme_point_of s /\ w' extreme_point_of s /\ w IN e1
     ==> w' IN e1`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `segment[w:real^N,w'] IN skeleton 1 c` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FN1_LF_EDGE_IN_SKELETON]; ALL_TAC] THEN
  MP_TAC(ISPECL [`UNIONS (skeleton 1 (c:(real^N->bool)->bool))`;
                 `segment[w:real^N,w']`; `e1:real^N->bool`; `e2:real^N->bool`]
         MOI_FN1_CONNECTED_SEPARATION) THEN
  ASM_REWRITE_TAC[CONNECTED_SEGMENT] THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`w:real^N`; `w':real^N`] ENDS_IN_SEGMENT) THEN
  ASM SET_TAC[]);;

let MOI_FN1_SIMPLEX_EXTREME_EXISTS = prove
 (`!c s:real^N->bool.
     lf_simplicial_complex c /\ s IN c /\ ~(s = {})
     ==> ?w. w extreme_point_of s`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC EXTREME_POINT_EXISTS_CONVEX THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `lf_simplicial_complex (c:(real^N->bool)->bool)` THEN
  REWRITE_TAC[lf_simplicial_complex] THEN
  ASM_MESON_TAC[SIMPLEX_IMP_COMPACT; SIMPLEX_IMP_CONVEX]);;

let MOI_FN1_SKEL_NONEMPTY_SIDE = prove
 (`!c e1 e2:real^N->bool.
     lf_simplicial_complex c /\ open e1 /\ open e2 /\
     UNIONS (skeleton 1 c) SUBSET e1 UNION e2 /\
     e1 INTER e2 INTER UNIONS (skeleton 1 c) = {} /\
     ~(e1 INTER UNIONS (skeleton 1 c) = {})
     ==> ?s w. s IN c /\ w extreme_point_of s /\ w IN e1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  REWRITE_TAC[IN_INTER; IN_UNIONS] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:real^N` (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `(s:real^N->bool) IN c` ASSUME_TAC THENL
   [UNDISCH_TAC `(s:real^N->bool) IN skeleton 1 c` THEN
    SIMP_TAC[skeleton; IN_ELIM_THM];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `s:real^N->bool`]
    MOI_FN1_SIMPLEX_EXTREME_EXISTS) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `w:real^N`) THEN
  MAP_EVERY EXISTS_TAC [`s:real^N->bool`; `w:real^N`] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`UNIONS (skeleton 1 (c:(real^N->bool)->bool))`;
                 `s:real^N->bool`; `e1:real^N->bool`; `e2:real^N->bool`]
         MOI_FN1_CONNECTED_SEPARATION) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONVEX_CONNECTED THEN
      UNDISCH_TAC `lf_simplicial_complex (c:(real^N->bool)->bool)` THEN
      REWRITE_TAC[lf_simplicial_complex] THEN
      ASM_MESON_TAC[SIMPLEX_IMP_CONVEX];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  UNDISCH_TAC `(w:real^N) extreme_point_of s` THEN
  REWRITE_TAC[extreme_point_of] THEN ASM SET_TAC[]);;

let MOI_FN1_LF_COMMON_VERTEX = prove
 (`!c s1 s2 (x:real^N).
     lf_simplicial_complex c /\ s1 IN c /\ s2 IN c /\ x IN s1 /\ x IN s2
     ==> ?z. z extreme_point_of s1 /\ z extreme_point_of s2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(s1 INTER s2:real^N->bool) face_of s1 /\
                (s1 INTER s2:real^N->bool) face_of s2`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `lf_simplicial_complex (c:(real^N->bool)->bool)` THEN
    REWRITE_TAC[lf_simplicial_complex] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `compact (s1:real^N->bool) /\ convex (s1:real^N->bool)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `lf_simplicial_complex (c:(real^N->bool)->bool)` THEN
    REWRITE_TAC[lf_simplicial_complex] THEN
    ASM_MESON_TAC[SIMPLEX_IMP_COMPACT; SIMPLEX_IMP_CONVEX];
    ALL_TAC] THEN
  MP_TAC(ISPEC `s1 INTER s2:real^N->bool` EXTREME_POINT_EXISTS_CONVEX) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[FACE_OF_IMP_COMPACT];
      ASM_MESON_TAC[FACE_OF_IMP_CONVEX];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `z:real^N`) THEN EXISTS_TAC `z:real^N` THEN
  ASM_MESON_TAC[EXTREME_POINT_OF_FACE]);;

let SKELETON_1_CONNECTED = prove
 (`!c:(real^N->bool)->bool.
     lf_simplicial_complex c /\ connected (UNIONS c)
     ==> connected (UNIONS (skeleton 1 c))`,
  GEN_TAC THEN STRIP_TAC THEN
  GEN_REWRITE_TAC I [connected] THEN REWRITE_TAC[NOT_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`e1:real^N->bool`; `e2:real^N->bool`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `UNIONS (skeleton 1 c) SUBSET (e2:real^N->bool) UNION e1 /\
    e2 INTER e1 INTER UNIONS (skeleton 1 c) = {}`
  STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!s (w:real^N). s IN c /\ w extreme_point_of s
                   ==> w IN UNIONS (skeleton 1 c)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `s:real^N->bool`;
                   `w:real^N`; `w:real^N`] MOI_FN1_LF_EDGE_IN_SKELETON) THEN
    ASM_REWRITE_TAC[SEGMENT_REFL; IN_UNIONS] THEN MESON_TAC[IN_SING];
    ALL_TAC] THEN
  SUBGOAL_THEN `~connected (UNIONS c:real^N->bool)`
    (fun th -> ASM_MESON_TAC[th]) THEN
  REWRITE_TAC[CONNECTED_CLOSED_IN] THEN
  MAP_EVERY EXISTS_TAC
   [`UNIONS {s:real^N->bool | s IN c /\
                              ?w:real^N. w extreme_point_of s /\ w IN e1}`;
    `UNIONS {s:real^N->bool | s IN c /\
                              ?w:real^N. w extreme_point_of s /\ w IN e2}`] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MOI_FN1_LF_CLOSED_IN_UNIONS THEN ASM_REWRITE_TAC[] THEN
    SET_TAC[];
    MATCH_MP_TAC MOI_FN1_LF_CLOSED_IN_UNIONS THEN ASM_REWRITE_TAC[] THEN
    SET_TAC[];
    REWRITE_TAC[SUBSET; IN_UNIONS; IN_UNION; IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^N` THEN
    DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `s:real^N->bool`]
      MOI_FN1_SIMPLEX_EXTREME_EXISTS) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_TAC `w:real^N`) THEN
    SUBGOAL_THEN `(w:real^N) IN e1 \/ w IN e2` MP_TAC THENL
     [ASM SET_TAC[]; ASM_MESON_TAC[]];
    REWRITE_TAC[EXTENSION; IN_INTER; IN_UNIONS; IN_ELIM_THM; NOT_IN_EMPTY] THEN
    X_GEN_TAC `x:real^N` THEN
    DISCH_THEN(CONJUNCTS_THEN2
     (X_CHOOSE_THEN `s1:real^N->bool` (CONJUNCTS_THEN2
       (CONJUNCTS_THEN2 ASSUME_TAC
          (X_CHOOSE_THEN `w1:real^N` STRIP_ASSUME_TAC)) ASSUME_TAC))
     (X_CHOOSE_THEN `s2:real^N->bool` (CONJUNCTS_THEN2
       (CONJUNCTS_THEN2 ASSUME_TAC
          (X_CHOOSE_THEN `w2:real^N` STRIP_ASSUME_TAC)) ASSUME_TAC))) THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `s1:real^N->bool`;
                   `s2:real^N->bool`; `x:real^N`] MOI_FN1_LF_COMMON_VERTEX) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `z:real^N` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(z:real^N) IN e1` ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_FN1_SKEL_SIDE THEN
      MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `e2:real^N->bool`;
                            `s1:real^N->bool`; `w1:real^N`] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(z:real^N) IN e2` ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_FN1_SKEL_SIDE THEN
      MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `e1:real^N->bool`;
                            `s2:real^N->bool`; `w2:real^N`] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(z:real^N) IN UNIONS (skeleton 1 c)` MP_TAC THENL
     [ASM_MESON_TAC[]; ASM SET_TAC[]];
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `e1:real^N->bool`;
                   `e2:real^N->bool`] MOI_FN1_SKEL_NONEMPTY_SIDE) THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_UNIONS; IN_ELIM_THM] THEN
    MESON_TAC[extreme_point_of];
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `e2:real^N->bool`;
                   `e1:real^N->bool`] MOI_FN1_SKEL_NONEMPTY_SIDE) THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_UNIONS; IN_ELIM_THM] THEN
    MESON_TAC[extreme_point_of]]);;

(* ------------------------------------------------------------------------- *)
(* 4. Every vertex of a combinatorial 3-manifold with boundary has at least *)
(* three edges (no end-points, Moise 33.1 p.230 and p.73).  The link of v   *)
(* lies in the convex hull of the far ends w of the edges segment[v,w] at v *)
(* (one edge per far end), and a PL 2-sphere or PL 2-ball cannot lie in an  *)
(* affine set of dimension at most 1 (invariance of dimension on a          *)
(* 2-simplex, a facet of the 3-simplex in the sphere case).                 *)
(* ------------------------------------------------------------------------- *)

let MOI_FN1_EDGES_FINITE = prove
 (`!c (v:real^N).
     lf_simplicial_complex c /\ v IN UNIONS c
     ==> FINITE {e | e IN c /\ aff_dim e = &1 /\ v IN e}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `lf_simplicial_complex (c:(real^N->bool)->bool)` THEN
  REWRITE_TAC[lf_simplicial_complex] THEN
  DISCH_THEN(MP_TAC o SPEC `v:real^N` o last o CONJUNCTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N->bool` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] FINITE_SUBSET)) THEN
  ASM SET_TAC[]);;

let MOI_FN1_VERTEX_EXTREME = prove
 (`!c t (v:real^N).
     lf_simplicial_complex c /\ {v} IN c /\ t IN c /\ v IN t
     ==> v extreme_point_of t`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM FACE_OF_SING] THEN
  SUBGOAL_THEN `{v:real^N} = {v} INTER t` SUBST1_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `lf_simplicial_complex (c:(real^N->bool)->bool)` THEN
  REWRITE_TAC[lf_simplicial_complex] THEN ASM_MESON_TAC[]);;

let MOI_FN1_LINK_IN_HULL = prove
 (`!c (v:real^N).
     lf_simplicial_complex c /\ {v} IN c
     ==> UNIONS (simplicial_link c v) SUBSET
         convex hull {w | ~(w = v) /\ segment[v,w] IN c}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[UNIONS_SUBSET] THEN
  X_GEN_TAC `s:real^N->bool` THEN
  REWRITE_TAC[simplicial_link; IN_ELIM_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `?n. n simplex (s:real^N->bool)` (X_CHOOSE_TAC `m:int`) THENL
   [UNDISCH_TAC `lf_simplicial_complex (c:(real^N->bool)->bool)` THEN
    REWRITE_TAC[lf_simplicial_complex] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?n. n simplex (t:real^N->bool)` (X_CHOOSE_TAC `n:int`) THENL
   [UNDISCH_TAC `lf_simplicial_complex (c:(real^N->bool)->bool)` THEN
    REWRITE_TAC[lf_simplicial_complex] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(v:real^N) extreme_point_of t` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FN1_VERTEX_EXTREME]; ALL_TAC] THEN
  MP_TAC(ISPEC `s:real^N->bool` KREIN_MILMAN_MINKOWSKI) THEN
  ANTS_TAC THENL
   [ASM_MESON_TAC[SIMPLEX_IMP_CONVEX; SIMPLEX_IMP_COMPACT]; ALL_TAC] THEN
  DISCH_THEN(fun th -> GEN_REWRITE_TAC LAND_CONV [th]) THEN
  MATCH_MP_TAC HULL_MONO THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(x:real^N) extreme_point_of t /\ x IN s` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[EXTREME_POINT_OF_FACE]; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `segment[v:real^N,x] face_of t` MP_TAC THENL
   [REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN
    MATCH_MP_TAC MOI_FN1_SIMPLEX_HULL_FACE THEN
    EXISTS_TAC `n:int` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN ASM_MESON_TAC[];
    UNDISCH_TAC `lf_simplicial_complex (c:(real^N->bool)->bool)` THEN
    REWRITE_TAC[lf_simplicial_complex] THEN ASM_MESON_TAC[]]);;

let MOI_FN1_FAR_ENDS_CARD = prove
 (`!c (v:real^N).
     FINITE {e | e IN c /\ aff_dim e = &1 /\ v IN e}
     ==> FINITE {w | ~(w = v) /\ segment[v,w] IN c} /\
         CARD {w | ~(w = v) /\ segment[v,w] IN c} <=
         CARD {e | e IN c /\ aff_dim e = &1 /\ v IN e}`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!w w'. w IN {w | ~(w = v) /\ segment[v,w] IN c} /\
           w' IN {w | ~(w = v) /\ segment[v,w] IN c} /\
           segment[v:real^N,w] = segment[v,w'] ==> w = w'`
  ASSUME_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM; SEGMENT_EQ] THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (\w. segment[v:real^N,w]) {w | ~(w = v) /\ segment[v,w] IN c}
    SUBSET {e | e IN c /\ aff_dim e = &1 /\ v IN e}`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
    X_GEN_TAC `w:real^N` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[AFF_DIM_SEGMENT; ENDS_IN_SEGMENT];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\w. segment[v:real^N,w]`;
                 `{w | ~(w = v) /\ segment[v:real^N,w] IN c}`]
         FINITE_IMAGE_INJ_EQ) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN
  CONJ_TAC THENL [ASM_MESON_TAC[FINITE_SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`\w. segment[v:real^N,w]`;
                 `{w | ~(w = v) /\ segment[v:real^N,w] IN c}`]
         CARD_IMAGE_INJ) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`\w. segment[v:real^N,w]`;
                   `{w | ~(w = v) /\ segment[v:real^N,w] IN c}`]
           FINITE_IMAGE_INJ_EQ) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN
    ASM_MESON_TAC[FINITE_SUBSET];
    ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC CARD_SUBSET THEN ASM_REWRITE_TAC[]);;

let MOI_FN1_HOMEO_SIMPLEX_DIM = prove
 (`!(s:real^M->bool) (t:real^N->bool) f g a w n.
     homeomorphism (s,t) (f,g) /\ n simplex a /\ a SUBSET s /\
     t SUBSET affine hull w
     ==> n <= aff_dim w`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP AFF_DIM_SIMPLEX) THEN
  MATCH_MP_TAC INVARIANCE_OF_DIMENSION_CONVEX_DOMAIN THEN
  EXISTS_TAC `f:real^M->real^N` THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[SIMPLEX_IMP_CONVEX];
    ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
    ASM SET_TAC[];
    ASM_MESON_TAC[SUBSET]]);;

let MOI_FN1_SIMPLEX_FACET_IN_RF = prove
 (`!n k:real^N->bool.
     &(n + 1) simplex k ==> ?f. &n simplex f /\ f SUBSET relative_frontier k`,
  REPEAT GEN_TAC THEN REWRITE_TAC[simplex] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real^N->bool` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  SUBGOAL_THEN `FINITE (v:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[AFFINE_INDEPENDENT_IMP_FINITE]; ALL_TAC] THEN
  SUBGOAL_THEN `CARD (v:real^N->bool) = n + 2` ASSUME_TAC THENL
   [UNDISCH_TAC `&(CARD (v:real^N->bool)):int = &(n + 1) + &1` THEN
    REWRITE_TAC[INT_OF_NUM_ADD; INT_OF_NUM_EQ] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `?a:real^N. a IN v` (X_CHOOSE_TAC `a:real^N`) THENL
   [REWRITE_TAC[MEMBER_NOT_EMPTY] THEN DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `CARD ({}:real^N->bool) = n + 2` THEN
    REWRITE_TAC[CARD_CLAUSES] THEN ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `convex hull ((v:real^N->bool) DELETE a)` THEN CONJ_TAC THENL
   [EXISTS_TAC `(v:real^N->bool) DELETE a` THEN REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC AFFINE_INDEPENDENT_SUBSET THEN
      EXISTS_TAC `v:real^N->bool` THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
      ASM_SIMP_TAC[CARD_DELETE] THEN
      REWRITE_TAC[INT_OF_NUM_ADD; INT_OF_NUM_EQ] THEN ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC FACE_OF_SUBSET_RELATIVE_FRONTIER THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
    EXISTS_TAC `(v:real^N->bool) DELETE a` THEN REWRITE_TAC[DELETE_SUBSET];
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `affine_dependent (v:real^N->bool)`
    (fun th -> ASM_MESON_TAC[th]) THEN
  REWRITE_TAC[affine_dependent] THEN EXISTS_TAC `a:real^N` THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `(v:real^N->bool) DELETE a` CONVEX_HULL_SUBSET_AFFINE_HULL) THEN
  ASM_REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
  MATCH_MP_TAC HULL_INC THEN ASM_REWRITE_TAC[]);;

let MOI_FN1_PL_2_NOT_FLAT = prove
 (`!(s:real^N->bool) w.
     (pl_sphere 2 s \/ pl_ball 2 s) /\ s SUBSET affine hull w
     ==> &2 <= aff_dim w`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_sphere; pl_ball; pl_homeomorphism] THEN
  STRIP_TAC THENL
   [MP_TAC(ISPECL [`2`; `k:real^N->bool`] MOI_FN1_SIMPLEX_FACET_IN_RF) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `a:real^N->bool` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC(ISPECL
     [`relative_frontier k:real^N->bool`; `s:real^N->bool`;
      `f:real^N->real^N`; `g:real^N->real^N`; `a:real^N->bool`;
      `w:real^N->bool`; `&2:int`] MOI_FN1_HOMEO_SIMPLEX_DIM) THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC(ISPECL
     [`k:real^N->bool`; `s:real^N->bool`;
      `f:real^N->real^N`; `g:real^N->real^N`; `k:real^N->bool`;
      `w:real^N->bool`; `&2:int`] MOI_FN1_HOMEO_SIMPLEX_DIM) THEN
    ASM_REWRITE_TAC[SUBSET_REFL]]);;

let MOI_FN1_DEGREE_ARITH = prove
 (`!(w:real^N->bool) e.
     FINITE w /\ CARD w <= e /\ &2 <= aff_dim w ==> 3 <= e`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `w:real^N->bool` AFF_DIM_LE_CARD) THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `CARD (w:real^N->bool) <= e` THEN
  UNDISCH_TAC `&2 <= aff_dim (w:real^N->bool)` THEN
  REWRITE_TAC[GSYM INT_OF_NUM_LE] THEN INT_ARITH_TAC);;

let COMBINATORIAL_DEGREE_3 = prove
 (`!(c:(real^N->bool)->bool) v.
     combinatorial_manifold_with_boundary 3 c /\ {v} IN c
     ==> FINITE {e | e IN c /\ aff_dim e = &1 /\ v IN e} /\
         3 <= CARD {e | e IN c /\ aff_dim e = &1 /\ v IN e}`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[combinatorial_manifold_with_boundary; ARITH_RULE `3 - 1 = 2`] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `v:real^N`)) ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(v:real^N) IN UNIONS c` ASSUME_TAC THENL
   [REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `{v:real^N}` THEN
    ASM_REWRITE_TAC[IN_SING];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE {e | e IN c /\ aff_dim e = &1 /\ (v:real^N) IN e}`
  ASSUME_TAC THENL [ASM_MESON_TAC[MOI_FN1_EDGES_FINITE]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MOI_FN1_DEGREE_ARITH THEN
  EXISTS_TAC `{w | ~(w = v) /\ segment[v:real^N,w] IN c}` THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`]
    MOI_FN1_FAR_ENDS_CARD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MOI_FN1_PL_2_NOT_FLAT THEN
  EXISTS_TAC `UNIONS (simplicial_link c (v:real^N))` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_TRANS THEN
  EXISTS_TAC `convex hull {w | ~(w = v) /\ segment[v:real^N,w] IN c}` THEN
  REWRITE_TAC[CONVEX_HULL_SUBSET_AFFINE_HULL] THEN
  MATCH_MP_TAC MOI_FN1_LINK_IN_HULL THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* 5. A PL 3-ball can be pushed into its interior by a PL homeomorphism     *)
(* moving points less than e (the reduction at the start of the proof of    *)
(* Moise 34.1, p.239).  With c = f(k) for a 3-simplex k, conjugate by f a   *)
(* small shrink of k towards an interior point b; the shrink maps k into    *)
(* interior k, which f maps into interior c (invariance of domain), and     *)
(* uniform continuity of f on k controls the displacement.                  *)
(* ------------------------------------------------------------------------- *)

let MOI_FN1_PL_CONJ = prove
 (`!(c:real^M->bool) (k:real^N->bool) (f:real^N->real^M) g h.
     pl_map_on c g /\ pl_map_on k h /\ pl_map_on k f /\
     IMAGE g c SUBSET k /\ IMAGE h k SUBSET k
     ==> pl_map_on c (\x. f(h(g x)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\x. (f:real^N->real^M)(h(g x))) =
                (f o (h:real^N->real^N)) o (g:real^M->real^N)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC PL_MAP_ON_COMPOSE THEN EXISTS_TAC `k:real^N->bool` THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC PL_MAP_ON_COMPOSE THEN EXISTS_TAC `k:real^N->bool` THEN
  ASM_REWRITE_TAC[]);;

let MOI_FN1_HOMEOMORPHISM_INTERIOR = prove
 (`!(k:real^N->bool) (c:real^N->bool) (f:real^N->real^N) g.
     homeomorphism (k,c) (f,g) ==> IMAGE f (interior k) SUBSET interior c`,
  REPEAT GEN_TAC THEN REWRITE_TAC[homeomorphism] THEN STRIP_TAC THEN
  MATCH_MP_TAC INTERIOR_MAXIMAL THEN CONJ_TAC THENL
   [MP_TAC(ISPEC `k:real^N->bool` INTERIOR_SUBSET) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC INVARIANCE_OF_DOMAIN THEN REWRITE_TAC[OPEN_INTERIOR] THEN
  MP_TAC(ISPEC `k:real^N->bool` INTERIOR_SUBSET) THEN DISCH_TAC THEN
  CONJ_TAC THENL [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET]; ALL_TAC] THEN
  ASM_MESON_TAC[SUBSET]);;

let MOI_FN1_SIMPLEX_3_INTERIOR = prove
 (`!k:real^3->bool. &3 simplex k ==> ?b. b IN interior k`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[MEMBER_NOT_EMPTY] THEN
  MP_TAC(ISPEC `k:real^3->bool` AFF_DIM_NONEMPTY_INTERIOR_EQ) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[SIMPLEX_IMP_CONVEX]; ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[DIMINDEX_3] THEN ASM_MESON_TAC[AFF_DIM_SIMPLEX]);;

let MOI_FN1_SHRINK_FACTOR = prove
 (`!D d. &0 <= D /\ &0 < d
         ==> ?t. &0 < t /\ t < &1 /\ t * (D + &1) < d`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`&1`; `d / (D + &1)`] REAL_DOWN2) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `t:real` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 < D + &1` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_MESON_TAC[REAL_LT_RDIV_EQ]);;

let PL_BALL_PUSH_IN = prove
 (`!(c:real^3->bool) e.
     pl_ball 3 c /\ &0 < e
     ==> ?p q. pl_homeomorphism (c,IMAGE p c) (p,q) /\
               IMAGE p c SUBSET interior c /\
               !x. x IN c ==> dist(p x,x) < e`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  GEN_REWRITE_TAC LAND_CONV [pl_ball] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^3->bool` (X_CHOOSE_THEN `f:real^3->real^3`
    (X_CHOOSE_THEN `g:real^3->real^3` (CONJUNCTS_THEN2 ASSUME_TAC
      (STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [pl_homeomorphism]))))) THEN
  SUBGOAL_THEN `convex (k:real^3->bool) /\ compact (k:real^3->bool)`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[SIMPLEX_IMP_CONVEX; SIMPLEX_IMP_COMPACT]; ALL_TAC] THEN
  SUBGOAL_THEN `bounded (k:real^3->bool)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[COMPACT_IMP_BOUNDED]; ALL_TAC] THEN
  MP_TAC(ASSUME `homeomorphism (k:real^3->bool,c:real^3->bool)
                         (f:real^3->real^3,g:real^3->real^3)`) THEN
  REWRITE_TAC[homeomorphism] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `?d. &0 < d /\
        !y y'. y IN k /\ y' IN k /\ dist(y',y) < d
               ==> dist((f:real^3->real^3) y',f y) < e`
  (X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "uc"))) THENL
   [MP_TAC(ISPECL [`f:real^3->real^3`; `k:real^3->bool`]
      COMPACT_UNIFORMLY_CONTINUOUS) THEN
    ASM_REWRITE_TAC[uniformly_continuous_on] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `k:real^3->bool` MOI_FN1_SIMPLEX_3_INTERIOR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `b:real^3`) THEN
  SUBGOAL_THEN `(b:real^3) IN k` ASSUME_TAC THENL
   [ASM_MESON_TAC[INTERIOR_SUBSET; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`diameter (k:real^3->bool)`; `d:real`]
    MOI_FN1_SHRINK_FACTOR) THEN
  ASM_SIMP_TAC[DIAMETER_POS_LE] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!y:real^3. y IN k ==> (&1 - t) % y + t % b IN interior k`
  (LABEL_TAC "shrinkint") THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(&1 - t) % y + t % b = y - t % (y - b:real^3)`
    SUBST1_TAC THENL [VECTOR_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC IN_INTERIOR_CONVEX_SHRINK THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `t < &1` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^3. y IN k ==> (&1 - t) % y + t % b IN k`
  (LABEL_TAC "shrinkin") THENL
   [ASM_MESON_TAC[INTERIOR_SUBSET; SUBSET]; ALL_TAC] THEN
  EXISTS_TAC `\x:real^3. (f:real^3->real^3) ((&1 - t) % g x + t % b)` THEN
  MP_TAC(ISPECL
   [`c:real^3->bool`;
    `\x:real^3. (f:real^3->real^3) ((&1 - t) % g x + t % b)`]
   PL_INJECTIVE_INVERSE) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [SUBGOAL_THEN `c = IMAGE (f:real^3->real^3) k` SUBST1_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC PL_POLYHEDRON_PL_IMAGE THEN
      ASM_MESON_TAC[SIMPLEX_IMP_POLYTOPE; POLYTOPE_IMP_PL_POLYHEDRON];
      MP_TAC(ISPECL [`c:real^3->bool`; `k:real^3->bool`; `f:real^3->real^3`;
                     `g:real^3->real^3`; `\y:real^3. (&1 - t) % y + t % b`]
        MOI_FN1_PL_CONJ) THEN
      REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[SUBSET_REFL] THEN CONJ_TAC THENL
       [MP_TAC(ISPECL [`k:real^3->bool`; `\y:real^3. (&1 - t) % y`;
                       `t % b:real^3`] PL_MAP_ON_AFFINE) THEN
        REWRITE_TAC[LINEAR_SCALING] THEN ANTS_TAC THENL
         [ASM_MESON_TAC[LOCALLY_POLYHEDRAL_POLYTOPE; SIMPLEX_IMP_POLYTOPE];
          MESON_TAC[]];
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
        USE_THEN "shrinkin" (fun th -> MESON_TAC[th])];
      MAP_EVERY X_GEN_TAC [`x:real^3`; `y:real^3`] THEN REWRITE_TAC[] THEN
      STRIP_TAC THEN
      SUBGOAL_THEN `(g:real^3->real^3) x IN k /\ g y IN k` STRIP_ASSUME_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN
       `(&1 - t) % (g:real^3->real^3) x + t % b = (&1 - t) % g y + t % b`
      MP_TAC THENL
       [USE_THEN "shrinkin" (MP_TAC o SPEC `(g:real^3->real^3) x`) THEN
        USE_THEN "shrinkin" (MP_TAC o SPEC `(g:real^3->real^3) y`) THEN
        ASM_MESON_TAC[];
        ALL_TAC] THEN
      REWRITE_TAC[VECTOR_ARITH `a % x + z:real^N = a % y + z <=> a % x = a % y`;
                  VECTOR_MUL_LCANCEL] THEN
      SUBGOAL_THEN `~(&1 - t = &0)` (fun th -> REWRITE_TAC[th]) THENL
       [UNDISCH_TAC `t < &1` THEN REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `q:real^3->real^3`) THEN
  EXISTS_TAC `q:real^3->real^3` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
    X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`k:real^3->bool`; `c:real^3->bool`; `f:real^3->real^3`;
                   `g:real^3->real^3`] MOI_FN1_HOMEOMORPHISM_INTERIOR) THEN
    ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN DISCH_THEN MATCH_MP_TAC THEN
    USE_THEN "shrinkint" MATCH_MP_TAC THEN ASM SET_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(g:real^3->real^3) x IN k` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `dist((f:real^3->real^3)((&1 - t) % (g:real^3->real^3) x + t % b),
         f(g x)) < e`
  MP_TAC THENL
   [USE_THEN "uc" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [USE_THEN "shrinkin" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `dist((&1 - t) % (g:real^3->real^3) x + t % b,g x) =
      t * norm(b - g x)`
    SUBST1_TAC THENL
     [REWRITE_TAC[dist; VECTOR_ARITH
        `((&1 - t) % y + t % b) - y:real^N = t % (b - y)`; NORM_MUL] THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN
      UNDISCH_TAC `&0 < t` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`k:real^3->bool`; `b:real^3`; `(g:real^3->real^3) x`]
      DIAMETER_BOUNDED_BOUND) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `t * diameter(k:real^3->bool)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `&0 < t` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    UNDISCH_TAC `t * (diameter (k:real^3->bool) + &1) < d` THEN
    UNDISCH_TAC `&0 < t` THEN
    REWRITE_TAC[REAL_ADD_LDISTRIB; REAL_MUL_RID] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_MESON_TAC[]);;

