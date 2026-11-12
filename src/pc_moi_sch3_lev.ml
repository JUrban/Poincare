(* ========================================================================= *)
(* pc_moi_sch3_lev: the level sets of a generic height x |-> a dot x on a    *)
(* triangulated PL 2-sphere (Moise GTM 47, p.122).  Main theorems            *)
(* (statements in pc_moi_sch3_stmt.ml):                                      *)
(* INMOST, LEVEL_POLYGONS_FINITE, SINGULAR_POLYGONS, LEVEL_STABLE.           *)
(* Route: the level set at the level of a vertex v is the polyhedron of the  *)
(* 1-dimensional simplicial complex of slices of the triangles; every vertex *)
(* of it other than v lies in exactly two of its edges.  PL circles in such  *)
(* a graph are unions of edges and are separated off v (invariance of domain *)
(* on lines), which gives finiteness, uniqueness and, with walks along the   *)
(* graph, the loops through v (two edges at v each).  Stability uses a       *)
(* simplexwise affine homeomorphism between the level graphs of nearby       *)
(* directions; INMOST takes a level polygon with minimal inside in the level *)
(* plane.                                                                    *)
(* ========================================================================= *)

needs "src/pc_moi_sch3_stmt.ml";;
needs "src/pc_moi_sch3_s2.ml";;
needs "src/pc_moi_sch3_gen.ml";;
needs "src/pc_moi_ptri.ml";;
needs "src/pc_moi_sch3_free.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* 1. PL circles: simple closed parametrizations, no isolated points,        *)
(* connected after removing a point, and locally two-sided along a line     *)
(* (invariance of domain in dimension 1).                                    *)
(* ------------------------------------------------------------------------- *)

let MOI_SLV_CIRCLE_LOOP = prove
 (`!p:real^N->bool.
     pl_sphere 1 p
     ==> ?g. simple_path g /\ pathfinish g = pathstart g /\ path_image g = p`,
  GEN_TAC THEN REWRITE_TAC[pl_sphere] THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
    (X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC))) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [MOI_PL2_SIMPLEX_2]) THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^N` (X_CHOOSE_THEN `b:real^N`
    (X_CHOOSE_THEN `c:real^N` STRIP_ASSUME_TAC))) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  MP_TAC(ISPECL [`a:real^N`; `b:real^N`; `c:real^N`]
    MOI_PL2_TRIANGLE_POLYGON) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [pl_homeomorphism]) THEN
  ASM_SIMP_TAC[RELATIVE_FRONTIER_OF_TRIANGLE] THEN
  REWRITE_TAC[homeomorphism] THEN STRIP_TAC THEN
  EXISTS_TAC `(f:real^N->real^N) o polygonal_path[a:real^N;b;c;a]` THEN
  ASM_REWRITE_TAC[PATHSTART_COMPOSE; PATHFINISH_COMPOSE; PATH_IMAGE_COMPOSE] THEN
  MATCH_MP_TAC SIMPLE_PATH_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[]);;

let MOI_SLV_SHIFT_BASIC = prove
 (`!(g:real^1->real^N) a.
     simple_path g /\ pathfinish g = pathstart g /\ a IN interval[vec 0,vec 1]
     ==> simple_path (shiftpath a g) /\
         pathfinish (shiftpath a g) = pathstart (shiftpath a g) /\
         path_image (shiftpath a g) = path_image g`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_SIMP_TAC[SIMPLE_PATH_SHIFTPATH; PATH_IMAGE_SHIFTPATH] THEN
  SUBGOAL_THEN `&0 <= drop a /\ drop a <= &1` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[IN_INTERVAL_1; DROP_VEC]; ALL_TAC] THEN
  ASM_SIMP_TAC[PATHSTART_SHIFTPATH; PATHFINISH_SHIFTPATH]);;

let MOI_SLV_LOOP_SHIFT = prove
 (`!(g:real^1->real^N) x t.
     simple_path g /\ pathfinish g = pathstart g /\ x IN path_image g /\
     t IN interval[vec 0,vec 1]
     ==> ?h. simple_path h /\ pathfinish h = pathstart h /\
             path_image h = path_image g /\ h t = x`,
  REPEAT STRIP_TAC THEN
  UNDISCH_TAC `(x:real^N) IN path_image g` THEN
  REWRITE_TAC[path_image; IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real^1` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM SUBST1_TAC THEN REWRITE_TAC[GSYM path_image] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1; DROP_VEC]) THEN
  ASM_CASES_TAC `drop t <= drop s` THENL
   [EXISTS_TAC `shiftpath (s - t:real^1) (g:real^1->real^N)` THEN
    MP_TAC(ISPECL [`g:real^1->real^N`; `s - t:real^1`] MOI_SLV_SHIFT_BASIC) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[IN_INTERVAL_1; DROP_SUB; DROP_VEC] THEN ASM_REAL_ARITH_TAC;
      SIMP_TAC[]] THEN
    DISCH_THEN(K ALL_TAC) THEN REWRITE_TAC[shiftpath] THEN
    REWRITE_TAC[VECTOR_ARITH `(s - t) + t:real^1 = s`] THEN
    ASM_REWRITE_TAC[];
    EXISTS_TAC `shiftpath (s - t + vec 1:real^1) (g:real^1->real^N)` THEN
    MP_TAC(ISPECL [`g:real^1->real^N`; `s - t + vec 1:real^1`]
      MOI_SLV_SHIFT_BASIC) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[IN_INTERVAL_1; DROP_SUB; DROP_ADD; DROP_VEC] THEN
      ASM_REAL_ARITH_TAC;
      SIMP_TAC[]] THEN
    DISCH_THEN(K ALL_TAC) THEN REWRITE_TAC[shiftpath] THEN
    REWRITE_TAC[VECTOR_ARITH `(s - t + vec 1) + t:real^1 = s + vec 1`;
                VECTOR_ARITH `(s - t + vec 1) + (t - vec 1):real^1 = s`] THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `s:real^1 = vec 0` SUBST_ALL_TAC THENL
     [REWRITE_TAC[GSYM DROP_EQ; DROP_VEC] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[DROP_ADD; DROP_VEC]) THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[VECTOR_ADD_LID] THEN
    UNDISCH_TAC `pathfinish (g:real^1->real^N) = pathstart g` THEN
    REWRITE_TAC[pathstart; pathfinish] THEN MESON_TAC[]]);;

let MOI_SLV_CIRCLE_LIMPT = prove
 (`!p:real^N->bool x. pl_sphere 1 p /\ x IN p ==> x limit_point_of p`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `g:real^1->real^N` STRIP_ASSUME_TAC o
    MATCH_MP MOI_SLV_CIRCLE_LOOP) THEN
  MATCH_MP_TAC CONNECTED_IMP_PERFECT THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    ASM_MESON_TAC[CONNECTED_PATH_IMAGE; SIMPLE_PATH_IMP_PATH];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `z:real^N`) THEN
  SUBGOAL_THEN `(g:real^1->real^N) (vec 0) IN p /\ g (lift(&1 / &2)) IN p`
  MP_TAC THENL
   [FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC (BINOP_CONV o RAND_CONV)
      [SYM th]) THEN
    REWRITE_TAC[path_image] THEN
    CONJ_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
    REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; LIFT_DROP] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[IN_SING] THEN STRIP_TAC THEN
  UNDISCH_TAC `simple_path (g:real^1->real^N)` THEN REWRITE_TAC[simple_path] THEN
  DISCH_THEN(MP_TAC o SPECL [`vec 0:real^1`; `lift(&1 / &2)`] o CONJUNCT2) THEN
  ASM_REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; LIFT_DROP; GSYM DROP_EQ] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV);;

let MOI_SLV_CIRCLE_CLOSED = prove
 (`!p:real^N->bool. pl_sphere 1 p ==> compact p /\ closed p /\ connected p`,
  GEN_TAC THEN DISCH_THEN(X_CHOOSE_THEN `g:real^1->real^N` STRIP_ASSUME_TAC o
    MATCH_MP MOI_SLV_CIRCLE_LOOP) THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  ASM_MESON_TAC[COMPACT_PATH_IMAGE; CLOSED_PATH_IMAGE; CONNECTED_PATH_IMAGE;
                SIMPLE_PATH_IMP_PATH]);;

let MOI_SLV_CIRCLE_DELETE = prove
 (`!p:real^N->bool x. pl_sphere 1 p /\ x IN p ==> connected (p DELETE x)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `g0:real^1->real^N` STRIP_ASSUME_TAC o
    MATCH_MP MOI_SLV_CIRCLE_LOOP) THEN
  MP_TAC(ISPECL [`g0:real^1->real^N`; `x:real^N`; `vec 0:real^1`]
    MOI_SLV_LOOP_SHIFT) THEN
  ASM_REWRITE_TAC[ENDS_IN_UNIT_INTERVAL] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^1->real^N` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPEC `g:real^1->real^N` CONNECTED_SIMPLE_PATH_ENDLESS) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  REWRITE_TAC[pathstart] THEN ASM SET_TAC[]);;

(* Invariance of domain along a line: if near x the circle p lies in an    *)
(* affine set l of dimension at most 1, then p contains a neighbourhood of  *)
(* x in l (an open arc around x maps onto an open subset of l).            *)

let MOI_SLV_CIRCLE_LINE = prove
 (`!p:real^N->bool x l r.
     pl_sphere 1 p /\ x IN p /\ affine l /\ aff_dim l <= &1 /\ &0 < r /\
     p INTER ball(x,r) SUBSET l
     ==> ?e. &0 < e /\ l INTER ball(x,e) SUBSET p`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `g0:real^1->real^N` STRIP_ASSUME_TAC o
    MATCH_MP MOI_SLV_CIRCLE_LOOP) THEN
  MP_TAC(ISPECL [`g0:real^1->real^N`; `x:real^N`; `lift(&1 / &2)`]
    MOI_SLV_LOOP_SHIFT) THEN
  ASM_REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP; DROP_VEC] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^1->real^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(g:real^1->real^N) continuous_on interval[vec 0,vec 1]`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[SIMPLE_PATH_IMP_PATH; path]; ALL_TAC] THEN
  SUBGOAL_THEN
   `?d. &0 < d /\ d <= &1 / &2 /\
        !s. s IN interval[vec 0,vec 1] /\ dist(s,lift(&1 / &2)) < d
            ==> dist((g:real^1->real^N) s,x) < r`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(g:real^1->real^N) continuous_on interval[vec 0,vec 1]` THEN
    REWRITE_TAC[continuous_on] THEN
    DISCH_THEN(MP_TAC o SPEC `lift(&1 / &2)`) THEN
    REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP; DROP_VEC] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    DISCH_THEN(MP_TAC o SPEC `r:real`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `min d (&1 / &2)` THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `s:real^1` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `s:real^1`) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1; DROP_VEC]) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `i = interval(lift(&1 / &2 - d),lift(&1 / &2 + d))` THEN
  SUBGOAL_THEN
   `!s. s IN i ==> s IN interval[vec 0,vec 1] /\ dist(s,lift(&1 / &2)) < d /\
                   &0 < drop s /\ drop s < &1`
  ASSUME_TAC THENL
   [EXPAND_TAC "i" THEN X_GEN_TAC `s:real^1` THEN
    REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP; DROP_VEC; dist; NORM_1;
                DROP_SUB] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`g:real^1->real^N`; `(:real^1)`; `l:real^N->bool`;
                 `i:real^1->bool`] INVARIANCE_OF_DOMAIN_AFFINE_SETS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[AFFINE_UNIV; AFF_DIM_UNIV; DIMINDEX_1;
                    SUBTOPOLOGY_UNIV; GSYM OPEN_IN] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `interval[vec 0:real^1,vec 1]` THEN
      ASM_SIMP_TAC[SUBSET];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `s:real^1` THEN
      DISCH_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
      REWRITE_TAC[IN_INTER; IN_BALL] THEN CONJ_TAC THENL
       [FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th] THEN
          ASSUME_TAC th) THEN
        REWRITE_TAC[path_image] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
        ASM_SIMP_TAC[];
        ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_SIMP_TAC[]];
      MAP_EVERY X_GEN_TAC [`s:real^1`; `s':real^1`] THEN STRIP_TAC THEN
      UNDISCH_TAC `simple_path (g:real^1->real^N)` THEN
      REWRITE_TAC[simple_path] THEN
      DISCH_THEN(MP_TAC o SPECL [`s:real^1`; `s':real^1`] o CONJUNCT2) THEN
      ASM_SIMP_TAC[] THEN
      REWRITE_TAC[GSYM DROP_EQ; DROP_VEC] THEN
      MAP_EVERY (fun t -> FIRST_X_ASSUM(MP_TAC o SPEC t) THEN ASM_REWRITE_TAC[])
        [`s:real^1`; `s':real^1`] THEN
      REAL_ARITH_TAC;
      EXPAND_TAC "i" THEN REWRITE_TAC[OPEN_INTERVAL]];
    ALL_TAC] THEN
  REWRITE_TAC[OPEN_IN_CONTAINS_BALL] THEN
  DISCH_THEN(MP_TAC o SPEC `x:real^N` o CONJUNCT2) THEN ANTS_TAC THENL
   [REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `lift(&1 / &2)` THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "i" THEN
    REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `e:real` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC SUBSET_TRANS THEN
  EXISTS_TAC `IMAGE (g:real^1->real^N) i` THEN
  CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th] THEN
    ASSUME_TAC th) THEN
  REWRITE_TAC[path_image] THEN MATCH_MP_TAC IMAGE_SUBSET THEN
  ASM_SIMP_TAC[SUBSET]);;

(* ------------------------------------------------------------------------- *)
(* 2. PL circles in the polyhedron of a simplicial complex of dimension at  *)
(* most 1: they are unions of edges, finitely many, and pass through every *)
(* vertex they contain along at least two edges.                             *)
(* ------------------------------------------------------------------------- *)

let MOI_SLV_SC_BASIC = prove
 (`!K:(real^N->bool)->bool.
     simplicial_complex K
     ==> FINITE K /\
         (!t. t IN K ==> closed t /\ compact t /\ convex t /\ polytope t) /\
         (!f t. t IN K /\ f face_of t ==> f IN K) /\
         (!s t. s IN K /\ t IN K
                ==> (s INTER t) face_of s /\ (s INTER t) face_of t)`,
  GEN_TAC THEN REWRITE_TAC[simplicial_complex] THEN
  MESON_TAC[SIMPLEX_IMP_CLOSED; SIMPLEX_IMP_COMPACT; SIMPLEX_IMP_CONVEX;
            SIMPLEX_IMP_POLYTOPE]);;

let MOI_SLV_VERTICES_FINITE = prove
 (`!K:(real^N->bool)->bool. FINITE K ==> FINITE {v | {v} IN K}`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`\v:real^N. {v}`; `K:(real^N->bool)->bool`]
    FINITE_IMAGE_INJ) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN SET_TAC[]);;

let MOI_SLV_VERTEX_IN_SEGMENT = prove
 (`!K (x:real^N) u w.
     simplicial_complex K /\ {x} IN K /\ segment[u,w] IN K /\
     x IN segment[u,w]
     ==> x = u \/ x = w`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `{x:real^N} INTER segment[u,w] face_of segment[u,w]` MP_TAC
  THENL [ASM_MESON_TAC[MOI_SLV_SC_BASIC]; ALL_TAC] THEN
  SUBGOAL_THEN `{x:real^N} INTER segment[u,w] = {x}` SUBST1_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[FACE_OF_SING; EXTREME_POINT_OF_SEGMENT]);;

let MOI_SLV_EDGE = prove
 (`!K s:real^N->bool.
     simplicial_complex K /\ s IN K /\ aff_dim s = &1
     ==> ?u w. ~(u = w) /\ s = segment[u,w] /\ {u} IN K /\ {w} IN K`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `s:real^N->bool`] MOI_SCF_EDGE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N` (X_CHOOSE_THEN `w:real^N`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`u:real^N`; `w:real^N`] THEN
  ASM_REWRITE_TAC[GSYM SEGMENT_CONVEX_HULL] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SLV_SC_BASIC) THEN
  CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  EXISTS_TAC `s:real^N->bool` THEN
  ASM_REWRITE_TAC[FACE_OF_SING; GSYM SEGMENT_CONVEX_HULL;
                  EXTREME_POINT_OF_SEGMENT]);;

let MOI_SLV_SEGMENT_ENDS = prove
 (`!K (u:real^N) w.
     simplicial_complex K /\ segment[u,w] IN K ==> {u} IN K /\ {w} IN K`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SLV_SC_BASIC) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `segment[u:real^N,w]` THEN
  ASM_REWRITE_TAC[FACE_OF_SING; EXTREME_POINT_OF_SEGMENT]);;

let MOI_SLV_LOCAL_BALL = prove
 (`!K (x:real^N).
     FINITE K /\ (!t. t IN K ==> closed t)
     ==> ?r. &0 < r /\ !t. t IN K /\ ~(t INTER ball(x,r) = {}) ==> x IN t`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`UNIONS {t:real^N->bool | t IN K /\ ~(x IN t)}`; `x:real^N`]
    SEPARATE_POINT_CLOSED) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC CLOSED_UNIONS THEN
      ASM_SIMP_TAC[FINITE_RESTRICT; IN_ELIM_THM];
      REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN MESON_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `r:real` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `t:real^N->bool` THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_BALL] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC)) THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `y:real^N`) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN ASM_MESON_TAC[];
    ASM_REAL_ARITH_TAC]);;

(* The relative interior of an edge meets no other simplex and is open in   *)
(* the polyhedron.                                                          *)

let MOI_SLV_EDGE_RELINT = prove
 (`!K (u:real^N) w.
     simplicial_complex K /\ (!s. s IN K ==> aff_dim s <= &1) /\
     segment[u,w] IN K /\ ~(u = w)
     ==> (!t. t IN K /\ ~(t = segment[u,w]) ==> t INTER segment(u,w) = {}) /\
         open_in (subtopology euclidean (UNIONS K)) (segment(u,w))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SLV_SC_BASIC) THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
   [X_GEN_TAC `t:real^N->bool` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `segment[u:real^N,w]`;
                   `t:real^N->bool`] MOI_SCF_NOT_SUBSET_RELINT) THEN
    ASM_REWRITE_TAC[RELATIVE_INTERIOR_SEGMENT] THEN DISCH_THEN MATCH_MP_TAC THEN
    DISCH_TAC THEN UNDISCH_TAC `~(t = segment[u:real^N,w])` THEN
    REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC MOI_SCF_SUBSET_DIM_EQ THEN
    EXISTS_TAC `K:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(INT_ARITH `a:int <= b /\ b <= &1 /\ a = &1 ==> a = b`) THEN
    ASM_SIMP_TAC[AFF_DIM_SUBSET; AFF_DIM_SEGMENT];
    DISCH_THEN(LABEL_TAC "dis")] THEN
  MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `u:real^N`; `w:real^N`]
    MOI_SLV_SEGMENT_ENDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[OPEN_IN_CONTAINS_BALL] THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_UNIONS] THEN X_GEN_TAC `x:real^N` THEN
    DISCH_TAC THEN EXISTS_TAC `segment[u:real^N,w]` THEN
    ASM_MESON_TAC[SEGMENT_OPEN_SUBSET_CLOSED; SUBSET];
    ALL_TAC] THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `x:real^N`] MOI_SLV_LOCAL_BALL) THEN
  ASM_SIMP_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `r:real` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "lb")) THEN
  ASM_REWRITE_TAC[SUBSET; IN_INTER; IN_UNIONS] THEN
  X_GEN_TAC `y:real^N` THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `(x:real^N) IN t` ASSUME_TAC THENL
   [USE_THEN "lb" MATCH_MP_TAC THEN ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `t = segment[u:real^N,w]` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    USE_THEN "dis" (MP_TAC o SPEC `t:real^N->bool`) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(x:real^N = u) /\ ~(x = w)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(x:real^N) IN segment(u,w)` THEN
    REWRITE_TAC[open_segment; IN_DIFF; IN_INSERT; NOT_IN_EMPTY] THEN MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[open_segment; IN_DIFF; IN_INSERT; NOT_IN_EMPTY] THEN
  ASM_REWRITE_TAC[DE_MORGAN_THM] THEN
  CONJ_TAC THEN DISCH_TAC THENL
   [UNDISCH_TAC `~(x:real^N = u)`; UNDISCH_TAC `~(x:real^N = w)`] THEN
  REWRITE_TAC[GSYM IN_SING] THEN USE_THEN "lb" MATCH_MP_TAC THEN
  ASM SET_TAC[]);;

(* An edge whose relative interior meets a PL circle lies in it: the trace  *)
(* of the circle on the open edge is open (invariance of domain on the     *)
(* line of the edge) and closed.                                            *)

let MOI_SLV_CIRCLE_EDGE_ALL = prove
 (`!K p (u:real^N) w.
     simplicial_complex K /\ (!s. s IN K ==> aff_dim s <= &1) /\
     segment[u,w] IN K /\ ~(u = w) /\ pl_sphere 1 p /\ p SUBSET UNIONS K /\
     ~(p INTER segment(u,w) = {})
     ==> segment[u,w] SUBSET p`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `u:real^N`; `w:real^N`]
    MOI_SLV_EDGE_RELINT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SLV_CIRCLE_CLOSED) THEN
  SUBGOAL_THEN `segment(u:real^N,w) SUBSET affine hull {u,w}` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `segment[u:real^N,w]` THEN
    REWRITE_TAC[SEGMENT_OPEN_SUBSET_CLOSED; SEGMENT_CONVEX_HULL;
                CONVEX_HULL_SUBSET_AFFINE_HULL];
    ALL_TAC] THEN
  SUBGOAL_THEN `segment(u:real^N,w) SUBSET p` ASSUME_TAC THENL
   [ALL_TAC;
    MP_TAC(ISPECL [`segment(u:real^N,w)`; `p:real^N->bool`] CLOSURE_MINIMAL) THEN
    ASM_REWRITE_TAC[CLOSURE_SEGMENT]] THEN
  MP_TAC(ISPEC `segment(u:real^N,w)` CONNECTED_CLOPEN) THEN
  REWRITE_TAC[CONNECTED_SEGMENT] THEN
  DISCH_THEN(MP_TAC o SPEC `segment(u:real^N,w) INTER p`) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[OPEN_IN_CONTAINS_BALL; INTER_SUBSET] THEN
      X_GEN_TAC `x:real^N` THEN REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN
      UNDISCH_TAC
       `open_in (subtopology euclidean (UNIONS K)) (segment(u:real^N,w))` THEN
      REWRITE_TAC[OPEN_IN_CONTAINS_BALL] THEN
      DISCH_THEN(MP_TAC o SPEC `x:real^N` o CONJUNCT2) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
      MP_TAC(ISPECL [`p:real^N->bool`; `x:real^N`; `affine hull {u:real^N,w}`;
                     `r:real`] MOI_SLV_CIRCLE_LINE) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[AFFINE_AFFINE_HULL; AFF_DIM_AFFINE_HULL; AFF_DIM_2] THEN
        CONJ_TAC THENL [INT_ARITH_TAC; ASM SET_TAC[]];
        ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `e:real` THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      MATCH_MP_TAC CLOSED_IN_CLOSED_INTER THEN ASM_REWRITE_TAC[]];
    ASM SET_TAC[]]);;

(* Every point of a PL circle in a complex of dimension at most 1 lies in   *)
(* an edge contained in the circle (it is a limit of points of the circle  *)
(* that are not vertices).                                                  *)

let MOI_SLV_CIRCLE_EDGE_AT = prove
 (`!K p (x:real^N).
     simplicial_complex K /\ (!s. s IN K ==> aff_dim s <= &1) /\
     pl_sphere 1 p /\ p SUBSET UNIONS K /\ x IN p
     ==> ?s. s IN K /\ aff_dim s = &1 /\ x IN s /\ s SUBSET p`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SLV_SC_BASIC) THEN
  MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `x:real^N`] MOI_SLV_LOCAL_BALL) THEN
  ASM_SIMP_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (LABEL_TAC "lb"))) THEN
  SUBGOAL_THEN
   `?y:real^N. y IN p /\ y IN ball(x,r) /\ ~(y = x) /\ ~({y} IN K)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`p:real^N->bool`; `x:real^N`] MOI_SLV_CIRCLE_LIMPT) THEN
    ASM_REWRITE_TAC[LIMPT_INFINITE_OPEN] THEN
    DISCH_THEN(MP_TAC o SPEC `ball(x:real^N,r)`) THEN
    ASM_REWRITE_TAC[OPEN_BALL; CENTRE_IN_BALL] THEN
    MATCH_MP_TAC(TAUT `(~q ==> ~p) ==> p ==> q`) THEN
    REWRITE_TAC[NOT_EXISTS_THM; INFINITE] THEN DISCH_TAC THEN
    MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `(x:real^N) INSERT {y | {y} IN K}` THEN
    ASM_SIMP_TAC[FINITE_INSERT; MOI_SLV_VERTICES_FINITE] THEN
    REWRITE_TAC[SUBSET; IN_INTER; IN_INSERT; IN_ELIM_THM] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?t:real^N->bool. t IN K /\ y IN t` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^N) IN t` ASSUME_TAC THENL
   [USE_THEN "lb" MATCH_MP_TAC THEN ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `aff_dim(t:real^N->bool) = &1` ASSUME_TAC THENL
   [MATCH_MP_TAC(INT_ARITH `-- &1 <= a:int /\ a <= &1 /\ ~(a = &0) /\
                             ~(a = -- &1) ==> a = &1`) THEN
    ASM_SIMP_TAC[AFF_DIM_EQ_0; AFF_DIM_EQ_MINUS1; AFF_DIM_GE] THEN
    CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
    DISCH_THEN(X_CHOOSE_THEN `z:real^N` SUBST_ALL_TAC) THEN
    UNDISCH_TAC `~({y:real^N} IN K)` THEN
    SUBGOAL_THEN `y:real^N = z` (fun th -> ASM_REWRITE_TAC[th]) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `t:real^N->bool`] MOI_SLV_EDGE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N` (X_CHOOSE_THEN `w:real^N`
    STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  MATCH_MP_TAC MOI_SLV_CIRCLE_EDGE_ALL THEN
  EXISTS_TAC `K:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN EXISTS_TAC `y:real^N` THEN
  ASM_REWRITE_TAC[open_segment; IN_DIFF; IN_INSERT; NOT_IN_EMPTY] THEN
  ASM_MESON_TAC[]);;

let MOI_SLV_CIRCLE_EDGES = prove
 (`!K p:real^N->bool.
     simplicial_complex K /\ (!s. s IN K ==> aff_dim s <= &1) /\
     pl_sphere 1 p /\ p SUBSET UNIONS K
     ==> p = UNIONS {s | s IN K /\ aff_dim s = &1 /\ s SUBSET p}`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN
  X_GEN_TAC `x:real^N` THEN REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
  EQ_TAC THENL [ALL_TAC; MESON_TAC[SUBSET]] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `p:real^N->bool`; `x:real^N`]
    MOI_SLV_CIRCLE_EDGE_AT) THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

let MOI_SLV_CIRCLES_FINITE = prove
 (`!K:(real^N->bool)->bool.
     simplicial_complex K /\ (!s. s IN K ==> aff_dim s <= &1)
     ==> FINITE {p | pl_sphere 1 p /\ p SUBSET UNIONS K}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `IMAGE UNIONS {d | d SUBSET (K:(real^N->bool)->bool)}` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_IMAGE THEN MATCH_MP_TAC FINITE_POWERSET THEN
    ASM_MESON_TAC[MOI_SLV_SC_BASIC];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_IMAGE] THEN
  X_GEN_TAC `p:real^N->bool` THEN STRIP_TAC THEN
  EXISTS_TAC `{s:real^N->bool | s IN K /\ aff_dim s = &1 /\ s SUBSET p}` THEN
  CONJ_TAC THENL [ALL_TAC; SET_TAC[]] THEN
  MATCH_MP_TAC MOI_SLV_CIRCLE_EDGES THEN ASM_REWRITE_TAC[SUBSET]);;

(* Near a vertex x every other point of the polyhedron lies in the open    *)
(* part of an edge from x.                                                  *)

let MOI_SLV_LOCAL_EDGE = prove
 (`!K (x:real^N) r y.
     simplicial_complex K /\ (!s. s IN K ==> aff_dim s <= &1) /\ {x} IN K /\
     (!t. t IN K /\ ~(t INTER ball(x,r) = {}) ==> x IN t) /\
     y IN UNIONS K /\ y IN ball(x,r) /\ ~(y = x)
     ==> ?w. ~(w = x) /\ segment[x,w] IN K /\ y IN segment(x,w)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "lb")
      STRIP_ASSUME_TAC)))) THEN
  SUBGOAL_THEN `?t:real^N->bool. t IN K /\ y IN t` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^N) IN t` ASSUME_TAC THENL
   [USE_THEN "lb" MATCH_MP_TAC THEN ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `aff_dim(t:real^N->bool) = &1` ASSUME_TAC THENL
   [MATCH_MP_TAC(INT_ARITH `&1 <= a:int /\ a <= &1 ==> a = &1`) THEN
    ASM_SIMP_TAC[] THEN
    MP_TAC(ISPECL [`{x:real^N,y}`; `t:real^N->bool`] AFF_DIM_SUBSET) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[AFF_DIM_2] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `t:real^N->bool`] MOI_SLV_EDGE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N` (X_CHOOSE_THEN `w:real^N`
    STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `x:real^N`; `u:real^N`;
                 `w:real^N`] MOI_SLV_VERTEX_IN_SEGMENT) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!a b:real^N. ~(a = b) /\ segment[a,b] IN K /\ {b} IN K /\ a = x /\
                 y IN segment[a,b]
                 ==> ?w. ~(w = x) /\ segment[x,w] IN K /\ y IN segment(x,w)`
  (fun th -> STRIP_TAC THENL
    [MATCH_MP_TAC th THEN MAP_EVERY EXISTS_TAC [`u:real^N`; `w:real^N`] THEN
     ASM_REWRITE_TAC[];
     MATCH_MP_TAC th THEN MAP_EVERY EXISTS_TAC [`w:real^N`; `u:real^N`] THEN
     ONCE_REWRITE_TAC[SEGMENT_SYM] THEN ASM_REWRITE_TAC[]]) THEN
  MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real^N`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  EXISTS_TAC `b:real^N` THEN ASM_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[open_segment; IN_DIFF; IN_INSERT; NOT_IN_EMPTY] THEN
  DISCH_TAC THEN UNDISCH_TAC `~(x:real^N = b)` THEN REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM IN_SING] THEN USE_THEN "lb" MATCH_MP_TAC THEN
  ASM SET_TAC[]);;

(* A PL circle through a vertex x uses at least two edges at x: otherwise  *)
(* near x it would lie in one edge ending at x, against invariance of     *)
(* domain on the line of that edge.                                         *)

let MOI_SLV_CIRCLE_TWO_EDGES = prove
 (`!K p (x:real^N).
     simplicial_complex K /\ (!s. s IN K ==> aff_dim s <= &1) /\
     pl_sphere 1 p /\ p SUBSET UNIONS K /\ {x} IN K /\ x IN p
     ==> ?s1 s2. s1 IN K /\ s2 IN K /\ ~(s1 = s2) /\
                 aff_dim s1 = &1 /\ aff_dim s2 = &1 /\
                 x IN s1 /\ x IN s2 /\ s1 SUBSET p /\ s2 SUBSET p`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SLV_SC_BASIC) THEN
  MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `p:real^N->bool`; `x:real^N`]
    MOI_SLV_CIRCLE_EDGE_AT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s1:real^N->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `s1:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
  DISCH_THEN(LABEL_TAC "one" o REWRITE_RULE[NOT_EXISTS_THM]) THEN
  MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `s1:real^N->bool`] MOI_SLV_EDGE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N` (X_CHOOSE_THEN `w:real^N`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `?z:real^N. ~(z = x) /\ s1 = segment[x,z] /\ {z} IN K`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `x:real^N`; `u:real^N`;
                   `w:real^N`] MOI_SLV_VERTEX_IN_SEGMENT) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    STRIP_TAC THENL
     [EXISTS_TAC `w:real^N` THEN ASM_MESON_TAC[];
      EXISTS_TAC `u:real^N` THEN ASM_MESON_TAC[SEGMENT_SYM]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
    concl th = `s1 = segment[x:real^N,z]`)) THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
    concl th = `segment[x:real^N,z] = segment[u,w]`)) THEN
  SUBGOAL_THEN
   `!s2:real^N->bool. s2 IN K /\ aff_dim s2 = &1 /\ x IN s2 /\ s2 SUBSET p
                      ==> s2 = segment[x,z]`
  (LABEL_TAC "only") THENL
   [X_GEN_TAC `s2:real^N->bool` THEN STRIP_TAC THEN
    REMOVE_THEN "one" (MP_TAC o SPEC `s2:real^N->bool`) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `x:real^N`] MOI_SLV_LOCAL_BALL) THEN
  ASM_SIMP_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (LABEL_TAC "lb"))) THEN
  SUBGOAL_THEN `p INTER ball(x:real^N,r) SUBSET segment[x,z]` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_INTER] THEN X_GEN_TAC `y:real^N` THEN STRIP_TAC THEN
    ASM_CASES_TAC `y:real^N = x` THENL
     [ASM_REWRITE_TAC[ENDS_IN_SEGMENT]; ALL_TAC] THEN
    MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `x:real^N`; `r:real`; `y:real^N`]
      MOI_SLV_LOCAL_EDGE) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
      UNDISCH_TAC `(y:real^N) IN p` THEN
      UNDISCH_TAC `p SUBSET UNIONS (K:(real^N->bool)->bool)` THEN SET_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `v:real^N` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `segment[x:real^N,v] SUBSET p` ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_SLV_CIRCLE_EDGE_ALL THEN
      EXISTS_TAC `K:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
      EXISTS_TAC `y:real^N` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    USE_THEN "only" (MP_TAC o SPEC `segment[x:real^N,v]`) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[AFF_DIM_SEGMENT; ENDS_IN_SEGMENT] THEN
      SUBGOAL_THEN `~(x:real^N = v)` (fun th -> REWRITE_TAC[th]) THEN
      UNDISCH_TAC `~(v:real^N = x)` THEN MESON_TAC[];
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      ASM_MESON_TAC[SEGMENT_OPEN_SUBSET_CLOSED; SUBSET]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`p:real^N->bool`; `x:real^N`; `affine hull {x:real^N,z}`;
                 `r:real`] MOI_SLV_CIRCLE_LINE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[AFFINE_AFFINE_HULL; AFF_DIM_AFFINE_HULL; AFF_DIM_2] THEN
    CONJ_TAC THENL [TRY COND_CASES_TAC THEN INT_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `segment[x:real^N,z]` THEN
    CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC;
      REWRITE_TAC[SEGMENT_CONVEX_HULL; CONVEX_HULL_SUBSET_AFFINE_HULL]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `&0 < norm(z - x:real^N)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT; VECTOR_SUB_EQ]; ALL_TAC] THEN
  SUBGOAL_THEN
   `?d. &0 < d /\ d * norm(z - x:real^N) < e /\ d * norm(z - x) < r`
  STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `min e r / (&2 * norm(z - x:real^N))` THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_LT_MUL; REAL_LT_MIN;
                 REAL_ARITH `&0 < &2`;
                 REAL_FIELD `&0 < n ==> m / (&2 * n) * n = m / &2`] THEN
    MAP_EVERY UNDISCH_TAC [`&0 < e`; `&0 < r`] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(x - d % (z - x):real^N) IN p` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
      can (find_term ((=) `e:real`)) (concl th))) THEN
    REWRITE_TAC[IN_INTER; IN_BALL; NORM_ARITH
     `dist(x:real^N,x - d) = norm d`; NORM_MUL] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < d ==> abs d = d`] THEN
    REWRITE_TAC[AFFINE_HULL_2; IN_ELIM_THM] THEN
    MAP_EVERY EXISTS_TAC [`&1 + d`; `--d:real`] THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; VECTOR_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x - d % (z - x):real^N) IN segment[x,z]` MP_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
      can (find_term ((=) `r:real`)) (concl th) &&
      can (find_term ((=) `p:real^N->bool`)) (concl th))) THEN
    ASM_REWRITE_TAC[IN_INTER; IN_BALL; NORM_ARITH
     `dist(x:real^N,x - d) = norm d`; NORM_MUL] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < d ==> abs d = d`];
    ALL_TAC] THEN
  REWRITE_TAC[IN_SEGMENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(v + d) % (z - x:real^N) = vec 0` MP_TAC THENL
   [UNDISCH_TAC `x - d % (z - x):real^N = (&1 - v) % x + v % z` THEN
    VECTOR_ARITH_TAC;
    ASM_REWRITE_TAC[VECTOR_MUL_EQ_0; VECTOR_SUB_EQ] THEN ASM_REAL_ARITH_TAC]);;

(* Two distinct edges of a simplicial complex meet only in common ends.    *)

let MOI_SLV_SEGMENTS_INTER_LEFT = prove
 (`!K (a:real^N) b c d.
     simplicial_complex K /\ segment[a,b] IN K /\ segment[c,d] IN K /\
     ~(a = b) /\ ~(c = d) /\ ~(segment[a,b] = segment[c,d])
     ==> segment[a,b] INTER segment[c,d] SUBSET {a,b}`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SLV_SC_BASIC) THEN
  REWRITE_TAC[SUBSET; IN_INTER] THEN X_GEN_TAC `x:real^N` THEN STRIP_TAC THEN
  ASM_CASES_TAC `(x:real^N) IN segment(a,b)` THENL
   [ALL_TAC;
    UNDISCH_TAC `~((x:real^N) IN segment(a,b))` THEN
    UNDISCH_TAC `(x:real^N) IN segment[a,b]` THEN
    REWRITE_TAC[open_segment; IN_DIFF] THEN SET_TAC[]] THEN
  UNDISCH_TAC `~(segment[a:real^N,b] = segment[c,d])` THEN
  MATCH_MP_TAC(TAUT `p ==> ~p ==> q`) THEN
  MATCH_MP_TAC MOI_SCF_SUBSET_DIM_EQ THEN
  EXISTS_TAC `K:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[AFF_DIM_SEGMENT] THEN
  MATCH_MP_TAC SUBSET_TRANS THEN
  EXISTS_TAC `segment[a:real^N,b] INTER segment[c,d]` THEN
  REWRITE_TAC[INTER_SUBSET] THEN
  MATCH_MP_TAC SUBSET_OF_FACE_OF THEN
  EXISTS_TAC `segment[a:real^N,b]` THEN ASM_SIMP_TAC[SUBSET_REFL] THEN
  ASM_REWRITE_TAC[RELATIVE_INTERIOR_SEGMENT] THEN ASM SET_TAC[]);;

let MOI_SLV_SEGMENTS_INTER = prove
 (`!K (a:real^N) b c d.
     simplicial_complex K /\ segment[a,b] IN K /\ segment[c,d] IN K /\
     ~(a = b) /\ ~(c = d) /\ ~(segment[a,b] = segment[c,d])
     ==> segment[a,b] INTER segment[c,d] SUBSET {a,b} INTER {c,d}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SUBSET_INTER] THEN CONJ_TAC THENL
   [MATCH_MP_TAC MOI_SLV_SEGMENTS_INTER_LEFT THEN
    EXISTS_TAC `K:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
    ONCE_REWRITE_TAC[INTER_COMM] THEN
    MATCH_MP_TAC MOI_SLV_SEGMENTS_INTER_LEFT THEN
    EXISTS_TAC `K:(real^N->bool)->bool` THEN ASM_MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* 3. Graphs whose vertices other than v lie in exactly two edges: a PL      *)
(* circle minus v is open and closed in the polyhedron minus v, so two PL   *)
(* circles sharing a point other than v coincide.                           *)
(* ------------------------------------------------------------------------- *)

let moi_slv_graph2 = new_definition
 `moi_slv_graph2 (K:(real^N->bool)->bool) (v:real^N) <=>
    simplicial_complex K /\ (!s. s IN K ==> aff_dim s <= &1) /\
    !x. {x} IN K /\ ~(x = v)
        ==> {s | s IN K /\ aff_dim s = &1 /\ x IN s} HAS_SIZE 2`;;

let MOI_SLV_G2_EDGES_AT = prove
 (`!K (v:real^N) x s1 s2 t.
     moi_slv_graph2 K v /\ {x} IN K /\ ~(x = v) /\
     s1 IN K /\ s2 IN K /\ ~(s1 = s2) /\ aff_dim s1 = &1 /\ aff_dim s2 = &1 /\
     x IN s1 /\ x IN s2 /\ t IN K /\ aff_dim t = &1 /\ x IN t
     ==> t = s1 \/ t = s2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_slv_graph2] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[MOI_SCF_HAS_SIZE_2] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^N->bool` (X_CHOOSE_THEN `b:real^N->bool`
    STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [EXTENSION]) THEN
  REWRITE_TAC[IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY] THEN
  DISCH_THEN(fun th -> MP_TAC(SPEC `s1:real^N->bool` th) THEN
    MP_TAC(SPEC `s2:real^N->bool` th) THEN MP_TAC(SPEC `t:real^N->bool` th)) THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

let MOI_SLV_CIRCLE_DELETE_ANY = prove
 (`!p (v:real^N). pl_sphere 1 p ==> connected (p DELETE v)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `(v:real^N) IN p` THENL
   [ASM_MESON_TAC[MOI_SLV_CIRCLE_DELETE];
    ASM_SIMP_TAC[SET_RULE `~((v:A) IN p) ==> p DELETE v = p`] THEN
    ASM_MESON_TAC[MOI_SLV_CIRCLE_CLOSED]]);;

let MOI_SLV_CIRCLE_DELETE_EQ = prove
 (`!p q (v:real^N).
     pl_sphere 1 p /\ pl_sphere 1 q /\ p DELETE v = q DELETE v ==> p = q`,
  SUBGOAL_THEN
   `!p q (v:real^N).
      pl_sphere 1 p /\ pl_sphere 1 q /\ p DELETE v = q DELETE v ==> p SUBSET q`
  (fun th -> MESON_TAC[th; SUBSET_ANTISYM]) THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:real^N` THEN
  DISCH_TAC THEN ASM_CASES_TAC `x:real^N = v` THENL
   [ALL_TAC; ASM SET_TAC[]] THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT1 o CONJUNCT2 o
    MATCH_MP MOI_SLV_CIRCLE_CLOSED o
    check (fun th -> concl th = `pl_sphere 1 (q:real^N->bool)`)) THEN
  REWRITE_TAC[CLOSED_LIMPT] THEN DISCH_THEN MATCH_MP_TAC THEN
  MATCH_MP_TAC LIMPT_SUBSET THEN EXISTS_TAC `q DELETE (v:real^N)` THEN
  REWRITE_TAC[DELETE_SUBSET] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[LIMPT_DELETE] THEN
  MATCH_MP_TAC MOI_SLV_CIRCLE_LIMPT THEN ASM_REWRITE_TAC[]);;

let MOI_SLV_G2_CLOPEN = prove
 (`!K (v:real^N) p.
     moi_slv_graph2 K v /\ pl_sphere 1 p /\ p SUBSET UNIONS K
     ==> open_in (subtopology euclidean (UNIONS K DELETE v)) (p DELETE v) /\
         closed_in (subtopology euclidean (UNIONS K DELETE v)) (p DELETE v)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_slv_graph2]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SLV_SC_BASIC) THEN
  CONJ_TAC THENL
   [ALL_TAC;
    SUBGOAL_THEN `p DELETE (v:real^N) = (UNIONS K DELETE v) INTER p`
    SUBST1_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC CLOSED_IN_CLOSED_INTER THEN
    ASM_MESON_TAC[MOI_SLV_CIRCLE_CLOSED]] THEN
  REWRITE_TAC[OPEN_IN_CONTAINS_BALL] THEN
  CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `x:real^N` THEN REWRITE_TAC[IN_DELETE] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `?e. &0 < e /\ ball(x:real^N,e) INTER UNIONS K SUBSET p`
  MP_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC MONO_EXISTS THEN SET_TAC[]] THEN
  ASM_CASES_TAC `{x:real^N} IN K` THENL
   [MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `p:real^N->bool`; `x:real^N`]
      MOI_SLV_CIRCLE_TWO_EDGES) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `s1:real^N->bool` (X_CHOOSE_THEN
      `s2:real^N->bool` STRIP_ASSUME_TAC)) THEN
    MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `x:real^N`] MOI_SLV_LOCAL_BALL) THEN
    ASM_SIMP_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real` (CONJUNCTS_THEN2 ASSUME_TAC
      (LABEL_TAC "lb"))) THEN
    EXISTS_TAC `r:real` THEN ASM_REWRITE_TAC[SUBSET; IN_INTER] THEN
    X_GEN_TAC `y:real^N` THEN STRIP_TAC THEN
    ASM_CASES_TAC `y:real^N = x` THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `x:real^N`; `r:real`; `y:real^N`]
      MOI_SLV_LOCAL_EDGE) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC);
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `v:real^N`; `x:real^N`;
                   `s1:real^N->bool`; `s2:real^N->bool`; `segment[x:real^N,w]`]
      MOI_SLV_G2_EDGES_AT) THEN
    ASM_REWRITE_TAC[AFF_DIM_SEGMENT; ENDS_IN_SEGMENT] THEN
    SUBGOAL_THEN `~(x:real^N = w)` (fun th -> REWRITE_TAC[th]) THENL
     [UNDISCH_TAC `~(w:real^N = x)` THEN MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(y:real^N) IN segment[x,w]` MP_TAC THENL
     [ASM_MESON_TAC[SEGMENT_OPEN_SUBSET_CLOSED; SUBSET]; ALL_TAC] THEN
    UNDISCH_TAC `(s1:real^N->bool) SUBSET p` THEN
    UNDISCH_TAC `(s2:real^N->bool) SUBSET p` THEN
    SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `p:real^N->bool`; `x:real^N`]
    MOI_SLV_CIRCLE_EDGE_AT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `s:real^N->bool`] MOI_SLV_EDGE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N` (X_CHOOSE_THEN `w:real^N`
    STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `u:real^N`; `w:real^N`]
    MOI_SLV_EDGE_RELINT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o CONJUNCT2) THEN REWRITE_TAC[OPEN_IN_CONTAINS_BALL] THEN
  DISCH_THEN(MP_TAC o SPEC `x:real^N` o CONJUNCT2) THEN ANTS_TAC THENL
   [REWRITE_TAC[open_segment; IN_DIFF; IN_INSERT; NOT_IN_EMPTY] THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `e:real` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`u:real^N`; `w:real^N`] SEGMENT_OPEN_SUBSET_CLOSED) THEN
  ASM SET_TAC[]);;

let MOI_SLV_G2_UNIQUE = prove
 (`!K (v:real^N) p q x.
     moi_slv_graph2 K v /\ pl_sphere 1 p /\ pl_sphere 1 q /\
     p SUBSET UNIONS K /\ q SUBSET UNIONS K /\ x IN p /\ x IN q /\ ~(x = v)
     ==> p = q`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_SLV_CIRCLE_DELETE_EQ THEN
  EXISTS_TAC `v:real^N` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `v:real^N`; `p:real^N->bool`]
    MOI_SLV_G2_CLOPEN) THEN
  MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `v:real^N`; `q:real^N->bool`]
    MOI_SLV_G2_CLOPEN) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THEN
  MATCH_MP_TAC CONNECTED_SUBSET_CLOPEN THEN
  EXISTS_TAC `UNIONS K DELETE (v:real^N)` THEN
  ASM_SIMP_TAC[MOI_SLV_CIRCLE_DELETE_ANY] THEN ASM SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* 4. Walks in finite graphs of degree at most 2 (the longest injective     *)
(* path from a vertex of degree 1 ends at another vertex of degree 1), and *)
(* polygons through distinct vertices of a simplicial complex.              *)
(* ------------------------------------------------------------------------- *)

let MOI_SLV_WALK = prove
 (`!(V:A->bool) R x0.
     FINITE V /\ x0 IN V /\ (!x y. R x y ==> R y x) /\ (!x. ~R x x) /\
     (!x y z w. x IN V /\ y IN V /\ z IN V /\ w IN V /\
                R x y /\ R x z /\ R x w ==> y = z \/ y = w \/ z = w) /\
     (?y. y IN V /\ R x0 y /\ !z. z IN V /\ R x0 z ==> z = y)
     ==> ?k W. moi_scf_path V R x0 k W /\ 1 <= k /\
               (!z. z IN V /\ R (W k) z ==> z = W(k - 1))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "sym") (CONJUNCTS_THEN2 (LABEL_TAC "irr")
      (CONJUNCTS_THEN2 (LABEL_TAC "two")
        (X_CHOOSE_THEN `y0:A` (CONJUNCTS_THEN2 ASSUME_TAC
          (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "one"))))))))) THEN
  MP_TAC(ISPEC `\k. ?W:num->A. moi_scf_path V R x0 k W` num_MAX) THEN
  REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `a /\ (b ==> c) ==> (a <=> b) ==> c`) THEN CONJ_TAC THENL
   [CONJ_TAC THENL
     [EXISTS_TAC `0` THEN EXISTS_TAC `\i:num. (x0:A)` THEN
      REWRITE_TAC[moi_scf_path; LE; LT] THEN ASM_MESON_TAC[];
      EXISTS_TAC `CARD(V:A->bool)` THEN X_GEN_TAC `k:num` THEN
      DISCH_THEN(X_CHOOSE_TAC `W:num->A`) THEN
      MATCH_MP_TAC LT_IMP_LE THEN MATCH_MP_TAC MOI_SCF_PATH_BOUND THEN
      MAP_EVERY EXISTS_TAC [`R:A->A->bool`; `x0:A`; `W:num->A`] THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` (CONJUNCTS_THEN2
    (X_CHOOSE_TAC `W:num->A`) (LABEL_TAC "max"))) THEN
  EXISTS_TAC `k:num` THEN EXISTS_TAC `W:num->A` THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [moi_scf_path]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "W0") (CONJUNCTS_THEN2
    (LABEL_TAC "WV") (CONJUNCTS_THEN2 (LABEL_TAC "WR") (LABEL_TAC "Winj")))) THEN
  SUBGOAL_THEN `!u:A. u IN V /\ R ((W:num->A) k) u ==> ?i. i <= k /\ W i = u`
  (LABEL_TAC "onpath") THENL
   [X_GEN_TAC `u:A` THEN STRIP_TAC THEN
    MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
    DISCH_THEN(ASSUME_TAC o
      REWRITE_RULE[NOT_EXISTS_THM; TAUT `~(a /\ b) <=> a ==> ~b`]) THEN
    USE_THEN "max" (MP_TAC o SPEC `SUC k`) THEN
    REWRITE_TAC[ARITH_RULE `~(SUC k <= k)`; NOT_CLAUSES; IMP_CLAUSES] THEN
    EXISTS_TAC `\i. if i <= k then (W:num->A) i else u` THEN
    MATCH_MP_TAC MOI_SCF_PATH_EXTEND THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!i. i <= k ==> (W:num->A) i IN V` (LABEL_TAC "inV") THENL
   [USE_THEN "WV" ACCEPT_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!i j. i <= k /\ j <= k /\ (W:num->A) i = W j ==> i = j`
  (LABEL_TAC "inj") THENL
   [USE_THEN "Winj" MP_TAC THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(x0:A = y0)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `(R:A->A->bool) y0 y0` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `1 <= k` ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `1 = SUC 0`] THEN USE_THEN "max" MATCH_MP_TAC THEN
    EXISTS_TAC `\i. if i <= 0 then (x0:A) else y0` THEN
    MATCH_MP_TAC MOI_SCF_PATH_EXTEND THEN
    REWRITE_TAC[moi_scf_path; LE; LT] THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `u:A` THEN STRIP_TAC THEN
  USE_THEN "onpath" (MP_TAC o SPEC `u:A`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
  ASM_CASES_TAC `i = k - 1` THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `i:num = k` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(R:A->A->bool) ((W:num->A) i) (W k)` ASSUME_TAC THENL
   [USE_THEN "sym" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(R:A->A->bool) ((W:num->A) i) (W(SUC i))` ASSUME_TAC THENL
   [USE_THEN "WR" MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `i = 0` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    SUBGOAL_THEN `(W:num->A)(SUC 0) = y0 /\ W k = y0` MP_TAC THENL
     [CONJ_TAC THEN USE_THEN "one" MATCH_MP_TAC THEN
      USE_THEN "W0" (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
      ASM_REWRITE_TAC[] THEN USE_THEN "inV" MATCH_MP_TAC THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(fun th -> MP_TAC(TRANS (CONJUNCT1 th) (SYM(CONJUNCT2 th)))) THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `SUC 0 = k` MP_TAC THENL
     [USE_THEN "inj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[LE_REFL] THEN
      ASM_ARITH_TAC;
      ASM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(R:A->A->bool) ((W:num->A) i) (W(i - 1))` ASSUME_TAC THENL
   [USE_THEN "sym" MATCH_MP_TAC THEN
    SUBGOAL_THEN `(W:num->A) i = W(SUC(i - 1))` SUBST1_TAC THENL
     [AP_TERM_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "WR" MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "two" (MP_TAC o SPECL [`(W:num->A) i`; `(W:num->A)(i - 1)`;
                                  `(W:num->A)(SUC i)`; `(W:num->A) k`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN USE_THEN "inV" MATCH_MP_TAC THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  STRIP_TAC THENL
   [SUBGOAL_THEN `i - 1 = SUC i` MP_TAC THENL
     [USE_THEN "inj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      ARITH_TAC];
    SUBGOAL_THEN `i - 1 = k` MP_TAC THENL
     [USE_THEN "inj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      ASM_ARITH_TAC];
    SUBGOAL_THEN `SUC i = k` MP_TAC THENL
     [USE_THEN "inj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      ASM_ARITH_TAC]]);;
(* Two PL arcs with common ends and no other common point form a PL         *)
(* 1-sphere (real^N with dimindex at least 2).  Adapted from               *)
(* MOI_SFR_ARCS_SPHERE of pc_moi_sch3_free.ml (stated there in real^2).     *)

let MOI_SLV_ARCS_SPHERE = prove
 (`!h1 h2:real^1->real^N.
     2 <= dimindex(:N) /\ arc h1 /\ pl_map_on (interval[vec 0,vec 1]) h1 /\
     arc h2 /\ pl_map_on (interval[vec 0,vec 1]) h2 /\
     pathstart h2 = pathstart h1 /\ pathfinish h2 = pathfinish h1 /\
     path_image h1 INTER path_image h2 = {pathstart h1,pathfinish h1}
     ==> pl_sphere 1 (path_image h1 UNION path_image h2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~collinear{vec 0:real^N,basis 1,basis 2}` ASSUME_TAC THENL
   [ASM_SIMP_TAC[MOI_SS2_STD_NONCOLLINEAR]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_PL2_NONCOLLINEAR_DISTINCT) THEN
  SUBGOAL_THEN
   `arc(linepath(vec 0:real^N,basis 1)) /\
    pl_map_on (interval[vec 0,vec 1]) (linepath(vec 0:real^N,basis 1)) /\
    pathstart(linepath(vec 0:real^N,basis 1)) = vec 0 /\
    pathfinish(linepath(vec 0:real^N,basis 1)) = basis 1 /\
    path_image(linepath(vec 0:real^N,basis 1)) = segment[vec 0,basis 1]`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[ARC_LINEPATH_EQ; PATHSTART_LINEPATH; PATHFINISH_LINEPATH;
                    PATH_IMAGE_LINEPATH] THEN
    SIMP_TAC[MOI_PL2_PL_LINEPATH; MOI_PL2_LOCALLY_POLYHEDRAL_INTERVAL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `arc(polygonal_path[vec 0:real^N;basis 2;basis 1]) /\
    pl_map_on (interval[vec 0,vec 1]) (polygonal_path[vec 0:real^N;basis 2;basis 1]) /\
    pathstart(polygonal_path[vec 0:real^N;basis 2;basis 1]) = vec 0 /\
    pathfinish(polygonal_path[vec 0:real^N;basis 2;basis 1]) = basis 1 /\
    path_image(polygonal_path[vec 0:real^N;basis 2;basis 1]) =
      segment[vec 0,basis 2] UNION segment[basis 2,basis 1]`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[MOI_PL2_PL_POLYGONAL_PATH] THEN REWRITE_TAC[polygonal_path] THEN
    SIMP_TAC[ARC_JOIN_EQ; PATHSTART_JOIN; PATHFINISH_JOIN; PATH_IMAGE_JOIN;
             PATHSTART_LINEPATH; PATHFINISH_LINEPATH; PATH_IMAGE_LINEPATH] THEN
    ASM_REWRITE_TAC[ARC_LINEPATH_EQ] THEN
    SUBGOAL_THEN `segment[vec 0:real^N,basis 2] INTER segment[basis 2,basis 1] =
                  {basis 2}` (fun th -> REWRITE_TAC[th; SUBSET_REFL]) THEN
    MATCH_MP_TAC INTER_SEGMENT THEN DISJ2_TAC THEN
    UNDISCH_TAC `~collinear{vec 0:real^N,basis 1,basis 2}` THEN
    REWRITE_TAC[INSERT_AC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `segment[vec 0:real^N,basis 1] INTER
    (segment[vec 0,basis 2] UNION segment[basis 2,basis 1]) = {vec 0,basis 1}`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `segment[vec 0:real^N,basis 1] INTER segment[vec 0,basis 2] =
                  {vec 0} /\
                  segment[vec 0:real^N,basis 1] INTER segment[basis 2,basis 1] =
                  {basis 1}`
    MP_TAC THENL
     [CONJ_TAC THENL
       [SUBST1_TAC(ISPECL [`vec 0:real^N`; `basis 1:real^N`] (CONJUNCT1 SEGMENT_SYM));
        SUBST1_TAC(ISPECL [`basis 2:real^N`; `basis 1:real^N`] (CONJUNCT1 SEGMENT_SYM))] THEN
      MATCH_MP_TAC INTER_SEGMENT THEN DISJ2_TAC THEN
      UNDISCH_TAC `~collinear{vec 0:real^N,basis 1,basis 2}` THEN
      REWRITE_TAC[INSERT_AC];
      ALL_TAC] THEN
    SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `linepath(vec 0:real^N,basis 1)` MOI_PL2_ARC_PL_HOMEOMORPHISM_ENDS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `l1:real^N->real^1`
    STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPEC `polygonal_path[vec 0:real^N;basis 2;basis 1]`
    MOI_PL2_ARC_PL_HOMEOMORPHISM_ENDS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `l2:real^N->real^1`
    STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPEC `h1:real^1->real^N` MOI_PL2_ARC_PL_HOMEOMORPHISM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `k1:real^N->real^1`) THEN
  MP_TAC(ISPEC `h2:real^1->real^N` MOI_PL2_ARC_PL_HOMEOMORPHISM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `k2:real^N->real^1`) THEN
  SUBGOAL_THEN
   `pl_homeomorphism (segment[vec 0:real^N,basis 1],path_image h1)
      ((h1:real^1->real^N) o (l1:real^N->real^1),
       linepath(vec 0:real^N,basis 1) o (k1:real^N->real^1)) /\
    pl_homeomorphism (segment[vec 0:real^N,basis 2] UNION segment[basis 2,basis 1],
                      path_image h2)
      ((h2:real^1->real^N) o (l2:real^N->real^1),
       polygonal_path[vec 0:real^N;basis 2;basis 1] o (k2:real^N->real^1))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
    EXISTS_TAC `interval[vec 0:real^1,vec 1]` THEN
    ONCE_REWRITE_TAC[PL_HOMEOMORPHISM_SYM] THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[PL_HOMEOMORPHISM_SYM] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`segment[vec 0:real^N,basis 1]`;
    `segment[vec 0:real^N,basis 2] UNION segment[basis 2,basis 1]`;
    `path_image(h1:real^1->real^N)`; `path_image(h2:real^1->real^N)`;
    `(h1:real^1->real^N) o (l1:real^N->real^1)`;
    `linepath(vec 0:real^N,basis 1) o (k1:real^N->real^1)`;
    `(h2:real^1->real^N) o (l2:real^N->real^1)`;
    `polygonal_path[vec 0:real^N;basis 2;basis 1] o (k2:real^N->real^1)`]
   MOI_PL2_PL_HOMEOMORPHISM_UNION) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    SIMP_TAC[CLOSED_UNION; CLOSED_SEGMENT] THEN
    ASM_SIMP_TAC[CLOSED_PATH_IMAGE; ARC_IMP_PATH] THEN
    REWRITE_TAC[FORALL_IN_INSERT; NOT_IN_EMPTY; IMAGE_CLAUSES; o_THM] THEN
    SUBGOAL_THEN `(l1:real^N->real^1) (vec 0) = vec 0 /\ l1 (basis 1) = vec 1 /\
                  (l2:real^N->real^1) (vec 0) = vec 0 /\ l2 (basis 1) = vec 1`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `pathstart (h2:real^1->real^N) = pathstart h1` THEN
    UNDISCH_TAC `pathfinish (h2:real^1->real^N) = pathfinish h1` THEN
    REWRITE_TAC[pathstart; pathfinish] THEN
    REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[];
    DISCH_TAC] THEN
  REWRITE_TAC[pl_sphere] THEN
  EXISTS_TAC `convex hull {vec 0:real^N,basis 1,basis 2}` THEN
  REWRITE_TAC[RIGHT_EXISTS_AND_THM] THEN CONJ_TAC THENL
   [REWRITE_TAC[ARITH_RULE `1 + 1 = 2`; MOI_PL2_SIMPLEX_2] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[RELATIVE_FRONTIER_OF_TRIANGLE] THEN
  SUBGOAL_THEN
   `segment[vec 0:real^N,basis 1] UNION segment[basis 1,basis 2] UNION
    segment[basis 2,vec 0] =
    segment[vec 0,basis 1] UNION
    (segment[vec 0,basis 2] UNION segment[basis 2,basis 1])`
  SUBST1_TAC THENL
   [REWRITE_TAC[ISPECL [`basis 1:real^N`; `basis 2:real^N`] (CONJUNCT1 SEGMENT_SYM);
                ISPECL [`basis 2:real^N`; `vec 0:real^N`] (CONJUNCT1 SEGMENT_SYM)] THEN
    SET_TAC[];
    ASM_MESON_TAC[]]);;

let MOI_SLV_LIST_OF_SEQ_CONS = prove
 (`!(Y:num->A) n.
     list_of_seq Y (SUC n) = CONS (Y 0) (list_of_seq (\i. Y(SUC i)) n)`,
  GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[list_of_seq; APPEND];
    ONCE_REWRITE_TAC[list_of_seq] THEN ASM_REWRITE_TAC[APPEND]]);;

let MOI_SLV_POLYGONAL_CONS = prove
 (`!(a:real^N) l.
     2 <= LENGTH l
     ==> polygonal_path (CONS a l) = linepath(a,HD l) ++ polygonal_path l`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `u:real^N` (X_CHOOSE_THEN `x:real^N`
    (X_CHOOSE_THEN `t:(real^N)list` SUBST1_TAC)) o
    MATCH_MP MOI_PL2_LIST_CONS_CONS) THEN
  REWRITE_TAC[polygonal_path; HD]);;

let MOI_SLV_UNIONS_LT_SUC = prove
 (`!(f:num->A->bool) n.
     UNIONS {f i | i < SUC n} = f 0 UNION UNIONS {f (SUC i) | i < n}`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN
  REWRITE_TAC[IN_UNION; IN_UNIONS; IN_ELIM_THM] THEN
  X_GEN_TAC `x:A` THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `t:A->bool` (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    DISJ_CASES_TAC(SPEC `i:num` num_CASES) THENL
     [DISJ1_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_REWRITE_TAC[];
      FIRST_X_ASSUM(X_CHOOSE_THEN `j:num` SUBST_ALL_TAC) THEN DISJ2_TAC THEN
      EXISTS_TAC `(f:num->A->bool) (SUC j)` THEN ASM_REWRITE_TAC[] THEN
      EXISTS_TAC `j:num` THEN REWRITE_TAC[] THEN ASM_ARITH_TAC];
    STRIP_TAC THENL
     [EXISTS_TAC `(f:num->A->bool) 0` THEN ASM_REWRITE_TAC[] THEN
      EXISTS_TAC `0` THEN REWRITE_TAC[] THEN ARITH_TAC;
      EXISTS_TAC `t:A->bool` THEN ASM_REWRITE_TAC[] THEN
      EXISTS_TAC `SUC i` THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]]);;

(* A polygonal path through distinct vertices of a simplicial complex along *)
(* its edges is an arc.                                                     *)

let MOI_SLV_POLY_ARC = prove
 (`!K m (Y:num->real^N).
     simplicial_complex K /\ 1 <= m /\
     (!i j. i <= m /\ j <= m /\ Y i = Y j ==> i = j) /\
     (!i. i < m ==> segment[Y i,Y(SUC i)] IN K)
     ==> arc(polygonal_path(list_of_seq Y (SUC m))) /\
         pathstart(polygonal_path(list_of_seq Y (SUC m))) = Y 0 /\
         pathfinish(polygonal_path(list_of_seq Y (SUC m))) = Y m /\
         path_image(polygonal_path(list_of_seq Y (SUC m))) =
           UNIONS {segment[Y i,Y(SUC i)] | i < m}`,
  GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC[ARITH_RULE `~(1 <= 0)`] THEN
  X_GEN_TAC `Y:num->real^N` THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[MOI_SLV_LIST_OF_SEQ_CONS] THEN
  REWRITE_TAC[MOI_SLV_UNIONS_LT_SUC] THEN
  ASM_CASES_TAC `m = 0` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    REWRITE_TAC[MOI_SLV_LIST_OF_SEQ_CONS; CONJUNCT1 list_of_seq] THEN
    REWRITE_TAC[polygonal_path; ARC_LINEPATH_EQ; PATHSTART_LINEPATH;
                PATHFINISH_LINEPATH; PATH_IMAGE_LINEPATH; LT] THEN
    REWRITE_TAC[ARITH_RULE `SUC 0 = 1`] THEN CONJ_TAC THENL
     [DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL [`0`; `1`] o
        check (is_forall o concl)) THEN
      ASM_REWRITE_TAC[] THEN ARITH_TAC;
      SET_TAC[]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `\i. (Y:num->real^N)(SUC i)`) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[ARITH_RULE `1 <= m <=> ~(m = 0)`] THEN CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN
      MATCH_MP_TAC(ARITH_RULE `SUC i = SUC j ==> i = j`) THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[LE_SUC];
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `polygonal_path (CONS ((Y:num->real^N) 0)
                         (list_of_seq (\i. Y (SUC i)) (SUC m))) =
    linepath(Y 0,Y 1) ++ polygonal_path (list_of_seq (\i. Y (SUC i)) (SUC m))`
  SUBST1_TAC THENL
   [W(fun (_,w) -> MP_TAC(ISPECL [`(Y:num->real^N) 0`;
       `list_of_seq (\i. (Y:num->real^N) (SUC i)) (SUC m)`]
       MOI_SLV_POLYGONAL_CONS)) THEN
    REWRITE_TAC[LENGTH_LIST_OF_SEQ] THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[MOI_SLV_LIST_OF_SEQ_CONS; HD; ARITH_RULE `SUC 0 = 1`];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `pathfinish(linepath((Y:num->real^N) 0,Y 1)) =
    pathstart(polygonal_path (list_of_seq (\i. Y (SUC i)) (SUC m)))`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[PATHFINISH_LINEPATH; ARITH_RULE `SUC 0 = 1`]; ALL_TAC] THEN
  ASM_SIMP_TAC[ARC_JOIN_EQ; PATHSTART_JOIN; PATHFINISH_JOIN; PATH_IMAGE_JOIN] THEN
  ASM_REWRITE_TAC[ARC_LINEPATH_EQ; PATHSTART_LINEPATH; PATH_IMAGE_LINEPATH;
                  ARITH_RULE `SUC 0 = 1`] THEN
  CONJ_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `0 = 1` MP_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      ARITH_TAC];
    ALL_TAC] THEN
    REWRITE_TAC[SUBSET; IN_INTER; IN_UNIONS; IN_ELIM_THM; IN_SING] THEN
    X_GEN_TAC `x:real^N` THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `t:real^N->bool`
      (CONJUNCTS_THEN2 (X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) ASSUME_TAC))) THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `(Y:num->real^N) 0`; `(Y:num->real^N) 1`;
                   `(Y:num->real^N)(SUC i)`; `(Y:num->real^N)(SUC(SUC i))`]
      MOI_SLV_SEGMENTS_INTER) THEN
    SUBGOAL_THEN
     `!a b. a <= SUC m /\ b <= SUC m /\ ~(a = b) ==> ~((Y:num->real^N) a = Y b)`
    ASSUME_TAC THENL
     [MESON_TAC[ASSUME `!i j. i <= SUC m /\ j <= SUC m /\ (Y:num->real^N) i = Y j
                             ==> i = j`];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `~((Y:num->real^N) 0 = Y(SUC i)) /\ ~(Y 0 = Y(SUC(SUC i))) /\
      ~(Y 0 = Y 1) /\ ~(Y(SUC i) = Y(SUC(SUC i)))`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[SEGMENT_EQ] THEN REPEAT CONJ_TAC THENL
       [REWRITE_TAC[ARITH_RULE `1 = SUC 0`] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        ASM_ARITH_TAC;
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
        REWRITE_TAC[EXTENSION; IN_INSERT; NOT_IN_EMPTY] THEN
        DISCH_THEN(MP_TAC o SPEC `(Y:num->real^N) 0`) THEN ASM_REWRITE_TAC[]];
      ASM SET_TAC[]]);;

(* A closed polygon through at least three distinct vertices of a          *)
(* simplicial complex along its edges is a PL 1-sphere.                     *)

let MOI_SLV_POLYGON_SPHERE = prove
 (`!K m (Y:num->real^N).
     2 <= dimindex(:N) /\ simplicial_complex K /\ 2 <= m /\
     (!i j. i <= m /\ j <= m /\ Y i = Y j ==> i = j) /\
     (!i. i < m ==> segment[Y i,Y(SUC i)] IN K) /\ segment[Y m,Y 0] IN K
     ==> pl_sphere 1
           (segment[Y m,Y 0] UNION UNIONS {segment[Y i,Y(SUC i)] | i < m})`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `m:num`; `Y:num->real^N`]
    MOI_SLV_POLY_ARC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN
   `!a b. a <= m /\ b <= m /\ ~(a = b) ==> ~((Y:num->real^N) a = Y b)`
  (LABEL_TAC "H") THENL
   [MESON_TAC[ASSUME `!i j. i <= m /\ j <= m /\ (Y:num->real^N) i = Y j
                           ==> i = j`];
    ALL_TAC] THEN
  UNDISCH_THEN `!i j. i <= m /\ j <= m /\ (Y:num->real^N) i = Y j ==> i = j`
    (K ALL_TAC) THEN
  SUBGOAL_THEN `~((Y:num->real^N) 0 = Y m)` ASSUME_TAC THENL
   [USE_THEN "H" MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `segment[(Y:num->real^N) 0,Y m] IN K` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[CONJUNCT1 SEGMENT_SYM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`linepath((Y:num->real^N) 0,Y m)`;
                 `polygonal_path(list_of_seq (Y:num->real^N) (SUC m))`]
    MOI_SLV_ARCS_SPHERE) THEN
  ASM_REWRITE_TAC[ARC_LINEPATH_EQ; PATHSTART_LINEPATH; PATHFINISH_LINEPATH;
                  PATH_IMAGE_LINEPATH] THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC MOI_PL2_PL_LINEPATH THEN
      REWRITE_TAC[MOI_PL2_LOCALLY_POLYHEDRAL_INTERVAL];
      ALL_TAC] THEN
    CONJ_TAC THENL [REWRITE_TAC[MOI_PL2_PL_POLYGONAL_PATH]; ALL_TAC] THEN
    MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_INTER; IN_UNIONS; IN_ELIM_THM] THEN
      X_GEN_TAC `x:real^N` THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `t:real^N->bool`
        (CONJUNCTS_THEN2 (X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC)
          ASSUME_TAC))) THEN
      FIRST_X_ASSUM SUBST_ALL_TAC THEN
      SUBGOAL_THEN `~((Y:num->real^N) 0 = Y(SUC i))` ASSUME_TAC THENL
       [USE_THEN "H" MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `~((Y:num->real^N) i = Y(SUC i))` ASSUME_TAC THENL
       [USE_THEN "H" MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
      MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `(Y:num->real^N) 0`;
                     `(Y:num->real^N) m`; `(Y:num->real^N) i`;
                     `(Y:num->real^N)(SUC i)`] MOI_SLV_SEGMENTS_INTER) THEN
      ANTS_TAC THENL
       [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
         [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
        REWRITE_TAC[SEGMENT_EQ] THEN DISCH_TAC THEN
        SUBGOAL_THEN
         `((Y:num->real^N) 0 = Y i \/ Y 0 = Y (SUC i)) /\
          (Y m = Y i \/ Y m = Y (SUC i))`
        MP_TAC THENL
         [UNDISCH_TAC `{(Y:num->real^N) 0,Y m} = {Y i,Y(SUC i)}` THEN SET_TAC[];
          ALL_TAC] THEN
        ASM_REWRITE_TAC[] THEN ASM_CASES_TAC `i = 0` THENL
         [FIRST_X_ASSUM SUBST_ALL_TAC THEN
          SUBGOAL_THEN `~((Y:num->real^N) m = Y 0) /\ ~(Y m = Y (SUC 0))`
          (fun th -> REWRITE_TAC[th]) THEN
          CONJ_TAC THEN USE_THEN "H" MATCH_MP_TAC THEN ASM_ARITH_TAC;
          SUBGOAL_THEN `~((Y:num->real^N) 0 = Y i)` (fun th -> REWRITE_TAC[th]) THEN
          USE_THEN "H" MATCH_MP_TAC THEN ASM_ARITH_TAC];
        REWRITE_TAC[SUBSET; IN_INTER] THEN
        DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[] THEN
        SIMP_TAC[]];
      REWRITE_TAC[SUBSET; IN_INSERT; NOT_IN_EMPTY; IN_INTER] THEN
      X_GEN_TAC `x:real^N` THEN
      DISCH_THEN(DISJ_CASES_THEN SUBST1_TAC) THEN
      REWRITE_TAC[ENDS_IN_SEGMENT; IN_UNIONS; IN_ELIM_THM] THENL
       [EXISTS_TAC `segment[(Y:num->real^N) 0,Y(SUC 0)]` THEN
        REWRITE_TAC[ENDS_IN_SEGMENT] THEN EXISTS_TAC `0` THEN ASM_ARITH_TAC;
        EXISTS_TAC `segment[(Y:num->real^N) (m - 1),Y(SUC(m - 1))]` THEN
        CONJ_TAC THENL [EXISTS_TAC `m - 1` THEN ASM_ARITH_TAC; ALL_TAC] THEN
        SUBGOAL_THEN `SUC(m - 1) = m` SUBST1_TAC THENL
         [ASM_ARITH_TAC; REWRITE_TAC[ENDS_IN_SEGMENT]]]];
    REWRITE_TAC[ISPECL [`(Y:num->real^N) m`; `(Y:num->real^N) 0`]
                  (CONJUNCT1 SEGMENT_SYM)]]);;

(* ------------------------------------------------------------------------- *)
(* 5. Existence and counting of PL circles in degree-2 graphs: through each *)
(* edge at v runs a circle (a walk from the other end returns to v) using   *)
(* exactly two edges at v; every edge lies in a circle; so the edges at v   *)
(* are twice the circles through v.                                          *)
(* ------------------------------------------------------------------------- *)

let MOI_SLV_EDGE_AT_VERTEX = prove
 (`!K t (x:real^N).
     simplicial_complex K /\ t IN K /\ aff_dim t = &1 /\ {x} IN K /\ x IN t
     ==> ?y. ~(y = x) /\ t = segment[x,y] /\ {y} IN K`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `t:real^N->bool`] MOI_SLV_EDGE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N` (X_CHOOSE_THEN `w:real^N`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `x:real^N`; `u:real^N`; `w:real^N`]
    MOI_SLV_VERTEX_IN_SEGMENT) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  STRIP_TAC THENL
   [EXISTS_TAC `w:real^N` THEN ASM_MESON_TAC[];
    EXISTS_TAC `u:real^N` THEN ASM_MESON_TAC[SEGMENT_SYM]]);;

let MOI_SLV_G2_EDGES_SET = prove
 (`!K (v:real^N) x.
     moi_slv_graph2 K v /\ {x} IN K /\ ~(x = v)
     ==> ?y z. ~(y = z) /\ ~(y = x) /\ ~(z = x) /\
               segment[x,y] IN K /\ segment[x,z] IN K /\ {y} IN K /\ {z} IN K /\
               !w. segment[x,w] IN K /\ ~(w = x) ==> w = y \/ w = z`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_slv_graph2]) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[MOI_SCF_HAS_SIZE_2] THEN
  DISCH_THEN(X_CHOOSE_THEN `e1:real^N->bool` (X_CHOOSE_THEN `e2:real^N->bool`
    STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [EXTENSION]) THEN
  REWRITE_TAC[IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY] THEN
  DISCH_THEN(LABEL_TAC "E") THEN
  SUBGOAL_THEN
   `!t:real^N->bool. t IN K /\ aff_dim t = &1 /\ x IN t ==> t = e1 \/ t = e2`
  (LABEL_TAC "E'") THENL
   [GEN_TAC THEN USE_THEN "E" (fun th -> REWRITE_TAC[th]); ALL_TAC] THEN
  SUBGOAL_THEN
   `(e1:real^N->bool) IN K /\ aff_dim e1 = &1 /\ x IN e1 /\
    e2 IN K /\ aff_dim e2 = &1 /\ x IN e2`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "E" (fun th -> MP_TAC(SPEC `e1:real^N->bool` th) THEN
                            MP_TAC(SPEC `e2:real^N->bool` th)) THEN
    REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `e1:real^N->bool`; `x:real^N`]
    MOI_SLV_EDGE_AT_VERTEX) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `e2:real^N->bool`; `x:real^N`]
    MOI_SLV_EDGE_AT_VERTEX) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:real^N` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`y:real^N`; `z:real^N`] THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
    is_eq(concl th) && is_var(lhs(concl th)) &&
    (lhs(concl th) = `e1:real^N->bool` || lhs(concl th) = `e2:real^N->bool`)))) THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `w:real^N` THEN STRIP_TAC THEN
  REMOVE_THEN "E'" (MP_TAC o SPEC `segment[x:real^N,w]`) THEN
  REMOVE_THEN "E" (K ALL_TAC) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[AFF_DIM_SEGMENT; ENDS_IN_SEGMENT] THEN
    COND_CASES_TAC THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SEGMENT_EQ; EXTENSION; IN_INSERT; NOT_IN_EMPTY] THEN
  DISCH_THEN(DISJ_CASES_THEN (MP_TAC o SPEC `w:real^N`)) THEN
  ASM_MESON_TAC[]);;

let MOI_SLV_POLYGON_VERTEX = prove
 (`!K m (Y:num->real^N) x.
     simplicial_complex K /\ (!i. i < m ==> segment[Y i,Y(SUC i)] IN K) /\
     segment[Y m,Y 0] IN K /\ {x} IN K /\
     x IN segment[Y m,Y 0] UNION UNIONS {segment[Y i,Y(SUC i)] | i < m}
     ==> ?j. j <= m /\ x = Y j`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[IN_UNION; IN_UNIONS; IN_ELIM_THM] THEN STRIP_TAC THENL
   [MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `x:real^N`; `(Y:num->real^N) m`;
                   `(Y:num->real^N) 0`] MOI_SLV_VERTEX_IN_SEGMENT) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
     [EXISTS_TAC `m:num` THEN ASM_REWRITE_TAC[LE_REFL];
      EXISTS_TAC `0` THEN ASM_REWRITE_TAC[LE_0]];
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `x:real^N`; `(Y:num->real^N) i`;
                   `(Y:num->real^N)(SUC i)`] MOI_SLV_VERTEX_IN_SEGMENT) THEN
    ASM_SIMP_TAC[] THEN STRIP_TAC THENL
     [EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      EXISTS_TAC `SUC i` THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]]);;

(* The walk from the far end of an edge at v returns to v.                  *)

let MOI_SLV_G2_WALK_SETUP = prove
 (`!K (v:real^N) p0.
     moi_slv_graph2 K v /\ {v} IN K /\ segment[v,p0] IN K /\ ~(p0 = v) /\
     {p0} IN K
     ==> ?k W. 1 <= k /\ W 0 = p0 /\
               (!i. i <= k ==> {W i} IN K /\ ~(W i = v)) /\
               (!i. i < k ==> segment[W i,W(SUC i)] IN K) /\
               (!i j. i <= k /\ j <= k /\ W i = W j ==> i = j) /\
               segment[W k,v] IN K`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_slv_graph2]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SLV_SC_BASIC) THEN
  MP_TAC(ISPECL [`{x:real^N | {x} IN K /\ ~(x = v)}`;
                 `\x y:real^N. ~(x = y) /\ segment[x,y] IN K`; `p0:real^N`]
    MOI_SLV_WALK) THEN
  REWRITE_TAC[IN_ELIM_THM] THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{x:real^N | {x} IN K}` THEN
      ASM_SIMP_TAC[MOI_SLV_VERTICES_FINITE] THEN SET_TAC[];
      REPEAT STRIP_TAC THENL
       [ASM_MESON_TAC[]; ONCE_REWRITE_TAC[SEGMENT_SYM] THEN ASM_REWRITE_TAC[]];
      MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`; `z:real^N`; `w:real^N`] THEN
      STRIP_TAC THEN
      MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `v:real^N`; `x:real^N`]
        MOI_SLV_G2_EDGES_SET) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `a:real^N` (X_CHOOSE_THEN `b:real^N`
        (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
          (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
            (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
              (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "nb")))))))))) THEN
      REMOVE_THEN "nb" (fun th ->
        MP_TAC(SPEC `y:real^N` th) THEN MP_TAC(SPEC `z:real^N` th) THEN
        MP_TAC(SPEC `w:real^N` th)) THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `~(w:real^N = x) /\ ~(z = x) /\ ~(y = x)`
        (fun th -> REWRITE_TAC[th]) THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      MESON_TAC[];
      MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `v:real^N`; `p0:real^N`]
        MOI_SLV_G2_EDGES_SET) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `a:real^N` (X_CHOOSE_THEN `b:real^N`
        (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
          (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
            (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
              (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "nb")))))))))) THEN
      SUBGOAL_THEN `v:real^N = a \/ v = b` (DISJ_CASES_THEN ASSUME_TAC) THENL
       [USE_THEN "nb" MATCH_MP_TAC THEN ONCE_REWRITE_TAC[SEGMENT_SYM] THEN
        ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
        EXISTS_TAC `b:real^N` THEN REPEAT CONJ_TAC THENL
         [ASM_REWRITE_TAC[]; ASM_MESON_TAC[]; ASM_MESON_TAC[]; ASM_REWRITE_TAC[];
          X_GEN_TAC `z:real^N` THEN STRIP_TAC THEN
          USE_THEN "nb" (MP_TAC o SPEC `z:real^N`) THEN ASM_MESON_TAC[]];
        EXISTS_TAC `a:real^N` THEN REPEAT CONJ_TAC THENL
         [ASM_REWRITE_TAC[]; ASM_MESON_TAC[]; ASM_MESON_TAC[]; ASM_REWRITE_TAC[];
          X_GEN_TAC `z:real^N` THEN STRIP_TAC THEN
          USE_THEN "nb" (MP_TAC o SPEC `z:real^N`) THEN ASM_MESON_TAC[]]]];
    ALL_TAC] THEN
  REWRITE_TAC[moi_scf_path; IN_ELIM_THM] THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `W:num->real^N`
    (CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
      (LABEL_TAC "WV") (CONJUNCTS_THEN2 (LABEL_TAC "WR") (LABEL_TAC "Winj"))))
     (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "end"))))) THEN
  MAP_EVERY EXISTS_TAC [`k:num`; `W:num->real^N`] THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN USE_THEN "WR" (MP_TAC o SPEC `i:num`) THEN
    ASM_SIMP_TAC[];
    USE_THEN "Winj" MP_TAC THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `{(W:num->real^N) k} IN K /\ ~(W k = v)` STRIP_ASSUME_TAC THENL
   [USE_THEN "WV" MATCH_MP_TAC THEN REWRITE_TAC[LE_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN `~((W:num->real^N)(k - 1) = W k) /\ segment[W k,W(k - 1)] IN K`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "WR" (MP_TAC o SPEC `k - 1`) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `SUC(k - 1) = k` SUBST1_TAC THENL
     [ASM_ARITH_TAC; MESON_TAC[SEGMENT_SYM]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `v:real^N`; `(W:num->real^N) k`]
    MOI_SLV_G2_EDGES_SET) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^N` (X_CHOOSE_THEN `b:real^N`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
        (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
          (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "nb")))))))))) THEN
  SUBGOAL_THEN `(W:num->real^N)(k - 1) = a \/ W(k - 1) = b` MP_TAC THENL
   [USE_THEN "nb" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!c:real^N. ~(c = W k) /\ ~(c = W(k - 1)) /\ segment[W k,c] IN K /\
                           {c} IN K ==> c = v`
  ASSUME_TAC THENL
   [X_GEN_TAC `c:real^N` THEN STRIP_TAC THEN
    MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    USE_THEN "end" (MP_TAC o SPEC `c:real^N`) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  STRIP_TAC THENL
   [SUBGOAL_THEN `b:real^N = v` (fun th -> ASM_MESON_TAC[th]) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[];
    SUBGOAL_THEN `a:real^N = v` (fun th -> ASM_MESON_TAC[th]) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]]);;

(* The polygon v, W 0, ..., W k of a walk returning to v: a PL circle that  *)
(* uses exactly the two edges [v,W 0] and [v,W k] at v.                      *)

let MOI_SLV_G2_LOOP_POLY = prove
 (`!K (v:real^N) k W.
     2 <= dimindex(:N) /\ moi_slv_graph2 K v /\ {v} IN K /\ 1 <= k /\
     (!i. i <= k ==> {W i} IN K /\ ~(W i = v)) /\
     (!i. i < k ==> segment[W i,W(SUC i)] IN K) /\
     (!i j. i <= k /\ j <= k /\ W i = W j ==> i = j) /\
     segment[v,W 0] IN K /\ segment[W k,v] IN K
     ==> ?q. pl_sphere 1 q /\ q SUBSET UNIONS K /\ segment[v,W 0] SUBSET q /\
             !t. t IN K /\ aff_dim t = &1 /\ v IN t /\ t SUBSET q <=>
                 t = segment[v,W 0] \/ t = segment[v,W k]`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (LABEL_TAC "WV") (CONJUNCTS_THEN2 (LABEL_TAC "WR")
        (CONJUNCTS_THEN2 (LABEL_TAC "Winj") STRIP_ASSUME_TAC))))))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_slv_graph2]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SLV_SC_BASIC) THEN
  SUBGOAL_THEN `?Y:num->real^N. Y 0 = v /\ !i. Y(SUC i) = W i`
  STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `\i. if i = 0 then (v:real^N) else W(i - 1)` THEN
    REWRITE_TAC[NOT_SUC; SUC_SUB1];
    ALL_TAC] THEN
  SUBGOAL_THEN `!i. i <= SUC k ==> (Y:num->real^N) i = v \/ ?j. j <= k /\ Y i = W j`
  ASSUME_TAC THENL
   [GEN_TAC THEN DISJ_CASES_TAC(SPEC `i:num` num_CASES) THEN
    ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM(X_CHOOSE_THEN `j:num` SUBST1_TAC) THEN
    ASM_REWRITE_TAC[LE_SUC] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i j. i <= SUC k /\ j <= SUC k /\ (Y:num->real^N) i = Y j ==> i = j`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN
    STRUCT_CASES_TAC(SPEC `i:num` num_CASES) THEN
    STRUCT_CASES_TAC(SPEC `j:num` num_CASES) THEN
    ASM_REWRITE_TAC[LE_SUC; SUC_INJ; NOT_SUC] THEN REPEAT STRIP_TAC THEN
    REMOVE_THEN "WV" (MP_TAC o SPEC `n:num`) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!i. i < SUC k ==> segment[(Y:num->real^N) i,Y(SUC i)] IN K`
  ASSUME_TAC THENL
   [GEN_TAC THEN DISJ_CASES_TAC(SPEC `i:num` num_CASES) THEN
    ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM(X_CHOOSE_THEN `j:num` SUBST1_TAC) THEN
    ASM_REWRITE_TAC[LT_SUC] THEN DISCH_TAC THEN
    USE_THEN "WR" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `pl_sphere 1 (segment[(W:num->real^N) k,v] UNION segment[v,W 0] UNION
                 UNIONS {segment[W i,W(SUC i)] | i < k}) /\
    !z. {z} IN K /\
        z IN segment[(W:num->real^N) k,v] UNION segment[v,W 0] UNION
             UNIONS {segment[W i,W(SUC i)] | i < k}
        ==> z = v \/ ?j. j <= k /\ z = W j`
  (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "vtx")) THENL
   [SUBGOAL_THEN
     `segment[(Y:num->real^N)(SUC k),Y 0] UNION
      UNIONS {segment[Y i,Y(SUC i)] | i < SUC k} =
      segment[(W:num->real^N) k,v] UNION segment[v,W 0] UNION
      UNIONS {segment[W i,W(SUC i)] | i < k}`
    (SUBST1_TAC o SYM) THENL
     [REWRITE_TAC[MOI_SLV_UNIONS_LT_SUC] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MOI_SLV_POLYGON_SPHERE THEN
      EXISTS_TAC `K:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
      ASM_ARITH_TAC;
      X_GEN_TAC `z:real^N` THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `SUC k`; `Y:num->real^N`;
                     `z:real^N`] MOI_SLV_POLYGON_VERTEX) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
      FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC
   `q = segment[(W:num->real^N) k,v] UNION segment[v,W 0] UNION
        UNIONS {segment[W i,W(SUC i)] | i < k}` THEN
  SUBGOAL_THEN `segment[v:real^N,W 0] SUBSET q /\ segment[v,W k] SUBSET q`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "q" THEN
    SUBGOAL_THEN `segment[v:real^N,(W:num->real^N) k] = segment[W k,v]`
    SUBST1_TAC THENL
     [REWRITE_TAC[SEGMENT_SYM]; ALL_TAC] THEN
    REWRITE_TAC[SUBSET; IN_UNION] THEN SIMP_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `q:real^N->bool` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [EXPAND_TAC "q" THEN
    REWRITE_TAC[UNION_SUBSET; UNIONS_SUBSET; FORALL_IN_GSPEC] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC(SET_RULE `(s:A->bool) IN f ==> s SUBSET UNIONS f`) THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC(SET_RULE `(s:A->bool) IN f ==> s SUBSET UNIONS f`) THEN
      ASM_REWRITE_TAC[];
      REPEAT STRIP_TAC THEN
      MATCH_MP_TAC(SET_RULE `(s:A->bool) IN f ==> s SUBSET UNIONS f`) THEN
      USE_THEN "WR" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(v:real^N = W 0) /\ ~(v = W k)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN DISCH_TAC THENL
     [USE_THEN "WV" (MP_TAC o SPEC `0`); USE_THEN "WV" (MP_TAC o SPEC `k:num`)] THEN
    REWRITE_TAC[LE_0; LE_REFL] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `segment[v:real^N,(W:num->real^N) k] IN K` ASSUME_TAC THENL
   [SUBGOAL_THEN `segment[v:real^N,(W:num->real^N) k] = segment[W k,v]`
    SUBST1_TAC THENL [REWRITE_TAC[SEGMENT_SYM]; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  X_GEN_TAC `t:real^N->bool` THEN EQ_TAC THENL
   [ALL_TAC;
    DISCH_THEN(DISJ_CASES_THEN SUBST1_TAC) THEN
    ASM_REWRITE_TAC[AFF_DIM_SEGMENT; ENDS_IN_SEGMENT]] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `t:real^N->bool`; `v:real^N`]
    MOI_SLV_EDGE_AT_VERTEX) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:real^N` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  REMOVE_THEN "vtx" (MP_TAC o SPEC `z:real^N`) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `segment[v:real^N,z] SUBSET q` THEN EXPAND_TAC "q" THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[ENDS_IN_SEGMENT];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  ASM_CASES_TAC `j = 0` THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `j:num = k` THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `{(W:num->real^N) j} IN K /\ ~(W j = v)` STRIP_ASSUME_TAC THENL
   [USE_THEN "WV" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `v:real^N`; `(W:num->real^N) j`]
    MOI_SLV_G2_EDGES_SET) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^N` (X_CHOOSE_THEN `b:real^N`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
        (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
          (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "nb")))))))))) THEN
  SUBGOAL_THEN
   `segment[(W:num->real^N) j,W(j - 1)] IN K /\ segment[W j,W(SUC j)] IN K /\
    segment[W j,v] IN K /\ ~(W(j - 1) = W j) /\ ~(W(SUC j) = W j) /\
    ~(W(j - 1) = W(SUC j)) /\ ~(W(j - 1) = v) /\ ~(W(SUC j) = v)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ONCE_REWRITE_TAC[CONJUNCT1 SEGMENT_SYM] THEN
      SUBGOAL_THEN `(W:num->real^N) j = W(SUC(j - 1))` SUBST1_TAC THENL
       [AP_TERM_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
      USE_THEN "WR" MATCH_MP_TAC THEN ASM_ARITH_TAC;
      USE_THEN "WR" MATCH_MP_TAC THEN ASM_ARITH_TAC;
      ONCE_REWRITE_TAC[CONJUNCT1 SEGMENT_SYM] THEN ASM_REWRITE_TAC[];
      DISCH_TAC THEN SUBGOAL_THEN `j - 1 = j` MP_TAC THENL
       [USE_THEN "Winj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
        ASM_ARITH_TAC];
      DISCH_TAC THEN SUBGOAL_THEN `SUC j = j` MP_TAC THENL
       [USE_THEN "Winj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
        ARITH_TAC];
      DISCH_TAC THEN SUBGOAL_THEN `j - 1 = SUC j` MP_TAC THENL
       [USE_THEN "Winj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
        ARITH_TAC];
      USE_THEN "WV" (MP_TAC o SPEC `j - 1`) THEN ANTS_TAC THENL
       [ASM_ARITH_TAC; SIMP_TAC[]];
      USE_THEN "WV" (MP_TAC o SPEC `SUC j`) THEN ANTS_TAC THENL
       [ASM_ARITH_TAC; SIMP_TAC[]]];
    ALL_TAC] THEN
  REMOVE_THEN "nb" (fun th ->
    MP_TAC(SPEC `(W:num->real^N)(j - 1)` th) THEN
    MP_TAC(SPEC `(W:num->real^N)(SUC j)` th) THEN MP_TAC(SPEC `v:real^N` th)) THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY UNDISCH_TAC
   [`~((W:num->real^N)(j - 1) = W(SUC j))`; `~((W:num->real^N)(j - 1) = v)`;
    `~((W:num->real^N)(SUC j) = v)`] THEN
  MESON_TAC[]);;

let MOI_SLV_G2_LOOP = prove
 (`!K (v:real^N) s.
     2 <= dimindex(:N) /\ moi_slv_graph2 K v /\ {v} IN K /\
     s IN K /\ aff_dim s = &1 /\ v IN s
     ==> ?q. pl_sphere 1 q /\ q SUBSET UNIONS K /\ s SUBSET q /\
             {t | t IN K /\ aff_dim t = &1 /\ v IN t /\ t SUBSET q} HAS_SIZE 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_slv_graph2]) THEN
  MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `s:real^N->bool`; `v:real^N`]
    MOI_SLV_EDGE_AT_VERTEX) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `p0:real^N` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `v:real^N`; `p0:real^N`]
    MOI_SLV_G2_WALK_SETUP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `W:num->real^N`
    STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th ->
    concl th = `(W:num->real^N) 0 = p0`)) THEN
  MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `v:real^N`; `k:num`;
                 `W:num->real^N`] MOI_SLV_G2_LOOP_POLY) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:real^N->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `q:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[MOI_SCF_HAS_SIZE_2] THEN
  MAP_EVERY EXISTS_TAC [`segment[v:real^N,W 0]`;
                        `segment[v:real^N,(W:num->real^N) k]`] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[SEGMENT_EQ; EXTENSION; IN_INSERT; NOT_IN_EMPTY] THEN
    DISCH_THEN(MP_TAC o SPEC `(W:num->real^N) 0`) THEN REWRITE_TAC[] THEN
    STRIP_TAC THENL
     [UNDISCH_TAC `~((W:num->real^N) 0 = v)` THEN ASM_REWRITE_TAC[];
      SUBGOAL_THEN `0 = k` MP_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
          is_forall(concl th) &&
          length(fst(strip_forall(concl th))) = 2 &&
          is_eq(snd(dest_imp(snd(strip_forall(concl th))))))) THEN
        ASM_REWRITE_TAC[LE_0; LE_REFL];
        ASM_ARITH_TAC]];
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY] THEN
    ASM_REWRITE_TAC[]]);;

(* Every edge lies in a PL circle: otherwise the vertices of edges in no   *)
(* circle form a 2-regular graph (the property spreads along vertices and  *)
(* avoids v), and its cycle through such an edge is a circle.             *)

let MOI_SLV_G2_SPREAD = prove
 (`!K (v:real^N) x t1 t2 q.
     moi_slv_graph2 K v /\ {x} IN K /\ ~(x = v) /\
     t1 IN K /\ aff_dim t1 = &1 /\ x IN t1 /\
     t2 IN K /\ aff_dim t2 = &1 /\ x IN t2 /\
     pl_sphere 1 q /\ q SUBSET UNIONS K /\ t2 SUBSET q
     ==> t1 SUBSET q`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_slv_graph2]) THEN
  MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `q:real^N->bool`; `x:real^N`]
    MOI_SLV_CIRCLE_TWO_EDGES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `s1:real^N->bool` (X_CHOOSE_THEN `s2:real^N->bool`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `v:real^N`; `x:real^N`;
                 `s1:real^N->bool`; `s2:real^N->bool`; `t1:real^N->bool`]
    MOI_SLV_G2_EDGES_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[]);;

let MOI_SLV_G2_COVER = prove
 (`!K (v:real^N) s.
     2 <= dimindex(:N) /\ moi_slv_graph2 K v /\ {v} IN K /\
     s IN K /\ aff_dim s = &1
     ==> ?q. pl_sphere 1 q /\ q SUBSET UNIONS K /\ s SUBSET q`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_slv_graph2]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SLV_SC_BASIC) THEN
  SUBGOAL_THEN
   `?bad:(real^N->bool)->bool.
      !t. bad t <=> t IN K /\ aff_dim t = &1 /\
                    ~(?q. pl_sphere 1 q /\ q SUBSET UNIONS K /\ t SUBSET q)`
  (X_CHOOSE_THEN `bad:(real^N->bool)->bool` (LABEL_TAC "bad")) THENL
   [EXISTS_TAC `\t:real^N->bool. t IN K /\ aff_dim t = &1 /\
                 ~(?q. pl_sphere 1 q /\ q SUBSET UNIONS K /\ t SUBSET q)` THEN
    REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  SUBGOAL_THEN `(bad:(real^N->bool)->bool) s` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!t:real^N->bool. bad t ==> ~(v IN t)` (LABEL_TAC "B2") THENL
   [X_GEN_TAC `t:real^N->bool` THEN USE_THEN "bad" (fun th -> REWRITE_TAC[th]) THEN
    STRIP_TAC THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `v:real^N`; `t:real^N->bool`]
      MOI_SLV_G2_LOOP) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x t1 t2:real^N->bool.
      {x} IN K /\ ~(x = v) /\ bad t1 /\ x IN t1 /\
      t2 IN K /\ aff_dim t2 = &1 /\ x IN t2 ==> bad t2`
  (LABEL_TAC "B3") THENL
   [REPEAT GEN_TAC THEN USE_THEN "bad" (fun th -> REWRITE_TAC[th]) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `q:real^N->bool` STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC `~(?q. pl_sphere 1 q /\ q SUBSET UNIONS K /\
                       (t1:real^N->bool) SUBSET q)` THEN
    REWRITE_TAC[] THEN EXISTS_TAC `q:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_SLV_G2_SPREAD THEN
    MAP_EVERY EXISTS_TAC [`K:(real^N->bool)->bool`; `v:real^N`; `x:real^N`;
                          `t2:real^N->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REMOVE_THEN "bad" (K ALL_TAC) THEN
  ABBREV_TAC
   `N2 = {x:real^N | {x} IN K /\ ~(x = v) /\ ?t. bad t /\ x IN t}` THEN
  SUBGOAL_THEN
   `!x:real^N. x IN N2
       ==> ?y z. y IN N2 /\ z IN N2 /\ ~(y = z) /\
                 (~(x = y) /\ segment[x,y] IN K) /\
                 (~(x = z) /\ segment[x,z] IN K) /\
                 !u. u IN N2 /\ (~(x = u) /\ segment[x,u] IN K)
                     ==> u = y \/ u = z`
  (LABEL_TAC "B4") THENL
   [X_GEN_TAC `x:real^N` THEN EXPAND_TAC "N2" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `t1:real^N->bool` STRIP_ASSUME_TAC))) THEN
    MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `v:real^N`; `x:real^N`]
      MOI_SLV_G2_EDGES_SET) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:real^N` (X_CHOOSE_THEN `z:real^N`
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
        (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
          (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
            (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "nb")))))))))) THEN
    SUBGOAL_THEN
     `(bad:(real^N->bool)->bool) (segment[x,y]) /\ bad (segment[x,z])`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN USE_THEN "B3" MATCH_MP_TAC THEN
      MAP_EVERY EXISTS_TAC [`x:real^N`; `t1:real^N->bool`] THEN
      ASM_REWRITE_TAC[AFF_DIM_SEGMENT; ENDS_IN_SEGMENT] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `~(y:real^N = v) /\ ~(z = v)` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
      REMOVE_THEN "B2" (MP_TAC o SPEC `segment[x:real^N,v]`) THEN
      ASM_REWRITE_TAC[ENDS_IN_SEGMENT];
      ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC [`y:real^N`; `z:real^N`] THEN
    EXPAND_TAC "N2" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN FIRST
     [EXISTS_TAC `segment[x:real^N,y]` THEN ASM_REWRITE_TAC[ENDS_IN_SEGMENT] THEN
      NO_TAC;
      EXISTS_TAC `segment[x:real^N,z]` THEN ASM_REWRITE_TAC[ENDS_IN_SEGMENT] THEN
      NO_TAC;
      X_GEN_TAC `u:real^N` THEN STRIP_TAC THEN
      REMOVE_THEN "nb" MATCH_MP_TAC THEN ASM_MESON_TAC[];
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `s:real^N->bool`] MOI_SLV_EDGE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^N` (X_CHOOSE_THEN `w:real^N`
    STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
    concl th = `s = segment[p:real^N,w]`)) THEN
  SUBGOAL_THEN `(p:real^N) IN N2 /\ w IN N2` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "N2" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN FIRST
     [EXISTS_TAC `segment[p:real^N,w]` THEN ASM_REWRITE_TAC[ENDS_IN_SEGMENT] THEN
      NO_TAC;
      DISCH_TAC THEN
      REMOVE_THEN "B2" (MP_TAC o SPEC `segment[p:real^N,w]`) THEN
      ASM_MESON_TAC[ENDS_IN_SEGMENT]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`N2:real^N->bool`; `\x y:real^N. ~(x = y) /\ segment[x,y] IN K`;
                 `p:real^N`] MOI_SCF_CYCLE_PATH) THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{x:real^N | {x} IN K}` THEN
      ASM_SIMP_TAC[MOI_SLV_VERTICES_FINITE] THEN EXPAND_TAC "N2" THEN SET_TAC[];
      REPEAT STRIP_TAC THENL
       [ASM_MESON_TAC[]; ONCE_REWRITE_TAC[SEGMENT_SYM] THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  REWRITE_TAC[moi_scf_path; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `W:num->real^N`
    (CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
      (LABEL_TAC "WV") (CONJUNCTS_THEN2 (LABEL_TAC "WR") (LABEL_TAC "Winj"))))
     (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC)))))) THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  RULE_ASSUM_TAC(CONV_RULE(DEPTH_CONV BETA_CONV)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th ->
    concl th = `(W:num->real^N) 0 = p`)) THEN
  MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `k:num`; `W:num->real^N`]
    MOI_SLV_POLYGON_SPHERE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [USE_THEN "Winj" MP_TAC THEN MESON_TAC[];
      GEN_TAC THEN DISCH_TAC THEN USE_THEN "WR" (MP_TAC o SPEC `i:num`) THEN
      ASM_SIMP_TAC[]];
    DISCH_TAC] THEN
  UNDISCH_TAC `~(?q. pl_sphere 1 q /\ q SUBSET UNIONS K /\
                     segment[(W:num->real^N) 0,w] SUBSET q)` THEN
  REWRITE_TAC[] THEN
  EXISTS_TAC
   `segment[(W:num->real^N) k,W 0] UNION UNIONS {segment[W i,W(SUC i)] | i < k}` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[UNION_SUBSET; UNIONS_SUBSET; FORALL_IN_GSPEC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC(SET_RULE `(s:A->bool) IN f ==> s SUBSET UNIONS f`) THEN
      ASM_REWRITE_TAC[];
      REPEAT STRIP_TAC THEN
      MATCH_MP_TAC(SET_RULE `(s:A->bool) IN f ==> s SUBSET UNIONS f`) THEN
      USE_THEN "WR" (MP_TAC o SPEC `i:num`) THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  REMOVE_THEN "B4" (MP_TAC o SPEC `(W:num->real^N) 0`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:real^N` (X_CHOOSE_THEN `z:real^N`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN
   `(W:num->real^N) 1 IN N2 /\ ~(W 0 = W 1) /\ segment[W 0,W 1] IN K /\
    W k IN N2 /\ ~(W 0 = W k) /\ segment[W 0,W k] IN K /\ ~(W 1 = W k)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [USE_THEN "WV" MATCH_MP_TAC THEN ASM_ARITH_TAC;
      REWRITE_TAC[ARITH_RULE `1 = SUC 0`] THEN USE_THEN "WR" (MP_TAC o SPEC `0`) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; SIMP_TAC[]];
      REWRITE_TAC[ARITH_RULE `1 = SUC 0`] THEN USE_THEN "WR" (MP_TAC o SPEC `0`) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; SIMP_TAC[]];
      USE_THEN "WV" MATCH_MP_TAC THEN ASM_ARITH_TAC;
      FIRST_ASSUM(MP_TAC o CONJUNCT1 o check (fun th ->
        concl th = `~((W:num->real^N) k = W 0) /\ segment[W k,W 0] IN K`)) THEN
      MESON_TAC[];
      ONCE_REWRITE_TAC[SEGMENT_SYM] THEN ASM_REWRITE_TAC[];
      USE_THEN "Winj" (MP_TAC o SPECL [`1`; `k:num`]) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; SIMP_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `w:real^N = W 1 \/ w = W k` MP_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `y:real^N`)) (concl th))) THEN
    DISCH_THEN(fun th -> MP_TAC(SPEC `(W:num->real^N) 1` th) THEN
      MP_TAC(SPEC `(W:num->real^N) k` th) THEN MP_TAC(SPEC `w:real^N` th)) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(DISJ_CASES_THEN SUBST1_TAC) THENL
   [MATCH_MP_TAC(SET_RULE `(s:A->bool) SUBSET u ==> s SUBSET t UNION u`) THEN
    MATCH_MP_TAC(SET_RULE `(s:A->bool) IN f ==> s SUBSET UNIONS f`) THEN
    REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `0` THEN
    REWRITE_TAC[ARITH_RULE `SUC 0 = 1`] THEN ASM_ARITH_TAC;
    SUBGOAL_THEN `segment[(W:num->real^N) 0,W k] = segment[W k,W 0]`
    SUBST1_TAC THENL [REWRITE_TAC[SEGMENT_SYM]; SET_TAC[]]]);;

(* Counting: the edges at v are partitioned by the PL circles through v,   *)
(* two edges each.                                                           *)

let MOI_SLV_G2_COUNT = prove
 (`!K (v:real^N).
     2 <= dimindex(:N) /\ moi_slv_graph2 K v /\ {v} IN K
     ==> CARD {s | s IN K /\ aff_dim s = &1 /\ v IN s} =
         2 * CARD {p | pl_sphere 1 p /\ p SUBSET UNIONS K /\ v IN p}`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_slv_graph2]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SLV_SC_BASIC) THEN
  ABBREV_TAC `P = {p:real^N->bool | pl_sphere 1 p /\ p SUBSET UNIONS K /\ v IN p}` THEN
  ABBREV_TAC
   `A = \p:real^N->bool. {s | s IN K /\ aff_dim s = &1 /\ v IN s /\ s SUBSET p}` THEN
  SUBGOAL_THEN `FINITE (P:(real^N->bool)->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{p:real^N->bool | pl_sphere 1 p /\ p SUBSET UNIONS K}` THEN
    ASM_SIMP_TAC[MOI_SLV_CIRCLES_FINITE] THEN EXPAND_TAC "P" THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!p q (s:real^N->bool).
      p IN P /\ q IN P /\ s IN (A:(real^N->bool)->(real^N->bool)->bool) p /\
      s IN A q ==> p = q`
  (LABEL_TAC "dis") THENL
   [REPEAT GEN_TAC THEN EXPAND_TAC "P" THEN EXPAND_TAC "A" THEN
    REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `s:real^N->bool`; `v:real^N`]
      MOI_SLV_EDGE_AT_VERTEX) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC MOI_SLV_G2_UNIQUE THEN
    MAP_EVERY EXISTS_TAC [`K:(real^N->bool)->bool`; `v:real^N`; `w:real^N`] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(s:real^N->bool) SUBSET p` THEN
    UNDISCH_TAC `(s:real^N->bool) SUBSET q` THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`v:real^N`; `w:real^N`] ENDS_IN_SEGMENT) THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!p:real^N->bool. p IN P ==> (A:(real^N->bool)->(real^N->bool)->bool) p HAS_SIZE 2`
  (LABEL_TAC "two") THENL
   [X_GEN_TAC `p:real^N->bool` THEN DISCH_TAC THEN
    SUBGOAL_THEN `pl_sphere 1 (p:real^N->bool) /\ p SUBSET UNIONS K /\ v IN p`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(p:real^N->bool) IN P` THEN EXPAND_TAC "P" THEN
      REWRITE_TAC[IN_ELIM_THM];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `p:real^N->bool`; `v:real^N`]
      MOI_SLV_CIRCLE_TWO_EDGES) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `s1:real^N->bool` (X_CHOOSE_THEN `s2:real^N->bool`
      STRIP_ASSUME_TAC)) THEN
    MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `v:real^N`; `s1:real^N->bool`]
      MOI_SLV_G2_LOOP) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `q:real^N->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(q:real^N->bool) IN P` ASSUME_TAC THENL
     [EXPAND_TAC "P" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `p:real^N->bool = q` SUBST1_TAC THENL
     [USE_THEN "dis" MATCH_MP_TAC THEN EXISTS_TAC `s1:real^N->bool` THEN
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "A" THEN REWRITE_TAC[IN_ELIM_THM] THEN
      ASM_REWRITE_TAC[];
      EXPAND_TAC "A" THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `{s:real^N->bool | s IN K /\ aff_dim s = &1 /\ v IN s} =
    UNIONS (IMAGE (A:(real^N->bool)->(real^N->bool)->bool) P)`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `s:real^N->bool` THEN
    REWRITE_TAC[IN_ELIM_THM; IN_UNIONS; EXISTS_IN_IMAGE] THEN EQ_TAC THENL
     [STRIP_TAC THEN
      MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `v:real^N`; `s:real^N->bool`]
        MOI_SLV_G2_LOOP) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `q:real^N->bool` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `q:real^N->bool` THEN
      EXPAND_TAC "P" THEN EXPAND_TAC "A" THEN REWRITE_TAC[IN_ELIM_THM] THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      DISCH_THEN(X_CHOOSE_THEN `p:real^N->bool` MP_TAC) THEN
      EXPAND_TAC "A" THEN REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[]];
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) CARD_UNIONS o lhand o snd) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[FINITE_IMAGE; FORALL_IN_IMAGE] THEN CONJ_TAC THENL
     [X_GEN_TAC `p:real^N->bool` THEN DISCH_TAC THEN
      USE_THEN "two" (fun th -> MP_TAC(MATCH_MP th
        (ASSUME `(p:real^N->bool) IN P`))) THEN
      SIMP_TAC[HAS_SIZE];
      REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
      X_GEN_TAC `p:real^N->bool` THEN DISCH_TAC THEN
      X_GEN_TAC `q:real^N->bool` THEN DISCH_TAC THEN DISCH_TAC THEN
      REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
      X_GEN_TAC `s:real^N->bool` THEN STRIP_TAC THEN
      UNDISCH_TAC `~((A:(real^N->bool)->(real^N->bool)->bool) p = A q)` THEN
      REWRITE_TAC[] THEN AP_TERM_TAC THEN USE_THEN "dis" MATCH_MP_TAC THEN
      EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[]];
    DISCH_THEN SUBST1_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) NSUM_IMAGE o lhand o snd) THEN
  ANTS_TAC THENL
   [MAP_EVERY X_GEN_TAC [`p:real^N->bool`; `q:real^N->bool`] THEN STRIP_TAC THEN
    USE_THEN "two" (fun th -> MP_TAC(MATCH_MP th
      (ASSUME `(p:real^N->bool) IN P`))) THEN
    REWRITE_TAC[MOI_SCF_HAS_SIZE_2] THEN
    DISCH_THEN(X_CHOOSE_THEN `a:real^N->bool` (X_CHOOSE_THEN `b:real^N->bool`
      STRIP_ASSUME_TAC)) THEN
    USE_THEN "dis" MATCH_MP_TAC THEN EXISTS_TAC `a:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(A:(real^N->bool)->(real^N->bool)->bool) p = A q` THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[IN_INSERT];
    DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN
   `nsum P (CARD o (A:(real^N->bool)->(real^N->bool)->bool)) = nsum P (\p. 2)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC NSUM_EQ THEN X_GEN_TAC `p:real^N->bool` THEN DISCH_TAC THEN
    REWRITE_TAC[o_THM] THEN USE_THEN "two" (fun th -> MP_TAC(MATCH_MP th
      (ASSUME `(p:real^N->bool) IN P`))) THEN
    SIMP_TAC[HAS_SIZE];
    ASM_SIMP_TAC[NSUM_CONST] THEN ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* 6. The slices of a simplicial complex by a hyperplane meeting every      *)
(* simplex in dimension at most 1 form a simplicial complex (the carrier of *)
(* a vertex of a slice is cut by the hyperplane in exactly that point).    *)
(* ------------------------------------------------------------------------- *)

let MOI_SLV_SLICE_POINT_FACE = prove
 (`!c s (a:real^N) t p.
     simplicial_complex c /\ s IN c /\
     {p} face_of (s INTER {x | a dot x = t})
     ==> ?r. r IN c /\ r INTER {x | a dot x = t} = {p}`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SLV_SC_BASIC) THEN
  SUBGOAL_THEN `(p:real^N) IN s /\ a dot p = t` STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP FACE_OF_IMP_SUBSET) THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `p:real^N`] IN_RELATIVE_INTERIOR_OF_FACE) THEN
  ASM_SIMP_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real^N->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `r:real^N->bool` THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(r INTER {x:real^N | a dot x = t}) face_of
                (s INTER {x | a dot x = t})` ASSUME_TAC THENL
   [MATCH_MP_TAC FACE_OF_SLICE THEN ASM_REWRITE_TAC[CONVEX_HYPERPLANE];
    ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[SING_SUBSET; IN_INTER; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET]] THEN
  MATCH_MP_TAC SUBSET_OF_FACE_OF THEN
  EXISTS_TAC `s INTER {x:real^N | a dot x = t}` THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[FACE_OF_IMP_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN
   `relative_interior(r INTER {x:real^N | a dot x = t}) =
    relative_interior r INTER relative_interior {x | a dot x = t}`
  SUBST1_TAC THENL
   [MATCH_MP_TAC RELATIVE_INTERIOR_INTER THEN
    REWRITE_TAC[CONVEX_HYPERPLANE] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[FACE_OF_IMP_CONVEX]; ALL_TAC] THEN
    SIMP_TAC[RELATIVE_INTERIOR_AFFINE; AFFINE_HYPERPLANE] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `p:real^N` THEN
    ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM];
    SIMP_TAC[RELATIVE_INTERIOR_AFFINE; AFFINE_HYPERPLANE] THEN
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_SING; NOT_IN_EMPTY;
                IN_ELIM_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `p:real^N`) THEN ASM_REWRITE_TAC[]]);;

let MOI_SLV_SLICE_COMPLEX = prove
 (`!c (a:real^N) t.
     simplicial_complex c /\
     (!s. s IN c ==> aff_dim (s INTER {x | a dot x = t}) <= &1)
     ==> simplicial_complex {s INTER {x | a dot x = t} | s IN c}`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SLV_SC_BASIC) THEN
  REWRITE_TAC[simplicial_complex] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[SIMPLE_IMAGE] THEN ASM_SIMP_TAC[FINITE_IMAGE];
    REWRITE_TAC[FORALL_IN_GSPEC] THEN X_GEN_TAC `s:real^N->bool` THEN
    DISCH_TAC THEN MATCH_MP_TAC POLYTOPE_LOWDIM_IMP_SIMPLEX THEN
    ASM_SIMP_TAC[POLYTOPE_INTER_POLYHEDRON; POLYHEDRON_HYPERPLANE];
    REWRITE_TAC[IN_ELIM_THM] THEN
    MAP_EVERY X_GEN_TAC [`f:real^N->bool`; `u:real^N->bool`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `s:real^N->bool`
      STRIP_ASSUME_TAC) ASSUME_TAC) THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    ASM_CASES_TAC `f:real^N->bool = {}` THENL
     [EXISTS_TAC `{}:real^N->bool` THEN REWRITE_TAC[INTER_EMPTY] THEN
      ASM_MESON_TAC[EMPTY_FACE_OF];
      ALL_TAC] THEN
    ASM_CASES_TAC `f = s INTER {x:real^N | a dot x = t}` THENL
     [EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `?p:real^N. f = {p}` STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[GSYM AFF_DIM_EQ_0] THEN
      MP_TAC(ISPECL [`f:real^N->bool`; `s INTER {x:real^N | a dot x = t}`]
        FACE_OF_AFF_DIM_LT) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONVEX_INTER THEN
        ASM_SIMP_TAC[CONVEX_HYPERPLANE];
        ALL_TAC] THEN
      SUBGOAL_THEN `aff_dim (s INTER {x:real^N | a dot x = t}) <= &1` MP_TAC THENL
       [ASM_SIMP_TAC[]; ALL_TAC] THEN
      MP_TAC(ISPEC `f:real^N->bool` AFF_DIM_GE) THEN
      MP_TAC(ISPEC `f:real^N->bool` AFF_DIM_EQ_MINUS1) THEN
      ASM_REWRITE_TAC[] THEN
      SPEC_TAC(`aff_dim (s INTER {x:real^N | a dot x = t})`,`d2:int`) THEN
      SPEC_TAC(`aff_dim (f:real^N->bool)`,`d1:int`) THEN INT_ARITH_TAC;
      ALL_TAC] THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `s:real^N->bool`; `a:real^N`;
                   `t:real`; `p:real^N`] MOI_SLV_SLICE_POINT_FACE) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    REWRITE_TAC[IN_ELIM_THM] THEN
    MAP_EVERY X_GEN_TAC [`u:real^N->bool`; `u':real^N->bool`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `s:real^N->bool`
      STRIP_ASSUME_TAC) (X_CHOOSE_THEN `s':real^N->bool` STRIP_ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SET_RULE
     `(s INTER h) INTER (s' INTER h) = (s INTER s') INTER (h:A->bool)`] THEN
    CONJ_TAC THEN MATCH_MP_TAC FACE_OF_SLICE THEN
    REWRITE_TAC[CONVEX_HYPERPLANE] THEN ASM_MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* 7. The level complex of a generic height on a triangulated PL 2-sphere:  *)
(* every simplex meets a level in dimension at most 1.                       *)
(* ------------------------------------------------------------------------- *)

let MOI_SLV_SPHERE_SURFACE = prove
 (`!c:(real^3->bool)->bool.
     simplicial_complex c /\ pl_sphere 2 (UNIONS c)
     ==> (!s. s IN c ==> aff_dim s <= &2) /\
         (!e. e IN c /\ aff_dim e = &1
              ==> CARD {t | t IN c /\ aff_dim t = &2 /\ e SUBSET t} = 2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `(:3)` MOI_SMO_SURFACE_COMPLEX) THEN
  REWRITE_TAC[MOI_SMO_SURFACE_COMPLEX_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPEC `c:(real^3->bool)->bool`) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[MOI_SCD_PL_SPHERE_2_HOMEOMORPHIC]; SIMP_TAC[]]);;

let MOI_SLV_SC_VERTEX_SING = prove
 (`!c s (w:real^N).
     simplicial_complex c /\ s IN c /\ w extreme_point_of s ==> {w} IN c`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SLV_SC_BASIC) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `s:real^N->bool` THEN
  ASM_REWRITE_TAC[FACE_OF_SING]);;

let MOI_SLV_LEVEL_DIM = prove
 (`!c (a:real^3) t s.
     moi_sch3_generic c a /\ pl_sphere 2 (UNIONS c) /\ s IN c
     ==> aff_dim (s INTER {x | a dot x = t}) <= &1`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_sch3_generic]) THEN
  MP_TAC(ISPEC `c:(real^3->bool)->bool` MOI_SLV_SPHERE_SURFACE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `aff_dim(s:real^3->bool) <= &2` ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `s:real^3->bool`] MOI_SCF_SC_VERTICES) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `V:real^3->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!w:real^3. w IN V ==> {w} IN c` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_SLV_SC_VERTEX_SING THEN
    EXISTS_TAC `s:real^3->bool` THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `affine hull s SUBSET {x:real^3 | a dot x = t}` THENL
   [MATCH_MP_TAC INT_LE_TRANS THEN EXISTS_TAC `aff_dim(s:real^3->bool)` THEN
    SIMP_TAC[AFF_DIM_SUBSET; INTER_SUBSET] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[INT_ARITH `a - &1:int <= &1 <=> a <= &2`; INT_OF_NUM_LE] THEN
    MATCH_MP_TAC(ARITH_RULE `n <= 1 ==> n <= 2`) THEN
    SUBGOAL_THEN `FINITE (V:real^3->bool) /\ CARD V <= 1` (fun th -> REWRITE_TAC[th]) THEN
    ASM_REWRITE_TAC[CARD_LE_1] THEN
    ASM_CASES_TAC `V:real^3->bool = {}` THENL [ASM SET_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(X_CHOOSE_TAC `w0:real^3` o REWRITE_RULE[GSYM MEMBER_NOT_EMPTY]) THEN
    EXISTS_TAC `w0:real^3` THEN REWRITE_TAC[SUBSET; IN_SING] THEN
    X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (find_term ((=) `a:real^3`)) (concl th) && is_forall(concl th))) THEN
    ASM_SIMP_TAC[] THEN
    SUBGOAL_THEN `(V:real^3->bool) SUBSET s` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[HULL_SUBSET]; ALL_TAC] THEN
    SUBGOAL_THEN `(V:real^3->bool) SUBSET {x | a dot x = t}` MP_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `affine hull s:real^3->bool` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `s:real^3->bool` THEN ASM_REWRITE_TAC[HULL_SUBSET];
      ASM SET_TAC[]];
    MATCH_MP_TAC INT_LE_TRANS THEN
    EXISTS_TAC `aff_dim(affine hull s INTER {x:real^3 | a dot x = t})` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC AFF_DIM_SUBSET THEN
      MP_TAC(ISPECL [`affine:(real^3->bool)->bool`; `s:real^3->bool`] HULL_SUBSET) THEN
      SET_TAC[];
      SIMP_TAC[AFF_DIM_AFFINE_INTER_HYPERPLANE; AFFINE_AFFINE_HULL] THEN
      ASM_REWRITE_TAC[AFF_DIM_AFFINE_HULL] THEN
      REPEAT COND_CASES_TAC THEN
      UNDISCH_TAC `aff_dim(s:real^3->bool) <= &2` THEN
      ASM_REWRITE_TAC[] THEN INT_ARITH_TAC]]);;

let MOI_SLV_LEVEL_COMPLEX = prove
 (`!c (a:real^3) t.
     moi_sch3_generic c a /\ pl_sphere 2 (UNIONS c)
     ==> simplicial_complex {s INTER {x | a dot x = t} | s IN c} /\
         (!s. s IN {s INTER {x | a dot x = t} | s IN c} ==> aff_dim s <= &1) /\
         UNIONS {s INTER {x | a dot x = t} | s IN c} =
         UNIONS c INTER {x | a dot x = t}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `simplicial_complex (c:(real^3->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[moi_sch3_generic]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MOI_SLV_SLICE_COMPLEX THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_SLV_LEVEL_DIM THEN
    EXISTS_TAC `c:(real^3->bool)->bool` THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[FORALL_IN_GSPEC] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC MOI_SLV_LEVEL_DIM THEN
    EXISTS_TAC `c:(real^3->bool)->bool` THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[UNIONS_GSPEC; INTER_UNIONS] THEN SET_TAC[]]);;

let MOI_SLV_LEVEL_POLYGONS_EQ = prove
 (`!s (a:real^3) t.
     moi_sch3_level_polygons s a t =
     {p | pl_sphere 1 p /\ p SUBSET s INTER {x | a dot x = t}}`,
  REWRITE_TAC[moi_sch3_level_polygons]);;

(* The theorem LEVEL_POLYGONS_FINITE.                                       *)

let LEVEL_POLYGONS_FINITE = prove
 (MOI_SCH3_LEVEL_POLYGONS_FINITE,
  MAP_EVERY X_GEN_TAC [`c:(real^3->bool)->bool`; `a:real^3`; `t:real`] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `a:real^3`; `t:real`]
    MOI_SLV_LEVEL_COMPLEX) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[MOI_SLV_LEVEL_POLYGONS_EQ] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC MOI_SLV_CIRCLES_FINITE THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* 8. Slices of simplices: crossing points of edges, supporting hyperplanes, *)
(* and a hyperplane through a relative interior point of a simplex of       *)
(* dimension at least 2 meets it in a second point.                          *)
(* ------------------------------------------------------------------------- *)

let MOI_SLV_CROSS_SING = prove
 (`!(a:real^N) t x y.
     a dot x < t /\ t < a dot y
     ==> ?p. segment[x,y] INTER {z | a dot z = t} = {p} /\ p IN segment(x,y)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `?u. &0 < u /\ u < &1 /\ (&1 - u) * a dot (x:real^N) + u * a dot y = t`
  STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `(t - a dot (x:real^N)) / (a dot y - a dot x)` THEN
    SUBGOAL_THEN `&0 < a dot (y:real^N) - a dot x` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_SUB_LT; REAL_LT_LDIV_EQ] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `&0 < a dot (y:real^N) - a dot x` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  EXISTS_TAC `(&1 - u) % x + u % y:real^N` THEN
  SUBGOAL_THEN `~(x:real^N = y)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[IN_SEGMENT] THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `u:real` THEN ASM_REWRITE_TAC[]] THEN
  REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM; IN_SING; IN_SEGMENT] THEN
  X_GEN_TAC `z:real^N` THEN EQ_TAC THENL
   [DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `w:real` STRIP_ASSUME_TAC)
      MP_TAC) THEN
    ASM_REWRITE_TAC[DOT_RADD; DOT_RMUL] THEN DISCH_TAC THEN
    SUBGOAL_THEN `w:real = u` (fun th -> REWRITE_TAC[th]) THEN
    SUBGOAL_THEN `~(a dot (x:real^N) - a dot y = &0)` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `(&1 - w) * a dot (x:real^N) + w * a dot y = t` THEN
    UNDISCH_TAC `(&1 - u) * a dot (x:real^N) + u * a dot y = t` THEN
    CONV_TAC REAL_FIELD;
    DISCH_THEN SUBST1_TAC THEN CONJ_TAC THENL
     [EXISTS_TAC `u:real` THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ASM_REWRITE_TAC[DOT_RADD; DOT_RMUL]]]);;

(* A hyperplane supporting a convex hull of finitely many points meets it  *)
(* in the convex hull of the points on it.                                  *)

let MOI_SLV_HALF_SLICE = prove
 (`!V (a:real^N) t.
     FINITE V /\ (!w. w IN V ==> t <= a dot w)
     ==> convex hull V INTER {x | a dot x = t} =
         convex hull {w | w IN V /\ a dot w = t}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`convex hull V:real^N->bool`; `a:real^N`; `t:real`]
      FACE_OF_INTER_SUPPORTING_HYPERPLANE_GE) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[CONVEX_CONVEX_HULL] THEN
      SUBGOAL_THEN `convex hull V SUBSET {x:real^N | a dot x >= t}`
        (fun th -> SET_TAC[th]) THEN
      MATCH_MP_TAC HULL_MINIMAL THEN REWRITE_TAC[CONVEX_HALFSPACE_GE] THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM; real_ge] THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    DISCH_TAC THEN
    MP_TAC(ISPECL [`V:real^N->bool`;
                   `convex hull V INTER {x:real^N | a dot x = t}`]
      FACE_OF_CONVEX_HULL_SUBSET) THEN
    ASM_SIMP_TAC[FINITE_IMP_COMPACT] THEN
    DISCH_THEN(X_CHOOSE_THEN `V':real^N->bool` (CONJUNCTS_THEN2 ASSUME_TAC
      (LABEL_TAC "eq"))) THEN
    USE_THEN "eq" SUBST1_TAC THEN MATCH_MP_TAC HULL_MONO THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `w:real^N` THEN DISCH_TAC THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(w:real^N) IN convex hull V'` MP_TAC THENL
     [ASM_MESON_TAC[HULL_SUBSET; SUBSET]; ALL_TAC] THEN
    USE_THEN "eq" (fun th -> REWRITE_TAC[GSYM th]) THEN
    REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN SIMP_TAC[];
    REWRITE_TAC[SUBSET_INTER] THEN CONJ_TAC THENL
     [MATCH_MP_TAC HULL_MONO THEN SET_TAC[];
      MATCH_MP_TAC HULL_MINIMAL THEN REWRITE_TAC[CONVEX_HYPERPLANE] THEN
      SET_TAC[]]]);;

let MOI_SLV_HALF_SLICE_LE = prove
 (`!V (a:real^N) t.
     FINITE V /\ (!w. w IN V ==> a dot w <= t)
     ==> convex hull V INTER {x | a dot x = t} =
         convex hull {w | w IN V /\ a dot w = t}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`V:real^N->bool`; `--a:real^N`; `--t:real`] MOI_SLV_HALF_SLICE) THEN
  ASM_SIMP_TAC[DOT_LNEG; REAL_LE_NEG2; REAL_EQ_NEG2]);;

let MOI_SLV_RELINT_SLICE_TWO = prove
 (`!e (a:real^N) t p.
     convex e /\ p IN relative_interior e /\ a dot p = t /\ &2 <= aff_dim e
     ==> ?q. ~(q = p) /\ q IN e /\ a dot q = t`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `L = affine hull e INTER {x:real^N | a dot x = t}` THEN
  SUBGOAL_THEN `affine (L:real^N->bool) /\ (p:real^N) IN L /\ &1 <= aff_dim L`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "L" THEN
    SIMP_TAC[AFFINE_INTER; AFFINE_AFFINE_HULL; AFFINE_HYPERPLANE] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; HULL_SUBSET; SUBSET];
      ALL_TAC] THEN
    SIMP_TAC[AFF_DIM_AFFINE_INTER_HYPERPLANE; AFFINE_AFFINE_HULL] THEN
    REWRITE_TAC[AFF_DIM_AFFINE_HULL] THEN
    REPEAT COND_CASES_TAC THEN TRY(UNDISCH_TAC `&2 <= aff_dim(e:real^N->bool)` THEN
      INT_ARITH_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[EXTENSION; IN_INTER; NOT_IN_EMPTY;
      IN_ELIM_THM] o check (fun th -> is_eq(concl th) &&
        rhs(concl th) = `{}:real^N->bool`)) THEN
    DISCH_THEN(MP_TAC o SPEC `p:real^N`) THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; HULL_SUBSET; SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN `?q0:real^N. q0 IN L /\ ~(q0 = p)` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    SUBGOAL_THEN `L = {p:real^N}` SUBST_ALL_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `&1 <= aff_dim {p:real^N}` THEN
    REWRITE_TAC[AFF_DIM_SING] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `(p:real^N) IN relative_interior e` THEN
  REWRITE_TAC[IN_RELATIVE_INTERIOR] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `r:real`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `&0 < norm(q0 - p:real^N)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT; VECTOR_SUB_EQ]; ALL_TAC] THEN
  SUBGOAL_THEN `?l. &0 < l /\ l * norm(q0 - p:real^N) < r` STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `r / (&2 * norm(q0 - p:real^N))` THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_LT_MUL; REAL_ARITH `&0 < &2`;
      REAL_FIELD `&0 < n ==> m / (&2 * n) * n = m / &2`] THEN
    UNDISCH_TAC `&0 < r` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `(&1 - l) % p + l % q0:real^N` THEN
  SUBGOAL_THEN `(&1 - l) % p + l % q0:real^N IN L` MP_TAC THENL
   [UNDISCH_TAC `affine (L:real^N->bool)` THEN REWRITE_TAC[affine] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXPAND_TAC "L" THEN REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[VECTOR_ARITH `(&1 - l) % p + l % q:real^N = p <=>
                              l % (q - p) = vec 0`] THEN
    ASM_REWRITE_TAC[VECTOR_MUL_EQ_0; VECTOR_SUB_EQ] THEN ASM_REAL_ARITH_TAC;
    FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
    ASM_REWRITE_TAC[IN_INTER; IN_BALL] THEN
    REWRITE_TAC[dist; VECTOR_ARITH `p - ((&1 - l) % p + l % q):real^N =
                                    --(l % (q - p))`; NORM_NEG] THEN
    ASM_SIMP_TAC[NORM_MUL; REAL_ARITH `&0 < l ==> abs l = l`]]);;

(* ------------------------------------------------------------------------- *)
(* 9. The level complex at the level of a vertex v: its vertices other than *)
(* v are crossing points of edges, each in exactly two level edges.         *)
(* ------------------------------------------------------------------------- *)

let MOI_SLV_CONVEX_SIGN = prove
 (`!u x y c. &0 < u /\ u < &1 /\ (&1 - u) * x + u * y = c /\ x < c ==> c < y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`&1 - u`; `c - x`] REAL_LT_MUL) THEN
  MP_TAC(SPECL [`u:real`; `c - y`] REAL_LE_MUL) THEN
  ASM_REAL_ARITH_TAC);;

let MOI_SLV_GENERIC_VERTEX = prove
 (`!c (a:real^3) v w.
     moi_sch3_generic c a /\ {v} IN c /\ {w} IN c /\ a dot w = a dot v
     ==> w = v`,
  REWRITE_TAC[moi_sch3_generic] THEN MESON_TAC[]);;

let MOI_SLV_LEVEL_CARRIER = prove
 (`!c (a:real^3) v s p.
     moi_sch3_generic c a /\ pl_sphere 2 (UNIONS c) /\ {v} IN c /\ s IN c /\
     s INTER {x | a dot x = a dot v} = {p} /\ ~(p = v)
     ==> ?w1 w2. segment[w1,w2] IN c /\ a dot w1 < a dot v /\ a dot v < a dot w2 /\
                 segment[w1,w2] INTER {x | a dot x = a dot v} = {p} /\
                 p IN segment(w1,w2)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_sch3_generic]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SLV_SC_BASIC) THEN
  MP_TAC(ISPEC `c:(real^3->bool)->bool` MOI_SLV_SPHERE_SURFACE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(p:real^3) IN s /\ a dot p = a dot v` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `s INTER {x:real^3 | a dot x = a dot v} = {p}` THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `p:real^3`] IN_RELATIVE_INTERIOR_OF_FACE) THEN
  ASM_SIMP_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real^3->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(e:real^3->bool) IN c` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(p:real^3) IN e` ASSUME_TAC THENL
   [ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `e INTER {x:real^3 | a dot x = a dot v} = {p}` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`s:real^3->bool`; `e:real^3->bool`] FACE_OF_IMP_SUBSET) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `s INTER {x:real^3 | a dot x = a dot v}` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC(SET_RULE `(e:A->bool) SUBSET s ==> e INTER h SUBSET s INTER h`) THEN
        ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[SUBSET_REFL]];
      ASM_REWRITE_TAC[SING_SUBSET; IN_INTER; IN_ELIM_THM]];
    ALL_TAC] THEN
  SUBGOAL_THEN `aff_dim(e:real^3->bool) = &1` ASSUME_TAC THENL
   [SUBGOAL_THEN `aff_dim(e:real^3->bool) <= &2` MP_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `~(aff_dim(e:real^3->bool) = -- &1)` MP_TAC THENL
     [REWRITE_TAC[AFF_DIM_EQ_MINUS1; GSYM MEMBER_NOT_EMPTY] THEN
      EXISTS_TAC `p:real^3` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `~(aff_dim(e:real^3->bool) = &0)` MP_TAC THENL
     [REWRITE_TAC[AFF_DIM_EQ_0] THEN
      DISCH_THEN(X_CHOOSE_THEN `q:real^3` SUBST_ALL_TAC) THEN
      UNDISCH_TAC `~(p:real^3 = v)` THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC MOI_SLV_GENERIC_VERTEX THEN
      MAP_EVERY EXISTS_TAC [`c:(real^3->bool)->bool`; `a:real^3`] THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[IN_SING];
      ALL_TAC] THEN
    SUBGOAL_THEN `~(aff_dim(e:real^3->bool) = &2)` MP_TAC THENL
     [DISCH_TAC THEN
      MP_TAC(ISPECL [`e:real^3->bool`; `a:real^3`; `a dot (v:real^3)`; `p:real^3`]
        MOI_SLV_RELINT_SLICE_TWO) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[INT_LE_REFL] THEN ASM_MESON_TAC[FACE_OF_IMP_CONVEX];
        ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `q:real^3` STRIP_ASSUME_TAC) THEN
      UNDISCH_TAC `e INTER {x:real^3 | a dot x = a dot v} = {p}` THEN
      REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM; IN_SING] THEN
      DISCH_THEN(MP_TAC o SPEC `q:real^3`) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPEC `e:real^3->bool` AFF_DIM_GE) THEN
    SPEC_TAC(`aff_dim(e:real^3->bool)`,`d:int`) THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `e:real^3->bool`] MOI_SLV_EDGE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `w1:real^3` (X_CHOOSE_THEN `w2:real^3`
    STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  SUBGOAL_THEN `(p:real^3) IN segment(w1,w2)` ASSUME_TAC THENL
   [UNDISCH_TAC `(p:real^3) IN relative_interior(segment[w1,w2])` THEN
    ASM_REWRITE_TAC[RELATIVE_INTERIOR_SEGMENT];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(a dot (w1:real^3) = a dot v)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `w1:real^3 = v` SUBST_ALL_TAC THENL
     [MATCH_MP_TAC MOI_SLV_GENERIC_VERTEX THEN
      MAP_EVERY EXISTS_TAC [`c:(real^3->bool)->bool`; `a:real^3`] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `~(p:real^3 = v)` THEN REWRITE_TAC[] THEN
    UNDISCH_TAC `segment[v:real^3,w2] INTER {x | a dot x = a dot v} = {p}` THEN
    REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM; IN_SING] THEN
    DISCH_THEN(MP_TAC o SPEC `v:real^3`) THEN REWRITE_TAC[ENDS_IN_SEGMENT] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(a dot (w2:real^3) = a dot v)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `w2:real^3 = v` SUBST_ALL_TAC THENL
     [MATCH_MP_TAC MOI_SLV_GENERIC_VERTEX THEN
      MAP_EVERY EXISTS_TAC [`c:(real^3->bool)->bool`; `a:real^3`] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `~(p:real^3 = v)` THEN REWRITE_TAC[] THEN
    UNDISCH_TAC `segment[w1:real^3,v] INTER {x | a dot x = a dot v} = {p}` THEN
    REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM; IN_SING] THEN
    DISCH_THEN(MP_TAC o SPEC `v:real^3`) THEN REWRITE_TAC[ENDS_IN_SEGMENT] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?u. &0 < u /\ u < &1 /\ p = (&1 - u) % w1 + u % (w2:real^3)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(p:real^3) IN segment(w1,w2)` THEN
    REWRITE_TAC[IN_SEGMENT] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(&1 - u) * a dot (w1:real^3) + u * a dot w2 = a dot v`
  ASSUME_TAC THENL
   [UNDISCH_TAC `a dot (p:real^3) = a dot v` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[DOT_RADD; DOT_RMUL];
    ALL_TAC] THEN
  ASM_CASES_TAC `a dot (w1:real^3) < a dot v` THENL
   [MAP_EVERY EXISTS_TAC [`w1:real^3`; `w2:real^3`] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_SLV_CONVEX_SIGN THEN
    MAP_EVERY EXISTS_TAC [`u:real`; `a dot (w1:real^3)`] THEN
    ASM_REWRITE_TAC[];
    MAP_EVERY EXISTS_TAC [`w2:real^3`; `w1:real^3`] THEN
    ONCE_REWRITE_TAC[SEGMENT_SYM] THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `--c < --y ==> y < c`) THEN
      MATCH_MP_TAC MOI_SLV_CONVEX_SIGN THEN
      MAP_EVERY EXISTS_TAC [`u:real`; `--(a dot (w1:real^3))`] THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [UNDISCH_TAC `(&1 - u) * a dot (w1:real^3) + u * a dot w2 = a dot v` THEN
        REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC];
      ASM_REAL_ARITH_TAC]]);;

(* An edge at v meets the level of v only in v.                             *)

let MOI_SLV_VERTEX_EDGE_SLICE = prove
 (`!c (a:real^3) v w.
     moi_sch3_generic c a /\ {v} IN c /\ segment[v,w] IN c /\ ~(w = v)
     ==> segment[v,w] INTER {x | a dot x = a dot v} = {v}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `simplicial_complex (c:(real^3->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[moi_sch3_generic]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `v:real^3`; `w:real^3`]
    MOI_SLV_SEGMENT_ENDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(a dot (w:real^3) = a dot v)` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `~(w:real^3 = v)` THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_SLV_GENERIC_VERTEX THEN
    MAP_EVERY EXISTS_TAC [`c:(real^3->bool)->bool`; `a:real^3`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN
  SUBGOAL_THEN `{u:real^3 | u IN {v,w} /\ a dot u = a dot v} = {v}`
  ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `a dot (v:real^3) < a dot w` THENL
   [MP_TAC(ISPECL [`{v:real^3,w}`; `a:real^3`; `a dot (v:real^3)`]
      MOI_SLV_HALF_SLICE);
    MP_TAC(ISPECL [`{v:real^3,w}`; `a:real^3`; `a dot (v:real^3)`]
      MOI_SLV_HALF_SLICE_LE)] THEN
  ASM_REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY; FORALL_IN_INSERT;
                  NOT_IN_EMPTY; CONVEX_HULL_SING] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC);;

(* A triangle over a crossing edge meets the level in a segment.            *)

let MOI_SLV_TRI_CROSS = prove
 (`!c (a:real^3) v w1 w2 tau p.
     moi_sch3_generic c a /\ pl_sphere 2 (UNIONS c) /\ {v} IN c /\
     segment[w1,w2] IN c /\ a dot w1 < a dot v /\ a dot v < a dot w2 /\
     segment[w1,w2] INTER {x | a dot x = a dot v} = {p} /\
     tau IN c /\ aff_dim tau = &2 /\ segment[w1,w2] SUBSET tau
     ==> aff_dim(tau INTER {x | a dot x = a dot v}) = &1`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_sch3_generic]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SLV_SC_BASIC) THEN
  SUBGOAL_THEN `(p:real^3) IN segment[w1,w2] /\ a dot p = a dot v`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `segment[w1:real^3,w2] INTER {x | a dot x = a dot v} = {p}` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(w1:real^3 = w2)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `w1:real^3`; `w2:real^3`;
                 `tau:real^3->bool`] MOI_SCF_TRIANGLE_ON_EDGE) THEN
  ASM_REWRITE_TAC[GSYM SEGMENT_CONVEX_HULL] THEN
  DISCH_THEN(X_CHOOSE_THEN `w3:real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `segment[w1:real^3,w3] IN c /\ segment[w3,w2] IN c /\ {w3} IN c`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (find_term ((=) `(face_of):(real^3->bool)->(real^3->bool)->bool`))
        (concl th) && length(fst(strip_forall(concl th))) = 2)) THEN
    EXISTS_TAC `tau:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
    REWRITE_TAC[SEGMENT_CONVEX_HULL] THENL
     [EXISTS_TAC `{w1:real^3,w3}`; EXISTS_TAC `{w3:real^3,w2}`;
      EXISTS_TAC `{w3:real^3}` THEN REWRITE_TAC[CONVEX_HULL_SING]] THEN
    REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?q:real^3. ~(q = p) /\ q IN tau /\ a dot q = a dot v`
  STRIP_ASSUME_TAC THENL
   [ASM_CASES_TAC `a dot (w3:real^3) = a dot v` THENL
     [EXISTS_TAC `w3:real^3` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [DISCH_THEN SUBST_ALL_TAC THEN
        MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `p:real^3`; `w1:real^3`;
                       `w2:real^3`] MOI_SLV_VERTEX_IN_SEGMENT) THEN
        ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
        FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_REAL_ARITH_TAC;
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HULL_INC THEN SET_TAC[]];
      ALL_TAC] THEN
    ASM_CASES_TAC `a dot (w3:real^3) < a dot v` THENL
     [MP_TAC(ISPECL [`a:real^3`; `a dot (v:real^3)`; `w3:real^3`; `w2:real^3`]
        MOI_SLV_CROSS_SING) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `q:real^3` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `q:real^3` THEN
      SUBGOAL_THEN `(q:real^3) IN segment[w3,w2] /\ a dot q = a dot v`
      STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `segment[w3:real^3,w2] INTER {z | a dot z = a dot v} = {q}` THEN
        SET_TAC[];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [DISCH_THEN SUBST_ALL_TAC THEN
        MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `w1:real^3`; `w2:real^3`;
                       `w3:real^3`; `w2:real^3`] MOI_SLV_SEGMENTS_INTER) THEN
        ANTS_TAC THENL
         [ASM_REWRITE_TAC[SEGMENT_EQ] THEN
          REWRITE_TAC[EXTENSION; IN_INSERT; NOT_IN_EMPTY] THEN
          DISCH_THEN(MP_TAC o SPEC `w1:real^3`) THEN ASM_REWRITE_TAC[] THEN
          ASM_MESON_TAC[];
          ALL_TAC] THEN
        REWRITE_TAC[SUBSET; IN_INTER; IN_INSERT; NOT_IN_EMPTY] THEN
        DISCH_THEN(MP_TAC o SPEC `p:real^3`) THEN ASM_REWRITE_TAC[] THEN
        STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_REAL_ARITH_TAC;
        ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `(q:real^3) IN segment[w3,w2]` THEN
        SPEC_TAC(`q:real^3`,`q:real^3`) THEN REWRITE_TAC[GSYM SUBSET] THEN
        REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN MATCH_MP_TAC HULL_MONO THEN
        SET_TAC[]];
      MP_TAC(ISPECL [`a:real^3`; `a dot (v:real^3)`; `w1:real^3`; `w3:real^3`]
        MOI_SLV_CROSS_SING) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `q:real^3` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `q:real^3` THEN
      SUBGOAL_THEN `(q:real^3) IN segment[w1,w3] /\ a dot q = a dot v`
      STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `segment[w1:real^3,w3] INTER {z | a dot z = a dot v} = {q}` THEN
        SET_TAC[];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [DISCH_THEN SUBST_ALL_TAC THEN
        MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `w1:real^3`; `w2:real^3`;
                       `w1:real^3`; `w3:real^3`] MOI_SLV_SEGMENTS_INTER) THEN
        ANTS_TAC THENL
         [ASM_REWRITE_TAC[SEGMENT_EQ] THEN
          REWRITE_TAC[EXTENSION; IN_INSERT; NOT_IN_EMPTY] THEN
          DISCH_THEN(MP_TAC o SPEC `w2:real^3`) THEN ASM_REWRITE_TAC[] THEN
          ASM_MESON_TAC[];
          ALL_TAC] THEN
        REWRITE_TAC[SUBSET; IN_INTER; IN_INSERT; NOT_IN_EMPTY] THEN
        DISCH_THEN(MP_TAC o SPEC `p:real^3`) THEN ASM_REWRITE_TAC[] THEN
        STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_REAL_ARITH_TAC;
        ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `(q:real^3) IN segment[w1,w3]` THEN
        SPEC_TAC(`q:real^3`,`q:real^3`) THEN REWRITE_TAC[GSYM SUBSET] THEN
        REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN MATCH_MP_TAC HULL_MONO THEN
        SET_TAC[]]];
    ALL_TAC] THEN
  MATCH_MP_TAC(INT_ARITH `&1 <= a /\ a <= &1 ==> a:int = &1`) THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`{p:real^3,q}`; `tau INTER {x:real^3 | a dot x = a dot v}`]
      AFF_DIM_SUBSET) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET; IN_INTER; IN_ELIM_THM] THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[SUBSET];
      ASM_REWRITE_TAC[AFF_DIM_2] THEN COND_CASES_TAC THEN
      ASM_MESON_TAC[INT_LE_REFL]];
    MATCH_MP_TAC MOI_SLV_LEVEL_DIM THEN
    EXISTS_TAC `c:(real^3->bool)->bool` THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* 10. The level complex at the level of a vertex v is a degree-2 graph off *)
(* v, and its edges at v correspond to the crossing link edges of v.         *)
(* ------------------------------------------------------------------------- *)

let MOI_SLV_SC_INTER = prove
 (`!K s t:real^N->bool.
     simplicial_complex K /\ s IN K /\ t IN K
     ==> (s INTER t) face_of s /\ (s INTER t) face_of t /\ (s INTER t) IN K`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SLV_SC_BASIC) THEN
  ASM_SIMP_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  EXISTS_TAC `s:real^N->bool` THEN ASM_SIMP_TAC[]);;

let MOI_SLV_LEVEL_EDGES_AT = prove
 (`!c (a:real^3) v p.
     moi_sch3_generic c a /\ pl_sphere 2 (UNIONS c) /\ {v} IN c /\
     {p} IN {s INTER {x | a dot x = a dot v} | s IN c} /\ ~(p = v)
     ==> {s | s IN {s INTER {x | a dot x = a dot v} | s IN c} /\
              aff_dim s = &1 /\ p IN s} HAS_SIZE 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_sch3_generic]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SLV_SC_BASIC) THEN
  MP_TAC(ISPEC `c:(real^3->bool)->bool` MOI_SLV_SPHERE_SURFACE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `s0:real^3->bool` (CONJUNCTS_THEN2 ASSUME_TAC
    (ASSUME_TAC o SYM)) o
    REWRITE_RULE[IN_ELIM_THM] o check (fun th -> aconv (concl th)
      `{p:real^3} IN {s INTER {x | a dot x = a dot v} | s IN c}`)) THEN
  MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `a:real^3`; `v:real^3`;
                 `s0:real^3->bool`; `p:real^3`] MOI_SLV_LEVEL_CARRIER) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `w1:real^3` (X_CHOOSE_THEN `w2:real^3`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `~(w1:real^3 = w2)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `{t:real^3->bool | t IN c /\ aff_dim t = &2 /\ segment[w1,w2] SUBSET t} HAS_SIZE 2` ASSUME_TAC THENL
   [REWRITE_TAC[HAS_SIZE] THEN CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `c:(real^3->bool)->bool` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[AFF_DIM_SEGMENT]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `{s | s IN {s INTER {x | a dot x = a dot v} | s IN c} /\
         aff_dim s = &1 /\ p IN s} =
    IMAGE (\t:real^3->bool. t INTER {x | a dot x = a dot v})
      {t:real^3->bool | t IN c /\ aff_dim t = &2 /\ segment[w1,w2] SUBSET t}`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `sig:real^3->bool` THEN
    REWRITE_TAC[IN_ELIM_THM; IN_IMAGE] THEN EQ_TAC THENL
     [DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `s:real^3->bool`
        STRIP_ASSUME_TAC) STRIP_ASSUME_TAC) THEN
      FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
        lhs(concl th) = `sig:real^3->bool`)) THEN
      EXISTS_TAC `s:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `segment[w1:real^3,w2] SUBSET s` ASSUME_TAC THENL
       [MATCH_MP_TAC MOI_SCF_RELINT_SUBSET THEN
        MAP_EVERY EXISTS_TAC [`c:(real^3->bool)->bool`; `p:real^3`] THEN
        ASM_REWRITE_TAC[RELATIVE_INTERIOR_SEGMENT] THEN ASM_MESON_TAC[IN_INTER];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `aff_dim(s:real^3->bool) <= &2` MP_TAC THENL
       [ASM_SIMP_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `&1 <= aff_dim(s:real^3->bool)` MP_TAC THENL
       [MP_TAC(ISPECL [`segment[w1:real^3,w2]`; `s:real^3->bool`] AFF_DIM_SUBSET) THEN
        ASM_REWRITE_TAC[AFF_DIM_SEGMENT];
        ALL_TAC] THEN
      SUBGOAL_THEN `~(aff_dim(s:real^3->bool) = &1)` MP_TAC THENL
       [DISCH_TAC THEN
        SUBGOAL_THEN `segment[w1:real^3,w2] = s` SUBST_ALL_TAC THENL
         [MATCH_MP_TAC MOI_SCF_SUBSET_DIM_EQ THEN
          EXISTS_TAC `c:(real^3->bool)->bool` THEN
          ASM_REWRITE_TAC[AFF_DIM_SEGMENT];
          ALL_TAC] THEN
        UNDISCH_TAC `aff_dim (s INTER {x:real^3 | a dot x = a dot v}) = &1` THEN
        ASM_REWRITE_TAC[AFF_DIM_SING] THEN INT_ARITH_TAC;
        ALL_TAC] THEN
      SPEC_TAC(`aff_dim(s:real^3->bool)`,`d:int`) THEN INT_ARITH_TAC;
      DISCH_THEN(X_CHOOSE_THEN `t:real^3->bool` STRIP_ASSUME_TAC) THEN
      FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
        lhs(concl th) = `sig:real^3->bool`)) THEN
      CONJ_TAC THENL [EXISTS_TAC `t:real^3->bool` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC MOI_SLV_TRI_CROSS THEN
        MAP_EVERY EXISTS_TAC [`c:(real^3->bool)->bool`; `w1:real^3`;
                              `w2:real^3`; `p:real^3`] THEN
        ASM_REWRITE_TAC[];
        UNDISCH_TAC `segment[w1:real^3,w2] INTER {x | a dot x = a dot v} = {p}` THEN
        UNDISCH_TAC `segment[w1:real^3,w2] SUBSET t` THEN SET_TAC[]]];
    ALL_TAC] THEN
  MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`t1:real^3->bool`; `t2:real^3->bool`] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  SUBGOAL_THEN `aff_dim(t1 INTER {x:real^3 | a dot x = a dot v}) = &1`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_SLV_TRI_CROSS THEN
    MAP_EVERY EXISTS_TAC [`c:(real^3->bool)->bool`; `w1:real^3`;
                          `w2:real^3`; `p:real^3`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `t1:real^3->bool`; `t2:real^3->bool`]
    MOI_SLV_SC_INTER) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `t1 INTER t2:real^3->bool = segment[w1,w2]` ASSUME_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOI_SCF_SUBSET_DIM_EQ THEN
    EXISTS_TAC `c:(real^3->bool)->bool` THEN
    ASM_REWRITE_TAC[SUBSET_INTER; AFF_DIM_SEGMENT] THEN
    MATCH_MP_TAC(INT_ARITH `&1 <= a /\ a < &2 ==> &1 = a:int`) THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`segment[w1:real^3,w2]`; `t1 INTER t2:real^3->bool`]
        AFF_DIM_SUBSET) THEN
      ASM_REWRITE_TAC[SUBSET_INTER; AFF_DIM_SEGMENT];
      FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        concl th = `aff_dim(t1:real^3->bool) = &2`)) THEN
      MATCH_MP_TAC FACE_OF_AFF_DIM_LT THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
      DISCH_TAC THEN UNDISCH_TAC `~(t1:real^3->bool = t2)` THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC MOI_SCF_SUBSET_DIM_EQ THEN
      EXISTS_TAC `c:(real^3->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `t1 INTER t2:real^3->bool = t1` THEN SET_TAC[]];
    ALL_TAC] THEN
  UNDISCH_TAC `aff_dim(t1 INTER {x:real^3 | a dot x = a dot v}) = &1` THEN
  SUBGOAL_THEN `t1 INTER {x:real^3 | a dot x = a dot v} = {p}` SUBST1_TAC THENL
   [UNDISCH_TAC `t1 INTER {x:real^3 | a dot x = a dot v} =
                 t2 INTER {x | a dot x = a dot v}` THEN
    UNDISCH_TAC `t1 INTER t2:real^3->bool = segment[w1,w2]` THEN
    UNDISCH_TAC `segment[w1:real^3,w2] INTER {x | a dot x = a dot v} = {p}` THEN
    UNDISCH_TAC `segment[w1:real^3,w2] SUBSET t1` THEN SET_TAC[];
    REWRITE_TAC[AFF_DIM_SING] THEN INT_ARITH_TAC]);;

let MOI_SLV_LEVEL_GRAPH2 = prove
 (`!c (a:real^3) v.
     moi_sch3_generic c a /\ pl_sphere 2 (UNIONS c) /\ {v} IN c
     ==> moi_slv_graph2 {s INTER {x | a dot x = a dot v} | s IN c} v /\
         {v} IN {s INTER {x | a dot x = a dot v} | s IN c}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `a:real^3`; `a dot (v:real^3)`]
    MOI_SLV_LEVEL_COMPLEX) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN CONJ_TAC THENL
   [REWRITE_TAC[moi_slv_graph2] THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_SLV_LEVEL_EDGES_AT THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `{v:real^3}` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[]]);;

let MOI_SLV_CONE_SLICE_ONE_SIDE = prove
 (`!V (a:real^N) v.
     FINITE V /\
     ((!w. w IN V ==> a dot v < a dot w) \/ (!w. w IN V ==> a dot w < a dot v))
     ==> convex hull (v INSERT V) INTER {x | a dot x = a dot v} = {v}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `{u:real^N | u IN v INSERT V /\ a dot u = a dot v} = {v}`
  ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY] THEN
    X_GEN_TAC `u:real^N` THEN EQ_TAC THENL [ALL_TAC; MESON_TAC[]] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `u:real^N`) THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    ALL_TAC;
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY] THEN
    X_GEN_TAC `u:real^N` THEN EQ_TAC THENL [ALL_TAC; MESON_TAC[]] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `u:real^N`) THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THENL
   [MP_TAC(ISPECL [`v INSERT V:real^N->bool`; `a:real^N`; `a dot (v:real^N)`]
      MOI_SLV_HALF_SLICE);
    MP_TAC(ISPECL [`v INSERT V:real^N->bool`; `a:real^N`; `a dot (v:real^N)`]
      MOI_SLV_HALF_SLICE_LE)] THEN
  ASM_REWRITE_TAC[FINITE_INSERT; FORALL_IN_INSERT; REAL_LE_REFL;
                  CONVEX_HULL_SING] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]);;

(* ------------------------------------------------------------------------- *)
(* 11. The level edges at v are the slices of the triangles over the        *)
(* crossing link edges of v; hence they number moi_sch3_crossings c a v.     *)
(* ------------------------------------------------------------------------- *)

let MOI_SLV_LINK_CROSS_SLICE = prove
 (`!c (a:real^3) v x y.
     moi_sch3_generic c a /\ pl_sphere 2 (UNIONS c) /\ {v} IN c /\
     segment[x,y] IN simplicial_link c v /\ a dot x < a dot v /\ a dot v < a dot y
     ==> convex hull (v INSERT segment[x,y]) IN c /\
         aff_dim (convex hull (v INSERT segment[x,y]) INTER
                  {z | a dot z = a dot v}) = &1 /\
         aff_dim (convex hull (v INSERT segment[x,y])) = &2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `simplicial_complex (c:(real^3->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[moi_sch3_generic]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `v:real^3`; `segment[x:real^3,y]`]
    MOI_SCF_LINK_JOIN) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(x:real^3 = y)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[AFF_DIM_SEGMENT] THEN CONV_TAC INT_REDUCE_CONV THEN
  MATCH_MP_TAC(INT_ARITH `&1 <= a /\ a <= &1 ==> a:int = &1`) THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC MOI_SLV_LEVEL_DIM THEN EXISTS_TAC `c:(real^3->bool)->bool` THEN
    ASM_REWRITE_TAC[]] THEN
  MP_TAC(ISPECL [`a:real^3`; `a dot (v:real^3)`; `x:real^3`; `y:real^3`]
    MOI_SLV_CROSS_SING) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(q:real^3) IN segment[x,y] /\ a dot q = a dot v`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `segment[x:real^3,y] INTER {z | a dot z = a dot v} = {q}` THEN
    SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`{v:real^3,q}`;
    `convex hull (v INSERT segment[x,y]) INTER {z:real^3 | a dot z = a dot v}`]
    AFF_DIM_SUBSET) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET; IN_INTER; IN_ELIM_THM] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `segment[x:real^3,y] SUBSET convex hull (v INSERT segment[x,y])` THEN
    UNDISCH_TAC `(q:real^3) IN segment[x,y]` THEN SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[AFF_DIM_2] THEN COND_CASES_TAC THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_MESON_TAC[]; INT_ARITH_TAC]);;

let MOI_SLV_STAR_EDGE_LINK = prove
 (`!c (a:real^3) v l.
     moi_sch3_generic c a /\ pl_sphere 2 (UNIONS c) /\ {v} IN c /\
     l IN simplicial_link c v /\
     aff_dim (convex hull (v INSERT l) INTER {x | a dot x = a dot v}) = &1
     ==> ?x y. l = segment[x,y] /\ a dot x < a dot v /\ a dot v < a dot y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_sch3_generic]) THEN
  MP_TAC(ISPEC `c:(real^3->bool)->bool` MOI_SLV_SPHERE_SURFACE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `v:real^3`; `l:real^3->bool`]
    MOI_SCF_LINK_JOIN) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(l:real^3->bool) IN c` ASSUME_TAC THENL
   [UNDISCH_TAC `(l:real^3->bool) IN simplicial_link c v` THEN
    REWRITE_TAC[simplicial_link; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `l:real^3->bool`] MOI_SCF_SC_VERTICES) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `V:real^3->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!w:real^3. w IN V ==> ~(a dot w = a dot v)` ASSUME_TAC THENL
   [X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `w:real^3 = v` SUBST_ALL_TAC THENL
     [MATCH_MP_TAC MOI_SLV_GENERIC_VERTEX THEN
      MAP_EVERY EXISTS_TAC [`c:(real^3->bool)->bool`; `a:real^3`] THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_SLV_SC_VERTEX_SING THEN
      EXISTS_TAC `l:real^3->bool` THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `~((v:real^3) IN l)` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC HULL_INC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?x y:real^3. x IN V /\ y IN V /\ a dot x < a dot v /\ a dot v < a dot y`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`V:real^3->bool`; `a:real^3`; `v:real^3`]
      MOI_SLV_CONE_SLICE_ONE_SIDE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      ASM_CASES_TAC `?x:real^3. x IN V /\ a dot x < a dot v` THENL
       [DISJ2_TAC THEN X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
        FIRST_X_ASSUM(X_CHOOSE_THEN `x:real^3` STRIP_ASSUME_TAC) THEN
        SUBGOAL_THEN `~(a dot (w:real^3) = a dot v)` MP_TAC THENL
         [ASM_SIMP_TAC[]; ALL_TAC] THEN
        MATCH_MP_TAC(REAL_ARITH `~(v < w) ==> ~(w = v) ==> w < v`) THEN
        DISCH_TAC THEN
        UNDISCH_TAC `~(?x y:real^3. x IN V /\ y IN V /\ a dot x < a dot v /\
                                     a dot v < a dot y)` THEN
        REWRITE_TAC[] THEN MAP_EVERY EXISTS_TAC [`x:real^3`; `w:real^3`] THEN
        ASM_REWRITE_TAC[];
        DISJ1_TAC THEN X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
        SUBGOAL_THEN `~(a dot (w:real^3) = a dot v)` MP_TAC THENL
         [ASM_SIMP_TAC[]; ALL_TAC] THEN
        MATCH_MP_TAC(REAL_ARITH `~(w < v) ==> ~(w = v) ==> v < w`) THEN
        DISCH_TAC THEN
        UNDISCH_TAC `~(?x:real^3. x IN V /\ a dot x < a dot v)` THEN
        REWRITE_TAC[] THEN EXISTS_TAC `w:real^3` THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    DISCH_TAC THEN
    UNDISCH_TAC
     `aff_dim (convex hull (v INSERT l) INTER {x:real^3 | a dot x = a dot v}) = &1` THEN
    FIRST_ASSUM((fun th -> REWRITE_TAC[th]) o check (fun th ->
      concl th = `l = convex hull (V:real^3->bool)`)) THEN
    REWRITE_TAC[MOI_SCF_HULL_INSERT_HULL] THEN ASM_REWRITE_TAC[AFF_DIM_SING] THEN
    INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(x:real^3 = y)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `CARD (V:real^3->bool) <= 2` ASSUME_TAC THENL
   [SUBGOAL_THEN `aff_dim (convex hull (v INSERT l):real^3->bool) <= &2` MP_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SPEC_TAC(`CARD(V:real^3->bool)`,`n:num`) THEN
    REWRITE_TAC[GSYM INT_OF_NUM_LE] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `V = {x:real^3,y}` SUBST_ALL_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC CARD_SUBSET_EQ THEN
    ASM_REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET] THEN
    MP_TAC(ISPECL [`{x:real^3,y}`; `V:real^3->bool`] CARD_SUBSET) THEN
    ASM_REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET] THEN
    ASM_SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY; IN_INSERT;
                 NOT_IN_EMPTY] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`x:real^3`; `y:real^3`] THEN
  ASM_REWRITE_TAC[SEGMENT_CONVEX_HULL]);;

let MOI_SLV_LEVEL_STAR = prove
 (`!c (a:real^3) v.
     moi_sch3_generic c a /\ pl_sphere 2 (UNIONS c) /\ {v} IN c
     ==> CARD {s | s IN {s INTER {x | a dot x = a dot v} | s IN c} /\
                   aff_dim s = &1 /\ v IN s} =
         moi_sch3_crossings c a v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_sch3_generic]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SLV_SC_BASIC) THEN
  MP_TAC(ISPEC `c:(real^3->bool)->bool` MOI_SLV_SPHERE_SURFACE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[moi_sch3_crossings] THEN
  SUBGOAL_THEN
   `{s | s IN {s INTER {x | a dot x = a dot v} | s IN c} /\
         aff_dim s = &1 /\ v IN s} =
    IMAGE (\l:real^3->bool. convex hull (v INSERT l) INTER {x | a dot x = a dot v})
      {e | e IN simplicial_link c v /\
           ?x y. e = segment[x,y] /\ a dot x < a dot v /\ a dot v < a dot y}`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `sig:real^3->bool` THEN
    REWRITE_TAC[IN_ELIM_THM; IN_IMAGE] THEN EQ_TAC THENL
     [DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `s:real^3->bool`
        STRIP_ASSUME_TAC) STRIP_ASSUME_TAC) THEN
      FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
        lhs(concl th) = `sig:real^3->bool`)) THEN
      MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `v:real^3`; `s:real^3->bool`]
        MOI_SCF_LINK_OPP) THEN
      ANTS_TAC THENL [ASM_MESON_TAC[IN_INTER]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `l:real^3->bool` STRIP_ASSUME_TAC) THEN
      FIRST_X_ASSUM SUBST_ALL_TAC THEN
      EXISTS_TAC `l:real^3->bool` THEN REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC MOI_SLV_STAR_EDGE_LINK THEN
      EXISTS_TAC `c:(real^3->bool)->bool` THEN ASM_REWRITE_TAC[];
      DISCH_THEN(X_CHOOSE_THEN `l:real^3->bool` (CONJUNCTS_THEN2 ASSUME_TAC
        (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `x:real^3`
          (X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC))))) THEN
      FIRST_X_ASSUM SUBST_ALL_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
      MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `a:real^3`; `v:real^3`;
                     `x:real^3`; `y:real^3`] MOI_SLV_LINK_CROSS_SLICE) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL
       [EXISTS_TAC `convex hull (v INSERT segment[x:real^3,y])` THEN
        ASM_REWRITE_TAC[];
        REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN
        MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_INSERT]]];
    ALL_TAC] THEN
  MATCH_MP_TAC CARD_IMAGE_INJ THEN CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `c:(real^3->bool)->bool` THEN
    ASM_REWRITE_TAC[SUBSET; IN_ELIM_THM; simplicial_link] THEN MESON_TAC[]] THEN
  MAP_EVERY X_GEN_TAC [`l1:real^3->bool`; `l2:real^3->bool`] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `x1:real^3` (X_CHOOSE_THEN `y1:real^3` STRIP_ASSUME_TAC)))
   (CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `x2:real^3` (X_CHOOSE_THEN `y2:real^3` STRIP_ASSUME_TAC)))
    ASSUME_TAC)) THEN
  MATCH_MP_TAC MOI_SCF_LINK_JOIN_INJ THEN
  MAP_EVERY EXISTS_TAC [`c:(real^3->bool)->bool`; `v:real^3`] THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY (fun (x,y,l) ->
    MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `a:real^3`; `v:real^3`; x; y]
      MOI_SLV_LINK_CROSS_SLICE) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; STRIP_TAC])
   [(`x1:real^3`,`y1:real^3`,`l1:real^3->bool`);
    (`x2:real^3`,`y2:real^3`,`l2:real^3->bool`)] THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
    is_var(lhs(concl th)) &&
    (lhs(concl th) = `l1:real^3->bool` || lhs(concl th) = `l2:real^3->bool`)))) THEN
  ABBREV_TAC `t1 = convex hull (v INSERT segment[x1:real^3,y1])` THEN
  ABBREV_TAC `t2 = convex hull (v INSERT segment[x2:real^3,y2])` THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `t1:real^3->bool`; `t2:real^3->bool`]
    MOI_SLV_SC_INTER) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(v:real^3) IN t1 INTER t2` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["t1"; "t2"] THEN REWRITE_TAC[IN_INTER] THEN
    CONJ_TAC THEN MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_INSERT];
    ALL_TAC] THEN
  SUBGOAL_THEN `aff_dim(t1 INTER t2:real^3->bool) = &1` ASSUME_TAC THENL
   [MATCH_MP_TAC(INT_ARITH `&1 <= a /\ a < &2 ==> a:int = &1`) THEN CONJ_TAC THENL
     [MATCH_MP_TAC INT_LE_TRANS THEN
      EXISTS_TAC `aff_dim(t1 INTER {x:real^3 | a dot x = a dot v})` THEN
      CONJ_TAC THENL [ASM_REWRITE_TAC[INT_LE_REFL]; ALL_TAC] THEN
      MATCH_MP_TAC AFF_DIM_SUBSET THEN
      UNDISCH_TAC `t1 INTER {x:real^3 | a dot x = a dot v} =
                   t2 INTER {x | a dot x = a dot v}` THEN SET_TAC[];
      FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        concl th = `aff_dim(t1:real^3->bool) = &2`)) THEN
      MATCH_MP_TAC FACE_OF_AFF_DIM_LT THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
      DISCH_TAC THEN UNDISCH_TAC `~(t1:real^3->bool = t2)` THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC MOI_SCF_SUBSET_DIM_EQ THEN
      EXISTS_TAC `c:(real^3->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `t1 INTER t2:real^3->bool = t1` THEN SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `t1 INTER t2:real^3->bool`; `v:real^3`]
    MOI_SLV_EDGE_AT_VERTEX) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^3` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `a:real^3`; `v:real^3`; `w:real^3`]
    MOI_SLV_VERTEX_EDGE_SLICE) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_TAC THEN
  UNDISCH_TAC `aff_dim(t1 INTER {x:real^3 | a dot x = a dot v}) = &1` THEN
  SUBGOAL_THEN `t1 INTER {x:real^3 | a dot x = a dot v} = {v}` SUBST1_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [SUBGOAL_THEN `t1 INTER {x:real^3 | a dot x = a dot v} SUBSET
                    (t1 INTER t2) INTER {x | a dot x = a dot v}` MP_TAC THENL
       [UNDISCH_TAC `t1 INTER {x:real^3 | a dot x = a dot v} =
                     t2 INTER {x | a dot x = a dot v}` THEN SET_TAC[];
        ASM_REWRITE_TAC[]];
      UNDISCH_TAC `(v:real^3) IN t1 INTER t2` THEN SET_TAC[]];
    REWRITE_TAC[AFF_DIM_SING] THEN INT_ARITH_TAC]);;

(* The theorem SINGULAR_POLYGONS: the circles through v pair off the        *)
(* crossing link edges of v.                                                *)

let SINGULAR_POLYGONS = prove
 (MOI_SCH3_SINGULAR_POLYGONS,
  MAP_EVERY X_GEN_TAC [`c:(real^3->bool)->bool`; `a:real^3`; `v:real^3`] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `a:real^3`; `a dot (v:real^3)`]
    MOI_SLV_LEVEL_COMPLEX) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `a:real^3`; `v:real^3`]
    MOI_SLV_LEVEL_GRAPH2) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`{s INTER {x:real^3 | a dot x = a dot v} | s IN c}`; `v:real^3`]
    MOI_SLV_G2_COUNT) THEN
  ASM_REWRITE_TAC[DIMINDEX_3; ARITH] THEN
  MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `a:real^3`; `v:real^3`]
    MOI_SLV_LEVEL_STAR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `{p | p IN moi_sch3_level_polygons (UNIONS c) a (a dot v) /\ v IN p} =
    {p | pl_sphere 1 p /\
         p SUBSET UNIONS {s INTER {x:real^3 | a dot x = a dot v} | s IN c} /\
         v IN p}`
  SUBST1_TAC THENL
   [ASM_REWRITE_TAC[MOI_SLV_LEVEL_POLYGONS_EQ; IN_ELIM_THM; CONJ_ASSOC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SIMP_TAC[EVEN_MULT; ARITH_EVEN; DIV_MULT; ARITH_EQ]);;

(* ------------------------------------------------------------------------- *)
(* 11. Two hyperplanes cutting a simplex with the same sign pattern on its  *)
(* vertices: the slices are empty together, singletons together, and the   *)
(* pattern is read off from crossing edges and vertices in the hyperplane.  *)
(* ------------------------------------------------------------------------- *)

let MOI_SLV_SLICE_CROSS_EXISTS = prove
 (`!W (a:real^N) t.
     FINITE W /\ ~(convex hull W INTER {x | a dot x = t} = {}) /\
     ~(?w. w IN W /\ a dot w = t)
     ==> ?x y. x IN W /\ y IN W /\ a dot x < t /\ t < a dot y`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `{w:real^N | w IN W /\ a dot w = t} = {}` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `!w:real^N. w IN W ==> t <= a dot w` THENL
   [MP_TAC(ISPECL [`W:real^N->bool`; `a:real^N`; `t:real`] MOI_SLV_HALF_SLICE) THEN
    ASM_REWRITE_TAC[CONVEX_HULL_EMPTY];
    ALL_TAC] THEN
  ASM_CASES_TAC `!w:real^N. w IN W ==> a dot w <= t` THENL
   [MP_TAC(ISPECL [`W:real^N->bool`; `a:real^N`; `t:real`]
      MOI_SLV_HALF_SLICE_LE) THEN
    ASM_REWRITE_TAC[CONVEX_HULL_EMPTY];
    ALL_TAC] THEN
  ASM_MESON_TAC[REAL_NOT_LE]);;

let MOI_SLV_AFFIND_HULL_INTER = prove
 (`!W A B:real^N->bool.
     ~affine_dependent W /\ A SUBSET W /\ B SUBSET W
     ==> convex hull A INTER convex hull B = convex hull (A INTER B)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `{A:real^N->bool,B}` CONVEX_HULL_INTERS) THEN
  REWRITE_TAC[UNIONS_2; INTERS_2] THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC AFFINE_INDEPENDENT_SUBSET THEN
    EXISTS_TAC `W:real^N->bool` THEN ASM_REWRITE_TAC[UNION_SUBSET];
    ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[SIMPLE_IMAGE; IMAGE_CLAUSES; INTERS_2]);;

let MOI_SLV_SIGN_NONEMPTY = prove
 (`!W (a:real^N) t a' t'.
     FINITE W /\
     (!w. w IN W ==> (a dot w < t <=> a' dot w < t') /\
                     (a dot w = t <=> a' dot w = t')) /\
     ~(convex hull W INTER {x | a dot x = t} = {})
     ==> ~(convex hull W INTER {x | a' dot x = t'} = {})`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "sa")
    ASSUME_TAC)) THEN
  ASM_CASES_TAC `?w:real^N. w IN W /\ a dot w = t` THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC) THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `w:real^N` THEN
    REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[HULL_SUBSET; SUBSET]; ALL_TAC] THEN
    USE_THEN "sa" (fun th -> MP_TAC(MATCH_MP (SPEC `w:real^N` th)
      (ASSUME `(w:real^N) IN W`))) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`W:real^N->bool`; `a:real^N`; `t:real`]
    MOI_SLV_SLICE_CROSS_EXISTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:real^N` (X_CHOOSE_THEN `y:real^N`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `a' dot (x:real^N) < t' /\ t' < a' dot (y:real^N)` MP_TAC THENL
   [MP_TAC(ASSUME `(a:real^N) dot x < t`) THEN
    MP_TAC(ASSUME `t < (a:real^N) dot y`) THEN
    USE_THEN "sa" (MP_TAC o SPEC `x:real^N`) THEN
    USE_THEN "sa" (MP_TAC o SPEC `y:real^N`) THEN
    REWRITE_TAC[ASSUME `(x:real^N) IN W`; ASSUME `(y:real^N) IN W`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP MOI_SLV_CROSS_SING) THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `segment[x:real^N,y] SUBSET convex hull W` MP_TAC THENL
   [REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN MATCH_MP_TAC HULL_MONO THEN
    ASM_REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET];
    ALL_TAC] THEN
  UNDISCH_TAC `segment[x:real^N,y] INTER {z | a' dot z = t'} = {p}` THEN
  SET_TAC[]);;

let MOI_SLV_SIGN_SING = prove
 (`!W (a:real^N) t a' t' p.
     ~affine_dependent W /\
     (!w. w IN W ==> (a dot w < t <=> a' dot w < t') /\
                     (a dot w = t <=> a' dot w = t')) /\
     convex hull W INTER {x | a dot x = t} = {p}
     ==> ?q. convex hull W INTER {x | a' dot x = t'} = {q}`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "sa")
    ASSUME_TAC)) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP AFFINE_INDEPENDENT_IMP_FINITE) THEN
  SUBGOAL_THEN `(p:real^N) IN convex hull W /\ a dot p = t` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `convex hull W INTER {x:real^N | a dot x = t} = {p}` THEN
    REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM; IN_SING] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!w:real^N. w IN W /\ a dot w = t ==> w = p` (LABEL_TAC "lev") THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(w:real^N) IN convex hull W INTER {x | a dot x = t}` MP_TAC THENL
     [REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN ASM_MESON_TAC[HULL_SUBSET; SUBSET];
      ASM_REWRITE_TAC[IN_SING]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x y:real^N. x IN W /\ y IN W /\ a dot x < t /\ t < a dot y
                 ==> p IN segment[x,y]` (LABEL_TAC "crs") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`a:real^N`; `t:real`; `x:real^N`; `y:real^N`]
      MOI_SLV_CROSS_SING) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `q:real^N` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `segment[x:real^N,y] SUBSET convex hull W` MP_TAC THENL
     [REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN MATCH_MP_TAC HULL_MONO THEN
      ASM_REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET];
      ALL_TAC] THEN
    UNDISCH_TAC `convex hull W INTER {x:real^N | a dot x = t} = {p}` THEN
    UNDISCH_TAC `segment[x:real^N,y] INTER {z | a dot z = t} = {q}` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!A B:real^N->bool. A SUBSET W /\ B SUBSET W
                 ==> convex hull A INTER convex hull B = convex hull (A INTER B)`
    (LABEL_TAC "ind") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_SLV_AFFIND_HULL_INTER THEN
    EXISTS_TAC `W:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `(p:real^N) IN W` THENL
   [SUBGOAL_THEN `(!w:real^N. w IN W DELETE p ==> t < a dot w) \/
                  (!w:real^N. w IN W DELETE p ==> a dot w < t)` ASSUME_TAC THENL
     [REWRITE_TAC[IN_DELETE] THEN
      MATCH_MP_TAC(TAUT `(~p /\ ~q ==> F) ==> p \/ q`) THEN
      REWRITE_TAC[NOT_FORALL_THM; NOT_IMP] THEN
      DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `w1:real^N` STRIP_ASSUME_TAC)
        (X_CHOOSE_THEN `w2:real^N` STRIP_ASSUME_TAC)) THEN
      SUBGOAL_THEN `~((a:real^N) dot w1 = t) /\ ~((a:real^N) dot w2 = t)`
        STRIP_ASSUME_TAC THENL
       [USE_THEN "lev" (MP_TAC o SPEC `w1:real^N`) THEN
        USE_THEN "lev" (MP_TAC o SPEC `w2:real^N`) THEN
        REWRITE_TAC[ASSUME `(w1:real^N) IN W`; ASSUME `(w2:real^N) IN W`;
                    ASSUME `~(w1:real^N = p)`; ASSUME `~(w2:real^N = p)`] THEN
        CONV_TAC TAUT;
        ALL_TAC] THEN
      SUBGOAL_THEN `(a:real^N) dot w1 < t /\ t < a dot w2` STRIP_ASSUME_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `(p:real^N) IN segment[w1,w2]` ASSUME_TAC THENL
       [USE_THEN "crs" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      USE_THEN "ind" (MP_TAC o SPECL [`{p:real^N}`; `{w1:real^N,w2}`]) THEN
      REWRITE_TAC[SING_SUBSET; INSERT_SUBSET; EMPTY_SUBSET; CONVEX_HULL_SING;
                  GSYM SEGMENT_CONVEX_HULL; ASSUME `(p:real^N) IN W`;
                  ASSUME `(w1:real^N) IN W`; ASSUME `(w2:real^N) IN W`] THEN
      SUBGOAL_THEN `{p:real^N} INTER {w1,w2} = {}` SUBST1_TAC THENL
       [UNDISCH_TAC `~(w1:real^N = p)` THEN UNDISCH_TAC `~(w2:real^N = p)` THEN
        SET_TAC[];
        ALL_TAC] THEN
      REWRITE_TAC[CONVEX_HULL_EMPTY] THEN
      UNDISCH_TAC `(p:real^N) IN segment[w1,w2]` THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(a':real^N) dot p = t'` ASSUME_TAC THENL
     [USE_THEN "sa" (fun th -> MP_TAC(MATCH_MP (SPEC `p:real^N` th)
        (ASSUME `(p:real^N) IN W`))) THEN
      ASM_REWRITE_TAC[] THEN MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(!w:real^N. w IN W DELETE p ==> a' dot p < a' dot w) \/
                  (!w:real^N. w IN W DELETE p ==> a' dot w < a' dot p)`
      ASSUME_TAC THENL
     [FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
       [DISJ1_TAC; DISJ2_TAC] THEN
      X_GEN_TAC `w:real^N` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `w:real^N`) THEN
      USE_THEN "sa" (MP_TAC o SPEC `w:real^N`) THEN
      UNDISCH_TAC `(w:real^N) IN W DELETE p` THEN
      UNDISCH_TAC `(a':real^N) dot p = t'` THEN
      REWRITE_TAC[IN_DELETE] THEN DISCH_THEN SUBST1_TAC THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    EXISTS_TAC `p:real^N` THEN
    SUBGOAL_THEN `W = (p:real^N) INSERT (W DELETE p)` SUBST1_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `{x:real^N | a' dot x = t'} = {x | a' dot x = a' dot p}`
      SUBST1_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC MOI_SLV_CONE_SLICE_ONE_SIDE THEN
    ASM_REWRITE_TAC[FINITE_DELETE];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(?w:real^N. w IN W /\ a dot w = t)` ASSUME_TAC THENL
   [REWRITE_TAC[NOT_EXISTS_THM] THEN X_GEN_TAC `w:real^N` THEN STRIP_TAC THEN
    SUBGOAL_THEN `w:real^N = p` SUBST_ALL_TAC THENL
     [USE_THEN "lev" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`W:real^N->bool`; `a:real^N`; `t:real`]
    MOI_SLV_SLICE_CROSS_EXISTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[NOT_INSERT_EMPTY]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:real^N` (X_CHOOSE_THEN `y:real^N`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `(p:real^N) IN segment[x,y]` ASSUME_TAC THENL
   [USE_THEN "crs" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `W = {x:real^N,y}` SUBST_ALL_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_INSERT; NOT_IN_EMPTY] THEN X_GEN_TAC `w:real^N` THEN
    EQ_TAC THENL [ALL_TAC; STRIP_TAC THEN ASM_REWRITE_TAC[]] THEN DISCH_TAC THEN
    MATCH_MP_TAC(TAUT `(~p /\ ~q ==> F) ==> p \/ q`) THEN STRIP_TAC THEN
    SUBGOAL_THEN `~((a:real^N) dot w = t)` ASSUME_TAC THENL
     [UNDISCH_TAC `~(?w:real^N. w IN W /\ a dot w = t)` THEN
      REWRITE_TAC[NOT_EXISTS_THM] THEN
      DISCH_THEN(MP_TAC o SPEC `w:real^N`) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_CASES_TAC `(a:real^N) dot w < t` THENL
     [SUBGOAL_THEN `(p:real^N) IN segment[w,y]` ASSUME_TAC THENL
       [USE_THEN "crs" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      USE_THEN "ind" (MP_TAC o SPECL [`{w:real^N,y}`; `{x:real^N,y}`]) THEN
      REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET; GSYM SEGMENT_CONVEX_HULL;
                  ASSUME `(w:real^N) IN W`; ASSUME `(x:real^N) IN W`;
                  ASSUME `(y:real^N) IN W`] THEN
      SUBGOAL_THEN `{w:real^N,y} INTER {x,y} = {y}` SUBST1_TAC THENL
       [UNDISCH_TAC `~(w:real^N = x)` THEN SET_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[CONVEX_HULL_SING] THEN DISCH_TAC THEN
      SUBGOAL_THEN `p:real^N = y` SUBST_ALL_TAC THENL
       [UNDISCH_TAC `segment[w:real^N,y] INTER segment[x,y] = {y}` THEN
        UNDISCH_TAC `(p:real^N) IN segment[w,y]` THEN
        UNDISCH_TAC `(p:real^N) IN segment[x,y]` THEN SET_TAC[];
        ALL_TAC] THEN
      UNDISCH_TAC `t < (a:real^N) dot y` THEN ASM_REWRITE_TAC[REAL_LT_REFL];
      SUBGOAL_THEN `t < (a:real^N) dot w` ASSUME_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `(p:real^N) IN segment[x,w]` ASSUME_TAC THENL
       [USE_THEN "crs" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      USE_THEN "ind" (MP_TAC o SPECL [`{x:real^N,w}`; `{x:real^N,y}`]) THEN
      REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET; GSYM SEGMENT_CONVEX_HULL;
                  ASSUME `(w:real^N) IN W`; ASSUME `(x:real^N) IN W`;
                  ASSUME `(y:real^N) IN W`] THEN
      SUBGOAL_THEN `{x:real^N,w} INTER {x,y} = {x}` SUBST1_TAC THENL
       [UNDISCH_TAC `~(w:real^N = y)` THEN SET_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[CONVEX_HULL_SING] THEN DISCH_TAC THEN
      SUBGOAL_THEN `p:real^N = x` SUBST_ALL_TAC THENL
       [UNDISCH_TAC `segment[x:real^N,w] INTER segment[x,y] = {x}` THEN
        UNDISCH_TAC `(p:real^N) IN segment[x,w]` THEN
        UNDISCH_TAC `(p:real^N) IN segment[x,y]` THEN SET_TAC[];
        ALL_TAC] THEN
      UNDISCH_TAC `(a:real^N) dot x < t` THEN ASM_REWRITE_TAC[REAL_LT_REFL]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`a':real^N`; `t':real`; `x:real^N`; `y:real^N`]
    MOI_SLV_CROSS_SING) THEN
  ANTS_TAC THENL
   [USE_THEN "sa" (MP_TAC o SPEC `x:real^N`) THEN
    USE_THEN "sa" (MP_TAC o SPEC `y:real^N`) THEN
    REWRITE_TAC[IN_INSERT] THEN
    UNDISCH_TAC `(a:real^N) dot x < t` THEN UNDISCH_TAC `t < (a:real^N) dot y` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM SEGMENT_CONVEX_HULL] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:real^N` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `q:real^N` THEN ASM_REWRITE_TAC[]);;

(* The same for the simplices of a simplicial complex, with the sign        *)
(* pattern given on all its vertices.                                        *)

let MOI_SLV_SC_SIMPLEX_VERTS = prove
 (`!c (s:real^N->bool).
     simplicial_complex c /\ s IN c
     ==> ?W. ~affine_dependent W /\ s = convex hull W /\ !w. w IN W ==> {w} IN c`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?n. n simplex (s:real^N->bool)` MP_TAC THENL
   [ASM_MESON_TAC[simplicial_complex]; ALL_TAC] THEN
  REWRITE_TAC[SIMPLEX] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:int` (X_CHOOSE_THEN `W:real^N->bool`
    STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `W:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `w:real^N` THEN DISCH_TAC THEN
  MATCH_MP_TAC MOI_SLV_SC_VERTEX_SING THEN
  EXISTS_TAC `s:real^N->bool` THEN
  ASM_SIMP_TAC[EXTREME_POINT_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
  ASM_MESON_TAC[]);;

let MOI_SLV_SC_SIGN_NONEMPTY = prove
 (`!c (a:real^N) t a' t' r.
     simplicial_complex c /\
     (!x. {x} IN c ==> (a dot x < t <=> a' dot x < t') /\
                       (a dot x = t <=> a' dot x = t')) /\
     r IN c /\ ~(r INTER {x | a dot x = t} = {})
     ==> ~(r INTER {x | a' dot x = t'} = {})`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "sa")
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `r:real^N->bool`]
    MOI_SLV_SC_SIMPLEX_VERTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `W:real^N->bool` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `~(r INTER {x:real^N | a dot x = t} = {})` THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC MOI_SLV_SIGN_NONEMPTY THEN
  MAP_EVERY EXISTS_TAC [`a:real^N`; `t:real`] THEN
  ASM_SIMP_TAC[AFFINE_INDEPENDENT_IMP_FINITE] THEN
  X_GEN_TAC `w:real^N` THEN DISCH_TAC THEN
  USE_THEN "sa" MATCH_MP_TAC THEN ASM_MESON_TAC[]);;

let MOI_SLV_SC_SIGN_SING = prove
 (`!c (a:real^N) t a' t' r p.
     simplicial_complex c /\
     (!x. {x} IN c ==> (a dot x < t <=> a' dot x < t') /\
                       (a dot x = t <=> a' dot x = t')) /\
     r IN c /\ r INTER {x | a dot x = t} = {p}
     ==> ?q. r INTER {x | a' dot x = t'} = {q}`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "sa")
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `r:real^N->bool`]
    MOI_SLV_SC_SIMPLEX_VERTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `W:real^N->bool` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `r INTER {x:real^N | a dot x = t} = {p}` THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC MOI_SLV_SIGN_SING THEN
  MAP_EVERY EXISTS_TAC [`a:real^N`; `t:real`; `p:real^N`] THEN
  ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `w:real^N` THEN DISCH_TAC THEN
  USE_THEN "sa" MATCH_MP_TAC THEN ASM_MESON_TAC[]);;

let MOI_SLV_SC_SIGN_WD = prove
 (`!c (a:real^N) t a' t' r1 r2 p q1 q2.
     simplicial_complex c /\
     (!x. {x} IN c ==> (a dot x < t <=> a' dot x < t') /\
                       (a dot x = t <=> a' dot x = t')) /\
     r1 IN c /\ r2 IN c /\
     r1 INTER {x | a dot x = t} = {p} /\ r2 INTER {x | a dot x = t} = {p} /\
     r1 INTER {x | a' dot x = t'} = {q1} /\ r2 INTER {x | a' dot x = t'} = {q2}
     ==> q1 = q2`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "sa")
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `a:real^N`; `t:real`; `a':real^N`;
                 `t':real`; `r1 INTER r2:real^N->bool`] MOI_SLV_SC_SIGN_NONEMPTY) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[MOI_SLV_SC_INTER];
      UNDISCH_TAC `r1 INTER {x:real^N | a dot x = t} = {p}` THEN
      UNDISCH_TAC `r2 INTER {x:real^N | a dot x = t} = {p}` THEN SET_TAC[]];
    UNDISCH_TAC `r1 INTER {x:real^N | a' dot x = t'} = {q1}` THEN
    UNDISCH_TAC `r2 INTER {x:real^N | a' dot x = t'} = {q2}` THEN SET_TAC[]]);;

let MOI_SLV_SLICE_POINT_SUBFACE = prove
 (`!c s (a:real^N) t p.
     simplicial_complex c /\ s IN c /\
     p extreme_point_of (s INTER {x | a dot x = t})
     ==> ?r. r IN c /\ r face_of s /\ r INTER {x | a dot x = t} = {p}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `s:real^N->bool`; `a:real^N`; `t:real`;
                 `p:real^N`] MOI_SLV_SLICE_POINT_FACE) THEN
  ASM_REWRITE_TAC[FACE_OF_SING] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real^N->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `r INTER s:real^N->bool` THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `r:real^N->bool`; `s:real^N->bool`]
    MOI_SLV_SC_INTER) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(p:real^N) IN s` MP_TAC THENL
   [UNDISCH_TAC `(p:real^N) extreme_point_of (s INTER {x | a dot x = t})` THEN
    REWRITE_TAC[extreme_point_of; IN_INTER] THEN MESON_TAC[];
    UNDISCH_TAC `r INTER {x:real^N | a dot x = t} = {p}` THEN SET_TAC[]]);;

let MOI_SLV_SLICE_CC = prove
 (`!c (s:real^N->bool) b u.
     simplicial_complex c /\ s IN c
     ==> convex (s INTER {x | b dot x = u}) /\ compact (s INTER {x | b dot x = u})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `polytope (s:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_PTR_SIMPLICIAL_COMPLEX_POLYTOPE]; ALL_TAC] THEN
  ASM_SIMP_TAC[CONVEX_INTER; CONVEX_HYPERPLANE; POLYTOPE_IMP_CONVEX;
               COMPACT_INTER_CLOSED; CLOSED_HYPERPLANE; POLYTOPE_IMP_COMPACT]);;

(* ------------------------------------------------------------------------- *)
(* 12. Slices by two hyperplanes with the same sign pattern on the vertices *)
(* are PL homeomorphic: the simplexwise affine map of the first slice       *)
(* complex sending each slice vertex to the corresponding slice vertex of  *)
(* the same simplex maps each slice onto the other slice.                   *)
(* ------------------------------------------------------------------------- *)

let MOI_SLV_AFFINE_IMAGE_HULL = prove
 (`!(l:real^M->real^N) y s.
     linear l
     ==> IMAGE (\x. l x + y) (convex hull s) =
         convex hull (IMAGE (\x. l x + y) s)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\x:real^M. (l:real^M->real^N) x + y) = (\x. y + x) o l`
    SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM] THEN REPEAT GEN_TAC THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[IMAGE_o; CONVEX_HULL_TRANSLATION] THEN
  ASM_SIMP_TAC[CONVEX_HULL_LINEAR_IMAGE]);;

let MOI_SLV_SLICE_IMAGE = prove
 (`!c (a:real^N) t a' t' (h:real^N->real^N) s l y.
     simplicial_complex c /\
     (!x. {x} IN c ==> (a dot x < t <=> a' dot x < t') /\
                       (a dot x = t <=> a' dot x = t')) /\
     (!r p q. r IN c /\ r INTER {x | a dot x = t} = {p} /\
              r INTER {x | a' dot x = t'} = {q} ==> h p = q) /\
     s IN c /\ linear l /\
     (!x. x IN s INTER {x | a dot x = t} ==> h x = l x + y)
     ==> IMAGE h (s INTER {x | a dot x = t}) = s INTER {x | a' dot x = t'}`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "sa")
    (CONJUNCTS_THEN2 (LABEL_TAC "hv") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "hl")))))) THEN
  SUBGOAL_THEN
   `IMAGE (h:real^N->real^N) {p | p extreme_point_of (s INTER {x | a dot x = t})} =
    {q | q extreme_point_of (s INTER {x | a' dot x = t'})}` ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN X_GEN_TAC `q:real^N` THEN
    EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `p:real^N` (CONJUNCTS_THEN2 SUBST1_TAC
        ASSUME_TAC)) THEN
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `s:real^N->bool`; `a:real^N`;
                     `t:real`; `p:real^N`] MOI_SLV_SLICE_POINT_SUBFACE) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `r:real^N->bool` STRIP_ASSUME_TAC) THEN
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `a:real^N`; `t:real`; `a':real^N`;
                     `t':real`; `r:real^N->bool`; `p:real^N`]
        MOI_SLV_SC_SIGN_SING) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `q0:real^N` ASSUME_TAC) THEN
      SUBGOAL_THEN `(h:real^N->real^N) p = q0` SUBST1_TAC THENL
       [USE_THEN "hv" MATCH_MP_TAC THEN EXISTS_TAC `r:real^N->bool` THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      REWRITE_TAC[GSYM FACE_OF_SING] THEN
      SUBGOAL_THEN `{q0:real^N} = r INTER {x | a' dot x = t'}` SUBST1_TAC THENL
       [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC FACE_OF_SLICE THEN ASM_REWRITE_TAC[CONVEX_HYPERPLANE];
      DISCH_TAC THEN
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `s:real^N->bool`; `a':real^N`;
                     `t':real`; `q:real^N`] MOI_SLV_SLICE_POINT_SUBFACE) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `r:real^N->bool` STRIP_ASSUME_TAC) THEN
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `a':real^N`; `t':real`; `a:real^N`;
                     `t:real`; `r:real^N->bool`; `q:real^N`]
        MOI_SLV_SC_SIGN_SING) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `p:real^N` ASSUME_TAC) THEN
      EXISTS_TAC `p:real^N` THEN CONJ_TAC THENL
       [CONV_TAC SYM_CONV THEN USE_THEN "hv" MATCH_MP_TAC THEN
        EXISTS_TAC `r:real^N->bool` THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[GSYM FACE_OF_SING] THEN
        SUBGOAL_THEN `{p:real^N} = r INTER {x | a dot x = t}` SUBST1_TAC THENL
         [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        MATCH_MP_TAC FACE_OF_SLICE THEN ASM_REWRITE_TAC[CONVEX_HYPERPLANE]]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (h:real^N->real^N) (s INTER {x:real^N | a dot x = t}) =
    IMAGE (\x. (l:real^N->real^N) x + y)
      (convex hull {p | p extreme_point_of (s INTER {x | a dot x = t})}) /\
    s INTER {x:real^N | a' dot x = t'} =
    convex hull {p | p extreme_point_of (s INTER {x | a' dot x = t'})}`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [CONJ_TAC THENL
     [TRANS_TAC EQ_TRANS
       `IMAGE (\x. (l:real^N->real^N) x + y) (s INTER {x:real^N | a dot x = t})` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC IMAGE_EQ THEN
        USE_THEN "hl" (fun th -> REWRITE_TAC[th]);
        AP_TERM_TAC];
      ALL_TAC] THEN
    MATCH_MP_TAC KREIN_MILMAN_MINKOWSKI THEN
    ASM_MESON_TAC[MOI_SLV_SLICE_CC];
    ALL_TAC] THEN
  ASM_SIMP_TAC[MOI_SLV_AFFINE_IMAGE_HULL] THEN AP_TERM_TAC THEN
  TRANS_TAC EQ_TRANS
   `IMAGE (h:real^N->real^N) {p | p extreme_point_of (s INTER {x | a dot x = t})}` THEN
  CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[]] THEN
  MATCH_MP_TAC IMAGE_EQ THEN
  X_GEN_TAC `z:real^N` THEN REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(z:real^N) IN s INTER {x | a dot x = t}` ASSUME_TAC THENL
   [ASM_MESON_TAC[extreme_point_of]; ALL_TAC] THEN
  USE_THEN "hl" (fun th -> REWRITE_TAC[MATCH_MP th
    (ASSUME `(z:real^N) IN s INTER {x | a dot x = t}`)]));;

let MOI_SLV_SLICE_MAP = prove
 (`!c (a:real^N) t a' t'.
     simplicial_complex c /\
     simplicial_complex {s INTER {x | a dot x = t} | s IN c} /\
     (!x. {x} IN c ==> (a dot x < t <=> a' dot x < t') /\
                       (a dot x = t <=> a' dot x = t'))
     ==> ?h. (!s. s IN c
                  ==> ?l y. linear l /\
                            !x. x IN s INTER {x | a dot x = t} ==> h x = l x + y) /\
             (!s. s IN c
                  ==> IMAGE h (s INTER {x | a dot x = t}) =
                      s INTER {x | a' dot x = t'}) /\
             (!r p q. r IN c /\ r INTER {x | a dot x = t} = {p} /\
                      r INTER {x | a' dot x = t'} = {q} ==> h p = q)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (LABEL_TAC "sa"))) THEN
  MP_TAC(ISPECL [`{s INTER {x:real^N | a dot x = t} | s IN c}`;
                 `\p:real^N. @q:real^N. ?r. r IN c /\
                     r INTER {x | a dot x = t} = {p} /\
                     r INTER {x | a' dot x = t'} = {q}`]
    MOI_PTR_SIMPLEXWISE_AFFINE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^N->real^N`
    (CONJUNCTS_THEN2 (LABEL_TAC "aff") (LABEL_TAC "vert"))) THEN
  EXISTS_TAC `h:real^N->real^N` THEN
  SUBGOAL_THEN
   `!s. s IN c
        ==> ?l y. linear l /\
                  !x. x IN s INTER {x:real^N | a dot x = t}
                      ==> (h:real^N->real^N) x = l x + y`
  (LABEL_TAC "aff2") THENL
   [X_GEN_TAC `s:real^N->bool` THEN DISCH_TAC THEN
    USE_THEN "aff" MATCH_MP_TAC THEN REWRITE_TAC[IN_ELIM_THM] THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!r p q. r IN c /\ r INTER {x:real^N | a dot x = t} = {p} /\
            r INTER {x | a' dot x = t'} = {q} ==> (h:real^N->real^N) p = q`
  (LABEL_TAC "hv") THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
     `(h:real^N->real^N) p =
      (@q:real^N. ?r. r IN c /\ r INTER {x | a dot x = t} = {p} /\
                      r INTER {x | a' dot x = t'} = {q})`
    SUBST1_TAC THENL
     [USE_THEN "vert" MATCH_MP_TAC THEN EXISTS_TAC `{p:real^N}` THEN
      REWRITE_TAC[IN_SING; MOI_REAL_IN_VERTEX_SETS; NOT_INSERT_EMPTY;
                  AFFINE_INDEPENDENT_1; CONVEX_HULL_SING; IN_ELIM_THM] THEN
      EXISTS_TAC `r:real^N->bool` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC SELECT_UNIQUE THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
    X_GEN_TAC `q0:real^N` THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `r0:real^N->bool` STRIP_ASSUME_TAC) THEN
      MATCH_MP_TAC MOI_SLV_SC_SIGN_WD THEN
      MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `a:real^N`; `t:real`;
        `a':real^N`; `t':real`; `r0:real^N->bool`; `r:real^N->bool`;
        `p:real^N`] THEN
      ASM_REWRITE_TAC[];
      DISCH_THEN SUBST1_TAC THEN EXISTS_TAC `r:real^N->bool` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `s:real^N->bool` THEN DISCH_TAC THEN
  USE_THEN "aff2" (fun th -> MP_TAC(MATCH_MP th
    (ASSUME `(s:real^N->bool) IN c`))) THEN
  DISCH_THEN(X_CHOOSE_THEN `l:real^N->real^N` (X_CHOOSE_THEN `y:real^N`
    STRIP_ASSUME_TAC)) THEN
  MATCH_MP_TAC MOI_SLV_SLICE_IMAGE THEN
  MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `l:real^N->real^N`;
                        `y:real^N`] THEN
  ASM_REWRITE_TAC[]);;

let MOI_SLV_SLICE_INV = prove
 (`!c (a:real^N) t a' t' (h:real^N->real^N) g.
     simplicial_complex c /\
     (!x. {x} IN c ==> (a dot x < t <=> a' dot x < t') /\
                       (a dot x = t <=> a' dot x = t')) /\
     (!s. s IN c ==> ?l y. linear l /\
                           !x. x IN s INTER {x | a dot x = t} ==> h x = l x + y) /\
     (!s. s IN c ==> IMAGE h (s INTER {x | a dot x = t}) =
                     s INTER {x | a' dot x = t'}) /\
     (!r p q. r IN c /\ r INTER {x | a dot x = t} = {p} /\
              r INTER {x | a' dot x = t'} = {q} ==> h p = q) /\
     (!s. s IN c ==> ?l y. linear l /\
                           !x. x IN s INTER {x | a' dot x = t'} ==> g x = l x + y) /\
     (!r p q. r IN c /\ r INTER {x | a' dot x = t'} = {p} /\
              r INTER {x | a dot x = t} = {q} ==> g p = q)
     ==> !x. x IN UNIONS c INTER {x | a dot x = t} ==> g (h x) = x`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "sa")
   (CONJUNCTS_THEN2 (LABEL_TAC "haff") (CONJUNCTS_THEN2 (LABEL_TAC "him")
   (CONJUNCTS_THEN2 (LABEL_TAC "hv") (CONJUNCTS_THEN2 (LABEL_TAC "gaff")
   (LABEL_TAC "gv"))))))) THEN
  X_GEN_TAC `x:real^N` THEN REWRITE_TAC[IN_INTER; IN_UNIONS; IN_ELIM_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC)
    ASSUME_TAC) THEN
  USE_THEN "haff" (fun th -> MP_TAC(MATCH_MP th
    (ASSUME `(s:real^N->bool) IN c`))) THEN
  DISCH_THEN(X_CHOOSE_THEN `l:real^N->real^N` (X_CHOOSE_THEN `y:real^N`
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "hl")))) THEN
  USE_THEN "gaff" (fun th -> MP_TAC(MATCH_MP th
    (ASSUME `(s:real^N->bool) IN c`))) THEN
  DISCH_THEN(X_CHOOSE_THEN `l':real^N->real^N` (X_CHOOSE_THEN `y':real^N`
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "gl")))) THEN
  SUBGOAL_THEN `(x:real^N) IN s INTER {x | a dot x = t}` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `(h:real^N->real^N) x IN s INTER {x | a' dot x = t'}`
    ASSUME_TAC THENL
   [USE_THEN "him" (fun th -> REWRITE_TAC[GSYM(MATCH_MP th
      (ASSUME `(s:real^N->bool) IN c`))]) THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `s INTER {x:real^N | a dot x = t} SUBSET
    {z | (l':real^N->real^N) (l z + y) + y' = z}` MP_TAC THENL
   [MP_TAC(ISPEC `s INTER {x:real^N | a dot x = t}` KREIN_MILMAN_MINKOWSKI) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[MOI_SLV_SLICE_CC]; ALL_TAC] THEN
    DISCH_THEN(fun th -> GEN_REWRITE_TAC LAND_CONV [th]) THEN
    MATCH_MP_TAC HULL_MINIMAL THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `p:real^N` THEN
      DISCH_TAC THEN
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `s:real^N->bool`; `a:real^N`;
                     `t:real`; `p:real^N`] MOI_SLV_SLICE_POINT_SUBFACE) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `r:real^N->bool` STRIP_ASSUME_TAC) THEN
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `a:real^N`; `t:real`; `a':real^N`;
                     `t':real`; `r:real^N->bool`; `p:real^N`]
        MOI_SLV_SC_SIGN_SING) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `q:real^N` ASSUME_TAC) THEN
      SUBGOAL_THEN `(h:real^N->real^N) p = q /\ (g:real^N->real^N) q = p`
        STRIP_ASSUME_TAC THENL
       [CONJ_TAC THENL
         [USE_THEN "hv" MATCH_MP_TAC THEN EXISTS_TAC `r:real^N->bool` THEN
          ASM_REWRITE_TAC[];
          USE_THEN "gv" MATCH_MP_TAC THEN EXISTS_TAC `r:real^N->bool` THEN
          ASM_REWRITE_TAC[]];
        ALL_TAC] THEN
      SUBGOAL_THEN `(p:real^N) IN s INTER {x | a dot x = t}` ASSUME_TAC THENL
       [ASM_MESON_TAC[extreme_point_of]; ALL_TAC] THEN
      SUBGOAL_THEN `(q:real^N) IN s INTER {x | a' dot x = t'}` ASSUME_TAC THENL
       [FIRST_ASSUM(MP_TAC o MATCH_MP FACE_OF_IMP_SUBSET) THEN
        UNDISCH_TAC `r INTER {x:real^N | a' dot x = t'} = {q}` THEN SET_TAC[];
        ALL_TAC] THEN
      USE_THEN "hl" (fun th -> REWRITE_TAC[GSYM(MATCH_MP th
        (ASSUME `(p:real^N) IN s INTER {x | a dot x = t}`))]) THEN
      ASM_REWRITE_TAC[] THEN
      USE_THEN "gl" (fun th -> REWRITE_TAC[GSYM(MATCH_MP th
        (ASSUME `(q:real^N) IN s INTER {x | a' dot x = t'}`))]) THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[convex; IN_ELIM_THM] THEN
      MAP_EVERY X_GEN_TAC [`z1:real^N`; `z2:real^N`; `u:real`; `v:real`] THEN
      STRIP_TAC THEN
      FIRST_X_ASSUM(SUBST_ALL_TAC o MATCH_MP
        (REAL_ARITH `u + v = &1 ==> v = &1 - u`)) THEN
      SUBGOAL_THEN
       `(l':real^N->real^N) (l z1) = z1 - l' y - y' /\
        l' (l z2) = z2 - l' y - y'` STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `(l':real^N->real^N) (l z1 + y) + y' = z1` THEN
        UNDISCH_TAC `(l':real^N->real^N) (l z2 + y) + y' = z2` THEN
        ASM_SIMP_TAC[LINEAR_ADD] THEN CONV_TAC VECTOR_ARITH;
        ALL_TAC] THEN
      ASM_SIMP_TAC[LINEAR_ADD; LINEAR_CMUL] THEN VECTOR_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
  DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[] THEN
  USE_THEN "gl" (fun th -> REWRITE_TAC[MATCH_MP th
    (ASSUME `(h:real^N->real^N) x IN s INTER {x | a' dot x = t'}`)]) THEN
  USE_THEN "hl" (fun th -> REWRITE_TAC[MATCH_MP th
    (ASSUME `(x:real^N) IN s INTER {x | a dot x = t}`)]));;

let MOI_SLV_IMAGE_UNIONS_SLICE = prove
 (`!(h:real^N->real^N) c u v.
     (!s. s IN c ==> IMAGE h (s INTER u) = s INTER v)
     ==> IMAGE h (UNIONS c INTER u) = UNIONS c INTER v`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[INTER_UNIONS; IMAGE_UNIONS] THEN
  AP_TERM_TAC THEN REWRITE_TAC[SIMPLE_IMAGE; GSYM IMAGE_o; o_DEF] THEN
  MATCH_MP_TAC IMAGE_EQ THEN
  ASM_SIMP_TAC[]);;

let MOI_SLV_SLICE_PL = prove
 (`!c (a:real^N) t (h:real^N->real^N).
     simplicial_complex {s INTER {x | a dot x = t} | s IN c} /\
     (!s. s IN c ==> ?l y. linear l /\
                           !x. x IN s INTER {x | a dot x = t} ==> h x = l x + y)
     ==> h continuous_on (UNIONS c INTER {x | a dot x = t}) /\
         pl_map_on (UNIONS c INTER {x | a dot x = t}) h`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[INTER_UNIONS] THEN
  MATCH_MP_TAC MOI_REAL_PIECEWISE_AFFINE_UNIONS THEN
  CONJ_TAC THENL
   [UNDISCH_TAC `simplicial_complex {s INTER {x:real^N | a dot x = t} | s IN c}` THEN
    SIMP_TAC[simplicial_complex];
    ALL_TAC] THEN
  REWRITE_TAC[FORALL_IN_GSPEC] THEN X_GEN_TAC `s:real^N->bool` THEN
  DISCH_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC MOI_PTR_SIMPLICIAL_COMPLEX_POLYTOPE THEN
    EXISTS_TAC `{s INTER {x:real^N | a dot x = t} | s IN c}` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN_ELIM_THM] THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[];
    ASM_MESON_TAC[]]);;

let MOI_SLV_SLICE_HOMEO = prove
 (`!c (a:real^N) t a' t'.
     simplicial_complex c /\
     simplicial_complex {s INTER {x | a dot x = t} | s IN c} /\
     simplicial_complex {s INTER {x | a' dot x = t'} | s IN c} /\
     (!x. {x} IN c ==> (a dot x < t <=> a' dot x < t') /\
                       (a dot x = t <=> a' dot x = t'))
     ==> ?f g. pl_homeomorphism (UNIONS c INTER {x | a dot x = t},
                                 UNIONS c INTER {x | a' dot x = t'}) (f,g)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "sa")))) THEN
  SUBGOAL_THEN `!x:real^N. {x} IN c ==> (a' dot x < t' <=> a dot x < t) /\
                                        (a' dot x = t' <=> a dot x = t)`
    (LABEL_TAC "sa'") THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `a:real^N`; `t:real`; `a':real^N`;
                 `t':real`] MOI_SLV_SLICE_MAP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^N->real^N` (CONJUNCTS_THEN2 (LABEL_TAC "haff")
    (CONJUNCTS_THEN2 (LABEL_TAC "him") (LABEL_TAC "hv")))) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `a':real^N`; `t':real`; `a:real^N`;
                 `t:real`] MOI_SLV_SLICE_MAP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^N->real^N` (CONJUNCTS_THEN2 (LABEL_TAC "gaff")
    (CONJUNCTS_THEN2 (LABEL_TAC "gim") (LABEL_TAC "gv")))) THEN
  MAP_EVERY EXISTS_TAC [`h:real^N->real^N`; `g:real^N->real^N`] THEN
  SUBGOAL_THEN
   `IMAGE (h:real^N->real^N) (UNIONS c INTER {x | a dot x = t}) =
    UNIONS c INTER {x | a' dot x = t'} /\
    IMAGE (g:real^N->real^N) (UNIONS c INTER {x | a' dot x = t'}) =
    UNIONS c INTER {x | a dot x = t}` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC MOI_SLV_IMAGE_UNIONS_SLICE THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(!x. x IN UNIONS c INTER {x:real^N | a dot x = t}
         ==> (g:real^N->real^N) ((h:real^N->real^N) x) = x) /\
    (!y. y IN UNIONS c INTER {x:real^N | a' dot x = t'} ==> h (g y) = y)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC MOI_SLV_SLICE_INV THENL
     [MAP_EVERY EXISTS_TAC [`a':real^N`; `t':real`];
      MAP_EVERY EXISTS_TAC [`a:real^N`; `t:real`]] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `a:real^N`; `t:real`;
                 `h:real^N->real^N`] MOI_SLV_SLICE_PL) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `a':real^N`; `t':real`;
                 `g:real^N->real^N`] MOI_SLV_SLICE_PL) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[pl_homeomorphism; homeomorphism]);;

(* ------------------------------------------------------------------------- *)
(* 13. The theorem LEVEL_STABLE: for a direction a' near the generic         *)
(* direction a every vertex has the same side with respect to the level of v *)
(* for a and for a', so the two level sets through v are PL homeomorphic,    *)
(* and the homeomorphism maps level polygons bijectively onto level          *)
(* polygons.                                                                 *)
(* ------------------------------------------------------------------------- *)

let MOI_SLV_HOMEO_POLYGONS = prove
 (`!(s:real^N->bool) (t:real^N->bool) (f:real^N->real^N) g.
     2 <= dimindex(:N) /\ pl_homeomorphism (s,t) (f,g) /\
     FINITE {p | pl_sphere 1 p /\ p SUBSET s}
     ==> CARD {p | pl_sphere 1 p /\ p SUBSET s} =
         CARD {p | pl_sphere 1 p /\ p SUBSET t}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `pl_homeomorphism (t:real^N->bool,s:real^N->bool)
                  (g:real^N->real^N,f:real^N->real^N)` ASSUME_TAC THENL
   [ASM_MESON_TAC[PL_HOMEOMORPHISM_SYM]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[pl_homeomorphism; homeomorphism]) THEN
  MATCH_MP_TAC BIJECTIONS_CARD_EQ THEN
  MAP_EVERY EXISTS_TAC [`IMAGE (f:real^N->real^N)`; `IMAGE (g:real^N->real^N)`] THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN CONJ_TAC THENL
   [X_GEN_TAC `p:real^N->bool` THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MOI_SS2_SPHERE1_IMAGE THEN
      MAP_EVERY EXISTS_TAC [`s:real^N->bool`; `t:real^N->bool`;
                            `g:real^N->real^N`] THEN
      ASM_REWRITE_TAC[];
      ASM SET_TAC[];
      ASM SET_TAC[]];
    X_GEN_TAC `p:real^N->bool` THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MOI_SS2_SPHERE1_IMAGE THEN
      MAP_EVERY EXISTS_TAC [`t:real^N->bool`; `s:real^N->bool`;
                            `f:real^N->real^N`] THEN
      ASM_REWRITE_TAC[];
      ASM SET_TAC[];
      ASM SET_TAC[]]]);;

let LEVEL_STABLE = prove
 (MOI_SCH3_LEVEL_STABLE,
  MAP_EVERY X_GEN_TAC [`c:(real^3->bool)->bool`; `a:real^3`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `a:real^3`] MOI_SGN_SIGN_OPEN) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e1:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (LABEL_TAC "e1"))) THEN
  MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `a:real^3`]
    MOI_SGN_CROSSINGS_STABLE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e2:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (LABEL_TAC "e2"))) THEN
  EXISTS_TAC `min e1 e2:real` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  MAP_EVERY X_GEN_TAC [`a':real^3`; `v:real^3`] THEN STRIP_TAC THEN
  REMOVE_THEN "e1" (MP_TAC o SPEC `a':real^3`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "sg")) THEN
  REMOVE_THEN "e2" (MP_TAC o SPEC `a':real^3`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC)) THEN
  SUBGOAL_THEN
   `!x:real^3. {x} IN c
               ==> (a dot x < a dot v <=> a' dot x < a' dot v) /\
                   (a dot x = a dot v <=> a' dot x = a' dot v)`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    ASM_CASES_TAC `x:real^3 = v` THEN ASM_REWRITE_TAC[REAL_LT_REFL] THEN
    SUBGOAL_THEN `~((a:real^3) dot x = a dot v) /\ ~((a':real^3) dot x = a' dot v)`
      (fun th -> REWRITE_TAC[th]) THENL
     [ASM_MESON_TAC[MOI_SLV_GENERIC_VERTEX]; ALL_TAC] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOI_SGN_SIGN_SAME THEN
    USE_THEN "sg" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `a:real^3`; `(a:real^3) dot v`;
                 `a':real^3`; `(a':real^3) dot v`] MOI_SLV_SLICE_HOMEO) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[moi_sch3_generic];
      MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `a:real^3`; `(a:real^3) dot v`]
        MOI_SLV_LEVEL_COMPLEX) THEN ASM_SIMP_TAC[];
      MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `a':real^3`; `(a':real^3) dot v`]
        MOI_SLV_LEVEL_COMPLEX) THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^3->real^3` (X_CHOOSE_TAC `g:real^3->real^3`)) THEN
  REWRITE_TAC[MOI_SLV_LEVEL_POLYGONS_EQ] THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC MOI_SLV_HOMEO_POLYGONS THEN
  MAP_EVERY EXISTS_TAC [`f:real^3->real^3`; `g:real^3->real^3`] THEN
  ASM_REWRITE_TAC[DIMINDEX_3; ARITH] THEN
  MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `a:real^3`; `(a:real^3) dot v`]
    LEVEL_POLYGONS_FINITE) THEN
  ASM_REWRITE_TAC[MOI_SLV_LEVEL_POLYGONS_EQ]);;

(* ------------------------------------------------------------------------- *)
(* 14. Planar facts for INMOST: Jordan regions of PL circles, nesting of    *)
(* circles meeting in at most one point, an inmost circle of a finite      *)
(* family covering a set, and the plane disk bounded by a PL circle.        *)
(* ------------------------------------------------------------------------- *)

let MOI_SLV_JORDAN_PL = prove
 (`!s:real^2->bool.
     pl_sphere 1 s
     ==> compact s /\ compact(s UNION inside s) /\
         frontier(s UNION inside s) = s /\
         (:real^2) DIFF outside s = s UNION inside s /\
         open(inside s) /\ open(outside s) /\
         connected(outside s) /\ ~bounded(outside s) /\
         inside s INTER s = {} /\ outside s INTER s = {} /\
         inside s INTER outside s = {} /\
         inside s UNION outside s = (:real^2) DIFF s`,
  GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP MOI_SLV_CIRCLE_LOOP) THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^1->real^2` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`g:real^1->real^2`; `s:real^2->bool`] MOI_SFR_JORDAN_REGION) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC OPEN_OUTSIDE THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED]);;

let MOI_SLV_CIRCLE_MEETS_OPEN = prove
 (`!(q:real^N->bool) u w.
     pl_sphere 1 q /\ open u /\ ~(q INTER u = {})
     ==> ~((q DELETE w) INTER u = {})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `z:real^N` MP_TAC o
    REWRITE_RULE[GSYM MEMBER_NOT_EMPTY]) THEN
  REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN
  ASM_CASES_TAC `z:real^N = w` THENL
   [ALL_TAC;
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `z:real^N` THEN
    ASM_REWRITE_TAC[IN_INTER; IN_DELETE]] THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  MP_TAC(ISPECL [`q:real^N->bool`; `w:real^N`] MOI_SLV_CIRCLE_LIMPT) THEN
  ASM_REWRITE_TAC[LIMPT_APPROACHABLE] THEN
  UNDISCH_TAC `open(u:real^N->bool)` THEN REWRITE_TAC[open_def] THEN
  DISCH_THEN(MP_TAC o SPEC `w:real^N`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `y:real^N` THEN
  ASM_REWRITE_TAC[IN_INTER; IN_DELETE] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let MOI_SLV_NESTED = prove
 (`!J Q (w:real^2).
     pl_sphere 1 J /\ pl_sphere 1 Q /\ J INTER Q SUBSET {w} /\
     ~(Q INTER inside J = {})
     ==> Q UNION inside Q SUBSET J UNION inside J`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `J:real^2->bool` MOI_SLV_JORDAN_PL) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `(Q:real^2->bool) INTER outside J = {}` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`Q:real^2->bool`; `w:real^2`] MOI_SLV_CIRCLE_DELETE_ANY) THEN
    ASM_REWRITE_TAC[connected] THEN
    MATCH_MP_TAC(TAUT `(~p ==> q) ==> ~q ==> p`) THEN DISCH_TAC THEN
    MAP_EVERY EXISTS_TAC [`inside J:real^2->bool`; `outside J:real^2->bool`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `inside J UNION outside J = (:real^2) DIFF J` THEN
      UNDISCH_TAC `J INTER Q SUBSET {w:real^2}` THEN SET_TAC[];
      UNDISCH_TAC `inside J INTER outside J:real^2->bool = {}` THEN SET_TAC[];
      ONCE_REWRITE_TAC[INTER_COMM] THEN MATCH_MP_TAC MOI_SLV_CIRCLE_MEETS_OPEN THEN
      ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[INTER_COMM] THEN ASM_REWRITE_TAC[];
      ONCE_REWRITE_TAC[INTER_COMM] THEN MATCH_MP_TAC MOI_SLV_CIRCLE_MEETS_OPEN THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[UNION_SUBSET] THEN CONJ_TAC THENL
   [UNDISCH_TAC `(:real^2) DIFF outside J = J UNION inside J` THEN
    UNDISCH_TAC `(Q:real^2->bool) INTER outside J = {}` THEN SET_TAC[];
    ALL_TAC] THEN
  TRANS_TAC SUBSET_TRANS `(:real^2) DIFF (Q UNION outside J)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC INSIDE_SUBSET THEN EXISTS_TAC `outside J:real^2->bool` THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(Q:real^2->bool) INTER outside J = {}` THEN SET_TAC[];
    UNDISCH_TAC `(:real^2) DIFF outside J = J UNION inside J` THEN SET_TAC[]]);;

let MOI_SLV_PLANAR_INMOST = prove
 (`!P (L:real^2->bool) w.
     FINITE P /\ ~(P = {}) /\
     (!p. p IN P ==> pl_sphere 1 p /\ p SUBSET L) /\
     (!x. x IN L ==> ?p. p IN P /\ x IN p) /\
     (!p q. p IN P /\ q IN P /\ ~(p = q) ==> p INTER q SUBSET {w})
     ==> ?j. j IN P /\ inside j INTER L = {}`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "pp") (CONJUNCTS_THEN2 (LABEL_TAC "cov")
    (LABEL_TAC "dis"))))) THEN
  MP_TAC(ISPEC `\q p:real^2->bool. q IN P /\ p IN P /\
                  (q UNION inside q) PSUBSET (p UNION inside p)` WF_FINITE) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [REWRITE_TAC[PSUBSET_IRREFL] THEN CONJ_TAC THENL
     [MESON_TAC[PSUBSET_TRANS];
      X_GEN_TAC `p:real^2->bool` THEN MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `P:(real^2->bool)->bool` THEN ASM_REWRITE_TAC[] THEN SET_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[WF] THEN
  DISCH_THEN(MP_TAC o SPEC `\p:real^2->bool. p IN P`) THEN REWRITE_TAC[] THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `j:real^2->bool` (CONJUNCTS_THEN2 ASSUME_TAC
    (LABEL_TAC "min"))) THEN
  EXISTS_TAC `j:real^2->bool` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
  X_GEN_TAC `z:real^2` THEN STRIP_TAC THEN
  USE_THEN "cov" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(z:real^2) IN L`))) THEN
  DISCH_THEN(X_CHOOSE_THEN `q:real^2->bool` STRIP_ASSUME_TAC) THEN
  USE_THEN "pp" (fun th -> MP_TAC(MATCH_MP th
    (ASSUME `(j:real^2->bool) IN P`))) THEN STRIP_TAC THEN
  USE_THEN "pp" (fun th -> MP_TAC(MATCH_MP th
    (ASSUME `(q:real^2->bool) IN P`))) THEN STRIP_TAC THEN
  MP_TAC(ISPEC `j:real^2->bool` MOI_SLV_JORDAN_PL) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  MP_TAC(ISPEC `q:real^2->bool` MOI_SLV_JORDAN_PL) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `~(q:real^2->bool = j)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `inside j INTER j:real^2->bool = {}` THEN
    UNDISCH_TAC `(z:real^2) IN inside j` THEN UNDISCH_TAC `(z:real^2) IN j` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `q UNION inside q SUBSET j UNION inside (j:real^2->bool)`
    ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_SLV_NESTED THEN EXISTS_TAC `w:real^2` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [USE_THEN "dis" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `z:real^2` THEN
      ASM_REWRITE_TAC[IN_INTER]];
    ALL_TAC] THEN
  USE_THEN "min" (MP_TAC o SPEC `q:real^2->bool`) THEN
  REWRITE_TAC[ASSUME `(q:real^2->bool) IN P`; ASSUME `(j:real^2->bool) IN P`;
    PSUBSET; ASSUME `q UNION inside q SUBSET j UNION inside (j:real^2->bool)`] THEN
  DISCH_THEN(MP_TAC o AP_TERM `frontier:(real^2->bool)->(real^2->bool)`) THEN
  ASM_REWRITE_TAC[]);;

let MOI_SLV_BIG_TRIANGLE = prove
 (`!s:real^2->bool. bounded s ==> ?k. &2 simplex k /\ s SUBSET interior k`,
  GEN_TAC THEN REWRITE_TAC[BOUNDED_POS] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `~collinear {vector[--(&2) * r; --(&2) * r]:real^2,
                vector[&6 * r; --(&2) * r], vector[--(&2) * r; &6 * r]}`
  ASSUME_TAC THENL
   [REWRITE_TAC[COLLINEAR_3_2D; VECTOR_2] THEN
    MP_TAC(SPECL [`r:real`; `r:real`] REAL_LT_MUL) THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `convex hull {vector[--(&2) * r; --(&2) * r]:real^2,
                           vector[&6 * r; --(&2) * r],
                           vector[--(&2) * r; &6 * r]}` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[MOI_PL2_SIMPLEX_2] THEN
    MAP_EVERY EXISTS_TAC [`vector[--(&2) * r; --(&2) * r]:real^2`;
      `vector[&6 * r; --(&2) * r]:real^2`; `vector[--(&2) * r; &6 * r]:real^2`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[INTERIOR_CONVEX_HULL_3_MINIMAL] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `y:real^2` THEN DISCH_TAC THEN
  SUBGOAL_THEN `abs((y:real^2)$1) <= r /\ abs(y$2) <= r` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[COMPONENT_LE_NORM; REAL_LE_TRANS]; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`(&4 * r - (y:real^2)$1 - y$2) / (&8 * r)`;
    `((y:real^2)$1 + &2 * r) / (&8 * r)`;
    `((y:real^2)$2 + &2 * r) / (&8 * r)`] THEN
  SUBGOAL_THEN `&0 < &8 * r` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
    UNDISCH_TAC `&0 < &8 * r` THEN CONV_TAC REAL_FIELD;
    REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_ADD_COMPONENT;
                VECTOR_MUL_COMPONENT; VECTOR_2] THEN
    UNDISCH_TAC `&0 < &8 * r` THEN CONV_TAC REAL_FIELD]);;

let MOI_SLV_PLANE_DISK = prove
 (`!J:real^2->bool. pl_sphere 1 J ==> moi_fsa_disk (J UNION inside J) J`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `J:real^2->bool` MOI_SLV_BIG_TRIANGLE) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC COMPACT_IMP_BOUNDED THEN ASM_MESON_TAC[MOI_SLV_CIRCLE_CLOSED];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^2->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`k:real^2->bool`; `J:real^2->bool`] MOI_SS2_PLANAR) THEN
  ASM_SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* 15. An affine chart of a plane in real^3 by real^2, a PL homeomorphism.  *)
(* ------------------------------------------------------------------------- *)

let MOI_SLV_PLANE_BASIS = prove
 (`!a:real^3.
     ~(a = vec 0)
     ==> ?e1 e2:real^3. e1 dot e1 = &1 /\ e2 dot e2 = &1 /\ e1 dot e2 = &0 /\
                 a dot e1 = &0 /\ a dot e2 = &0 /\
                 !x. a dot x = &0 ==> x = (x dot e1) % e1 + (x dot e2) % e2`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `{x:real^3 | a dot x = &0}` ORTHONORMAL_BASIS_SUBSPACE) THEN
  REWRITE_TAC[SUBSPACE_HYPERPLANE] THEN
  ASM_SIMP_TAC[DIM_HYPERPLANE; DIMINDEX_3] THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN(X_CHOOSE_THEN `b:real^3->bool` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)))))) THEN
  REWRITE_TAC[HAS_SIZE_CONV `(b:real^3->bool) HAS_SIZE 2`] THEN
  DISCH_THEN(X_CHOOSE_THEN `e1:real^3` (X_CHOOSE_THEN `e2:real^3`
    (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`e1:real^3`; `e2:real^3`] THEN
  SUBGOAL_THEN `(e1:real^3) dot e1 = &1 /\ (e2:real^3) dot e2 = &1`
    STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM NORM_EQ_1] THEN CONJ_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_INSERT];
    ALL_TAC] THEN
  SUBGOAL_THEN `(e1:real^3) dot e2 = &0` ASSUME_TAC THENL
   [UNDISCH_TAC `pairwise orthogonal {e1:real^3,e2}` THEN
    REWRITE_TAC[PAIRWISE_INSERT; IN_SING] THEN
    DISCH_THEN(MP_TAC o SPEC `e2:real^3` o CONJUNCT1) THEN
    ASM_REWRITE_TAC[orthogonal] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(a:real^3) dot e1 = &0 /\ a dot (e2:real^3) = &0`
    STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `{e1:real^3,e2} SUBSET {x | a dot x = &0}` THEN
    REWRITE_TAC[INSERT_SUBSET; IN_ELIM_THM] THEN SIMP_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(x:real^3) IN span {e1,e2}` MP_TAC THENL
   [ASM_REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  REWRITE_TAC[SPAN_2; IN_ELIM_THM; IN_UNIV] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real` (X_CHOOSE_THEN `w:real` SUBST1_TAC)) THEN
  SUBGOAL_THEN `(e2:real^3) dot e1 = &0` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[DOT_SYM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[DOT_LADD; DOT_LMUL] THEN
  REWRITE_TAC[REAL_MUL_RID; REAL_MUL_RZERO; REAL_ADD_RID; REAL_ADD_LID]);;

let MOI_SLV_PLANE_CHART = prove
 (`!(a:real^3) t.
     ~(a = vec 0)
     ==> ?psi:real^2->real^3 phi.
            pl_homeomorphism ((:real^2),{x | a dot x = t}) (psi,phi)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_SLV_PLANE_BASIS) THEN
  DISCH_THEN(X_CHOOSE_THEN `e1:real^3` (X_CHOOSE_THEN `e2:real^3`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "exp")))))))) THEN
  SUBGOAL_THEN `(e2:real^3) dot e1 = &0` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[DOT_SYM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `?w0:real^3. a dot w0 = t` (X_CHOOSE_TAC `w0:real^3`) THENL
   [EXISTS_TAC `(t / (a dot a)) % (a:real^3)` THEN REWRITE_TAC[DOT_RMUL] THEN
    ASM_SIMP_TAC[REAL_DIV_RMUL; DOT_EQ_0];
    ALL_TAC] THEN
  SUBGOAL_THEN `linear (\y:real^2. y$1 % e1 + y$2 % (e2:real^3)) /\
                linear (\x:real^3. vector[x dot e1; x dot e2]:real^2)`
    STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[linear; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
      CONJ_TAC THEN REPEAT GEN_TAC THEN VECTOR_ARITH_TAC;
      REWRITE_TAC[linear; CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2;
                  VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; DOT_LADD;
                  DOT_LMUL]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y:real^2. vector[((y$1 % e1 + y$2 % e2) + w0) dot e1;
                      ((y$1 % e1 + y$2 % e2) + w0) dot e2] -
               vector[w0 dot e1; w0 dot (e2:real^3)] = y`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2; VECTOR_SUB_COMPONENT] THEN
    ASM_REWRITE_TAC[DOT_LADD; DOT_LMUL] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x:real^3. a dot x = t
               ==> ((vector[x dot e1; x dot e2] - vector[w0 dot e1; w0 dot e2]:real^2)$1
                    % e1 +
                    (vector[x dot e1; x dot e2] - vector[w0 dot e1; w0 dot e2]:real^2)$2
                    % e2) + w0 = x`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    REWRITE_TAC[VECTOR_SUB_COMPONENT; VECTOR_2] THEN
    USE_THEN "exp" (MP_TAC o SPEC `x - w0:real^3`) THEN
    REWRITE_TAC[DOT_RSUB; DOT_LSUB; ASSUME `(a:real^3) dot x = t`;
                ASSUME `(a:real^3) dot w0 = t`; REAL_SUB_REFL] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `\y:real^2. (y$1 % e1 + y$2 % e2) + w0:real^3` THEN
  EXISTS_TAC `\x:real^3. vector[x dot e1; x dot e2] -
                         vector[w0 dot e1; w0 dot e2]:real^2` THEN
  MATCH_MP_TAC HOMEOMORPHISM_IMP_PL_HOMEOMORPHISM THEN CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC PL_MAP_ON_AFFINE THEN
    ASM_SIMP_TAC[LOCALLY_POLYHEDRAL_OPEN; OPEN_UNIV]] THEN
  REWRITE_TAC[homeomorphism; IN_UNIV] THEN REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    REWRITE_TAC[EXTENSION; IN_IMAGE; IN_UNIV; IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^3` THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `y:real^2` SUBST1_TAC) THEN
      ASM_REWRITE_TAC[DOT_RADD; DOT_RMUL] THEN REAL_ARITH_TAC;
      DISCH_TAC THEN
      EXISTS_TAC `vector[(x:real^3) dot e1; x dot e2] -
                  vector[(w0:real^3) dot e1; w0 dot e2]:real^2` THEN
      CONV_TAC SYM_CONV THEN ASM_SIMP_TAC[]];
    MATCH_MP_TAC CONTINUOUS_ON_ADD THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
    MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[IN_ELIM_THM] THEN ASM_SIMP_TAC[];
    REWRITE_TAC[EXTENSION; IN_IMAGE; IN_UNIV; IN_ELIM_THM] THEN
    X_GEN_TAC `y:real^2` THEN
    EXISTS_TAC `((y:real^2)$1 % e1 + y$2 % e2) + w0:real^3` THEN
    ASM_REWRITE_TAC[DOT_RADD; DOT_RMUL] THEN REAL_ARITH_TAC;
    MATCH_MP_TAC CONTINUOUS_ON_SUB THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
    MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* 16. The theorem INMOST: every point of the level set lies on a level      *)
(* polygon (all graph vertices other than v have degree 2 and v has an       *)
(* edge), two level polygons meet at most in v, so in the chart of the level *)
(* plane an inmost polygon exists, and its plane disk meets the sphere in it *)
(* only.                                                                     *)
(* ------------------------------------------------------------------------- *)

let MOI_SLV_G2_POINT_COVER = prove
 (`!K (v:real^N) x.
     2 <= dimindex(:N) /\ moi_slv_graph2 K v /\ {v} IN K /\
     ~({s | s IN K /\ aff_dim s = &1 /\ v IN s} = {}) /\ x IN UNIONS K
     ==> ?q. pl_sphere 1 q /\ q SUBSET UNIONS K /\ x IN q`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `?s:real^N->bool. s IN K /\ aff_dim s = &1 /\ x IN s` MP_TAC THENL
   [UNDISCH_TAC `(x:real^N) IN UNIONS K` THEN REWRITE_TAC[IN_UNIONS] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC) THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_slv_graph2]) THEN
    SUBGOAL_THEN `aff_dim(t:real^N->bool) <= &1` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `aff_dim(t:real^N->bool) = -- &1 \/ aff_dim t = &0 \/ aff_dim t = &1`
    MP_TAC THENL
     [MP_TAC(ISPEC `t:real^N->bool` AFF_DIM_GE) THEN
      UNDISCH_TAC `aff_dim(t:real^N->bool) <= &1` THEN
      SPEC_TAC(`aff_dim(t:real^N->bool)`,`d:int`) THEN INT_ARITH_TAC;
      ALL_TAC] THEN
    STRIP_TAC THENL
     [UNDISCH_TAC `aff_dim(t:real^N->bool) = -- &1` THEN
      REWRITE_TAC[AFF_DIM_EQ_MINUS1] THEN DISCH_THEN SUBST_ALL_TAC THEN
      ASM_MESON_TAC[NOT_IN_EMPTY];
      UNDISCH_TAC `aff_dim(t:real^N->bool) = &0` THEN
      REWRITE_TAC[AFF_DIM_EQ_0] THEN
      DISCH_THEN(X_CHOOSE_THEN `x0:real^N` SUBST_ALL_TAC) THEN
      UNDISCH_TAC `(x:real^N) IN {x0}` THEN REWRITE_TAC[IN_SING] THEN
      DISCH_THEN SUBST_ALL_TAC THEN
      ASM_CASES_TAC `x0:real^N = v` THENL
       [FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM SET_TAC[];
        ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `x0:real^N` o check (is_forall o concl)) THEN
      ASM_REWRITE_TAC[HAS_SIZE_CONV
        `{s | s IN K /\ aff_dim s = &1 /\ (x0:real^N) IN s} HAS_SIZE 2`] THEN
      DISCH_THEN(X_CHOOSE_THEN `e1:real^N->bool` (X_CHOOSE_THEN `e2:real^N->bool`
        (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC))) THEN
      REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY] THEN
      DISCH_THEN(MP_TAC o SPEC `e1:real^N->bool`) THEN
      REWRITE_TAC[] THEN MESON_TAC[];
      EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `v:real^N`; `s:real^N->bool`]
    MOI_SLV_G2_COVER) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:real^N->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `q:real^N->bool` THEN ASM SET_TAC[]);;

let MOI_SLV_INMOST_GEN = prove
 (`!P (L:real^3->bool) H w (psi:real^2->real^3) phi.
     pl_homeomorphism ((:real^2),H) (psi,phi) /\ L SUBSET H /\
     FINITE P /\ ~(P = {}) /\
     (!p. p IN P ==> pl_sphere 1 p /\ p SUBSET L) /\
     (!x. x IN L ==> ?p. p IN P /\ x IN p) /\
     (!p q. p IN P /\ q IN P /\ ~(p = q) ==> p INTER q SUBSET {w})
     ==> ?j d. j IN P /\ pl_cell_with_boundary 2 d j /\ d SUBSET H /\
               d INTER L = j`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "pp") (CONJUNCTS_THEN2 (LABEL_TAC "cov")
    (LABEL_TAC "dis"))))))) THEN
  MP_TAC(ASSUME `pl_homeomorphism ((:real^2),H)
                   (psi:real^2->real^3,phi:real^3->real^2)`) THEN
  REWRITE_TAC[pl_homeomorphism; homeomorphism; IN_UNIV] THEN STRIP_TAC THEN
  SUBGOAL_THEN `pl_homeomorphism (H,(:real^2))
                  (phi:real^3->real^2,psi:real^2->real^3)` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[PL_HOMEOMORPHISM_SYM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (IMAGE (phi:real^3->real^2)) P`;
                 `IMAGE (phi:real^3->real^2) L`; `(phi:real^3->real^2) w`]
    MOI_SLV_PLANAR_INMOST) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[FINITE_IMAGE; IMAGE_EQ_EMPTY] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `p:real^3->bool` THEN
      DISCH_TAC THEN
      USE_THEN "pp" (fun th -> MP_TAC(MATCH_MP th
        (ASSUME `(p:real^3->bool) IN P`))) THEN
      STRIP_TAC THEN CONJ_TAC THENL
       [MATCH_MP_TAC MOI_SS2_SPHERE1_IMAGE THEN
        MAP_EVERY EXISTS_TAC [`H:real^3->bool`; `(:real^2)`;
                              `psi:real^2->real^3`] THEN
        ASM_REWRITE_TAC[DIMINDEX_2; LE_REFL] THEN ASM SET_TAC[];
        MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[]];
      REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
      USE_THEN "cov" (fun th -> MP_TAC(MATCH_MP th
        (ASSUME `(x:real^3) IN L`))) THEN
      DISCH_THEN(X_CHOOSE_THEN `p:real^3->bool` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `IMAGE (phi:real^3->real^2) p` THEN
      CONJ_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
      X_GEN_TAC `p:real^3->bool` THEN DISCH_TAC THEN
      X_GEN_TAC `q:real^3->bool` THEN DISCH_TAC THEN DISCH_TAC THEN
      USE_THEN "pp" (fun th -> MP_TAC(MATCH_MP th
        (ASSUME `(p:real^3->bool) IN P`))) THEN STRIP_TAC THEN
      USE_THEN "pp" (fun th -> MP_TAC(MATCH_MP th
        (ASSUME `(q:real^3->bool) IN P`))) THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`phi:real^3->real^2`; `psi:real^2->real^3`; `H:real^3->bool`;
                     `p:real^3->bool`; `q:real^3->bool`] MOI_SS2_INJ_IMAGE) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
      DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN
      SUBGOAL_THEN `(p:real^3->bool) INTER q SUBSET {w}` MP_TAC THENL
       [USE_THEN "dis" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
        DISCH_THEN SUBST_ALL_TAC THEN ASM_MESON_TAC[];
        SET_TAC[]]];
    ALL_TAC] THEN
  REWRITE_TAC[EXISTS_IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `j:real^3->bool` STRIP_ASSUME_TAC) THEN
  USE_THEN "pp" (fun th -> MP_TAC(MATCH_MP th
    (ASSUME `(j:real^3->bool) IN P`))) THEN STRIP_TAC THEN
  SUBGOAL_THEN `pl_sphere 1 (IMAGE (phi:real^3->real^2) j)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_SS2_SPHERE1_IMAGE THEN
    MAP_EVERY EXISTS_TAC [`H:real^3->bool`; `(:real^2)`; `psi:real^2->real^3`] THEN
    ASM_REWRITE_TAC[DIMINDEX_2; LE_REFL] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (psi:real^2->real^3) (IMAGE (phi:real^3->real^2) j) = j`
    ASSUME_TAC THENL
   [UNDISCH_TAC `!y:real^3. y IN H ==> (psi:real^2->real^3) (phi y) = y` THEN
    UNDISCH_TAC `(j:real^3->bool) SUBSET L` THEN
    UNDISCH_TAC `(L:real^3->bool) SUBSET H` THEN SET_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `j:real^3->bool` THEN
  EXISTS_TAC `IMAGE (psi:real^2->real^3)
                (IMAGE (phi:real^3->real^2) j UNION inside(IMAGE phi j))` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN
     `moi_fsa_disk (IMAGE (psi:real^2->real^3)
                     (IMAGE (phi:real^3->real^2) j UNION inside(IMAGE phi j)))
                   (IMAGE psi (IMAGE phi j))`
    MP_TAC THENL
     [MATCH_MP_TAC MOI_SS2_FSA_IMAGE THEN
      MAP_EVERY EXISTS_TAC [`(:real^2)`; `H:real^3->bool`;
                            `phi:real^3->real^2`] THEN
      ASM_REWRITE_TAC[SUBSET_UNIV] THEN MATCH_MP_TAC MOI_SLV_PLANE_DISK THEN
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[MOI_SS2_CELL_EQ_FSA]];
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `IMAGE (psi:real^2->real^3) (:real^2)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[SUBSET_UNIV];
      ASM_REWRITE_TAC[SUBSET_REFL]];
    MAP_EVERY UNDISCH_TAC
     [`!x:real^2. (phi:real^3->real^2) ((psi:real^2->real^3) x) = x`;
      `!y:real^3. y IN H ==> (psi:real^2->real^3) ((phi:real^3->real^2) y) = y`;
      `(j:real^3->bool) SUBSET L`; `(L:real^3->bool) SUBSET H`;
      `inside (IMAGE (phi:real^3->real^2) j) INTER IMAGE phi L = {}`] THEN
    SET_TAC[]]);;

let INMOST = prove
 (MOI_SCH3_INMOST,
  MAP_EVERY X_GEN_TAC [`c:(real^3->bool)->bool`; `a:real^3`; `v:real^3`] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `a:real^3`; `a dot (v:real^3)`]
    MOI_SLV_LEVEL_COMPLEX) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `a:real^3`; `v:real^3`]
    MOI_SLV_LEVEL_GRAPH2) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `~({s | s IN {s INTER {x:real^3 | a dot x = a dot v} | s IN c} /\
           aff_dim s = &1 /\ v IN s} = {})`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `a:real^3`; `v:real^3`]
      MOI_SLV_LEVEL_STAR) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o SYM) THEN DISCH_TAC THEN
    UNDISCH_TAC `4 <= moi_sch3_crossings c a v` THEN
    ASM_REWRITE_TAC[CARD_CLAUSES] THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`a:real^3`; `a dot (v:real^3)`] MOI_SLV_PLANE_CHART) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[moi_sch3_generic]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `psi:real^2->real^3` (X_CHOOSE_TAC
    `phi:real^3->real^2`)) THEN
  MP_TAC(ISPECL [`moi_sch3_level_polygons (UNIONS c) a (a dot v)`;
                 `UNIONS c INTER {x:real^3 | a dot x = a dot v}`;
                 `{x:real^3 | a dot x = a dot v}`; `v:real^3`;
                 `psi:real^2->real^3`; `phi:real^3->real^2`]
    MOI_SLV_INMOST_GEN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[INTER_SUBSET] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC LEVEL_POLYGONS_FINITE THEN ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`{s INTER {x:real^3 | a dot x = a dot v} | s IN c}`;
                     `v:real^3`; `v:real^3`] MOI_SLV_G2_POINT_COVER) THEN
      ASM_REWRITE_TAC[DIMINDEX_3; ARITH] THEN ANTS_TAC THENL
       [REWRITE_TAC[IN_INTER; IN_UNIONS; IN_ELIM_THM] THEN
        EXISTS_TAC `{v:real^3}` THEN ASM_REWRITE_TAC[IN_SING];
        ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `q:real^3->bool` STRIP_ASSUME_TAC) THEN
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `q:real^3->bool` THEN
      REWRITE_TAC[MOI_SLV_LEVEL_POLYGONS_EQ; IN_ELIM_THM] THEN ASM_MESON_TAC[];
      REWRITE_TAC[MOI_SLV_LEVEL_POLYGONS_EQ; IN_ELIM_THM] THEN SIMP_TAC[];
      X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`{s INTER {x:real^3 | a dot x = a dot v} | s IN c}`;
                     `v:real^3`; `x:real^3`] MOI_SLV_G2_POINT_COVER) THEN
      ASM_REWRITE_TAC[DIMINDEX_3; ARITH] THEN
      DISCH_THEN(X_CHOOSE_THEN `q:real^3->bool` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `q:real^3->bool` THEN
      REWRITE_TAC[MOI_SLV_LEVEL_POLYGONS_EQ; IN_ELIM_THM] THEN ASM_MESON_TAC[];
      REWRITE_TAC[MOI_SLV_LEVEL_POLYGONS_EQ; IN_ELIM_THM] THEN
      MAP_EVERY X_GEN_TAC [`p:real^3->bool`; `q:real^3->bool`] THEN STRIP_TAC THEN
      REWRITE_TAC[SUBSET; IN_INTER; IN_SING] THEN X_GEN_TAC `x:real^3` THEN
      STRIP_TAC THEN ASM_CASES_TAC `x:real^3 = v` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `~(p:real^3->bool = q)` THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC MOI_SLV_G2_UNIQUE THEN
      MAP_EVERY EXISTS_TAC [`{s INTER {x:real^3 | a dot x = a dot v} | s IN c}`;
                            `v:real^3`; `x:real^3`] THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `j:real^3->bool` THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real^3->bool` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `d INTER (UNIONS c INTER {x:real^3 | a dot x = a dot v}) = j` THEN
  UNDISCH_TAC `d SUBSET {x:real^3 | a dot x = a dot v}` THEN SET_TAC[]);;

