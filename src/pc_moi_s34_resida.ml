(* ========================================================================= *)
(* pc_moi_s34_resida: Moise GTM 47, Sec 34, printed pp.244-245, the tetra    *)
(* ball C''(r) of one 3-simplex r.                                           *)
(* Main theorem: RESID_A = MOI_S4X_RESID_A (pc_moi_s34_residstmt.ml).        *)
(* Route, in the order of the file:                                          *)
(*  - generic arcs, circles, sides (Jordan-Brouwer) and the THETA split:     *)
(*    three disjoint disks on a PL 2-sphere joined cyclically by three       *)
(*    disjoint arcs cut the sphere minus the disks into two hexagons;        *)
(*  - the tetra configuration: four PL 3-balls meeting pairwise in           *)
(*    splitting disks and four face disks; the hexagons at each vertex       *)
(*    are chosen consistently by one Jordan-Brouwer argument on the          *)
(*    sphere glued from two hexagons, the face disks and a disk of the       *)
(*    frontier of the other two balls (no orientation argument);             *)
(*  - the two-two split: the disk Z, the sphere Sigma, the side lemmas;      *)
(*  - consistency of the hexagon choices;                                    *)
(*  - the two spheres of a consistent choice; the one with the balls         *)
(*    outside bounds the tetra ball (PL Schoenflies, an antecedent);         *)
(*  - the configuration at a 3-simplex r of kk (frame, fdisk);               *)
(*  - the clauses of moi_s4x_local, and RESID_A.                             *)
(* ========================================================================= *)

needs "src/pc_moi_s34_residstmt.ml";;
needs "src/pc_moi_sch3_stmt.ml";;
needs "src/pc_moi_sch3_s2.ml";;
needs "src/pc_moi_sch3_lev.ml";;
needs "src/pc_moi_sch3_free.ml";;
needs "src/pc_moi_s34_outer.ml";;
needs "src/pc_moi_s34_frame.ml";;
needs "src/pc_moi_s34_tinf.ml";;
needs "src/pc_moi_s34_l910.ml";;
needs "src/pc_moi_s34_scellb.ml";;
needs "src/pc_moi_pl1m.ml";;
needs "src/pc_moi_pl2.ml";;
needs "src/pc_moi_sch3_cvx.ml";;
needs "src/pc_moi_s34_rchart.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Generic arcs, circles, disks, sides and the THETA split.                  *)
(* All in real^3 or real^N; no Sec 34 vocabulary.                          *)
(* ------------------------------------------------------------------------- *)

(* 1-cells as oriented PL arcs. *)

let MOI_S4X_CELL1_ARC = prove
 (`!a p q:real^N.
     pl_cell_with_boundary 1 a {p,q}
     ==> ~(p = q) /\
         ?h. arc h /\ pl_map_on (interval[vec 0,vec 1]) h /\ path_image h = a /\
             pathstart h = p /\ pathfinish h = q`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^1->real^N` STRIP_ASSUME_TAC o
    MATCH_MP MOI_S4L_CELL1_PL_ARC) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP ARC_DISTINCT_ENDS) THEN
  SUBGOAL_THEN `(pathstart h = (p:real^N) /\ pathfinish h = q) \/
                (pathstart h = q /\ pathfinish (h:real^1->real^N) = p)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `{p,q} = {pathstart h,pathfinish (h:real^1->real^N)}` THEN
    UNDISCH_TAC `~(pathfinish h = pathstart (h:real^1->real^N))` THEN
    REWRITE_TAC[EXTENSION; IN_INSERT; NOT_IN_EMPTY] THEN MESON_TAC[];
    CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    EXISTS_TAC `h:real^1->real^N` THEN ASM_REWRITE_TAC[];
    CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    EXISTS_TAC `reversepath(h:real^1->real^N)` THEN
    ASM_SIMP_TAC[ARC_REVERSEPATH; MOI_PL2_PL_REVERSEPATH; PATH_IMAGE_REVERSEPATH;
                 PATHSTART_REVERSEPATH; PATHFINISH_REVERSEPATH]]);;

(* Two arcs meeting exactly in a common end form an arc. *)

let MOI_S4X_ARC_UNION = prove
 (`!a b p q r:real^N.
     pl_cell_with_boundary 1 a {p,q} /\ pl_cell_with_boundary 1 b {q,r} /\
     a INTER b = {q}
     ==> pl_cell_with_boundary 1 (a UNION b) {p,r}`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP MOI_S4X_CELL1_ARC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `hb:real^1->real^N` STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP MOI_S4X_CELL1_ARC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `ha:real^1->real^N` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `arc((ha:real^1->real^N) ++ hb) /\
                pl_map_on (interval[vec 0,vec 1]) (ha ++ hb)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC ARC_JOIN THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
      MATCH_MP_TAC MOI_PL2_PL_JOINPATHS THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `path_image((ha:real^1->real^N) ++ hb) = a UNION b` ASSUME_TAC THENL
   [ASM_SIMP_TAC[PATH_IMAGE_JOIN]; ALL_TAC] THEN
  MP_TAC(ISPEC `(ha:real^1->real^N) ++ hb` MOI_S4O_ARC_CELL) THEN
  ASM_REWRITE_TAC[PATHSTART_JOIN; PATHFINISH_JOIN]);;

(* Two arcs with the same ends and no other common point form a circle. *)

let MOI_S4X_ARCS_CIRCLE = prove
 (`!a b p q:real^N.
     2 <= dimindex(:N) /\
     pl_cell_with_boundary 1 a {p,q} /\ pl_cell_with_boundary 1 b {p,q} /\
     a INTER b = {p,q}
     ==> pl_sphere 1 (a UNION b)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP MOI_S4X_CELL1_ARC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `hb:real^1->real^N` STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP MOI_S4X_CELL1_ARC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `ha:real^1->real^N` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`ha:real^1->real^N`; `hb:real^1->real^N`] MOI_SLV_ARCS_SPHERE) THEN
  ASM_REWRITE_TAC[]);;

(* A circle with two of its points is the union of two arcs between them. *)

let MOI_S4X_CIRCLE_SPLIT = prove
 (`!k p q:real^N.
     pl_sphere 1 k /\ p IN k /\ q IN k /\ ~(p = q)
     ==> ?a b. pl_cell_with_boundary 1 a {p,q} /\ pl_cell_with_boundary 1 b {p,q} /\
               a UNION b = k /\ a INTER b = {p,q}`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `g:real^1->real^N` STRIP_ASSUME_TAC o
    MATCH_MP MOI_S4O_CIRCLE_LOOP) THEN
  MP_TAC(ISPECL [`g:real^1->real^N`; `p:real^N`; `q:real^N`] MOI_SFR_LOOP_SPLIT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `a1:real^1->real^N` (X_CHOOSE_THEN `a2:real^1->real^N`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`path_image(a1:real^1->real^N)`; `path_image(a2:real^1->real^N)`] THEN
  MP_TAC(ISPEC `a1:real^1->real^N` MOI_S4O_ARC_CELL) THEN
  MP_TAC(ISPEC `a2:real^1->real^N` MOI_S4O_ARC_CELL) THEN
  ASM_REWRITE_TAC[] THEN SIMP_TAC[]);;

(* Two disks meeting exactly in an arc of both boundaries form a disk. *)

let MOI_S4X_DISK_GLUE = prove
 (`!d1 j1 d2 j2 c p q:real^N.
     2 <= dimindex(:N) /\
     pl_cell_with_boundary 2 d1 j1 /\ pl_cell_with_boundary 2 d2 j2 /\
     pl_cell_with_boundary 1 c {p,q} /\ d1 INTER d2 = c /\ c SUBSET j1 /\ c SUBSET j2
     ==> pl_cell_with_boundary 2 (d1 UNION d2) ((j1 UNION j2) DIFF (c DIFF {p,q}))`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP MOI_S4X_CELL1_ARC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `al:real^1->real^N` STRIP_ASSUME_TAC)) THEN
  MATCH_MP_TAC MOI_SS2_CELL_OF_FSA THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`d1:real^N->bool`; `j1:real^N->bool`; `d2:real^N->bool`;
                 `j2:real^N->bool`; `al:real^1->real^N`] MOI_FSA_GLUE) THEN
  ASM_SIMP_TAC[MOI_SS2_FSA_OF_CELL]);;

(* Two closed sides u, v with common part c: two connected sets covering a  *)
(* neighbourhood of a point of c off c lie on opposite sides.               *)

let MOI_S4X_SIDES = prove
 (`!u v c (x:real^N) w g1 g2.
     closed u /\ closed v /\ u INTER v = c /\
     x IN closure(u DIFF c) /\ x IN closure(v DIFF c) /\
     open w /\ x IN w /\ w INTER ((u UNION v) DIFF c) SUBSET g1 UNION g2 /\
     connected g1 /\ connected g2 /\
     g1 SUBSET (u UNION v) DIFF c /\ g2 SUBSET (u UNION v) DIFF c
     ==> (g1 SUBSET u /\ g2 SUBSET v) \/ (g1 SUBSET v /\ g2 SUBSET u)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!g:real^N->bool. connected g /\ g SUBSET (u UNION v) DIFF c
                                 ==> g SUBSET u \/ g SUBSET v`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_SFR_CONNECTED_SIDE THEN
    EXISTS_TAC `c:real^N->bool` THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?y:real^N. y IN w /\ y IN u DIFF c` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(x:real^N) IN closure(u DIFF c)` THEN
    REWRITE_TAC[CLOSURE_APPROACHABLE] THEN
    UNDISCH_TAC `open(w:real^N->bool)` THEN REWRITE_TAC[open_def] THEN
    DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
    DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `y:real^N` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?z:real^N. z IN w /\ z IN v DIFF c` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(x:real^N) IN closure(v DIFF c)` THEN
    REWRITE_TAC[CLOSURE_APPROACHABLE] THEN
    UNDISCH_TAC `open(w:real^N->bool)` THEN REWRITE_TAC[open_def] THEN
    DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
    DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `z:real^N` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `z:real^N` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^N) IN g1 UNION g2 /\ (z:real^N) IN g1 UNION g2`
  STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `g1:real^N->bool`) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `g2:real^N->bool`) THEN
  ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

(* Jordan-Brouwer for PL 2-spheres in real^3. *)

let MOI_S4X_JB = prove
 (`!s:real^3->bool.
     pl_sphere 2 s
     ==> compact s /\ closed s /\
         ~(inside s = {}) /\ open(inside s) /\ connected(inside s) /\
         ~(outside s = {}) /\ open(outside s) /\ connected(outside s) /\
         bounded(inside s) /\ ~bounded(outside s) /\
         inside s INTER outside s = {} /\
         inside s UNION outside s = (:real^3) DIFF s /\
         frontier(inside s) = s /\ frontier(outside s) = s /\
         s INTER inside s = {} /\ s INTER outside s = {} /\
         closure(inside s) = s UNION inside s /\
         closure(outside s) = s UNION outside s`,
  GEN_TAC THEN DISCH_THEN(ASSUME_TAC o MATCH_MP MOI_SCD_PL_SPHERE_2_HOMEOMORPHIC) THEN
  MP_TAC(ISPEC `s:real^3->bool` JORDAN_INSIDE_OUTSIDE_GEN) THEN
  ASM_REWRITE_TAC[DIMINDEX_3; ARITH] THEN STRIP_TAC THEN
  SUBGOAL_THEN `compact(s:real^3->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[HOMEOMORPHIC_COMPACTNESS; COMPACT_SPHERE]; ALL_TAC] THEN
  ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN
  ONCE_REWRITE_TAC[GSYM CLOSURE_UNION_FRONTIER] THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN TRY(ASM SET_TAC[]) THEN
  REWRITE_TAC[CLOSURE_UNION_FRONTIER] THEN ASM_REWRITE_TAC[] THEN SET_TAC[]);;

(* PL 3-balls in real^3. *)

let MOI_S4X_JB_CLOSED = prove
 (`!s:real^3->bool. pl_sphere 2 s ==> closed(s UNION inside s) /\ closed(s UNION outside s)`,
  GEN_TAC THEN DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP MOI_S4X_JB) THEN
  REWRITE_TAC[GSYM CLOSURE_UNION_FRONTIER] THEN ASM_MESON_TAC[CLOSED_CLOSURE]);;

(* A connected set missing a PL 2-sphere lies on one side. *)

let MOI_S4X_SIDE3 = prove
 (`!s g:real^3->bool.
     pl_sphere 2 s /\ connected g /\ g INTER s = {}
     ==> g SUBSET inside s \/ g SUBSET outside s`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4X_JB) THEN
  MP_TAC(ISPECL [`g:real^3->bool`; `s UNION inside s:real^3->bool`;
                 `s UNION outside s:real^3->bool`; `s:real^3->bool`]
    MOI_SFR_CONNECTED_SIDE) THEN
  ASM_SIMP_TAC[MOI_S4X_JB_CLOSED] THEN
  ANTS_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`inside s UNION outside s = (:real^3) DIFF s`;
      `inside s INTER outside s:real^3->bool = {}`] THEN
    SET_TAC[];
    UNDISCH_TAC `g INTER s:real^3->bool = {}` THEN SET_TAC[]]);;

let MOI_S4X_BALL = prove
 (`!c:real^3->bool.
     pl_ball 3 c
     ==> compact c /\ closed c /\ pl_sphere 2 (frontier c) /\ frontier c SUBSET c /\
         interior c = inside(frontier c) /\ c = frontier c UNION inside(frontier c) /\
         closure(interior c) = c /\ connected(interior c) /\ ~(interior c = {}) /\
         open(interior c) /\ (:real^3) DIFF c = outside(frontier c)`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `compact(c:real^3->bool) /\ closed c` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_S4L_PL_BALL_COMPACT; COMPACT_IMP_CLOSED]; ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MOI_S4L_BALL_FRONTIER_SPHERE) THEN
  SUBGOAL_THEN `frontier c SUBSET (c:real^3->bool) /\
                interior c UNION frontier c = c /\ interior c INTER frontier c = {} /\
                frontier(interior c) SUBSET frontier c`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[FRONTIER_SUBSET_CLOSED; FRONTIER_INTERIOR_SUBSET] THEN
    REWRITE_TAC[frontier] THEN ASM_SIMP_TAC[CLOSURE_CLOSED] THEN
    MP_TAC(ISPEC `c:real^3->bool` INTERIOR_SUBSET) THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `connected(interior c:real^3->bool) /\ ~(interior c = {})`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `pl_ball 3 (c:real^3->bool)` THEN
    REWRITE_TAC[pl_ball] THEN
    DISCH_THEN(X_CHOOSE_THEN `k:real^3->bool` (X_CHOOSE_THEN `f:real^3->real^3`
      (X_CHOOSE_THEN `g:real^3->real^3` STRIP_ASSUME_TAC))) THEN
    MP_TAC(ISPECL [`k:real^3->bool`; `c:real^3->bool`; `f:real^3->real^3`;
                   `g:real^3->real^3`] MOI_SCD_BALL_FRONTIER) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    UNDISCH_TAC `pl_homeomorphism (k,c) (f:real^3->real^3,g)` THEN
    REWRITE_TAC[pl_homeomorphism; homeomorphism] THEN STRIP_TAC THEN
    SUBGOAL_THEN `closed(k:real^3->bool) /\ convex k /\ ~(k = {})` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL [ASM_MESON_TAC[SIMPLEX_IMP_CLOSED]; ALL_TAC] THEN
      CONJ_TAC THENL [ASM_MESON_TAC[SIMPLEX_IMP_CONVEX]; ALL_TAC] THEN
      DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `&3 simplex ({}:real^3->bool)` THEN
      REWRITE_TAC[SIMPLEX_EMPTY] THEN INT_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `relative_interior k = k DIFF relative_frontier(k:real^3->bool) /\
                  relative_frontier k SUBSET k`
    STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[RELATIVE_FRONTIER_SUBSET] THEN REWRITE_TAC[relative_frontier] THEN
      ASM_SIMP_TAC[CLOSURE_CLOSED] THEN
      MP_TAC(ISPEC `k:real^3->bool` RELATIVE_INTERIOR_SUBSET) THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `interior c = IMAGE (f:real^3->real^3) (relative_interior k)`
    SUBST1_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`f:real^3->real^3`; `k:real^3->bool`;
                     `relative_frontier k:real^3->bool`] IMAGE_DIFF_INJ_ALT) THEN
      ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_THEN SUBST1_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      MAP_EVERY UNDISCH_TAC
       [`interior c UNION frontier(c:real^3->bool) = c`;
        `interior c INTER frontier c:real^3->bool = {}`] THEN
      SET_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `k:real^3->bool` THEN
        ASM_REWRITE_TAC[RELATIVE_INTERIOR_SUBSET];
        MATCH_MP_TAC CONVEX_CONNECTED THEN ASM_SIMP_TAC[CONVEX_RELATIVE_INTERIOR]];
      ASM_SIMP_TAC[IMAGE_EQ_EMPTY; RELATIVE_INTERIOR_EQ_EMPTY]];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4X_JB) THEN
  SUBGOAL_THEN `!t:real^3->bool. connected t /\ t INTER frontier c = {} /\
                                 ~(t INTER interior c = {})
                                 ==> t SUBSET interior c`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`t:real^3->bool`; `interior c:real^3->bool`] CONNECTED_INTER_FRONTIER) THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC
     [`frontier(interior c) SUBSET frontier(c:real^3->bool)`;
      `t INTER frontier c:real^3->bool = {}`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `interior c = inside(frontier c:real^3->bool)` ASSUME_TAC THENL
   [SUBGOAL_THEN `interior c SUBSET inside(frontier c:real^3->bool) \/
                  interior c SUBSET outside(frontier c)` STRIP_ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_S4X_SIDE3 THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC SUBSET_ANTISYM THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      MAP_EVERY UNDISCH_TAC
       [`interior c SUBSET inside(frontier c:real^3->bool)`;
        `~(interior c:real^3->bool = {})`;
        `frontier c INTER inside(frontier c:real^3->bool) = {}`] THEN
      SET_TAC[];
      SUBGOAL_THEN `outside(frontier c:real^3->bool) SUBSET interior c` ASSUME_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
        MAP_EVERY UNDISCH_TAC
         [`interior c SUBSET outside(frontier c:real^3->bool)`;
          `~(interior c:real^3->bool = {})`;
          `frontier c INTER outside(frontier c:real^3->bool) = {}`] THEN
        SET_TAC[];
        ALL_TAC] THEN
      UNDISCH_TAC `~bounded(outside(frontier c):real^3->bool)` THEN
      MATCH_MP_TAC(TAUT `p ==> ~p ==> q`) THEN
      MATCH_MP_TAC BOUNDED_SUBSET THEN EXISTS_TAC `c:real^3->bool` THEN
      ASM_SIMP_TAC[COMPACT_IMP_BOUNDED] THEN
      MP_TAC(ISPEC `c:real^3->bool` INTERIOR_SUBSET) THEN
      UNDISCH_TAC `outside(frontier c:real^3->bool) SUBSET interior c` THEN SET_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[OPEN_INTERIOR] THEN
  REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `interior c UNION frontier(c:real^3->bool) = c` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    UNDISCH_TAC `interior c UNION frontier(c:real^3->bool) = c` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    UNDISCH_TAC `interior c UNION frontier(c:real^3->bool) = c` THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC
     [`inside(frontier c) UNION outside(frontier c) = (:real^3) DIFF frontier c`;
      `inside(frontier c) INTER outside(frontier c:real^3->bool) = {}`;
      `frontier c INTER outside(frontier c:real^3->bool) = {}`] THEN
    SET_TAC[]]);;

(* Sides of a circle in a PL 2-sphere (the two disks of a split). *)

let MOI_S4X_SIDES2 = prove
 (`!d d' k (x:real^N) w g1 g2.
     pl_cell_with_boundary 2 d k /\ pl_cell_with_boundary 2 d' k /\ d INTER d' = k /\
     x IN k /\ open w /\ x IN w /\
     w INTER ((d UNION d') DIFF k) SUBSET g1 UNION g2 /\
     connected g1 /\ connected g2 /\
     g1 SUBSET (d UNION d') DIFF k /\ g2 SUBSET (d UNION d') DIFF k
     ==> (g1 SUBSET d /\ g2 SUBSET d') \/ (g1 SUBSET d' /\ g2 SUBSET d)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_S4X_SIDES THEN
  MAP_EVERY EXISTS_TAC [`k:real^N->bool`; `x:real^N`; `w:real^N->bool`] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4L_PL_CELL2_TOPO o
    check (fun th -> rand(rator(concl th)) = `d:real^N->bool`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4L_PL_CELL2_TOPO o
    check (fun th -> rand(rator(concl th)) = `d':real^N->bool`)) THEN
  ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN ASM SET_TAC[]);;

(* Sides of a PL 2-sphere in real^3. *)

let MOI_S4X_SIDES3 = prove
 (`!s (x:real^3) w g1 g2.
     pl_sphere 2 s /\ x IN s /\ open w /\ x IN w /\
     w DIFF s SUBSET g1 UNION g2 /\ connected g1 /\ connected g2 /\
     g1 INTER s = {} /\ g2 INTER s = {}
     ==> (g1 SUBSET inside s /\ g2 SUBSET outside s) \/
         (g1 SUBSET outside s /\ g2 SUBSET inside s)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4X_JB) THEN
  MP_TAC(ISPECL [`s UNION inside s:real^3->bool`; `s UNION outside s:real^3->bool`;
                 `s:real^3->bool`; `x:real^3`; `w:real^3->bool`;
                 `g1:real^3->bool`; `g2:real^3->bool`] MOI_S4X_SIDES) THEN
  ASM_SIMP_TAC[MOI_S4X_JB_CLOSED] THEN
  SUBGOAL_THEN `(s UNION inside s) DIFF s = inside s /\
                (s UNION outside s) DIFF s = outside s /\
                ((s UNION inside s) UNION (s UNION outside s)) DIFF s =
                (:real^3) DIFF s /\
                (s UNION inside s) INTER (s UNION outside s) = s`
  (fun th -> REWRITE_TAC[th]) THENL
   [MAP_EVERY UNDISCH_TAC
     [`inside s UNION outside s = (:real^3) DIFF s`;
      `inside s INTER outside s:real^3->bool = {}`;
      `s INTER inside s:real^3->bool = {}`; `s INTER outside s:real^3->bool = {}`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^3) IN closure(inside s) /\ x IN closure(outside s)`
  (fun th -> REWRITE_TAC[th]) THENL [ASM SET_TAC[]; ALL_TAC] THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MAP_EVERY UNDISCH_TAC
   [`g1 INTER s:real^3->bool = {}`; `g2 INTER s:real^3->bool = {}`] THEN
  SET_TAC[]);;

(* The flip: a disk e on the d-side of a split of the sphere, meeting the   *)
(* circle k in the arc c of its boundary c UNION c', moves to the other side *)
(* when c is replaced by c' in the circle.                                  *)

let MOI_S4X_FLIP = prove
 (`!sg d d' k e r c c' (p:real^3) q.
     pl_sphere 2 sg /\ pl_cell_with_boundary 2 d k /\ pl_cell_with_boundary 2 d' k /\
     d UNION d' = sg /\ d INTER d' = k /\
     pl_cell_with_boundary 2 e r /\ e SUBSET sg /\
     pl_cell_with_boundary 1 c {p,q} /\ c UNION c' = r /\ c INTER c' = {p,q} /\
     k INTER e = c /\ e DIFF c SUBSET d
     ==> ?d1. pl_cell_with_boundary 2 d1 ((k DIFF (c DIFF {p,q})) UNION c') /\
              pl_cell_with_boundary 2 (d' UNION e) ((k DIFF (c DIFF {p,q})) UNION c') /\
              d1 UNION (d' UNION e) = sg /\
              d1 INTER (d' UNION e) = (k DIFF (c DIFF {p,q})) UNION c' /\
              d1 SUBSET d`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(r:real^3->bool) SUBSET e` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_S4L_PL_CELL_FACTS]; ALL_TAC] THEN
  SUBGOAL_THEN `d' INTER e = (c:real^3->bool)` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`e DIFF c SUBSET (d:real^3->bool)`; `k INTER e = (c:real^3->bool)`;
      `d INTER d' = (k:real^3->bool)`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`d':real^3->bool`; `k:real^3->bool`; `e:real^3->bool`; `r:real^3->bool`;
                 `c:real^3->bool`; `p:real^3`; `q:real^3`] MOI_S4X_DISK_GLUE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[DIMINDEX_3; ARITH] THEN
    MAP_EVERY UNDISCH_TAC
     [`k INTER e = (c:real^3->bool)`; `c UNION c' = (r:real^3->bool)`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(k UNION r) DIFF (c DIFF {p,q}) =
                (k DIFF (c DIFF {p:real^3,q})) UNION c'`
  SUBST1_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`c UNION c' = (r:real^3->bool)`; `c INTER c' = {p:real^3,q}`] THEN
    SET_TAC[];
    DISCH_TAC] THEN
  ABBREV_TAC `k1 = (k DIFF (c DIFF {p:real^3,q})) UNION c'` THEN
  SUBGOAL_THEN `(k1:real^3->bool) SUBSET d' UNION e` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_S4L_PL_CELL_FACTS]; ALL_TAC] THEN
  MP_TAC(ISPECL [`sg:real^3->bool`; `d' UNION e:real^3->bool`; `k1:real^3->bool`]
    DISK_COMPLEMENT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC
     [`e SUBSET (sg:real^3->bool)`; `d UNION d' = (sg:real^3->bool)`] THEN
    SET_TAC[];
    DISCH_TAC] THEN
  EXISTS_TAC `(sg DIFF (d' UNION e)) UNION k1:real^3->bool` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(k1:real^3->bool) SUBSET d` ASSUME_TAC THENL
   [EXPAND_TAC "k1" THEN
    MAP_EVERY UNDISCH_TAC
     [`e DIFF c SUBSET (d:real^3->bool)`; `k INTER e = (c:real^3->bool)`;
      `d INTER d' = (k:real^3->bool)`; `c UNION c' = (r:real^3->bool)`;
      `(r:real^3->bool) SUBSET e`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  MAP_EVERY UNDISCH_TAC
   [`(k1:real^3->bool) SUBSET d`; `(k1:real^3->bool) SUBSET d' UNION e`;
    `e SUBSET (sg:real^3->bool)`; `d UNION d' = (sg:real^3->bool)`] THEN
  SET_TAC[]);;

(* One step of the THETA construction: flip e to the d'-side if needed. *)

let MOI_S4X_FLIP_STEP = prove
 (`!sg d d' k e r c c' (p:real^3) q.
     pl_sphere 2 sg /\ pl_cell_with_boundary 2 d k /\ pl_cell_with_boundary 2 d' k /\
     d UNION d' = sg /\ d INTER d' = k /\
     pl_cell_with_boundary 2 e r /\ e SUBSET sg /\
     pl_cell_with_boundary 1 c {p,q} /\ c UNION c' = r /\ c INTER c' = {p,q} /\
     k INTER e = c /\ connected(e DIFF c)
     ==> ?d1 d1' k1 c1 c1'.
           pl_cell_with_boundary 2 d1 k1 /\ pl_cell_with_boundary 2 d1' k1 /\
           d1 UNION d1' = sg /\ d1 INTER d1' = k1 /\
           ((c1 = c /\ c1' = c' /\ k1 = k) \/
            (c1 = c' /\ c1' = c /\ k1 = (k DIFF (c DIFF {p,q})) UNION c')) /\
           e DIFF c1 SUBSET d1' /\ k1 INTER e = c1 /\
           (!a. a SUBSET d' DIFF k /\ a INTER e = {} ==> a SUBSET d1' DIFF k1) /\
           (!a. a INTER e = {} ==> k1 INTER a = k INTER a)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(r:real^3->bool) SUBSET e /\ closed (d:real^3->bool) /\ closed (d':real^3->bool)`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_S4L_PL_CELL_FACTS; COMPACT_IMP_CLOSED]; ALL_TAC] THEN
  SUBGOAL_THEN `e DIFF c SUBSET (d:real^3->bool) \/ e DIFF c SUBSET d'`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_SFR_CONNECTED_SIDE THEN EXISTS_TAC `k:real^3->bool` THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC
     [`k INTER e = (c:real^3->bool)`; `e SUBSET (sg:real^3->bool)`;
      `d UNION d' = (sg:real^3->bool)`] THEN
    SET_TAC[];
    MP_TAC(ISPECL [`sg:real^3->bool`; `d:real^3->bool`; `d':real^3->bool`; `k:real^3->bool`;
                   `e:real^3->bool`; `r:real^3->bool`; `c:real^3->bool`; `c':real^3->bool`;
                   `p:real^3`; `q:real^3`] MOI_S4X_FLIP) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `d1:real^3->bool` STRIP_ASSUME_TAC) THEN
    MAP_EVERY EXISTS_TAC
     [`d1:real^3->bool`; `d' UNION e:real^3->bool`;
      `(k DIFF (c DIFF {p:real^3,q})) UNION c'`; `c':real^3->bool`; `c:real^3->bool`] THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC
     [`k INTER e = (c:real^3->bool)`; `c UNION c' = (r:real^3->bool)`;
      `c INTER c' = {p:real^3,q}`; `(r:real^3->bool) SUBSET e`] THEN
    SET_TAC[];
    MAP_EVERY EXISTS_TAC
     [`d:real^3->bool`; `d':real^3->bool`; `k:real^3->bool`; `c:real^3->bool`;
      `c':real^3->bool`] THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[]]);;

let MOI_S4X_CELL1_SYM = prove
 (`!a p q:real^N. pl_cell_with_boundary 1 a {p,q} ==> pl_cell_with_boundary 1 a {q,p}`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN SET_TAC[]);;

let MOI_S4X_CELL1_ENDS = prove
 (`!a p q:real^N. pl_cell_with_boundary 1 a {p,q} ==> p IN a /\ q IN a /\ ~(p = q)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4L_PL_CELL_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4X_CELL1_ARC) THEN ASM SET_TAC[]);;

let MOI_S4X_CELL_DIFF_CONNECTED = prove
 (`!e r c:real^N->bool.
     pl_cell_with_boundary 2 e r /\ c SUBSET r ==> connected(e DIFF c)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4L_PL_CELL2_TOPO) THEN
  MATCH_MP_TAC CONNECTED_INTERMEDIATE_CLOSURE THEN
  EXISTS_TAC `e DIFF r:real^N->bool` THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

(* The hexagon of THETA is a PL circle. *)

let MOI_S4X_HEXAGON = prove
 (`!e1 e2 e3 c1 c2 c3 a12 a23 a31 (x1:real^3) y1 x2 y2 x3 y3.
     c1 SUBSET e1 /\ c2 SUBSET e2 /\ c3 SUBSET e3 /\
     DISJOINT e1 e2 /\ DISJOINT e1 e3 /\ DISJOINT e2 e3 /\
     pl_cell_with_boundary 1 c1 {x1,y1} /\ pl_cell_with_boundary 1 c2 {x2,y2} /\
     pl_cell_with_boundary 1 c3 {x3,y3} /\
     pl_cell_with_boundary 1 a12 {x1,y2} /\ pl_cell_with_boundary 1 a23 {x2,y3} /\
     pl_cell_with_boundary 1 a31 {x3,y1} /\
     DISJOINT a12 a23 /\ DISJOINT a12 a31 /\ DISJOINT a23 a31 /\
     a12 INTER e1 = {x1} /\ a12 INTER e2 = {y2} /\ a12 INTER e3 = {} /\
     a23 INTER e2 = {x2} /\ a23 INTER e3 = {y3} /\ a23 INTER e1 = {} /\
     a31 INTER e3 = {x3} /\ a31 INTER e1 = {y1} /\ a31 INTER e2 = {}
     ==> pl_sphere 1 (a12 UNION c2 UNION a23 UNION c3 UNION a31 UNION c1)`,
  REPEAT STRIP_TAC THEN
  MAP_EVERY (fun t -> FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4X_CELL1_ENDS o
    check (fun th -> rand(rator(concl th)) = t)))
   [`c1:real^3->bool`; `c2:real^3->bool`; `c3:real^3->bool`;
    `a12:real^3->bool`; `a23:real^3->bool`; `a31:real^3->bool`] THEN
  SUBGOAL_THEN `pl_cell_with_boundary 1 (a12 UNION c2) {x1:real^3,x2}` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S4X_ARC_UNION THEN EXISTS_TAC `y2:real^3` THEN
    ASM_SIMP_TAC[MOI_S4X_CELL1_SYM] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_cell_with_boundary 1 ((a12 UNION c2) UNION a23) {x1:real^3,y3}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S4X_ARC_UNION THEN EXISTS_TAC `x2:real^3` THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_cell_with_boundary 1 (((a12 UNION c2) UNION a23) UNION c3) {x1:real^3,x3}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S4X_ARC_UNION THEN EXISTS_TAC `y3:real^3` THEN
    ASM_SIMP_TAC[MOI_S4X_CELL1_SYM] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_cell_with_boundary 1 ((((a12 UNION c2) UNION a23) UNION c3) UNION a31)
                                        {x1:real^3,y1}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S4X_ARC_UNION THEN EXISTS_TAC `x3:real^3` THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `a12 UNION c2 UNION a23 UNION c3 UNION a31 UNION c1 =
                ((((a12 UNION c2) UNION a23) UNION c3) UNION a31) UNION (c1:real^3->bool)`
  SUBST1_TAC THENL [SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC MOI_S4X_ARCS_CIRCLE THEN
  MAP_EVERY EXISTS_TAC [`x1:real^3`; `y1:real^3`] THEN
  ASM_REWRITE_TAC[DIMINDEX_3; ARITH] THEN ASM SET_TAC[]);;

(* One step of THETA: the circle is m UNION c, with c an arc of the boundary *)
(* of the disk e meeting m only in its ends.                                *)

let MOI_S4X_THETA_STEP = prove
 (`!sg q q' m e r c c' (p:real^3) p2.
     pl_sphere 2 sg /\ pl_cell_with_boundary 2 q (m UNION c) /\
     pl_cell_with_boundary 2 q' (m UNION c) /\ q UNION q' = sg /\ q INTER q' = m UNION c /\
     pl_cell_with_boundary 2 e r /\ e SUBSET sg /\
     pl_cell_with_boundary 1 c {p,p2} /\ pl_cell_with_boundary 1 c' {p,p2} /\
     c UNION c' = r /\ c INTER c' = {p,p2} /\ m INTER e = {p,p2}
     ==> ?q1 q1' d d'.
           pl_cell_with_boundary 2 q1 (m UNION d) /\ pl_cell_with_boundary 2 q1' (m UNION d) /\
           q1 UNION q1' = sg /\ q1 INTER q1' = m UNION d /\
           ((d = c /\ d' = c') \/ (d = c' /\ d' = c)) /\
           pl_cell_with_boundary 1 d {p,p2} /\ pl_cell_with_boundary 1 d' {p,p2} /\
           d UNION d' = r /\ d INTER d' = {p,p2} /\
           e DIFF d SUBSET q1' DIFF (m UNION d) /\
           (!a. a SUBSET q' DIFF (m UNION c) /\ a INTER e = {}
                ==> a SUBSET q1' DIFF (m UNION d))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(r:real^3->bool) SUBSET e` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_S4L_PL_CELL_FACTS]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4X_CELL1_ENDS o
    check (fun th -> rand(rator(concl th)) = `c:real^3->bool`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4X_CELL1_ENDS o
    check (fun th -> rand(rator(concl th)) = `c':real^3->bool`)) THEN
  MP_TAC(ISPECL [`sg:real^3->bool`; `q:real^3->bool`; `q':real^3->bool`;
                 `m UNION c:real^3->bool`; `e:real^3->bool`; `r:real^3->bool`;
                 `c:real^3->bool`; `c':real^3->bool`; `p:real^3`; `p2:real^3`]
    MOI_S4X_FLIP_STEP) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       [`m INTER e = {p:real^3,p2}`; `(r:real^3->bool) SUBSET e`;
        `c UNION c' = (r:real^3->bool)`; `(p:real^3) IN c`; `(p2:real^3) IN c`] THEN
      SET_TAC[];
      MATCH_MP_TAC MOI_S4X_CELL_DIFF_CONNECTED THEN EXISTS_TAC `r:real^3->bool` THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `q1:real^3->bool` (X_CHOOSE_THEN `q1':real^3->bool`
    (X_CHOOSE_THEN `k1:real^3->bool` (X_CHOOSE_THEN `d:real^3->bool`
    (X_CHOOSE_THEN `d':real^3->bool` (fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th))))))) THEN
  SUBGOAL_THEN `k1 = m UNION (d:real^3->bool) /\
                pl_cell_with_boundary 1 d {p:real^3,p2} /\
                pl_cell_with_boundary 1 d' {p:real^3,p2} /\
                d UNION d' = (r:real^3->bool) /\ d INTER d' = {p,p2}`
  STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(DISJ_CASES_THEN STRIP_ASSUME_TAC o check (fun th -> is_disj(concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC
     [`m INTER e = {p:real^3,p2}`; `(r:real^3->bool) SUBSET e`;
      `c UNION c' = (r:real^3->bool)`; `c INTER c' = {p:real^3,p2}`;
      `(p:real^3) IN c`; `(p2:real^3) IN c`; `(p:real^3) IN c'`; `(p2:real^3) IN c'`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`q1:real^3->bool`; `q1':real^3->bool`; `d:real^3->bool`;
                        `d':real^3->bool`] THEN
  UNDISCH_TAC `k1 = m UNION (d:real^3->bool)` THEN DISCH_THEN SUBST_ALL_TAC THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th -> is_disj(concl th))) THEN MESON_TAC[];
    UNDISCH_TAC `(m UNION d) INTER e = (d:real^3->bool)` THEN
    UNDISCH_TAC `e DIFF d SUBSET (q1':real^3->bool)` THEN SET_TAC[]]);;

let MOI_S4X_THETA_FWD = prove
 (`!sg e1 e2 e3 r1 r2 r3 c1 c1' c2 c2' c3 c3' a12 a23 a31 (x1:real^3) y1 x2 y2 x3 y3.
     pl_sphere 2 sg /\
     pl_cell_with_boundary 2 e1 r1 /\ pl_cell_with_boundary 2 e2 r2 /\
     pl_cell_with_boundary 2 e3 r3 /\
     e1 SUBSET sg /\ e2 SUBSET sg /\ e3 SUBSET sg /\
     DISJOINT e1 e2 /\ DISJOINT e1 e3 /\ DISJOINT e2 e3 /\
     pl_cell_with_boundary 1 c1 {x1,y1} /\ pl_cell_with_boundary 1 c1' {x1,y1} /\
     c1 UNION c1' = r1 /\ c1 INTER c1' = {x1,y1} /\
     pl_cell_with_boundary 1 c2 {x2,y2} /\ pl_cell_with_boundary 1 c2' {x2,y2} /\
     c2 UNION c2' = r2 /\ c2 INTER c2' = {x2,y2} /\
     pl_cell_with_boundary 1 c3 {x3,y3} /\ pl_cell_with_boundary 1 c3' {x3,y3} /\
     c3 UNION c3' = r3 /\ c3 INTER c3' = {x3,y3} /\
     pl_cell_with_boundary 1 a12 {x1,y2} /\ pl_cell_with_boundary 1 a23 {x2,y3} /\
     pl_cell_with_boundary 1 a31 {x3,y1} /\
     a12 SUBSET sg /\ a23 SUBSET sg /\ a31 SUBSET sg /\
     DISJOINT a12 a23 /\ DISJOINT a12 a31 /\ DISJOINT a23 a31 /\
     a12 INTER e1 = {x1} /\ a12 INTER e2 = {y2} /\ a12 INTER e3 = {} /\
     a23 INTER e2 = {x2} /\ a23 INTER e3 = {y3} /\ a23 INTER e1 = {} /\
     a31 INTER e3 = {x3} /\ a31 INTER e1 = {y1} /\ a31 INTER e2 = {}
     ==> ?p p' d1 d1' d2 d2' d3 d3'.
           ((d1 = c1 /\ d1' = c1') \/ (d1 = c1' /\ d1' = c1)) /\
           ((d2 = c2 /\ d2' = c2') \/ (d2 = c2' /\ d2' = c2)) /\
           ((d3 = c3 /\ d3' = c3') \/ (d3 = c3' /\ d3' = c3)) /\
           pl_cell_with_boundary 2 p (a12 UNION a23 UNION a31 UNION d1 UNION d2 UNION d3) /\
           pl_cell_with_boundary 2 p' (a12 UNION a23 UNION a31 UNION d1 UNION d2 UNION d3) /\
           p UNION p' = sg /\
           p INTER p' = a12 UNION a23 UNION a31 UNION d1 UNION d2 UNION d3 /\
           e1 SUBSET p' /\ e2 SUBSET p' /\ e3 SUBSET p' /\
           p INTER e1 = d1 /\ p INTER e2 = d2 /\ p INTER e3 = d3`,
  REPEAT STRIP_TAC THEN
  MAP_EVERY (fun t -> FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4X_CELL1_ENDS o
    check (fun th -> rand(rator(concl th)) = t)))
   [`c1:real^3->bool`; `c2:real^3->bool`; `c3:real^3->bool`;
    `a12:real^3->bool`; `a23:real^3->bool`; `a31:real^3->bool`] THEN
  SUBGOAL_THEN `(r1:real^3->bool) SUBSET e1 /\ (r2:real^3->bool) SUBSET e2 /\
                (r3:real^3->bool) SUBSET e3`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN FIRST_ASSUM(MATCH_ACCEPT_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o
      MATCH_MP MOI_S4L_PL_CELL_FACTS); ALL_TAC] THEN
  ABBREV_TAC `aa = a12 UNION a23 UNION (a31:real^3->bool)` THEN
  SUBGOAL_THEN `(aa:real^3->bool) INTER e1 = {x1,y1} /\ aa INTER e2 = {x2,y2} /\
                aa INTER e3 = {x3,y3} /\ aa SUBSET sg`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "aa" THEN
    MAP_EVERY UNDISCH_TAC
     [`(a12:real^3->bool) INTER e1 = {x1}`; `(a12:real^3->bool) INTER e2 = {y2}`;
      `(a12:real^3->bool) INTER e3 = {}`; `(a23:real^3->bool) INTER e1 = {}`;
      `(a23:real^3->bool) INTER e2 = {x2}`; `(a23:real^3->bool) INTER e3 = {y3}`;
      `(a31:real^3->bool) INTER e1 = {y1}`; `(a31:real^3->bool) INTER e2 = {}`;
      `(a31:real^3->bool) INTER e3 = {x3}`; `(a12:real^3->bool) SUBSET sg`;
      `(a23:real^3->bool) SUBSET sg`; `(a31:real^3->bool) SUBSET sg`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  (* the hexagon and its split *)
  SUBGOAL_THEN `pl_sphere 1 ((aa UNION c2 UNION c3) UNION (c1:real^3->bool))`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `(aa UNION c2 UNION c3) UNION (c1:real^3->bool) =
                  a12 UNION c2 UNION a23 UNION c3 UNION a31 UNION c1` SUBST1_TAC THENL
     [EXPAND_TAC "aa" THEN SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC MOI_S4X_HEXAGON THEN
    MAP_EVERY EXISTS_TAC [`e1:real^3->bool`; `e2:real^3->bool`; `e3:real^3->bool`;
      `x1:real^3`; `y1:real^3`; `x2:real^3`; `y2:real^3`; `x3:real^3`; `y3:real^3`] THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`sg:real^3->bool`; `(aa UNION c2 UNION c3) UNION (c1:real^3->bool)`]
    SPHERE_SPLIT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `q0:real^3->bool` (X_CHOOSE_THEN `q0':real^3->bool`
    STRIP_ASSUME_TAC)) THEN
  (* step 1: the disk e1 *)
  MP_TAC(ISPECL [`sg:real^3->bool`; `q0:real^3->bool`; `q0':real^3->bool`;
                 `aa UNION c2 UNION (c3:real^3->bool)`;
                 `e1:real^3->bool`; `r1:real^3->bool`; `c1:real^3->bool`; `c1':real^3->bool`;
                 `x1:real^3`; `y1:real^3`] MOI_S4X_THETA_STEP) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC
     [`(aa:real^3->bool) INTER e1 = {x1,y1}`; `c2 UNION c2' = (r2:real^3->bool)`;
      `(r2:real^3->bool) SUBSET e2`; `c3 UNION c3' = (r3:real^3->bool)`;
      `(r3:real^3->bool) SUBSET e3`; `DISJOINT (e1:real^3->bool) e2`;
      `DISJOINT (e1:real^3->bool) e3`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `q1:real^3->bool` (X_CHOOSE_THEN `q1':real^3->bool`
    (X_CHOOSE_THEN `d1:real^3->bool` (X_CHOOSE_THEN `d1':real^3->bool`
    (fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)))))) THEN
  SUBGOAL_THEN `(d1:real^3->bool) SUBSET e1 /\ (d1':real^3->bool) SUBSET e1`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`d1 UNION d1' = (r1:real^3->bool)`; `(r1:real^3->bool) SUBSET e1`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  (* step 2: the disk e2 *)
  SUBGOAL_THEN `(aa UNION c2 UNION c3) UNION (d1:real^3->bool) =
                (aa UNION d1 UNION c3) UNION c2`
  (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL [SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`sg:real^3->bool`; `q1:real^3->bool`; `q1':real^3->bool`;
                 `aa UNION d1 UNION (c3:real^3->bool)`;
                 `e2:real^3->bool`; `r2:real^3->bool`; `c2:real^3->bool`; `c2':real^3->bool`;
                 `x2:real^3`; `y2:real^3`] MOI_S4X_THETA_STEP) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC
     [`(aa:real^3->bool) INTER e2 = {x2,y2}`; `(d1:real^3->bool) SUBSET e1`;
      `c3 UNION c3' = (r3:real^3->bool)`; `(r3:real^3->bool) SUBSET e3`;
      `DISJOINT (e1:real^3->bool) e2`; `DISJOINT (e2:real^3->bool) e3`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `q2:real^3->bool` (X_CHOOSE_THEN `q2':real^3->bool`
    (X_CHOOSE_THEN `d2:real^3->bool` (X_CHOOSE_THEN `d2':real^3->bool`
    (fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)))))) THEN
  SUBGOAL_THEN `(d2:real^3->bool) SUBSET e2 /\ (d2':real^3->bool) SUBSET e2`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`d2 UNION d2' = (r2:real^3->bool)`; `(r2:real^3->bool) SUBSET e2`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `e1 DIFF d1 SUBSET q2' DIFF ((aa UNION d1 UNION c3) UNION (d2:real^3->bool))`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `DISJOINT (e1:real^3->bool) e2` THEN SET_TAC[];
    ALL_TAC] THEN
  (* step 3: the disk e3 *)
  SUBGOAL_THEN `(aa UNION d1 UNION c3) UNION (d2:real^3->bool) =
                (aa UNION d1 UNION d2) UNION c3`
  (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL [SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`sg:real^3->bool`; `q2:real^3->bool`; `q2':real^3->bool`;
                 `aa UNION d1 UNION (d2:real^3->bool)`;
                 `e3:real^3->bool`; `r3:real^3->bool`; `c3:real^3->bool`; `c3':real^3->bool`;
                 `x3:real^3`; `y3:real^3`] MOI_S4X_THETA_STEP) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC
     [`(aa:real^3->bool) INTER e3 = {x3,y3}`; `(d1:real^3->bool) SUBSET e1`;
      `(d2:real^3->bool) SUBSET e2`; `DISJOINT (e1:real^3->bool) e3`;
      `DISJOINT (e2:real^3->bool) e3`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `q3:real^3->bool` (X_CHOOSE_THEN `q3':real^3->bool`
    (X_CHOOSE_THEN `d3:real^3->bool` (X_CHOOSE_THEN `d3':real^3->bool`
    (fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)))))) THEN
  SUBGOAL_THEN `(d3:real^3->bool) SUBSET e3 /\ (d3':real^3->bool) SUBSET e3`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`d3 UNION d3' = (r3:real^3->bool)`; `(r3:real^3->bool) SUBSET e3`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `e1 DIFF d1 SUBSET q3' DIFF ((aa UNION d1 UNION d2) UNION (d3:real^3->bool)) /\
    e2 DIFF d2 SUBSET q3' DIFF ((aa UNION d1 UNION d2) UNION (d3:real^3->bool))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC [`DISJOINT (e1:real^3->bool) e3`; `DISJOINT (e2:real^3->bool) e3`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(aa UNION d1 UNION d2) UNION (d3:real^3->bool) =
                a12 UNION a23 UNION a31 UNION d1 UNION d2 UNION d3`
  (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [EXPAND_TAC "aa" THEN SET_TAC[]; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`q3:real^3->bool`; `q3':real^3->bool`; `d1:real^3->bool`; `d1':real^3->bool`;
    `d2:real^3->bool`; `d2':real^3->bool`; `d3:real^3->bool`; `d3':real^3->bool`] THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY UNDISCH_TAC
   [`e1 DIFF d1 SUBSET q3' DIFF (a12 UNION a23 UNION a31 UNION d1 UNION d2 UNION
                                (d3:real^3->bool))`;
    `e2 DIFF d2 SUBSET q3' DIFF (a12 UNION a23 UNION a31 UNION d1 UNION d2 UNION
                                (d3:real^3->bool))`;
    `e3 DIFF d3 SUBSET q3' DIFF (a12 UNION a23 UNION a31 UNION d1 UNION d2 UNION
                                (d3:real^3->bool))`;
    `q3 INTER q3' = a12 UNION a23 UNION a31 UNION d1 UNION d2 UNION (d3:real^3->bool)`;
    `(d1:real^3->bool) SUBSET e1`; `(d2:real^3->bool) SUBSET e2`;
    `(d3:real^3->bool) SUBSET e3`] THEN
  SET_TAC[]);;

(* The flip seen from the other side: a disk e on the far side p' of the     *)
(* split, meeting p in the arc d of its boundary, joins p.                   *)

let MOI_S4X_FLIP_BACK = prove
 (`!sg p p' k e r d d' (x:real^3) y.
     pl_sphere 2 sg /\ pl_cell_with_boundary 2 p k /\ pl_cell_with_boundary 2 p' k /\
     p UNION p' = sg /\ p INTER p' = k /\
     pl_cell_with_boundary 2 e r /\ e SUBSET p' /\
     pl_cell_with_boundary 1 d {x,y} /\ d UNION d' = r /\ d INTER d' = {x,y} /\
     p INTER e = d /\ d SUBSET k
     ==> ?g. pl_cell_with_boundary 2 g ((k DIFF (d DIFF {x,y})) UNION d') /\
             pl_cell_with_boundary 2 (p UNION e) ((k DIFF (d DIFF {x,y})) UNION d') /\
             g UNION (p UNION e) = sg /\
             g INTER (p UNION e) = (k DIFF (d DIFF {x,y})) UNION d' /\
             g SUBSET p'`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_S4X_FLIP THEN
  MAP_EVERY EXISTS_TAC [`r:real^3->bool`] THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY UNDISCH_TAC
   [`p INTER p' = (k:real^3->bool)`; `p UNION p' = (sg:real^3->bool)`;
    `p INTER e = (d:real^3->bool)`; `(d:real^3->bool) SUBSET k`;
    `(e:real^3->bool) SUBSET p'`] THEN
  SET_TAC[]);;

let MOI_S4X_THETA = prove
 (`!sg e1 e2 e3 r1 r2 r3 c1 c1' c2 c2' c3 c3' a12 a23 a31 (x1:real^3) y1 x2 y2 x3 y3.
     pl_sphere 2 sg /\
     pl_cell_with_boundary 2 e1 r1 /\ pl_cell_with_boundary 2 e2 r2 /\
     pl_cell_with_boundary 2 e3 r3 /\
     e1 SUBSET sg /\ e2 SUBSET sg /\ e3 SUBSET sg /\
     DISJOINT e1 e2 /\ DISJOINT e1 e3 /\ DISJOINT e2 e3 /\
     pl_cell_with_boundary 1 c1 {x1,y1} /\ pl_cell_with_boundary 1 c1' {x1,y1} /\
     c1 UNION c1' = r1 /\ c1 INTER c1' = {x1,y1} /\
     pl_cell_with_boundary 1 c2 {x2,y2} /\ pl_cell_with_boundary 1 c2' {x2,y2} /\
     c2 UNION c2' = r2 /\ c2 INTER c2' = {x2,y2} /\
     pl_cell_with_boundary 1 c3 {x3,y3} /\ pl_cell_with_boundary 1 c3' {x3,y3} /\
     c3 UNION c3' = r3 /\ c3 INTER c3' = {x3,y3} /\
     pl_cell_with_boundary 1 a12 {x1,y2} /\ pl_cell_with_boundary 1 a23 {x2,y3} /\
     pl_cell_with_boundary 1 a31 {x3,y1} /\
     a12 SUBSET sg /\ a23 SUBSET sg /\ a31 SUBSET sg /\
     DISJOINT a12 a23 /\ DISJOINT a12 a31 /\ DISJOINT a23 a31 /\
     a12 INTER e1 = {x1} /\ a12 INTER e2 = {y2} /\ a12 INTER e3 = {} /\
     a23 INTER e2 = {x2} /\ a23 INTER e3 = {y3} /\ a23 INTER e1 = {} /\
     a31 INTER e3 = {x3} /\ a31 INTER e1 = {y1} /\ a31 INTER e2 = {}
     ==> ?p q d1 d1' d2 d2' d3 d3'.
           ((d1 = c1 /\ d1' = c1') \/ (d1 = c1' /\ d1' = c1)) /\
           ((d2 = c2 /\ d2' = c2') \/ (d2 = c2' /\ d2' = c2)) /\
           ((d3 = c3 /\ d3' = c3') \/ (d3 = c3' /\ d3' = c3)) /\
           pl_cell_with_boundary 2 p (a12 UNION a23 UNION a31 UNION d1 UNION d2 UNION d3) /\
           pl_cell_with_boundary 2 q (a12 UNION a23 UNION a31 UNION d1' UNION d2' UNION d3') /\
           p UNION q UNION e1 UNION e2 UNION e3 = sg /\
           p INTER q = a12 UNION a23 UNION a31 /\
           p INTER e1 = d1 /\ p INTER e2 = d2 /\ p INTER e3 = d3 /\
           q INTER e1 = d1' /\ q INTER e2 = d2' /\ q INTER e3 = d3'`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_S4X_THETA_FWD) THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^3->bool` (X_CHOOSE_THEN `p':real^3->bool`
    (X_CHOOSE_THEN `d1:real^3->bool` (X_CHOOSE_THEN `d1':real^3->bool`
    (X_CHOOSE_THEN `d2:real^3->bool` (X_CHOOSE_THEN `d2':real^3->bool`
    (X_CHOOSE_THEN `d3:real^3->bool` (X_CHOOSE_THEN `d3':real^3->bool`
    (fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)))))))))) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (fun th -> is_conj(concl th))) THEN
  SUBGOAL_THEN
   `pl_cell_with_boundary 1 d1 {x1:real^3,y1} /\ pl_cell_with_boundary 1 d1' {x1,y1} /\
    d1 UNION d1' = (r1:real^3->bool) /\ d1 INTER d1' = {x1,y1} /\
    pl_cell_with_boundary 1 d2 {x2:real^3,y2} /\ pl_cell_with_boundary 1 d2' {x2,y2} /\
    d2 UNION d2' = (r2:real^3->bool) /\ d2 INTER d2' = {x2,y2} /\
    pl_cell_with_boundary 1 d3 {x3:real^3,y3} /\ pl_cell_with_boundary 1 d3' {x3,y3} /\
    d3 UNION d3' = (r3:real^3->bool) /\ d3 INTER d3' = {x3,y3}`
  STRIP_ASSUME_TAC THENL
   [REPEAT(FIRST_X_ASSUM(DISJ_CASES_THEN STRIP_ASSUME_TAC o
      check (fun th -> is_disj(concl th)))) THEN
    ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[UNION_COMM; INTER_COMM];
    ALL_TAC] THEN
  MAP_EVERY (fun t -> FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4X_CELL1_ENDS o
    check (fun th -> rand(rator(concl th)) = t)))
   [`a12:real^3->bool`; `a23:real^3->bool`; `a31:real^3->bool`] THEN
  SUBGOAL_THEN `(r1:real^3->bool) SUBSET e1 /\ (r2:real^3->bool) SUBSET e2 /\
                (r3:real^3->bool) SUBSET e3`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN FIRST_ASSUM(MATCH_ACCEPT_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o
      MATCH_MP MOI_S4L_PL_CELL_FACTS); ALL_TAC] THEN
  SUBGOAL_THEN `(d1:real^3->bool) SUBSET e1 /\ (d1':real^3->bool) SUBSET e1 /\
                (d2:real^3->bool) SUBSET e2 /\ (d2':real^3->bool) SUBSET e2 /\
                (d3:real^3->bool) SUBSET e3 /\ (d3':real^3->bool) SUBSET e3`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`d1 UNION d1' = (r1:real^3->bool)`; `d2 UNION d2' = (r2:real^3->bool)`;
      `d3 UNION d3' = (r3:real^3->bool)`; `(r1:real^3->bool) SUBSET e1`;
      `(r2:real^3->bool) SUBSET e2`; `(r3:real^3->bool) SUBSET e3`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `aa = a12 UNION a23 UNION (a31:real^3->bool)` THEN
  SUBGOAL_THEN `(aa:real^3->bool) INTER e1 = {x1,y1} /\ aa INTER e2 = {x2,y2} /\
                aa INTER e3 = {x3,y3} /\
                x1 IN aa /\ y1 IN aa /\ x2 IN aa /\ y2 IN aa /\ x3 IN aa /\ y3 IN aa`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "aa" THEN
    MAP_EVERY UNDISCH_TAC
     [`a12 INTER e1 = {x1:real^3}`; `a12 INTER e2 = {y2:real^3}`;
      `a12 INTER e3:real^3->bool = {}`;
      `a23 INTER e2 = {x2:real^3}`; `a23 INTER e3 = {y3:real^3}`;
      `a23 INTER e1:real^3->bool = {}`;
      `a31 INTER e3 = {x3:real^3}`; `a31 INTER e1 = {y1:real^3}`;
      `a31 INTER e2:real^3->bool = {}`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `a12 UNION a23 UNION a31 UNION d1 UNION d2 UNION (d3:real^3->bool) =
                aa UNION d1 UNION d2 UNION d3 /\
                a12 UNION a23 UNION a31 UNION d1' UNION d2' UNION (d3':real^3->bool) =
                aa UNION d1' UNION d2' UNION d3'`
  (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th]) THENL
   [EXPAND_TAC "aa" THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `DISJOINT (d2:real^3->bool) e1 /\ DISJOINT (d3:real^3->bool) e1 /\
                DISJOINT (d1':real^3->bool) e2 /\ DISJOINT (d3:real^3->bool) e2 /\
                DISJOINT (d1':real^3->bool) e3 /\ DISJOINT (d2':real^3->bool) e3 /\
                x1 IN d1' /\ y1 IN (d1':real^3->bool) /\ x2 IN d2' /\
                y2 IN (d2':real^3->bool) /\ x3 IN d3' /\ y3 IN (d3':real^3->bool)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`(d1':real^3->bool) SUBSET e1`; `(d2:real^3->bool) SUBSET e2`;
      `(d2':real^3->bool) SUBSET e2`; `(d3:real^3->bool) SUBSET e3`;
      `DISJOINT (e1:real^3->bool) e2`; `DISJOINT (e1:real^3->bool) e3`;
      `DISJOINT (e2:real^3->bool) e3`;
      `d1 INTER d1' = {x1:real^3,y1}`; `d2 INTER d2' = {x2:real^3,y2}`;
      `d3 INTER d3' = {x3:real^3,y3}`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  (* backward flip 1 *)
  MP_TAC(ISPECL [`sg:real^3->bool`; `p:real^3->bool`; `p':real^3->bool`;
                 `aa UNION d1 UNION d2 UNION (d3:real^3->bool)`;
                 `e1:real^3->bool`; `r1:real^3->bool`; `d1:real^3->bool`; `d1':real^3->bool`;
                 `x1:real^3`; `y1:real^3`] MOI_S4X_FLIP_BACK) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `((aa UNION d1 UNION d2 UNION d3) DIFF (d1 DIFF {x1,y1})) UNION d1' =
    aa UNION d1' UNION d2 UNION (d3:real^3->bool)`
  SUBST1_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`(aa:real^3->bool) INTER e1 = {x1,y1}`; `(d1:real^3->bool) SUBSET e1`;
      `DISJOINT (d2:real^3->bool) e1`; `DISJOINT (d3:real^3->bool) e1`;
      `x1 IN (d1':real^3->bool)`; `y1 IN (d1':real^3->bool)`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `g1:real^3->bool` STRIP_ASSUME_TAC) THEN
  (* backward flip 2 *)
  MP_TAC(ISPECL [`sg:real^3->bool`; `p UNION e1:real^3->bool`; `g1:real^3->bool`;
                 `aa UNION d1' UNION d2 UNION (d3:real^3->bool)`;
                 `e2:real^3->bool`; `r2:real^3->bool`; `d2:real^3->bool`; `d2':real^3->bool`;
                 `x2:real^3`; `y2:real^3`] MOI_S4X_FLIP_BACK) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC
     [`g1 UNION (p UNION e1) = (sg:real^3->bool)`;
      `g1 INTER (p UNION e1) = aa UNION d1' UNION d2 UNION (d3:real^3->bool)`;
      `p INTER e2 = (d2:real^3->bool)`; `DISJOINT (e1:real^3->bool) e2`;
      `(e2:real^3->bool) SUBSET sg`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((aa UNION d1' UNION d2 UNION d3) DIFF (d2 DIFF {x2,y2})) UNION d2' =
    aa UNION d1' UNION d2' UNION (d3:real^3->bool)`
  SUBST1_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`(aa:real^3->bool) INTER e2 = {x2,y2}`; `(d2:real^3->bool) SUBSET e2`;
      `DISJOINT (d1':real^3->bool) e2`; `DISJOINT (d3:real^3->bool) e2`;
      `x2 IN (d2':real^3->bool)`; `y2 IN (d2':real^3->bool)`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `g2:real^3->bool` STRIP_ASSUME_TAC) THEN
  (* backward flip 3 *)
  MP_TAC(ISPECL [`sg:real^3->bool`; `(p UNION e1) UNION e2:real^3->bool`; `g2:real^3->bool`;
                 `aa UNION d1' UNION d2' UNION (d3:real^3->bool)`;
                 `e3:real^3->bool`; `r3:real^3->bool`; `d3:real^3->bool`; `d3':real^3->bool`;
                 `x3:real^3`; `y3:real^3`] MOI_S4X_FLIP_BACK) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC
     [`g2 UNION ((p UNION e1) UNION e2) = (sg:real^3->bool)`;
      `g2 INTER ((p UNION e1) UNION e2) = aa UNION d1' UNION d2' UNION (d3:real^3->bool)`;
      `p INTER e3 = (d3:real^3->bool)`; `DISJOINT (e1:real^3->bool) e3`;
      `DISJOINT (e2:real^3->bool) e3`; `(e3:real^3->bool) SUBSET sg`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((aa UNION d1' UNION d2' UNION d3) DIFF (d3 DIFF {x3,y3})) UNION d3' =
    aa UNION d1' UNION d2' UNION (d3':real^3->bool)`
  SUBST1_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`(aa:real^3->bool) INTER e3 = {x3,y3}`; `(d3:real^3->bool) SUBSET e3`;
      `DISJOINT (d1':real^3->bool) e3`; `DISJOINT (d2':real^3->bool) e3`;
      `x3 IN (d3':real^3->bool)`; `y3 IN (d3':real^3->bool)`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `g3:real^3->bool` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC
   [`p:real^3->bool`; `g3:real^3->bool`; `d1:real^3->bool`; `d1':real^3->bool`;
    `d2:real^3->bool`; `d2':real^3->bool`; `d3:real^3->bool`; `d3':real^3->bool`] THEN
  SUBGOAL_THEN `a12 UNION a23 UNION a31 UNION d1 UNION d2 UNION (d3:real^3->bool) =
                aa UNION d1 UNION d2 UNION d3 /\
                a12 UNION a23 UNION a31 UNION d1' UNION d2' UNION (d3':real^3->bool) =
                aa UNION d1' UNION d2' UNION d3'`
  (fun th -> REWRITE_TAC[th]) THENL
   [EXPAND_TAC "aa" THEN SET_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `DISJOINT (d2':real^3->bool) e1 /\ DISJOINT (d3':real^3->bool) e1 /\
                DISJOINT (d3':real^3->bool) e2`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`(d2':real^3->bool) SUBSET e2`; `(d3':real^3->bool) SUBSET e3`;
      `DISJOINT (e1:real^3->bool) e2`; `DISJOINT (e1:real^3->bool) e3`;
      `DISJOINT (e2:real^3->bool) e3`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `g3 INTER e1 = (d1':real^3->bool)` (fun th -> REWRITE_TAC[th]) THENL
   [MAP_EVERY UNDISCH_TAC
     [`g3 INTER (((p UNION e1) UNION e2) UNION e3) =
       aa UNION d1' UNION d2' UNION (d3':real^3->bool)`;
      `(aa:real^3->bool) INTER e1 = {x1,y1}`; `(d1':real^3->bool) SUBSET e1`;
      `DISJOINT (d2':real^3->bool) e1`; `DISJOINT (d3':real^3->bool) e1`;
      `x1 IN (d1':real^3->bool)`; `y1 IN (d1':real^3->bool)`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `g3 INTER e2 = (d2':real^3->bool)` (fun th -> REWRITE_TAC[th]) THENL
   [MAP_EVERY UNDISCH_TAC
     [`g3 INTER (((p UNION e1) UNION e2) UNION e3) =
       aa UNION d1' UNION d2' UNION (d3':real^3->bool)`;
      `(aa:real^3->bool) INTER e2 = {x2,y2}`; `(d2':real^3->bool) SUBSET e2`;
      `DISJOINT (d1':real^3->bool) e2`; `DISJOINT (d3':real^3->bool) e2`;
      `x2 IN (d2':real^3->bool)`; `y2 IN (d2':real^3->bool)`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `g3 INTER e3 = (d3':real^3->bool)` (fun th -> REWRITE_TAC[th]) THENL
   [MAP_EVERY UNDISCH_TAC
     [`g3 INTER (((p UNION e1) UNION e2) UNION e3) =
       aa UNION d1' UNION d2' UNION (d3':real^3->bool)`;
      `(aa:real^3->bool) INTER e3 = {x3,y3}`; `(d3':real^3->bool) SUBSET e3`;
      `DISJOINT (d1':real^3->bool) e3`; `DISJOINT (d2':real^3->bool) e3`;
      `x3 IN (d3':real^3->bool)`; `y3 IN (d3':real^3->bool)`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [UNDISCH_TAC `g3 UNION (((p UNION e1) UNION e2) UNION e3) = (sg:real^3->bool)` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(aa:real^3->bool) SUBSET p` ASSUME_TAC THENL
   [UNDISCH_TAC `p INTER p' = aa UNION d1 UNION d2 UNION (d3:real^3->bool)` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `p INTER d1' SUBSET (aa:real^3->bool) /\ p INTER d2' SUBSET aa /\
                p INTER d3' SUBSET aa`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`p INTER e1 = (d1:real^3->bool)`; `p INTER e2 = (d2:real^3->bool)`;
      `p INTER e3 = (d3:real^3->bool)`;
      `d1 INTER d1' = {x1:real^3,y1}`; `d2 INTER d2' = {x2:real^3,y2}`;
      `d3 INTER d3' = {x3:real^3,y3}`;
      `(d1':real^3->bool) SUBSET e1`; `(d2':real^3->bool) SUBSET e2`;
      `(d3':real^3->bool) SUBSET e3`;
      `x1 IN (aa:real^3->bool)`; `y1 IN (aa:real^3->bool)`; `x2 IN (aa:real^3->bool)`;
      `y2 IN (aa:real^3->bool)`; `x3 IN (aa:real^3->bool)`; `y3 IN (aa:real^3->bool)`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  MAP_EVERY UNDISCH_TAC
   [`g3 INTER (((p UNION e1) UNION e2) UNION e3) =
     aa UNION d1' UNION d2' UNION (d3':real^3->bool)`;
    `(aa:real^3->bool) SUBSET p`; `p INTER d1' SUBSET (aa:real^3->bool)`;
    `p INTER d2' SUBSET (aa:real^3->bool)`; `p INTER d3' SUBSET (aa:real^3->bool)`] THEN
  SET_TAC[]);;


(* ------------------------------------------------------------------------- *)
(* The tetra configuration.  Four PL 3-balls V 0, ..., V 3                   *)
(* (the vertex balls of r), meeting pairwise in the splitting disks          *)
(* V i INTER V j with rims R i j, never three at a time; four face disks D l *)
(* (D l the face opposite the vertex l) with boundaries J l, touching the    *)
(* balls only in J l, which is the union of the three face arcs D l INTER   *)
(* V i, each a PL arc whose ends are the points where D l meets the two     *)
(* splitting disks at V i.                                                   *)
(* ------------------------------------------------------------------------- *)

let moi_s4x_tconf = new_definition
 `moi_s4x_tconf (V:num->real^3->bool) (R:num->num->real^3->bool)
                (D:num->real^3->bool) (J:num->real^3->bool) <=>
   (!i. i < 4 ==> pl_ball 3 (V i)) /\
   (!i j. i < 4 /\ j < 4 /\ ~(i = j)
          ==> R j i = R i j /\ pl_cell_with_boundary 2 (V i INTER V j) (R i j) /\
              V i INTER V j SUBSET frontier (V i) /\
              (V i INTER V j) DIFF R i j SUBSET interior (V i UNION V j)) /\
   (!i j k. i < 4 /\ j < 4 /\ k < 4 /\ ~(i = j) /\ ~(i = k) /\ ~(j = k)
            ==> V i INTER V j INTER V k = {}) /\
   (!l. l < 4
        ==> pl_cell_with_boundary 2 (D l) (J l) /\ D l INTER V l = {} /\
            J l = UNIONS {D l INTER V i | i | i < 4}) /\
   (!l m. l < 4 /\ m < 4 /\ ~(l = m) ==> DISJOINT (D l) (D m)) /\
   (!l i j k. l < 4 /\ i < 4 /\ j < 4 /\ k < 4 /\
              ~(l = i) /\ ~(l = j) /\ ~(l = k) /\ ~(i = j) /\ ~(i = k) /\ ~(j = k)
              ==> (?x. D l INTER V i INTER V j = {x}) /\
                  pl_cell_with_boundary 1 (D l INTER V i)
                    ((D l INTER V i INTER V j) UNION (D l INTER V i INTER V k)))`;;

let MOI_S4X_TC_TAC =
  REWRITE_TAC[moi_s4x_tconf] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ball") (CONJUNCTS_THEN2 (LABEL_TAC "edge")
    (CONJUNCTS_THEN2 (LABEL_TAC "three") (CONJUNCTS_THEN2 (LABEL_TAC "face")
    (CONJUNCTS_THEN2 (LABEL_TAC "fdisj") (LABEL_TAC "fpt"))))));;

(* A 2-cell meeting an open set meets it off its boundary. *)

let MOI_S4X_CELL_TOUCH = prove
 (`!d j w:real^N->bool.
     pl_cell_with_boundary 2 d j /\ open w /\ (d DIFF j) INTER w = {}
     ==> d INTER w = {}`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4L_PL_CELL2_TOPO) THEN
  REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN X_GEN_TAC `x:real^N` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `(x:real^N) IN closure(d DIFF j)` MP_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[CLOSURE_APPROACHABLE] THEN
  UNDISCH_TAC `open(w:real^N->bool)` THEN REWRITE_TAC[open_def] THEN
  DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(y:real^N) IN w` MP_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    UNDISCH_TAC `(d DIFF j) INTER w:real^N->bool = {}` THEN
    UNDISCH_TAC `(y:real^N) IN d DIFF j` THEN SET_TAC[]]);;

(* Basic consequences: face disks off their boundaries miss the balls, face *)
(* arcs lie in the frontiers of the balls, face points lie on the rims.     *)

let MOI_S4X_TC_BASIC = prove
 (`!V R D J.
     moi_s4x_tconf V R D J
     ==> (!l i. l < 4 /\ i < 4 ==> (D l DIFF J l) INTER V i = {}) /\
         (!l i. l < 4 /\ i < 4 ==> D l INTER V i SUBSET J l) /\
         (!l i. l < 4 /\ i < 4 ==> D l INTER V i SUBSET frontier(V i)) /\
         (!l i j. l < 4 /\ i < 4 /\ j < 4 /\ ~(i = j)
                  ==> D l INTER V i INTER V j SUBSET R i j)`,
  REPEAT GEN_TAC THEN MOI_S4X_TC_TAC THEN
  SUBGOAL_THEN `!l i. l < 4 /\ i < 4 ==> (D l DIFF J l) INTER V i = {} /\
                                        D l INTER V i SUBSET (J:num->real^3->bool) l`
  (LABEL_TAC "dj") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    USE_THEN "face" (MP_TAC o SPEC `l:num`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT2(CONJUNCT2 th)]) THEN
    REWRITE_TAC[UNIONS_GSPEC] THEN
    UNDISCH_TAC `i < 4` THEN SET_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `closed((V:num->real^3->bool) i)` ASSUME_TAC THENL
     [USE_THEN "ball" (MP_TAC o SPEC `i:num`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN MESON_TAC[MOI_S4X_BALL];
      ALL_TAC] THEN
    SUBGOAL_THEN `(D:num->real^3->bool) l INTER interior((V:num->real^3->bool) i) = {}` MP_TAC THENL
     [MATCH_MP_TAC MOI_S4X_CELL_TOUCH THEN
      EXISTS_TAC `(J:num->real^3->bool) l` THEN REWRITE_TAC[OPEN_INTERIOR] THEN
      CONJ_TAC THENL
       [USE_THEN "face" (MP_TAC o SPEC `l:num`) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
        USE_THEN "dj" (MP_TAC o SPECL [`l:num`; `i:num`]) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        MP_TAC(ISPEC `(V:num->real^3->bool) i` INTERIOR_SUBSET) THEN SET_TAC[]];
      ALL_TAC] THEN
    REWRITE_TAC[frontier] THEN ASM_SIMP_TAC[CLOSURE_CLOSED] THEN SET_TAC[];
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(D:num->real^3->bool) l INTER interior((V:num->real^3->bool) i UNION V j) = {}` MP_TAC THENL
   [MATCH_MP_TAC MOI_S4X_CELL_TOUCH THEN
    EXISTS_TAC `(J:num->real^3->bool) l` THEN REWRITE_TAC[OPEN_INTERIOR] THEN
    CONJ_TAC THENL
     [USE_THEN "face" (MP_TAC o SPEC `l:num`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
      USE_THEN "dj" (MP_TAC o SPECL [`l:num`; `i:num`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      USE_THEN "dj" (MP_TAC o SPECL [`l:num`; `j:num`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      MP_TAC(ISPEC `(V:num->real^3->bool) i UNION V j` INTERIOR_SUBSET) THEN SET_TAC[]];
    ALL_TAC] THEN
  USE_THEN "edge" (MP_TAC o SPECL [`i:num`; `j:num`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SET_TAC[]);;

let MOI_S4X_PERM = prove
 (`!i j k l.
     i < 4 /\ j < 4 /\ k < 4 /\ l < 4 /\
     ~(i = j) /\ ~(i = k) /\ ~(i = l) /\ ~(j = k) /\ ~(j = l) /\ ~(k = l)
     ==> !m. m < 4 <=> m = i \/ m = j \/ m = k \/ m = l`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `{i:num,j,k,l} = {m:num | m < 4}` MP_TAC THENL
   [MATCH_MP_TAC CARD_SUBSET_EQ THEN
    REWRITE_TAC[FINITE_NUMSEG_LT; CARD_NUMSEG_LT] THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC[SUBSET; IN_INSERT; NOT_IN_EMPTY; IN_ELIM_THM] THEN
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
      SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN
      ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN CONV_TAC NUM_REDUCE_CONV];
    REWRITE_TAC[EXTENSION; IN_INSERT; NOT_IN_EMPTY; IN_ELIM_THM] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN MESON_TAC[]]);;

let MOI_S4X_OTHER2 = prove
 (`!i j. i < 4 /\ j < 4 /\ ~(i = j)
         ==> ?k l. k < 4 /\ l < 4 /\ ~(i = k) /\ ~(i = l) /\ ~(j = k) /\ ~(j = l) /\
                   ~(k = l)`,
  REPEAT STRIP_TAC THEN
  EXISTS_TAC `if ~(i = 0) /\ ~(j = 0) then 0 else if ~(i = 1) /\ ~(j = 1) then 1 else 2` THEN
  EXISTS_TAC `if ~(i = 3) /\ ~(j = 3) then 3 else if ~(i = 2) /\ ~(j = 2) then 2 else 1` THEN
  MAP_EVERY UNDISCH_TAC [`~(i:num = j)`; `j < 4`; `i < 4`] THEN
  REWRITE_TAC[ARITH_RULE `n < 4 <=> n = 0 \/ n = 1 \/ n = 2 \/ n = 3`] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) THEN
  REWRITE_TAC[ARITH]);;

(* The two face points on a splitting disk. *)

let MOI_S4X_TC_PTS = prove
 (`!V R D J i j k l.
     moi_s4x_tconf V R D J /\
     i < 4 /\ j < 4 /\ k < 4 /\ l < 4 /\
     ~(i = j) /\ ~(i = k) /\ ~(i = l) /\ ~(j = k) /\ ~(j = l) /\ ~(k = l)
     ==> UNIONS {D m INTER V i INTER V j | m | m < 4 /\ ~(m = i) /\ ~(m = j)} =
         (D k INTER V i INTER V j) UNION (D l INTER V i INTER V j) /\
         UNIONS {D m INTER V j INTER V i | m | m < 4 /\ ~(m = j) /\ ~(m = i)} =
         (D k INTER V i INTER V j) UNION (D l INTER V i INTER V j)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`i:num`; `j:num`; `k:num`; `l:num`] MOI_S4X_PERM) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  REWRITE_TAC[UNIONS_GSPEC] THEN CONJ_TAC THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:real^3` THEN
  REWRITE_TAC[IN_ELIM_THM; IN_UNION; IN_INTER] THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[]);;

(* The two arcs of each rim between its two face points, chosen once for   *)
(* each splitting disk (symmetric in i, j).                                 *)

let MOI_S4X_RIMARCS = prove
 (`!V R D J.
     moi_s4x_tconf V R D J
     ==> ?C C'. !i j k l.
           i < 4 /\ j < 4 /\ k < 4 /\ l < 4 /\
           ~(i = j) /\ ~(i = k) /\ ~(i = l) /\ ~(j = k) /\ ~(j = l) /\ ~(k = l)
           ==> C j i = C i j /\ C' j i = C' i j /\
               pl_cell_with_boundary 1 (C i j)
                 ((D k INTER V i INTER V j) UNION (D l INTER V i INTER V j)) /\
               pl_cell_with_boundary 1 (C' i j)
                 ((D k INTER V i INTER V j) UNION (D l INTER V i INTER V j)) /\
               C i j UNION C' i j = R i j /\
               C i j INTER C' i j =
               (D k INTER V i INTER V j) UNION (D l INTER V i INTER V j)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4X_TC_BASIC) THEN
  SUBGOAL_THEN
   `!i j. ?A B. i < 4 /\ j < 4 /\ ~(i = j)
                ==> pl_cell_with_boundary 1 A
                      (UNIONS {(D:num->real^3->bool) m INTER V i INTER V j | m |
                               m < 4 /\ ~(m = i) /\ ~(m = j)}) /\
                    pl_cell_with_boundary 1 B
                      (UNIONS {D m INTER V i INTER V j | m |
                               m < 4 /\ ~(m = i) /\ ~(m = j)}) /\
                    A UNION B = (R:num->num->real^3->bool) i j /\
                    A INTER B = UNIONS {D m INTER V i INTER V j | m |
                                        m < 4 /\ ~(m = i) /\ ~(m = j)}`
  MP_TAC THENL
   [REPEAT GEN_TAC THEN
    ASM_CASES_TAC `i < 4 /\ j < 4 /\ ~(i = j)` THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[] o check (fun th -> is_conj(concl th) &&
      concl th = `i < 4 /\ j < 4 /\ ~(i = j)`)) THEN
    MP_TAC(SPECL [`i:num`; `j:num`] MOI_S4X_OTHER2) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `l:num` STRIP_ASSUME_TAC)) THEN
    MP_TAC(ISPECL [`V:num->real^3->bool`; `R:num->num->real^3->bool`;
                   `D:num->real^3->bool`; `J:num->real^3->bool`;
                   `i:num`; `j:num`; `k:num`; `l:num`] MOI_S4X_TC_PTS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(SUBST1_TAC o CONJUNCT1)] THEN
    UNDISCH_TAC `moi_s4x_tconf V R D (J:num->real^3->bool)` THEN MOI_S4X_TC_TAC THEN
    USE_THEN "fpt" (MP_TAC o SPECL [`k:num`; `i:num`; `j:num`; `l:num`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_TAC `x:real^3` o CONJUNCT1) THEN
    USE_THEN "fpt" (MP_TAC o SPECL [`l:num`; `i:num`; `j:num`; `k:num`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_TAC `y:real^3` o CONJUNCT1) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `{x:real^3} UNION {y} = {x,y}` SUBST1_TAC THENL [SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC MOI_S4X_CIRCLE_SPLIT THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MOI_S4O_CELL_SPHERE THEN
      EXISTS_TAC `(V:num->real^3->bool) i INTER V j` THEN
      USE_THEN "edge" (MP_TAC o SPECL [`i:num`; `j:num`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[ARITH_RULE `1 + 1 = 2`]];
      FIRST_X_ASSUM(MP_TAC o SPECL [`k:num`; `i:num`; `j:num`] o check (fun th ->
        is_forall(concl th) && length(fst(strip_forall(concl th))) = 3)) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN ASM SET_TAC[];
      FIRST_X_ASSUM(MP_TAC o SPECL [`l:num`; `i:num`; `j:num`] o check (fun th ->
        is_forall(concl th) && length(fst(strip_forall(concl th))) = 3)) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN ASM SET_TAC[];
      USE_THEN "fdisj" (MP_TAC o SPECL [`k:num`; `l:num`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `A0:num->num->real^3->bool`
    (X_CHOOSE_THEN `B0:num->num->real^3->bool` (LABEL_TAC "ab"))) THEN
  EXISTS_TAC `\i j. if i < j then (A0:num->num->real^3->bool) i j else A0 j i` THEN
  EXISTS_TAC `\i j. if i < j then (B0:num->num->real^3->bool) i j else B0 j i` THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`V:num->real^3->bool`; `R:num->num->real^3->bool`;
                 `D:num->real^3->bool`; `J:num->real^3->bool`;
                 `i:num`; `j:num`; `k:num`; `l:num`] MOI_S4X_TC_PTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `(R:num->num->real^3->bool) j i = R i j` ASSUME_TAC THENL
   [UNDISCH_TAC `moi_s4x_tconf V R D (J:num->real^3->bool)` THEN MOI_S4X_TC_TAC THEN
    USE_THEN "edge" (MP_TAC o SPECL [`i:num`; `j:num`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  ASM_CASES_TAC `i:num < j` THENL
   [SUBGOAL_THEN `~(j:num < i)` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    USE_THEN "ab" (MP_TAC o SPECL [`i:num`; `j:num`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN ASM_REWRITE_TAC[];
    SUBGOAL_THEN `j:num < i` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    USE_THEN "ab" (MP_TAC o SPECL [`j:num`; `i:num`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN ASM_REWRITE_TAC[]]);;

let moi_s4x_rimarcs = new_definition
 `moi_s4x_rimarcs (V:num->real^3->bool) (R:num->num->real^3->bool) (D:num->real^3->bool)
                  (C:num->num->real^3->bool) (C':num->num->real^3->bool) <=>
   !i j k l.
     i < 4 /\ j < 4 /\ k < 4 /\ l < 4 /\
     ~(i = j) /\ ~(i = k) /\ ~(i = l) /\ ~(j = k) /\ ~(j = l) /\ ~(k = l)
     ==> C j i = C i j /\ C' j i = C' i j /\
         pl_cell_with_boundary 1 (C i j)
           ((D k INTER V i INTER V j) UNION (D l INTER V i INTER V j)) /\
         pl_cell_with_boundary 1 (C' i j)
           ((D k INTER V i INTER V j) UNION (D l INTER V i INTER V j)) /\
         C i j UNION C' i j = R i j /\
         C i j INTER C' i j =
         (D k INTER V i INTER V j) UNION (D l INTER V i INTER V j)`;;

let MOI_S4X_RIMARCS_EX = prove
 (`!V R D J. moi_s4x_tconf V R D J ==> ?C C'. moi_s4x_rimarcs V R D C C'`,
  REWRITE_TAC[moi_s4x_rimarcs; MOI_S4X_RIMARCS]);;

(* The two hexagons at the vertex i (neighbours j, k, l). *)

let MOI_S4X_VERTEX = prove
 (`!V R D J C C' i j k l.
     moi_s4x_tconf V R D J /\ moi_s4x_rimarcs V R D C C' /\
     i < 4 /\ j < 4 /\ k < 4 /\ l < 4 /\
     ~(i = j) /\ ~(i = k) /\ ~(i = l) /\ ~(j = k) /\ ~(j = l) /\ ~(k = l)
     ==> ?p q.
           pl_cell_with_boundary 2 p
             ((D l INTER V i) UNION (D j INTER V i) UNION (D k INTER V i) UNION
              (p INTER V j) UNION (p INTER V k) UNION (p INTER V l)) /\
           pl_cell_with_boundary 2 q
             ((D l INTER V i) UNION (D j INTER V i) UNION (D k INTER V i) UNION
              (q INTER V j) UNION (q INTER V k) UNION (q INTER V l)) /\
           p UNION q UNION (V i INTER V j) UNION (V i INTER V k) UNION (V i INTER V l) =
           frontier(V i) /\
           p INTER q = (D l INTER V i) UNION (D j INTER V i) UNION (D k INTER V i) /\
           ((p INTER V j = C i j /\ q INTER V j = C' i j) \/
            (p INTER V j = C' i j /\ q INTER V j = C i j)) /\
           ((p INTER V k = C i k /\ q INTER V k = C' i k) \/
            (p INTER V k = C' i k /\ q INTER V k = C i k)) /\
           ((p INTER V l = C i l /\ q INTER V l = C' i l) \/
            (p INTER V l = C' i l /\ q INTER V l = C i l))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "ra") STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM(CONJUNCTS_THEN2 (LABEL_TAC "b1") (CONJUNCTS_THEN2 (LABEL_TAC "b2")
    (CONJUNCTS_THEN2 (LABEL_TAC "b3") (LABEL_TAC "b4"))) o MATCH_MP MOI_S4X_TC_BASIC) THEN
  UNDISCH_TAC `moi_s4x_tconf V R D (J:num->real^3->bool)` THEN MOI_S4X_TC_TAC THEN
  (* the six face points *)
  USE_THEN "fpt" (MP_TAC o SPECL [`l:num`; `i:num`; `j:num`; `k:num`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `x1:real^3`) (LABEL_TAC "a12")) THEN
  USE_THEN "fpt" (MP_TAC o SPECL [`l:num`; `i:num`; `k:num`; `j:num`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `y2:real^3` o CONJUNCT1) THEN
  USE_THEN "fpt" (MP_TAC o SPECL [`j:num`; `i:num`; `k:num`; `l:num`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `x2:real^3`) (LABEL_TAC "a23")) THEN
  USE_THEN "fpt" (MP_TAC o SPECL [`j:num`; `i:num`; `l:num`; `k:num`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `y3:real^3` o CONJUNCT1) THEN
  USE_THEN "fpt" (MP_TAC o SPECL [`k:num`; `i:num`; `l:num`; `j:num`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `x3:real^3`) (LABEL_TAC "a31")) THEN
  USE_THEN "fpt" (MP_TAC o SPECL [`k:num`; `i:num`; `j:num`; `l:num`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `y1:real^3` o CONJUNCT1) THEN
  (* facts about the sphere and the three splitting disks *)
  SUBGOAL_THEN `pl_sphere 2 (frontier((V:num->real^3->bool) i)) /\
                closed(frontier((V:num->real^3->bool) i)) /\
                frontier(V i) SUBSET V i`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "ball" (MP_TAC o SPEC `i:num`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP MOI_S4X_BALL) THEN
    ASM_REWRITE_TAC[FRONTIER_CLOSED];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!m. m < 4 /\ ~(m = i)
        ==> pl_cell_with_boundary 2 ((V:num->real^3->bool) i INTER V m) (R i m) /\
            V i INTER V m SUBSET frontier(V i)`
  (LABEL_TAC "em") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN USE_THEN "edge" (MP_TAC o SPECL [`i:num`; `m:num`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(V:num->real^3->bool) i INTER V j INTER V k = {} /\
                V i INTER V j INTER V l = {} /\ V i INTER V k INTER V l = {}`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN USE_THEN "three" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(D:num->real^3->bool) l INTER (V:num->real^3->bool) l = {} /\ D j INTER V j = {} /\
                D k INTER V k = {}`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [USE_THEN "face" (MP_TAC o SPEC `l:num`); USE_THEN "face" (MP_TAC o SPEC `j:num`);
      USE_THEN "face" (MP_TAC o SPEC `k:num`)] THEN
    ANTS_TAC THEN ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `DISJOINT ((D:num->real^3->bool) l) (D j) /\ DISJOINT (D l) (D k) /\
                DISJOINT (D j) (D k)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN USE_THEN "fdisj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(D:num->real^3->bool) l INTER (V:num->real^3->bool) i SUBSET frontier(V i) /\
                D j INTER V i SUBSET frontier(V i) /\ D k INTER V i SUBSET frontier(V i)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN USE_THEN "b3" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `pl_cell_with_boundary 1 ((D:num->real^3->bool) l INTER (V:num->real^3->bool) i)
      {x1:real^3,y2} /\
    pl_cell_with_boundary 1 (D j INTER V i) {x2:real^3,y3} /\
    pl_cell_with_boundary 1 (D k INTER V i) {x3:real^3,y1}`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY (fun s -> USE_THEN s MP_TAC) ["a12"; "a23"; "a31"] THEN
    REWRITE_TAC[ASSUME `(D:num->real^3->bool) l INTER (V:num->real^3->bool) i INTER V j = {x1:real^3}`;
      ASSUME `(D:num->real^3->bool) l INTER (V:num->real^3->bool) i INTER V k = {y2:real^3}`;
      ASSUME `(D:num->real^3->bool) j INTER (V:num->real^3->bool) i INTER V k = {x2:real^3}`;
      ASSUME `(D:num->real^3->bool) j INTER (V:num->real^3->bool) i INTER V l = {y3:real^3}`;
      ASSUME `(D:num->real^3->bool) k INTER (V:num->real^3->bool) i INTER V l = {x3:real^3}`;
      ASSUME `(D:num->real^3->bool) k INTER (V:num->real^3->bool) i INTER V j = {y1:real^3}`] THEN
    REWRITE_TAC[SET_RULE `!a b:real^3. {a} UNION {b} = {a,b}`] THEN SIMP_TAC[];
    ALL_TAC] THEN
  (* the rim arcs *)
  SUBGOAL_THEN
   `pl_cell_with_boundary 1 ((C:num->num->real^3->bool) i j) {x1:real^3,y1} /\
    pl_cell_with_boundary 1 ((C':num->num->real^3->bool) i j) {x1,y1} /\
    C i j UNION C' i j = (R:num->num->real^3->bool) i j /\ C i j INTER C' i j = {x1,y1} /\
    pl_cell_with_boundary 1 (C i k) {x2:real^3,y2} /\
    pl_cell_with_boundary 1 (C' i k) {x2,y2} /\
    C i k UNION C' i k = R i k /\ C i k INTER C' i k = {x2,y2} /\
    pl_cell_with_boundary 1 (C i l) {x3:real^3,y3} /\
    pl_cell_with_boundary 1 (C' i l) {x3,y3} /\
    C i l UNION C' i l = R i l /\ C i l INTER C' i l = {x3,y3}`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "ra" (MP_TAC o SPECL [`i:num`; `j:num`; `k:num`; `l:num`] o
      REWRITE_RULE[moi_s4x_rimarcs]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    USE_THEN "ra" (MP_TAC o SPECL [`i:num`; `k:num`; `j:num`; `l:num`] o
      REWRITE_RULE[moi_s4x_rimarcs]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    USE_THEN "ra" (MP_TAC o SPECL [`i:num`; `l:num`; `j:num`; `k:num`] o
      REWRITE_RULE[moi_s4x_rimarcs]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[ASSUME `(D:num->real^3->bool) l INTER (V:num->real^3->bool) i INTER V j = {x1:real^3}`;
      ASSUME `(D:num->real^3->bool) l INTER (V:num->real^3->bool) i INTER V k = {y2:real^3}`;
      ASSUME `(D:num->real^3->bool) j INTER (V:num->real^3->bool) i INTER V k = {x2:real^3}`;
      ASSUME `(D:num->real^3->bool) j INTER (V:num->real^3->bool) i INTER V l = {y3:real^3}`;
      ASSUME `(D:num->real^3->bool) k INTER (V:num->real^3->bool) i INTER V l = {x3:real^3}`;
      ASSUME `(D:num->real^3->bool) k INTER (V:num->real^3->bool) i INTER V j = {y1:real^3}`] THEN
    REWRITE_TAC[SET_RULE `!a b:real^3. {a} UNION {b} = {a,b}`] THEN
    REWRITE_TAC[SET_RULE `{y1:real^3,x1} = {x1,y1} /\ {y3:real^3,x3} = {x3,y3}`] THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  (* the hypotheses of THETA in the exact form *)
  SUBGOAL_THEN
   `DISJOINT ((V:num->real^3->bool) i INTER V j) (V i INTER V k) /\
    DISJOINT ((V:num->real^3->bool) i INTER V j) (V i INTER V l) /\
    DISJOINT ((V:num->real^3->bool) i INTER V k) (V i INTER V l)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`(V:num->real^3->bool) i INTER V j INTER V k = {}`;
      `(V:num->real^3->bool) i INTER V j INTER V l = {}`;
      `(V:num->real^3->bool) i INTER V k INTER V l = {}`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `DISJOINT ((D:num->real^3->bool) l INTER (V:num->real^3->bool) i) (D j INTER V i) /\
    DISJOINT ((D:num->real^3->bool) l INTER (V:num->real^3->bool) i) (D k INTER V i) /\
    DISJOINT ((D:num->real^3->bool) j INTER (V:num->real^3->bool) i) (D k INTER V i)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`DISJOINT ((D:num->real^3->bool) l) (D j)`; `DISJOINT ((D:num->real^3->bool) l) (D k)`;
      `DISJOINT ((D:num->real^3->bool) j) (D k)`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!a b c:real^3->bool. (a INTER b) INTER (b INTER c) = a INTER b INTER c`
  (LABEL_TAC "abc") THENL [SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `((D:num->real^3->bool) l INTER (V:num->real^3->bool) i) INTER (V i INTER V j) = {x1:real^3} /\
    ((D:num->real^3->bool) l INTER (V:num->real^3->bool) i) INTER (V i INTER V k) = {y2:real^3} /\
    ((D:num->real^3->bool) j INTER (V:num->real^3->bool) i) INTER (V i INTER V k) = {x2:real^3} /\
    ((D:num->real^3->bool) j INTER (V:num->real^3->bool) i) INTER (V i INTER V l) = {y3:real^3} /\
    ((D:num->real^3->bool) k INTER (V:num->real^3->bool) i) INTER (V i INTER V l) = {x3:real^3} /\
    ((D:num->real^3->bool) k INTER (V:num->real^3->bool) i) INTER (V i INTER V j) = {y1:real^3}`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "abc" (fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `((D:num->real^3->bool) l INTER (V:num->real^3->bool) i) INTER (V i INTER V l) = {} /\
    ((D:num->real^3->bool) j INTER (V:num->real^3->bool) i) INTER (V i INTER V j) = {} /\
    ((D:num->real^3->bool) k INTER (V:num->real^3->bool) i) INTER (V i INTER V k) = {}`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`(D:num->real^3->bool) l INTER (V:num->real^3->bool) l = {}`;
      `(D:num->real^3->bool) j INTER (V:num->real^3->bool) j = {}`;
      `(D:num->real^3->bool) k INTER (V:num->real^3->bool) k = {}`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  USE_THEN "em" (MP_TAC o SPEC `j:num`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  USE_THEN "em" (MP_TAC o SPEC `k:num`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  USE_THEN "em" (MP_TAC o SPEC `l:num`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL
   [`frontier((V:num->real^3->bool) i)`;
    `(V:num->real^3->bool) i INTER V j`; `(V:num->real^3->bool) i INTER V k`;
    `(V:num->real^3->bool) i INTER V l`;
    `(R:num->num->real^3->bool) i j`; `(R:num->num->real^3->bool) i k`;
    `(R:num->num->real^3->bool) i l`;
    `(C:num->num->real^3->bool) i j`; `(C':num->num->real^3->bool) i j`;
    `(C:num->num->real^3->bool) i k`; `(C':num->num->real^3->bool) i k`;
    `(C:num->num->real^3->bool) i l`; `(C':num->num->real^3->bool) i l`;
    `(D:num->real^3->bool) l INTER (V:num->real^3->bool) i`;
    `(D:num->real^3->bool) j INTER (V:num->real^3->bool) i`;
    `(D:num->real^3->bool) k INTER (V:num->real^3->bool) i`;
    `x1:real^3`; `y1:real^3`; `x2:real^3`; `y2:real^3`; `x3:real^3`; `y3:real^3`]
   MOI_S4X_THETA) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^3->bool` (X_CHOOSE_THEN `q:real^3->bool`
    (X_CHOOSE_THEN `d1:real^3->bool` (X_CHOOSE_THEN `d1':real^3->bool`
    (X_CHOOSE_THEN `d2:real^3->bool` (X_CHOOSE_THEN `d2':real^3->bool`
    (X_CHOOSE_THEN `d3:real^3->bool` (X_CHOOSE_THEN `d3':real^3->bool`
    (fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)))))))))) THEN
  SUBGOAL_THEN `(p:real^3->bool) SUBSET (V:num->real^3->bool) i /\ (q:real^3->bool) SUBSET V i`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`p UNION q UNION ((V:num->real^3->bool) i INTER V j) UNION (V i INTER V k) UNION
       (V i INTER V l) = frontier (V i)`;
      `frontier((V:num->real^3->bool) i) SUBSET V i`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(p:real^3->bool) INTER (V:num->real^3->bool) j = d1 /\ p INTER V k = d2 /\
    p INTER V l = d3 /\ (q:real^3->bool) INTER V j = d1' /\ q INTER V k = d2' /\
    q INTER V l = d3'`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`(p:real^3->bool) SUBSET (V:num->real^3->bool) i`;
      `(q:real^3->bool) SUBSET (V:num->real^3->bool) i`;
      `(p:real^3->bool) INTER ((V:num->real^3->bool) i INTER V j) = d1`;
      `(p:real^3->bool) INTER ((V:num->real^3->bool) i INTER V k) = d2`;
      `(p:real^3->bool) INTER ((V:num->real^3->bool) i INTER V l) = d3`;
      `(q:real^3->bool) INTER ((V:num->real^3->bool) i INTER V j) = d1'`;
      `(q:real^3->bool) INTER ((V:num->real^3->bool) i INTER V k) = d2'`;
      `(q:real^3->bool) INTER ((V:num->real^3->bool) i INTER V l) = d3'`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`p:real^3->bool`; `q:real^3->bool`] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> concl th =
    `(p:real^3->bool) UNION q UNION ((V:num->real^3->bool) i INTER V j) UNION
     (V i INTER V k) UNION (V i INTER V l) = frontier (V i)`)) THEN
  SIMP_TAC[]);;

(* A hexagon pair at the vertex i: the two pieces of the sphere frontier    *)
(* V i cut by the three face arcs, minus the three splitting disks.         *)

let moi_s4x_hex = new_definition
 `moi_s4x_hex (V:num->real^3->bool) (D:num->real^3->bool) (C:num->num->real^3->bool)
              (C':num->num->real^3->bool) (i:num) (p:real^3->bool) (q:real^3->bool) <=>
   pl_cell_with_boundary 2 p
     (UNIONS {D m INTER V i | m | m < 4} UNION
      UNIONS {p INTER V m | m | m < 4 /\ ~(m = i)}) /\
   pl_cell_with_boundary 2 q
     (UNIONS {D m INTER V i | m | m < 4} UNION
      UNIONS {q INTER V m | m | m < 4 /\ ~(m = i)}) /\
   p UNION q UNION UNIONS {V i INTER V m | m | m < 4 /\ ~(m = i)} = frontier (V i) /\
   p INTER q = UNIONS {D m INTER V i | m | m < 4} /\
   (!m. m < 4 /\ ~(m = i)
        ==> (p INTER V m = C i m /\ q INTER V m = C' i m) \/
            (p INTER V m = C' i m /\ q INTER V m = C i m))`;;

let MOI_S4X_HEX_SYM = prove
 (`!V D C C' i p q. moi_s4x_hex V D C C' i p q ==> moi_s4x_hex V D C C' i q p`,
  REWRITE_TAC[moi_s4x_hex] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) &&
      rand(concl th) = `frontier((V:num->real^3->bool) i)`)) THEN
    MATCH_ACCEPT_TAC(SET_RULE `!p q u f:real^3->bool.
      p UNION q UNION u = f ==> q UNION p UNION u = f`);
    ALL_TAC] THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) &&
      lhand(concl th) = `(p:real^3->bool) INTER q`)) THEN
    MATCH_ACCEPT_TAC(SET_RULE `!p q x:real^3->bool. p INTER q = x ==> q INTER p = x`);
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `m:num` o check (fun th -> is_forall(concl th))) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC TAUT);;

(* The index sets of the hexagon definitions for an explicit permutation. *)

let MOI_S4X_UNIONS3 = prove
 (`!i j k l (f:num->real^3->bool).
     i < 4 /\ j < 4 /\ k < 4 /\ l < 4 /\
     ~(i = j) /\ ~(i = k) /\ ~(i = l) /\ ~(j = k) /\ ~(j = l) /\ ~(k = l)
     ==> UNIONS {f m | m | m < 4 /\ ~(m = i)} = f j UNION f k UNION f l /\
         UNIONS {f m | m | m < 4} = f i UNION f j UNION f k UNION f l`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`i:num`; `j:num`; `k:num`; `l:num`] MOI_S4X_PERM) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  REWRITE_TAC[UNIONS_GSPEC] THEN CONJ_TAC THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:real^3` THEN
  REWRITE_TAC[IN_ELIM_THM; IN_UNION] THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

let MOI_S4X_HEX_EXPAND = prove
 (`!V R D J C C' i j k l p q.
     moi_s4x_tconf V R D J /\ moi_s4x_hex V D C C' i p q /\
     i < 4 /\ j < 4 /\ k < 4 /\ l < 4 /\
     ~(i = j) /\ ~(i = k) /\ ~(i = l) /\ ~(j = k) /\ ~(j = l) /\ ~(k = l)
     ==> pl_cell_with_boundary 2 p
           ((D j INTER V i) UNION (D k INTER V i) UNION (D l INTER V i) UNION
            (p INTER V j) UNION (p INTER V k) UNION (p INTER V l)) /\
         pl_cell_with_boundary 2 q
           ((D j INTER V i) UNION (D k INTER V i) UNION (D l INTER V i) UNION
            (q INTER V j) UNION (q INTER V k) UNION (q INTER V l)) /\
         p UNION q UNION (V i INTER V j) UNION (V i INTER V k) UNION (V i INTER V l) =
         frontier (V i) /\
         p INTER q = (D j INTER V i) UNION (D k INTER V i) UNION (D l INTER V i) /\
         ((p INTER V j = C i j /\ q INTER V j = C' i j) \/
          (p INTER V j = C' i j /\ q INTER V j = C i j)) /\
         ((p INTER V k = C i k /\ q INTER V k = C' i k) \/
          (p INTER V k = C' i k /\ q INTER V k = C i k)) /\
         ((p INTER V l = C i l /\ q INTER V l = C' i l) \/
          (p INTER V l = C' i l /\ q INTER V l = C i l))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC)) THEN
  REWRITE_TAC[moi_s4x_hex] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "arcs"))))) THEN
  MOI_S4X_TC_TAC THEN
  SUBGOAL_THEN `(D:num->real^3->bool) i INTER (V:num->real^3->bool) i = {}` ASSUME_TAC THENL
   [USE_THEN "face" (MP_TAC o SPEC `i:num`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(BETA_RULE(ISPECL [`i:num`; `j:num`; `k:num`; `l:num`;
                 `\m. (V:num->real^3->bool) i INTER V m`] MOI_S4X_UNIONS3)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(fun th ->
    RULE_ASSUM_TAC(REWRITE_RULE[CONJUNCT1 th]))] THEN
  MP_TAC(BETA_RULE(ISPECL [`i:num`; `j:num`; `k:num`; `l:num`;
                 `\m. (q:real^3->bool) INTER (V:num->real^3->bool) m`] MOI_S4X_UNIONS3)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(fun th ->
    RULE_ASSUM_TAC(REWRITE_RULE[CONJUNCT1 th]))] THEN
  MP_TAC(BETA_RULE(ISPECL [`i:num`; `j:num`; `k:num`; `l:num`;
                 `\m. (p:real^3->bool) INTER (V:num->real^3->bool) m`] MOI_S4X_UNIONS3)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(fun th ->
    RULE_ASSUM_TAC(REWRITE_RULE[CONJUNCT1 th]))] THEN
  MP_TAC(BETA_RULE(ISPECL [`i:num`; `j:num`; `k:num`; `l:num`;
                 `\m. (D:num->real^3->bool) m INTER (V:num->real^3->bool) i`] MOI_S4X_UNIONS3)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(fun th ->
    RULE_ASSUM_TAC(REWRITE_RULE[CONJUNCT2 th; UNION_EMPTY;
      ASSUME `(D:num->real^3->bool) i INTER (V:num->real^3->bool) i = {}`]))] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[UNION_ASSOC]) THEN
  REWRITE_TAC[UNION_ASSOC] THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN USE_THEN "arcs" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;


let MOI_S4X_OTHER3 = prove
 (`!i. i < 4
       ==> ?j k l. j < 4 /\ k < 4 /\ l < 4 /\ ~(i = j) /\ ~(i = k) /\ ~(i = l) /\
                   ~(j = k) /\ ~(j = l) /\ ~(k = l)`,
  REPEAT STRIP_TAC THEN
  EXISTS_TAC `if i = 0 then 1 else 0` THEN
  EXISTS_TAC `if i <= 1 then 2 else 1` THEN
  EXISTS_TAC `if i = 3 then 2 else 3` THEN
  REPEAT COND_CASES_TAC THEN ASM_ARITH_TAC);;

(* Hexagon pairs exist at every vertex. *)

let MOI_S4X_HEX_EX = prove
 (`!V R D J C C' i.
     moi_s4x_tconf V R D J /\ moi_s4x_rimarcs V R D C C' /\ i < 4
     ==> ?p q. moi_s4x_hex V D C C' i p q`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `j:num` (X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `l:num`
    STRIP_ASSUME_TAC)) o MATCH_MP MOI_S4X_OTHER3) THEN
  MP_TAC(ISPECL [`V:num->real^3->bool`; `R:num->num->real^3->bool`; `D:num->real^3->bool`;
                 `J:num->real^3->bool`; `C:num->num->real^3->bool`;
                 `C':num->num->real^3->bool`; `i:num`; `j:num`; `k:num`; `l:num`]
    MOI_S4X_VERTEX) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^3->bool` (X_CHOOSE_THEN `q:real^3->bool`
    (fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)))) THEN
  MAP_EVERY EXISTS_TAC [`p:real^3->bool`; `q:real^3->bool`] THEN
  SUBGOAL_THEN `(D:num->real^3->bool) i INTER (V:num->real^3->bool) i = {}` ASSUME_TAC THENL
   [UNDISCH_TAC `moi_s4x_tconf V R D (J:num->real^3->bool)` THEN MOI_S4X_TC_TAC THEN
    USE_THEN "face" (MP_TAC o SPEC `i:num`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[moi_s4x_hex] THEN
  MP_TAC(BETA_RULE(ISPECL [`i:num`; `j:num`; `k:num`; `l:num`;
                 `\m. (V:num->real^3->bool) i INTER V m`] MOI_S4X_UNIONS3)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT1 th])] THEN
  MP_TAC(BETA_RULE(ISPECL [`i:num`; `j:num`; `k:num`; `l:num`;
                 `\m. (q:real^3->bool) INTER (V:num->real^3->bool) m`] MOI_S4X_UNIONS3)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT1 th])] THEN
  MP_TAC(BETA_RULE(ISPECL [`i:num`; `j:num`; `k:num`; `l:num`;
                 `\m. (p:real^3->bool) INTER (V:num->real^3->bool) m`] MOI_S4X_UNIONS3)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT1 th])] THEN
  MP_TAC(BETA_RULE(ISPECL [`i:num`; `j:num`; `k:num`; `l:num`;
                 `\m. (D:num->real^3->bool) m INTER (V:num->real^3->bool) i`] MOI_S4X_UNIONS3)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT2 th])] THEN
  ASM_REWRITE_TAC[UNION_EMPTY] THEN
  SUBGOAL_THEN
   `!x:real^3->bool. (D:num->real^3->bool) j INTER (V:num->real^3->bool) i UNION
                     D k INTER V i UNION D l INTER V i UNION x =
                     D l INTER V i UNION D j INTER V i UNION D k INTER V i UNION x`
  (fun th -> REWRITE_TAC[th]) THENL [SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(D:num->real^3->bool) j INTER (V:num->real^3->bool) i UNION
    D k INTER V i UNION D l INTER V i =
    D l INTER V i UNION D j INTER V i UNION D k INTER V i`
  (fun th -> REWRITE_TAC[th]) THENL [SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[UNION_ASSOC] THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `m:num` THEN STRIP_TAC THEN
  MP_TAC(SPECL [`i:num`; `j:num`; `k:num`; `l:num`] MOI_S4X_PERM) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(MP_TAC o SPEC `m:num`)] THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[]);;


(* ------------------------------------------------------------------------- *)
(* The two-two split.  For a permutation a, b, c, d of the                  *)
(* indices, A = V a UNION V c and B = V b UNION V d.  Two hexagons at a and *)
(* c sharing their rim arc on V a INTER V c glue to a disk; the four face   *)
(* disks attach to it along their arcs in A; the result Z is a disk whose   *)
(* boundary is Z INTER B.                                                   *)
(* ------------------------------------------------------------------------- *)

(* Attaching a disk d along the arc d INTER a of the free boundary part f. *)

let MOI_S4X_ATTACH = prove
 (`!y f d j a b (e1:real^3) e2.
     pl_cell_with_boundary 2 y ((y INTER b) UNION f) /\
     pl_cell_with_boundary 2 d j /\ j = (d INTER a) UNION (d INTER b) /\
     pl_cell_with_boundary 1 (d INTER a) {e1,e2} /\ d INTER a INTER b = {e1,e2} /\
     y INTER d = d INTER a /\ d INTER a SUBSET f
     ==> pl_cell_with_boundary 2 (y UNION d)
           (((y UNION d) INTER b) UNION (f DIFF ((d INTER a) DIFF {e1,e2})))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`y:real^3->bool`; `(y INTER b) UNION f:real^3->bool`; `d:real^3->bool`;
                 `j:real^3->bool`; `d INTER a:real^3->bool`; `e1:real^3`; `e2:real^3`]
    MOI_S4X_DISK_GLUE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[DIMINDEX_3; ARITH] THEN
    UNDISCH_TAC `d INTER a SUBSET (f:real^3->bool)` THEN
    UNDISCH_TAC `j = (d INTER a) UNION (d INTER b:real^3->bool)` THEN SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  MAP_EVERY UNDISCH_TAC
   [`j = (d INTER a) UNION (d INTER b:real^3->bool)`;
    `d INTER a INTER b = {e1:real^3,e2}`; `y INTER d = d INTER (a:real^3->bool)`] THEN
  SET_TAC[]);;

(* Hexagons lie in the frontier of their ball. *)

let MOI_S4X_HEX_SUBSET = prove
 (`!V R D J C C' i p q.
     moi_s4x_tconf V R D J /\ moi_s4x_hex V D C C' i p q /\ i < 4
     ==> p SUBSET frontier(V i) /\ q SUBSET frontier(V i) /\ p SUBSET V i /\ q SUBSET V i`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s4x_hex; moi_s4x_tconf] THEN STRIP_TAC THEN
  SUBGOAL_THEN `frontier((V:num->real^3->bool) i) SUBSET V i` ASSUME_TAC THENL
   [MATCH_MP_TAC FRONTIER_SUBSET_CLOSED THEN ASM_MESON_TAC[MOI_S4X_BALL]; ALL_TAC] THEN
  UNDISCH_TAC `frontier((V:num->real^3->bool) i) SUBSET V i` THEN
  UNDISCH_TAC `p UNION q UNION UNIONS {(V:num->real^3->bool) i INTER V m | m |
                                      m < 4 /\ ~(m = i)} = frontier (V i)` THEN
  SET_TAC[]);;

(* Two hexagons at a and c sharing their rim arc on V a INTER V c. *)

let MOI_S4X_XGLUE = prove
 (`!V R D J C C' a b c d sa sa' sc sc'.
     moi_s4x_tconf V R D J /\ moi_s4x_rimarcs V R D C C' /\
     moi_s4x_hex V D C C' a sa sa' /\ moi_s4x_hex V D C C' c sc sc' /\
     a < 4 /\ b < 4 /\ c < 4 /\ d < 4 /\
     ~(a = b) /\ ~(a = c) /\ ~(a = d) /\ ~(b = c) /\ ~(b = d) /\ ~(c = d) /\
     sa INTER V c = sc INTER V a
     ==> pl_cell_with_boundary 2 (sa UNION sc)
           (((sa UNION sc) INTER (V b UNION V d)) UNION
            ((D a INTER (V a UNION V c)) UNION (D b INTER (V a UNION V c)) UNION
             (D c INTER (V a UNION V c)) UNION (D d INTER (V a UNION V c))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o
    MATCH_MP (SET_RULE `!x y:real^3->bool. x = y ==> x SUBSET y /\ y SUBSET x`) o
    check (fun th -> concl th = `(sa:real^3->bool) INTER (V:num->real^3->bool) c = sc INTER V a`)) THEN
  MP_TAC(ISPECL [`V:num->real^3->bool`; `R:num->num->real^3->bool`; `D:num->real^3->bool`;
                 `J:num->real^3->bool`; `C:num->num->real^3->bool`;
                 `C':num->num->real^3->bool`; `a:num`; `b:num`; `c:num`; `d:num`;
                 `sa:real^3->bool`; `sa':real^3->bool`] MOI_S4X_HEX_EXPAND) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th))] THEN
  MP_TAC(ISPECL [`V:num->real^3->bool`; `R:num->num->real^3->bool`; `D:num->real^3->bool`;
                 `J:num->real^3->bool`; `C:num->num->real^3->bool`;
                 `C':num->num->real^3->bool`; `c:num`; `a:num`; `b:num`; `d:num`;
                 `sc:real^3->bool`; `sc':real^3->bool`] MOI_S4X_HEX_EXPAND) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th))] THEN
  MP_TAC(ISPECL [`V:num->real^3->bool`; `R:num->num->real^3->bool`; `D:num->real^3->bool`;
                 `J:num->real^3->bool`; `C:num->num->real^3->bool`;
                 `C':num->num->real^3->bool`; `a:num`;
                 `sa:real^3->bool`; `sa':real^3->bool`] MOI_S4X_HEX_SUBSET) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`V:num->real^3->bool`; `R:num->num->real^3->bool`; `D:num->real^3->bool`;
                 `J:num->real^3->bool`; `C:num->num->real^3->bool`;
                 `C':num->num->real^3->bool`; `c:num`;
                 `sc:real^3->bool`; `sc':real^3->bool`] MOI_S4X_HEX_SUBSET) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  UNDISCH_TAC `moi_s4x_rimarcs V (R:num->num->real^3->bool) (D:num->real^3->bool) (C:num->num->real^3->bool) (C':num->num->real^3->bool)` THEN
  REWRITE_TAC[moi_s4x_rimarcs] THEN
  DISCH_THEN(MP_TAC o SPECL [`a:num`; `c:num`; `b:num`; `d:num`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  UNDISCH_TAC `moi_s4x_tconf V (R:num->num->real^3->bool) (D:num->real^3->bool) (J:num->real^3->bool)` THEN MOI_S4X_TC_TAC THEN
  USE_THEN "fpt" (MP_TAC o SPECL [`b:num`; `a:num`; `c:num`; `d:num`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `u:real^3` o CONJUNCT1) THEN
  USE_THEN "fpt" (MP_TAC o SPECL [`d:num`; `a:num`; `c:num`; `b:num`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `v:real^3` o CONJUNCT1) THEN
  SUBGOAL_THEN `pl_cell_with_boundary 1 (sa INTER (V:num->real^3->bool) c) {u:real^3,v}` ASSUME_TAC THENL
   [SUBGOAL_THEN `{u:real^3,v} = ((D:num->real^3->bool) b INTER (V:num->real^3->bool) a INTER V c) UNION (D d INTER V a INTER V c)`
    SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN SET_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(DISJ_CASES_THEN (CONJUNCTS_THEN2 SUBST1_TAC (K ALL_TAC)) o check (fun th ->
      is_disj(concl th) && can (find_term ((=) `(sa:real^3->bool) INTER (V:num->real^3->bool) c`)) (concl th))) THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(sa:real^3->bool) INTER sc = (sa INTER (V:num->real^3->bool) c)` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`(sa:real^3->bool) INTER (V:num->real^3->bool) c SUBSET sc INTER V a`; `(sc:real^3->bool) INTER (V:num->real^3->bool) a SUBSET sa INTER V c`;
      `(sa:real^3->bool) SUBSET (V:num->real^3->bool) a`; `(sc:real^3->bool) SUBSET (V:num->real^3->bool) c`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`sa:real^3->bool`;
    `(D:num->real^3->bool) b INTER V a UNION D c INTER V a UNION D d INTER V a UNION
     sa INTER V b UNION sa INTER (V:num->real^3->bool) c UNION sa INTER V d`;
    `sc:real^3->bool`;
    `(D:num->real^3->bool) a INTER V c UNION D b INTER V c UNION D d INTER V c UNION
     sc INTER V a UNION sc INTER (V:num->real^3->bool) b UNION sc INTER V d`;
    `(sa INTER (V:num->real^3->bool) c):real^3->bool`; `u:real^3`; `v:real^3`] MOI_S4X_DISK_GLUE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[DIMINDEX_3; ARITH] THEN
    MAP_EVERY UNDISCH_TAC
     [`(sa:real^3->bool) INTER (V:num->real^3->bool) c SUBSET sc INTER V a`; `(sc:real^3->bool) INTER (V:num->real^3->bool) a SUBSET sa INTER V c`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  SUBGOAL_THEN `(sa INTER (V:num->real^3->bool) c) INTER ((V:num->real^3->bool) b UNION V d) = {}` ASSUME_TAC THENL
   [SUBGOAL_THEN `(V:num->real^3->bool) a INTER V c INTER V b = {} /\
                  V a INTER V c INTER V d = {}` MP_TAC THENL
     [CONJ_TAC THEN USE_THEN "three" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MAP_EVERY UNDISCH_TAC
     [`(sa:real^3->bool) SUBSET (V:num->real^3->bool) a`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(D:num->real^3->bool) a INTER (V:num->real^3->bool) a = {} /\ D c INTER V c = {}`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [USE_THEN "face" (MP_TAC o SPEC `a:num`); USE_THEN "face" (MP_TAC o SPEC `c:num`)] THEN
    ANTS_TAC THEN ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((D:num->real^3->bool) b INTER (V:num->real^3->bool) a UNION D c INTER V a UNION D d INTER V a UNION
     D a INTER V c UNION D b INTER V c UNION D d INTER V c) INTER (sa INTER (V:num->real^3->bool) c) SUBSET {u:real^3,v} /\
    u IN D b INTER V a /\ v IN D d INTER V a`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`(sa:real^3->bool) SUBSET (V:num->real^3->bool) a`;
      `(D:num->real^3->bool) b INTER (V:num->real^3->bool) a INTER V c = {u:real^3}`;
      `(D:num->real^3->bool) d INTER (V:num->real^3->bool) a INTER V c = {v:real^3}`;
      `(D:num->real^3->bool) a INTER (V:num->real^3->bool) a = {}`; `(D:num->real^3->bool) c INTER (V:num->real^3->bool) c = {}`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  MAP_EVERY UNDISCH_TAC
   [`(sa INTER (V:num->real^3->bool) c) INTER ((V:num->real^3->bool) b UNION V d) = {}`;
    `((D:num->real^3->bool) b INTER (V:num->real^3->bool) a UNION D c INTER V a UNION D d INTER V a UNION
      D a INTER V c UNION D b INTER V c UNION D d INTER V c) INTER (sa INTER (V:num->real^3->bool) c) SUBSET {u:real^3,v}`;
    `(u:real^3) IN (D:num->real^3->bool) b INTER (V:num->real^3->bool) a`; `(v:real^3) IN (D:num->real^3->bool) d INTER (V:num->real^3->bool) a`;
    `(D:num->real^3->bool) a INTER (V:num->real^3->bool) a = {}`; `(D:num->real^3->bool) c INTER (V:num->real^3->bool) c = {}`;
    `(sa:real^3->bool) INTER (V:num->real^3->bool) c SUBSET sc INTER V a`; `(sc:real^3->bool) INTER (V:num->real^3->bool) a SUBSET sa INTER V c`] THEN
  SET_TAC[]);;

(* A face disk meeting A in two face arcs (the face opposite b). *)

let MOI_S4X_FACE2 = prove
 (`!V R D J a b c d.
     moi_s4x_tconf V R D J /\
     a < 4 /\ b < 4 /\ c < 4 /\ d < 4 /\
     ~(a = b) /\ ~(a = c) /\ ~(a = d) /\ ~(b = c) /\ ~(b = d) /\ ~(c = d)
     ==> ?e1 e2. pl_cell_with_boundary 1 (D b INTER (V a UNION V c)) {e1,e2} /\
                 D b INTER (V a UNION V c) INTER (V b UNION V d) = {e1,e2}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `moi_s4x_tconf V (R:num->num->real^3->bool) (D:num->real^3->bool) (J:num->real^3->bool)` THEN MOI_S4X_TC_TAC THEN
  USE_THEN "fpt" (MP_TAC o SPECL [`b:num`; `a:num`; `c:num`; `d:num`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `u:real^3`) (LABEL_TAC "arca")) THEN
  USE_THEN "fpt" (MP_TAC o SPECL [`b:num`; `a:num`; `d:num`; `c:num`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `w1:real^3` o CONJUNCT1) THEN
  USE_THEN "fpt" (MP_TAC o SPECL [`b:num`; `c:num`; `a:num`; `d:num`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(LABEL_TAC "arcc" o CONJUNCT2) THEN
  USE_THEN "fpt" (MP_TAC o SPECL [`b:num`; `c:num`; `d:num`; `a:num`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `w2:real^3` o CONJUNCT1) THEN
  SUBGOAL_THEN `(D:num->real^3->bool) b INTER (V:num->real^3->bool) b = {}` ASSUME_TAC THENL
   [USE_THEN "face" (MP_TAC o SPEC `b:num`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(D:num->real^3->bool) b INTER (V:num->real^3->bool) c INTER V a = {u:real^3}`
  ASSUME_TAC THENL
   [UNDISCH_TAC `(D:num->real^3->bool) b INTER (V:num->real^3->bool) a INTER V c = {u:real^3}` THEN
    SET_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`w1:real^3`; `w2:real^3`] THEN CONJ_TAC THENL
   [SUBGOAL_THEN `(D:num->real^3->bool) b INTER ((V:num->real^3->bool) a UNION V c) =
                  (D b INTER V a) UNION (D b INTER V c)` SUBST1_TAC THENL
     [SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC MOI_S4X_ARC_UNION THEN EXISTS_TAC `u:real^3` THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MOI_S4X_CELL1_SYM THEN USE_THEN "arca" MP_TAC THEN
      REWRITE_TAC[ASSUME `(D:num->real^3->bool) b INTER (V:num->real^3->bool) a INTER V c = {u:real^3}`;
                  ASSUME `(D:num->real^3->bool) b INTER (V:num->real^3->bool) a INTER V d = {w1:real^3}`] THEN
      MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN SET_TAC[];
      USE_THEN "arcc" MP_TAC THEN
      REWRITE_TAC[ASSUME `(D:num->real^3->bool) b INTER (V:num->real^3->bool) c INTER V a = {u:real^3}`;
                  ASSUME `(D:num->real^3->bool) b INTER (V:num->real^3->bool) c INTER V d = {w2:real^3}`] THEN
      MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN SET_TAC[];
      UNDISCH_TAC `(D:num->real^3->bool) b INTER (V:num->real^3->bool) a INTER V c = {u:real^3}` THEN
      SET_TAC[]];
    MAP_EVERY UNDISCH_TAC
     [`(D:num->real^3->bool) b INTER (V:num->real^3->bool) b = {}`;
      `(D:num->real^3->bool) b INTER (V:num->real^3->bool) a INTER V d = {w1:real^3}`;
      `(D:num->real^3->bool) b INTER (V:num->real^3->bool) c INTER V d = {w2:real^3}`] THEN
    SET_TAC[]]);;

(* A face disk meeting A in one face arc (the face opposite a). *)

let MOI_S4X_FACE1 = prove
 (`!V R D J a b c d.
     moi_s4x_tconf V R D J /\
     a < 4 /\ b < 4 /\ c < 4 /\ d < 4 /\
     ~(a = b) /\ ~(a = c) /\ ~(a = d) /\ ~(b = c) /\ ~(b = d) /\ ~(c = d)
     ==> ?e1 e2. pl_cell_with_boundary 1 (D a INTER (V a UNION V c)) {e1,e2} /\
                 D a INTER (V a UNION V c) INTER (V b UNION V d) = {e1,e2}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `moi_s4x_tconf V (R:num->num->real^3->bool) (D:num->real^3->bool) (J:num->real^3->bool)` THEN MOI_S4X_TC_TAC THEN
  USE_THEN "fpt" (MP_TAC o SPECL [`a:num`; `c:num`; `b:num`; `d:num`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `w1:real^3`) (LABEL_TAC "arcc")) THEN
  USE_THEN "fpt" (MP_TAC o SPECL [`a:num`; `c:num`; `d:num`; `b:num`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `w2:real^3` o CONJUNCT1) THEN
  SUBGOAL_THEN `(D:num->real^3->bool) a INTER (V:num->real^3->bool) a = {}` ASSUME_TAC THENL
   [USE_THEN "face" (MP_TAC o SPEC `a:num`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(D:num->real^3->bool) a INTER ((V:num->real^3->bool) a UNION V c) = D a INTER V c` SUBST1_TAC THENL
   [UNDISCH_TAC `(D:num->real^3->bool) a INTER (V:num->real^3->bool) a = {}` THEN SET_TAC[]; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`w1:real^3`; `w2:real^3`] THEN CONJ_TAC THENL
   [USE_THEN "arcc" MP_TAC THEN
    REWRITE_TAC[ASSUME `(D:num->real^3->bool) a INTER (V:num->real^3->bool) c INTER V b = {w1:real^3}`;
                ASSUME `(D:num->real^3->bool) a INTER (V:num->real^3->bool) c INTER V d = {w2:real^3}`] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN SET_TAC[];
    MAP_EVERY UNDISCH_TAC
     [`(D:num->real^3->bool) a INTER (V:num->real^3->bool) a = {}`;
      `(D:num->real^3->bool) a INTER (V:num->real^3->bool) c INTER V b = {w1:real^3}`;
      `(D:num->real^3->bool) a INTER (V:num->real^3->bool) c INTER V d = {w2:real^3}`] THEN
    SET_TAC[]]);;

let SPDR9_ZDISK_SET = prove
 (`!Da Db Dc Dd aa bb sa sc e f g h:real^3->bool.
     Dc INTER aa INTER bb = h ==> Da INTER aa INTER bb = g ==>
     Dd INTER aa INTER bb = f ==> Db INTER aa INTER bb = e ==>
     (Da INTER aa UNION Db INTER aa UNION Dc INTER aa UNION Dd INTER aa) DIFF
     (Db INTER aa DIFF e) DIFF (Dd INTER aa DIFF f) DIFF (Da INTER aa DIFF g) DIFF
     (Dc INTER aa DIFF h) SUBSET
     (sa UNION sc UNION Da UNION Db UNION Dc UNION Dd) INTER bb`,
  REPEAT GEN_TAC THEN REWRITE_TAC[SUBSET; EXTENSION; IN_INTER; IN_UNION; IN_DIFF] THEN
  REPEAT DISCH_TAC THEN X_GEN_TAC `y:real^3` THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `y:real^3`)) THEN CONV_TAC TAUT);;

(* The disk Z of the two-two split. *)

let MOI_S4X_ZDISK = prove
 (`!V R D J C C' a b c d sa sa' sc sc'.
     moi_s4x_tconf V R D J /\ moi_s4x_rimarcs V R D C C' /\
     moi_s4x_hex V D C C' a sa sa' /\ moi_s4x_hex V D C C' c sc sc' /\
     a < 4 /\ b < 4 /\ c < 4 /\ d < 4 /\
     ~(a = b) /\ ~(a = c) /\ ~(a = d) /\ ~(b = c) /\ ~(b = d) /\ ~(c = d) /\
     sa INTER V c = sc INTER V a
     ==> pl_cell_with_boundary 2 (sa UNION sc UNION D a UNION D b UNION D c UNION D d)
           ((sa UNION sc UNION D a UNION D b UNION D c UNION D d) INTER (V b UNION V d))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `aa = (V:num->real^3->bool) a UNION V c` THEN
  ABBREV_TAC `bb = (V:num->real^3->bool) b UNION V d` THEN
  ABBREV_TAC `f0 = (D:num->real^3->bool) a INTER aa UNION D b INTER aa UNION
                   D c INTER aa UNION D d INTER aa` THEN
  MP_TAC(ISPECL [`V:num->real^3->bool`; `R:num->num->real^3->bool`; `D:num->real^3->bool`;
                 `J:num->real^3->bool`; `C:num->num->real^3->bool`;
                 `C':num->num->real^3->bool`; `a:num`; `b:num`; `c:num`; `d:num`;
                 `sa:real^3->bool`; `sa':real^3->bool`; `sc:real^3->bool`; `sc':real^3->bool`]
    MOI_S4X_XGLUE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[] THEN DISCH_TAC] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o
    MATCH_MP (SET_RULE `!x y:real^3->bool. x = y ==> x SUBSET y /\ y SUBSET x`) o
    check (fun th -> concl th = `(sa:real^3->bool) INTER (V:num->real^3->bool) c = sc INTER V a`)) THEN
  (* facts on the face disks *)
  SUBGOAL_THEN
   `!m. m < 4 ==> (J:num->real^3->bool) m = (D m INTER aa) UNION (D m INTER bb) /\
                  pl_cell_with_boundary 2 ((D:num->real^3->bool) m) (J m)`
  (LABEL_TAC "jm") THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN
    UNDISCH_TAC `moi_s4x_tconf V (R:num->num->real^3->bool) (D:num->real^3->bool) (J:num->real^3->bool)` THEN MOI_S4X_TC_TAC THEN
    USE_THEN "face" (MP_TAC o SPEC `m:num`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`a:num`; `b:num`; `c:num`; `d:num`;
                   `\i. (D:num->real^3->bool) m INTER (V:num->real^3->bool) i`]
      MOI_S4X_UNIONS3) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o CONJUNCT2 o BETA_RULE) THEN
    MAP_EVERY EXPAND_TAC ["aa"; "bb"] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(D:num->real^3->bool) a INTER D b = {} /\ D a INTER D c = {} /\
                D a INTER D d = {} /\ D b INTER D c = {} /\ D b INTER D d = {} /\
                D c INTER D d = {}`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `moi_s4x_tconf V (R:num->num->real^3->bool) (D:num->real^3->bool) (J:num->real^3->bool)` THEN MOI_S4X_TC_TAC THEN
    REWRITE_TAC[GSYM DISJOINT] THEN REPEAT CONJ_TAC THEN
    USE_THEN "fdisj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!m. m < 4 ==> (sa UNION sc) INTER (D:num->real^3->bool) m = D m INTER aa`
  (LABEL_TAC "xd") THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`V:num->real^3->bool`; `R:num->num->real^3->bool`; `D:num->real^3->bool`;
                   `J:num->real^3->bool`; `C:num->num->real^3->bool`;
                   `C':num->num->real^3->bool`; `a:num`;
                   `sa:real^3->bool`; `sa':real^3->bool`] MOI_S4X_HEX_SUBSET) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    MP_TAC(ISPECL [`V:num->real^3->bool`; `R:num->num->real^3->bool`; `D:num->real^3->bool`;
                   `J:num->real^3->bool`; `C:num->num->real^3->bool`;
                   `C':num->num->real^3->bool`; `c:num`;
                   `sc:real^3->bool`; `sc':real^3->bool`] MOI_S4X_HEX_SUBSET) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    SUBGOAL_THEN `(D:num->real^3->bool) m INTER (V:num->real^3->bool) a SUBSET sa /\ D m INTER V c SUBSET sc`
    MP_TAC THENL
     [UNDISCH_TAC `moi_s4x_hex V (D:num->real^3->bool) (C:num->num->real^3->bool) (C':num->num->real^3->bool) a sa (sa':real^3->bool)` THEN
      UNDISCH_TAC `moi_s4x_hex V (D:num->real^3->bool) (C:num->num->real^3->bool) (C':num->num->real^3->bool) c sc (sc':real^3->bool)` THEN
      REWRITE_TAC[moi_s4x_hex] THEN
      DISCH_THEN(MP_TAC o MATCH_MP MOI_S4L_PL_CELL_FACTS o CONJUNCT1) THEN STRIP_TAC THEN
      DISCH_THEN(MP_TAC o MATCH_MP MOI_S4L_PL_CELL_FACTS o CONJUNCT1) THEN STRIP_TAC THEN
      REWRITE_TAC[UNIONS_GSPEC] THEN ASM SET_TAC[];
      EXPAND_TAC "aa" THEN
      UNDISCH_TAC `(sa:real^3->bool) SUBSET (V:num->real^3->bool) a` THEN
      UNDISCH_TAC `(sc:real^3->bool) SUBSET (V:num->real^3->bool) c` THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(V:num->real^3->bool) d UNION V b = bb /\ V c UNION V a = aa`
  STRIP_ASSUME_TAC THENL [MAP_EVERY EXPAND_TAC ["aa"; "bb"] THEN SET_TAC[]; ALL_TAC] THEN
  (* the arcs of the four face disks in aa, with ends in bb *)
  MP_TAC(ISPECL [`V:num->real^3->bool`; `R:num->num->real^3->bool`; `D:num->real^3->bool`;
                 `J:num->real^3->bool`; `a:num`; `b:num`; `c:num`; `d:num`] MOI_S4X_FACE2) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]] THEN
  DISCH_THEN(X_CHOOSE_THEN `e1:real^3` (X_CHOOSE_THEN `e2:real^3` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`V:num->real^3->bool`; `R:num->num->real^3->bool`; `D:num->real^3->bool`;
                 `J:num->real^3->bool`; `a:num`; `d:num`; `c:num`; `b:num`] MOI_S4X_FACE2) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]] THEN
  DISCH_THEN(X_CHOOSE_THEN `f1:real^3` (X_CHOOSE_THEN `f2:real^3` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`V:num->real^3->bool`; `R:num->num->real^3->bool`; `D:num->real^3->bool`;
                 `J:num->real^3->bool`; `a:num`; `b:num`; `c:num`; `d:num`] MOI_S4X_FACE1) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]] THEN
  DISCH_THEN(X_CHOOSE_THEN `g1:real^3` (X_CHOOSE_THEN `g2:real^3` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`V:num->real^3->bool`; `R:num->num->real^3->bool`; `D:num->real^3->bool`;
                 `J:num->real^3->bool`; `c:num`; `b:num`; `a:num`; `d:num`] MOI_S4X_FACE1) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]] THEN
  DISCH_THEN(X_CHOOSE_THEN `h1:real^3` (X_CHOOSE_THEN `h2:real^3` STRIP_ASSUME_TAC)) THEN
  (* four attachments *)
  MP_TAC(ISPECL [`sa UNION sc:real^3->bool`; `f0:real^3->bool`; `(D:num->real^3->bool) b`;
                 `(J:num->real^3->bool) b`; `aa:real^3->bool`; `bb:real^3->bool`;
                 `e1:real^3`; `e2:real^3`] MOI_S4X_ATTACH) THEN
  ANTS_TAC THENL
   [USE_THEN "jm" (MP_TAC o SPEC `b:num`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    USE_THEN "xd" (MP_TAC o SPEC `b:num`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "f0" THEN SET_TAC[];
    DISCH_TAC] THEN
  MP_TAC(ISPECL [`(sa UNION sc) UNION (D:num->real^3->bool) b`;
                 `f0 DIFF (((D:num->real^3->bool) b INTER aa) DIFF {e1:real^3,e2})`;
                 `(D:num->real^3->bool) d`;
                 `(J:num->real^3->bool) d`; `aa:real^3->bool`; `bb:real^3->bool`;
                 `f1:real^3`; `f2:real^3`] MOI_S4X_ATTACH) THEN
  ANTS_TAC THENL
   [USE_THEN "jm" (MP_TAC o SPEC `d:num`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    USE_THEN "xd" (MP_TAC o SPEC `d:num`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC
     [`(sa UNION sc) INTER (D:num->real^3->bool) d = D d INTER aa`;
      `(D:num->real^3->bool) b INTER D d = {}`] THEN
    EXPAND_TAC "f0" THEN SET_TAC[];
    DISCH_TAC] THEN
  MP_TAC(ISPECL [`((sa UNION sc) UNION (D:num->real^3->bool) b) UNION D d`;
                 `(f0 DIFF (((D:num->real^3->bool) b INTER aa) DIFF {e1:real^3,e2})) DIFF
                  ((D d INTER aa) DIFF {f1:real^3,f2})`;
                 `(D:num->real^3->bool) a`;
                 `(J:num->real^3->bool) a`; `aa:real^3->bool`; `bb:real^3->bool`;
                 `g1:real^3`; `g2:real^3`] MOI_S4X_ATTACH) THEN
  ANTS_TAC THENL
   [USE_THEN "jm" (MP_TAC o SPEC `a:num`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    USE_THEN "xd" (MP_TAC o SPEC `a:num`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC
     [`(sa UNION sc) INTER (D:num->real^3->bool) a = D a INTER aa`;
      `(D:num->real^3->bool) a INTER D b = {}`; `(D:num->real^3->bool) a INTER D d = {}`] THEN
    EXPAND_TAC "f0" THEN SET_TAC[];
    DISCH_TAC] THEN
  MP_TAC(ISPECL [`(((sa UNION sc) UNION (D:num->real^3->bool) b) UNION D d) UNION D a`;
                 `((f0 DIFF (((D:num->real^3->bool) b INTER aa) DIFF {e1:real^3,e2})) DIFF
                   ((D d INTER aa) DIFF {f1:real^3,f2})) DIFF ((D a INTER aa) DIFF {g1:real^3,g2})`;
                 `(D:num->real^3->bool) c`;
                 `(J:num->real^3->bool) c`; `aa:real^3->bool`; `bb:real^3->bool`;
                 `h1:real^3`; `h2:real^3`] MOI_S4X_ATTACH) THEN
  ANTS_TAC THENL
   [USE_THEN "jm" (MP_TAC o SPEC `c:num`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    USE_THEN "xd" (MP_TAC o SPEC `c:num`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC
     [`(sa UNION sc) INTER (D:num->real^3->bool) c = D c INTER aa`;
      `(D:num->real^3->bool) a INTER D c = {}`; `(D:num->real^3->bool) b INTER D c = {}`;
      `(D:num->real^3->bool) c INTER D d = {}`] THEN
    EXPAND_TAC "f0" THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `((((sa UNION sc) UNION (D:num->real^3->bool) b) UNION D d) UNION D a) UNION D c =
                sa UNION sc UNION D a UNION D b UNION D c UNION D d`
  SUBST1_TAC THENL [SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  MATCH_MP_TAC(SET_RULE `(f:real^3->bool) SUBSET s ==> s UNION f = s`) THEN
  MAP_EVERY UNDISCH_TAC
   [`(D:num->real^3->bool) b INTER aa INTER bb = {e1:real^3,e2}`;
    `(D:num->real^3->bool) d INTER aa INTER bb = {f1:real^3,f2}`;
    `(D:num->real^3->bool) a INTER aa INTER bb = {g1:real^3,g2}`;
    `(D:num->real^3->bool) c INTER aa INTER bb = {h1:real^3,h2}`] THEN
  EXPAND_TAC "f0" THEN MATCH_ACCEPT_TAC SPDR9_ZDISK_SET);;

(* A 1-cell has points other than its two ends. *)

let MOI_S4X_CELL1_MID = prove
 (`!a p q:real^N. pl_cell_with_boundary 1 a {p,q} ==> ?y. y IN a /\ ~(y = p) /\ ~(y = q)`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP MOI_S4X_CELL1_ARC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `h:real^1->real^N` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `(h:real^1->real^N)(lift(&1 / &2))` THEN
  SUBGOAL_THEN `lift(&1 / &2) IN interval[vec 0,vec 1]` ASSUME_TAC THENL
   [REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP; DROP_VEC] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [UNDISCH_TAC `path_image (h:real^1->real^N) = a` THEN
    REWRITE_TAC[path_image] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `arc(h:real^1->real^N)` THEN REWRITE_TAC[arc] THEN
  DISCH_THEN(MP_TAC o CONJUNCT2) THEN
  MAP_EVERY UNDISCH_TAC
   [`pathstart (h:real^1->real^N) = p`; `pathfinish (h:real^1->real^N) = q`] THEN
  REWRITE_TAC[pathstart; pathfinish] THEN REPEAT DISCH_TAC THEN
  CONJ_TAC THEN DISCH_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`lift(&1 / &2)`; `vec 0:real^1`]);
    FIRST_X_ASSUM(MP_TAC o SPECL [`lift(&1 / &2)`; `vec 1:real^1`])] THEN
  ASM_REWRITE_TAC[ENDS_IN_UNIT_INTERVAL; GSYM DROP_EQ; LIFT_DROP; DROP_VEC] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV);;

let SPDR9_SIG_SET = prove
 (`!Fb Fd R Va Vb Vc Vd sb sb' sd sd':real^3->bool.
     Vb INTER Vd INTER Vc = {} ==> Vb INTER Vd INTER Va = {} ==>
     sd' SUBSET Vd ==> sd SUBSET Vd ==> sb' SUBSET Vb ==> sb SUBSET Vb ==>
     R = sd INTER Vb UNION sd' INTER Vb ==> R = sb INTER Vd UNION sb' INTER Vd ==>
     sd UNION sd' UNION Vd INTER Va UNION Vb INTER Vd UNION Vd INTER Vc = Fd ==>
     sb UNION sb' UNION Vb INTER Va UNION Vb INTER Vc UNION Vb INTER Vd = Fb ==>
     (Fb DIFF Vb INTER Vd UNION R) UNION Fd DIFF Vb INTER Vd UNION R =
     sb UNION sb' UNION Vb INTER Va UNION Vb INTER Vc UNION sd UNION sd' UNION
     Vd INTER Va UNION Vd INTER Vc`,
  REPEAT GEN_TAC THEN REWRITE_TAC[SUBSET; EXTENSION; IN_INTER; IN_UNION; IN_DIFF; NOT_IN_EMPTY] THEN
  REPEAT DISCH_TAC THEN X_GEN_TAC `y:real^3` THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `y:real^3`)) THEN CONV_TAC TAUT);;

(* The sphere of the two balls b and d minus their open splitting disk. *)

let MOI_S4X_SIG = prove
 (`!V R D J C C' a b c d sb sb' sd sd'.
     moi_s4x_tconf V R D J /\ moi_s4x_rimarcs V R D C C' /\
     moi_s4x_hex V D C C' b sb sb' /\ moi_s4x_hex V D C C' d sd sd' /\
     a < 4 /\ b < 4 /\ c < 4 /\ d < 4 /\
     ~(a = b) /\ ~(a = c) /\ ~(a = d) /\ ~(b = c) /\ ~(b = d) /\ ~(c = d)
     ==> pl_sphere 2 (sb UNION sb' UNION (V b INTER V a) UNION (V b INTER V c) UNION
                      sd UNION sd' UNION (V d INTER V a) UNION (V d INTER V c))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:num->real^3->bool`; `R:num->num->real^3->bool`; `D:num->real^3->bool`;
                 `J:num->real^3->bool`; `C:num->num->real^3->bool`;
                 `C':num->num->real^3->bool`; `b:num`; `a:num`; `c:num`; `d:num`;
                 `sb:real^3->bool`; `sb':real^3->bool`] MOI_S4X_HEX_EXPAND) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th))] THEN
  MP_TAC(ISPECL [`V:num->real^3->bool`; `R:num->num->real^3->bool`; `D:num->real^3->bool`;
                 `J:num->real^3->bool`; `C:num->num->real^3->bool`;
                 `C':num->num->real^3->bool`; `d:num`; `a:num`; `b:num`; `c:num`;
                 `sd:real^3->bool`; `sd':real^3->bool`] MOI_S4X_HEX_EXPAND) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th))] THEN
  MP_TAC(ISPECL [`V:num->real^3->bool`; `R:num->num->real^3->bool`; `D:num->real^3->bool`;
                 `J:num->real^3->bool`; `C:num->num->real^3->bool`;
                 `C':num->num->real^3->bool`; `b:num`;
                 `sb:real^3->bool`; `sb':real^3->bool`] MOI_S4X_HEX_SUBSET) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`V:num->real^3->bool`; `R:num->num->real^3->bool`; `D:num->real^3->bool`;
                 `J:num->real^3->bool`; `C:num->num->real^3->bool`;
                 `C':num->num->real^3->bool`; `d:num`;
                 `sd:real^3->bool`; `sd':real^3->bool`] MOI_S4X_HEX_SUBSET) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN
   `(R:num->num->real^3->bool) b d = (sb INTER (V:num->real^3->bool) d) UNION (sb' INTER V d) /\
    R b d = (sd INTER V b) UNION (sd' INTER V b)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `moi_s4x_rimarcs (V:num->real^3->bool) (R:num->num->real^3->bool) (D:num->real^3->bool)
                   (C:num->num->real^3->bool) (C':num->num->real^3->bool)` THEN
    REWRITE_TAC[moi_s4x_rimarcs] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`b:num`; `d:num`; `a:num`; `c:num`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    FIRST_X_ASSUM(DISJ_CASES_THEN STRIP_ASSUME_TAC o check (fun th -> is_disj(concl th) &&
      can (find_term ((=) `(sb:real^3->bool) INTER (V:num->real^3->bool) d`)) (concl th))) THEN
    FIRST_X_ASSUM(DISJ_CASES_THEN STRIP_ASSUME_TAC o check (fun th -> is_disj(concl th) &&
      can (find_term ((=) `(sd:real^3->bool) INTER (V:num->real^3->bool) b`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[UNION_COMM];
    ALL_TAC] THEN
  UNDISCH_TAC `moi_s4x_tconf (V:num->real^3->bool) (R:num->num->real^3->bool) (D:num->real^3->bool) (J:num->real^3->bool)` THEN
  MOI_S4X_TC_TAC THEN
  USE_THEN "edge" (MP_TAC o SPECL [`b:num`; `d:num`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  USE_THEN "edge" (MP_TAC o SPECL [`d:num`; `b:num`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `pl_sphere 2 (frontier((V:num->real^3->bool) b)) /\
                pl_sphere 2 (frontier((V:num->real^3->bool) d))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [USE_THEN "ball" (MP_TAC o SPEC `b:num`); USE_THEN "ball" (MP_TAC o SPEC `d:num`)] THEN
    ANTS_TAC THEN ASM_REWRITE_TAC[] THEN MESON_TAC[MOI_S4X_BALL];
    ALL_TAC] THEN
  SUBGOAL_THEN `(V:num->real^3->bool) b INTER V d INTER V a = {} /\
                V b INTER V d INTER V c = {}`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN USE_THEN "three" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `frontier((V:num->real^3->bool) b) SUBSET V b /\ frontier(V d) SUBSET V d /\
                (R:num->num->real^3->bool) b d SUBSET V b INTER V d`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC FRONTIER_SUBSET_CLOSED THEN
      USE_THEN "ball" (MP_TAC o SPEC `b:num`) THEN
      ANTS_TAC THEN ASM_REWRITE_TAC[] THEN MESON_TAC[MOI_S4X_BALL];
      MATCH_MP_TAC FRONTIER_SUBSET_CLOSED THEN
      USE_THEN "ball" (MP_TAC o SPEC `d:num`) THEN
      ANTS_TAC THEN ASM_REWRITE_TAC[] THEN MESON_TAC[MOI_S4X_BALL];
      FIRST_ASSUM(MATCH_ACCEPT_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o
        MATCH_MP MOI_S4L_PL_CELL_FACTS)];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`frontier((V:num->real^3->bool) b)`; `(V:num->real^3->bool) b INTER V d`;
                 `(R:num->num->real^3->bool) b d`] DISK_COMPLEMENT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(ISPECL [`frontier((V:num->real^3->bool) d)`; `(V:num->real^3->bool) d INTER V b`;
                 `(R:num->num->real^3->bool) d b`] DISK_COMPLEMENT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN `(R:num->num->real^3->bool) d b = R b d /\
                (V:num->real^3->bool) d INTER V b = V b INTER V d`
  (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [ASM_REWRITE_TAC[] THEN SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`(frontier((V:num->real^3->bool) b) DIFF (V b INTER V d)) UNION (R:num->num->real^3->bool) b d`;
                 `(frontier((V:num->real^3->bool) d) DIFF (V b INTER V d)) UNION (R:num->num->real^3->bool) b d`;
                 `(R:num->num->real^3->bool) b d`] DISK_UNION) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC
     [`(R:num->num->real^3->bool) b d SUBSET (V:num->real^3->bool) b INTER V d`;
      `frontier((V:num->real^3->bool) b) SUBSET V b`;
      `frontier((V:num->real^3->bool) d) SUBSET V d`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  MAP_EVERY UNDISCH_TAC
   [`sb UNION sb' UNION ((V:num->real^3->bool) b INTER V a) UNION (V b INTER V c) UNION
     (V b INTER V d) = frontier (V b)`;
    `sd UNION sd' UNION ((V:num->real^3->bool) d INTER V a) UNION (V b INTER V d) UNION
     (V d INTER V c) = frontier (V d)`;
    `(R:num->num->real^3->bool) b d = (sb INTER (V:num->real^3->bool) d) UNION (sb' INTER V d)`;
    `(R:num->num->real^3->bool) b d = (sd INTER (V:num->real^3->bool) b) UNION (sd' INTER V b)`;
    `(sb:real^3->bool) SUBSET (V:num->real^3->bool) b`; `(sb':real^3->bool) SUBSET (V:num->real^3->bool) b`;
    `(sd:real^3->bool) SUBSET (V:num->real^3->bool) d`; `(sd':real^3->bool) SUBSET (V:num->real^3->bool) d`;
    `(V:num->real^3->bool) b INTER V d INTER V a = {}`;
    `(V:num->real^3->bool) b INTER V d INTER V c = {}`] THEN
  MATCH_ACCEPT_TAC SPDR9_SIG_SET);;

(* The context of the two-two split: hexagon pairs at all four vertices,  *)
(* the two at a and c sharing their rim arc on V a INTER V c.               *)

let moi_s4x_ctx = new_definition
 `moi_s4x_ctx (V:num->real^3->bool) (R:num->num->real^3->bool) (D:num->real^3->bool)
              (J:num->real^3->bool) (C:num->num->real^3->bool) (C':num->num->real^3->bool)
              (a:num) (b:num) (c:num) (d:num)
              (sa:real^3->bool) (sa':real^3->bool) (sb:real^3->bool) (sb':real^3->bool)
              (sc:real^3->bool) (sc':real^3->bool) (sd:real^3->bool) (sd':real^3->bool) <=>
   moi_s4x_tconf V R D J /\ moi_s4x_rimarcs V R D C C' /\
   moi_s4x_hex V D C C' a sa sa' /\ moi_s4x_hex V D C C' b sb sb' /\
   moi_s4x_hex V D C C' c sc sc' /\ moi_s4x_hex V D C C' d sd sd' /\
   a < 4 /\ b < 4 /\ c < 4 /\ d < 4 /\
   ~(a = b) /\ ~(a = c) /\ ~(a = d) /\ ~(b = c) /\ ~(b = d) /\ ~(c = d) /\
   sa INTER V c = sc INTER V a`;;

(* Replace an equation among the assumptions by the two inclusions (so that   *)
(* ASM_REWRITE_TAC cannot use it to rewrite).                               *)

let MOI_S4X_EQ2SUB_TAC tm =
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o
    MATCH_MP (SET_RULE `!x y:real^3->bool. x = y ==> x SUBSET y /\ y SUBSET x`) o
    check (fun th -> concl th = tm));;

(* Two disks of the sphere sg meeting near a point y of the circle k:      *)
(* their interiors lie on opposite sides of k.                              *)

let MOI_S4X_LOCAL2 = prove
 (`!sg om om' k (y:real^3) p1 b1 p2 b2 yy.
     pl_cell_with_boundary 2 om k /\ pl_cell_with_boundary 2 om' k /\
     om UNION om' = sg /\ om INTER om' = k /\
     pl_cell_with_boundary 2 p1 b1 /\ pl_cell_with_boundary 2 p2 b2 /\
     p1 SUBSET sg /\ p2 SUBSET sg /\
     closed yy /\ sg SUBSET p1 UNION p2 UNION yy /\ y IN k /\ ~(y IN yy) /\
     k INTER p1 SUBSET b1 /\ k INTER p2 SUBSET b2 /\
     b1 SUBSET k UNION yy /\ b2 SUBSET k UNION yy
     ==> (p1 DIFF b1 SUBSET om /\ p2 DIFF b2 SUBSET om') \/
         (p1 DIFF b1 SUBSET om' /\ p2 DIFF b2 SUBSET om)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`om:real^3->bool`; `om':real^3->bool`; `k:real^3->bool`; `y:real^3`;
                 `(:real^3) DIFF yy`; `p1 DIFF b1:real^3->bool`; `p2 DIFF b2:real^3->bool`]
    MOI_S4X_SIDES2) THEN
  ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4L_PL_CELL2_TOPO o
    check (fun th -> rand(rator(concl th)) = `p1:real^3->bool`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4L_PL_CELL2_TOPO o
    check (fun th -> rand(rator(concl th)) = `p2:real^3->bool`)) THEN
  ASM_REWRITE_TAC[GSYM closed; IN_DIFF; IN_UNIV] THEN
  MAP_EVERY UNDISCH_TAC
   [`om UNION om' = (sg:real^3->bool)`; `(sg:real^3->bool) SUBSET p1 UNION p2 UNION yy`;
    `k INTER p1 SUBSET (b1:real^3->bool)`; `k INTER p2 SUBSET (b2:real^3->bool)`;
    `(b1:real^3->bool) SUBSET k UNION yy`; `(b2:real^3->bool) SUBSET k UNION yy`;
    `(p1:real^3->bool) SUBSET sg`; `(p2:real^3->bool) SUBSET sg`] THEN
  SET_TAC[]);;

(* Two disks of sg sharing a point off k lie on the same side. *)

let MOI_S4X_SAME2 = prove
 (`!sg om om' k (y:real^3) p1 b1 p2 b2.
     pl_cell_with_boundary 2 om k /\ pl_cell_with_boundary 2 om' k /\
     om UNION om' = sg /\ om INTER om' = k /\
     pl_cell_with_boundary 2 p1 b1 /\ pl_cell_with_boundary 2 p2 b2 /\
     p1 SUBSET sg /\ p2 SUBSET sg /\
     (p1 DIFF b1) INTER k = {} /\ (p2 DIFF b2) INTER k = {} /\
     y IN p1 /\ y IN p2 /\ ~(y IN k)
     ==> (p1 DIFF b1 SUBSET om /\ p2 DIFF b2 SUBSET om) \/
         (p1 DIFF b1 SUBSET om' /\ p2 DIFF b2 SUBSET om')`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4L_PL_CELL2_TOPO o
    check (fun th -> rand(rator(concl th)) = `p1:real^3->bool`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4L_PL_CELL2_TOPO o
    check (fun th -> rand(rator(concl th)) = `p2:real^3->bool`)) THEN
  SUBGOAL_THEN `closed(om:real^3->bool) /\ closed(om':real^3->bool)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_S4L_PL_CELL_FACTS; COMPACT_IMP_CLOSED]; ALL_TAC] THEN
  SUBGOAL_THEN `!g:real^3->bool. connected g /\ g SUBSET sg /\ g INTER k = {}
                                 ==> g SUBSET om \/ g SUBSET om'`
  (LABEL_TAC "cs") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_SFR_CONNECTED_SIDE THEN
    EXISTS_TAC `k:real^3->bool` THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!g c:real^3->bool. g SUBSET c /\ closed c /\ (y:real^3) IN closure g
                                   ==> y IN c`
  (LABEL_TAC "cl") THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `closure g SUBSET (c:real^3->bool)` MP_TAC THENL
     [MATCH_MP_TAC CLOSURE_MINIMAL THEN ASM_REWRITE_TAC[]; ASM SET_TAC[]];
    ALL_TAC] THEN
  USE_THEN "cs" (MP_TAC o SPEC `p1 DIFF b1:real^3->bool`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; DISCH_TAC] THEN
  USE_THEN "cs" (MP_TAC o SPEC `p2 DIFF b2:real^3->bool`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN `(y:real^3) IN closure(p1 DIFF b1) /\ y IN closure(p2 DIFF b2)`
  STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!c:real^3->bool. closed c /\ (p1 DIFF b1) SUBSET c ==> (y:real^3) IN c`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN USE_THEN "cl" MATCH_MP_TAC THEN
    EXISTS_TAC `p1 DIFF b1:real^3->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!c:real^3->bool. closed c /\ (p2 DIFF b2) SUBSET c ==> (y:real^3) IN c`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN USE_THEN "cl" MATCH_MP_TAC THEN
    EXISTS_TAC `p2 DIFF b2:real^3->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY UNDISCH_TAC
   [`p1 DIFF b1 SUBSET om \/ p1 DIFF b1 SUBSET (om':real^3->bool)`;
    `p2 DIFF b2 SUBSET om \/ p2 DIFF b2 SUBSET (om':real^3->bool)`;
    `!c:real^3->bool. closed c /\ (p1 DIFF b1) SUBSET c ==> (y:real^3) IN c`;
    `!c:real^3->bool. closed c /\ (p2 DIFF b2) SUBSET c ==> (y:real^3) IN c`;
    `closed(om:real^3->bool)`; `closed(om':real^3->bool)`;
    `om INTER om' = (k:real^3->bool)`; `~((y:real^3) IN k)`] THEN
  REPEAT DISCH_TAC THEN ASM_MESON_TAC[SET_RULE
    `!y:real^3. y IN om /\ y IN om' /\ om INTER om' = k ==> y IN k`]);;

(* The split of the sphere of b and d by the boundary circle of Z. *)

let moi_s4x_split = new_definition
 `moi_s4x_split (V:num->real^3->bool) (D:num->real^3->bool) (a:num) (b:num) (c:num) (d:num)
                (sa:real^3->bool) (sb:real^3->bool) (sb':real^3->bool) (sc:real^3->bool)
                (sd:real^3->bool) (sd':real^3->bool) (om:real^3->bool) (om':real^3->bool) <=>
   pl_cell_with_boundary 2 om
     ((sa UNION sc UNION D a UNION D b UNION D c UNION D d) INTER (V b UNION V d)) /\
   pl_cell_with_boundary 2 om'
     ((sa UNION sc UNION D a UNION D b UNION D c UNION D d) INTER (V b UNION V d)) /\
   om UNION om' =
   sb UNION sb' UNION (V b INTER V a) UNION (V b INTER V c) UNION
   sd UNION sd' UNION (V d INTER V a) UNION (V d INTER V c) /\
   om INTER om' = (sa UNION sc UNION D a UNION D b UNION D c UNION D d) INTER (V b UNION V d)`;;

(* Common facts in the context of the split. *)

let MOI_S4X_CTX_FACTS = prove
 (`!V R D J C C' a b c d sa sa' sb sb' sc sc' sd sd'.
     moi_s4x_ctx V R D J C C' a b c d sa sa' sb sb' sc sc' sd sd'
     ==> sa SUBSET V a /\ sb SUBSET V b /\ sb' SUBSET V b /\ sc SUBSET V c /\
         sd SUBSET V d /\ sd' SUBSET V d /\
         closed(V a) /\ closed(V b) /\ closed(V c) /\ closed(V d) /\
         closed(D a) /\ closed(D b) /\ closed(D c) /\ closed(D d) /\
         D a INTER V a = {} /\ D b INTER V b = {} /\ D c INTER V c = {} /\
         D d INTER V d = {} /\
         D a INTER D b = {} /\ D a INTER D c = {} /\ D a INTER D d = {} /\
         D b INTER D c = {} /\ D b INTER D d = {} /\ D c INTER D d = {} /\
         V a INTER V b INTER V c = {} /\ V a INTER V b INTER V d = {} /\
         V a INTER V c INTER V d = {} /\ V b INTER V c INTER V d = {}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s4x_ctx] THEN STRIP_TAC THEN
  MAP_EVERY (fun (i,p,q) ->
    MP_TAC(ISPECL [`V:num->real^3->bool`; `R:num->num->real^3->bool`; `D:num->real^3->bool`;
                   `J:num->real^3->bool`; `C:num->num->real^3->bool`;
                   `C':num->num->real^3->bool`; i; p; q] MOI_S4X_HEX_SUBSET) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC])
   [`a:num`,`sa:real^3->bool`,`sa':real^3->bool`;
    `b:num`,`sb:real^3->bool`,`sb':real^3->bool`;
    `c:num`,`sc:real^3->bool`,`sc':real^3->bool`;
    `d:num`,`sd:real^3->bool`,`sd':real^3->bool`] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `moi_s4x_tconf V (R:num->num->real^3->bool) (D:num->real^3->bool) (J:num->real^3->bool)` THEN MOI_S4X_TC_TAC THEN
  SUBGOAL_THEN `!x. x < 4 ==> closed((V:num->real^3->bool) x) /\ closed((D:num->real^3->bool) x) /\
                              D x INTER V x = {}`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN
    USE_THEN "ball" (MP_TAC o SPEC `x:num`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    USE_THEN "face" (MP_TAC o SPEC `x:num`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[MOI_S4X_BALL; MOI_S4L_PL_CELL_FACTS; COMPACT_IMP_CLOSED];
    ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN
  REPEAT CONJ_TAC THEN
  FIRST [REWRITE_TAC[GSYM DISJOINT] THEN USE_THEN "fdisj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
         USE_THEN "three" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

let SPDR9_RIM2_SET = prove
 (`!sa sb sc Da Db Dc Dd Va Vb Vc Vd:real^3->bool.
     sb SUBSET Vb /\ sa SUBSET Va /\ sc SUBSET Vc /\ Db INTER Vb = {}
     ==> ((sa UNION sc UNION Da UNION Db UNION Dc UNION Dd) INTER (Vb UNION Vd)) INTER sb SUBSET
         Da INTER Vb UNION Dc INTER Vb UNION Dd INTER Vb UNION
         sb INTER Va UNION sb INTER Vc UNION sb INTER Vd`,
  REPEAT GEN_TAC THEN REWRITE_TAC[SUBSET; EXTENSION; IN_INTER; IN_UNION; NOT_IN_EMPTY] THEN
  STRIP_TAC THEN X_GEN_TAC `y:real^3` THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `y:real^3`)) THEN CONV_TAC TAUT);;

(* The two hexagons at b lie on opposite sides of the circle. *)

let MOI_S4X_RIM1 = prove
 (`!V R D J C C' a b c d sa sa' sb sb' sc sc' sd sd' om om'.
     moi_s4x_ctx V R D J C C' a b c d sa sa' sb sb' sc sc' sd sd' /\
     moi_s4x_split V D a b c d sa sb sb' sc sd sd' om om'
     ==> (sb DIFF ((D a INTER V b) UNION (D c INTER V b) UNION (D d INTER V b) UNION
                   (sb INTER V a) UNION (sb INTER V c) UNION (sb INTER V d)) SUBSET om /\
          sb' DIFF ((D a INTER V b) UNION (D c INTER V b) UNION (D d INTER V b) UNION
                    (sb' INTER V a) UNION (sb' INTER V c) UNION (sb' INTER V d)) SUBSET om') \/
         (sb DIFF ((D a INTER V b) UNION (D c INTER V b) UNION (D d INTER V b) UNION
                   (sb INTER V a) UNION (sb INTER V c) UNION (sb INTER V d)) SUBSET om' /\
          sb' DIFF ((D a INTER V b) UNION (D c INTER V b) UNION (D d INTER V b) UNION
                    (sb' INTER V a) UNION (sb' INTER V c) UNION (sb' INTER V d)) SUBSET om)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4X_CTX_FACTS) THEN
  UNDISCH_TAC `moi_s4x_split V (D:num->real^3->bool) a b c d sa sb sb' sc sd sd' om (om':real^3->bool)` THEN
  REWRITE_TAC[moi_s4x_split] THEN STRIP_TAC THEN
  UNDISCH_TAC `moi_s4x_ctx V R D (J:num->real^3->bool) (C:num->num->real^3->bool) (C':num->num->real^3->bool) a b c d sa sa' sb sb' sc sc' sd (sd':real^3->bool)` THEN
  REWRITE_TAC[moi_s4x_ctx] THEN STRIP_TAC THEN
  MOI_S4X_EQ2SUB_TAC `(sa:real^3->bool) INTER (V:num->real^3->bool) c = sc INTER V a` THEN
  MP_TAC(ISPECL [`V:num->real^3->bool`; `R:num->num->real^3->bool`; `D:num->real^3->bool`;
                 `J:num->real^3->bool`; `C:num->num->real^3->bool`;
                 `C':num->num->real^3->bool`; `b:num`; `a:num`; `c:num`; `d:num`;
                 `sb:real^3->bool`; `sb':real^3->bool`] MOI_S4X_HEX_EXPAND) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th))] THEN
  UNDISCH_TAC `moi_s4x_tconf V (R:num->num->real^3->bool) (D:num->real^3->bool) (J:num->real^3->bool)` THEN MOI_S4X_TC_TAC THEN
  USE_THEN "fpt" (MP_TAC o SPECL [`a:num`; `b:num`; `c:num`; `d:num`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `e1:real^3`) MP_TAC) THEN
  USE_THEN "fpt" (MP_TAC o SPECL [`a:num`; `b:num`; `d:num`; `c:num`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `e2:real^3` o CONJUNCT1) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[SET_RULE `!x y:real^3. {x} UNION {y} = {x,y}`] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC o MATCH_MP MOI_S4X_CELL1_MID) THEN
  SUBGOAL_THEN `closed((V:num->real^3->bool) a UNION V c UNION V d UNION
                       (D:num->real^3->bool) c UNION D d)` ASSUME_TAC THENL
   [REPEAT((MATCH_MP_TAC CLOSED_UNION THEN CONJ_TAC) ORELSE FIRST_ASSUM ACCEPT_TAC);
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_S4X_LOCAL2 THEN
  MAP_EVERY EXISTS_TAC
   [`om UNION om':real^3->bool`;
    `(sa UNION sc UNION (D:num->real^3->bool) a UNION D b UNION D c UNION D d) INTER
     ((V:num->real^3->bool) b UNION V d)`;
    `y:real^3`;
    `(V:num->real^3->bool) a UNION V c UNION V d UNION (D:num->real^3->bool) c UNION D d`] THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  FIRST [MATCH_MP_TAC SPDR9_RIM2_SET THEN ASM_REWRITE_TAC[] THEN NO_TAC; ALL_TAC] THEN
  MAP_EVERY UNDISCH_TAC
   [`(sa:real^3->bool) SUBSET (V:num->real^3->bool) a`; `(sb:real^3->bool) SUBSET (V:num->real^3->bool) b`;
    `(sb':real^3->bool) SUBSET (V:num->real^3->bool) b`; `(sc:real^3->bool) SUBSET (V:num->real^3->bool) c`;
    `(sd:real^3->bool) SUBSET (V:num->real^3->bool) d`; `(sd':real^3->bool) SUBSET (V:num->real^3->bool) d`;
    `(D:num->real^3->bool) a INTER (V:num->real^3->bool) a = {}`; `(D:num->real^3->bool) b INTER (V:num->real^3->bool) b = {}`;
    `(D:num->real^3->bool) a INTER D c = {}`; `(D:num->real^3->bool) a INTER D d = {}`;
    `(D:num->real^3->bool) a INTER (V:num->real^3->bool) b INTER V c = {e1:real^3}`;
    `(D:num->real^3->bool) a INTER (V:num->real^3->bool) b INTER V d = {e2:real^3}`;
    `(y:real^3) IN (D:num->real^3->bool) a INTER (V:num->real^3->bool) b`; `~(y:real^3 = e1)`; `~(y:real^3 = e2)`] THEN
  SET_TAC[]);;

(* The splitting disk V b INTER V a and the hexagon at b sharing the rim    *)
(* arc of sa lie on opposite sides of the circle.                           *)

let MOI_S4X_RIM2 = prove
 (`!V R D J C C' a b c d sa sa' sb sb' sc sc' sd sd' om om'.
     moi_s4x_ctx V R D J C C' a b c d sa sa' sb sb' sc sc' sd sd' /\
     moi_s4x_split V D a b c d sa sb sb' sc sd sd' om om' /\
     sb INTER V a = sa INTER V b
     ==> ((V b INTER V a) DIFF R b a SUBSET om /\
          sb DIFF ((D a INTER V b) UNION (D c INTER V b) UNION (D d INTER V b) UNION
                   (sb INTER V a) UNION (sb INTER V c) UNION (sb INTER V d)) SUBSET om') \/
         ((V b INTER V a) DIFF R b a SUBSET om' /\
          sb DIFF ((D a INTER V b) UNION (D c INTER V b) UNION (D d INTER V b) UNION
                   (sb INTER V a) UNION (sb INTER V c) UNION (sb INTER V d)) SUBSET om)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4X_CTX_FACTS) THEN
  UNDISCH_TAC `moi_s4x_split V (D:num->real^3->bool) a b c d sa sb sb' sc sd sd' om (om':real^3->bool)` THEN
  REWRITE_TAC[moi_s4x_split] THEN STRIP_TAC THEN
  UNDISCH_TAC `moi_s4x_ctx V R D (J:num->real^3->bool) (C:num->num->real^3->bool) (C':num->num->real^3->bool) a b c d sa sa' sb sb' sc sc' sd (sd':real^3->bool)` THEN
  REWRITE_TAC[moi_s4x_ctx] THEN STRIP_TAC THEN
  MOI_S4X_EQ2SUB_TAC `(sa:real^3->bool) INTER (V:num->real^3->bool) c = sc INTER V a` THEN
  MOI_S4X_EQ2SUB_TAC `(sb:real^3->bool) INTER (V:num->real^3->bool) a = sa INTER V b` THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4X_TC_BASIC) THEN
  MP_TAC(ISPECL [`V:num->real^3->bool`; `R:num->num->real^3->bool`; `D:num->real^3->bool`;
                 `J:num->real^3->bool`; `C:num->num->real^3->bool`;
                 `C':num->num->real^3->bool`; `b:num`; `a:num`; `c:num`; `d:num`;
                 `sb:real^3->bool`; `sb':real^3->bool`] MOI_S4X_HEX_EXPAND) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th))] THEN
  UNDISCH_TAC `moi_s4x_rimarcs V (R:num->num->real^3->bool) (D:num->real^3->bool) (C:num->num->real^3->bool) (C':num->num->real^3->bool)` THEN
  REWRITE_TAC[moi_s4x_rimarcs] THEN
  DISCH_THEN(MP_TAC o SPECL [`b:num`; `a:num`; `c:num`; `d:num`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  UNDISCH_TAC `moi_s4x_tconf V (R:num->num->real^3->bool) (D:num->real^3->bool) (J:num->real^3->bool)` THEN MOI_S4X_TC_TAC THEN
  USE_THEN "fpt" (MP_TAC o SPECL [`c:num`; `b:num`; `a:num`; `d:num`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `e1:real^3` o CONJUNCT1) THEN
  USE_THEN "fpt" (MP_TAC o SPECL [`d:num`; `b:num`; `a:num`; `c:num`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `e2:real^3` o CONJUNCT1) THEN
  SUBGOAL_THEN
   `pl_cell_with_boundary 1 (sb INTER (V:num->real^3->bool) a) {e1:real^3,e2} /\
    (sb INTER V a) UNION (sb' INTER V a) = (R:num->num->real^3->bool) b a /\
    (sb INTER V a) INTER (sb' INTER V a) = {e1,e2}`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `{e1:real^3,e2} = ((D:num->real^3->bool) c INTER (V:num->real^3->bool) b INTER V a)
                                   UNION (D d INTER V b INTER V a)` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[] THEN SET_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(DISJ_CASES_THEN STRIP_ASSUME_TAC o check (fun th ->
      is_disj(concl th) &&
      can (find_term ((=) `(sb:real^3->bool) INTER (V:num->real^3->bool) a`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[UNION_COMM; INTER_COMM];
    ALL_TAC] THEN
  USE_THEN "edge" (MP_TAC o SPECL [`b:num`; `a:num`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `closed(sb':real^3->bool)` ASSUME_TAC THENL
   [FIRST_ASSUM(MATCH_ACCEPT_TAC o MATCH_MP COMPACT_IMP_CLOSED o CONJUNCT1 o
      MATCH_MP MOI_S4L_PL_CELL_FACTS); ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o check (fun th ->
    concl th = `pl_cell_with_boundary 1 (sb INTER (V:num->real^3->bool) a) {e1:real^3,e2}`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC o MATCH_MP MOI_S4X_CELL1_MID) THEN
  SUBGOAL_THEN `closed((sb':real^3->bool) UNION (V:num->real^3->bool) c UNION V d)` ASSUME_TAC THENL
   [REPEAT((MATCH_MP_TAC CLOSED_UNION THEN CONJ_TAC) ORELSE FIRST_ASSUM ACCEPT_TAC);
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_S4X_LOCAL2 THEN
  MAP_EVERY EXISTS_TAC
   [`om UNION om':real^3->bool`;
    `(sa UNION sc UNION (D:num->real^3->bool) a UNION D b UNION D c UNION D d) INTER
     ((V:num->real^3->bool) b UNION V d)`;
    `y:real^3`;
    `sb' UNION (V:num->real^3->bool) c UNION V d`] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `(D:num->real^3->bool) a INTER (V:num->real^3->bool) b INTER V a SUBSET (R:num->num->real^3->bool) b a /\
    D b INTER V b INTER V a SUBSET R b a /\ D c INTER V b INTER V a SUBSET R b a /\
    D d INTER V b INTER V a SUBSET R b a`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REPEAT CONJ_TAC THEN
  FIRST [MATCH_MP_TAC SPDR9_RIM2_SET THEN ASM_REWRITE_TAC[] THEN NO_TAC; ALL_TAC] THEN
  MAP_EVERY UNDISCH_TAC
   [`(sa:real^3->bool) SUBSET (V:num->real^3->bool) a`; `(sb:real^3->bool) SUBSET (V:num->real^3->bool) b`;
    `(sb':real^3->bool) SUBSET (V:num->real^3->bool) b`; `(sc:real^3->bool) SUBSET (V:num->real^3->bool) c`;
    `(sd:real^3->bool) SUBSET (V:num->real^3->bool) d`; `(sd':real^3->bool) SUBSET (V:num->real^3->bool) d`;
    `(D:num->real^3->bool) b INTER (V:num->real^3->bool) b = {}`;
    `(V:num->real^3->bool) a INTER V b INTER V c = {}`;
    `(V:num->real^3->bool) a INTER V b INTER V d = {}`;
    `(sb:real^3->bool) INTER (V:num->real^3->bool) a SUBSET sa INTER V b`;
    `(sa:real^3->bool) INTER (V:num->real^3->bool) b SUBSET sb INTER V a`;
    `(sb INTER (V:num->real^3->bool) a) UNION (sb' INTER V a) = (R:num->num->real^3->bool) b a`;
    `(sb INTER (V:num->real^3->bool) a) INTER (sb' INTER V a) = {e1:real^3,e2}`;
    `(D:num->real^3->bool) a INTER (V:num->real^3->bool) b INTER V a SUBSET (R:num->num->real^3->bool) b a`;
    `(D:num->real^3->bool) b INTER (V:num->real^3->bool) b INTER V a SUBSET (R:num->num->real^3->bool) b a`;
    `(D:num->real^3->bool) c INTER (V:num->real^3->bool) b INTER V a SUBSET (R:num->num->real^3->bool) b a`;
    `(D:num->real^3->bool) d INTER (V:num->real^3->bool) b INTER V a SUBSET (R:num->num->real^3->bool) b a`;
    `(y:real^3) IN sb INTER (V:num->real^3->bool) a`; `~(y:real^3 = e1)`; `~(y:real^3 = e2)`] THEN
  SET_TAC[]);;

(* Two balls meeting at a point off a sphere: interiors on the same side. *)

(* The facts on a PL 3-ball used below, without equations of the form       *)
(* c = ... (which rewriting would loop on).                                 *)

let MOI_S4X_BALL_INT = prove
 (`!c:real^3->bool.
     pl_ball 3 c
     ==> closure(interior c) = c /\ connected(interior c) /\ ~(interior c = {}) /\
         open(interior c) /\ closed c /\ frontier c SUBSET c /\
         c DIFF frontier c = interior c /\ pl_sphere 2 (frontier c)`,
  GEN_TAC THEN
  DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC
    (filter (fun t -> not(is_eq(concl t) && is_var(lhs(concl t))))
            (CONJUNCTS(MATCH_MP MOI_S4X_BALL th)))) THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
  REWRITE_TAC[frontier] THEN SIMP_TAC[CLOSURE_CLOSED; ASSUME `closed(c:real^3->bool)`] THEN
  MP_TAC(ISPEC `c:real^3->bool` INTERIOR_SUBSET) THEN SET_TAC[]);;

let MOI_S4X_TB_SAME = prove
 (`!s v1 v2 (z:real^3).
     pl_sphere 2 s /\ pl_ball 3 v1 /\ pl_ball 3 v2 /\
     interior v1 INTER s = {} /\ interior v2 INTER s = {} /\
     z IN v1 /\ z IN v2 /\ ~(z IN s)
     ==> (interior v1 SUBSET inside s <=> interior v2 SUBSET inside s)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4X_JB) THEN
  MP_TAC(ISPEC `v1:real^3->bool` MOI_S4X_BALL_INT) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `v2:real^3->bool` MOI_S4X_BALL_INT) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `connected(interior v1 UNION {z:real^3}) /\ connected({z} UNION interior v2)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC CONNECTED_INTERMEDIATE_CLOSURE THENL
     [EXISTS_TAC `interior v1:real^3->bool`; EXISTS_TAC `interior v2:real^3->bool`] THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC [`(z:real^3) IN v1`; `(z:real^3) IN v2`] THEN
    MP_TAC(ISPEC `v1:real^3->bool` CLOSURE_SUBSET) THEN
    MP_TAC(ISPEC `interior v1:real^3->bool` CLOSURE_SUBSET) THEN
    MP_TAC(ISPEC `interior v2:real^3->bool` CLOSURE_SUBSET) THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `connected(interior v1 UNION {z:real^3} UNION interior v2)` ASSUME_TAC THENL
   [SUBGOAL_THEN `interior v1 UNION {z:real^3} UNION interior v2 =
                  (interior v1 UNION {z}) UNION ({z} UNION interior v2)` SUBST1_TAC THENL
     [SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC CONNECTED_UNION THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `interior v1 UNION {z:real^3} UNION interior v2`]
    MOI_S4X_SIDE3) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC
     [`interior v1 INTER s:real^3->bool = {}`; `interior v2 INTER s:real^3->bool = {}`;
      `~((z:real^3) IN s)`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  MAP_EVERY UNDISCH_TAC
   [`inside s INTER outside s:real^3->bool = {}`;
    `~(interior v1:real^3->bool = {})`; `~(interior v2:real^3->bool = {})`] THEN
  SET_TAC[]);;

(* Two balls meeting along a piece of a sphere near a point of it:          *)
(* interiors on opposite sides.                                             *)

let MOI_S4X_TB_OPP = prove
 (`!s v1 v2 (z:real^3) w.
     pl_sphere 2 s /\ pl_ball 3 v1 /\ pl_ball 3 v2 /\
     interior v1 INTER s = {} /\ interior v2 INTER s = {} /\
     z IN s /\ open w /\ z IN w /\ w SUBSET v1 UNION v2 /\
     w INTER frontier v1 SUBSET s /\ w INTER frontier v2 SUBSET s
     ==> (interior v1 SUBSET inside s <=> ~(interior v2 SUBSET inside s))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4X_JB) THEN
  MP_TAC(ISPEC `v1:real^3->bool` MOI_S4X_BALL_INT) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `v2:real^3->bool` MOI_S4X_BALL_INT) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `z:real^3`; `w:real^3->bool`;
                 `interior v1:real^3->bool`; `interior v2:real^3->bool`] MOI_S4X_SIDES3) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC
     [`(w:real^3->bool) SUBSET v1 UNION v2`;
      `w INTER frontier v1 SUBSET (s:real^3->bool)`;
      `w INTER frontier v2 SUBSET (s:real^3->bool)`;
      `(v1:real^3->bool) DIFF frontier v1 = interior v1`;
      `(v2:real^3->bool) DIFF frontier v2 = interior v2`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  MAP_EVERY UNDISCH_TAC
   [`inside s INTER outside s:real^3->bool = {}`;
    `~(interior v1:real^3->bool = {})`; `~(interior v2:real^3->bool = {})`] THEN
  SET_TAC[]);;

(* Symmetries of the context and the split. *)

let MOI_S4X_CTX_SWAP = prove
 (`!V R D J C C' a b c d sa sa' sb sb' sc sc' sd sd'.
     moi_s4x_ctx V R D J C C' a b c d sa sa' sb sb' sc sc' sd sd'
     ==> moi_s4x_ctx V R D J C C' c b a d sc sc' sb sb' sa sa' sd sd' /\
         moi_s4x_ctx V R D J C C' a d c b sa sa' sd sd' sc sc' sb sb' /\
         moi_s4x_ctx V R D J C C' a b c d sa sa' sb' sb sc sc' sd sd' /\
         moi_s4x_ctx V R D J C C' a b c d sa sa' sb sb' sc sc' sd' sd`,
  REWRITE_TAC[moi_s4x_ctx] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_SIMP_TAC[MOI_S4X_HEX_SYM]);;

let MOI_S4X_SPLIT_SWAP = prove
 (`!V D a b c d sa sb sb' sc sd sd' om om'.
     moi_s4x_split V D a b c d sa sb sb' sc sd sd' om om'
     ==> moi_s4x_split V D c b a d sc sb sb' sa sd sd' om om' /\
         moi_s4x_split V D a d c b sa sd sd' sc sb sb' om om' /\
         moi_s4x_split V D a b c d sa sb' sb sc sd sd' om om' /\
         moi_s4x_split V D a b c d sa sb sb' sc sd' sd om om' /\
         moi_s4x_split V D a b c d sa sb sb' sc sd sd' om' om`,
  REWRITE_TAC[moi_s4x_split] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(sc UNION sa UNION D c UNION D b UNION D a UNION D d) INTER
    ((V:num->real^3->bool) b UNION V d) =
    (sa UNION sc UNION D a UNION D b UNION D c UNION D d) INTER (V b UNION V d) /\
    (sa UNION sc UNION D a UNION D d UNION D c UNION D b) INTER (V d UNION V b) =
    (sa UNION sc UNION D a UNION D b UNION D c UNION (D:num->real^3->bool) d) INTER
    (V b UNION V d) /\
    sb UNION sb' UNION (V b INTER V c) UNION (V b INTER V a) UNION
    sd UNION sd' UNION (V d INTER V c) UNION (V d INTER V a) =
    sb UNION sb' UNION (V b INTER V a) UNION (V b INTER V c) UNION
    sd UNION sd' UNION (V d INTER V a) UNION (V d INTER V c) /\
    sd UNION sd' UNION (V d INTER V a) UNION (V d INTER V c) UNION
    sb UNION sb' UNION (V b INTER V a) UNION (V b INTER V c) =
    sb UNION sb' UNION (V b INTER V a) UNION (V b INTER V c) UNION
    sd UNION sd' UNION (V d INTER V a) UNION (V d INTER V c) /\
    sb' UNION sb UNION (V b INTER V a) UNION (V b INTER V c) UNION
    sd UNION sd' UNION (V d INTER V a) UNION (V d INTER V c) =
    sb UNION sb' UNION (V b INTER V a) UNION (V b INTER V c) UNION
    sd UNION sd' UNION (V d INTER V a) UNION (V d INTER V c) /\
    sb UNION sb' UNION (V b INTER V a) UNION (V b INTER V c) UNION
    sd' UNION sd UNION (V d INTER V a) UNION (V d INTER V c) =
    sb UNION sb' UNION (V b INTER V a) UNION (V b INTER V c) UNION
    sd UNION sd' UNION (V d INTER V a) UNION (V d INTER V c)`
  (fun th -> REWRITE_TAC[th]) THENL [REWRITE_TAC[UNION_ACI]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[UNION_COMM; INTER_COMM]);;

(* One splitting disk between the two sides of the split: V b INTER V a. *)

let MOI_S4X_UNIF_H = prove
 (`!V R D J C C' a b c d sa sa' sb sb' sc sc' sd sd' om om'.
     moi_s4x_ctx V R D J C C' a b c d sa sa' sb sb' sc sc' sd sd' /\
     moi_s4x_split V D a b c d sa sb sb' sc sd sd' om om' /\
     pl_sphere 2 ((sa UNION sc UNION D a UNION D b UNION D c UNION D d) UNION om) /\
     interior(V a) INTER ((sa UNION sc UNION D a UNION D b UNION D c UNION D d) UNION om) = {} /\
     interior(V b) INTER ((sa UNION sc UNION D a UNION D b UNION D c UNION D d) UNION om) = {}
     ==> ((V b INTER V a) DIFF R b a SUBSET om
          ==> (interior(V b) SUBSET
               inside((sa UNION sc UNION D a UNION D b UNION D c UNION D d) UNION om) <=>
               ~(interior(V a) SUBSET
                 inside((sa UNION sc UNION D a UNION D b UNION D c UNION D d) UNION om)))) /\
         ((V b INTER V a) DIFF R b a SUBSET om'
          ==> (interior(V b) SUBSET
               inside((sa UNION sc UNION D a UNION D b UNION D c UNION D d) UNION om) <=>
               interior(V a) SUBSET
               inside((sa UNION sc UNION D a UNION D b UNION D c UNION D d) UNION om))) /\
         ((V b INTER V a) DIFF R b a SUBSET om \/ (V b INTER V a) DIFF R b a SUBSET om') /\
         ~((V b INTER V a) DIFF R b a SUBSET om /\ (V b INTER V a) DIFF R b a SUBSET om')`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4X_CTX_FACTS) THEN
  UNDISCH_TAC `moi_s4x_split (V:num->real^3->bool) (D:num->real^3->bool) a b c d sa sb sb' sc sd sd' om (om':real^3->bool)` THEN
  REWRITE_TAC[moi_s4x_split] THEN STRIP_TAC THEN
  UNDISCH_TAC `moi_s4x_ctx (V:num->real^3->bool) (R:num->num->real^3->bool) (D:num->real^3->bool) (J:num->real^3->bool) (C:num->num->real^3->bool) (C':num->num->real^3->bool) a b c d sa sa' sb sb' sc sc' sd (sd':real^3->bool)` THEN
  REWRITE_TAC[moi_s4x_ctx] THEN STRIP_TAC THEN
  MOI_S4X_EQ2SUB_TAC `(sa:real^3->bool) INTER (V:num->real^3->bool) c = sc INTER V a` THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4X_TC_BASIC) THEN
  (* the hexagons at a and b *)
  MP_TAC(ISPECL [`V:num->real^3->bool`; `R:num->num->real^3->bool`; `D:num->real^3->bool`;
                 `J:num->real^3->bool`; `C:num->num->real^3->bool`;
                 `C':num->num->real^3->bool`; `b:num`; `a:num`; `c:num`; `d:num`;
                 `sb:real^3->bool`; `sb':real^3->bool`] MOI_S4X_HEX_EXPAND) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th))] THEN
  MP_TAC(ISPECL [`V:num->real^3->bool`; `R:num->num->real^3->bool`; `D:num->real^3->bool`;
                 `J:num->real^3->bool`; `C:num->num->real^3->bool`;
                 `C':num->num->real^3->bool`; `a:num`; `b:num`; `c:num`; `d:num`;
                 `sa:real^3->bool`; `sa':real^3->bool`] MOI_S4X_HEX_EXPAND) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th))] THEN
  MP_TAC(ISPECL [`V:num->real^3->bool`; `R:num->num->real^3->bool`; `D:num->real^3->bool`;
                 `J:num->real^3->bool`; `C:num->num->real^3->bool`;
                 `C':num->num->real^3->bool`; `a:num`;
                 `sa:real^3->bool`; `sa':real^3->bool`] MOI_S4X_HEX_SUBSET) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  (* the rim arcs on V b INTER V a are in R b a *)
  SUBGOAL_THEN
   `(sb INTER (V:num->real^3->bool) a) SUBSET (R:num->num->real^3->bool) b a /\
    (sb' INTER V a) SUBSET R b a /\ (sa INTER V b) SUBSET R b a /\ (sa' INTER V b) SUBSET R b a`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `moi_s4x_rimarcs (V:num->real^3->bool) (R:num->num->real^3->bool) (D:num->real^3->bool)
                   (C:num->num->real^3->bool) (C':num->num->real^3->bool)` THEN
    REWRITE_TAC[moi_s4x_rimarcs] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`b:num`; `a:num`; `c:num`; `d:num`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    FIRST_X_ASSUM(DISJ_CASES_THEN STRIP_ASSUME_TAC o check (fun th -> is_disj(concl th) &&
      can (find_term ((=) `(sb:real^3->bool) INTER (V:num->real^3->bool) a`)) (concl th))) THEN
    FIRST_X_ASSUM(DISJ_CASES_THEN STRIP_ASSUME_TAC o check (fun th -> is_disj(concl th) &&
      can (find_term ((=) `(sa:real^3->bool) INTER (V:num->real^3->bool) b`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(C:num->num->real^3->bool) b a UNION (C':num->num->real^3->bool) b a = (R:num->num->real^3->bool) b a` THEN
    SET_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `moi_s4x_tconf (V:num->real^3->bool) (R:num->num->real^3->bool) (D:num->real^3->bool) (J:num->real^3->bool)` THEN
  MOI_S4X_TC_TAC THEN
  USE_THEN "edge" (MP_TAC o SPECL [`b:num`; `a:num`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4L_PL_CELL2_TOPO o check (fun th ->
    concl th = `pl_cell_with_boundary 2 ((V:num->real^3->bool) b INTER V a)
                                        ((R:num->num->real^3->bool) b a)`)) THEN
  SUBGOAL_THEN
   `(D:num->real^3->bool) a INTER (V:num->real^3->bool) b INTER V a SUBSET (R:num->num->real^3->bool) b a /\
    D b INTER V b INTER V a SUBSET R b a /\ D c INTER V b INTER V a SUBSET R b a /\
    D d INTER V b INTER V a SUBSET R b a`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `zz = (sa UNION sc UNION (D:num->real^3->bool) a UNION D b UNION D c UNION D d)` THEN
  SUBGOAL_THEN `(zz INTER ((V:num->real^3->bool) b UNION V d)) INTER (V b INTER V a) SUBSET
                (R:num->num->real^3->bool) b a /\
                zz INTER (V b INTER V a) SUBSET R b a`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "zz" THEN
    MAP_EVERY UNDISCH_TAC
     [`(sa INTER (V:num->real^3->bool) b) SUBSET (R:num->num->real^3->bool) b a`;
      `(sc:real^3->bool) SUBSET (V:num->real^3->bool) c`;
      `(V:num->real^3->bool) a INTER V b INTER V c = {}`;
      `(D:num->real^3->bool) a INTER (V:num->real^3->bool) b INTER V a SUBSET (R:num->num->real^3->bool) b a`;
      `(D:num->real^3->bool) b INTER (V:num->real^3->bool) b INTER V a SUBSET (R:num->num->real^3->bool) b a`;
      `(D:num->real^3->bool) c INTER (V:num->real^3->bool) b INTER V a SUBSET (R:num->num->real^3->bool) b a`;
      `(D:num->real^3->bool) d INTER (V:num->real^3->bool) b INTER V a SUBSET (R:num->num->real^3->bool) b a`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `hh = ((V:num->real^3->bool) b INTER V a) DIFF (R:num->num->real^3->bool) b a` THEN
  SUBGOAL_THEN `hh SUBSET (om:real^3->bool) \/ hh SUBSET om'` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_SFR_CONNECTED_SIDE THEN
    EXISTS_TAC `zz INTER ((V:num->real^3->bool) b UNION V d)` THEN
    REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      FIRST_ASSUM(MATCH_ACCEPT_TAC o MATCH_MP COMPACT_IMP_CLOSED o CONJUNCT1 o MATCH_MP MOI_S4L_PL_CELL_FACTS);
      FIRST_ASSUM(MATCH_ACCEPT_TAC o MATCH_MP COMPACT_IMP_CLOSED o CONJUNCT1 o MATCH_MP MOI_S4L_PL_CELL_FACTS);
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "hh" THEN SET_TAC[];
      ASM_REWRITE_TAC[];
      EXPAND_TAC "hh" THEN
      UNDISCH_TAC `(zz INTER ((V:num->real^3->bool) b UNION V d)) INTER (V b INTER V a) SUBSET
                   (R:num->num->real^3->bool) b a` THEN
      SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `hh INTER (zz INTER ((V:num->real^3->bool) b UNION V d)) = {}` ASSUME_TAC THENL
   [EXPAND_TAC "hh" THEN
    UNDISCH_TAC `(zz INTER ((V:num->real^3->bool) b UNION V d)) INTER (V b INTER V a) SUBSET
                 (R:num->num->real^3->bool) b a` THEN
    SET_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `z:real^3` o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY] o
    check (fun th -> concl th = `~(hh:real^3->bool = {})`)) THEN
  SUBGOAL_THEN `pl_ball 3 ((V:num->real^3->bool) a) /\ pl_ball 3 (V b)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN USE_THEN "ball" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(z:real^3) IN V a /\ z IN V b /\ ~(z IN (R:num->num->real^3->bool) b a) /\
                z IN interior((V:num->real^3->bool) b UNION V a)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`(z:real^3) IN hh`;
      `(V:num->real^3->bool) b INTER V a DIFF (R:num->num->real^3->bool) b a = hh`;
      `hh SUBSET interior((V:num->real^3->bool) b UNION V a)`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [DISCH_TAC THEN
    MATCH_MP_TAC MOI_S4X_TB_OPP THEN
    MAP_EVERY EXISTS_TAC
     [`z:real^3`;
      `interior((V:num->real^3->bool) b UNION V a) DIFF
       (sb UNION sb' UNION (V b INTER V c) UNION (V b INTER V d) UNION
        sa UNION sa' UNION (V a INTER V c) UNION (V a INTER V d))`] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(V:num->real^3->bool) b INTER V a SUBSET om` ASSUME_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `closure(hh:real^3->bool)` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CLOSURE_MINIMAL THEN ASM_REWRITE_TAC[] THEN
      FIRST_ASSUM(MATCH_ACCEPT_TAC o MATCH_MP COMPACT_IMP_CLOSED o CONJUNCT1 o MATCH_MP MOI_S4L_PL_CELL_FACTS);
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `(V:num->real^3->bool) b INTER V a SUBSET om` THEN
      UNDISCH_TAC `(z:real^3) IN (V:num->real^3->bool) a` THEN UNDISCH_TAC `(z:real^3) IN (V:num->real^3->bool) b` THEN SET_TAC[];
      MATCH_MP_TAC OPEN_DIFF THEN REWRITE_TAC[OPEN_INTERIOR] THEN
      SUBGOAL_THEN `closed(sa:real^3->bool) /\ closed(sa':real^3->bool) /\
                    closed(sb:real^3->bool) /\ closed(sb':real^3->bool)`
      STRIP_ASSUME_TAC THENL
       [REPEAT CONJ_TAC THEN
        FIRST_ASSUM(MATCH_ACCEPT_TAC o MATCH_MP COMPACT_IMP_CLOSED o CONJUNCT1 o MATCH_MP MOI_S4L_PL_CELL_FACTS); ALL_TAC] THEN
      REPEAT((MATCH_MP_TAC CLOSED_UNION THEN CONJ_TAC) ORELSE
             (MATCH_MP_TAC CLOSED_INTER THEN CONJ_TAC) ORELSE FIRST_ASSUM ACCEPT_TAC);
      MAP_EVERY UNDISCH_TAC
       [`(sb INTER (V:num->real^3->bool) a) SUBSET (R:num->num->real^3->bool) b a`;
        `(sb' INTER (V:num->real^3->bool) a) SUBSET (R:num->num->real^3->bool) b a`;
        `(sa INTER (V:num->real^3->bool) b) SUBSET (R:num->num->real^3->bool) b a`;
        `(sa' INTER (V:num->real^3->bool) b) SUBSET (R:num->num->real^3->bool) b a`;
        `(V:num->real^3->bool) a INTER V b INTER V c = {}`;
        `(V:num->real^3->bool) a INTER V b INTER V d = {}`;
        `(z:real^3) IN (V:num->real^3->bool) a`; `(z:real^3) IN (V:num->real^3->bool) b`;
        `~((z:real^3) IN (R:num->num->real^3->bool) b a)`;
        `(z:real^3) IN interior((V:num->real^3->bool) b UNION V a)`] THEN
      SET_TAC[];
      MP_TAC(ISPEC `(V:num->real^3->bool) b UNION V a` INTERIOR_SUBSET) THEN SET_TAC[];
      MAP_EVERY UNDISCH_TAC
       [`sb UNION sb' UNION ((V:num->real^3->bool) b INTER V a) UNION (V b INTER V c) UNION
         (V b INTER V d) = frontier (V b)`;
        `(V:num->real^3->bool) b INTER V a SUBSET om`] THEN
      SET_TAC[];
      MAP_EVERY UNDISCH_TAC
       [`sa UNION sa' UNION ((V:num->real^3->bool) a INTER V b) UNION (V a INTER V c) UNION
         (V a INTER V d) = frontier (V a)`;
        `(V:num->real^3->bool) b INTER V a SUBSET om`] THEN
      SET_TAC[]];
    DISCH_TAC THEN MATCH_MP_TAC MOI_S4X_TB_SAME THEN EXISTS_TAC `z:real^3` THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC
     [`zz INTER ((V:num->real^3->bool) b INTER V a) SUBSET (R:num->num->real^3->bool) b a`;
      `hh SUBSET (om':real^3->bool)`;
      `hh INTER (zz INTER ((V:num->real^3->bool) b UNION V d)) = {}`;
      `om INTER om' = zz INTER ((V:num->real^3->bool) b UNION V d)`;
      `(z:real^3) IN hh`; `(z:real^3) IN (V:num->real^3->bool) a`;
      `(z:real^3) IN (V:num->real^3->bool) b`;
      `~((z:real^3) IN (R:num->num->real^3->bool) b a)`] THEN
    SET_TAC[];
    ASM_REWRITE_TAC[];
    MAP_EVERY UNDISCH_TAC
     [`hh INTER (zz INTER ((V:num->real^3->bool) b UNION V d)) = {}`;
      `om INTER om' = zz INTER ((V:num->real^3->bool) b UNION V d)`;
      `(z:real^3) IN hh`] THEN
    SET_TAC[]]);;

(* Instantiate a labelled implication and keep the instance as an assumption *)
(* (ANTS_TAC instead of MP_TAC plus ASM_REWRITE_TAC: no collapse).          *)

let MOI_S4X_INST_TAC lab tms =
  USE_THEN lab (MP_TAC o SPECL tms) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC ORELSE ASM_REWRITE_TAC[]; DISCH_TAC];;

let MOI_S4X_INSTS_TAC lab tms =
  USE_THEN lab (MP_TAC o SPECL tms) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC ORELSE ASM_REWRITE_TAC[];
                  DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th))];;

(* The sphere Z UNION om and the interiors of the four balls. *)

let MOI_S4X_ZOM = prove
 (`!V R D J C C' a b c d sa sa' sb sb' sc sc' sd sd' om om'.
     moi_s4x_ctx V R D J C C' a b c d sa sa' sb sb' sc sc' sd sd' /\
     moi_s4x_split V D a b c d sa sb sb' sc sd sd' om om'
     ==> pl_sphere 2 ((sa UNION sc UNION D a UNION D b UNION D c UNION D d) UNION om) /\
         interior(V a) INTER
         ((sa UNION sc UNION D a UNION D b UNION D c UNION D d) UNION om) = {} /\
         interior(V b) INTER
         ((sa UNION sc UNION D a UNION D b UNION D c UNION D d) UNION om) = {} /\
         interior(V c) INTER
         ((sa UNION sc UNION D a UNION D b UNION D c UNION D d) UNION om) = {} /\
         interior(V d) INTER
         ((sa UNION sc UNION D a UNION D b UNION D c UNION D d) UNION om) = {}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4X_CTX_FACTS) THEN
  SUBGOAL_THEN `pl_cell_with_boundary 2 (sa UNION sc UNION (D:num->real^3->bool) a UNION D b UNION
                                         D c UNION D d)
                ((sa UNION sc UNION D a UNION D b UNION D c UNION D d) INTER
                 ((V:num->real^3->bool) b UNION V d))`
  ASSUME_TAC THENL
   [UNDISCH_TAC `moi_s4x_ctx V (R:num->num->real^3->bool) (D:num->real^3->bool) (J:num->real^3->bool) (C:num->num->real^3->bool) (C':num->num->real^3->bool) a b c d sa sa' sb sb' sc sc' sd (sd':real^3->bool)` THEN
    REWRITE_TAC[moi_s4x_ctx] THEN STRIP_TAC THEN
    MATCH_MP_TAC MOI_S4X_ZDISK THEN
    MAP_EVERY EXISTS_TAC [`R:num->num->real^3->bool`; `J:num->real^3->bool`;
      `C:num->num->real^3->bool`; `C':num->num->real^3->bool`;
      `sa':real^3->bool`; `sc':real^3->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `moi_s4x_split (V:num->real^3->bool) (D:num->real^3->bool) a b c d sa sb sb' sc sd sd' om (om':real^3->bool)` THEN
  REWRITE_TAC[moi_s4x_split] THEN STRIP_TAC THEN
  UNDISCH_TAC `moi_s4x_ctx V (R:num->num->real^3->bool) (D:num->real^3->bool) (J:num->real^3->bool) (C:num->num->real^3->bool) (C':num->num->real^3->bool) a b c d sa sa' sb sb' sc sc' sd (sd':real^3->bool)` THEN
  REWRITE_TAC[moi_s4x_ctx] THEN STRIP_TAC THEN
  MOI_S4X_EQ2SUB_TAC `(sa:real^3->bool) INTER (V:num->real^3->bool) c = sc INTER V a` THEN
  FIRST_ASSUM(CONJUNCTS_THEN2 (LABEL_TAC "b1") (CONJUNCTS_THEN2 (LABEL_TAC "b2")
    (CONJUNCTS_THEN2 (LABEL_TAC "df") (LABEL_TAC "b4"))) o MATCH_MP MOI_S4X_TC_BASIC) THEN
  MAP_EVERY (fun (i,p,q) ->
    MP_TAC(ISPECL [`V:num->real^3->bool`; `R:num->num->real^3->bool`; `D:num->real^3->bool`;
                   `J:num->real^3->bool`; `C:num->num->real^3->bool`;
                   `C':num->num->real^3->bool`; i; p; q] MOI_S4X_HEX_SUBSET) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC])
   [`a:num`,`sa:real^3->bool`,`sa':real^3->bool`;
    `b:num`,`sb:real^3->bool`,`sb':real^3->bool`;
    `c:num`,`sc:real^3->bool`,`sc':real^3->bool`;
    `d:num`,`sd:real^3->bool`,`sd':real^3->bool`] THEN
  ABBREV_TAC `zz = (sa UNION sc UNION (D:num->real^3->bool) a UNION D b UNION D c UNION D d)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC DISK_UNION THEN
    EXISTS_TAC `zz INTER ((V:num->real^3->bool) b UNION V d)` THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC
     [`om UNION om' = sb UNION sb' UNION ((V:num->real^3->bool) b INTER V a) UNION
       (V b INTER V c) UNION sd UNION sd' UNION (V d INTER V a) UNION (V d INTER V c)`;
      `om INTER om' = zz INTER ((V:num->real^3->bool) b UNION V d)`;
      `(sb:real^3->bool) SUBSET (V:num->real^3->bool) b`;
      `(sb':real^3->bool) SUBSET (V:num->real^3->bool) b`;
      `(sd:real^3->bool) SUBSET (V:num->real^3->bool) d`;
      `(sd':real^3->bool) SUBSET (V:num->real^3->bool) d`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  (* om lies in V b UNION V d *)
  SUBGOAL_THEN `om SUBSET (V:num->real^3->bool) b UNION V d` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`om UNION om' = sb UNION sb' UNION ((V:num->real^3->bool) b INTER V a) UNION
       (V b INTER V c) UNION sd UNION sd' UNION (V d INTER V a) UNION (V d INTER V c)`;
      `(sb:real^3->bool) SUBSET (V:num->real^3->bool) b`;
      `(sb':real^3->bool) SUBSET (V:num->real^3->bool) b`;
      `(sd:real^3->bool) SUBSET (V:num->real^3->bool) d`;
      `(sd':real^3->bool) SUBSET (V:num->real^3->bool) d`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:num. frontier((V:num->real^3->bool) x) INTER interior(V x) = {}` ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[frontier] THEN SET_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `moi_s4x_tconf V (R:num->num->real^3->bool) (D:num->real^3->bool) (J:num->real^3->bool)` THEN
  MOI_S4X_TC_TAC THEN
  SUBGOAL_THEN `!x y. x < 4 /\ y < 4 /\ ~(x = y)
                      ==> (V:num->real^3->bool) x INTER V y SUBSET frontier(V x)`
  (LABEL_TAC "ef") THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN USE_THEN "edge" (MP_TAC o SPECL [`x:num`; `y:num`]) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x < 4 /\ zz INTER (V:num->real^3->bool) x SUBSET frontier(V x) /\
        om INTER V x SUBSET frontier(V x)
        ==> interior(V x) INTER (zz UNION om) = {}`
  (LABEL_TAC "int") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC(SPEC `x:num` (ASSUME `!x:num. frontier((V:num->real^3->bool) x) INTER interior(V x) = {}`)) THEN
    MP_TAC(ISPEC `(V:num->real^3->bool) x` INTERIOR_SUBSET) THEN
    MAP_EVERY UNDISCH_TAC
     [`zz INTER (V:num->real^3->bool) x SUBSET frontier(V x)`;
      `om INTER (V:num->real^3->bool) x SUBSET frontier(V x)`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  (* the pieces meet each V x inside its frontier *)
  SUBGOAL_THEN
   `!x y p:real^3->bool. x < 4 /\ y < 4 /\ p SUBSET (V:num->real^3->bool) y /\
                         (x = y ==> p SUBSET frontier(V y))
                         ==> p INTER V x SUBSET frontier(V x)`
  (LABEL_TAC "piece") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_CASES_TAC `x:num = y` THENL
     [FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp(concl th))) THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      USE_THEN "ef" (MP_TAC o SPECL [`x:num`; `y:num`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `p SUBSET (V:num->real^3->bool) y` THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `om SUBSET sb UNION sb' UNION ((V:num->real^3->bool) b INTER V a) UNION
                (V b INTER V c) UNION sd UNION sd' UNION (V d INTER V a) UNION (V d INTER V c)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `om UNION om' = sb UNION sb' UNION ((V:num->real^3->bool) b INTER V a) UNION
                 (V b INTER V c) UNION sd UNION sd' UNION (V d INTER V a) UNION (V d INTER V c)` THEN
    SET_TAC[];
    ALL_TAC] THEN
  (let piece_tac =
     FIRST [USE_THEN "df" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN NO_TAC;
            FIRST (map (fun y -> USE_THEN "piece" MATCH_MP_TAC THEN EXISTS_TAC y THEN
                                 ASM_REWRITE_TAC[INTER_SUBSET] THEN NO_TAC)
                       [`a:num`; `b:num`; `c:num`; `d:num`])] in
   REPEAT CONJ_TAC THEN (USE_THEN "int" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
   EXPAND_TAC "zz" THEN CONJ_TAC THENL
    [REWRITE_TAC[SET_RULE `!a b c:real^3->bool. (a UNION b) INTER c = (a INTER c) UNION (b INTER c)`; UNION_SUBSET] THEN REPEAT CONJ_TAC THEN piece_tac;
     MATCH_MP_TAC(SET_RULE `!om s v f:real^3->bool.
       om SUBSET s /\ s INTER v SUBSET f ==> om INTER v SUBSET f`) THEN
     EXISTS_TAC `sb UNION sb' UNION ((V:num->real^3->bool) b INTER V a) UNION
                 (V b INTER V c) UNION sd UNION sd' UNION (V d INTER V a) UNION (V d INTER V c)` THEN
     ASM_REWRITE_TAC[] THEN
     REWRITE_TAC[SET_RULE `!a b c:real^3->bool. (a UNION b) INTER c = (a INTER c) UNION (b INTER c)`; UNION_SUBSET] THEN REPEAT CONJ_TAC THEN piece_tac])));;

(* Rim arcs of hexagons lie in the rims. *)

let MOI_S4X_HEX_RIM = prove
 (`!V R D J C C' i j p q.
     moi_s4x_tconf V R D J /\ moi_s4x_rimarcs V R D C C' /\ moi_s4x_hex V D C C' i p q /\
     i < 4 /\ j < 4 /\ ~(i = j)
     ==> p INTER V j SUBSET R i j /\ q INTER V j SUBSET R i j`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`i:num`; `j:num`] MOI_S4X_OTHER2) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `l:num` STRIP_ASSUME_TAC)) THEN
  UNDISCH_TAC `moi_s4x_rimarcs V (R:num->num->real^3->bool) (D:num->real^3->bool)
                 (C:num->num->real^3->bool) (C':num->num->real^3->bool)` THEN
  REWRITE_TAC[moi_s4x_rimarcs] THEN
  DISCH_THEN(MP_TAC o SPECL [`i:num`; `j:num`; `k:num`; `l:num`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  UNDISCH_TAC `moi_s4x_hex V (D:num->real^3->bool) (C:num->num->real^3->bool)
                 (C':num->num->real^3->bool) i p q` THEN
  REWRITE_TAC[moi_s4x_hex] THEN
  DISCH_THEN(MP_TAC o SPEC `j:num` o last o CONJUNCTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `(C:num->num->real^3->bool) i j UNION C' i j = (R:num->num->real^3->bool) i j` THEN
  SET_TAC[]);;


(* The two balls on each side of the split lie on the same side of the      *)
(* sphere Z UNION om.                                                       *)

let MOI_S4X_ZOM_SAME = prove
 (`!V R D J C C' a b c d sa sa' sb sb' sc sc' sd sd' om om'.
     moi_s4x_ctx V R D J C C' a b c d sa sa' sb sb' sc sc' sd sd' /\
     moi_s4x_split V D a b c d sa sb sb' sc sd sd' om om'
     ==> (interior(V a) SUBSET
          inside((sa UNION sc UNION D a UNION D b UNION D c UNION D d) UNION om) <=>
          interior(V c) SUBSET
          inside((sa UNION sc UNION D a UNION D b UNION D c UNION D d) UNION om)) /\
         (interior(V b) SUBSET
          inside((sa UNION sc UNION D a UNION D b UNION D c UNION D d) UNION om) <=>
          interior(V d) SUBSET
          inside((sa UNION sc UNION D a UNION D b UNION D c UNION D d) UNION om))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:num->real^3->bool`; `R:num->num->real^3->bool`; `D:num->real^3->bool`;
                 `J:num->real^3->bool`; `C:num->num->real^3->bool`;
                 `C':num->num->real^3->bool`; `a:num`; `b:num`; `c:num`; `d:num`;
                 `sa:real^3->bool`; `sa':real^3->bool`; `sb:real^3->bool`; `sb':real^3->bool`;
                 `sc:real^3->bool`; `sc':real^3->bool`; `sd:real^3->bool`; `sd':real^3->bool`;
                 `om:real^3->bool`; `om':real^3->bool`] MOI_S4X_ZOM) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4X_CTX_FACTS) THEN
  UNDISCH_TAC `moi_s4x_split V (D:num->real^3->bool) a b c d sa sb sb' sc sd sd' om (om':real^3->bool)` THEN
  REWRITE_TAC[moi_s4x_split] THEN STRIP_TAC THEN
  UNDISCH_TAC `moi_s4x_ctx V R D (J:num->real^3->bool) (C:num->num->real^3->bool) (C':num->num->real^3->bool) a b c d sa sa' sb sb' sc sc' sd (sd':real^3->bool)` THEN
  REWRITE_TAC[moi_s4x_ctx] THEN STRIP_TAC THEN
  MOI_S4X_EQ2SUB_TAC `(sa:real^3->bool) INTER (V:num->real^3->bool) c = sc INTER V a` THEN
  FIRST_ASSUM(CONJUNCTS_THEN2 (LABEL_TAC "b1") (CONJUNCTS_THEN2 (LABEL_TAC "b2")
    (CONJUNCTS_THEN2 (LABEL_TAC "b3") (LABEL_TAC "rimp"))) o MATCH_MP MOI_S4X_TC_BASIC) THEN
  (* rim arcs of the hexagons *)
  MAP_EVERY (fun (i,j,p,q) ->
    MP_TAC(ISPECL [`V:num->real^3->bool`; `R:num->num->real^3->bool`; `D:num->real^3->bool`;
                   `J:num->real^3->bool`; `C:num->num->real^3->bool`;
                   `C':num->num->real^3->bool`; i; j; p; q] MOI_S4X_HEX_RIM) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC])
   [`a:num`,`c:num`,`sa:real^3->bool`,`sa':real^3->bool`;
    `c:num`,`a:num`,`sc:real^3->bool`,`sc':real^3->bool`;
    `b:num`,`d:num`,`sb:real^3->bool`,`sb':real^3->bool`;
    `d:num`,`b:num`,`sd:real^3->bool`,`sd':real^3->bool`] THEN
  UNDISCH_TAC `moi_s4x_tconf V (R:num->num->real^3->bool) (D:num->real^3->bool) (J:num->real^3->bool)` THEN
  MOI_S4X_TC_TAC THEN
  MAP_EVERY (fun (i,j) -> USE_THEN "edge" (MP_TAC o SPECL [i; j]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[];
                    DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th))])
   [`a:num`,`c:num`; `b:num`,`d:num`] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `(R:num->num->real^3->bool) c a = R a c`;
                              ASSUME `(R:num->num->real^3->bool) d b = R b d`]) THEN
  MAP_EVERY (fun (m,i,j) -> USE_THEN "rimp" (MP_TAC o SPECL [m; i; j]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC])
   [`a:num`,`a:num`,`c:num`; `b:num`,`a:num`,`c:num`; `c:num`,`a:num`,`c:num`;
    `d:num`,`a:num`,`c:num`;
    `a:num`,`b:num`,`d:num`; `b:num`,`b:num`,`d:num`; `c:num`,`b:num`,`d:num`;
    `d:num`,`b:num`,`d:num`] THEN
  SUBGOAL_THEN `pl_ball 3 ((V:num->real^3->bool) a) /\ pl_ball 3 (V b) /\
                pl_ball 3 (V c) /\ pl_ball 3 (V d)` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN USE_THEN "ball" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `om SUBSET sb UNION sb' UNION ((V:num->real^3->bool) b INTER V a) UNION
                (V b INTER V c) UNION sd UNION sd' UNION (V d INTER V a) UNION (V d INTER V c)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `om UNION om' = sb UNION sb' UNION ((V:num->real^3->bool) b INTER V a) UNION
                 (V b INTER V c) UNION sd UNION sd' UNION (V d INTER V a) UNION (V d INTER V c)` THEN
    SET_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THEN MATCH_MP_TAC MOI_S4X_TB_SAME THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th -> concl th =
      `pl_cell_with_boundary 2 ((V:num->real^3->bool) a INTER V c) ((R:num->num->real^3->bool) a c)`)) THEN
    DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o MATCH_MP MOI_S4L_PL_CELL2_TOPO) THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN DISCH_THEN(X_CHOOSE_TAC `z:real^3`) THEN
    EXISTS_TAC `z:real^3` THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC
     [`(z:real^3) IN (V:num->real^3->bool) a INTER V c DIFF (R:num->num->real^3->bool) a c`;
      `om SUBSET sb UNION sb' UNION ((V:num->real^3->bool) b INTER V a) UNION
       (V b INTER V c) UNION sd UNION sd' UNION (V d INTER V a) UNION (V d INTER V c)`;
      `(sb:real^3->bool) SUBSET (V:num->real^3->bool) b`;
      `(sb':real^3->bool) SUBSET (V:num->real^3->bool) b`;
      `(sd:real^3->bool) SUBSET (V:num->real^3->bool) d`;
      `(sd':real^3->bool) SUBSET (V:num->real^3->bool) d`;
      `(V:num->real^3->bool) a INTER V b INTER V c = {}`;
      `(V:num->real^3->bool) a INTER V c INTER V d = {}`;
      `(sa:real^3->bool) INTER (V:num->real^3->bool) c SUBSET (R:num->num->real^3->bool) a c`;
      `(sc:real^3->bool) INTER (V:num->real^3->bool) a SUBSET (R:num->num->real^3->bool) a c`;
      `(D:num->real^3->bool) a INTER (V:num->real^3->bool) a INTER V c SUBSET (R:num->num->real^3->bool) a c`;
      `(D:num->real^3->bool) b INTER (V:num->real^3->bool) a INTER V c SUBSET (R:num->num->real^3->bool) a c`;
      `(D:num->real^3->bool) c INTER (V:num->real^3->bool) a INTER V c SUBSET (R:num->num->real^3->bool) a c`;
      `(D:num->real^3->bool) d INTER (V:num->real^3->bool) a INTER V c SUBSET (R:num->num->real^3->bool) a c`] THEN
    SET_TAC[];
    FIRST_X_ASSUM(MP_TAC o check (fun th -> concl th =
      `pl_cell_with_boundary 2 ((V:num->real^3->bool) b INTER V d) ((R:num->num->real^3->bool) b d)`)) THEN
    DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o MATCH_MP MOI_S4L_PL_CELL2_TOPO) THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN DISCH_THEN(X_CHOOSE_TAC `z:real^3`) THEN
    EXISTS_TAC `z:real^3` THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC
     [`(z:real^3) IN (V:num->real^3->bool) b INTER V d DIFF (R:num->num->real^3->bool) b d`;
      `om SUBSET sb UNION sb' UNION ((V:num->real^3->bool) b INTER V a) UNION
       (V b INTER V c) UNION sd UNION sd' UNION (V d INTER V a) UNION (V d INTER V c)`;
      `(sa:real^3->bool) SUBSET (V:num->real^3->bool) a`;
      `(sc:real^3->bool) SUBSET (V:num->real^3->bool) c`;
      `(V:num->real^3->bool) a INTER V b INTER V d = {}`;
      `(V:num->real^3->bool) b INTER V c INTER V d = {}`;
      `(sb:real^3->bool) INTER (V:num->real^3->bool) d SUBSET (R:num->num->real^3->bool) b d`;
      `(sb':real^3->bool) INTER (V:num->real^3->bool) d SUBSET (R:num->num->real^3->bool) b d`;
      `(sd:real^3->bool) INTER (V:num->real^3->bool) b SUBSET (R:num->num->real^3->bool) b d`;
      `(sd':real^3->bool) INTER (V:num->real^3->bool) b SUBSET (R:num->num->real^3->bool) b d`;
      `(D:num->real^3->bool) a INTER (V:num->real^3->bool) b INTER V d SUBSET (R:num->num->real^3->bool) b d`;
      `(D:num->real^3->bool) b INTER (V:num->real^3->bool) b INTER V d SUBSET (R:num->num->real^3->bool) b d`;
      `(D:num->real^3->bool) c INTER (V:num->real^3->bool) b INTER V d SUBSET (R:num->num->real^3->bool) b d`;
      `(D:num->real^3->bool) d INTER (V:num->real^3->bool) b INTER V d SUBSET (R:num->num->real^3->bool) b d`] THEN
    SET_TAC[]]);;

(* The four splitting disks between the two sides lie on one side of the   *)
(* circle together.                                                         *)

let MOI_S4X_UNIF = prove
 (`!V R D J C C' a b c d sa sa' sb sb' sc sc' sd sd' om om'.
     moi_s4x_ctx V R D J C C' a b c d sa sa' sb sb' sc sc' sd sd' /\
     moi_s4x_split V D a b c d sa sb sb' sc sd sd' om om'
     ==> ((V b INTER V a) DIFF R b a SUBSET om <=> (V b INTER V c) DIFF R b c SUBSET om) /\
         ((V b INTER V a) DIFF R b a SUBSET om <=> (V d INTER V a) DIFF R d a SUBSET om) /\
         ((V b INTER V a) DIFF R b a SUBSET om <=> (V d INTER V c) DIFF R d c SUBSET om)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4X_CTX_SWAP) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4X_SPLIT_SWAP) THEN
  MP_TAC(ISPECL [`V:num->real^3->bool`; `R:num->num->real^3->bool`; `D:num->real^3->bool`;
                 `J:num->real^3->bool`; `C:num->num->real^3->bool`;
                 `C':num->num->real^3->bool`; `a:num`; `b:num`; `c:num`; `d:num`;
                 `sa:real^3->bool`; `sa':real^3->bool`; `sb:real^3->bool`; `sb':real^3->bool`;
                 `sc:real^3->bool`; `sc':real^3->bool`; `sd:real^3->bool`; `sd':real^3->bool`;
                 `om:real^3->bool`; `om':real^3->bool`] MOI_S4X_ZOM) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  ABBREV_TAC `zz = (sa UNION sc UNION (D:num->real^3->bool) a UNION D b UNION D c UNION D d)` THEN
  SUBGOAL_THEN
   `sc UNION sa UNION (D:num->real^3->bool) c UNION D b UNION D a UNION D d = zz /\
    sa UNION sc UNION D a UNION D d UNION D c UNION D b = zz /\
    sc UNION sa UNION D c UNION D d UNION D a UNION D b = zz`
  STRIP_ASSUME_TAC THENL [EXPAND_TAC "zz" THEN SET_TAC[]; ALL_TAC] THEN
  (* the four splitting disks *)
  MP_TAC(ISPECL [`V:num->real^3->bool`; `R:num->num->real^3->bool`; `D:num->real^3->bool`;
                 `J:num->real^3->bool`; `C:num->num->real^3->bool`;
                 `C':num->num->real^3->bool`; `a:num`; `b:num`; `c:num`; `d:num`;
                 `sa:real^3->bool`; `sa':real^3->bool`; `sb:real^3->bool`; `sb':real^3->bool`;
                 `sc:real^3->bool`; `sc':real^3->bool`; `sd:real^3->bool`; `sd':real^3->bool`;
                 `om:real^3->bool`; `om':real^3->bool`] MOI_S4X_UNIF_H) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  MP_TAC(ISPECL [`V:num->real^3->bool`; `R:num->num->real^3->bool`; `D:num->real^3->bool`;
                 `J:num->real^3->bool`; `C:num->num->real^3->bool`;
                 `C':num->num->real^3->bool`; `c:num`; `b:num`; `a:num`; `d:num`;
                 `sc:real^3->bool`; `sc':real^3->bool`; `sb:real^3->bool`; `sb':real^3->bool`;
                 `sa:real^3->bool`; `sa':real^3->bool`; `sd:real^3->bool`; `sd':real^3->bool`;
                 `om:real^3->bool`; `om':real^3->bool`] MOI_S4X_UNIF_H) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  MP_TAC(ISPECL [`V:num->real^3->bool`; `R:num->num->real^3->bool`; `D:num->real^3->bool`;
                 `J:num->real^3->bool`; `C:num->num->real^3->bool`;
                 `C':num->num->real^3->bool`; `a:num`; `d:num`; `c:num`; `b:num`;
                 `sa:real^3->bool`; `sa':real^3->bool`; `sd:real^3->bool`; `sd':real^3->bool`;
                 `sc:real^3->bool`; `sc':real^3->bool`; `sb:real^3->bool`; `sb':real^3->bool`;
                 `om:real^3->bool`; `om':real^3->bool`] MOI_S4X_UNIF_H) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  SUBGOAL_THEN `moi_s4x_ctx V R D J C C' c d a b sc sc' sd sd' sa sa' sb sb' /\
                moi_s4x_split V D c d a b sc sd sd' sa sb sb' om om'`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o CONJUNCT1 o MATCH_MP MOI_S4X_CTX_SWAP o check (fun th ->
        concl th = `moi_s4x_ctx V (R:num->num->real^3->bool) (D:num->real^3->bool)
          (J:num->real^3->bool) (C:num->num->real^3->bool) (C':num->num->real^3->bool)
          a d c b sa sa' sd sd' sc sc' sb sb'`)) THEN SIMP_TAC[];
      FIRST_X_ASSUM(MP_TAC o CONJUNCT1 o MATCH_MP MOI_S4X_SPLIT_SWAP o check (fun th ->
        concl th = `moi_s4x_split V (D:num->real^3->bool) a d c b sa sd sd' sc sb sb' om om'`)) THEN
      SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:num->real^3->bool`; `R:num->num->real^3->bool`; `D:num->real^3->bool`;
                 `J:num->real^3->bool`; `C:num->num->real^3->bool`;
                 `C':num->num->real^3->bool`; `c:num`; `d:num`; `a:num`; `b:num`;
                 `sc:real^3->bool`; `sc':real^3->bool`; `sd:real^3->bool`; `sd':real^3->bool`;
                 `sa:real^3->bool`; `sa':real^3->bool`; `sb:real^3->bool`; `sb':real^3->bool`;
                 `om:real^3->bool`; `om':real^3->bool`] MOI_S4X_UNIF_H) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  MP_TAC(ISPECL [`V:num->real^3->bool`; `R:num->num->real^3->bool`; `D:num->real^3->bool`;
                 `J:num->real^3->bool`; `C:num->num->real^3->bool`;
                 `C':num->num->real^3->bool`; `a:num`; `b:num`; `c:num`; `d:num`;
                 `sa:real^3->bool`; `sa':real^3->bool`; `sb:real^3->bool`; `sb':real^3->bool`;
                 `sc:real^3->bool`; `sc':real^3->bool`; `sd:real^3->bool`; `sd':real^3->bool`;
                 `om:real^3->bool`; `om':real^3->bool`] MOI_S4X_ZOM_SAME) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (fun th ->
    let c = concl th in
    (is_disj c || (is_neg c && is_conj(dest_neg c)) ||
     can (find_term (fun t -> is_const t && fst(dest_const t) = "inside")) c) &&
    not (can (find_term (fun t -> is_const t && fst(dest_const t) = "moi_s4x_ctx")) c)))) THEN
  CONV_TAC TAUT);;


(* ------------------------------------------------------------------------- *)
(* Consistency.  In the split of the sphere Sigma (the two                  *)
(* hexagon pairs at b and d and the splitting disks at b and d other than   *)
(* V b INTER V d) by the boundary circle of Z, the four cross splitting     *)
(* disks lie on one side (UNIF).  On the other side lie the open parts of   *)
(* the hexagon at b sharing the rim arc of sa (RIM2) and of the hexagon at  *)
(* b sharing the rim arc of sc; RIM1 makes them equal.  The same at d, and  *)
(* the two chosen hexagons share their rim arc on V b INTER V d (CROSS).   *)
(* ------------------------------------------------------------------------- *)

(* The hexagon at y sharing the rim arc of a hexagon at x. *)

let MOI_S4X_PICK = prove
 (`!V R D J C C' x y sx sx' sy sy'.
     moi_s4x_tconf V R D J /\ moi_s4x_rimarcs V R D C C' /\
     moi_s4x_hex V D C C' x sx sx' /\ moi_s4x_hex V D C C' y sy sy' /\
     x < 4 /\ y < 4 /\ ~(x = y)
     ==> ?t t'. ((t = sy /\ t' = sy') \/ (t = sy' /\ t' = sy)) /\
                t INTER V x = sx INTER V y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`y:num`; `x:num`] MOI_S4X_OTHER2) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `l:num` STRIP_ASSUME_TAC)) THEN
  UNDISCH_TAC `moi_s4x_rimarcs V (R:num->num->real^3->bool) (D:num->real^3->bool)
                 (C:num->num->real^3->bool) (C':num->num->real^3->bool)` THEN
  REWRITE_TAC[moi_s4x_rimarcs] THEN
  DISCH_THEN(MP_TAC o SPECL [`y:num`; `x:num`; `k:num`; `l:num`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  UNDISCH_TAC `moi_s4x_hex V (D:num->real^3->bool) (C:num->num->real^3->bool)
                 (C':num->num->real^3->bool) y sy sy'` THEN
  REWRITE_TAC[moi_s4x_hex] THEN
  DISCH_THEN(MP_TAC o SPEC `x:num` o last o CONJUNCTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  UNDISCH_TAC `moi_s4x_hex V (D:num->real^3->bool) (C:num->num->real^3->bool)
                 (C':num->num->real^3->bool) x sx sx'` THEN
  REWRITE_TAC[moi_s4x_hex] THEN
  DISCH_THEN(MP_TAC o SPEC `y:num` o last o CONJUNCTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  ASM_CASES_TAC `(sy:real^3->bool) INTER (V:num->real^3->bool) x = sx INTER V y` THENL
   [MAP_EVERY EXISTS_TAC [`sy:real^3->bool`; `sy':real^3->bool`] THEN ASM_REWRITE_TAC[];
    MAP_EVERY EXISTS_TAC [`sy':real^3->bool`; `sy:real^3->bool`] THEN REWRITE_TAC[] THEN
    UNDISCH_TAC `~((sy:real^3->bool) INTER (V:num->real^3->bool) x = sx INTER V y)` THEN
    MAP_EVERY UNDISCH_TAC
     [`(sy INTER (V:num->real^3->bool) x = (C:num->num->real^3->bool) y x /\
        sy' INTER V x = (C':num->num->real^3->bool) y x) \/
       (sy INTER V x = C' y x /\ sy' INTER V x = C y x)`;
      `(sx INTER (V:num->real^3->bool) y = (C:num->num->real^3->bool) x y /\
        sx' INTER V y = (C':num->num->real^3->bool) x y) \/
       (sx INTER V y = C' x y /\ sx' INTER V y = C x y)`;
      `(C:num->num->real^3->bool) x y = C y x`;
      `(C':num->num->real^3->bool) x y = C' y x`] THEN
    MESON_TAC[]]);;

let SPDR9_HINT_SET = prove
 (`!om om' sa sb sc Da Db Dc Dd Va Vb Vc Vd:real^3->bool.
     om INTER om' = (sa UNION sc UNION Da UNION Db UNION Dc UNION Dd) INTER (Vb UNION Vd) ==>
     Db INTER Vb = {} ==> sc SUBSET Vc ==> sb SUBSET Vb ==> sa SUBSET Va ==>
     ~(sb DIFF (Da INTER Vb UNION Dc INTER Vb UNION Dd INTER Vb UNION
                sb INTER Va UNION sb INTER Vc UNION sb INTER Vd) = {}) ==>
     ~(sb DIFF (Da INTER Vb UNION Dc INTER Vb UNION Dd INTER Vb UNION
                sb INTER Va UNION sb INTER Vc UNION sb INTER Vd) SUBSET om /\
       sb DIFF (Da INTER Vb UNION Dc INTER Vb UNION Dd INTER Vb UNION
                sb INTER Va UNION sb INTER Vc UNION sb INTER Vd) SUBSET om')`,
  REPEAT GEN_TAC THEN REPLICATE_TAC 6 DISCH_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `y:real^3` o REWRITE_RULE[GSYM MEMBER_NOT_EMPTY]) THEN
  REWRITE_TAC[SUBSET] THEN
  DISCH_THEN(CONJUNCTS_THEN (MP_TAC o SPEC `y:real^3`)) THEN ASM_REWRITE_TAC[] THEN
  REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `(y:real^3) IN om INTER om'` MP_TAC THENL
   [ASM_REWRITE_TAC[IN_INTER]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `(y:real^3) IN sb DIFF (Da INTER Vb UNION Dc INTER Vb UNION Dd INTER Vb UNION
                sb INTER Va UNION sb INTER Vc UNION sb INTER Vd)` THEN
  REWRITE_TAC[IN_DIFF; IN_UNION; IN_INTER] THEN
  MAP_EVERY UNDISCH_TAC [`Db INTER Vb:real^3->bool = {}`; `sc SUBSET Vc:real^3->bool`;
    `sb SUBSET Vb:real^3->bool`; `sa SUBSET Va:real^3->bool`] THEN
  REWRITE_TAC[SUBSET; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN MESON_TAC[]);;

(* The open part of a hexagon at b misses the circle: it is not on both sides. *)

let MOI_S4X_HINT = prove
 (`!V R D J C C' a b c d sa sa' sb sb' sc sc' sd sd' om om'.
     moi_s4x_ctx V R D J C C' a b c d sa sa' sb sb' sc sc' sd sd' /\
     moi_s4x_split V D a b c d sa sb sb' sc sd sd' om om'
     ==> ~(sb DIFF ((D a INTER V b) UNION (D c INTER V b) UNION (D d INTER V b) UNION
                    (sb INTER V a) UNION (sb INTER V c) UNION (sb INTER V d)) SUBSET om /\
           sb DIFF ((D a INTER V b) UNION (D c INTER V b) UNION (D d INTER V b) UNION
                    (sb INTER V a) UNION (sb INTER V c) UNION (sb INTER V d)) SUBSET om')`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4X_CTX_FACTS) THEN
  UNDISCH_TAC `moi_s4x_split V (D:num->real^3->bool) a b c d sa sb sb' sc sd sd' om (om':real^3->bool)` THEN
  REWRITE_TAC[moi_s4x_split] THEN STRIP_TAC THEN
  UNDISCH_TAC `moi_s4x_ctx V R D (J:num->real^3->bool) (C:num->num->real^3->bool) (C':num->num->real^3->bool) a b c d sa sa' sb sb' sc sc' sd (sd':real^3->bool)` THEN
  REWRITE_TAC[moi_s4x_ctx] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:num->real^3->bool`; `R:num->num->real^3->bool`; `D:num->real^3->bool`;
                 `J:num->real^3->bool`; `C:num->num->real^3->bool`;
                 `C':num->num->real^3->bool`; `b:num`; `a:num`; `c:num`; `d:num`;
                 `sb:real^3->bool`; `sb':real^3->bool`] MOI_S4X_HEX_EXPAND) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(ASSUME_TAC o CONJUNCT1)] THEN
  FIRST_X_ASSUM(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o
    MATCH_MP MOI_S4L_PL_CELL2_TOPO) THEN
  MAP_EVERY UNDISCH_TAC
   [`(sa:real^3->bool) SUBSET (V:num->real^3->bool) a`;
    `(sb:real^3->bool) SUBSET (V:num->real^3->bool) b`;
    `(sc:real^3->bool) SUBSET (V:num->real^3->bool) c`;
    `(D:num->real^3->bool) b INTER (V:num->real^3->bool) b = {}`;
    `om INTER om' =
     (sa UNION sc UNION (D:num->real^3->bool) a UNION D b UNION D c UNION D d) INTER
     ((V:num->real^3->bool) b UNION V d)`] THEN
  MATCH_ACCEPT_TAC SPDR9_HINT_SET);;

(* Rename the two hexagons at b (and at d) in the context and the split. *)

let MOI_S4X_CTX_CHOICE = prove
 (`!V R D J C C' a b c d sa sa' sb sb' sc sc' sd sd' tb tb' td td'.
     moi_s4x_ctx V R D J C C' a b c d sa sa' sb sb' sc sc' sd sd' /\
     ((tb = sb /\ tb' = sb') \/ (tb = sb' /\ tb' = sb)) /\
     ((td = sd /\ td' = sd') \/ (td = sd' /\ td' = sd))
     ==> moi_s4x_ctx V R D J C C' a b c d sa sa' tb tb' sc sc' td td'`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN
    (DISJ_CASES_THEN (CONJUNCTS_THEN SUBST1_TAC)))) THEN
  ASM_MESON_TAC[MOI_S4X_CTX_SWAP]);;

let MOI_S4X_SPLIT_CHOICE = prove
 (`!V D a b c d sa sb sb' sc sd sd' om om' tb tb' td td'.
     moi_s4x_split V D a b c d sa sb sb' sc sd sd' om om' /\
     ((tb = sb /\ tb' = sb') \/ (tb = sb' /\ tb' = sb)) /\
     ((td = sd /\ td' = sd') \/ (td = sd' /\ td' = sd))
     ==> moi_s4x_split V D a b c d sa tb tb' sc td td' om om'`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN
    (DISJ_CASES_THEN (CONJUNCTS_THEN SUBST1_TAC)))) THEN
  ASM_MESON_TAC[MOI_S4X_SPLIT_SWAP]);;

(* The splitting disk V b INTER V a is not on both sides. *)

let MOI_S4X_HNOT2 = prove
 (`!V R D J C C' a b c d sa sa' sb sb' sc sc' sd sd' om om'.
     moi_s4x_ctx V R D J C C' a b c d sa sa' sb sb' sc sc' sd sd' /\
     moi_s4x_split V D a b c d sa sb sb' sc sd sd' om om'
     ==> ~((V b INTER V a) DIFF R b a SUBSET om /\ (V b INTER V a) DIFF R b a SUBSET om')`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL MOI_S4X_ZOM) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL MOI_S4X_UNIF_H) THEN ASM_REWRITE_TAC[] THEN SIMP_TAC[]);;

(* At b: when both splitting disks at b are on the om' side, the hexagon    *)
(* at b sharing the rim arc of sa also shares the rim arc of sc, and its    *)
(* open part is on the om side.                                             *)

let MOI_S4X_CONSIST_B = prove
 (`!V R D J C C' a b c d sa sa' sb sb' sc sc' sd sd' om om'.
     moi_s4x_ctx V R D J C C' a b c d sa sa' sb sb' sc sc' sd sd' /\
     moi_s4x_split V D a b c d sa sb sb' sc sd sd' om om' /\
     (V b INTER V a) DIFF R b a SUBSET om' /\ (V b INTER V c) DIFF R b c SUBSET om'
     ==> ?tb tb'. ((tb = sb /\ tb' = sb') \/ (tb = sb' /\ tb' = sb)) /\
                  tb INTER V a = sa INTER V b /\ tb INTER V c = sc INTER V b /\
                  tb DIFF ((D a INTER V b) UNION (D c INTER V b) UNION (D d INTER V b) UNION
                           (tb INTER V a) UNION (tb INTER V c) UNION (tb INTER V d)) SUBSET om /\
                  tb' DIFF ((D a INTER V b) UNION (D c INTER V b) UNION (D d INTER V b) UNION
                            (tb' INTER V a) UNION (tb' INTER V c) UNION (tb' INTER V d))
                  SUBSET om'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `moi_s4x_tconf V (R:num->num->real^3->bool) (D:num->real^3->bool) (J:num->real^3->bool) /\
    moi_s4x_rimarcs V R D (C:num->num->real^3->bool) (C':num->num->real^3->bool) /\
    moi_s4x_hex V D C C' a sa sa' /\ moi_s4x_hex V D C C' b sb sb' /\
    moi_s4x_hex V D C C' c sc sc' /\
    a < 4 /\ b < 4 /\ c < 4 /\ d < 4 /\
    ~(a = b) /\ ~(a = c) /\ ~(a = d) /\ ~(b = c) /\ ~(b = d) /\ ~(c = d)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `moi_s4x_ctx V R D (J:num->real^3->bool) (C:num->num->real^3->bool)
                   (C':num->num->real^3->bool) a b c d sa sa' sb sb' sc sc' sd (sd':real^3->bool)` THEN
    REWRITE_TAC[moi_s4x_ctx] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:num->real^3->bool`; `R:num->num->real^3->bool`; `D:num->real^3->bool`;
                 `J:num->real^3->bool`; `C:num->num->real^3->bool`;
                 `C':num->num->real^3->bool`; `a:num`; `b:num`;
                 `sa:real^3->bool`; `sa':real^3->bool`; `sb:real^3->bool`; `sb':real^3->bool`]
                MOI_S4X_PICK) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `tb:real^3->bool` (X_CHOOSE_THEN `tb':real^3->bool`
    (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`V:num->real^3->bool`; `R:num->num->real^3->bool`; `D:num->real^3->bool`;
                 `J:num->real^3->bool`; `C:num->num->real^3->bool`;
                 `C':num->num->real^3->bool`; `c:num`; `b:num`;
                 `sc:real^3->bool`; `sc':real^3->bool`; `sb:real^3->bool`; `sb':real^3->bool`]
                MOI_S4X_PICK) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `ub:real^3->bool` (X_CHOOSE_THEN `ub':real^3->bool`
    (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC))) THEN
  (* the renamed contexts *)
  SUBGOAL_THEN
   `moi_s4x_ctx V R D J C C' a b c d sa sa' tb tb' sc sc' sd sd' /\
    moi_s4x_split V D a b c d sa tb tb' sc sd sd' om om' /\
    moi_s4x_ctx V R D J C C' a b c d sa sa' tb' tb sc sc' sd sd' /\
    moi_s4x_split V D a b c d sa tb' tb sc sd sd' om om' /\
    moi_s4x_ctx V R D J C C' c b a d sc sc' ub ub' sa sa' sd sd' /\
    moi_s4x_split V D c b a d sc ub ub' sa sd sd' om om'`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MOI_S4X_CTX_CHOICE THEN
      MAP_EVERY EXISTS_TAC [`sb:real^3->bool`; `sb':real^3->bool`;
                            `sd:real^3->bool`; `sd':real^3->bool`] THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC MOI_S4X_SPLIT_CHOICE THEN
      MAP_EVERY EXISTS_TAC [`sb:real^3->bool`; `sb':real^3->bool`;
                            `sd:real^3->bool`; `sd':real^3->bool`] THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC MOI_S4X_CTX_CHOICE THEN
      MAP_EVERY EXISTS_TAC [`sb:real^3->bool`; `sb':real^3->bool`;
                            `sd:real^3->bool`; `sd':real^3->bool`] THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(tb = sb /\ tb' = sb') \/ (tb = sb' /\ tb' = (sb:real^3->bool))` THEN
      MESON_TAC[];
      MATCH_MP_TAC MOI_S4X_SPLIT_CHOICE THEN
      MAP_EVERY EXISTS_TAC [`sb:real^3->bool`; `sb':real^3->bool`;
                            `sd:real^3->bool`; `sd':real^3->bool`] THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(tb = sb /\ tb' = sb') \/ (tb = sb' /\ tb' = (sb:real^3->bool))` THEN
      MESON_TAC[];
      MATCH_MP_TAC MOI_S4X_CTX_CHOICE THEN
      MAP_EVERY EXISTS_TAC [`sb:real^3->bool`; `sb':real^3->bool`;
                            `sd:real^3->bool`; `sd':real^3->bool`] THEN
      ASM_SIMP_TAC[MOI_S4X_CTX_SWAP];
      MATCH_MP_TAC MOI_S4X_SPLIT_CHOICE THEN
      MAP_EVERY EXISTS_TAC [`sb:real^3->bool`; `sb':real^3->bool`;
                            `sd:real^3->bool`; `sd':real^3->bool`] THEN
      ASM_SIMP_TAC[MOI_S4X_SPLIT_SWAP]];
    ALL_TAC] THEN
  (* RIM2 at tb, and at ub in the swapped context *)
  SUBGOAL_THEN
   `tb DIFF (((D:num->real^3->bool) a INTER (V:num->real^3->bool) b) UNION (D c INTER V b) UNION
             (D d INTER V b) UNION (tb INTER V a) UNION (tb INTER V c) UNION (tb INTER V d))
    SUBSET om`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`V:num->real^3->bool`; `R:num->num->real^3->bool`; `D:num->real^3->bool`;
                   `J:num->real^3->bool`; `C:num->num->real^3->bool`;
                   `C':num->num->real^3->bool`; `a:num`; `b:num`; `c:num`; `d:num`;
                   `sa:real^3->bool`; `sa':real^3->bool`; `tb:real^3->bool`; `tb':real^3->bool`;
                   `sc:real^3->bool`; `sc':real^3->bool`; `sd:real^3->bool`; `sd':real^3->bool`;
                   `om:real^3->bool`; `om':real^3->bool`] MOI_S4X_RIM2) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`V:num->real^3->bool`; `R:num->num->real^3->bool`; `D:num->real^3->bool`;
                   `J:num->real^3->bool`; `C:num->num->real^3->bool`;
                   `C':num->num->real^3->bool`; `a:num`; `b:num`; `c:num`; `d:num`;
                   `sa:real^3->bool`; `sa':real^3->bool`; `tb:real^3->bool`; `tb':real^3->bool`;
                   `sc:real^3->bool`; `sc':real^3->bool`; `sd:real^3->bool`; `sd':real^3->bool`;
                   `om:real^3->bool`; `om':real^3->bool`] MOI_S4X_HNOT2) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `((V:num->real^3->bool) b INTER V a) DIFF (R:num->num->real^3->bool) b a
                 SUBSET om'` THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ub DIFF (((D:num->real^3->bool) a INTER (V:num->real^3->bool) b) UNION (D c INTER V b) UNION
             (D d INTER V b) UNION (ub INTER V a) UNION (ub INTER V c) UNION (ub INTER V d))
    SUBSET om`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`V:num->real^3->bool`; `R:num->num->real^3->bool`; `D:num->real^3->bool`;
                   `J:num->real^3->bool`; `C:num->num->real^3->bool`;
                   `C':num->num->real^3->bool`; `c:num`; `b:num`; `a:num`; `d:num`;
                   `sc:real^3->bool`; `sc':real^3->bool`; `ub:real^3->bool`; `ub':real^3->bool`;
                   `sa:real^3->bool`; `sa':real^3->bool`; `sd:real^3->bool`; `sd':real^3->bool`;
                   `om:real^3->bool`; `om':real^3->bool`] MOI_S4X_RIM2) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`V:num->real^3->bool`; `R:num->num->real^3->bool`; `D:num->real^3->bool`;
                   `J:num->real^3->bool`; `C:num->num->real^3->bool`;
                   `C':num->num->real^3->bool`; `c:num`; `b:num`; `a:num`; `d:num`;
                   `sc:real^3->bool`; `sc':real^3->bool`; `ub:real^3->bool`; `ub':real^3->bool`;
                   `sa:real^3->bool`; `sa':real^3->bool`; `sd:real^3->bool`; `sd':real^3->bool`;
                   `om:real^3->bool`; `om':real^3->bool`] MOI_S4X_HNOT2) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `((V:num->real^3->bool) b INTER V c) DIFF (R:num->num->real^3->bool) b c
                 SUBSET om'` THEN
    SUBGOAL_THEN
     `ub DIFF (((D:num->real^3->bool) c INTER (V:num->real^3->bool) b) UNION (D a INTER V b) UNION
               (D d INTER V b) UNION (ub INTER V c) UNION (ub INTER V a) UNION (ub INTER V d)) =
      ub DIFF ((D a INTER V b) UNION (D c INTER V b) UNION
               (D d INTER V b) UNION (ub INTER V a) UNION (ub INTER V c) UNION (ub INTER V d))`
    SUBST1_TAC THENL [AP_TERM_TAC THEN REWRITE_TAC[UNION_ACI]; MESON_TAC[]];
    ALL_TAC] THEN
  (* RIM1 and HINT at the original pair sb, sb' *)
  MP_TAC(ISPECL [`V:num->real^3->bool`; `R:num->num->real^3->bool`; `D:num->real^3->bool`;
                 `J:num->real^3->bool`; `C:num->num->real^3->bool`;
                 `C':num->num->real^3->bool`; `a:num`; `b:num`; `c:num`; `d:num`;
                 `sa:real^3->bool`; `sa':real^3->bool`; `tb:real^3->bool`; `tb':real^3->bool`;
                 `sc:real^3->bool`; `sc':real^3->bool`; `sd:real^3->bool`; `sd':real^3->bool`;
                 `om:real^3->bool`; `om':real^3->bool`] MOI_S4X_RIM1) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`V:num->real^3->bool`; `R:num->num->real^3->bool`; `D:num->real^3->bool`;
                 `J:num->real^3->bool`; `C:num->num->real^3->bool`;
                 `C':num->num->real^3->bool`; `a:num`; `b:num`; `c:num`; `d:num`;
                 `sa:real^3->bool`; `sa':real^3->bool`; `tb:real^3->bool`; `tb':real^3->bool`;
                 `sc:real^3->bool`; `sc':real^3->bool`; `sd:real^3->bool`; `sd':real^3->bool`;
                 `om:real^3->bool`; `om':real^3->bool`] MOI_S4X_HINT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`V:num->real^3->bool`; `R:num->num->real^3->bool`; `D:num->real^3->bool`;
                 `J:num->real^3->bool`; `C:num->num->real^3->bool`;
                 `C':num->num->real^3->bool`; `a:num`; `b:num`; `c:num`; `d:num`;
                 `sa:real^3->bool`; `sa':real^3->bool`; `tb':real^3->bool`; `tb:real^3->bool`;
                 `sc:real^3->bool`; `sc':real^3->bool`; `sd:real^3->bool`; `sd':real^3->bool`;
                 `om:real^3->bool`; `om':real^3->bool`] MOI_S4X_HINT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `ub:real^3->bool = tb` ASSUME_TAC THENL
   [SUBGOAL_THEN `ub:real^3->bool = tb \/ ub = tb'` MP_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       [`(tb = sb /\ tb' = sb') \/ (tb = sb' /\ tb' = (sb:real^3->bool))`;
        `(ub = sb /\ ub' = sb') \/ (ub = sb' /\ ub' = (sb:real^3->bool))`] THEN
      MESON_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(DISJ_CASES_THEN SUBST_ALL_TAC) THEN REWRITE_TAC[] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`tb:real^3->bool`; `tb':real^3->bool`] THEN
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [UNDISCH_TAC `(ub:real^3->bool) INTER (V:num->real^3->bool) c = sc INTER V b` THEN
    ASM_REWRITE_TAC[];
    ASM_MESON_TAC[]]);;

(* A 2-cell whose open part lies in a closed set lies in it. *)

let MOI_S4X_CELL_CLOSE = prove
 (`!p bp om:real^N->bool.
     pl_cell_with_boundary 2 p bp /\ closed om /\ p DIFF bp SUBSET om ==> p SUBSET om`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4L_PL_CELL2_TOPO) THEN
  MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `closure(p DIFF bp:real^N->bool)` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CLOSURE_MINIMAL THEN ASM_REWRITE_TAC[]);;

let SPDR9_CROSS_SET = prove
 (`!(y:real^3) e1 e2 sb sd sd' om om' sa sc Da Db Dc Dd Va Vb Vc Vd.
     ~(y = e2) ==> ~(y = e1) ==> y IN sb INTER Vd ==> sb INTER Vd = sd' INTER Vb ==>
     sd' SUBSET om' ==> sb SUBSET om ==>
     om INTER om' = (sa UNION sc UNION Da UNION Db UNION Dc UNION Dd) INTER (Vb UNION Vd) ==>
     Dc INTER Vb INTER Vd = {e2} ==> Da INTER Vb INTER Vd = {e1} ==> Dd INTER Vd = {} ==>
     Db INTER Vb = {} ==> Vb INTER Vc INTER Vd = {} ==> Va INTER Vb INTER Vd = {} ==>
     sc SUBSET Vc ==> sa SUBSET Va ==> sb INTER Vd = sd INTER Vb`,
  REPEAT GEN_TAC THEN REWRITE_TAC[SUBSET; EXTENSION; IN_INTER; IN_UNION; NOT_IN_EMPTY; IN_SING] THEN
  REPEAT DISCH_TAC THEN MATCH_MP_TAC(TAUT `F ==> p`) THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `y:real^3`)) THEN
  REPEAT(FIRST_X_ASSUM MP_TAC) THEN CONV_TAC TAUT);;

(* The rim arcs at the cross edge V b INTER V d agree when the open parts   *)
(* of sb and sd are on the om side and that of sd' on the om' side.         *)

let MOI_S4X_CROSS = prove
 (`!V R D J C C' a b c d sa sa' sb sb' sc sc' sd sd' om om'.
     moi_s4x_ctx V R D J C C' a b c d sa sa' sb sb' sc sc' sd sd' /\
     moi_s4x_split V D a b c d sa sb sb' sc sd sd' om om' /\
     sb DIFF ((D a INTER V b) UNION (D c INTER V b) UNION (D d INTER V b) UNION
              (sb INTER V a) UNION (sb INTER V c) UNION (sb INTER V d)) SUBSET om /\
     sd' DIFF ((D a INTER V d) UNION (D c INTER V d) UNION (D b INTER V d) UNION
               (sd' INTER V a) UNION (sd' INTER V c) UNION (sd' INTER V b)) SUBSET om'
     ==> sb INTER V d = sd INTER V b`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4X_CTX_FACTS) THEN
  UNDISCH_TAC `moi_s4x_split V (D:num->real^3->bool) a b c d sa sb sb' sc sd sd' om (om':real^3->bool)` THEN
  REWRITE_TAC[moi_s4x_split] THEN STRIP_TAC THEN
  UNDISCH_TAC `moi_s4x_ctx V R D (J:num->real^3->bool) (C:num->num->real^3->bool) (C':num->num->real^3->bool) a b c d sa sa' sb sb' sc sc' sd (sd':real^3->bool)` THEN
  REWRITE_TAC[moi_s4x_ctx] THEN STRIP_TAC THEN
  MOI_S4X_EQ2SUB_TAC `(sa:real^3->bool) INTER (V:num->real^3->bool) c = sc INTER V a` THEN
  SUBGOAL_THEN `closed(om:real^3->bool) /\ closed(om':real^3->bool)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_S4L_PL_CELL_FACTS; COMPACT_IMP_CLOSED]; ALL_TAC] THEN
  MP_TAC(ISPECL [`V:num->real^3->bool`; `R:num->num->real^3->bool`; `D:num->real^3->bool`;
                 `J:num->real^3->bool`; `C:num->num->real^3->bool`;
                 `C':num->num->real^3->bool`; `b:num`; `a:num`; `c:num`; `d:num`;
                 `sb:real^3->bool`; `sb':real^3->bool`] MOI_S4X_HEX_EXPAND) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> LABEL_TAC "cb" (CONJUNCT1 th) THEN
                       LABEL_TAC "xb" (last(CONJUNCTS th))) THEN
  MP_TAC(ISPECL [`V:num->real^3->bool`; `R:num->num->real^3->bool`; `D:num->real^3->bool`;
                 `J:num->real^3->bool`; `C:num->num->real^3->bool`;
                 `C':num->num->real^3->bool`; `d:num`; `a:num`; `c:num`; `b:num`;
                 `sd:real^3->bool`; `sd':real^3->bool`] MOI_S4X_HEX_EXPAND) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> LABEL_TAC "cd" (CONJUNCT1(CONJUNCT2 th)) THEN
                       LABEL_TAC "xd" (last(CONJUNCTS th))) THEN
  SUBGOAL_THEN `(sb:real^3->bool) SUBSET om /\ (sd':real^3->bool) SUBSET om'` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC MOI_S4X_CELL_CLOSE THEN ASM_REWRITE_TAC[] THENL
     [EXISTS_TAC
       `((D:num->real^3->bool) a INTER (V:num->real^3->bool) b) UNION (D c INTER V b) UNION
        (D d INTER V b) UNION (sb INTER V a) UNION (sb INTER V c) UNION (sb INTER V d)` THEN
      ASM_REWRITE_TAC[];
      EXISTS_TAC
       `((D:num->real^3->bool) a INTER (V:num->real^3->bool) d) UNION (D c INTER V d) UNION
        (D b INTER V d) UNION (sd' INTER V a) UNION (sd' INTER V c) UNION (sd' INTER V b)` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  UNDISCH_TAC `moi_s4x_rimarcs V (R:num->num->real^3->bool) (D:num->real^3->bool) (C:num->num->real^3->bool) (C':num->num->real^3->bool)` THEN
  REWRITE_TAC[moi_s4x_rimarcs] THEN
  DISCH_THEN(MP_TAC o SPECL [`b:num`; `d:num`; `a:num`; `c:num`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  UNDISCH_TAC `moi_s4x_tconf V (R:num->num->real^3->bool) (D:num->real^3->bool) (J:num->real^3->bool)` THEN MOI_S4X_TC_TAC THEN
  USE_THEN "fpt" (MP_TAC o SPECL [`a:num`; `b:num`; `d:num`; `c:num`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `e1:real^3` o CONJUNCT1) THEN
  USE_THEN "fpt" (MP_TAC o SPECL [`c:num`; `b:num`; `d:num`; `a:num`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `e2:real^3` o CONJUNCT1) THEN
  SUBGOAL_THEN `pl_cell_with_boundary 1 ((sb:real^3->bool) INTER (V:num->real^3->bool) d) {e1:real^3,e2}`
  MP_TAC THENL
   [SUBGOAL_THEN `{e1:real^3,e2} = ((D:num->real^3->bool) a INTER (V:num->real^3->bool) b INTER V d)
                                   UNION (D c INTER V b INTER V d)` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[] THEN SET_TAC[]; ALL_TAC] THEN
    REMOVE_THEN "xb" (DISJ_CASES_THEN (SUBST1_TAC o CONJUNCT1)) THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC o MATCH_MP MOI_S4X_CELL1_MID) THEN
  SUBGOAL_THEN `(sb:real^3->bool) INTER (V:num->real^3->bool) d = sd INTER V b \/
                sb INTER V d = sd' INTER V b`
  MP_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`(C:num->num->real^3->bool) d b = C b d`; `(C':num->num->real^3->bool) d b = C' b d`] THEN
    USE_THEN "xb" MP_TAC THEN USE_THEN "xd" MP_TAC THEN MESON_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(DISJ_CASES_THEN2 ACCEPT_TAC ASSUME_TAC) THEN
  MAP_EVERY UNDISCH_TAC
   [`(sa:real^3->bool) SUBSET (V:num->real^3->bool) a`;
    `(sc:real^3->bool) SUBSET (V:num->real^3->bool) c`;
    `(V:num->real^3->bool) a INTER V b INTER V d = {}`;
    `(V:num->real^3->bool) b INTER V c INTER V d = {}`;
    `(D:num->real^3->bool) b INTER (V:num->real^3->bool) b = {}`;
    `(D:num->real^3->bool) d INTER (V:num->real^3->bool) d = {}`;
    `(D:num->real^3->bool) a INTER (V:num->real^3->bool) b INTER V d = {e1:real^3}`;
    `(D:num->real^3->bool) c INTER (V:num->real^3->bool) b INTER V d = {e2:real^3}`;
    `om INTER om' =
     (sa UNION sc UNION (D:num->real^3->bool) a UNION D b UNION D c UNION D d) INTER
     ((V:num->real^3->bool) b UNION V d)`;
    `(sb:real^3->bool) SUBSET om`; `(sd':real^3->bool) SUBSET om'`;
    `(sb:real^3->bool) INTER (V:num->real^3->bool) d = sd' INTER V b`;
    `(y:real^3) IN (sb:real^3->bool) INTER (V:num->real^3->bool) d`;
    `~(y:real^3 = e1)`; `~(y:real^3 = e2)`] THEN
  MATCH_ACCEPT_TAC SPDR9_CROSS_SET);;

(* The split exists: the boundary circle of the disk Z cuts the sphere.     *)

let MOI_S4X_SPLIT_EX = prove
 (`!V R D J C C' a b c d sa sa' sb sb' sc sc' sd sd'.
     moi_s4x_ctx V R D J C C' a b c d sa sa' sb sb' sc sc' sd sd'
     ==> ?om om'. moi_s4x_split V D a b c d sa sb sb' sc sd sd' om om'`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4X_CTX_FACTS) THEN
  UNDISCH_TAC `moi_s4x_ctx V R D (J:num->real^3->bool) (C:num->num->real^3->bool) (C':num->num->real^3->bool) a b c d sa sa' sb sb' sc sc' sd (sd':real^3->bool)` THEN
  REWRITE_TAC[moi_s4x_ctx] THEN STRIP_TAC THEN
  REWRITE_TAC[moi_s4x_split] THEN MATCH_MP_TAC SPHERE_SPLIT THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MOI_S4X_SIG THEN
    MAP_EVERY EXISTS_TAC [`R:num->num->real^3->bool`; `D:num->real^3->bool`; `J:num->real^3->bool`;
                          `C:num->num->real^3->bool`; `C':num->num->real^3->bool`] THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOI_SCX_CELL_SPHERE THEN
    EXISTS_TAC `sa UNION sc UNION (D:num->real^3->bool) a UNION D b UNION D c UNION D d` THEN
    MATCH_MP_TAC MOI_S4X_ZDISK THEN
    MAP_EVERY EXISTS_TAC [`R:num->num->real^3->bool`; `J:num->real^3->bool`;
                          `C:num->num->real^3->bool`; `C':num->num->real^3->bool`;
                          `sa':real^3->bool`; `sc':real^3->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:num->real^3->bool`; `R:num->num->real^3->bool`; `D:num->real^3->bool`;
                 `J:num->real^3->bool`; `C:num->num->real^3->bool`;
                 `C':num->num->real^3->bool`; `b:num`; `a:num`; `c:num`; `d:num`;
                 `sb:real^3->bool`; `sb':real^3->bool`] MOI_S4X_HEX_EXPAND) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(ASSUME_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
  MP_TAC(ISPECL [`V:num->real^3->bool`; `R:num->num->real^3->bool`; `D:num->real^3->bool`;
                 `J:num->real^3->bool`; `C:num->num->real^3->bool`;
                 `C':num->num->real^3->bool`; `d:num`; `a:num`; `c:num`; `b:num`;
                 `sd:real^3->bool`; `sd':real^3->bool`] MOI_S4X_HEX_EXPAND) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(ASSUME_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
  MAP_EVERY UNDISCH_TAC
   [`(sa:real^3->bool) SUBSET (V:num->real^3->bool) a`;
    `(sc:real^3->bool) SUBSET (V:num->real^3->bool) c`;
    `(D:num->real^3->bool) b INTER (V:num->real^3->bool) b = {}`;
    `(D:num->real^3->bool) d INTER (V:num->real^3->bool) d = {}`;
    `sb INTER sb' =
     ((D:num->real^3->bool) a INTER (V:num->real^3->bool) b) UNION (D c INTER V b) UNION
     (D d INTER V b)`;
    `sd INTER sd' =
     ((D:num->real^3->bool) a INTER (V:num->real^3->bool) d) UNION (D c INTER V d) UNION
     (D b INTER V d)`] THEN
  SET_TAC[]);;

(* The splitting disk V b INTER V a is on one side. *)

let MOI_S4X_HEITHER = prove
 (`!V R D J C C' a b c d sa sa' sb sb' sc sc' sd sd' om om'.
     moi_s4x_ctx V R D J C C' a b c d sa sa' sb sb' sc sc' sd sd' /\
     moi_s4x_split V D a b c d sa sb sb' sc sd sd' om om'
     ==> (V b INTER V a) DIFF R b a SUBSET om \/ (V b INTER V a) DIFF R b a SUBSET om'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL MOI_S4X_ZOM) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL MOI_S4X_UNIF_H) THEN ASM_REWRITE_TAC[] THEN SIMP_TAC[]);;

(* Consistency when the four cross splitting disks are on the om' side. *)

let MOI_S4X_CONSIST_SIDE = prove
 (`!V R D J C C' a b c d sa sa' sb sb' sc sc' sd sd' om om'.
     moi_s4x_ctx V R D J C C' a b c d sa sa' sb sb' sc sc' sd sd' /\
     moi_s4x_split V D a b c d sa sb sb' sc sd sd' om om' /\
     (V b INTER V a) DIFF R b a SUBSET om' /\ (V b INTER V c) DIFF R b c SUBSET om' /\
     (V d INTER V a) DIFF R d a SUBSET om' /\ (V d INTER V c) DIFF R d c SUBSET om'
     ==> ?tb tb' td td'. ((tb = sb /\ tb' = sb') \/ (tb = sb' /\ tb' = sb)) /\
                         ((td = sd /\ td' = sd') \/ (td = sd' /\ td' = sd)) /\
                         tb INTER V a = sa INTER V b /\ tb INTER V c = sc INTER V b /\
                         td INTER V a = sa INTER V d /\ td INTER V c = sc INTER V d /\
                         tb INTER V d = td INTER V b`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:num->real^3->bool`; `R:num->num->real^3->bool`; `D:num->real^3->bool`;
                 `J:num->real^3->bool`; `C:num->num->real^3->bool`;
                 `C':num->num->real^3->bool`; `a:num`; `b:num`; `c:num`; `d:num`;
                 `sa:real^3->bool`; `sa':real^3->bool`; `sb:real^3->bool`; `sb':real^3->bool`;
                 `sc:real^3->bool`; `sc':real^3->bool`; `sd:real^3->bool`; `sd':real^3->bool`;
                 `om:real^3->bool`; `om':real^3->bool`] MOI_S4X_CONSIST_B) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `tb:real^3->bool` (X_CHOOSE_THEN `tb':real^3->bool`
    (fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)))) THEN
  SUBGOAL_THEN
   `moi_s4x_ctx V R D J C C' a d c b sa sa' sd sd' sc sc' sb sb' /\
    moi_s4x_split V D a d c b sa sd sd' sc sb sb' om om'`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[MOI_S4X_CTX_SWAP; MOI_S4X_SPLIT_SWAP]; ALL_TAC] THEN
  MP_TAC(ISPECL [`V:num->real^3->bool`; `R:num->num->real^3->bool`; `D:num->real^3->bool`;
                 `J:num->real^3->bool`; `C:num->num->real^3->bool`;
                 `C':num->num->real^3->bool`; `a:num`; `d:num`; `c:num`; `b:num`;
                 `sa:real^3->bool`; `sa':real^3->bool`; `sd:real^3->bool`; `sd':real^3->bool`;
                 `sc:real^3->bool`; `sc':real^3->bool`; `sb:real^3->bool`; `sb':real^3->bool`;
                 `om:real^3->bool`; `om':real^3->bool`] MOI_S4X_CONSIST_B) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `td:real^3->bool` (X_CHOOSE_THEN `td':real^3->bool`
    (fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)))) THEN
  MAP_EVERY EXISTS_TAC [`tb:real^3->bool`; `tb':real^3->bool`;
                        `td:real^3->bool`; `td':real^3->bool`] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`V:num->real^3->bool`; `R:num->num->real^3->bool`; `D:num->real^3->bool`;
                 `J:num->real^3->bool`; `C:num->num->real^3->bool`;
                 `C':num->num->real^3->bool`; `a:num`; `b:num`; `c:num`; `d:num`;
                 `sa:real^3->bool`; `sa':real^3->bool`; `tb:real^3->bool`; `tb':real^3->bool`;
                 `sc:real^3->bool`; `sc':real^3->bool`; `td:real^3->bool`; `td':real^3->bool`;
                 `om:real^3->bool`; `om':real^3->bool`] MOI_S4X_CROSS) THEN
  ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC MOI_S4X_CTX_CHOICE THEN
    MAP_EVERY EXISTS_TAC [`sb:real^3->bool`; `sb':real^3->bool`;
                          `sd:real^3->bool`; `sd':real^3->bool`] THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOI_S4X_SPLIT_CHOICE THEN
    MAP_EVERY EXISTS_TAC [`sb:real^3->bool`; `sb':real^3->bool`;
                          `sd:real^3->bool`; `sd':real^3->bool`] THEN
    ASM_REWRITE_TAC[]]);;

(* Consistency: choices of hexagons at b and d sharing the rim arcs of sa   *)
(* and sc and sharing a rim arc on V b INTER V d.                           *)

let MOI_S4X_CONSIST = prove
 (`!V R D J C C' a b c d sa sa' sb sb' sc sc' sd sd'.
     moi_s4x_ctx V R D J C C' a b c d sa sa' sb sb' sc sc' sd sd'
     ==> ?tb tb' td td'. ((tb = sb /\ tb' = sb') \/ (tb = sb' /\ tb' = sb)) /\
                         ((td = sd /\ td' = sd') \/ (td = sd' /\ td' = sd)) /\
                         tb INTER V a = sa INTER V b /\ tb INTER V c = sc INTER V b /\
                         td INTER V a = sa INTER V d /\ td INTER V c = sc INTER V d /\
                         tb INTER V d = td INTER V b`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `om:real^3->bool` (X_CHOOSE_TAC `om':real^3->bool`) o
    MATCH_MP MOI_S4X_SPLIT_EX) THEN
  MP_TAC(SPEC_ALL MOI_S4X_UNIF) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `moi_s4x_ctx V R D J C C' c b a d sc sc' sb sb' sa sa' sd sd' /\
    moi_s4x_split V D c b a d sc sb sb' sa sd sd' om om' /\
    moi_s4x_ctx V R D J C C' a d c b sa sa' sd sd' sc sc' sb sb' /\
    moi_s4x_split V D a d c b sa sd sd' sc sb sb' om om' /\
    moi_s4x_ctx V R D J C C' c d a b sc sc' sd sd' sa sa' sb sb' /\
    moi_s4x_split V D c d a b sc sd sd' sa sb sb' om om' /\
    moi_s4x_split V D a b c d sa sb sb' sc sd sd' om' om`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[MOI_S4X_CTX_SWAP; MOI_S4X_SPLIT_SWAP]; ALL_TAC] THEN
  ASM_CASES_TAC `((V:num->real^3->bool) b INTER V a) DIFF (R:num->num->real^3->bool) b a SUBSET om` THENL
   [SUBGOAL_THEN
     `((V:num->real^3->bool) b INTER V c) DIFF (R:num->num->real^3->bool) b c SUBSET om /\
      (V d INTER V a) DIFF R d a SUBSET om /\ (V d INTER V c) DIFF R d c SUBSET om`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`V:num->real^3->bool`; `R:num->num->real^3->bool`; `D:num->real^3->bool`;
                   `J:num->real^3->bool`; `C:num->num->real^3->bool`;
                   `C':num->num->real^3->bool`; `a:num`; `b:num`; `c:num`; `d:num`;
                   `sa:real^3->bool`; `sa':real^3->bool`; `sb:real^3->bool`; `sb':real^3->bool`;
                   `sc:real^3->bool`; `sc':real^3->bool`; `sd:real^3->bool`; `sd':real^3->bool`;
                   `om':real^3->bool`; `om:real^3->bool`] MOI_S4X_CONSIST_SIDE) THEN
    ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((V:num->real^3->bool) b INTER V a) DIFF (R:num->num->real^3->bool) b a SUBSET om' /\
    (V b INTER V c) DIFF R b c SUBSET om' /\
    (V d INTER V a) DIFF R d a SUBSET om' /\ (V d INTER V c) DIFF R d c SUBSET om'`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`V:num->real^3->bool`; `R:num->num->real^3->bool`; `D:num->real^3->bool`;
                   `J:num->real^3->bool`; `C:num->num->real^3->bool`;
                   `C':num->num->real^3->bool`; `a:num`; `b:num`; `c:num`; `d:num`;
                   `sa:real^3->bool`; `sa':real^3->bool`; `sb:real^3->bool`; `sb':real^3->bool`;
                   `sc:real^3->bool`; `sc':real^3->bool`; `sd:real^3->bool`; `sd':real^3->bool`;
                   `om:real^3->bool`; `om':real^3->bool`] MOI_S4X_HEITHER) THEN
    ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    MP_TAC(ISPECL [`V:num->real^3->bool`; `R:num->num->real^3->bool`; `D:num->real^3->bool`;
                   `J:num->real^3->bool`; `C:num->num->real^3->bool`;
                   `C':num->num->real^3->bool`; `c:num`; `b:num`; `a:num`; `d:num`;
                   `sc:real^3->bool`; `sc':real^3->bool`; `sb:real^3->bool`; `sb':real^3->bool`;
                   `sa:real^3->bool`; `sa':real^3->bool`; `sd:real^3->bool`; `sd':real^3->bool`;
                   `om:real^3->bool`; `om':real^3->bool`] MOI_S4X_HEITHER) THEN
    ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    MP_TAC(ISPECL [`V:num->real^3->bool`; `R:num->num->real^3->bool`; `D:num->real^3->bool`;
                   `J:num->real^3->bool`; `C:num->num->real^3->bool`;
                   `C':num->num->real^3->bool`; `a:num`; `d:num`; `c:num`; `b:num`;
                   `sa:real^3->bool`; `sa':real^3->bool`; `sd:real^3->bool`; `sd':real^3->bool`;
                   `sc:real^3->bool`; `sc':real^3->bool`; `sb:real^3->bool`; `sb':real^3->bool`;
                   `om:real^3->bool`; `om':real^3->bool`] MOI_S4X_HEITHER) THEN
    ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    MP_TAC(ISPECL [`V:num->real^3->bool`; `R:num->num->real^3->bool`; `D:num->real^3->bool`;
                   `J:num->real^3->bool`; `C:num->num->real^3->bool`;
                   `C':num->num->real^3->bool`; `c:num`; `d:num`; `a:num`; `b:num`;
                   `sc:real^3->bool`; `sc':real^3->bool`; `sd:real^3->bool`; `sd':real^3->bool`;
                   `sa:real^3->bool`; `sa':real^3->bool`; `sb:real^3->bool`; `sb':real^3->bool`;
                   `om:real^3->bool`; `om':real^3->bool`] MOI_S4X_HEITHER) THEN
    ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    MAP_EVERY UNDISCH_TAC
     [`~(((V:num->real^3->bool) b INTER V a) DIFF (R:num->num->real^3->bool) b a SUBSET om)`;
      `((V:num->real^3->bool) b INTER V a) DIFF (R:num->num->real^3->bool) b a SUBSET om <=>
       (V b INTER V c) DIFF R b c SUBSET om`;
      `((V:num->real^3->bool) b INTER V a) DIFF (R:num->num->real^3->bool) b a SUBSET om <=>
       (V d INTER V a) DIFF R d a SUBSET om`;
      `((V:num->real^3->bool) b INTER V a) DIFF (R:num->num->real^3->bool) b a SUBSET om <=>
       (V d INTER V c) DIFF R d c SUBSET om`] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:num->real^3->bool`; `R:num->num->real^3->bool`; `D:num->real^3->bool`;
                 `J:num->real^3->bool`; `C:num->num->real^3->bool`;
                 `C':num->num->real^3->bool`; `a:num`; `b:num`; `c:num`; `d:num`;
                 `sa:real^3->bool`; `sa':real^3->bool`; `sb:real^3->bool`; `sb':real^3->bool`;
                 `sc:real^3->bool`; `sc':real^3->bool`; `sd:real^3->bool`; `sd':real^3->bool`;
                 `om:real^3->bool`; `om':real^3->bool`] MOI_S4X_CONSIST_SIDE) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The spheres of a consistent choice and the side choice.                  *)
(* SPHERE: Z and the disk glued from the hexagons at b and d share their    *)
(* boundary.  VSIDE: the four ball interiors lie on one side.  The           *)
(* complementary choice is consistent too (COMP); its sphere and the first  *)
(* cannot both have the balls inside (NOT_BOTH_INSIDE at a point of the     *)
(* open hexagon sa), so one of them has the four ball interiors outside     *)
(* (SIDE_CHOICE).                                                            *)
(* ------------------------------------------------------------------------- *)

(* A consistent choice of hexagons gives a PL 2-sphere: the disk Z and the *)
(* disk glued from the hexagons at b and d have the same boundary.          *)

let MOI_S4X_SPHERE = prove
 (`!V R D J C C' a b c d sa sa' sb sb' sc sc' sd sd'.
     moi_s4x_ctx V R D J C C' a b c d sa sa' sb sb' sc sc' sd sd' /\
     sb INTER V a = sa INTER V b /\ sb INTER V c = sc INTER V b /\
     sd INTER V a = sa INTER V d /\ sd INTER V c = sc INTER V d /\
     sb INTER V d = sd INTER V b
     ==> pl_sphere 2 ((sa UNION sc UNION D a UNION D b UNION D c UNION D d) UNION
                      (sb UNION sd))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4X_CTX_FACTS) THEN
  UNDISCH_TAC `moi_s4x_ctx V R D (J:num->real^3->bool) (C:num->num->real^3->bool) (C':num->num->real^3->bool) a b c d sa sa' sb sb' sc sc' sd (sd':real^3->bool)` THEN
  REWRITE_TAC[moi_s4x_ctx] THEN STRIP_TAC THEN
  MATCH_MP_TAC DISK_UNION THEN
  EXISTS_TAC `(sa UNION sc UNION (D:num->real^3->bool) a UNION D b UNION D c UNION D d) INTER
              ((V:num->real^3->bool) b UNION V d)` THEN
  SUBGOAL_THEN
   `pl_cell_with_boundary 2 (sa UNION sc UNION (D:num->real^3->bool) a UNION D b UNION D c UNION D d)
      ((sa UNION sc UNION D a UNION D b UNION D c UNION D d) INTER
       ((V:num->real^3->bool) b UNION V d))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S4X_ZDISK THEN
    MAP_EVERY EXISTS_TAC [`R:num->num->real^3->bool`; `J:num->real^3->bool`;
                          `C:num->num->real^3->bool`; `C':num->num->real^3->bool`;
                          `sa':real^3->bool`; `sc':real^3->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:num->real^3->bool`; `R:num->num->real^3->bool`; `D:num->real^3->bool`;
                 `J:num->real^3->bool`; `C:num->num->real^3->bool`;
                 `C':num->num->real^3->bool`; `b:num`; `a:num`; `d:num`; `c:num`;
                 `sb:real^3->bool`; `sb':real^3->bool`; `sd:real^3->bool`; `sd':real^3->bool`]
                MOI_S4X_XGLUE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN
   `((sb UNION sd) INTER ((V:num->real^3->bool) a UNION V c)) UNION
    (((D:num->real^3->bool) b INTER (V b UNION V d)) UNION (D a INTER (V b UNION V d)) UNION
     (D d INTER (V b UNION V d)) UNION (D c INTER (V b UNION V d))) =
    (sa UNION sc UNION D a UNION D b UNION D c UNION D d) INTER (V b UNION V d)`
  ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`(sb:real^3->bool) INTER (V:num->real^3->bool) a = sa INTER V b`;
      `(sb:real^3->bool) INTER (V:num->real^3->bool) c = sc INTER V b`;
      `(sd:real^3->bool) INTER (V:num->real^3->bool) a = sa INTER V d`;
      `(sd:real^3->bool) INTER (V:num->real^3->bool) c = sc INTER V d`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(sa UNION sc UNION (D:num->real^3->bool) a UNION D b UNION D c UNION D d) INTER
    ((V:num->real^3->bool) b UNION V d) SUBSET sb UNION sd`
  MP_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    FIRST_X_ASSUM(MATCH_ACCEPT_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o
      MATCH_MP MOI_S4L_PL_CELL_FACTS);
    ALL_TAC] THEN
  MAP_EVERY UNDISCH_TAC
   [`(sb:real^3->bool) SUBSET (V:num->real^3->bool) b`;
    `(sd:real^3->bool) SUBSET (V:num->real^3->bool) d`] THEN
  SET_TAC[]);;

(* The complementary hexagons of a consistent pair are consistent. *)

let MOI_S4X_COMP = prove
 (`!V R D J C C' i j p p' q q'.
     moi_s4x_tconf V R D J /\ moi_s4x_rimarcs V R D C C' /\
     moi_s4x_hex V D C C' i p p' /\ moi_s4x_hex V D C C' j q q' /\
     i < 4 /\ j < 4 /\ ~(i = j) /\ p INTER V j = q INTER V i
     ==> p' INTER V j = q' INTER V i`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`i:num`; `j:num`] MOI_S4X_OTHER2) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `l:num` STRIP_ASSUME_TAC)) THEN
  UNDISCH_TAC `moi_s4x_rimarcs V (R:num->num->real^3->bool) (D:num->real^3->bool)
                 (C:num->num->real^3->bool) (C':num->num->real^3->bool)` THEN
  REWRITE_TAC[moi_s4x_rimarcs] THEN
  DISCH_THEN(MP_TAC o SPECL [`i:num`; `j:num`; `k:num`; `l:num`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  UNDISCH_TAC `moi_s4x_hex V (D:num->real^3->bool) (C:num->num->real^3->bool)
                 (C':num->num->real^3->bool) i p p'` THEN
  REWRITE_TAC[moi_s4x_hex] THEN
  DISCH_THEN(MP_TAC o SPEC `j:num` o last o CONJUNCTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  UNDISCH_TAC `moi_s4x_hex V (D:num->real^3->bool) (C:num->num->real^3->bool)
                 (C':num->num->real^3->bool) j q q'` THEN
  REWRITE_TAC[moi_s4x_hex] THEN
  DISCH_THEN(MP_TAC o SPEC `i:num` o last o CONJUNCTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MAP_EVERY UNDISCH_TAC
   [`(p INTER (V:num->real^3->bool) j = (C:num->num->real^3->bool) i j /\
      p' INTER V j = (C':num->num->real^3->bool) i j) \/
     (p INTER V j = C' i j /\ p' INTER V j = C i j)`;
    `(q INTER (V:num->real^3->bool) i = (C:num->num->real^3->bool) j i /\
      q' INTER V i = (C':num->num->real^3->bool) j i) \/
     (q INTER V i = C' j i /\ q' INTER V i = C j i)`;
    `(C:num->num->real^3->bool) j i = C i j`;
    `(C':num->num->real^3->bool) j i = C' i j`;
    `(p:real^3->bool) INTER (V:num->real^3->bool) j = q INTER V i`] THEN
  MESON_TAC[]);;

(* The interior of a ball misses the other balls and the face disks. *)

let MOI_S4X_VINT = prove
 (`!V R D J x y l.
     moi_s4x_tconf V R D J /\ x < 4 /\ y < 4 /\ l < 4 /\ ~(x = y)
     ==> interior(V x) INTER V y = {} /\ interior(V x) INTER D l = {} /\
         interior(V x) INTER frontier(V x) = {}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `interior((V:num->real^3->bool) x) INTER frontier(V x) = {}` ASSUME_TAC THENL
   [REWRITE_TAC[frontier] THEN SET_TAC[]; ASM_REWRITE_TAC[]] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4X_TC_BASIC) THEN
  SUBGOAL_THEN `(D:num->real^3->bool) l INTER (V:num->real^3->bool) x SUBSET frontier(V x)`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (find_term ((=) `frontier:(real^3->bool)->real^3->bool`)) (concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `moi_s4x_tconf V (R:num->num->real^3->bool) (D:num->real^3->bool) (J:num->real^3->bool)` THEN
  MOI_S4X_TC_TAC THEN
  USE_THEN "edge" (MP_TAC o SPECL [`x:num`; `y:num`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPEC `(V:num->real^3->bool) x` INTERIOR_SUBSET) THEN
  MAP_EVERY UNDISCH_TAC
   [`interior((V:num->real^3->bool) x) INTER frontier(V x) = {}`;
    `(D:num->real^3->bool) l INTER (V:num->real^3->bool) x SUBSET frontier(V x)`;
    `(V:num->real^3->bool) x INTER V y SUBSET frontier(V x)`] THEN
  SET_TAC[]);;

(* The sphere of a context: its intersections with the balls. *)

let MOI_S4X_VS_FACTS = prove
 (`!V R D J C C' a b c d sa sa' sb sb' sc sc' sd sd'.
     moi_s4x_ctx V R D J C C' a b c d sa sa' sb sb' sc sc' sd sd'
     ==> interior(V a) INTER
         ((sa UNION sc UNION D a UNION D b UNION D c UNION D d) UNION (sb UNION sd)) = {} /\
         interior(V b) INTER
         ((sa UNION sc UNION D a UNION D b UNION D c UNION D d) UNION (sb UNION sd)) = {} /\
         interior(V c) INTER
         ((sa UNION sc UNION D a UNION D b UNION D c UNION D d) UNION (sb UNION sd)) = {} /\
         interior(V d) INTER
         ((sa UNION sc UNION D a UNION D b UNION D c UNION D d) UNION (sb UNION sd)) = {} /\
         ((sa UNION sc UNION D a UNION D b UNION D c UNION D d) UNION (sb UNION sd)) INTER
         (V a INTER V b) SUBSET R a b /\
         ((sa UNION sc UNION D a UNION D b UNION D c UNION D d) UNION (sb UNION sd)) INTER
         (V a INTER V c) SUBSET R a c /\
         ((sa UNION sc UNION D a UNION D b UNION D c UNION D d) UNION (sb UNION sd)) INTER
         (V a INTER V d) SUBSET R a d`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4X_CTX_FACTS) THEN
  UNDISCH_TAC `moi_s4x_ctx V R D (J:num->real^3->bool) (C:num->num->real^3->bool) (C':num->num->real^3->bool) a b c d sa sa' sb sb' sc sc' sd (sd':real^3->bool)` THEN
  REWRITE_TAC[moi_s4x_ctx] THEN STRIP_TAC THEN
  MOI_S4X_EQ2SUB_TAC `(sa:real^3->bool) INTER (V:num->real^3->bool) c = sc INTER V a` THEN
  MAP_EVERY (fun (i,p,q) ->
    MP_TAC(ISPECL [`V:num->real^3->bool`; `R:num->num->real^3->bool`; `D:num->real^3->bool`;
                   `J:num->real^3->bool`; `C:num->num->real^3->bool`;
                   `C':num->num->real^3->bool`; i; p; q] MOI_S4X_HEX_SUBSET) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC])
   [`a:num`,`sa:real^3->bool`,`sa':real^3->bool`;
    `b:num`,`sb:real^3->bool`,`sb':real^3->bool`;
    `c:num`,`sc:real^3->bool`,`sc':real^3->bool`;
    `d:num`,`sd:real^3->bool`,`sd':real^3->bool`] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4X_TC_BASIC) THEN
  FIRST_ASSUM(MP_TAC o check (fun th -> concl th =
    `moi_s4x_tconf (V:num->real^3->bool) (R:num->num->real^3->bool) (D:num->real^3->bool)
                   (J:num->real^3->bool)`)) THEN
  MOI_S4X_TC_TAC THEN
  (* for the pair x, y with hexagons px (pair px px') and py: the pieces of *)
  (* the sphere on V x INTER V y lie on the rim                              *)
  let rim_tac x y px px' py py' =
    MP_TAC(ISPECL [`V:num->real^3->bool`; `R:num->num->real^3->bool`; `D:num->real^3->bool`;
                   `J:num->real^3->bool`; `C:num->num->real^3->bool`;
                   `C':num->num->real^3->bool`; x; y; px; px'] MOI_S4X_HEX_RIM) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(MP_TAC o CONJUNCT1)] THEN
    MP_TAC(ISPECL [`V:num->real^3->bool`; `R:num->num->real^3->bool`; `D:num->real^3->bool`;
                   `J:num->real^3->bool`; `C:num->num->real^3->bool`;
                   `C':num->num->real^3->bool`; y; x; py; py'] MOI_S4X_HEX_RIM) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(MP_TAC o CONJUNCT1)] THEN
    USE_THEN "edge" (MP_TAC o SPECL [x; y]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(MP_TAC o CONJUNCT1)] THEN
    MAP_EVERY (fun l ->
      FIRST_ASSUM(MP_TAC o SPECL [l; x; y] o check (fun th ->
        is_forall(concl th) && length(fst(strip_forall(concl th))) = 3 &&
        can (find_term ((=) `R:num->num->real^3->bool`)) (concl th))) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC])
     [`a:num`; `b:num`; `c:num`; `d:num`] in
  REPEAT CONJ_TAC THENL
   [(* a *)
    MAP_EVERY (fun (y,l) ->
      MP_TAC(ISPECL [`V:num->real^3->bool`; `R:num->num->real^3->bool`; `D:num->real^3->bool`;
                     `J:num->real^3->bool`; `a:num`; y; l] MOI_S4X_VINT) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC])
     [`b:num`,`a:num`; `c:num`,`b:num`; `d:num`,`c:num`; `b:num`,`d:num`] THEN
    MAP_EVERY UNDISCH_TAC
     [`(sa:real^3->bool) SUBSET frontier((V:num->real^3->bool) a)`;
      `(sb:real^3->bool) SUBSET (V:num->real^3->bool) b`;
      `(sc:real^3->bool) SUBSET (V:num->real^3->bool) c`;
      `(sd:real^3->bool) SUBSET (V:num->real^3->bool) d`] THEN
    SET_TAC[];
    (* b *)
    MAP_EVERY (fun (y,l) ->
      MP_TAC(ISPECL [`V:num->real^3->bool`; `R:num->num->real^3->bool`; `D:num->real^3->bool`;
                     `J:num->real^3->bool`; `b:num`; y; l] MOI_S4X_VINT) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC])
     [`a:num`,`a:num`; `c:num`,`b:num`; `d:num`,`c:num`; `a:num`,`d:num`] THEN
    MAP_EVERY UNDISCH_TAC
     [`(sb:real^3->bool) SUBSET frontier((V:num->real^3->bool) b)`;
      `(sa:real^3->bool) SUBSET (V:num->real^3->bool) a`;
      `(sc:real^3->bool) SUBSET (V:num->real^3->bool) c`;
      `(sd:real^3->bool) SUBSET (V:num->real^3->bool) d`] THEN
    SET_TAC[];
    (* c *)
    MAP_EVERY (fun (y,l) ->
      MP_TAC(ISPECL [`V:num->real^3->bool`; `R:num->num->real^3->bool`; `D:num->real^3->bool`;
                     `J:num->real^3->bool`; `c:num`; y; l] MOI_S4X_VINT) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC])
     [`a:num`,`a:num`; `b:num`,`b:num`; `d:num`,`c:num`; `a:num`,`d:num`] THEN
    MAP_EVERY UNDISCH_TAC
     [`(sc:real^3->bool) SUBSET frontier((V:num->real^3->bool) c)`;
      `(sa:real^3->bool) SUBSET (V:num->real^3->bool) a`;
      `(sb:real^3->bool) SUBSET (V:num->real^3->bool) b`;
      `(sd:real^3->bool) SUBSET (V:num->real^3->bool) d`] THEN
    SET_TAC[];
    (* d *)
    MAP_EVERY (fun (y,l) ->
      MP_TAC(ISPECL [`V:num->real^3->bool`; `R:num->num->real^3->bool`; `D:num->real^3->bool`;
                     `J:num->real^3->bool`; `d:num`; y; l] MOI_S4X_VINT) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC])
     [`a:num`,`a:num`; `b:num`,`b:num`; `c:num`,`c:num`; `a:num`,`d:num`] THEN
    MAP_EVERY UNDISCH_TAC
     [`(sd:real^3->bool) SUBSET frontier((V:num->real^3->bool) d)`;
      `(sa:real^3->bool) SUBSET (V:num->real^3->bool) a`;
      `(sb:real^3->bool) SUBSET (V:num->real^3->bool) b`;
      `(sc:real^3->bool) SUBSET (V:num->real^3->bool) c`] THEN
    SET_TAC[];
rim_tac `a:num` `b:num` `sa:real^3->bool` `sa':real^3->bool`
            `sb:real^3->bool` `sb':real^3->bool` THEN
    MAP_EVERY UNDISCH_TAC
     [`(sc:real^3->bool) SUBSET (V:num->real^3->bool) c`;
      `(sd:real^3->bool) SUBSET (V:num->real^3->bool) d`;
      `(V:num->real^3->bool) a INTER V b INTER V c = {}`;
      `(V:num->real^3->bool) a INTER V b INTER V d = {}`] THEN
    SET_TAC[];
    rim_tac `a:num` `c:num` `sa:real^3->bool` `sa':real^3->bool`
            `sc:real^3->bool` `sc':real^3->bool` THEN
    MAP_EVERY UNDISCH_TAC
     [`(sb:real^3->bool) SUBSET (V:num->real^3->bool) b`;
      `(sd:real^3->bool) SUBSET (V:num->real^3->bool) d`;
      `(V:num->real^3->bool) a INTER V b INTER V c = {}`;
      `(V:num->real^3->bool) a INTER V c INTER V d = {}`] THEN
    SET_TAC[];
    rim_tac `a:num` `d:num` `sa:real^3->bool` `sa':real^3->bool`
            `sd:real^3->bool` `sd':real^3->bool` THEN
    MAP_EVERY UNDISCH_TAC
     [`(sb:real^3->bool) SUBSET (V:num->real^3->bool) b`;
      `(sc:real^3->bool) SUBSET (V:num->real^3->bool) c`;
      `(V:num->real^3->bool) a INTER V b INTER V d = {}`;
      `(V:num->real^3->bool) a INTER V c INTER V d = {}`] THEN
    SET_TAC[]]);;

(* Two balls whose interiors miss a sphere meeting it on their splitting   *)
(* disk only in the rim: interiors on the same side.                        *)

let MOI_S4X_PAIR_SAME = prove
 (`!V R D J x y s.
     moi_s4x_tconf V R D J /\ x < 4 /\ y < 4 /\ ~(x = y) /\ pl_sphere 2 s /\
     interior(V x) INTER s = {} /\ interior(V y) INTER s = {} /\
     s INTER (V x INTER V y) SUBSET R x y
     ==> (interior(V x) SUBSET inside s <=> interior(V y) SUBSET inside s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `moi_s4x_tconf V (R:num->num->real^3->bool) (D:num->real^3->bool) (J:num->real^3->bool)` THEN
  MOI_S4X_TC_TAC THEN
  USE_THEN "edge" (MP_TAC o SPECL [`x:num`; `y:num`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o
    MATCH_MP MOI_S4L_PL_CELL2_TOPO o check (fun th -> concl th =
    `pl_cell_with_boundary 2 ((V:num->real^3->bool) x INTER V y) ((R:num->num->real^3->bool) x y)`)) THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN DISCH_THEN(X_CHOOSE_TAC `z:real^3`) THEN
  MATCH_MP_TAC MOI_S4X_TB_SAME THEN EXISTS_TAC `z:real^3` THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [USE_THEN "ball" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    USE_THEN "ball" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    UNDISCH_TAC `(z:real^3) IN (V:num->real^3->bool) x INTER V y DIFF (R:num->num->real^3->bool) x y` THEN
    SET_TAC[];
    UNDISCH_TAC `(z:real^3) IN (V:num->real^3->bool) x INTER V y DIFF (R:num->num->real^3->bool) x y` THEN
    SET_TAC[];
    MAP_EVERY UNDISCH_TAC
     [`(z:real^3) IN (V:num->real^3->bool) x INTER V y DIFF (R:num->num->real^3->bool) x y`;
      `s INTER ((V:num->real^3->bool) x INTER V y) SUBSET (R:num->num->real^3->bool) x y`] THEN
    SET_TAC[]]);;

(* The four ball interiors lie on one side of the sphere of a context. *)

let MOI_S4X_VSIDE = prove
 (`!V R D J C C' a b c d sa sa' sb sb' sc sc' sd sd'.
     moi_s4x_ctx V R D J C C' a b c d sa sa' sb sb' sc sc' sd sd' /\
     pl_sphere 2 ((sa UNION sc UNION D a UNION D b UNION D c UNION D d) UNION (sb UNION sd))
     ==> (interior(V a) SUBSET
          inside((sa UNION sc UNION D a UNION D b UNION D c UNION D d) UNION (sb UNION sd)) /\
          interior(V b) SUBSET
          inside((sa UNION sc UNION D a UNION D b UNION D c UNION D d) UNION (sb UNION sd)) /\
          interior(V c) SUBSET
          inside((sa UNION sc UNION D a UNION D b UNION D c UNION D d) UNION (sb UNION sd)) /\
          interior(V d) SUBSET
          inside((sa UNION sc UNION D a UNION D b UNION D c UNION D d) UNION (sb UNION sd))) \/
         (interior(V a) SUBSET
          outside((sa UNION sc UNION D a UNION D b UNION D c UNION D d) UNION (sb UNION sd)) /\
          interior(V b) SUBSET
          outside((sa UNION sc UNION D a UNION D b UNION D c UNION D d) UNION (sb UNION sd)) /\
          interior(V c) SUBSET
          outside((sa UNION sc UNION D a UNION D b UNION D c UNION D d) UNION (sb UNION sd)) /\
          interior(V d) SUBSET
          outside((sa UNION sc UNION D a UNION D b UNION D c UNION D d) UNION (sb UNION sd)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_S4X_VS_FACTS) THEN
  ABBREV_TAC `S = (sa UNION sc UNION (D:num->real^3->bool) a UNION D b UNION D c UNION D d) UNION
                  (sb UNION sd)` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `moi_s4x_tconf V (R:num->num->real^3->bool) (D:num->real^3->bool) (J:num->real^3->bool) /\
    a < 4 /\ b < 4 /\ c < 4 /\ d < 4 /\
    ~(a = b) /\ ~(a = c) /\ ~(a = d) /\ ~(b = c) /\ ~(b = d) /\ ~(c = d)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `moi_s4x_ctx V R D (J:num->real^3->bool) (C:num->num->real^3->bool) (C':num->num->real^3->bool) a b c d sa sa' sb sb' sc sc' sd (sd':real^3->bool)` THEN
    REWRITE_TAC[moi_s4x_ctx] THEN SIMP_TAC[];
    ALL_TAC] THEN
  (* each interior lies on one side *)
  SUBGOAL_THEN
   `!x. x < 4 /\ interior((V:num->real^3->bool) x) INTER S = {}
        ==> interior(V x) SUBSET inside S \/ interior(V x) SUBSET outside S`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_S4X_SIDE3 THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `moi_s4x_tconf V (R:num->num->real^3->bool) (D:num->real^3->bool) (J:num->real^3->bool)` THEN
    REWRITE_TAC[moi_s4x_tconf] THEN
    DISCH_THEN(MP_TAC o SPEC `x:num` o CONJUNCT1) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP MOI_S4X_BALL_INT th]);
    ALL_TAC] THEN
  MAP_EVERY (fun x ->
    FIRST_ASSUM(MP_TAC o SPEC x o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `outside:(real^3->bool)->real^3->bool`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC])
   [`a:num`; `b:num`; `c:num`; `d:num`] THEN
  MAP_EVERY (fun y ->
    MP_TAC(ISPECL [`V:num->real^3->bool`; `R:num->num->real^3->bool`; `D:num->real^3->bool`;
                   `J:num->real^3->bool`; `a:num`; y; `S:real^3->bool`] MOI_S4X_PAIR_SAME) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC])
   [`b:num`; `c:num`; `d:num`] THEN
  CONV_TAC TAUT);;

(* Two spheres with the set w inside both, s' inside s UNION w, and a point *)
(* of s in w off s': impossible.                                            *)

let MOI_S4X_NOT_BOTH_INSIDE = prove
 (`!s s' w (z:real^3).
     pl_sphere 2 s /\ pl_sphere 2 s' /\ s' SUBSET s UNION w /\
     w SUBSET s UNION inside s /\ w SUBSET s' UNION inside s' /\
     z IN s /\ z IN w /\ ~(z IN s')
     ==> F`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `s:real^3->bool` MOI_S4X_JB) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `s':real^3->bool` MOI_S4X_JB) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `outside s SUBSET inside s' \/ outside s SUBSET outside (s':real^3->bool)`
  MP_TAC THENL
   [MATCH_MP_TAC MOI_S4X_SIDE3 THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC
     [`s' SUBSET s UNION (w:real^3->bool)`; `w SUBSET s UNION inside(s:real^3->bool)`;
      `s INTER outside s:real^3->bool = {}`; `inside s INTER outside s:real^3->bool = {}`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THENL
   [UNDISCH_TAC `~bounded(outside(s:real^3->bool))` THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC BOUNDED_SUBSET THEN EXISTS_TAC `inside s':real^3->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(z:real^3) IN closure(outside s')` MP_TAC THENL
   [SUBGOAL_THEN `closure(outside s) SUBSET closure(outside s':real^3->bool)` MP_TAC THENL
     [MATCH_MP_TAC SUBSET_CLOSURE THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    UNDISCH_TAC `closure(outside s) = s UNION outside(s:real^3->bool)` THEN
    UNDISCH_TAC `(z:real^3) IN s` THEN SET_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `closure(outside s') = s' UNION outside(s':real^3->bool)` THEN
  DISCH_THEN SUBST1_TAC THEN
  MAP_EVERY UNDISCH_TAC
   [`(z:real^3) IN w`; `w SUBSET s' UNION inside(s':real^3->bool)`; `~((z:real^3) IN s')`;
    `inside s' INTER outside s':real^3->bool = {}`] THEN
  SET_TAC[]);;

(* A point of the hexagon sa off everything else of the configuration. *)

let MOI_S4X_HEX_PT = prove
 (`!V R D J C C' a b c d sa sa' sb sb' sc sc' sd sd'.
     moi_s4x_ctx V R D J C C' a b c d sa sa' sb sb' sc sc' sd sd'
     ==> ?z. z IN sa /\ ~(z IN sa') /\ ~(z IN V b) /\ ~(z IN V c) /\ ~(z IN V d) /\
             ~(z IN D a) /\ ~(z IN D b) /\ ~(z IN D c) /\ ~(z IN D d)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4X_CTX_FACTS) THEN
  UNDISCH_TAC `moi_s4x_ctx V R D (J:num->real^3->bool) (C:num->num->real^3->bool) (C':num->num->real^3->bool) a b c d sa sa' sb sb' sc sc' sd (sd':real^3->bool)` THEN
  REWRITE_TAC[moi_s4x_ctx] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:num->real^3->bool`; `R:num->num->real^3->bool`; `D:num->real^3->bool`;
                 `J:num->real^3->bool`; `C:num->num->real^3->bool`;
                 `C':num->num->real^3->bool`; `a:num`; `b:num`; `c:num`; `d:num`;
                 `sa:real^3->bool`; `sa':real^3->bool`] MOI_S4X_HEX_EXPAND) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> MP_TAC(CONJUNCT1(CONJUNCT2(CONJUNCT2(CONJUNCT2 th)))) THEN
                       MP_TAC(CONJUNCT1(CONJUNCT2(CONJUNCT2(CONJUNCT2
                         (MATCH_MP MOI_S4L_PL_CELL2_TOPO (CONJUNCT1 th))))))) THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
  DISCH_THEN(X_CHOOSE_TAC `z:real^3`) THEN DISCH_TAC THEN
  EXISTS_TAC `z:real^3` THEN
  MAP_EVERY UNDISCH_TAC
   [`(sa:real^3->bool) SUBSET (V:num->real^3->bool) a`;
    `(D:num->real^3->bool) a INTER (V:num->real^3->bool) a = {}`] THEN
  POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
  SET_TAC[]);;

(* A ball whose interior lies inside a sphere lies in the sphere plus its   *)
(* inside.                                                                   *)

let MOI_S4X_BALL_IN = prove
 (`!v s:real^3->bool.
     pl_ball 3 v /\ pl_sphere 2 s /\ interior v SUBSET inside s ==> v SUBSET s UNION inside s`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `v:real^3->bool` MOI_S4X_BALL_INT) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT1) THEN
  MP_TAC(ISPEC `s:real^3->bool` MOI_S4X_JB) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `closure(inside s:real^3->bool)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUBSET_CLOSURE THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[SUBSET_REFL]]);;

(* The side choice: one of the two spheres of a consistent choice has the  *)
(* four ball interiors outside.                                             *)

let MOI_S4X_SIDE_CHOICE = prove
 (`!V R D J C C' a b c d sa sa' sb sb' sc sc' sd sd'.
     moi_s4x_ctx V R D J C C' a b c d sa sa' sb sb' sc sc' sd sd' /\
     sb INTER V a = sa INTER V b /\ sb INTER V c = sc INTER V b /\
     sd INTER V a = sa INTER V d /\ sd INTER V c = sc INTER V d /\
     sb INTER V d = sd INTER V b
     ==> ?ta ta' tb tb' tc tc' td td'.
           moi_s4x_ctx V R D J C C' a b c d ta ta' tb tb' tc tc' td td' /\
           tb INTER V a = ta INTER V b /\ tb INTER V c = tc INTER V b /\
           td INTER V a = ta INTER V d /\ td INTER V c = tc INTER V d /\
           tb INTER V d = td INTER V b /\
           pl_sphere 2 ((ta UNION tc UNION D a UNION D b UNION D c UNION D d) UNION
                        (tb UNION td)) /\
           interior(V a) SUBSET
           outside((ta UNION tc UNION D a UNION D b UNION D c UNION D d) UNION (tb UNION td)) /\
           interior(V b) SUBSET
           outside((ta UNION tc UNION D a UNION D b UNION D c UNION D d) UNION (tb UNION td)) /\
           interior(V c) SUBSET
           outside((ta UNION tc UNION D a UNION D b UNION D c UNION D d) UNION (tb UNION td)) /\
           interior(V d) SUBSET
           outside((ta UNION tc UNION D a UNION D b UNION D c UNION D d) UNION (tb UNION td))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `moi_s4x_tconf V (R:num->num->real^3->bool) (D:num->real^3->bool) (J:num->real^3->bool) /\
    moi_s4x_rimarcs V R D (C:num->num->real^3->bool) (C':num->num->real^3->bool) /\
    moi_s4x_hex V D C C' a sa sa' /\ moi_s4x_hex V D C C' b sb sb' /\
    moi_s4x_hex V D C C' c sc sc' /\ moi_s4x_hex V D C C' d sd sd' /\
    a < 4 /\ b < 4 /\ c < 4 /\ d < 4 /\
    ~(a = b) /\ ~(a = c) /\ ~(a = d) /\ ~(b = c) /\ ~(b = d) /\ ~(c = d) /\
    sa INTER V c = sc INTER V a`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `moi_s4x_ctx V R D (J:num->real^3->bool) (C:num->num->real^3->bool)
                   (C':num->num->real^3->bool) a b c d sa sa' sb sb' sc sc' sd (sd':real^3->bool)` THEN
    REWRITE_TAC[moi_s4x_ctx] THEN SIMP_TAC[];
    ALL_TAC] THEN
  (* the complementary choice is consistent *)
  MAP_EVERY (fun (i,j,p,p',q,q') ->
    MP_TAC(ISPECL [`V:num->real^3->bool`; `R:num->num->real^3->bool`; `D:num->real^3->bool`;
                   `J:num->real^3->bool`; `C:num->num->real^3->bool`;
                   `C':num->num->real^3->bool`; i; j; p; p'; q; q'] MOI_S4X_COMP) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC])
   [`a:num`,`c:num`,`sa:real^3->bool`,`sa':real^3->bool`,`sc:real^3->bool`,`sc':real^3->bool`;
    `b:num`,`a:num`,`sb:real^3->bool`,`sb':real^3->bool`,`sa:real^3->bool`,`sa':real^3->bool`;
    `b:num`,`c:num`,`sb:real^3->bool`,`sb':real^3->bool`,`sc:real^3->bool`,`sc':real^3->bool`;
    `d:num`,`a:num`,`sd:real^3->bool`,`sd':real^3->bool`,`sa:real^3->bool`,`sa':real^3->bool`;
    `d:num`,`c:num`,`sd:real^3->bool`,`sd':real^3->bool`,`sc:real^3->bool`,`sc':real^3->bool`;
    `b:num`,`d:num`,`sb:real^3->bool`,`sb':real^3->bool`,`sd:real^3->bool`,`sd':real^3->bool`] THEN
  SUBGOAL_THEN `moi_s4x_ctx V R D J C C' a b c d sa' sa sb' sb sc' sc sd' sd` ASSUME_TAC THENL
   [REWRITE_TAC[moi_s4x_ctx] THEN REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    MATCH_MP_TAC MOI_S4X_HEX_SYM THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  (* the two spheres *)
  MP_TAC(ISPECL [`V:num->real^3->bool`; `R:num->num->real^3->bool`; `D:num->real^3->bool`;
                 `J:num->real^3->bool`; `C:num->num->real^3->bool`;
                 `C':num->num->real^3->bool`; `a:num`; `b:num`; `c:num`; `d:num`;
                 `sa:real^3->bool`; `sa':real^3->bool`; `sb:real^3->bool`; `sb':real^3->bool`;
                 `sc:real^3->bool`; `sc':real^3->bool`; `sd:real^3->bool`; `sd':real^3->bool`]
                MOI_S4X_SPHERE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(ISPECL [`V:num->real^3->bool`; `R:num->num->real^3->bool`; `D:num->real^3->bool`;
                 `J:num->real^3->bool`; `C:num->num->real^3->bool`;
                 `C':num->num->real^3->bool`; `a:num`; `b:num`; `c:num`; `d:num`;
                 `sa':real^3->bool`; `sa:real^3->bool`; `sb':real^3->bool`; `sb:real^3->bool`;
                 `sc':real^3->bool`; `sc:real^3->bool`; `sd':real^3->bool`; `sd:real^3->bool`]
                MOI_S4X_SPHERE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(ISPECL [`V:num->real^3->bool`; `R:num->num->real^3->bool`; `D:num->real^3->bool`;
                 `J:num->real^3->bool`; `C:num->num->real^3->bool`;
                 `C':num->num->real^3->bool`; `a:num`; `b:num`; `c:num`; `d:num`;
                 `sa:real^3->bool`; `sa':real^3->bool`; `sb:real^3->bool`; `sb':real^3->bool`;
                 `sc:real^3->bool`; `sc':real^3->bool`; `sd:real^3->bool`; `sd':real^3->bool`]
                MOI_S4X_VSIDE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(DISJ_CASES_THEN2 MP_TAC STRIP_ASSUME_TAC) THENL
   [ALL_TAC;
    MAP_EVERY EXISTS_TAC [`sa:real^3->bool`; `sa':real^3->bool`; `sb:real^3->bool`;
                          `sb':real^3->bool`; `sc:real^3->bool`; `sc':real^3->bool`;
                          `sd:real^3->bool`; `sd':real^3->bool`] THEN
    ASM_REWRITE_TAC[]] THEN
  ABBREV_TAC `S = (sa UNION sc UNION (D:num->real^3->bool) a UNION D b UNION D c UNION D d) UNION
                  (sb UNION sd)` THEN
  DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  MP_TAC(ISPECL [`V:num->real^3->bool`; `R:num->num->real^3->bool`; `D:num->real^3->bool`;
                 `J:num->real^3->bool`; `C:num->num->real^3->bool`;
                 `C':num->num->real^3->bool`; `a:num`; `b:num`; `c:num`; `d:num`;
                 `sa':real^3->bool`; `sa:real^3->bool`; `sb':real^3->bool`; `sb:real^3->bool`;
                 `sc':real^3->bool`; `sc:real^3->bool`; `sd':real^3->bool`; `sd:real^3->bool`]
                MOI_S4X_VSIDE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(DISJ_CASES_THEN2 MP_TAC STRIP_ASSUME_TAC) THENL
   [ALL_TAC;
    MAP_EVERY EXISTS_TAC [`sa':real^3->bool`; `sa:real^3->bool`; `sb':real^3->bool`;
                          `sb:real^3->bool`; `sc':real^3->bool`; `sc:real^3->bool`;
                          `sd':real^3->bool`; `sd:real^3->bool`] THEN
    ASM_REWRITE_TAC[]] THEN
  ABBREV_TAC `S' = (sa' UNION sc' UNION (D:num->real^3->bool) a UNION D b UNION D c UNION D d) UNION
                   (sb' UNION sd')` THEN
  DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  (* both have the balls inside: impossible *)
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_S4X_HEX_PT o check (fun th -> concl th =
    `moi_s4x_ctx V (R:num->num->real^3->bool) (D:num->real^3->bool) (J:num->real^3->bool)
       (C:num->num->real^3->bool) (C':num->num->real^3->bool) a b c d
       sa sa' sb sb' sc sc' sd sd'`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4X_CTX_FACTS o check (fun th -> concl th =
    `moi_s4x_ctx V (R:num->num->real^3->bool) (D:num->real^3->bool) (J:num->real^3->bool)
       (C:num->num->real^3->bool) (C':num->num->real^3->bool) a b c d
       sa' sa sb' sb sc' sc sd' sd`)) THEN
  SUBGOAL_THEN `!x. x < 4 ==> pl_ball 3 ((V:num->real^3->bool) x)` ASSUME_TAC THENL
   [UNDISCH_TAC `moi_s4x_tconf V (R:num->num->real^3->bool) (D:num->real^3->bool) (J:num->real^3->bool)` THEN
    REWRITE_TAC[moi_s4x_tconf] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `F ==> q`) THEN MATCH_MP_TAC MOI_S4X_NOT_BOTH_INSIDE THEN
  MAP_EVERY EXISTS_TAC [`S:real^3->bool`; `S':real^3->bool`;
                        `(V:num->real^3->bool) a UNION V b UNION V c UNION V d`; `z:real^3`] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
   [EXPAND_TAC "S" THEN EXPAND_TAC "S'" THEN
    MAP_EVERY UNDISCH_TAC
     [`(sa':real^3->bool) SUBSET (V:num->real^3->bool) a`;
      `(sb':real^3->bool) SUBSET (V:num->real^3->bool) b`;
      `(sc':real^3->bool) SUBSET (V:num->real^3->bool) c`;
      `(sd':real^3->bool) SUBSET (V:num->real^3->bool) d`] THEN
    SET_TAC[];
    REWRITE_TAC[UNION_SUBSET] THEN REPEAT CONJ_TAC THEN MATCH_MP_TAC MOI_S4X_BALL_IN THEN
    ASM_SIMP_TAC[];
    REWRITE_TAC[UNION_SUBSET] THEN REPEAT CONJ_TAC THEN MATCH_MP_TAC MOI_S4X_BALL_IN THEN
    ASM_SIMP_TAC[];
    EXPAND_TAC "S" THEN UNDISCH_TAC `(z:real^3) IN sa` THEN SET_TAC[];
    MP_TAC(ISPECL [`V:num->real^3->bool`; `R:num->num->real^3->bool`; `D:num->real^3->bool`;
                   `J:num->real^3->bool`; `C:num->num->real^3->bool`;
                   `C':num->num->real^3->bool`; `a:num`; `sa:real^3->bool`; `sa':real^3->bool`]
                  MOI_S4X_HEX_SUBSET) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    MAP_EVERY UNDISCH_TAC
     [`(z:real^3) IN sa`; `(sa:real^3->bool) SUBSET (V:num->real^3->bool) a`] THEN
    SET_TAC[];
    EXPAND_TAC "S'" THEN
    MAP_EVERY UNDISCH_TAC
     [`(sb':real^3->bool) SUBSET (V:num->real^3->bool) b`;
      `(sc':real^3->bool) SUBSET (V:num->real^3->bool) c`;
      `(sd':real^3->bool) SUBSET (V:num->real^3->bool) d`;
      `~((z:real^3) IN sa')`; `~((z:real^3) IN (V:num->real^3->bool) b)`;
      `~((z:real^3) IN (V:num->real^3->bool) c)`; `~((z:real^3) IN (V:num->real^3->bool) d)`;
      `~((z:real^3) IN (D:num->real^3->bool) a)`; `~((z:real^3) IN (D:num->real^3->bool) b)`;
      `~((z:real^3) IN (D:num->real^3->bool) c)`; `~((z:real^3) IN (D:num->real^3->bool) d)`] THEN
    SET_TAC[]]);;

(* The tetra configuration: a consistent choice of hexagons t i whose      *)
(* sphere, with the four face disks, has the four ball interiors outside.   *)

let MOI_S4X_TETRA = prove
 (`!V R D J.
     moi_s4x_tconf V R D J
     ==> ?C C' t t'.
           moi_s4x_rimarcs V R D C C' /\
           (!i. i < 4 ==> moi_s4x_hex V D C C' i (t i) (t' i)) /\
           (!i j. i < 4 /\ j < 4 /\ ~(i = j) ==> t i INTER V j = t j INTER V i) /\
           pl_sphere 2 (t 0 UNION t 1 UNION t 2 UNION t 3 UNION
                        D 0 UNION D 1 UNION D 2 UNION D 3) /\
           (!i. i < 4 ==> interior(V i) SUBSET
                          outside(t 0 UNION t 1 UNION t 2 UNION t 3 UNION
                                  D 0 UNION D 1 UNION D 2 UNION D 3))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `C:num->num->real^3->bool` (X_CHOOSE_TAC `C':num->num->real^3->bool`) o
    MATCH_MP MOI_S4X_RIMARCS_EX) THEN
  MAP_EVERY (fun (i,p,q) ->
    MP_TAC(ISPECL [`V:num->real^3->bool`; `R:num->num->real^3->bool`; `D:num->real^3->bool`;
                   `J:num->real^3->bool`; `C:num->num->real^3->bool`;
                   `C':num->num->real^3->bool`; i] MOI_S4X_HEX_EX) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[ARITH]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN p (X_CHOOSE_TAC q)))
   [`0`,`h0:real^3->bool`,`h0':real^3->bool`; `1`,`h1:real^3->bool`,`h1':real^3->bool`;
    `2`,`h2:real^3->bool`,`h2':real^3->bool`; `3`,`h3:real^3->bool`,`h3':real^3->bool`] THEN
  (* the hexagon at 2 sharing the rim arc of h0 *)
  MP_TAC(ISPECL [`V:num->real^3->bool`; `R:num->num->real^3->bool`; `D:num->real^3->bool`;
                 `J:num->real^3->bool`; `C:num->num->real^3->bool`;
                 `C':num->num->real^3->bool`; `0`; `2`;
                 `h0:real^3->bool`; `h0':real^3->bool`; `h2:real^3->bool`; `h2':real^3->bool`]
                MOI_S4X_PICK) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[ARITH]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `u2:real^3->bool` (X_CHOOSE_THEN `u2':real^3->bool`
    (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC))) THEN
  SUBGOAL_THEN `moi_s4x_hex V D C C' 2 u2 u2'` ASSUME_TAC THENL
   [FIRST_X_ASSUM(DISJ_CASES_THEN (CONJUNCTS_THEN SUBST1_TAC) o check (fun th ->
      is_disj(concl th))) THEN
    TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    MATCH_MP_TAC MOI_S4X_HEX_SYM THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_s4x_ctx V R D J C C' 0 1 2 3 h0 h0' h1 h1' u2 u2' h3 h3'` ASSUME_TAC THENL
   [REWRITE_TAC[moi_s4x_ctx] THEN ASM_REWRITE_TAC[ARITH]; ALL_TAC] THEN
  (* consistent choices at 1 and 3 *)
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_S4X_CONSIST) THEN
  DISCH_THEN(X_CHOOSE_THEN `tb:real^3->bool` (X_CHOOSE_THEN `tb':real^3->bool`
    (X_CHOOSE_THEN `td:real^3->bool` (X_CHOOSE_THEN `td':real^3->bool`
    (fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)))))) THEN
  SUBGOAL_THEN `moi_s4x_ctx V R D J C C' 0 1 2 3 h0 h0' tb tb' u2 u2' td td'` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S4X_CTX_CHOICE THEN
    MAP_EVERY EXISTS_TAC [`h1:real^3->bool`; `h1':real^3->bool`;
                          `h3:real^3->bool`; `h3':real^3->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the side choice *)
  MP_TAC(ISPECL [`V:num->real^3->bool`; `R:num->num->real^3->bool`; `D:num->real^3->bool`;
                 `J:num->real^3->bool`; `C:num->num->real^3->bool`;
                 `C':num->num->real^3->bool`; `0`; `1`; `2`; `3`;
                 `h0:real^3->bool`; `h0':real^3->bool`; `tb:real^3->bool`; `tb':real^3->bool`;
                 `u2:real^3->bool`; `u2':real^3->bool`; `td:real^3->bool`; `td':real^3->bool`]
                MOI_S4X_SIDE_CHOICE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `a0:real^3->bool` (X_CHOOSE_THEN `a0':real^3->bool`
    (X_CHOOSE_THEN `a1:real^3->bool` (X_CHOOSE_THEN `a1':real^3->bool`
    (X_CHOOSE_THEN `a2:real^3->bool` (X_CHOOSE_THEN `a2':real^3->bool`
    (X_CHOOSE_THEN `a3:real^3->bool` (X_CHOOSE_THEN `a3':real^3->bool`
    (fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)))))))))) THEN
  SUBGOAL_THEN
   `moi_s4x_hex V D C C' 0 a0 a0' /\ moi_s4x_hex V D C C' 1 a1 a1' /\
    moi_s4x_hex V D C C' 2 a2 a2' /\ moi_s4x_hex V D C C' 3 a3 a3' /\
    a0 INTER (V:num->real^3->bool) 2 = a2 INTER V 0`
  STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th -> is_comb(concl th) &&
      is_const(fst(strip_comb(concl th))) &&
      fst(dest_const(fst(strip_comb(concl th)))) = "moi_s4x_ctx" &&
      can (find_term ((=) `a0:real^3->bool`)) (concl th))) THEN
    REWRITE_TAC[moi_s4x_ctx] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `a0 UNION a1 UNION a2 UNION a3 UNION
    (D:num->real^3->bool) 0 UNION D 1 UNION D 2 UNION D 3 =
    (a0 UNION a2 UNION D 0 UNION D 1 UNION D 2 UNION D 3) UNION (a1 UNION a3)`
  ASSUME_TAC THENL [SET_TAC[]; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`C:num->num->real^3->bool`; `C':num->num->real^3->bool`;
    `\i:num. if i = 0 then a0 else if i = 1 then a1 else if i = 2 then a2 else a3:real^3->bool`;
    `\i:num. if i = 0 then a0' else if i = 1 then a1' else if i = 2 then a2' else a3':real^3->bool`] THEN
  BETA_TAC THEN REWRITE_TAC[ARITH] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ARITH_RULE `i < 4 <=> i = 0 \/ i = 1 \/ i = 2 \/ i = 3`] THEN
  REPEAT CONJ_TAC THENL
   [GEN_TAC THEN DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) THEN
    ASM_REWRITE_TAC[ARITH];
    REPEAT GEN_TAC THEN
    DISCH_THEN(CONJUNCTS_THEN2 (REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC)
      (CONJUNCTS_THEN2 (REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) MP_TAC)) THEN
    ASM_REWRITE_TAC[ARITH];
    GEN_TAC THEN DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) THEN
    ASM_REWRITE_TAC[ARITH]]);;

(* ------------------------------------------------------------------------- *)
(* The configuration at a 3-simplex r of kk.  The vertices of               *)
(* r as a function vx on 0..3 (moi_s4x_rverts), its faces moi_s4x_rface vx  *)
(* l (the face opposite vx l), and the classification of the edges and     *)
(* faces of kk inside r (affine independence of the vertices).              *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Affinely independent vertex sets.                                         *)
(* ------------------------------------------------------------------------- *)

let MOI_S4X_AI_MEM = prove
 (`!w c x:real^N.
     ~affine_dependent w /\ c SUBSET w /\ x IN w
     ==> (x IN convex hull c <=> x IN c)`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL [ALL_TAC; MESON_TAC[HULL_INC]] THEN
  DISCH_TAC THEN ASM_CASES_TAC `(x:real^N) IN c` THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `~affine_dependent(w:real^N->bool)` THEN
  REWRITE_TAC[affine_dependent] THEN EXISTS_TAC `x:real^N` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `convex hull c SUBSET affine hull (w DELETE (x:real^N))` MP_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `affine hull c:real^N->bool` THEN
    REWRITE_TAC[CONVEX_HULL_SUBSET_AFFINE_HULL] THEN MATCH_MP_TAC HULL_MONO THEN
    MAP_EVERY UNDISCH_TAC [`(c:real^N->bool) SUBSET w`; `~((x:real^N) IN c)`] THEN SET_TAC[];
    UNDISCH_TAC `(x:real^N) IN convex hull c` THEN SET_TAC[]]);;

let MOI_S4X_AI_HULL_SUBSET = prove
 (`!w c c':real^N->bool.
     ~affine_dependent w /\ c SUBSET w /\ c' SUBSET w
     ==> (convex hull c SUBSET convex hull c' <=> c SUBSET c')`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL [ALL_TAC; REWRITE_TAC[HULL_MONO]] THEN
  REWRITE_TAC[SUBSET] THEN DISCH_TAC THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`w:real^N->bool`; `c':real^N->bool`; `x:real^N`] MOI_S4X_AI_MEM) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN MATCH_MP_TAC HULL_INC THEN ASM_REWRITE_TAC[]);;

let MOI_S4X_AI_DIM = prove
 (`!w c:real^N->bool.
     ~affine_dependent w /\ c SUBSET w
     ==> aff_dim(convex hull c) = &(CARD c) - &1`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[AFF_DIM_CONVEX_HULL] THEN
  MATCH_MP_TAC AFF_DIM_AFFINE_INDEPENDENT THEN
  ASM_MESON_TAC[AFFINE_INDEPENDENT_SUBSET]);;

(* The faces of a simplex of kk that lie in kk. *)

let MOI_S4X_KK_FACE = prove
 (`!(kk:(real^N->bool)->bool) q w.
     lf_simplicial_complex kk /\ convex hull w IN kk /\ ~affine_dependent w /\
     q IN kk /\ q SUBSET convex hull w
     ==> ?c. c SUBSET w /\ q = convex hull c`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(q:real^N->bool) face_of convex hull w` MP_TAC THENL
   [SUBGOAL_THEN `q:real^N->bool = q INTER convex hull w` SUBST1_TAC THENL
     [UNDISCH_TAC `(q:real^N->bool) SUBSET convex hull w` THEN SET_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o
      GEN_REWRITE_RULE I [lf_simplicial_complex]) THEN
    DISCH_THEN(MP_TAC o SPECL [`q:real^N->bool`; `convex hull w:real^N->bool`]) THEN
    ASM_SIMP_TAC[];
    ASM_SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT]]);;

(* Edges of kk inside a simplex of kk join two of its vertices. *)

let MOI_S4X_KK_EDGE = prove
 (`!(kk:(real^N->bool)->bool) g w.
     lf_simplicial_complex kk /\ convex hull w IN kk /\ ~affine_dependent w /\
     g IN moi_s34_simp kk (&1) /\ g SUBSET convex hull w
     ==> ?x y. x IN w /\ y IN w /\ ~(x = y) /\ g = segment[x,y]`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s34_simp; IN_ELIM_THM] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`kk:(real^N->bool)->bool`; `g:real^N->bool`; `w:real^N->bool`]
    MOI_S4X_KK_FACE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `c:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(c:real^N->bool) HAS_SIZE 2` MP_TAC THENL
   [REWRITE_TAC[HAS_SIZE] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[FINITE_SUBSET; AFFINE_INDEPENDENT_IMP_FINITE]; ALL_TAC] THEN
    MP_TAC(ISPECL [`w:real^N->bool`; `c:real^N->bool`] MOI_S4X_AI_DIM) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `aff_dim(g:real^N->bool) = &1` THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[INT_ARITH `&1:int = x - &1 <=> x = &2`; INT_OF_NUM_EQ] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  CONV_TAC(LAND_CONV HAS_SIZE_CONV) THEN
  DISCH_THEN(X_CHOOSE_THEN `x:real^N` (X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`x:real^N`; `y:real^N`] THEN
  ASM_REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN
  UNDISCH_TAC `(c:real^N->bool) SUBSET w` THEN ASM_REWRITE_TAC[] THEN SET_TAC[]);;

(* The vertices of a 3-simplex r of kk. *)

let MOI_S4X_TET_FORM = prove
 (`!(tt:(real^N->bool)->bool) kk r.
     moi_s34_tube tt kk /\ r IN moi_s34_simp kk (&3)
     ==> ?a b c d. ~(a = b) /\ ~(a = c) /\ ~(a = d) /\ ~(b = c) /\ ~(b = d) /\ ~(c = d) /\
                   ~affine_dependent {a,b,c,d} /\ r = convex hull {a,b,c,d} /\
                   {a} IN kk /\ {b} IN kk /\ {c} IN kk /\ {d} IN kk /\
                   (!v. v IN r /\ {v} IN kk ==> v = a \/ v = b \/ v = c \/ v = d) /\
                   (!f. f face_of r ==> f IN kk)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s34_simp; IN_ELIM_THM] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4L_TUBE_TUBE) THEN
  SUBGOAL_THEN `?n. n simplex (r:real^N->bool)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[lf_simplicial_complex]; ALL_TAC] THEN
  SUBGOAL_THEN `(n:int) = &3` SUBST_ALL_TAC THENL
   [ASM_MESON_TAC[AFF_DIM_SIMPLEX]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [simplex]) THEN
  DISCH_THEN(X_CHOOSE_THEN `cc:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(cc:real^N->bool) HAS_SIZE 4` MP_TAC THENL
   [ASM_SIMP_TAC[HAS_SIZE; AFFINE_INDEPENDENT_IMP_FINITE] THEN
    UNDISCH_TAC `&(CARD(cc:real^N->bool)):int = &3 + &1` THEN
    REWRITE_TAC[INT_OF_NUM_ADD; INT_OF_NUM_EQ] THEN ARITH_TAC;
    ALL_TAC] THEN
  CONV_TAC(LAND_CONV HAS_SIZE_CONV) THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^N` (X_CHOOSE_THEN `b:real^N`
    (X_CHOOSE_THEN `c:real^N` (X_CHOOSE_THEN `d:real^N` STRIP_ASSUME_TAC)))) THEN
  MAP_EVERY EXISTS_TAC [`a:real^N`; `b:real^N`; `c:real^N`; `d:real^N`] THEN
  UNDISCH_TAC `~affine_dependent(cc:real^N->bool)` THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `!f:real^N->bool. f face_of convex hull {a,b,c,d} ==> f IN kk`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_ASSUM(MATCH_MP_TAC o CONJUNCT1 o CONJUNCT2 o
      GEN_REWRITE_RULE I [lf_simplicial_complex] o check (fun th ->
        concl th = `lf_simplicial_complex (kk:(real^N->bool)->bool)`)) THEN
    EXISTS_TAC `r:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN TRY
   (FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_SIMP_TAC[FACE_OF_SING; EXTREME_POINT_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
    SET_TAC[] THEN NO_TAC) THEN
  X_GEN_TAC `v:real^N` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(v:real^N) extreme_point_of convex hull {a,b,c,d}` MP_TAC THENL
   [MATCH_MP_TAC MOI_S4L_LF_VERTEX_EXTREME THEN
    EXISTS_TAC `kk:(real^N->bool)->bool` THEN ASM_MESON_TAC[];
    ASM_SIMP_TAC[EXTREME_POINT_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The vertices of r as a function on 0..3, its edges and faces.            *)
(* ------------------------------------------------------------------------- *)

let moi_s4x_rverts = new_definition
 `moi_s4x_rverts (kk:(real^N->bool)->bool) (r:real^N->bool) (vx:num->real^N) <=>
   (!i j. i < 4 /\ j < 4 /\ vx i = vx j ==> i = j) /\
   ~affine_dependent {vx 0, vx 1, vx 2, vx 3} /\ r = convex hull {vx 0, vx 1, vx 2, vx 3} /\
   (!i. i < 4 ==> {vx i} IN kk) /\
   (!v. v IN r /\ {v} IN kk ==> ?i. i < 4 /\ v = vx i) /\
   (!f. f face_of r ==> f IN kk)`;;

let moi_s4x_rface = new_definition
 `moi_s4x_rface (vx:num->real^N) (l:num) =
    convex hull ({vx 0, vx 1, vx 2, vx 3} DELETE vx l)`;;

let MOI_S4X_LT4 = prove
 (`!i. i < 4 <=> i = 0 \/ i = 1 \/ i = 2 \/ i = 3`,
  ARITH_TAC);;

let MOI_S4X_RVERTS_EX = prove
 (`!(tt:(real^N->bool)->bool) kk r.
     moi_s34_tube tt kk /\ r IN moi_s34_simp kk (&3)
     ==> ?vx. moi_s4x_rverts kk r vx`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_S4X_TET_FORM) THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^N` (X_CHOOSE_THEN `b:real^N`
    (X_CHOOSE_THEN `c:real^N` (X_CHOOSE_THEN `d:real^N` STRIP_ASSUME_TAC)))) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `r:real^N->bool`)) THEN
  EXISTS_TAC `\i:num. if i = 0 then a else if i = 1 then b else if i = 2 then c
                      else d:real^N` THEN
  REWRITE_TAC[moi_s4x_rverts] THEN BETA_TAC THEN REWRITE_TAC[ARITH] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[MOI_S4X_LT4] THEN
    DISCH_THEN(fun th -> MP_TAC(CONJUNCT2(CONJUNCT2 th)) THEN
      MP_TAC(CONJUNCT1(CONJUNCT2 th)) THEN MP_TAC(CONJUNCT1 th)) THEN
    DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) THEN
    DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) THEN
    REWRITE_TAC[ARITH] THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[MOI_S4X_LT4] THEN GEN_TAC THEN
    DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) THEN
    REWRITE_TAC[ARITH] THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `v:real^N` o check (fun th ->
      is_forall(concl th) && is_imp(snd(dest_forall(concl th))) &&
      is_disj(rand(snd(dest_forall(concl th)))))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
     [EXISTS_TAC `0`; EXISTS_TAC `1`; EXISTS_TAC `2`; EXISTS_TAC `3`] THEN
    ASM_REWRITE_TAC[ARITH]]);;

(* Facts on the vertex function. *)

let MOI_S4X_RV_BASIC = prove
 (`!(kk:(real^N->bool)->bool) r vx.
     moi_s4x_rverts kk r vx
     ==> FINITE {vx 0, vx 1, vx 2, vx 3} /\
         (!i. i < 4 ==> vx i IN {vx 0, vx 1, vx 2, vx 3} /\ vx i IN r) /\
         (!x. x IN {vx 0, vx 1, vx 2, vx 3} ==> ?i. i < 4 /\ x = vx i) /\
         (!i j. i < 4 /\ j < 4 ==> (vx i = vx j <=> i = j))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s4x_rverts] THEN STRIP_TAC THEN
  REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY] THEN
  SUBGOAL_THEN `!i. i < 4 ==> (vx:num->real^N) i IN {vx 0, vx 1, vx 2, vx 3}` ASSUME_TAC THENL
   [REWRITE_TAC[MOI_S4X_LT4] THEN GEN_TAC THEN
    DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) THEN REWRITE_TAC[IN_INSERT];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN
    FIRST_ASSUM(fun th -> MP_TAC(MATCH_MP th (ASSUME `i < 4`))) THEN DISCH_TAC THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HULL_INC THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN GEN_TAC THEN STRIP_TAC THENL
     [EXISTS_TAC `0`; EXISTS_TAC `1`; EXISTS_TAC `2`; EXISTS_TAC `3`] THEN
    ASM_REWRITE_TAC[ARITH];
    ASM_MESON_TAC[]]);;

(* The content of moi_s4x_rverts without the injectivity implication (which, *)
(* next to the iff form of RV_BASIC, makes conditional rewriting loop).      *)

let MOI_S4X_RV_PARTS = prove
 (`!(kk:(real^N->bool)->bool) r vx.
     moi_s4x_rverts kk r vx
     ==> ~affine_dependent {vx 0, vx 1, vx 2, vx 3} /\
         r = convex hull {vx 0, vx 1, vx 2, vx 3} /\
         (!i. i < 4 ==> {vx i} IN kk) /\
         (!v. v IN r /\ {v} IN kk ==> ?i. i < 4 /\ v = vx i) /\
         (!f. f face_of r ==> f IN kk)`,
  REWRITE_TAC[moi_s4x_rverts] THEN REPEAT GEN_TAC THEN DISCH_THEN(ACCEPT_TAC o CONJUNCT2));;

(* Vertices in hulls of vertex subsets. *)

let MOI_S4X_RV_MEM = prove
 (`!(kk:(real^N->bool)->bool) r vx c i.
     moi_s4x_rverts kk r vx /\ c SUBSET {vx 0, vx 1, vx 2, vx 3} /\ i < 4
     ==> (vx i IN convex hull c <=> vx i IN c)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_S4X_AI_MEM THEN
  EXISTS_TAC `{vx 0, vx 1, vx 2, vx 3}:real^N->bool` THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4X_RV_BASIC) THEN
  ASM_SIMP_TAC[] THEN ASM_MESON_TAC[moi_s4x_rverts]);;

let MOI_S4X_RV_SEG = prove
 (`!(kk:(real^N->bool)->bool) r vx i j m.
     moi_s4x_rverts kk r vx /\ i < 4 /\ j < 4 /\ m < 4
     ==> (vx m IN segment[vx i,vx j] <=> m = i \/ m = j)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4X_RV_BASIC) THEN
  MP_TAC(ISPECL [`kk:(real^N->bool)->bool`; `r:real^N->bool`; `vx:num->real^N`;
                 `{(vx:num->real^N) i, vx j}`; `m:num`] MOI_S4X_RV_MEM) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[INSERT_SUBSET; EMPTY_SUBSET]; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN ASM_MESON_TAC[]);;

let MOI_S4X_RV_FACE = prove
 (`!(kk:(real^N->bool)->bool) r vx i l.
     moi_s4x_rverts kk r vx /\ i < 4 /\ l < 4
     ==> (vx i IN moi_s4x_rface vx l <=> ~(i = l))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[moi_s4x_rface] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4X_RV_BASIC) THEN
  MP_TAC(ISPECL [`kk:(real^N->bool)->bool`; `r:real^N->bool`; `vx:num->real^N`;
                 `{(vx:num->real^N) 0, vx 1, vx 2, vx 3} DELETE vx l`; `i:num`]
                MOI_S4X_RV_MEM) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN SET_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[IN_DELETE] THEN ASM_SIMP_TAC[]);;

let MOI_S4X_RV_SEG_FACE = prove
 (`!(kk:(real^N->bool)->bool) r vx i j l.
     moi_s4x_rverts kk r vx /\ i < 4 /\ j < 4 /\ l < 4
     ==> (segment[vx i,vx j] SUBSET moi_s4x_rface vx l <=> ~(i = l) /\ ~(j = l))`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN
    MP_TAC(ISPECL [`kk:(real^N->bool)->bool`; `r:real^N->bool`; `vx:num->real^N`;
                   `i:num`; `l:num`] MOI_S4X_RV_FACE) THEN
    MP_TAC(ISPECL [`kk:(real^N->bool)->bool`; `r:real^N->bool`; `vx:num->real^N`;
                   `j:num`; `l:num`] MOI_S4X_RV_FACE) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`vx (i:num):real^N`; `vx (j:num):real^N`] ENDS_IN_SEGMENT) THEN
    UNDISCH_TAC `segment[vx i:real^N,vx j] SUBSET moi_s4x_rface vx l` THEN SET_TAC[];
    STRIP_TAC THEN REWRITE_TAC[SEGMENT_CONVEX_HULL; moi_s4x_rface] THEN
    MATCH_MP_TAC HULL_MONO THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4X_RV_BASIC) THEN
    REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET; IN_DELETE] THEN ASM_SIMP_TAC[]]);;

let MOI_S4X_RV_FACE_INJ = prove
 (`!(kk:(real^N->bool)->bool) r vx l m.
     moi_s4x_rverts kk r vx /\ l < 4 /\ m < 4 /\ moi_s4x_rface vx l = moi_s4x_rface vx m
     ==> l = m`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`kk:(real^N->bool)->bool`; `r:real^N->bool`; `vx:num->real^N`;
                 `l:num`; `l:num`] MOI_S4X_RV_FACE) THEN
  MP_TAC(ISPECL [`kk:(real^N->bool)->bool`; `r:real^N->bool`; `vx:num->real^N`;
                 `l:num`; `m:num`] MOI_S4X_RV_FACE) THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

let MOI_S4X_RV_FACE_SUB = prove
 (`!(kk:(real^N->bool)->bool) r vx l.
     moi_s4x_rverts kk r vx /\ l < 4 ==> moi_s4x_rface vx l SUBSET r`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s4x_rverts; moi_s4x_rface] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HULL_MONO THEN SET_TAC[]);;

(* The four vertices of r form a set of size 4. *)

let MOI_S4X_RV_SIZE = prove
 (`!(kk:(real^N->bool)->bool) r vx.
     moi_s4x_rverts kk r vx ==> {vx 0, vx 1, vx 2, vx 3} HAS_SIZE 4`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4X_RV_BASIC) THEN
  CONV_TAC HAS_SIZE_CONV THEN
  MAP_EVERY EXISTS_TAC [`(vx:num->real^N) 0`; `(vx:num->real^N) 1`;
                        `(vx:num->real^N) 2`; `(vx:num->real^N) 3`] THEN
  ASM_SIMP_TAC[ARITH]);;

(* The edges of r. *)

let MOI_S4X_RV_EDGE = prove
 (`!(tt:(real^N->bool)->bool) kk r vx i j.
     moi_s34_tube tt kk /\ moi_s4x_rverts kk r vx /\ i < 4 /\ j < 4 /\ ~(i = j)
     ==> segment[vx i,vx j] IN moi_s34_simp kk (&1) /\ segment[vx i,vx j] SUBSET r /\
         moi_s34_sd tt kk (segment[vx i,vx j]) =
         moi_s34_vb tt kk (vx i) INTER moi_s34_vb tt kk (vx j)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4X_RV_BASIC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4X_RV_PARTS) THEN
  SUBGOAL_THEN `{(vx:num->real^N) i, vx j} SUBSET {vx 0, vx 1, vx 2, vx 3}` ASSUME_TAC THENL
   [ASM_SIMP_TAC[INSERT_SUBSET; EMPTY_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `~((vx:num->real^N) i = vx j)` ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[moi_s34_simp; IN_ELIM_THM] THEN CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT; SEGMENT_CONVEX_HULL] THEN
      EXISTS_TAC `{(vx:num->real^N) i, vx j}` THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN
      MP_TAC(ISPECL [`{(vx:num->real^N) 0, vx 1, vx 2, vx 3}`; `{(vx:num->real^N) i, vx j}`]
        MOI_S4X_AI_DIM) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      ASM_SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY; IN_INSERT; NOT_IN_EMPTY] THEN
      CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC INT_REDUCE_CONV];
    ASM_REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN MATCH_MP_TAC HULL_MONO THEN
    FIRST_ASSUM ACCEPT_TAC;
    MATCH_MP_TAC MOI_S4D_SAN_SD_EDGE THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY] THEN
    X_GEN_TAC `v:real^N` THEN EQ_TAC THENL
     [STRIP_TAC THEN
      SUBGOAL_THEN `?m. m < 4 /\ v = (vx:num->real^N) m` STRIP_ASSUME_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `(v:real^N) IN segment[(vx:num->real^N) i,vx j]` THEN
        SUBGOAL_THEN `segment[(vx:num->real^N) i,vx j] SUBSET convex hull {vx 0, vx 1, vx 2, vx 3}`
        MP_TAC THENL
         [REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN MATCH_MP_TAC HULL_MONO THEN
          FIRST_ASSUM ACCEPT_TAC;
          SET_TAC[]];
        ALL_TAC] THEN
      UNDISCH_TAC `(v:real^N) IN segment[(vx:num->real^N) i,vx j]` THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`kk:(real^N->bool)->bool`; `r:real^N->bool`; `vx:num->real^N`;
                     `i:num`; `j:num`; `m:num`] MOI_S4X_RV_SEG) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN MESON_TAC[];
      STRIP_TAC THEN ASM_REWRITE_TAC[ENDS_IN_SEGMENT] THEN ASM_SIMP_TAC[]]]);;

(* The faces of r. *)

let MOI_S4X_RV_FACE_IN = prove
 (`!(kk:(real^N->bool)->bool) r vx l.
     moi_s4x_rverts kk r vx /\ l < 4
     ==> moi_s4x_rface vx l IN moi_s34_simp kk (&2) /\ moi_s4x_rface vx l SUBSET r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4X_RV_BASIC) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MOI_S4X_RV_SIZE) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4X_RV_PARTS) THEN
  CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[MOI_S4X_RV_FACE_SUB]] THEN
  REWRITE_TAC[moi_s34_simp; IN_ELIM_THM; moi_s4x_rface] THEN CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
    EXISTS_TAC `{(vx:num->real^N) 0, vx 1, vx 2, vx 3} DELETE vx l` THEN
    REWRITE_TAC[DELETE_SUBSET];
    MP_TAC(ISPECL [`{(vx:num->real^N) 0, vx 1, vx 2, vx 3}`;
                   `{(vx:num->real^N) 0, vx 1, vx 2, vx 3} DELETE vx l`] MOI_S4X_AI_DIM) THEN
    ASM_REWRITE_TAC[DELETE_SUBSET] THEN DISCH_THEN SUBST1_TAC THEN
    UNDISCH_TAC `{(vx:num->real^N) 0, vx 1, vx 2, vx 3} HAS_SIZE 4` THEN
    REWRITE_TAC[HAS_SIZE] THEN STRIP_TAC THEN ASM_SIMP_TAC[CARD_DELETE] THEN
    CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC INT_REDUCE_CONV]);;

let MOI_S4X_RV_IN = prove
 (`!(kk:(real^N->bool)->bool) r vx. moi_s4x_rverts kk r vx ==> r IN kk`,
  REPEAT GEN_TAC THEN DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP MOI_S4X_RV_PARTS) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN MATCH_MP_TAC FACE_OF_REFL THEN
  ASM_REWRITE_TAC[CONVEX_CONVEX_HULL]);;

(* The edges of kk in r join two vertices of r. *)

let MOI_S4X_RV_EDGE_CLASS = prove
 (`!(tt:(real^N->bool)->bool) kk r vx g.
     moi_s34_tube tt kk /\ moi_s4x_rverts kk r vx /\
     g IN moi_s34_simp kk (&1) /\ g SUBSET r
     ==> ?i j. i < 4 /\ j < 4 /\ ~(i = j) /\ g = segment[vx i,vx j]`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MOI_S4X_RV_IN) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4X_RV_BASIC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4X_RV_PARTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4L_TUBE_TUBE) THEN
  MP_TAC(ISPECL [`kk:(real^N->bool)->bool`; `g:real^N->bool`;
                 `{(vx:num->real^N) 0, vx 1, vx 2, vx 3}`] MOI_S4X_KK_EDGE) THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `(g:real^N->bool) SUBSET r` THEN UNDISCH_TAC `(r:real^N->bool) IN kk` THEN
    UNDISCH_TAC `r = convex hull {(vx:num->real^N) 0, vx 1, vx 2, vx 3}` THEN
    DISCH_THEN SUBST1_TAC THEN REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:real^N` (X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `?i. i < 4 /\ x = (vx:num->real^N) i` (X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      is_exists(rand(snd(dest_forall(concl th)))) &&
      can (find_term ((=) `{(vx:num->real^N) 0, vx 1, vx 2, vx 3}`)) (concl th))) THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `?j. j < 4 /\ y = (vx:num->real^N) j` (X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      is_exists(rand(snd(dest_forall(concl th)))) &&
      can (find_term ((=) `{(vx:num->real^N) 0, vx 1, vx 2, vx 3}`)) (concl th))) THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`i:num`; `j:num`] THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST_ALL_TAC THEN
  UNDISCH_TAC `~(x:real^N = y)` THEN ASM_REWRITE_TAC[]);;

(* The faces of kk in r are the four faces of r. *)

let MOI_S4X_RV_FACE_CLASS = prove
 (`!(tt:(real^N->bool)->bool) kk r vx s.
     moi_s34_tube tt kk /\ moi_s4x_rverts kk r vx /\
     s IN moi_s34_simp kk (&2) /\ s SUBSET r
     ==> ?l. l < 4 /\ s = moi_s4x_rface vx l`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MOI_S4X_RV_IN) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4X_RV_BASIC) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MOI_S4X_RV_SIZE) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4X_RV_PARTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4L_TUBE_TUBE) THEN
  UNDISCH_TAC `(s:real^N->bool) IN moi_s34_simp kk (&2)` THEN
  REWRITE_TAC[moi_s34_simp; IN_ELIM_THM] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`kk:(real^N->bool)->bool`; `s:real^N->bool`;
                 `{(vx:num->real^N) 0, vx 1, vx 2, vx 3}`] MOI_S4X_KK_FACE) THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `(s:real^N->bool) SUBSET r` THEN UNDISCH_TAC `(r:real^N->bool) IN kk` THEN
    UNDISCH_TAC `r = convex hull {(vx:num->real^N) 0, vx 1, vx 2, vx 3}` THEN
    DISCH_THEN SUBST1_TAC THEN REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real^N->bool` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `{(vx:num->real^N) 0, vx 1, vx 2, vx 3} HAS_SIZE 4` THEN
  REWRITE_TAC[HAS_SIZE] THEN STRIP_TAC THEN
  SUBGOAL_THEN `CARD(c:real^N->bool) = 3` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`{(vx:num->real^N) 0, vx 1, vx 2, vx 3}`; `c:real^N->bool`]
      MOI_S4X_AI_DIM) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `aff_dim(s:real^N->bool) = &2` THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[INT_ARITH `&2:int = x - &1 <=> x = &3`; INT_OF_NUM_EQ] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE(c:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[FINITE_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `?l. l < 4 /\ ~((vx:num->real^N) l IN c)` STRIP_ASSUME_TAC THENL
   [ASM_CASES_TAC `?l. l < 4 /\ ~((vx:num->real^N) l IN c)` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[NOT_EXISTS_THM; TAUT `~(a /\ ~b) <=> a ==> b`]) THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `{(vx:num->real^N) 0, vx 1, vx 2, vx 3} SUBSET c` ASSUME_TAC THENL
     [REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET] THEN ASM_SIMP_TAC[ARITH]; ALL_TAC] THEN
    MP_TAC(ISPECL [`{(vx:num->real^N) 0, vx 1, vx 2, vx 3}`; `c:real^N->bool`] CARD_SUBSET) THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `l:num` THEN ASM_REWRITE_TAC[moi_s4x_rface] THEN AP_TERM_TAC THEN
  MATCH_MP_TAC CARD_SUBSET_EQ THEN
  ASM_SIMP_TAC[FINITE_DELETE; CARD_DELETE; ARITH] THEN
  UNDISCH_TAC `(c:real^N->bool) SUBSET {vx 0, vx 1, vx 2, vx 3}` THEN
  UNDISCH_TAC `~((vx:num->real^N) l IN c)` THEN SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The tetra configuration at r: the four vertex balls of r, the rims of    *)
(* their splitting disks, the four face disks of r and their boundaries     *)
(* (RCONF).                                                                  *)
(* ------------------------------------------------------------------------- *)

(* A disk shared by the frontiers of two balls with disjoint interiors:    *)
(* its open part lies in the interior of the union.                         *)

let MOI_S4X_SD_OPEN = prove
 (`!b1 b2 e j:real^3->bool.
     pl_ball 3 b1 /\ pl_ball 3 b2 /\ b1 INTER b2 = e /\ pl_cell_with_boundary 2 e j /\
     e SUBSET frontier b1 /\ e SUBSET frontier b2
     ==> e DIFF j SUBSET interior(b1 UNION b2)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `b1:real^3->bool` MOI_S4X_BALL_INT) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `b2:real^3->bool` MOI_S4X_BALL_INT) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`frontier b1:real^3->bool`; `e:real^3->bool`; `j:real^3->bool`]
    DISK_COMPLEMENT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(ISPECL [`frontier b2:real^3->bool`; `e:real^3->bool`; `j:real^3->bool`]
    DISK_COMPLEMENT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN `closed((frontier b1 DIFF e) UNION j:real^3->bool) /\
                closed((frontier b2 DIFF e) UNION j:real^3->bool) /\
                (j:real^3->bool) SUBSET e`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(MATCH_MP_TAC COMPACT_IMP_CLOSED) THEN
    ASM_MESON_TAC[MOI_S4L_PL_CELL_FACTS];
    ALL_TAC] THEN
  SUBGOAL_THEN `interior b1 INTER interior b2:real^3->bool = {}` ASSUME_TAC THENL
   [MP_TAC(ISPEC `b1:real^3->bool` INTERIOR_SUBSET) THEN
    MP_TAC(ISPEC `b2:real^3->bool` INTERIOR_SUBSET) THEN
    UNDISCH_TAC `e SUBSET frontier(b1:real^3->bool)` THEN
    UNDISCH_TAC `b1 INTER b2:real^3->bool = e` THEN
    REWRITE_TAC[frontier] THEN SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
  MATCH_MP_TAC MOI_S4YC_BALLS_GLUE THEN ASM_REWRITE_TAC[DISJOINT] THEN CONJ_TAC THENL
   [UNDISCH_TAC `(x:real^3) IN e DIFF j` THEN
    UNDISCH_TAC `e SUBSET frontier(b1:real^3->bool)` THEN SET_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `(:real^3) DIFF (((frontier b1 DIFF e) UNION j) UNION ((frontier b2 DIFF e) UNION j))` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_DIFF THEN REWRITE_TAC[OPEN_UNIV] THEN
    MATCH_MP_TAC CLOSED_UNION THEN ASM_REWRITE_TAC[];
    UNDISCH_TAC `(x:real^3) IN e DIFF j` THEN SET_TAC[];
    MAP_EVERY UNDISCH_TAC
     [`e SUBSET frontier(b1:real^3->bool)`; `e SUBSET frontier(b2:real^3->bool)`] THEN
    SET_TAC[]]);;

(* The fdisk clauses for one face disk, and disjointness. *)

let MOI_S4X_FD = prove
 (`!(tt:(real^N->bool)->bool) kk (f1:real^N->real^3) car dd s.
     moi_s34_fdisk tt kk f1 car dd /\ s IN moi_s34_simp kk (&2)
     ==> pl_cell_with_boundary 2 (dd s) (dd s INTER IMAGE f1 (moi_s34_bd tt kk)) /\
         dd s INTER IMAGE f1 (moi_s34_nb tt kk) = dd s INTER IMAGE f1 (moi_s34_bd tt kk) /\
         dd s SUBSET car s /\
         (!w. {w} IN kk /\ ~(w IN s) ==> DISJOINT (dd s) (IMAGE f1 (moi_s34_vb tt kk w))) /\
         (!v. {v} IN kk /\ v IN s
              ==> pl_cell_with_boundary 1 (dd s INTER IMAGE f1 (moi_s34_vb tt kk v))
                    (UNIONS {dd s INTER IMAGE f1 (moi_s34_sd tt kk g) | g |
                             g IN moi_s34_simp kk (&1) /\ v IN g /\ g SUBSET s})) /\
         (!g. g IN moi_s34_simp kk (&1) /\ g SUBSET s
              ==> ?p. dd s INTER IMAGE f1 (moi_s34_sd tt kk g) = {p})`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s34_fdisk] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 (MP_TAC o SPEC `s:real^N->bool`) (K ALL_TAC))
    ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `g:real^N->bool` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `g:real^N->bool` o check (fun th ->
    is_forall(concl th) &&
    can (find_term ((=) `pl_curve_crossing_at:(real^3->bool)->(real^3->bool)->(real^3->bool)->real^3->bool`))
      (concl th))) THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

let MOI_S4X_FD2 = prove
 (`!(tt:(real^N->bool)->bool) kk (f1:real^N->real^3) car dd s s'.
     moi_s34_fdisk tt kk f1 car dd /\ s IN moi_s34_simp kk (&2) /\
     s' IN moi_s34_simp kk (&2) /\ ~(s = s')
     ==> DISJOINT (dd s) (dd s')`,
  REWRITE_TAC[moi_s34_fdisk] THEN MESON_TAC[]);;

(* The vertex balls of r and their splitting disks. *)

let MOI_S4X_RC_EDGE = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car r vx i j.
     moi_s34_tube tt kk /\ moi_s34_frame tt kk h ep f1 car /\ moi_s4x_rverts kk r vx /\
     i < 4 /\ j < 4 /\ ~(i = j)
     ==> IMAGE f1 (moi_s34_vb tt kk (vx i)) INTER IMAGE f1 (moi_s34_vb tt kk (vx j)) =
         IMAGE f1 (moi_s34_sd tt kk (segment[vx i,vx j])) /\
         pl_cell_with_boundary 2 (IMAGE f1 (moi_s34_sd tt kk (segment[vx i,vx j])))
           (IMAGE f1 (moi_s34_sd tt kk (segment[vx i,vx j]) INTER moi_s34_bd tt kk)) /\
         IMAGE f1 (moi_s34_sd tt kk (segment[vx i,vx j])) SUBSET
         frontier(IMAGE f1 (moi_s34_vb tt kk (vx i))) /\
         segment[vx j,vx i] = segment[vx i,vx j]`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `r:real^N->bool`;
                 `vx:num->real^N`; `i:num`; `j:num`] MOI_S4X_RV_EDGE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4X_RV_PARTS) THEN
  REWRITE_TAC[SEGMENT_SYM] THEN REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                   `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`]
                  MOI_S4L_IMAGES) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4L_GRAPH_TUBE) THEN
    CONJ_TAC THEN FIRST_X_ASSUM(MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `pl_cell_with_boundary 3:(real^N->bool)->(real^N->bool)->bool`))
        (concl th))) THENL
     [DISCH_THEN(MP_TAC o SPEC `(vx:num->real^N) i`);
      DISCH_THEN(MP_TAC o SPEC `(vx:num->real^N) j`)] THEN
    ASM_SIMP_TAC[];
    UNDISCH_TAC `moi_s34_frame tt kk (h:real^N->real^3) ep f1 car` THEN
    REWRITE_TAC[moi_s34_frame] THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    FIRST_ASSUM ACCEPT_TAC;
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                   `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                   `(vx:num->real^N) i`] MOI_S4L_AV_BASIC) THEN
    ASM_SIMP_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(SET_RULE `!a b (u:(real^3->bool)->bool). a IN u ==> a SUBSET b UNION UNIONS u`) THEN
    REWRITE_TAC[IN_ELIM_THM] THEN
    EXISTS_TAC `segment[(vx:num->real^N) i,vx j]` THEN
    ASM_REWRITE_TAC[ENDS_IN_SEGMENT]]);;

(* The edges of kk at a vertex of r inside a face of r. *)

let MOI_S4X_RV_VEDGES = prove
 (`!(tt:(real^N->bool)->bool) kk r vx i j k l g.
     moi_s34_tube tt kk /\ moi_s4x_rverts kk r vx /\
     i < 4 /\ j < 4 /\ k < 4 /\ l < 4 /\
     ~(i = j) /\ ~(i = k) /\ ~(i = l) /\ ~(j = k) /\ ~(j = l) /\ ~(k = l)
     ==> (g IN moi_s34_simp kk (&1) /\ vx i IN g /\ g SUBSET moi_s4x_rface vx l <=>
          g = segment[vx i,vx j] \/ g = segment[vx i,vx k])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN EQ_TAC THENL
   [STRIP_TAC THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `r:real^N->bool`;
                   `vx:num->real^N`; `g:real^N->bool`] MOI_S4X_RV_EDGE_CLASS) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `moi_s4x_rface (vx:num->real^N) l` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC MOI_S4X_RV_FACE_SUB THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `a:num` (X_CHOOSE_THEN `b:num` STRIP_ASSUME_TAC)) THEN
    UNDISCH_TAC `(vx:num->real^N) i IN g` THEN UNDISCH_TAC `g SUBSET moi_s4x_rface (vx:num->real^N) l` THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`kk:(real^N->bool)->bool`; `r:real^N->bool`; `vx:num->real^N`;
                   `a:num`; `b:num`; `l:num`] MOI_S4X_RV_SEG_FACE) THEN
    MP_TAC(ISPECL [`kk:(real^N->bool)->bool`; `r:real^N->bool`; `vx:num->real^N`;
                   `a:num`; `b:num`; `i:num`] MOI_S4X_RV_SEG) THEN
    ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN
    MP_TAC(SPECL [`i:num`; `j:num`; `k:num`; `l:num`] MOI_S4X_PERM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `(a:num) = i \/ a = j \/ a = k \/ a = l` MP_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(b:num) = i \/ b = j \/ b = k \/ b = l` MP_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[SEGMENT_SYM] THEN
    REPEAT STRIP_TAC THEN ASM_MESON_TAC[SEGMENT_SYM];
    STRIP_TAC THEN ASM_REWRITE_TAC[ENDS_IN_SEGMENT] THENL
     [MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `r:real^N->bool`;
                     `vx:num->real^N`; `i:num`; `j:num`] MOI_S4X_RV_EDGE) THEN
      MP_TAC(ISPECL [`kk:(real^N->bool)->bool`; `r:real^N->bool`; `vx:num->real^N`;
                     `i:num`; `j:num`; `l:num`] MOI_S4X_RV_SEG_FACE);
      MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `r:real^N->bool`;
                     `vx:num->real^N`; `i:num`; `k:num`] MOI_S4X_RV_EDGE) THEN
      MP_TAC(ISPECL [`kk:(real^N->bool)->bool`; `r:real^N->bool`; `vx:num->real^N`;
                     `i:num`; `k:num`; `l:num`] MOI_S4X_RV_SEG_FACE)] THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[]]);;

(* f1(N) is the union of the vertex balls. *)

let MOI_S4X_FN = prove
 (`!(tt:(real^N->bool)->bool) kk (f1:real^N->real^3).
     moi_s34_tube tt kk
     ==> IMAGE f1 (moi_s34_nb tt kk) = UNIONS {IMAGE f1 (moi_s34_vb tt kk v) | v | {v} IN kk}`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[CONJUNCT1(MATCH_MP MOI_S4L_GRAPH_TUBE th)]) THEN
  REWRITE_TAC[IMAGE_UNIONS] THEN AP_TERM_TAC THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN MESON_TAC[]);;

(* The face disk of r opposite vx l: boundary and traces on the balls. *)

let MOI_S4X_RC_FACE = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car dd r vx l.
     moi_s34_tube tt kk /\ moi_s34_frame tt kk h ep f1 car /\ moi_s34_fdisk tt kk f1 car dd /\
     moi_s4x_rverts kk r vx /\ l < 4
     ==> pl_cell_with_boundary 2 (dd (moi_s4x_rface vx l))
           (dd (moi_s4x_rface vx l) INTER IMAGE f1 (moi_s34_bd tt kk)) /\
         dd (moi_s4x_rface vx l) INTER IMAGE f1 (moi_s34_vb tt kk (vx l)) = {} /\
         dd (moi_s4x_rface vx l) INTER IMAGE f1 (moi_s34_bd tt kk) =
         UNIONS {dd (moi_s4x_rface vx l) INTER IMAGE f1 (moi_s34_vb tt kk (vx i)) | i | i < 4}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(!i. i < 4 ==> {(vx:num->real^N) i} IN kk) /\
    (!v. v IN r /\ {v} IN kk ==> ?i. i < 4 /\ v = (vx:num->real^N) i) /\
    moi_s4x_rface vx l SUBSET r /\ ~((vx:num->real^N) l IN moi_s4x_rface vx l)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[MOI_S4X_RV_PARTS];
      ASM_MESON_TAC[MOI_S4X_RV_PARTS];
      MATCH_MP_TAC MOI_S4X_RV_FACE_SUB THEN ASM_MESON_TAC[];
      MP_TAC(ISPECL [`kk:(real^N->bool)->bool`; `r:real^N->bool`; `vx:num->real^N`;
                     `l:num`; `l:num`] MOI_S4X_RV_FACE) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`kk:(real^N->bool)->bool`; `r:real^N->bool`; `vx:num->real^N`; `l:num`]
    MOI_S4X_RV_FACE_IN) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `dd:(real^N->bool)->real^3->bool`;
                 `moi_s4x_rface (vx:num->real^N) l`] MOI_S4X_FD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[GSYM DISJOINT] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
    can (find_term ((=) `moi_s34_nb (tt:(real^N->bool)->bool) kk`)) (concl th))) THEN
  ASM_SIMP_TAC[MOI_S4X_FN] THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_INTER; IN_UNIONS; IN_ELIM_THM] THEN
  X_GEN_TAC `x:real^3` THEN EQ_TAC THENL
   [DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `t:real^3->bool`
      (CONJUNCTS_THEN2 (X_CHOOSE_THEN `v:real^N` STRIP_ASSUME_TAC) ASSUME_TAC))) THEN
    ASM_CASES_TAC `(v:real^N) IN moi_s4x_rface vx l` THENL
     [SUBGOAL_THEN `?m. m < 4 /\ v = (vx:num->real^N) m` STRIP_ASSUME_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
          can (find_term ((=) `r:real^N->bool`)) (concl th) &&
          is_exists(rand(snd(dest_forall(concl th)))))) THEN
        ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `(v:real^N) IN moi_s4x_rface vx l` THEN
        UNDISCH_TAC `moi_s4x_rface (vx:num->real^N) l SUBSET r` THEN SET_TAC[];
        ALL_TAC] THEN
      EXISTS_TAC `dd (moi_s4x_rface (vx:num->real^N) l) INTER
                  IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk (vx(m:num)))` THEN
      CONJ_TAC THENL [EXISTS_TAC `m:num` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `(x:real^3) IN t` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(x:real^3) IN dd (moi_s4x_rface (vx:num->real^N) l)` THEN SET_TAC[];
      FIRST_X_ASSUM(MP_TAC o SPEC `v:real^N` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `DISJOINT:(real^3->bool)->(real^3->bool)->bool`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN
      MAP_EVERY UNDISCH_TAC
       [`(x:real^3) IN t`; `(x:real^3) IN dd (moi_s4x_rface (vx:num->real^N) l)`] THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[]];
    DISCH_THEN(X_CHOOSE_THEN `t:real^3->bool` (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `m:num` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
    UNDISCH_TAC `(x:real^3) IN t` THEN ASM_REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk (vx(m:num)))` THEN
    ASM_REWRITE_TAC[] THEN EXISTS_TAC `(vx:num->real^N) m` THEN ASM_SIMP_TAC[]]);;

(* Face points and face arcs of the face disk of r opposite vx l. *)

let MOI_S4X_RC_FPT = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car dd r vx l i j k.
     moi_s34_tube tt kk /\ moi_s34_frame tt kk h ep f1 car /\ moi_s34_fdisk tt kk f1 car dd /\
     moi_s4x_rverts kk r vx /\
     l < 4 /\ i < 4 /\ j < 4 /\ k < 4 /\
     ~(l = i) /\ ~(l = j) /\ ~(l = k) /\ ~(i = j) /\ ~(i = k) /\ ~(j = k)
     ==> (?x. dd (moi_s4x_rface vx l) INTER IMAGE f1 (moi_s34_vb tt kk (vx i)) INTER
              IMAGE f1 (moi_s34_vb tt kk (vx j)) = {x}) /\
         pl_cell_with_boundary 1
           (dd (moi_s4x_rface vx l) INTER IMAGE f1 (moi_s34_vb tt kk (vx i)))
           ((dd (moi_s4x_rface vx l) INTER IMAGE f1 (moi_s34_vb tt kk (vx i)) INTER
             IMAGE f1 (moi_s34_vb tt kk (vx j))) UNION
            (dd (moi_s4x_rface vx l) INTER IMAGE f1 (moi_s34_vb tt kk (vx i)) INTER
             IMAGE f1 (moi_s34_vb tt kk (vx k))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(!m. m < 4 ==> {(vx:num->real^N) m} IN kk) /\ (vx:num->real^N) i IN moi_s4x_rface vx l`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [ASM_MESON_TAC[MOI_S4X_RV_PARTS];
      MP_TAC(ISPECL [`kk:(real^N->bool)->bool`; `r:real^N->bool`; `vx:num->real^N`;
                     `i:num`; `l:num`] MOI_S4X_RV_FACE) THEN
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`kk:(real^N->bool)->bool`; `r:real^N->bool`; `vx:num->real^N`; `l:num`]
    MOI_S4X_RV_FACE_IN) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `dd:(real^N->bool)->real^3->bool`;
                 `moi_s4x_rface (vx:num->real^N) l`] MOI_S4X_FD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                 `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                 `r:real^N->bool`; `vx:num->real^N`; `i:num`; `j:num`] MOI_S4X_RC_EDGE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                 `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                 `r:real^N->bool`; `vx:num->real^N`; `i:num`; `k:num`] MOI_S4X_RC_EDGE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `r:real^N->bool`;
                   `vx:num->real^N`; `i:num`; `j:num`] MOI_S4X_RV_EDGE) THEN
    MP_TAC(ISPECL [`kk:(real^N->bool)->bool`; `r:real^N->bool`; `vx:num->real^N`;
                   `i:num`; `j:num`; `l:num`] MOI_S4X_RV_SEG_FACE) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(vx:num->real^N) i` o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `pl_cell_with_boundary 1:(real^3->bool)->(real^3->bool)->bool`))
      (concl th))) THEN
  ASM_SIMP_TAC[] THEN
  MATCH_MP_TAC(TAUT `(a <=> b) ==> a ==> b`) THEN AP_TERM_TAC THEN
  MP_TAC(GEN `g:real^N->bool` (ISPECL
    [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `r:real^N->bool`; `vx:num->real^N`;
     `i:num`; `j:num`; `k:num`; `l:num`; `g:real^N->bool`] MOI_S4X_RV_VEDGES)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_UNIONS; IN_ELIM_THM; IN_UNION] THEN
  MESON_TAC[]);;

(* The tetra configuration at r. *)

let MOI_S4X_RCONF = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car dd r vx.
     moi_s34_tube tt kk /\ moi_s34_frame tt kk h ep f1 car /\ moi_s34_fdisk tt kk f1 car dd /\
     moi_s4x_rverts kk r vx
     ==> moi_s4x_tconf (\i. IMAGE f1 (moi_s34_vb tt kk (vx i)))
           (\i j. IMAGE f1 (moi_s34_sd tt kk (segment[vx i,vx j]) INTER moi_s34_bd tt kk))
           (\l. dd (moi_s4x_rface vx l))
           (\l. dd (moi_s4x_rface vx l) INTER IMAGE f1 (moi_s34_bd tt kk))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(!m. m < 4 ==> {(vx:num->real^N) m} IN kk) /\
    (!i j. i < 4 /\ j < 4 ==> ((vx:num->real^N) i = vx j <=> i = j))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_MESON_TAC[MOI_S4X_RV_PARTS]; ASM_MESON_TAC[MOI_S4X_RV_BASIC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!m. m < 4 ==> pl_ball 3 (IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk (vx m)))`
  ASSUME_TAC THENL
   [X_GEN_TAC `m:num` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                   `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                   `(vx:num->real^N) m`] MOI_S4L_AV_BASIC) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[moi_s4x_tconf] THEN BETA_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [(* edges *)
    MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                   `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                   `r:real^N->bool`; `vx:num->real^N`; `i:num`; `j:num`] MOI_S4X_RC_EDGE) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                   `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                   `r:real^N->bool`; `vx:num->real^N`; `j:num`; `i:num`] MOI_S4X_RC_EDGE) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_S4X_SD_OPEN THEN ASM_SIMP_TAC[];
    (* triple intersections *)
    MAP_EVERY X_GEN_TAC [`i:num`; `j:num`; `k:num`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                   `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`]
                  MOI_S4L_IMAGES) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL [`(vx:num->real^N) i`; `(vx:num->real^N) j`; `(vx:num->real^N) k`] o
      CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
    ASM_SIMP_TAC[];
    (* face disks *)
    X_GEN_TAC `l:num` THEN DISCH_TAC THEN
    MATCH_MP_TAC MOI_S4X_RC_FACE THEN
    MAP_EVERY EXISTS_TAC [`h:real^N->real^3`; `ep:real^N->real`; `car:(real^N->bool)->real^3->bool`;
                          `r:real^N->bool`] THEN
    ASM_REWRITE_TAC[];
    (* disjoint face disks *)
    MAP_EVERY X_GEN_TAC [`l:num`; `m:num`] THEN STRIP_TAC THEN
    MATCH_MP_TAC MOI_S4X_FD2 THEN
    MAP_EVERY EXISTS_TAC [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                          `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`kk:(real^N->bool)->bool`; `r:real^N->bool`; `vx:num->real^N`; `l:num`]
      MOI_S4X_RV_FACE_IN) THEN
    MP_TAC(ISPECL [`kk:(real^N->bool)->bool`; `r:real^N->bool`; `vx:num->real^N`; `m:num`]
      MOI_S4X_RV_FACE_IN) THEN
    MP_TAC(ISPECL [`kk:(real^N->bool)->bool`; `r:real^N->bool`; `vx:num->real^N`;
                   `l:num`; `m:num`] MOI_S4X_RV_FACE_INJ) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    (* face points and face arcs *)
    MAP_EVERY X_GEN_TAC [`l:num`; `i:num`; `j:num`; `k:num`] THEN STRIP_TAC THEN
    MATCH_MP_TAC MOI_S4X_RC_FPT THEN
    MAP_EVERY EXISTS_TAC [`h:real^N->real^3`; `ep:real^N->real`; `car:(real^N->bool)->real^3->bool`;
                          `r:real^N->bool`] THEN
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The tetra ball b = S UNION inside S of a tetra                          *)
(* configuration (generic part): b INTER V i = t i, foreign balls and face  *)
(* disks miss b, and the local side of b at an open patch point.            *)
(* ------------------------------------------------------------------------- *)

let moi_s4x_sph = new_definition
 `moi_s4x_sph (t:num->real^3->bool) (D:num->real^3->bool) =
    t 0 UNION t 1 UNION t 2 UNION t 3 UNION D 0 UNION D 1 UNION D 2 UNION D 3`;;

let moi_s4x_tball = new_definition
 `moi_s4x_tball (V:num->real^3->bool) (R:num->num->real^3->bool) (D:num->real^3->bool)
                (J:num->real^3->bool) (C:num->num->real^3->bool) (C':num->num->real^3->bool)
                (t:num->real^3->bool) (t':num->real^3->bool) <=>
   moi_s4x_tconf V R D J /\ moi_s4x_rimarcs V R D C C' /\
   (!i. i < 4 ==> moi_s4x_hex V D C C' i (t i) (t' i)) /\
   (!i j. i < 4 /\ j < 4 /\ ~(i = j) ==> t i INTER V j = t j INTER V i) /\
   pl_sphere 2 (moi_s4x_sph t D) /\
   (!i. i < 4 ==> interior(V i) SUBSET outside(moi_s4x_sph t D))`;;

let MOI_S4X_TETRA_TB = prove
 (`!V R D J. moi_s4x_tconf V R D J ==> ?C C' t t'. moi_s4x_tball V R D J C C' t t'`,
  REWRITE_TAC[moi_s4x_tball; moi_s4x_sph] THEN REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_S4X_TETRA) THEN
  REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN ASM_SIMP_TAC[]);;

let MOI_S4X_SPH_MEM = prove
 (`!t D (x:real^3).
     x IN moi_s4x_sph t D <=> (?j. j < 4 /\ x IN t j) \/ (?l. l < 4 /\ x IN D l)`,
  REWRITE_TAC[moi_s4x_sph; IN_UNION; MOI_S4X_LT4] THEN
  REWRITE_TAC[RIGHT_OR_DISTRIB; LEFT_OR_DISTRIB; EXISTS_OR_THM; UNWIND_THM2] THEN
  CONV_TAC TAUT);;

(* A ball whose interior lies outside a sphere lies in the sphere plus its  *)
(* outside.                                                                  *)

let MOI_S4X_BALL_OUT = prove
 (`!v s:real^3->bool.
     pl_ball 3 v /\ pl_sphere 2 s /\ interior v SUBSET outside s ==> v SUBSET s UNION outside s`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `v:real^3->bool` MOI_S4X_BALL_INT) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT1) THEN
  MP_TAC(ISPEC `s:real^3->bool` MOI_S4X_JB) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `closure(outside s:real^3->bool)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUBSET_CLOSURE THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[SUBSET_REFL]]);;

(* Facts of a tetra ball configuration. *)

let MOI_S4X_TB_FACTS = prove
 (`!V R D J C C' t t'.
     moi_s4x_tball V R D J C C' t t'
     ==> (!i. i < 4 ==> pl_ball 3 (V i) /\ t i SUBSET V i /\ t' i SUBSET V i /\
                        t i SUBSET frontier(V i) /\ t' i SUBSET frontier(V i) /\
                        V i SUBSET moi_s4x_sph t D UNION outside(moi_s4x_sph t D) /\
                        V i INTER inside(moi_s4x_sph t D) = {} /\
                        t i SUBSET moi_s4x_sph t D /\ closed(t i) /\ closed(t' i) /\
                        t i INTER t' i = UNIONS {D m INTER V i | m | m < 4} /\
                        t i UNION t' i UNION UNIONS {V i INTER V m | m | m < 4 /\ ~(m = i)} =
                        frontier(V i) /\
                        UNIONS {D m INTER V i | m | m < 4} SUBSET t i) /\
         (!l. l < 4 ==> D l SUBSET moi_s4x_sph t D)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s4x_tball] THEN STRIP_TAC THEN
  CONJ_TAC THENL [ALL_TAC; REWRITE_TAC[moi_s4x_sph; MOI_S4X_LT4] THEN GEN_TAC THEN
    DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) THEN SET_TAC[]] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `pl_ball 3 ((V:num->real^3->bool) i)` ASSUME_TAC THENL
   [UNDISCH_TAC `moi_s4x_tconf V (R:num->num->real^3->bool) (D:num->real^3->bool) (J:num->real^3->bool)` THEN
    REWRITE_TAC[moi_s4x_tconf] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `moi_s4x_hex:(num->real^3->bool)->(num->real^3->bool)->
      (num->num->real^3->bool)->(num->num->real^3->bool)->num->(real^3->bool)->(real^3->bool)->bool`))
      (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`V:num->real^3->bool`; `R:num->num->real^3->bool`; `D:num->real^3->bool`;
                 `J:num->real^3->bool`; `C:num->num->real^3->bool`;
                 `C':num->num->real^3->bool`; `i:num`; `(t:num->real^3->bool) i`;
                 `(t':num->real^3->bool) i`] MOI_S4X_HEX_SUBSET) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `moi_s4x_hex V (D:num->real^3->bool) (C:num->num->real^3->bool)
                 (C':num->num->real^3->bool) i (t i) ((t':num->real^3->bool) i)` THEN
  REWRITE_TAC[moi_s4x_hex] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(V:num->real^3->bool) i SUBSET moi_s4x_sph t D UNION outside(moi_s4x_sph t D)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S4X_BALL_OUT THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MP_TAC(ISPEC `moi_s4x_sph t D` MOI_S4X_JB) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MAP_EVERY UNDISCH_TAC
     [`(V:num->real^3->bool) i SUBSET moi_s4x_sph t D UNION outside(moi_s4x_sph t D)`;
      `inside(moi_s4x_sph t D) INTER outside(moi_s4x_sph t D) = {}`;
      `moi_s4x_sph t D INTER inside(moi_s4x_sph t D) = {}`] THEN
    SET_TAC[];
    REWRITE_TAC[SUBSET; MOI_S4X_SPH_MEM] THEN GEN_TAC THEN DISCH_TAC THEN DISJ1_TAC THEN
    EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[];
    ASM_MESON_TAC[MOI_S4L_PL_CELL_FACTS; COMPACT_IMP_CLOSED];
    ASM_MESON_TAC[MOI_S4L_PL_CELL_FACTS; COMPACT_IMP_CLOSED];
    FIRST_X_ASSUM(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o MATCH_MP MOI_S4L_PL_CELL_FACTS o
      check (fun th -> can (find_term ((=) `(t:num->real^3->bool) i`)) (concl th) &&
                       is_comb(concl th) &&
                       can (find_term ((=) `pl_cell_with_boundary 2:(real^3->bool)->(real^3->bool)->bool`)) (concl th) &&
                       not(can (find_term ((=) `(t':num->real^3->bool) i`)) (concl th)))) THEN
    SET_TAC[]]);;

(* The trace of the tetra ball on a vertex ball is the chosen hexagon. *)

let MOI_S4X_TB_PATCH = prove
 (`!V R D J C C' t t' i.
     moi_s4x_tball V R D J C C' t t' /\ i < 4
     ==> V i INTER (moi_s4x_sph t D UNION inside(moi_s4x_sph t D)) = t i`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_S4X_TB_FACTS) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o SPEC `i:num`) ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!j. j < 4 /\ ~(j = i) ==> (t:num->real^3->bool) j INTER V i = t i INTER V j`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    UNDISCH_TAC `moi_s4x_tball V (R:num->num->real^3->bool) D (J:num->real^3->bool)
                   (C:num->num->real^3->bool) (C':num->num->real^3->bool) t t'` THEN
    REWRITE_TAC[moi_s4x_tball] THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [ALL_TAC;
    MAP_EVERY UNDISCH_TAC
     [`(t:num->real^3->bool) i SUBSET V i`; `(t:num->real^3->bool) i SUBSET moi_s4x_sph t D`] THEN
    SET_TAC[]] THEN
  REWRITE_TAC[SUBSET; IN_INTER; IN_UNION; MOI_S4X_SPH_MEM] THEN X_GEN_TAC `x:real^3` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(DISJ_CASES_THEN MP_TAC) THENL
   [DISCH_THEN(DISJ_CASES_THEN (X_CHOOSE_THEN `m:num` STRIP_ASSUME_TAC)) THENL
     [ASM_CASES_TAC `m:num = i` THENL
       [UNDISCH_TAC `(x:real^3) IN (t:num->real^3->bool) m` THEN ASM_REWRITE_TAC[];
        FIRST_X_ASSUM(MP_TAC o SPEC `m:num` o check (fun th -> is_forall(concl th) &&
          is_imp(snd(dest_forall(concl th))) &&
          is_eq(rand(snd(dest_forall(concl th)))))) THEN
        ASM_REWRITE_TAC[] THEN
        MAP_EVERY UNDISCH_TAC [`(x:real^3) IN (t:num->real^3->bool) m`;
                               `(x:real^3) IN (V:num->real^3->bool) i`] THEN
        SET_TAC[]];
      UNDISCH_TAC `UNIONS {(D:num->real^3->bool) m INTER (V:num->real^3->bool) i | m | m < 4}
                   SUBSET (t:num->real^3->bool) i` THEN
      REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN DISCH_THEN MATCH_MP_TAC THEN
      EXISTS_TAC `(D:num->real^3->bool) m INTER (V:num->real^3->bool) i` THEN
      CONJ_TAC THENL [EXISTS_TAC `m:num` THEN ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[IN_INTER]]];
    DISCH_TAC THEN
    UNDISCH_TAC `(V:num->real^3->bool) i INTER inside(moi_s4x_sph t D) = {}` THEN
    MAP_EVERY UNDISCH_TAC [`(x:real^3) IN inside(moi_s4x_sph t D)`;
                           `(x:real^3) IN (V:num->real^3->bool) i`] THEN
    SET_TAC[]]);;

(* A connected subset of the frontier of V i missing the other balls and    *)
(* the face disks lies in the hexagon t i or misses it.                      *)

let MOI_S4X_TB_DISK_SIDE = prove
 (`!V R D J C C' t t' i (e:real^3->bool).
     moi_s4x_tball V R D J C C' t t' /\ i < 4 /\ connected e /\ e SUBSET frontier(V i) /\
     (!n. n < 4 /\ ~(n = i) ==> e INTER V n = {}) /\ (!n. n < 4 ==> e INTER D n = {})
     ==> e SUBSET t i \/ e INTER t i = {}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_S4X_TB_FACTS) THEN
  DISCH_THEN(MP_TAC o SPEC `i:num` o CONJUNCT1) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `e SUBSET (t:num->real^3->bool) i UNION t' i` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`e SUBSET frontier((V:num->real^3->bool) i)`;
      `!n. n < 4 /\ ~(n = i) ==> e INTER (V:num->real^3->bool) n = {}`;
      `(t:num->real^3->bool) i UNION t' i UNION
       UNIONS {(V:num->real^3->bool) i INTER V m | m | m < 4 /\ ~(m = i)} = frontier(V i)`] THEN
    REWRITE_TAC[EXTENSION; SUBSET; IN_UNION; IN_UNIONS; IN_ELIM_THM; IN_INTER; NOT_IN_EMPTY] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `e INTER ((t:num->real^3->bool) i INTER t' i) = {}` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `!n. n < 4 ==> e INTER (D:num->real^3->bool) n = {}` THEN
    REWRITE_TAC[EXTENSION; IN_INTER; IN_UNIONS; IN_ELIM_THM; NOT_IN_EMPTY] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`e:real^3->bool`; `(t:num->real^3->bool) i`; `(t':num->real^3->bool) i`;
                 `(t:num->real^3->bool) i INTER t' i`] MOI_SFR_CONNECTED_SIDE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(DISJ_CASES_THEN ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
  DISJ2_TAC THEN
  MAP_EVERY UNDISCH_TAC
   [`e SUBSET (t':num->real^3->bool) i`; `e INTER ((t:num->real^3->bool) i INTER t' i) = {}`] THEN
  SET_TAC[]);;

(* A foreign ball meeting the vertex balls only in disks of their frontiers *)
(* and having a point outside the sphere misses the tetra ball.             *)

let MOI_S4X_TB_FOREIGN = prove
 (`!V R D J C C' t t' (W:real^3->bool) Q (z0:real^3).
     moi_s4x_tball V R D J C C' t t' /\ pl_ball 3 W /\
     (!l. l < 4 ==> W INTER D l = {}) /\
     (!i j. i < 4 /\ j < 4 /\ ~(i = j) ==> W INTER V i INTER V j = {}) /\
     (!i. i < 4 ==> W INTER V i = {} \/
                    (pl_cell_with_boundary 2 (W INTER V i) (Q i) /\
                     W INTER V i SUBSET frontier(V i) /\ W INTER V i SUBSET frontier W /\
                     (W INTER V i) DIFF Q i SUBSET interior(V i UNION W))) /\
     z0 IN W /\ z0 IN outside(moi_s4x_sph t D)
     ==> W INTER (moi_s4x_sph t D UNION inside(moi_s4x_sph t D)) = {}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_S4X_TB_FACTS) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "vf") (LABEL_TAC "df")) THEN
  SUBGOAL_THEN `pl_sphere 2 (moi_s4x_sph t D)` ASSUME_TAC THENL
   [UNDISCH_TAC `moi_s4x_tball V (R:num->num->real^3->bool) D (J:num->real^3->bool)
                   (C:num->num->real^3->bool) (C':num->num->real^3->bool) t t'` THEN
    REWRITE_TAC[moi_s4x_tball] THEN SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `S = moi_s4x_sph (t:num->real^3->bool) D` THEN
  MP_TAC(ISPEC `S:real^3->bool` MOI_S4X_JB) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `W:real^3->bool` MOI_S4X_BALL_INT) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  (* the interior of W misses S *)
  SUBGOAL_THEN `interior W INTER S:real^3->bool = {}` ASSUME_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `moi_s4x_sph (t:num->real^3->bool) (D:num->real^3->bool) = S`)) THEN REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY; MOI_S4X_SPH_MEM] THEN
    X_GEN_TAC `x:real^3` THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (DISJ_CASES_THEN
      (X_CHOOSE_THEN `m:num` STRIP_ASSUME_TAC))) THENL
     [USE_THEN "vf" (MP_TAC o SPEC `m:num`) THEN ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `m:num` o check (fun th -> is_forall(concl th) &&
        is_disj(rand(snd(dest_forall(concl th)))))) THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPEC `W:real^3->bool` INTERIOR_SUBSET) THEN
      MAP_EVERY UNDISCH_TAC
       [`(x:real^3) IN interior W`; `(x:real^3) IN (t:num->real^3->bool) m`;
        `(t:num->real^3->bool) m SUBSET V m`] THEN
      REWRITE_TAC[frontier] THEN SET_TAC[];
      FIRST_X_ASSUM(MP_TAC o SPEC `m:num` o check (fun th -> is_forall(concl th) &&
        is_eq(rand(snd(dest_forall(concl th)))))) THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPEC `W:real^3->bool` INTERIOR_SUBSET) THEN
      MAP_EVERY UNDISCH_TAC [`(x:real^3) IN interior W`; `(x:real^3) IN (D:num->real^3->bool) m`] THEN
      SET_TAC[]];
    ALL_TAC] THEN
  (* hence it lies outside S, and W lies in S UNION outside S *)
  SUBGOAL_THEN `interior W SUBSET outside(S:real^3->bool)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`S:real^3->bool`; `interior W:real^3->bool`] MOI_S4X_SIDE3) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC ACCEPT_TAC) THEN
    SUBGOAL_THEN `(z0:real^3) IN closure(inside S)` MP_TAC THENL
     [UNDISCH_TAC `closure(interior W) = W:real^3->bool` THEN
      DISCH_THEN(MP_TAC o AP_TERM `\u:real^3->bool. (z0:real^3) IN u`) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`interior W:real^3->bool`; `inside S:real^3->bool`] SUBSET_CLOSURE) THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      ASM_REWRITE_TAC[] THEN
      MAP_EVERY UNDISCH_TAC
       [`(z0:real^3) IN outside S`; `inside S INTER outside S:real^3->bool = {}`;
        `S INTER outside S:real^3->bool = {}`] THEN
      SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `W SUBSET S UNION outside(S:real^3->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S4X_BALL_OUT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `W INTER inside S:real^3->bool = {}` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`W SUBSET S UNION outside(S:real^3->bool)`; `inside S INTER outside S:real^3->bool = {}`;
      `S INTER inside S:real^3->bool = {}`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  (* W misses the hexagons: a hexagon containing the disk W INTER V m would  *)
  (* put interior points of V m UNION W into the closure of inside S          *)
  SUBGOAL_THEN `!m. m < 4 ==> W INTER (t:num->real^3->bool) m = {}` ASSUME_TAC THENL
   [X_GEN_TAC `m:num` THEN DISCH_TAC THEN
    USE_THEN "vf" (MP_TAC o SPEC `m:num`) THEN ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `m:num` o check (fun th -> is_forall(concl th) &&
      is_disj(rand(snd(dest_forall(concl th)))))) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    DISCH_THEN(DISJ_CASES_THEN2 MP_TAC STRIP_ASSUME_TAC) THENL
     [UNDISCH_TAC `(t:num->real^3->bool) m SUBSET V m` THEN SET_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`V:num->real^3->bool`; `R:num->num->real^3->bool`; `D:num->real^3->bool`;
                   `J:num->real^3->bool`; `C:num->num->real^3->bool`;
                   `C':num->num->real^3->bool`; `t:num->real^3->bool`; `t':num->real^3->bool`;
                   `m:num`; `W INTER (V:num->real^3->bool) m`] MOI_S4X_TB_DISK_SIDE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [ASM_MESON_TAC[MOI_S4L_PL_CELL_FACTS];
        X_GEN_TAC `n:num` THEN STRIP_TAC THEN REWRITE_TAC[INTER_ASSOC] THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
        X_GEN_TAC `n:num` THEN DISCH_TAC THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `n:num` o check (fun th -> is_forall(concl th) &&
          is_eq(rand(snd(dest_forall(concl th)))))) THEN
        ASM_REWRITE_TAC[] THEN SET_TAC[]];
      ALL_TAC] THEN
    DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC MP_TAC) THENL
     [ALL_TAC; UNDISCH_TAC `(t:num->real^3->bool) m SUBSET V m` THEN SET_TAC[]] THEN
    FIRST_ASSUM(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o
      MATCH_MP MOI_S4L_PL_CELL2_TOPO o check (fun th ->
        can (find_term ((=) `(Q:num->real^3->bool) m`)) (concl th) &&
        can (find_term ((=) `pl_cell_with_boundary 2:(real^3->bool)->(real^3->bool)->bool`)) (concl th))) THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN DISCH_THEN(X_CHOOSE_TAC `z:real^3`) THEN
    SUBGOAL_THEN `interior((V:num->real^3->bool) m UNION W) INTER closure(inside S) = {}`
    MP_TAC THENL
     [ASM_SIMP_TAC[OPEN_INTER_CLOSURE_EQ_EMPTY; OPEN_INTERIOR] THEN
      MP_TAC(ISPEC `(V:num->real^3->bool) m UNION W` INTERIOR_SUBSET) THEN
      MAP_EVERY UNDISCH_TAC
       [`(V:num->real^3->bool) m INTER inside S = {}`; `W INTER inside S:real^3->bool = {}`] THEN
      SET_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC
     [`(z:real^3) IN W INTER (V:num->real^3->bool) m DIFF Q m`;
      `W INTER (V:num->real^3->bool) m DIFF Q m SUBSET interior (V m UNION W)`;
      `W INTER (V:num->real^3->bool) m SUBSET t m`;
      `(t:num->real^3->bool) m SUBSET S`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `W INTER S:real^3->bool = {}` ASSUME_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `moi_s4x_sph (t:num->real^3->bool) (D:num->real^3->bool) = S`)) THEN
    REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY; MOI_S4X_SPH_MEM] THEN
    X_GEN_TAC `x:real^3` THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (DISJ_CASES_THEN
      (X_CHOOSE_THEN `m:num` STRIP_ASSUME_TAC))) THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `m:num` o check (fun th -> is_forall(concl th) &&
        is_eq(rand(snd(dest_forall(concl th)))) &&
        can (find_term ((=) `t:num->real^3->bool`)) (concl th)));
      FIRST_X_ASSUM(MP_TAC o SPEC `m:num` o check (fun th -> is_forall(concl th) &&
        is_eq(rand(snd(dest_forall(concl th)))) &&
        can (find_term ((=) `D:num->real^3->bool`)) (concl th)))] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(x:real^3) IN W` THEN POP_ASSUM MP_TAC THEN SET_TAC[];
    ALL_TAC] THEN
  MAP_EVERY UNDISCH_TAC [`W INTER S:real^3->bool = {}`; `W INTER inside S:real^3->bool = {}`] THEN
  SET_TAC[]);;

(* Finite unions over the indices below 4 of closed sets are closed. *)

let MOI_S4X_CLOSED_UNIONS4 = prove
 (`!(f:num->real^3->bool) P.
     (!j. j < 4 ==> closed(f j)) ==> closed(UNIONS {f j | j | j < 4 /\ P j})`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CLOSED_UNIONS THEN CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `IMAGE (f:num->real^3->bool) {j | j < 4}` THEN
    SIMP_TAC[FINITE_IMAGE; FINITE_NUMSEG_LT] THEN SET_TAC[];
    REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[]]);;

(* The tetra ball near a point of an open hexagon: the complement of the   *)
(* interior of the vertex ball (MOI_S4YC_BALLS_SIDE).                        *)

let MOI_S4X_TB_SIDE = prove
 (`!V R D J C C' t t' i (y:real^3).
     moi_s4x_tball V R D J C C' t t' /\
     pl_ball 3 (moi_s4x_sph t D UNION inside(moi_s4x_sph t D)) /\
     i < 4 /\ y IN t i /\ (!l. l < 4 ==> ~(y IN D l)) /\
     (!j. j < 4 /\ ~(j = i) ==> ~(y IN V j))
     ==> ?v. open v /\ y IN v /\
             v INTER (moi_s4x_sph t D UNION inside(moi_s4x_sph t D)) = v DIFF interior(V i)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_S4X_TB_FACTS) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "vf") (LABEL_TAC "df")) THEN
  USE_THEN "vf" (MP_TAC o SPEC `i:num`) THEN ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `pl_sphere 2 (moi_s4x_sph t D) /\
                (!j. j < 4 ==> interior((V:num->real^3->bool) j) SUBSET outside(moi_s4x_sph t D)) /\
                (!j. j < 4 ==> closed((V:num->real^3->bool) j)) /\
                (!l. l < 4 ==> closed((D:num->real^3->bool) l))`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `moi_s4x_tball V (R:num->num->real^3->bool) D (J:num->real^3->bool)
                   (C:num->num->real^3->bool) (C':num->num->real^3->bool) t t'` THEN
    REWRITE_TAC[moi_s4x_tball; moi_s4x_tconf] THEN STRIP_TAC THEN ASM_SIMP_TAC[] THEN
    CONJ_TAC THEN X_GEN_TAC `j:num` THEN DISCH_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `pl_ball 3:(real^3->bool)->bool`)) (concl th) &&
        length(fst(strip_forall(concl th))) = 1)) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP MOI_S4X_BALL_INT th]);
      FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `J:num->real^3->bool`)) (concl th) &&
        length(fst(strip_forall(concl th))) = 1)) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o CONJUNCT1 o MATCH_MP MOI_S4L_PL_CELL_FACTS o CONJUNCT1) THEN
      REWRITE_TAC[COMPACT_IMP_CLOSED]];
    ALL_TAC] THEN
  ABBREV_TAC `S = moi_s4x_sph (t:num->real^3->bool) D` THEN
  MP_TAC(ISPEC `S:real^3->bool` MOI_SCD_FILLED_FRONTIER) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> ASSUME_TAC(CONJUNCT1 th) THEN ASSUME_TAC(CONJUNCT1(CONJUNCT2 th))) THEN
  MP_TAC(ISPEC `S:real^3->bool` MOI_S4X_JB) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(y:real^3) IN S` ASSUME_TAC THENL
   [UNDISCH_TAC `(y:real^3) IN (t:num->real^3->bool) i` THEN
    UNDISCH_TAC `(t:num->real^3->bool) i SUBSET S` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `DISJOINT (inside S) (interior((V:num->real^3->bool) i))` ASSUME_TAC THENL
   [REWRITE_TAC[DISJOINT] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `outside:(real^3->bool)->real^3->bool`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `inside S INTER outside S:real^3->bool = {}` THEN SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_S4YC_BALLS_SIDE THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `Q = (t':num->real^3->bool) i UNION
                  UNIONS {(V:num->real^3->bool) j | j | j < 4 /\ ~(j = i)} UNION
                  UNIONS {(D:num->real^3->bool) l | l | l < 4 /\ T}` THEN
  SUBGOAL_THEN `closed(Q:real^3->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "Q" THEN
    REPEAT(MATCH_MP_TAC CLOSED_UNION THEN CONJ_TAC) THEN
    ASM_SIMP_TAC[MOI_S4X_CLOSED_UNIONS4];
    ALL_TAC] THEN
  EXISTS_TAC `(:real^3) DIFF Q` THEN
  ASM_SIMP_TAC[OPEN_DIFF; OPEN_UNIV] THEN
  SUBGOAL_THEN `!j. j < 4 /\ ~(j = i) ==> (V:num->real^3->bool) j SUBSET Q` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "Q" THEN
    MATCH_MP_TAC(SET_RULE `!a b c x:real^3->bool. x SUBSET b ==> x SUBSET a UNION b UNION c`) THEN
    MATCH_MP_TAC(SET_RULE `!x (f:(real^3->bool)->bool). x IN f ==> x SUBSET UNIONS f`) THEN
    REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `j:num` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!l. l < 4 ==> (D:num->real^3->bool) l SUBSET Q` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "Q" THEN
    MATCH_MP_TAC(SET_RULE `!a b c x:real^3->bool. x SUBSET c ==> x SUBSET a UNION b UNION c`) THEN
    MATCH_MP_TAC(SET_RULE `!x (f:(real^3->bool)->bool). x IN f ==> x SUBSET UNIONS f`) THEN
    REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `l:num` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(t':num->real^3->bool) i SUBSET Q` ASSUME_TAC THENL
   [EXPAND_TAC "Q" THEN SET_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN `~((y:real^3) IN Q)` (fun th -> MP_TAC th THEN SET_TAC[]) THEN
    EXPAND_TAC "Q" THEN REWRITE_TAC[IN_UNION; UNIONS_GSPEC; IN_ELIM_THM; DE_MORGAN_THM] THEN
    REWRITE_TAC[NOT_EXISTS_THM] THEN REPEAT CONJ_TAC THENL
     [DISCH_TAC THEN
      SUBGOAL_THEN `(y:real^3) IN UNIONS {(D:num->real^3->bool) m INTER (V:num->real^3->bool) i | m | m < 4}`
      MP_TAC THENL
       [UNDISCH_TAC `(t:num->real^3->bool) i INTER t' i = UNIONS {(D:num->real^3->bool) m INTER V i | m | m < 4}` THEN
        DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[IN_INTER];
        REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM; IN_INTER] THEN
        DISCH_THEN(X_CHOOSE_THEN `m:num` STRIP_ASSUME_TAC) THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `m:num` o check (fun th -> is_forall(concl th) &&
          can (find_term ((=) `D:num->real^3->bool`)) (concl th) &&
          can (find_term ((=) `y:real^3`)) (concl th))) THEN
        ASM_REWRITE_TAC[]];
      X_GEN_TAC `j:num` THEN
      DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC ASSUME_TAC) THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `V:num->real^3->bool`)) (concl th) &&
        can (find_term ((=) `y:real^3`)) (concl th))) THEN
      ASM_REWRITE_TAC[];
      X_GEN_TAC `l:num` THEN
      DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC ASSUME_TAC) THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `l:num` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `D:num->real^3->bool`)) (concl th) &&
        can (find_term ((=) `y:real^3`)) (concl th))) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* both frontiers agree off Q *)
  SUBGOAL_THEN `!j. j < 4 /\ ~(j = i) ==> (t:num->real^3->bool) j SUBSET Q` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `(V:num->real^3->bool) j` THEN ASM_SIMP_TAC[] THEN
    USE_THEN "vf" (MP_TAC o SPEC `j:num`) THEN ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `UNIONS {(V:num->real^3->bool) i INTER V m | m | m < 4 /\ ~(m = i)} SUBSET Q`
  ASSUME_TAC THENL
   [REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `(V:num->real^3->bool) m` THEN
    ASM_SIMP_TAC[INTER_SUBSET];
    ALL_TAC] THEN
  MATCH_MP_TAC(SET_RULE `!v a b c:real^3->bool. v INTER a = v INTER c /\ v INTER b = v INTER c
                                                 ==> v INTER a = v INTER b`) THEN
  EXISTS_TAC `(t:num->real^3->bool) i` THEN CONJ_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `moi_s4x_sph (t:num->real^3->bool) (D:num->real^3->bool) = S`)) THEN
    GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_INTER; IN_DIFF; IN_UNIV; MOI_S4X_SPH_MEM] THEN
    X_GEN_TAC `x:real^3` THEN ASM_CASES_TAC `(x:real^3) IN Q` THEN ASM_REWRITE_TAC[] THEN
    EQ_TAC THENL [ALL_TAC; DISCH_TAC THEN DISJ1_TAC THEN EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[]] THEN
    DISCH_THEN(DISJ_CASES_THEN (X_CHOOSE_THEN `m:num` STRIP_ASSUME_TAC)) THENL
     [ASM_CASES_TAC `m:num = i` THENL
       [UNDISCH_TAC `(x:real^3) IN (t:num->real^3->bool) m` THEN ASM_REWRITE_TAC[];
        UNDISCH_TAC `~((x:real^3) IN Q)` THEN
        SUBGOAL_THEN `(t:num->real^3->bool) m SUBSET Q` MP_TAC THENL
         [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
        UNDISCH_TAC `(x:real^3) IN (t:num->real^3->bool) m` THEN SET_TAC[]];
      UNDISCH_TAC `~((x:real^3) IN Q)` THEN
      SUBGOAL_THEN `(D:num->real^3->bool) m SUBSET Q` MP_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `(x:real^3) IN (D:num->real^3->bool) m` THEN SET_TAC[]];
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      rhs(concl th) = `frontier((V:num->real^3->bool) i)`)) THEN
    MAP_EVERY UNDISCH_TAC
     [`(t':num->real^3->bool) i SUBSET Q`;
      `UNIONS {(V:num->real^3->bool) i INTER V m | m | m < 4 /\ ~(m = i)} SUBSET Q`] THEN
    SET_TAC[]]);;

(* A disk whose open part lies outside the sphere and misses V i cannot     *)
(* meet the open hexagon t i.                                                *)

let MOI_S4X_TB_FACE_PT = prove
 (`!V R D J C C' t t' i (e:real^3->bool) je (y:real^3).
     moi_s4x_tball V R D J C C' t t' /\
     pl_ball 3 (moi_s4x_sph t D UNION inside(moi_s4x_sph t D)) /\
     pl_cell_with_boundary 2 e je /\ e DIFF je SUBSET outside(moi_s4x_sph t D) /\
     (e DIFF je) INTER V i = {} /\
     i < 4 /\ y IN e /\ y IN t i /\ (!l. l < 4 ==> ~(y IN D l)) /\
     (!j. j < 4 /\ ~(j = i) ==> ~(y IN V j))
     ==> F`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:num->real^3->bool`; `R:num->num->real^3->bool`; `D:num->real^3->bool`;
                 `J:num->real^3->bool`; `C:num->num->real^3->bool`;
                 `C':num->num->real^3->bool`; `t:num->real^3->bool`; `t':num->real^3->bool`;
                 `i:num`; `y:real^3`] MOI_S4X_TB_SIDE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real^3->bool` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4L_PL_CELL2_TOPO) THEN
  SUBGOAL_THEN `~(v INTER (e DIFF je):real^3->bool = {})` MP_TAC THENL
   [DISCH_TAC THEN
    MP_TAC(ISPECL [`v:real^3->bool`; `e DIFF je:real^3->bool`] OPEN_INTER_CLOSURE_EQ_EMPTY) THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC
     [`(y:real^3) IN e`; `(y:real^3) IN v`; `e SUBSET closure(e DIFF je:real^3->bool)`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o REWRITE_RULE[GSYM MEMBER_NOT_EMPTY; IN_INTER]) THEN
  DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(z:real^3) IN moi_s4x_sph t D UNION inside(moi_s4x_sph t D)` MP_TAC THENL
   [SUBGOAL_THEN `(z:real^3) IN v DIFF interior((V:num->real^3->bool) i)` MP_TAC THENL
     [MP_TAC(ISPEC `(V:num->real^3->bool) i` INTERIOR_SUBSET) THEN
      MAP_EVERY UNDISCH_TAC
       [`(z:real^3) IN v`; `(z:real^3) IN e DIFF je`;
        `(e DIFF je) INTER (V:num->real^3->bool) i = {}`] THEN
      SET_TAC[];
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
        can (find_term ((=) `v:real^3->bool`)) (lhs(concl th)))) THEN
      SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_sphere 2 (moi_s4x_sph t D)` ASSUME_TAC THENL
   [UNDISCH_TAC `moi_s4x_tball V (R:num->num->real^3->bool) D (J:num->real^3->bool)
                   (C:num->num->real^3->bool) (C':num->num->real^3->bool) t t'` THEN
    REWRITE_TAC[moi_s4x_tball] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `moi_s4x_sph t D` MOI_S4X_JB) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MAP_EVERY UNDISCH_TAC
   [`(z:real^3) IN e DIFF je`; `e DIFF je SUBSET outside(moi_s4x_sph t D)`;
    `moi_s4x_sph t D INTER outside(moi_s4x_sph t D) = {}`;
    `inside(moi_s4x_sph t D) INTER outside(moi_s4x_sph t D) = {}`] THEN
  SET_TAC[]);;

(* A connected set covered by a closed set and one point, meeting the closed *)
(* set: the point lies in the closed set.                                    *)

let MOI_S4X_CONN_PT = prove
 (`!a u (y:real^3).
     connected a /\ closed u /\ a SUBSET u UNION {y} /\ y IN a /\ ~(a INTER u = {})
     ==> y IN u`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [CONNECTED_CLOSED] o check (fun th ->
    is_comb(concl th) && rator(concl th) = `connected:(real^3->bool)->bool`)) THEN
  REWRITE_TAC[NOT_EXISTS_THM] THEN
  DISCH_THEN(MP_TAC o SPECL [`u:real^3->bool`; `{y:real^3}`]) THEN
  ASM_REWRITE_TAC[CLOSED_SING] THEN
  MAP_EVERY UNDISCH_TAC [`(a:real^3->bool) SUBSET u UNION {y}`; `(y:real^3) IN a`;
                         `~((a:real^3->bool) INTER u = {})`] THEN
  SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The clauses of moi_s4x_local for the tetra ball at r.                    *)
(* ------------------------------------------------------------------------- *)

(* The vertex balls of the two ends of an edge of kk. *)

let MOI_S4X_GEN_EDGE = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car u w.
     moi_s34_tube tt kk /\ moi_s34_frame tt kk h ep f1 car /\
     {u} IN kk /\ {w} IN kk /\ ~(u = w) /\ segment[u,w] IN kk
     ==> segment[u,w] IN moi_s34_simp kk (&1) /\
         IMAGE f1 (moi_s34_vb tt kk u) INTER IMAGE f1 (moi_s34_vb tt kk w) =
         IMAGE f1 (moi_s34_sd tt kk (segment[u,w])) /\
         pl_cell_with_boundary 2 (IMAGE f1 (moi_s34_sd tt kk (segment[u,w])))
           (IMAGE f1 (moi_s34_sd tt kk (segment[u,w]) INTER moi_s34_bd tt kk)) /\
         IMAGE f1 (moi_s34_sd tt kk (segment[u,w])) SUBSET
         frontier(IMAGE f1 (moi_s34_vb tt kk u)) /\
         IMAGE f1 (moi_s34_sd tt kk (segment[u,w])) SUBSET
         frontier(IMAGE f1 (moi_s34_vb tt kk w)) /\
         IMAGE f1 (moi_s34_sd tt kk (segment[u,w])) DIFF
         IMAGE f1 (moi_s34_sd tt kk (segment[u,w]) INTER moi_s34_bd tt kk) SUBSET
         interior(IMAGE f1 (moi_s34_vb tt kk u) UNION IMAGE f1 (moi_s34_vb tt kk w))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `segment[u:real^N,w] IN moi_s34_simp kk (&1)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[moi_s34_simp; IN_ELIM_THM; AFF_DIM_SEGMENT]; ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk u) INTER IMAGE f1 (moi_s34_vb tt kk w) =
                IMAGE f1 (moi_s34_sd tt kk (segment[u,w]))` ASSUME_TAC THENL
   [SUBGOAL_THEN `moi_s34_sd tt kk (segment[u:real^N,w]) =
                  moi_s34_vb tt kk u INTER moi_s34_vb tt kk w` SUBST1_TAC THENL
     [MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                     `segment[u:real^N,w]`] MOI_S4L_EDGE_VERTS) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `u':real^N` (X_CHOOSE_THEN `w':real^N` STRIP_ASSUME_TAC)) THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `segment[u:real^N,w] = segment[u',w']` THEN REWRITE_TAC[SEGMENT_EQ] THEN
      REWRITE_TAC[EXTENSION; IN_INSERT; NOT_IN_EMPTY] THEN
      DISCH_TAC THEN
      SUBGOAL_THEN `(u':real^N = u /\ w' = w) \/ (u' = w /\ w' = u)` MP_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[INTER_COMM];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                   `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`]
                  MOI_S4L_IMAGES) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
    DISCH_THEN(fun th -> CONV_TAC SYM_CONV THEN MATCH_MP_TAC th) THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4L_GRAPH_TUBE) THEN
    CONJ_TAC THEN FIRST_X_ASSUM(MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `pl_cell_with_boundary 3:(real^N->bool)->(real^N->bool)->bool`))
        (concl th))) THENL
     [DISCH_THEN(MP_TAC o SPEC `u:real^N`); DISCH_THEN(MP_TAC o SPEC `w:real^N`)] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_cell_with_boundary 2 (IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk (segment[u,w])))
                  (IMAGE f1 (moi_s34_sd tt kk (segment[u,w]) INTER moi_s34_bd tt kk))`
  ASSUME_TAC THENL
   [UNDISCH_TAC `moi_s34_frame tt kk (h:real^N->real^3) ep f1 car` THEN
    REWRITE_TAC[moi_s34_frame] THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                 `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                 `u:real^N`] MOI_S4L_AV_BASIC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                 `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                 `w:real^N`] MOI_S4L_AV_BASIC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk (segment[u,w])) SUBSET
    frontier(IMAGE f1 (moi_s34_vb tt kk u)) /\
    IMAGE f1 (moi_s34_sd tt kk (segment[u,w])) SUBSET frontier(IMAGE f1 (moi_s34_vb tt kk w))`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
    MATCH_MP_TAC(SET_RULE `!a b (u:(real^3->bool)->bool). a IN u ==> a SUBSET b UNION UNIONS u`) THEN
    REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `segment[u:real^N,w]` THEN
    ASM_REWRITE_TAC[ENDS_IN_SEGMENT];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
  MATCH_MP_TAC MOI_S4X_SD_OPEN THEN REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC);;

(* The tetra ball context at r. *)

let moi_s4x_rball = new_definition
 `moi_s4x_rball (tt:(real^N->bool)->bool) kk (h:real^N->real^3) ep (f1:real^N->real^3)
                car (dd:(real^N->bool)->real^3->bool) r (vx:num->real^N)
                (C:num->num->real^3->bool) (C':num->num->real^3->bool)
                (t:num->real^3->bool) (t':num->real^3->bool) <=>
   PL_SCHOENFLIES_3_STATEMENT /\ moi_s34_tube tt kk /\ moi_s34_frame tt kk h ep f1 car /\
   moi_s34_fdisk tt kk f1 car dd /\ r IN moi_s34_simp kk (&3) /\ moi_s4x_rverts kk r vx /\
   moi_s4x_tball (\i. IMAGE f1 (moi_s34_vb tt kk (vx i)))
     (\i j. IMAGE f1 (moi_s34_sd tt kk (segment[vx i,vx j]) INTER moi_s34_bd tt kk))
     (\l. dd (moi_s4x_rface vx l))
     (\l. dd (moi_s4x_rface vx l) INTER IMAGE f1 (moi_s34_bd tt kk)) C C' t t'`;;

let moi_s4x_rS = new_definition
 `moi_s4x_rS (dd:(real^N->bool)->real^3->bool) (vx:num->real^N) (t:num->real^3->bool) =
    moi_s4x_sph t (\l. dd (moi_s4x_rface vx l))`;;

let MOI_S4X_RB_EX = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car dd r.
     PL_SCHOENFLIES_3_STATEMENT /\ moi_s34_tube tt kk /\ moi_s34_frame tt kk h ep f1 car /\
     moi_s34_fdisk tt kk f1 car dd /\ r IN moi_s34_simp kk (&3)
     ==> ?vx C C' t t'. moi_s4x_rball tt kk h ep f1 car dd r vx C C' t t'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `r:real^N->bool`]
    MOI_S4X_RVERTS_EX) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `vx:num->real^N`) THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                 `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                 `dd:(real^N->bool)->real^3->bool`; `r:real^N->bool`; `vx:num->real^N`]
                MOI_S4X_RCONF) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o MATCH_MP MOI_S4X_TETRA_TB) THEN
  DISCH_THEN(X_CHOOSE_THEN `C:num->num->real^3->bool` (X_CHOOSE_THEN `C':num->num->real^3->bool`
    (X_CHOOSE_THEN `t:num->real^3->bool` (X_CHOOSE_TAC `t':num->real^3->bool`)))) THEN
  MAP_EVERY EXISTS_TAC [`vx:num->real^N`; `C:num->num->real^3->bool`;
                        `C':num->num->real^3->bool`; `t:num->real^3->bool`;
                        `t':num->real^3->bool`] THEN
  ASM_REWRITE_TAC[moi_s4x_rball]);;

(* Basic facts of the tetra ball at r. *)

let MOI_S4X_RB_BASIC = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car dd r vx C C' t t'.
     moi_s4x_rball tt kk h ep f1 car dd r vx C C' t t'
     ==> pl_sphere 2 (moi_s4x_rS dd vx t) /\
         pl_ball 3 (moi_s4x_rS dd vx t UNION inside(moi_s4x_rS dd vx t)) /\
         frontier(moi_s4x_rS dd vx t UNION inside(moi_s4x_rS dd vx t)) = moi_s4x_rS dd vx t /\
         interior(moi_s4x_rS dd vx t UNION inside(moi_s4x_rS dd vx t)) =
         inside(moi_s4x_rS dd vx t) /\
         moi_s4x_rS dd vx t =
         t 0 UNION t 1 UNION t 2 UNION t 3 UNION
         dd (moi_s4x_rface vx 0) UNION dd (moi_s4x_rface vx 1) UNION
         dd (moi_s4x_rface vx 2) UNION dd (moi_s4x_rface vx 3) /\
         (!i. i < 4 ==> IMAGE f1 (moi_s34_vb tt kk (vx i)) INTER
                        (moi_s4x_rS dd vx t UNION inside(moi_s4x_rS dd vx t)) = t i)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s4x_rball] THEN STRIP_TAC THEN
  SUBGOAL_THEN `pl_sphere 2 (moi_s4x_rS dd (vx:num->real^N) t)` ASSUME_TAC THENL
   [REWRITE_TAC[moi_s4x_rS] THEN
    UNDISCH_TAC `moi_s4x_tball (\i. IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk (vx i)))
     (\i j. IMAGE f1 (moi_s34_sd tt kk (segment[vx i,vx j]) INTER moi_s34_bd tt kk))
     (\l. (dd:(real^N->bool)->real^3->bool) (moi_s4x_rface vx l))
     (\l. dd (moi_s4x_rface vx l) INTER IMAGE f1 (moi_s34_bd tt kk)) C C' t t'` THEN
    REWRITE_TAC[moi_s4x_tball] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `moi_s4x_rS dd (vx:num->real^N) t` MOI_SCD_FILLED_FRONTIER) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT1 th; CONJUNCT1(CONJUNCT2 th)]) THEN
  CONJ_TAC THENL
   [UNDISCH_TAC `PL_SCHOENFLIES_3_STATEMENT` THEN REWRITE_TAC[PL_SCHOENFLIES_3_STATEMENT] THEN
    DISCH_THEN MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL [REWRITE_TAC[moi_s4x_rS; moi_s4x_sph]; ALL_TAC] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  MP_TAC(BETA_RULE(ISPECL
    [`\i. IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk ((vx:num->real^N) i))`;
     `\i j. IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk (segment[(vx:num->real^N) i,vx j]) INTER
                                     moi_s34_bd tt kk)`;
     `\l. (dd:(real^N->bool)->real^3->bool) (moi_s4x_rface (vx:num->real^N) l)`;
     `\l. (dd:(real^N->bool)->real^3->bool) (moi_s4x_rface (vx:num->real^N) l) INTER
          IMAGE (f1:real^N->real^3) (moi_s34_bd tt kk)`;
     `C:num->num->real^3->bool`; `C':num->num->real^3->bool`;
     `t:num->real^3->bool`; `t':num->real^3->bool`; `i:num`] MOI_S4X_TB_PATCH)) THEN
  ASM_REWRITE_TAC[moi_s4x_rS]);;

(* The pieces of the sphere lie in the carriers of proper faces of r. *)

let MOI_S4X_RB_SCAR = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car dd r vx C C' t t'.
     moi_s4x_rball tt kk h ep f1 car dd r vx C C' t t'
     ==> (!i. i < 4 ==> t i SUBSET car {vx i} /\ {vx i} IN kk /\ ~({vx i} = {}) /\
                        {vx i} SUBSET r /\ ~({vx i} = r)) /\
         (!l. l < 4 ==> dd (moi_s4x_rface vx l) SUBSET car (moi_s4x_rface vx l) /\
                        moi_s4x_rface vx l IN kk /\ ~(moi_s4x_rface vx l = {}) /\
                        moi_s4x_rface vx l SUBSET r /\ ~(moi_s4x_rface vx l = r))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_s4x_rball]) THEN
  SUBGOAL_THEN `!i. i < 4 ==> {(vx:num->real^N) i} IN kk` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_S4X_RV_PARTS]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4X_RV_BASIC) THEN
  SUBGOAL_THEN `aff_dim(r:real^N->bool) = &3` ASSUME_TAC THENL
   [UNDISCH_TAC `(r:real^N->bool) IN moi_s34_simp kk (&3)` THEN
    REWRITE_TAC[moi_s34_simp; IN_ELIM_THM] THEN SIMP_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THEN X_GEN_TAC `i:num` THEN DISCH_TAC THENL
   [MP_TAC(BETA_RULE(ISPECL
      [`\i. IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk ((vx:num->real^N) i))`;
       `\i j. IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk (segment[(vx:num->real^N) i,vx j]) INTER
                                       moi_s34_bd tt kk)`;
       `\l. (dd:(real^N->bool)->real^3->bool) (moi_s4x_rface (vx:num->real^N) l)`;
       `\l. (dd:(real^N->bool)->real^3->bool) (moi_s4x_rface (vx:num->real^N) l) INTER
            IMAGE (f1:real^N->real^3) (moi_s34_bd tt kk)`;
       `C:num->num->real^3->bool`; `C':num->num->real^3->bool`;
       `t:num->real^3->bool`; `t':num->real^3->bool`] MOI_S4X_TB_FACTS)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `i:num` o CONJUNCT1) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                   `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                   `(vx:num->real^N) i`] MOI_S4L_AV_BASIC) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[]; STRIP_TAC] THEN
    REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[SUBSET_TRANS];
      ASM_SIMP_TAC[];
      REWRITE_TAC[NOT_INSERT_EMPTY];
      ASM_SIMP_TAC[SING_SUBSET];
      DISCH_TAC THEN UNDISCH_TAC `aff_dim(r:real^N->bool) = &3` THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `{(vx:num->real^N) i} = r`)) THEN
      REWRITE_TAC[AFF_DIM_SING] THEN INT_ARITH_TAC];
    MP_TAC(ISPECL [`kk:(real^N->bool)->bool`; `r:real^N->bool`; `vx:num->real^N`; `i:num`]
      MOI_S4X_RV_FACE_IN) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `f1:real^N->real^3`;
                   `car:(real^N->bool)->real^3->bool`; `dd:(real^N->bool)->real^3->bool`;
                   `moi_s4x_rface (vx:num->real^N) i`] MOI_S4X_FD) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `moi_s4x_rface (vx:num->real^N) i IN moi_s34_simp kk (&2)` THEN
    REWRITE_TAC[moi_s34_simp; IN_ELIM_THM] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THEN DISCH_TAC THENL
     [UNDISCH_TAC `aff_dim(moi_s4x_rface (vx:num->real^N) i) = &2` THEN
      ASM_REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC;
      UNDISCH_TAC `aff_dim(moi_s4x_rface (vx:num->real^N) i) = &2` THEN
      ASM_REWRITE_TAC[] THEN INT_ARITH_TAC]]);;

(* The image of a vertex under h lies in its vertex ball. *)

let MOI_S4X_HW = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car w.
     moi_s34_tube tt kk /\ moi_s34_frame tt kk h ep f1 car /\ {w} IN kk
     ==> h w IN IMAGE f1 (moi_s34_vb tt kk w)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(h:real^N->real^3) w IN IMAGE (f1:real^N->real^3) (moi_s34_nb tt kk)` MP_TAC THENL
   [UNDISCH_TAC `moi_s34_frame tt kk (h:real^N->real^3) ep f1 car` THEN
    REWRITE_TAC[moi_s34_frame] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
    MP_TAC(ISPEC `IMAGE (f1:real^N->real^3) (moi_s34_nb (tt:(real^N->bool)->bool) kk)` INTERIOR_SUBSET) THEN
    MATCH_MP_TAC(SET_RULE `!a b c (x:real^3). x IN a ==> c SUBSET b ==> a SUBSET c ==> x IN b`) THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[IN_UNIONS] THEN
    EXISTS_TAC `{w:real^N}` THEN ASM_REWRITE_TAC[MOI_S4K_SKEL_VERTEX; IN_SING];
    ALL_TAC] THEN
  ASM_SIMP_TAC[MOI_S4X_FN] THEN REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real^3->bool` (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `v:real^N` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
  ASM_CASES_TAC `v:real^N = w` THENL
   [UNDISCH_TAC `(h:real^N->real^3) w IN s` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                 `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                 `v:real^N`] MOI_S4L_AV_BASIC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  UNDISCH_TAC `moi_s34_frame tt kk (h:real^N->real^3) ep f1 car` THEN
  REWRITE_TAC[moi_s34_frame] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`v:real^N`; `{w:real^N}`] o check (fun th ->
    is_forall(concl th) && length(fst(strip_forall(concl th))) = 2 &&
    can (find_term ((=) `car:(real^N->bool)->real^3->bool`)) (concl th) &&
    can (find_term ((=) `DISJOINT:(real^3->bool)->(real^3->bool)->bool`)) (concl th))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[IN_SING]; ALL_TAC] THEN
  MAP_EVERY UNDISCH_TAC
   [`(h:real^N->real^3) w IN s`; `s = IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v)`;
    `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v) SUBSET car {v}`] THEN
  REWRITE_TAC[IMAGE_CLAUSES] THEN SET_TAC[]);;

(* Clause: the tetra ball misses the vertex balls of the vertices off r. *)

let MOI_S4X_RB_FOREIGN = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car dd r vx C C' t t' w.
     moi_s4x_rball tt kk h ep f1 car dd r vx C C' t t' /\ {w} IN kk /\ ~(w IN r)
     ==> DISJOINT (moi_s4x_rS dd vx t UNION inside(moi_s4x_rS dd vx t))
                  (IMAGE f1 (moi_s34_vb tt kk w))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4X_RB_SCAR) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_s4x_rball]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4X_RV_BASIC) THEN
  SUBGOAL_THEN `!i. i < 4 ==> ~((vx:num->real^N) i = w)` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN UNDISCH_TAC `~((w:real^N) IN r)` THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                 `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`]
                MOI_S4L_IMAGES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                 `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                 `w:real^N`] MOI_S4L_AV_BASIC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  REWRITE_TAC[DISJOINT; moi_s4x_rS] THEN ONCE_REWRITE_TAC[INTER_COMM] THEN
  MATCH_MP_TAC(BETA_RULE(ISPECL
    [`\i. IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk ((vx:num->real^N) i))`;
     `\i j. IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk (segment[(vx:num->real^N) i,vx j]) INTER
                                     moi_s34_bd tt kk)`;
     `\l. (dd:(real^N->bool)->real^3->bool) (moi_s4x_rface (vx:num->real^N) l)`;
     `\l. (dd:(real^N->bool)->real^3->bool) (moi_s4x_rface (vx:num->real^N) l) INTER
          IMAGE (f1:real^N->real^3) (moi_s34_bd tt kk)`;
     `C:num->num->real^3->bool`; `C':num->num->real^3->bool`;
     `t:num->real^3->bool`; `t':num->real^3->bool`;
     `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk w)`;
     `\i. IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk (segment[(vx:num->real^N) i,w]) INTER
                                   moi_s34_bd tt kk)`;
     `(h:real^N->real^3) w`] MOI_S4X_TB_FOREIGN)) THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [(* the face disks of r miss V w *)
    X_GEN_TAC `l:num` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`kk:(real^N->bool)->bool`; `r:real^N->bool`; `vx:num->real^N`; `l:num`]
      MOI_S4X_RV_FACE_IN) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `f1:real^N->real^3`;
                   `car:(real^N->bool)->real^3->bool`; `dd:(real^N->bool)->real^3->bool`;
                   `moi_s4x_rface (vx:num->real^N) l`] MOI_S4X_FD) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `w:real^N` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `DISJOINT:(real^3->bool)->(real^3->bool)->bool`)) (concl th))) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `~((w:real^N) IN r)` THEN
      UNDISCH_TAC `moi_s4x_rface (vx:num->real^N) l SUBSET r` THEN SET_TAC[];
      SET_TAC[]];
    (* triple intersections *)
    MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`w:real^N`; `(vx:num->real^N) i`; `(vx:num->real^N) j`] o
      check (fun th -> is_forall(concl th) && length(fst(strip_forall(concl th))) = 3)) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[]; SET_TAC[]];
    (* the traces on the vertex balls of r *)
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    ASM_CASES_TAC `segment[(vx:num->real^N) i,w] IN kk` THENL
     [DISJ2_TAC THEN
      MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                     `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                     `(vx:num->real^N) i`; `w:real^N`] MOI_S4X_GEN_EDGE) THEN
      ANTS_TAC THENL [ASM_SIMP_TAC[]; STRIP_TAC] THEN
      SUBGOAL_THEN `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk w) INTER
                    IMAGE f1 (moi_s34_vb tt kk ((vx:num->real^N) i)) =
                    IMAGE f1 (moi_s34_sd tt kk (segment[vx i,w]))` SUBST1_TAC THENL
       [ONCE_REWRITE_TAC[INTER_COMM] THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
      UNDISCH_TAC `IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk (segment[(vx:num->real^N) i,w])) SUBSET
                   frontier(IMAGE f1 (moi_s34_vb tt kk w))` THEN
      ASM_REWRITE_TAC[];
      DISJ1_TAC THEN ONCE_REWRITE_TAC[INTER_COMM] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[]];
    (* h w is in V w *)
    MATCH_MP_TAC MOI_S4X_HW THEN
    MAP_EVERY EXISTS_TAC [`ep:real^N->real`; `car:(real^N->bool)->real^3->bool`] THEN
    ASM_REWRITE_TAC[];
    (* h w lies outside the sphere *)
    ABBREV_TAC `U = UNIONS {(car:(real^N->bool)->real^3->bool) q | q |
                            q IN kk /\ ~(q = {}) /\ q SUBSET r /\ ~(q = r)}` THEN
    SUBGOAL_THEN `(!i. i < 4 ==> (t:num->real^3->bool) i SUBSET U) /\
                  (!l. l < 4 ==> (dd:(real^N->bool)->real^3->bool) (moi_s4x_rface vx l) SUBSET U)`
    STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "U" THEN CONJ_TAC THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      MATCH_MP_TAC(SET_RULE `!a b (u:(real^3->bool)->bool). a SUBSET b /\ b IN u ==> a SUBSET UNIONS u`) THENL
       [EXISTS_TAC `(car:(real^N->bool)->real^3->bool) {(vx:num->real^N) i}`;
        EXISTS_TAC `(car:(real^N->bool)->real^3->bool) (moi_s4x_rface (vx:num->real^N) i)`] THEN
      ASM_SIMP_TAC[] THEN REWRITE_TAC[IN_ELIM_THM] THENL
       [EXISTS_TAC `{(vx:num->real^N) i}`; EXISTS_TAC `moi_s4x_rface (vx:num->real^N) i`] THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `moi_s34_frame tt kk (h:real^N->real^3) ep f1 car` THEN
    REWRITE_TAC[moi_s34_frame] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`r:real^N->bool`; `w:real^N`] o check (fun th ->
      is_forall(concl th) && length(fst(strip_forall(concl th))) = 2 &&
      can (find_term ((=) `outside:(real^3->bool)->real^3->bool`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(SET_RULE `!a b x:real^3. a SUBSET b ==> x IN a ==> x IN b`) THEN
    MATCH_MP_TAC OUTSIDE_MONO THEN
    REWRITE_TAC[moi_s4x_sph; UNION_SUBSET] THEN BETA_TAC THEN ASM_SIMP_TAC[ARITH]]);;

(* The hexagons of the tetra ball lie on Bd N''. *)

let MOI_S4X_RB_TF = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car dd r vx C C' t t' i.
     moi_s4x_rball tt kk h ep f1 car dd r vx C C' t t' /\ i < 4
     ==> t i SUBSET IMAGE f1 (moi_s34_bd tt kk)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4X_RB_BASIC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_s4x_rball]) THEN
  SUBGOAL_THEN
   `(!m. m < 4 ==> {(vx:num->real^N) m} IN kk) /\
    (!v. v IN r /\ {v} IN kk ==> ?m. m < 4 /\ v = (vx:num->real^N) m)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN FIRST_ASSUM(MP_TAC o MATCH_MP MOI_S4X_RV_PARTS) THEN SIMP_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4X_RV_BASIC) THEN
  MP_TAC(BETA_RULE(ISPECL
    [`\i. IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk ((vx:num->real^N) i))`;
     `\i j. IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk (segment[(vx:num->real^N) i,vx j]) INTER
                                     moi_s34_bd tt kk)`;
     `\l. (dd:(real^N->bool)->real^3->bool) (moi_s4x_rface (vx:num->real^N) l)`;
     `\l. (dd:(real^N->bool)->real^3->bool) (moi_s4x_rface (vx:num->real^N) l) INTER
          IMAGE (f1:real^N->real^3) (moi_s34_bd tt kk)`;
     `C:num->num->real^3->bool`; `C':num->num->real^3->bool`;
     `t:num->real^3->bool`; `t':num->real^3->bool`] MOI_S4X_TB_FACTS)) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `i:num` o CONJUNCT1) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                 `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                 `(vx:num->real^N) i`] MOI_S4L_AV_BASIC) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; STRIP_TAC] THEN
  (* the rim arcs of t i on the splitting disks of r *)
  SUBGOAL_THEN
   `!j. j < 4 /\ ~(j = i)
        ==> (t:num->real^3->bool) i INTER IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk (vx j))
            SUBSET IMAGE f1 (moi_s34_sd tt kk (segment[vx i,vx j]) INTER moi_s34_bd tt kk)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    UNDISCH_TAC `moi_s4x_tball (\i. IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk (vx i)))
     (\i j. IMAGE f1 (moi_s34_sd tt kk (segment[vx i,vx j]) INTER moi_s34_bd tt kk))
     (\l. (dd:(real^N->bool)->real^3->bool) (moi_s4x_rface vx l))
     (\l. dd (moi_s4x_rface vx l) INTER IMAGE f1 (moi_s34_bd tt kk)) C C' t t'` THEN
    REWRITE_TAC[moi_s4x_tball] THEN STRIP_TAC THEN
    MP_TAC(BETA_RULE(ISPECL
      [`\i. IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk ((vx:num->real^N) i))`;
       `\i j. IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk (segment[(vx:num->real^N) i,vx j]) INTER
                                       moi_s34_bd tt kk)`;
       `\l. (dd:(real^N->bool)->real^3->bool) (moi_s4x_rface (vx:num->real^N) l)`;
       `\l. (dd:(real^N->bool)->real^3->bool) (moi_s4x_rface (vx:num->real^N) l) INTER
            IMAGE (f1:real^N->real^3) (moi_s34_bd tt kk)`;
       `C:num->num->real^3->bool`; `C':num->num->real^3->bool`;
       `i:num`; `j:num`; `(t:num->real^3->bool) i`; `(t':num->real^3->bool) i`] MOI_S4X_HEX_RIM)) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(x:real^3) IN frontier(IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk (vx(i:num))))`
  MP_TAC THENL
   [UNDISCH_TAC `(t:num->real^3->bool) i SUBSET
                 frontier(IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk (vx(i:num))))` THEN
    UNDISCH_TAC `(x:real^3) IN (t:num->real^3->bool) i` THEN SET_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM((fun th -> REWRITE_TAC[th]) o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `frontier(IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk (vx(i:num))))`)) THEN
  REWRITE_TAC[IN_UNION; UNIONS_GSPEC; IN_ELIM_THM] THEN
  DISCH_THEN(DISJ_CASES_THEN MP_TAC) THENL
   [MATCH_MP_TAC(SET_RULE `!a b x:real^3. a SUBSET b ==> x IN a ==> x IN b`) THEN
    MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[INTER_SUBSET];
    DISCH_THEN(X_CHOOSE_THEN `g:real^N->bool` STRIP_ASSUME_TAC)] THEN
  (* the other end y of the edge g at vx i *)
  SUBGOAL_THEN `?y. {y} IN kk /\ ~(y = (vx:num->real^N) i) /\ g = segment[vx i,y]`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `g:real^N->bool`]
      MOI_S4L_EDGE_VERTS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real^N` (X_CHOOSE_THEN `w:real^N` MP_TAC)) THEN
    DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
    SUBGOAL_THEN `(vx:num->real^N) i IN {v | v IN g /\ {v} IN kk}` MP_TAC THENL
     [REWRITE_TAC[IN_ELIM_THM] THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
    FIRST_ASSUM((fun th -> REWRITE_TAC[th]) o check (fun th -> is_eq(concl th) &&
      rhs(concl th) = `{u:real^N,w}`)) THEN
    REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN STRIP_TAC THENL
     [EXISTS_TAC `w:real^N` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `~(u:real^N = w)` THEN MESON_TAC[];
      EXISTS_TAC `u:real^N` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `~(u:real^N = w)` THEN MESON_TAC[SEGMENT_SYM]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^3) IN IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk y)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                   `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                   `(vx:num->real^N) i`; `y:real^N`] MOI_S4X_GEN_EDGE) THEN
    ANTS_TAC THENL
     [SUBGOAL_THEN `~((vx:num->real^N) i = y) /\ segment[(vx:num->real^N) i,y] IN kk`
      STRIP_ASSUME_TAC THENL
       [CONJ_TAC THENL
         [UNDISCH_TAC `~(y:real^N = vx(i:num))` THEN MESON_TAC[];
          UNDISCH_TAC `(g:real^N->bool) IN moi_s34_simp kk (&1)` THEN
          UNDISCH_TAC `g = segment[(vx:num->real^N) i,y]` THEN DISCH_THEN SUBST1_TAC THEN
          REWRITE_TAC[moi_s34_simp; IN_ELIM_THM] THEN SIMP_TAC[]];
        ASM_SIMP_TAC[]];
      STRIP_TAC] THEN
    UNDISCH_TAC `(x:real^3) IN IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g)` THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM((fun th -> REWRITE_TAC[SYM th]) o check (fun th -> is_eq(concl th) &&
      can (find_term ((=) `y:real^N`)) (lhs(concl th)))) THEN
    SET_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `(y:real^N) IN r` THENL
   [SUBGOAL_THEN `?j. j < 4 /\ y = (vx:num->real^N) j` STRIP_ASSUME_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `r:real^N->bool`)) (concl th) &&
        is_exists(rand(snd(dest_forall(concl th)))))) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `~(j:num = i)` ASSUME_TAC THENL
     [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC `~(y:real^N = vx(i:num))` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `moi_s34_bd (tt:(real^N->bool)->bool) kk`)) (concl th) &&
      can (find_term ((=) `(t:num->real^3->bool) i`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(SET_RULE `!a b c (x:real^3). x IN a /\ b SUBSET c ==> a SUBSET b ==> x IN c`) THEN
    CONJ_TAC THENL
     [ASM_REWRITE_TAC[IN_INTER] THEN
      UNDISCH_TAC `(x:real^3) IN IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk y)` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[INTER_SUBSET]];
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                   `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                   `dd:(real^N->bool)->real^3->bool`; `r:real^N->bool`; `vx:num->real^N`;
                   `C:num->num->real^3->bool`; `C':num->num->real^3->bool`;
                   `t:num->real^3->bool`; `t':num->real^3->bool`; `y:real^N`] MOI_S4X_RB_FOREIGN) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[DISJOINT] THEN DISCH_TAC THEN MATCH_MP_TAC(TAUT `F ==> q`) THEN
    SUBGOAL_THEN `(x:real^3) IN moi_s4x_rS dd (vx:num->real^N) t UNION inside(moi_s4x_rS dd vx t)`
    MP_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `inside:(real^3->bool)->real^3->bool`)) (concl th))) THEN
      ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      UNDISCH_TAC `(x:real^3) IN (t:num->real^3->bool) i` THEN SET_TAC[];
      UNDISCH_TAC `(moi_s4x_rS dd (vx:num->real^N) t UNION inside(moi_s4x_rS dd vx t)) INTER
                   IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk y) = {}` THEN
      UNDISCH_TAC `(x:real^3) IN IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk y)` THEN
      SET_TAC[]]]);;

(* Unions over the indices below 4. *)

let MOI_S4X_IN_UNION4 = prove
 (`!(f:num->real^3->bool) x.
     x IN f 0 UNION f 1 UNION f 2 UNION f 3 <=> ?i. i < 4 /\ x IN f i`,
  REWRITE_TAC[IN_UNION; MOI_S4X_LT4] THEN
  REWRITE_TAC[RIGHT_OR_DISTRIB; EXISTS_OR_THM; UNWIND_THM2] THEN CONV_TAC TAUT);;

(* The trace of the tetra ball on N'' and on Bd N'' is the union of the    *)
(* hexagons.                                                                 *)

let MOI_S4X_RB_NB = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car dd r vx C C' t t'.
     moi_s4x_rball tt kk h ep f1 car dd r vx C C' t t'
     ==> (moi_s4x_rS dd vx t UNION inside(moi_s4x_rS dd vx t)) INTER
         IMAGE f1 (moi_s34_nb tt kk) = t 0 UNION t 1 UNION t 2 UNION t 3 /\
         (moi_s4x_rS dd vx t UNION inside(moi_s4x_rS dd vx t)) INTER
         IMAGE f1 (moi_s34_bd tt kk) = t 0 UNION t 1 UNION t 2 UNION t 3`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4X_RB_BASIC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_s4x_rball]) THEN
  SUBGOAL_THEN
   `(!m. m < 4 ==> {(vx:num->real^N) m} IN kk) /\
    (!v. v IN r /\ {v} IN kk ==> ?m. m < 4 /\ v = (vx:num->real^N) m)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN FIRST_ASSUM(MP_TAC o MATCH_MP MOI_S4X_RV_PARTS) THEN SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `b = moi_s4x_rS dd (vx:num->real^N) t UNION inside(moi_s4x_rS dd vx t)` THEN
  SUBGOAL_THEN `!m. m < 4 ==> (t:num->real^3->bool) m SUBSET b /\
                              t m SUBSET IMAGE (f1:real^N->real^3) (moi_s34_bd tt kk)`
  ASSUME_TAC THENL
   [X_GEN_TAC `m:num` THEN DISCH_TAC THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `m:num` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `b:real^3->bool`)) (concl th) &&
        can (find_term ((=) `(t:num->real^3->bool)`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      MATCH_MP_TAC MOI_S4X_RB_TF THEN
      MAP_EVERY EXISTS_TAC [`h:real^N->real^3`; `ep:real^N->real`; `car:(real^N->bool)->real^3->bool`;
                            `dd:(real^N->bool)->real^3->bool`; `r:real^N->bool`; `vx:num->real^N`;
                            `C:num->num->real^3->bool`; `C':num->num->real^3->bool`;
                            `t':num->real^3->bool`] THEN
      ASM_REWRITE_TAC[] THEN FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `b INTER IMAGE (f1:real^N->real^3) (moi_s34_nb tt kk) =
                t 0 UNION t 1 UNION t 2 UNION (t:num->real^3->bool) 3`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[MOI_S4X_FN] THEN
    GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_INTER; IN_UNIONS; IN_ELIM_THM;
      MOI_S4X_IN_UNION4] THEN
    X_GEN_TAC `x:real^3` THEN EQ_TAC THENL
     [DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `s:real^3->bool`
        (CONJUNCTS_THEN2 (X_CHOOSE_THEN `v:real^N` STRIP_ASSUME_TAC) ASSUME_TAC))) THEN
      ASM_CASES_TAC `(v:real^N) IN r` THENL
       [SUBGOAL_THEN `?m. m < 4 /\ v = (vx:num->real^N) m` STRIP_ASSUME_TAC THENL
         [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
            can (find_term ((=) `r:real^N->bool`)) (concl th) &&
            is_exists(rand(snd(dest_forall(concl th)))))) THEN
          ASM_REWRITE_TAC[];
          ALL_TAC] THEN
        EXISTS_TAC `m:num` THEN ASM_REWRITE_TAC[] THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `m:num` o check (fun th -> is_forall(concl th) &&
          can (find_term ((=) `b:real^3->bool`)) (concl th) &&
          is_eq(rand(snd(dest_forall(concl th)))))) THEN
        ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
        MAP_EVERY UNDISCH_TAC
         [`(x:real^3) IN s`; `(x:real^3) IN b`; `s = IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v)`;
          `v = (vx:num->real^N) m`] THEN
        DISCH_THEN SUBST1_TAC THEN DISCH_THEN SUBST1_TAC THEN SET_TAC[];
        MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                       `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                       `dd:(real^N->bool)->real^3->bool`; `r:real^N->bool`; `vx:num->real^N`;
                       `C:num->num->real^3->bool`; `C':num->num->real^3->bool`;
                       `t:num->real^3->bool`; `t':num->real^3->bool`; `v:real^N`] MOI_S4X_RB_FOREIGN) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        ASM_REWRITE_TAC[DISJOINT] THEN
        MAP_EVERY UNDISCH_TAC
         [`(x:real^3) IN s`; `(x:real^3) IN b`; `s = IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v)`] THEN
        DISCH_THEN SUBST1_TAC THEN SET_TAC[]];
      DISCH_THEN(X_CHOOSE_THEN `m:num` STRIP_ASSUME_TAC) THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `m:num` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `b:real^3->bool`)) (concl th) &&
        is_eq(rand(snd(dest_forall(concl th)))))) THEN
      ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; DISCH_TAC] THEN
      CONJ_TAC THENL
       [UNDISCH_TAC `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk (vx(m:num))) INTER b = t m` THEN
        UNDISCH_TAC `(x:real^3) IN (t:num->real^3->bool) m` THEN SET_TAC[];
        EXISTS_TAC `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk (vx(m:num)))` THEN
        CONJ_TAC THENL
         [EXISTS_TAC `(vx:num->real^N) m` THEN ASM_SIMP_TAC[];
          UNDISCH_TAC `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk (vx(m:num))) INTER b = t m` THEN
          UNDISCH_TAC `(x:real^3) IN (t:num->real^3->bool) m` THEN SET_TAC[]]]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `moi_s34_bd tt kk SUBSET moi_s34_nb (tt:(real^N->bool)->bool) kk` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP MOI_S4L_GRAPH_TUBE) THEN SIMP_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [FIRST_X_ASSUM((fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) o check (fun th ->
      is_eq(concl th) && lhs(concl th) = `b INTER IMAGE (f1:real^N->real^3) (moi_s34_nb tt kk)`)) THEN
    MATCH_MP_TAC(SET_RULE `!a b c:real^3->bool. b SUBSET c ==> a INTER b SUBSET a INTER c`) THEN
    MATCH_MP_TAC IMAGE_SUBSET THEN FIRST_ASSUM ACCEPT_TAC;
    REWRITE_TAC[UNION_SUBSET] THEN
    REPEAT CONJ_TAC THEN REWRITE_TAC[SUBSET_INTER] THEN ASM_SIMP_TAC[ARITH]]);;

(* The face disks of the faces of kk in r. *)

let MOI_S4X_RB_DD = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car dd r vx C C' t t'.
     moi_s4x_rball tt kk h ep f1 car dd r vx C C' t t'
     ==> UNIONS {dd s | s | s IN moi_s34_simp kk (&2) /\ s SUBSET r} =
         dd (moi_s4x_rface vx 0) UNION dd (moi_s4x_rface vx 1) UNION
         dd (moi_s4x_rface vx 2) UNION dd (moi_s4x_rface vx 3)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_s4x_rball]) THEN
  MP_TAC(BETA_RULE(ISPEC `\l. (dd:(real^N->bool)->real^3->bool) (moi_s4x_rface (vx:num->real^N) l)`
    MOI_S4X_IN_UNION4)) THEN
  DISCH_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN ASM_REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM] THEN
  X_GEN_TAC `x:real^3` THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `r:real^N->bool`;
                   `vx:num->real^N`; `s:real^N->bool`] MOI_S4X_RV_FACE_CLASS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `l:num` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `l:num` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(x:real^3) IN (dd:(real^N->bool)->real^3->bool) s` THEN ASM_REWRITE_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `l:num` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `moi_s4x_rface (vx:num->real^N) l` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_S4X_RV_FACE_IN THEN ASM_REWRITE_TAC[]]);;

(* Clauses: the frontier of the tetra ball and its trace on N''. *)

let MOI_S4X_RB_FRONT = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car dd r vx C C' t t'.
     moi_s4x_rball tt kk h ep f1 car dd r vx C C' t t'
     ==> frontier(moi_s4x_rS dd vx t UNION inside(moi_s4x_rS dd vx t)) =
         UNIONS {dd s | s | s IN moi_s34_simp kk (&2) /\ s SUBSET r} UNION
         ((moi_s4x_rS dd vx t UNION inside(moi_s4x_rS dd vx t)) INTER IMAGE f1 (moi_s34_bd tt kk)) /\
         (moi_s4x_rS dd vx t UNION inside(moi_s4x_rS dd vx t)) INTER IMAGE f1 (moi_s34_nb tt kk) =
         (moi_s4x_rS dd vx t UNION inside(moi_s4x_rS dd vx t)) INTER IMAGE f1 (moi_s34_bd tt kk)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4X_RB_BASIC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4X_RB_NB) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MOI_S4X_RB_DD) THEN
  ASM_REWRITE_TAC[] THEN SET_TAC[]);;

(* Clause: the tetra ball lies in the convex hull of the carrier of r. *)

let MOI_S4X_RB_HULL = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car dd r vx C C' t t'.
     moi_s4x_rball tt kk h ep f1 car dd r vx C C' t t'
     ==> moi_s4x_rS dd vx t UNION inside(moi_s4x_rS dd vx t) SUBSET convex hull (car r)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4X_RB_SCAR) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4X_RB_BASIC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_s4x_rball]) THEN
  SUBGOAL_THEN `(r:real^N->bool) IN kk` ASSUME_TAC THENL
   [UNDISCH_TAC `(r:real^N->bool) IN moi_s34_simp kk (&3)` THEN
    REWRITE_TAC[moi_s34_simp; IN_ELIM_THM] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!q. q IN kk /\ ~(q = {}) /\ q SUBSET r ==> (car:(real^N->bool)->real^3->bool) q SUBSET car r`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    UNDISCH_TAC `moi_s34_frame tt kk (h:real^N->real^3) ep f1 car` THEN
    REWRITE_TAC[moi_s34_frame] THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_s4x_rS dd (vx:num->real^N) t SUBSET (car:(real^N->bool)->real^3->bool) r`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[UNION_SUBSET] THEN REPEAT CONJ_TAC THEN
    MATCH_MP_TAC SUBSET_TRANS THENL
     [EXISTS_TAC `(car:(real^N->bool)->real^3->bool) {(vx:num->real^N) 0}`;
      EXISTS_TAC `(car:(real^N->bool)->real^3->bool) {(vx:num->real^N) 1}`;
      EXISTS_TAC `(car:(real^N->bool)->real^3->bool) {(vx:num->real^N) 2}`;
      EXISTS_TAC `(car:(real^N->bool)->real^3->bool) {(vx:num->real^N) 3}`;
      EXISTS_TAC `(car:(real^N->bool)->real^3->bool) (moi_s4x_rface (vx:num->real^N) 0)`;
      EXISTS_TAC `(car:(real^N->bool)->real^3->bool) (moi_s4x_rface (vx:num->real^N) 1)`;
      EXISTS_TAC `(car:(real^N->bool)->real^3->bool) (moi_s4x_rface (vx:num->real^N) 2)`;
      EXISTS_TAC `(car:(real^N->bool)->real^3->bool) (moi_s4x_rface (vx:num->real^N) 3)`] THEN
    ASM_SIMP_TAC[ARITH];
    ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_TRANS THEN
  EXISTS_TAC `convex hull (moi_s4x_rS dd (vx:num->real^N) t)` THEN CONJ_TAC THENL
   [REWRITE_TAC[UNION_SUBSET; HULL_SUBSET; INSIDE_SUBSET_CONVEX_HULL];
    MATCH_MP_TAC HULL_MONO THEN FIRST_ASSUM ACCEPT_TAC]);;

(* Comparing two unions of families (empty members may be unmatched). *)

let MOI_S4X_UNIONS_EQ = prove
 (`!(f:A->real^3->bool) (g:B->real^3->bool) P Q.
     (!x. P x ==> f x = {} \/ ?y. Q y /\ f x = g y) /\
     (!y. Q y ==> g y = {} \/ ?x. P x /\ g y = f x)
     ==> UNIONS {f x | x | P x} = UNIONS {g y | y | Q y}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM] THEN
  X_GEN_TAC `z:real^3` THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `x:A` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:A` o check (fun th -> is_forall(concl th) &&
      type_of(fst(dest_forall(concl th))) = `:A`)) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
     [UNDISCH_TAC `(z:real^3) IN (f:A->real^3->bool) x` THEN ASM_REWRITE_TAC[NOT_IN_EMPTY];
      EXISTS_TAC `y:B` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(z:real^3) IN (f:A->real^3->bool) x` THEN ASM_REWRITE_TAC[]];
    DISCH_THEN(X_CHOOSE_THEN `y:B` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:B` o check (fun th -> is_forall(concl th) &&
      type_of(fst(dest_forall(concl th))) = `:B`)) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
     [UNDISCH_TAC `(z:real^3) IN (g:B->real^3->bool) y` THEN ASM_REWRITE_TAC[NOT_IN_EMPTY];
      EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(z:real^3) IN (g:B->real^3->bool) y` THEN ASM_REWRITE_TAC[]]]);;

(* Clause: the patches b INTER C_v'' at the vertices of r. *)

let MOI_S4X_RB_PATCH = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car dd r vx C C' t t' v.
     moi_s4x_rball tt kk h ep f1 car dd r vx C C' t t' /\ {v} IN kk /\ v IN r
     ==> pl_cell_with_boundary 2
           ((moi_s4x_rS dd vx t UNION inside(moi_s4x_rS dd vx t)) INTER
            IMAGE f1 (moi_s34_vb tt kk v))
           (UNIONS {dd s INTER IMAGE f1 (moi_s34_vb tt kk v) | s |
                    s IN moi_s34_simp kk (&2) /\ v IN s /\ s SUBSET r} UNION
            UNIONS {(moi_s4x_rS dd vx t UNION inside(moi_s4x_rS dd vx t)) INTER
                    IMAGE f1 (moi_s34_sd tt kk g) | g |
                    g IN moi_s34_simp kk (&1) /\ v IN g /\ g SUBSET r})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4X_RB_BASIC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_s4x_rball]) THEN
  SUBGOAL_THEN `?i. i < 4 /\ v = (vx:num->real^N) i` STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP MOI_S4X_RV_PARTS) THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  ABBREV_TAC `b = moi_s4x_rS dd (vx:num->real^N) t UNION inside(moi_s4x_rS dd vx t)` THEN
  SUBGOAL_THEN `b INTER IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk (vx(i:num))) = t i`
  SUBST1_TAC THENL
   [ONCE_REWRITE_TAC[INTER_COMM] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `b:real^3->bool`)) (concl th) &&
      is_eq(rand(snd(dest_forall(concl th)))))) THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  (* the hexagon t i and its boundary *)
  SUBGOAL_THEN
   `moi_s4x_hex (\i. IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk ((vx:num->real^N) i)))
      (\l. (dd:(real^N->bool)->real^3->bool) (moi_s4x_rface vx l)) C C' i (t i) (t' i)`
  MP_TAC THENL
   [UNDISCH_TAC `moi_s4x_tball (\i. IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk (vx i)))
     (\i j. IMAGE f1 (moi_s34_sd tt kk (segment[vx i,vx j]) INTER moi_s34_bd tt kk))
     (\l. (dd:(real^N->bool)->real^3->bool) (moi_s4x_rface vx l))
     (\l. dd (moi_s4x_rface vx l) INTER IMAGE f1 (moi_s34_bd tt kk)) C C' t t'` THEN
    REWRITE_TAC[moi_s4x_tball] THEN STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[moi_s4x_hex] THEN BETA_TAC THEN
  DISCH_THEN(MP_TAC o CONJUNCT1) THEN
  MATCH_MP_TAC(TAUT `(a <=> b) ==> a ==> b`) THEN AP_TERM_TAC THEN
  SUBGOAL_THEN `!m. m < 4 ==> IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk ((vx:num->real^N) m)) INTER b =
                              (t:num->real^3->bool) m`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(ACCEPT_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `b:real^3->bool`)) (concl th) &&
      is_eq(rand(snd(dest_forall(concl th))))));
    ALL_TAC] THEN
  BINOP_TAC THEN MATCH_MP_TAC MOI_S4X_UNIONS_EQ THEN CONJ_TAC THENL
   [(* face arcs *)
    X_GEN_TAC `m:num` THEN DISCH_TAC THEN ASM_CASES_TAC `m:num = i` THENL
     [DISJ1_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
      MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                     `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                     `dd:(real^N->bool)->real^3->bool`; `r:real^N->bool`; `vx:num->real^N`;
                     `i:num`] MOI_S4X_RC_FACE) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
      DISJ2_TAC THEN EXISTS_TAC `moi_s4x_rface (vx:num->real^N) m` THEN REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`kk:(real^N->bool)->bool`; `r:real^N->bool`; `vx:num->real^N`; `m:num`]
        MOI_S4X_RV_FACE_IN) THEN
      MP_TAC(ISPECL [`kk:(real^N->bool)->bool`; `r:real^N->bool`; `vx:num->real^N`;
                     `i:num`; `m:num`] MOI_S4X_RV_FACE) THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[]];
    X_GEN_TAC `s:real^N->bool` THEN STRIP_TAC THEN DISJ2_TAC THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `r:real^N->bool`;
                   `vx:num->real^N`; `s:real^N->bool`] MOI_S4X_RV_FACE_CLASS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `l:num` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `l:num` THEN ASM_REWRITE_TAC[];
    (* rim arcs *)
    X_GEN_TAC `m:num` THEN STRIP_TAC THEN DISJ2_TAC THEN
    EXISTS_TAC `segment[(vx:num->real^N) i,vx m]` THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `r:real^N->bool`;
                   `vx:num->real^N`; `i:num`; `m:num`] MOI_S4X_RV_EDGE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[];
      DISCH_THEN(fun th -> ASSUME_TAC(CONJUNCT1 th) THEN ASSUME_TAC(CONJUNCT1(CONJUNCT2 th)))] THEN
    ASM_REWRITE_TAC[ENDS_IN_SEGMENT] THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                   `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                   `r:real^N->bool`; `vx:num->real^N`; `i:num`; `m:num`] MOI_S4X_RC_EDGE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT1)] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `b:real^3->bool`)) (concl th) &&
      is_eq(rand(snd(dest_forall(concl th)))))) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    MATCH_ACCEPT_TAC(SET_RULE `!a b c d:real^3->bool. a INTER b = d ==> d INTER c = b INTER (a INTER c)`);
    X_GEN_TAC `g:real^N->bool` THEN STRIP_TAC THEN DISJ2_TAC THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `r:real^N->bool`;
                   `vx:num->real^N`; `g:real^N->bool`] MOI_S4X_RV_EDGE_CLASS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `a:num` (X_CHOOSE_THEN `c:num` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `?m. m < 4 /\ ~(m = i) /\ g = segment[(vx:num->real^N) i,vx m]`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(vx:num->real^N) i IN g` THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`kk:(real^N->bool)->bool`; `r:real^N->bool`; `vx:num->real^N`;
                     `a:num`; `c:num`; `i:num`] MOI_S4X_RV_SEG) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
      STRIP_TAC THENL
       [EXISTS_TAC `c:num` THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
        EXISTS_TAC `a:num` THEN ASM_REWRITE_TAC[SEGMENT_SYM] THEN ASM_ARITH_TAC];
      ALL_TAC] THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
      concl th = `g = segment[(vx:num->real^N) i,vx m]`)) THEN
    EXISTS_TAC `m:num` THEN CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                   `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                   `r:real^N->bool`; `vx:num->real^N`; `i:num`; `m:num`] MOI_S4X_RC_EDGE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT1)] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `b:real^3->bool`)) (concl th) &&
      is_eq(rand(snd(dest_forall(concl th)))))) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    MATCH_ACCEPT_TAC(SET_RULE `!a b c d:real^3->bool. a INTER b = d ==> b INTER (a INTER c) = d INTER c`)]);;

(* Clause: the rim arcs b INTER D_g'' on the edges of r. *)

let MOI_S4X_RB_EDGE = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car dd r vx C C' t t' g.
     moi_s4x_rball tt kk h ep f1 car dd r vx C C' t t' /\
     g IN moi_s34_simp kk (&1) /\ g SUBSET r
     ==> pl_cell_with_boundary 1
           ((moi_s4x_rS dd vx t UNION inside(moi_s4x_rS dd vx t)) INTER
            IMAGE f1 (moi_s34_sd tt kk g))
           (UNIONS {dd s INTER IMAGE f1 (moi_s34_sd tt kk g) | s |
                    s IN moi_s34_simp kk (&2) /\ g SUBSET s /\ s SUBSET r})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4X_RB_BASIC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_s4x_rball]) THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `r:real^N->bool`;
                 `vx:num->real^N`; `g:real^N->bool`] MOI_S4X_RV_EDGE_CLASS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `i:num` (X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  ABBREV_TAC `b = moi_s4x_rS dd (vx:num->real^N) t UNION inside(moi_s4x_rS dd vx t)` THEN
  MP_TAC(SPECL [`i:num`; `j:num`] MOI_S4X_OTHER2) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `l:num` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                 `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                 `r:real^N->bool`; `vx:num->real^N`; `i:num`; `j:num`] MOI_S4X_RC_EDGE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(ASSUME_TAC o SYM o CONJUNCT1)] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `b INTER (IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk ((vx:num->real^N) i)) INTER
             IMAGE f1 (moi_s34_vb tt kk (vx j))) =
    (t:num->real^3->bool) i INTER IMAGE f1 (moi_s34_vb tt kk (vx j))`
  SUBST1_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `b:real^3->bool`)) (concl th) &&
      is_eq(rand(snd(dest_forall(concl th)))))) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    MATCH_ACCEPT_TAC(SET_RULE `!a b c d:real^3->bool. a INTER b = d ==> b INTER (a INTER c) = d INTER c`);
    ALL_TAC] THEN
  (* the boundary: the two face points of the faces of r containing the edge *)
  SUBGOAL_THEN
   `UNIONS {(dd:(real^N->bool)->real^3->bool) s INTER
            (IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk ((vx:num->real^N) i)) INTER
             IMAGE f1 (moi_s34_vb tt kk (vx j))) | s |
            s IN moi_s34_simp kk (&2) /\ segment[vx i,vx j] SUBSET s /\ s SUBSET r} =
    (dd (moi_s4x_rface vx k) INTER IMAGE f1 (moi_s34_vb tt kk (vx i)) INTER
     IMAGE f1 (moi_s34_vb tt kk (vx j))) UNION
    (dd (moi_s4x_rface vx l) INTER IMAGE f1 (moi_s34_vb tt kk (vx i)) INTER
     IMAGE f1 (moi_s34_vb tt kk (vx j)))`
  SUBST1_TAC THENL
   [SUBGOAL_THEN
     `(dd (moi_s4x_rface vx k) INTER IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk ((vx:num->real^N) i)) INTER
       IMAGE f1 (moi_s34_vb tt kk (vx j))) UNION
      ((dd:(real^N->bool)->real^3->bool) (moi_s4x_rface vx l) INTER IMAGE f1 (moi_s34_vb tt kk (vx i)) INTER
       IMAGE f1 (moi_s34_vb tt kk (vx j))) =
      UNIONS {dd (moi_s4x_rface vx m) INTER IMAGE f1 (moi_s34_vb tt kk (vx i)) INTER
              IMAGE f1 (moi_s34_vb tt kk (vx j)) | m | m = k \/ m = l}`
    SUBST1_TAC THENL
     [GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM; IN_UNION] THEN
      MESON_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC MOI_S4X_UNIONS_EQ THEN CONJ_TAC THENL
     [X_GEN_TAC `s:real^N->bool` THEN STRIP_TAC THEN DISJ2_TAC THEN
      MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `r:real^N->bool`;
                     `vx:num->real^N`; `s:real^N->bool`] MOI_S4X_RV_FACE_CLASS) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `m:num` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `m:num` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `segment[(vx:num->real^N) i,vx j] SUBSET s` THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`kk:(real^N->bool)->bool`; `r:real^N->bool`; `vx:num->real^N`;
                     `i:num`; `j:num`; `m:num`] MOI_S4X_RV_SEG_FACE) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
      MP_TAC(SPECL [`i:num`; `j:num`; `k:num`; `l:num`] MOI_S4X_PERM) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(MP_TAC o SPEC `m:num`)] THEN
      ASM_REWRITE_TAC[] THEN MESON_TAC[];
      X_GEN_TAC `m:num` THEN DISCH_TAC THEN DISJ2_TAC THEN
      EXISTS_TAC `moi_s4x_rface (vx:num->real^N) m` THEN REWRITE_TAC[] THEN
      SUBGOAL_THEN `m < 4 /\ ~(i:num = m) /\ ~(j = m)` STRIP_ASSUME_TAC THENL
       [FIRST_X_ASSUM(DISJ_CASES_THEN SUBST1_TAC) THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
        ALL_TAC] THEN
      MP_TAC(ISPECL [`kk:(real^N->bool)->bool`; `r:real^N->bool`; `vx:num->real^N`; `m:num`]
        MOI_S4X_RV_FACE_IN) THEN
      MP_TAC(ISPECL [`kk:(real^N->bool)->bool`; `r:real^N->bool`; `vx:num->real^N`;
                     `i:num`; `j:num`; `m:num`] MOI_S4X_RV_SEG_FACE) THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[]];
    ALL_TAC] THEN
  (* the rim arc t i INTER V j *)
  UNDISCH_TAC `moi_s4x_tball (\i. IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk (vx i)))
     (\i j. IMAGE f1 (moi_s34_sd tt kk (segment[vx i,vx j]) INTER moi_s34_bd tt kk))
     (\l. (dd:(real^N->bool)->real^3->bool) (moi_s4x_rface vx l))
     (\l. dd (moi_s4x_rface vx l) INTER IMAGE f1 (moi_s34_bd tt kk)) C C' t t'` THEN
  REWRITE_TAC[moi_s4x_tball] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `moi_s4x_hex:(num->real^3->bool)->(num->real^3->bool)->
      (num->num->real^3->bool)->(num->num->real^3->bool)->num->(real^3->bool)->(real^3->bool)->bool`))
      (concl th))) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  REWRITE_TAC[moi_s4x_hex] THEN BETA_TAC THEN
  DISCH_THEN(MP_TAC o SPEC `j:num` o last o CONJUNCTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `moi_s4x_rimarcs (\i. IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk ((vx:num->real^N) i)))
     (\i j. IMAGE f1 (moi_s34_sd tt kk (segment[vx i,vx j]) INTER moi_s34_bd tt kk))
     (\l. (dd:(real^N->bool)->real^3->bool) (moi_s4x_rface vx l)) C C'` THEN
  REWRITE_TAC[moi_s4x_rimarcs] THEN BETA_TAC THEN
  DISCH_THEN(MP_TAC o SPECL [`i:num`; `j:num`; `k:num`; `l:num`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  DISCH_THEN(DISJ_CASES_THEN (SUBST1_TAC o CONJUNCT1)) THEN ASM_REWRITE_TAC[]);;

(* A 1-cell is the closure of its open part. *)

let MOI_S4X_CELL1_DENSE = prove
 (`!a aa:real^N->bool. pl_cell_with_boundary 1 a aa ==> a SUBSET closure(a DIFF aa)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^1->real^N` STRIP_ASSUME_TAC o MATCH_MP MOI_S4L_CELL1_PL_ARC) THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `path_image(h:real^1->real^N)`)) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_SFR_ARC_DENSE THEN
  ASM_REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY]);;

(* A face disk of a face not in r: its open part lies outside the sphere. *)

let MOI_S4X_RB_FF_OUT = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car dd r vx C C' t t' s.
     moi_s4x_rball tt kk h ep f1 car dd r vx C C' t t' /\
     s IN moi_s34_simp kk (&2) /\ ~(s SUBSET r)
     ==> dd s DIFF (dd s INTER IMAGE f1 (moi_s34_bd tt kk)) SUBSET outside(moi_s4x_rS dd vx t) /\
         (dd s DIFF (dd s INTER IMAGE f1 (moi_s34_bd tt kk))) INTER IMAGE f1 (moi_s34_nb tt kk) = {} /\
         dd s INTER inside(moi_s4x_rS dd vx t) = {} /\
         (!l. l < 4 ==> dd s INTER dd (moi_s4x_rface vx l) = {})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o MATCH_MP MOI_S4X_RB_BASIC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_s4x_rball]) THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `dd:(real^N->bool)->real^3->bool`;
                 `s:real^N->bool`] MOI_S4X_FD) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  (* the face disks of r miss dd s *)
  SUBGOAL_THEN `!l. l < 4 ==> (dd:(real^N->bool)->real^3->bool) s INTER dd (moi_s4x_rface vx l) = {}`
  ASSUME_TAC THENL
   [X_GEN_TAC `l:num` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`kk:(real^N->bool)->bool`; `r:real^N->bool`; `vx:num->real^N`; `l:num`]
      MOI_S4X_RV_FACE_IN) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    REWRITE_TAC[GSYM DISJOINT] THEN MATCH_MP_TAC MOI_S4X_FD2 THEN
    MAP_EVERY EXISTS_TAC [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                          `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`] THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  (* a foreign vertex of s and a point of dd s on its ball *)
  SUBGOAL_THEN `?w. {w} IN kk /\ (w:real^N) IN s /\ ~(w IN r)` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `s:real^N->bool`]
      MOI_S4L_TRI_FORM) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `a:real^N` (X_CHOOSE_THEN `b:real^N` (X_CHOOSE_THEN `c:real^N`
      STRIP_ASSUME_TAC))) THEN
    UNDISCH_TAC `~((s:real^N->bool) SUBSET r)` THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `(a:real^N) IN r /\ b IN r /\ c IN r` THENL
     [DISCH_TAC THEN MATCH_MP_TAC(TAUT `F ==> q`) THEN
      UNDISCH_TAC `~(convex hull {a:real^N,b,c} SUBSET r)` THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC HULL_MINIMAL THEN
      CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      FIRST_ASSUM(MP_TAC o MATCH_MP MOI_S4X_RV_PARTS) THEN
      DISCH_THEN(SUBST1_TAC o CONJUNCT1 o CONJUNCT2) THEN REWRITE_TAC[CONVEX_CONVEX_HULL];
      DISCH_TAC THEN
      FIRST_X_ASSUM(DISJ_CASES_THEN MP_TAC o REWRITE_RULE[DE_MORGAN_THM]) THENL
       [DISCH_TAC THEN EXISTS_TAC `a:real^N`; ALL_TAC] THEN
      TRY(DISCH_THEN(DISJ_CASES_THEN ASSUME_TAC) THENL
       [EXISTS_TAC `b:real^N`; EXISTS_TAC `c:real^N`]) THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HULL_INC THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((dd:(real^N->bool)->real^3->bool) s DIFF (dd s INTER IMAGE (f1:real^N->real^3) (moi_s34_bd tt kk))) INTER
    IMAGE f1 (moi_s34_nb tt kk) = {}`
  ASSUME_TAC THENL
   [UNDISCH_TAC `(dd:(real^N->bool)->real^3->bool) s INTER IMAGE (f1:real^N->real^3) (moi_s34_nb tt kk) =
                 dd s INTER IMAGE f1 (moi_s34_bd tt kk)` THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!m. m < 4 ==> (t:num->real^3->bool) m SUBSET IMAGE (f1:real^N->real^3) (moi_s34_bd tt kk)`
  ASSUME_TAC THENL
   [X_GEN_TAC `m:num` THEN DISCH_TAC THEN MATCH_MP_TAC MOI_S4X_RB_TF THEN
    MAP_EVERY EXISTS_TAC [`h:real^N->real^3`; `ep:real^N->real`; `car:(real^N->bool)->real^3->bool`;
                          `dd:(real^N->bool)->real^3->bool`; `r:real^N->bool`; `vx:num->real^N`;
                          `C:num->num->real^3->bool`; `C':num->num->real^3->bool`;
                          `t':num->real^3->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* a point z0 of dd s on the ball of the foreign vertex w *)
  FIRST_X_ASSUM(MP_TAC o SPEC `w:real^N` o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `pl_cell_with_boundary 1:(real^3->bool)->(real^3->bool)->bool`)) (concl th))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `hw:real^1->real^3` STRIP_ASSUME_TAC o MATCH_MP MOI_S4L_CELL1_PL_ARC) THEN
  SUBGOAL_THEN `?z0:real^3. z0 IN (dd:(real^N->bool)->real^3->bool) s /\ z0 IN IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk w)`
  STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `pathstart(hw:real^1->real^3)` THEN
    MP_TAC(ISPEC `hw:real^1->real^3` PATHSTART_IN_PATH_IMAGE) THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                 `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                 `dd:(real^N->bool)->real^3->bool`; `r:real^N->bool`; `vx:num->real^N`;
                 `C:num->num->real^3->bool`; `C':num->num->real^3->bool`;
                 `t:num->real^3->bool`; `t':num->real^3->bool`; `w:real^N`] MOI_S4X_RB_FOREIGN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  ABBREV_TAC `S = moi_s4x_rS dd (vx:num->real^N) t` THEN
  MP_TAC(ISPEC `S:real^3->bool` MOI_S4X_JB) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(z0:real^3) IN outside S` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`DISJOINT (S UNION inside S) (IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk w))`;
      `(z0:real^3) IN IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk w)`;
      `inside S UNION outside S = (:real^3) DIFF S`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  (* the open part of dd s misses S *)
  SUBGOAL_THEN
   `(t:num->real^3->bool) 0 SUBSET IMAGE (f1:real^N->real^3) (moi_s34_bd tt kk) /\
    t 1 SUBSET IMAGE f1 (moi_s34_bd tt kk) /\ t 2 SUBSET IMAGE f1 (moi_s34_bd tt kk) /\
    t 3 SUBSET IMAGE f1 (moi_s34_bd tt kk) /\
    (dd:(real^N->bool)->real^3->bool) s INTER dd (moi_s4x_rface vx 0) = {} /\
    dd s INTER dd (moi_s4x_rface vx 1) = {} /\ dd s INTER dd (moi_s4x_rface vx 2) = {} /\
    dd s INTER dd (moi_s4x_rface vx 3) = {}`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[ARITH]; ALL_TAC] THEN
  ABBREV_TAC `FF = IMAGE (f1:real^N->real^3) (moi_s34_bd tt kk)` THEN
  ABBREV_TAC `e = (dd:(real^N->bool)->real^3->bool) s DIFF (dd s INTER FF)` THEN
  SUBGOAL_THEN `e INTER S:real^3->bool = {}` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o
      MATCH_MP MOI_S4X_RB_BASIC) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    EXPAND_TAC "e" THEN
    MAP_EVERY UNDISCH_TAC
     [`(t:num->real^3->bool) 0 SUBSET FF`; `(t:num->real^3->bool) 1 SUBSET FF`;
      `(t:num->real^3->bool) 2 SUBSET FF`; `(t:num->real^3->bool) 3 SUBSET FF`;
      `(dd:(real^N->bool)->real^3->bool) s INTER dd (moi_s4x_rface vx 0) = {}`;
      `(dd:(real^N->bool)->real^3->bool) s INTER dd (moi_s4x_rface vx 1) = {}`;
      `(dd:(real^N->bool)->real^3->bool) s INTER dd (moi_s4x_rface vx 2) = {}`;
      `(dd:(real^N->bool)->real^3->bool) s INTER dd (moi_s4x_rface vx 3) = {}`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(MATCH_MP MOI_S4L_PL_CELL2_TOPO (ASSUME
    `pl_cell_with_boundary 2 ((dd:(real^N->bool)->real^3->bool) s) (dd s INTER FF)`)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `e SUBSET outside(S:real^3->bool)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`S:real^3->bool`; `e:real^3->bool`] MOI_S4X_SIDE3) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(DISJ_CASES_THEN2 MP_TAC ACCEPT_TAC) THEN DISCH_TAC THEN
    MATCH_MP_TAC(TAUT `F ==> q`) THEN
    MP_TAC(ISPECL [`outside S:real^3->bool`; `e:real^3->bool`] OPEN_INTER_CLOSURE_EQ_EMPTY) THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC
     [`(z0:real^3) IN outside S`; `(z0:real^3) IN (dd:(real^N->bool)->real^3->bool) s`;
      `(dd:(real^N->bool)->real^3->bool) s SUBSET closure e`; `e SUBSET inside(S:real^3->bool)`;
      `inside S INTER outside S:real^3->bool = {}`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `closure e SUBSET S UNION outside(S:real^3->bool)` MP_TAC THENL
   [FIRST_ASSUM((fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) o check (fun th ->
      concl th = `closure(outside S) = S UNION outside(S:real^3->bool)`)) THEN
    MATCH_MP_TAC SUBSET_CLOSURE THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  MAP_EVERY UNDISCH_TAC
   [`(dd:(real^N->bool)->real^3->bool) s SUBSET closure e`;
    `inside S INTER outside S:real^3->bool = {}`; `S INTER inside S:real^3->bool = {}`] THEN
  SET_TAC[]);;

(* A face disk of a face not in r misses the hexagons. *)

let MOI_S4X_RB_FF_T = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car dd r vx C C' t t' s i.
     moi_s4x_rball tt kk h ep f1 car dd r vx C C' t t' /\
     s IN moi_s34_simp kk (&2) /\ ~(s SUBSET r) /\ i < 4
     ==> dd s INTER t i = {}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                 `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                 `dd:(real^N->bool)->real^3->bool`; `r:real^N->bool`; `vx:num->real^N`;
                 `C:num->num->real^3->bool`; `C':num->num->real^3->bool`;
                 `t:num->real^3->bool`; `t':num->real^3->bool`; `s:real^N->bool`] MOI_S4X_RB_FF_OUT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o CONJUNCT2 o MATCH_MP MOI_S4X_RB_BASIC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_s4x_rball]) THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `dd:(real^N->bool)->real^3->bool`;
                 `s:real^N->bool`] MOI_S4X_FD) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `{(vx:num->real^N) i} IN kk /\ (!m. m < 4 ==> {(vx:num->real^N) m} IN kk)`
  STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o MATCH_MP MOI_S4X_RV_PARTS) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(BETA_RULE(ISPECL
    [`\i. IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk ((vx:num->real^N) i))`;
     `\i j. IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk (segment[(vx:num->real^N) i,vx j]) INTER
                                     moi_s34_bd tt kk)`;
     `\l. (dd:(real^N->bool)->real^3->bool) (moi_s4x_rface (vx:num->real^N) l)`;
     `\l. (dd:(real^N->bool)->real^3->bool) (moi_s4x_rface (vx:num->real^N) l) INTER
          IMAGE (f1:real^N->real^3) (moi_s34_bd tt kk)`;
     `C:num->num->real^3->bool`; `C':num->num->real^3->bool`;
     `t:num->real^3->bool`; `t':num->real^3->bool`] MOI_S4X_TB_FACTS)) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `i:num` o CONJUNCT1) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
  ASM_CASES_TAC `(vx:num->real^N) i IN s` THENL
   [ALL_TAC;
    FIRST_X_ASSUM(MP_TAC o SPEC `(vx:num->real^N) i` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `DISJOINT:(real^3->bool)->(real^3->bool)->bool`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(t:num->real^3->bool) i SUBSET IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk (vx(i:num)))` THEN
    SET_TAC[]] THEN
  (* s is convex *)
  SUBGOAL_THEN `convex(s:real^N->bool)` ASSUME_TAC THENL
   [FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4L_TUBE_TUBE) THEN
    UNDISCH_TAC `(s:real^N->bool) IN moi_s34_simp kk (&2)` THEN
    REWRITE_TAC[moi_s34_simp; IN_ELIM_THM] THEN STRIP_TAC THEN
    SUBGOAL_THEN `?n. n simplex (s:real^N->bool)` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `lf_simplicial_complex (kk:(real^N->bool)->bool)` THEN
      REWRITE_TAC[lf_simplicial_complex] THEN ASM_MESON_TAC[];
      ASM_MESON_TAC[SIMPLEX_IMP_CONVEX]];
    ALL_TAC] THEN
  (* the face arc a = dd s INTER V i with its ends P *)
  FIRST_ASSUM(MP_TAC o SPEC `(vx:num->real^N) i` o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `pl_cell_with_boundary 1:(real^3->bool)->(real^3->bool)->bool`)) (concl th))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  ABBREV_TAC `a = (dd:(real^N->bool)->real^3->bool) s INTER
                  IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk (vx(i:num)))` THEN
  ABBREV_TAC `P = UNIONS {(dd:(real^N->bool)->real^3->bool) s INTER
                          IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g) | g |
                          g IN moi_s34_simp kk (&1) /\ (vx:num->real^N) i IN g /\ g SUBSET s}` THEN
  (* a lies in the frontier of V i *)
  SUBGOAL_THEN `a SUBSET frontier(IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk (vx(i:num))))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                   `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`]
                  MOI_S4L_FRAME_F1) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    SUBGOAL_THEN `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk (vx(i:num))) SUBSET
                  IMAGE f1 (moi_s34_nb tt kk)` ASSUME_TAC THENL
     [MATCH_MP_TAC IMAGE_SUBSET THEN
      FIRST_ASSUM(MP_TAC o MATCH_MP MOI_S4L_GRAPH_TUBE) THEN
      DISCH_THEN(MP_TAC o SPEC `(vx:num->real^N) i` o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                   `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                   `(vx:num->real^N) i`] MOI_S4L_AV_BASIC) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    REWRITE_TAC[frontier] THEN
    ASM_SIMP_TAC[CLOSURE_CLOSED; COMPACT_IMP_CLOSED] THEN
    MP_TAC(ISPECL [`IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk (vx(i:num)))`;
                   `IMAGE (f1:real^N->real^3) (moi_s34_nb tt kk)`] SUBSET_INTERIOR) THEN
    ASM_REWRITE_TAC[] THEN
    ABBREV_TAC `VVi = IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk (vx(i:num)))` THEN
    ABBREV_TAC `FNN = IMAGE (f1:real^N->real^3) (moi_s34_nb tt kk)` THEN
    ABBREV_TAC `FBB = IMAGE (f1:real^N->real^3) (moi_s34_bd tt kk)` THEN
    MAP_EVERY UNDISCH_TAC
     [`(dd:(real^N->bool)->real^3->bool) s INTER FNN = dd s INTER FBB`;
      `FBB INTER interior FNN:real^3->bool = {}`;
      `VVi SUBSET FNN:real^3->bool`;
      `(dd:(real^N->bool)->real^3->bool) s INTER VVi = a`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  (* the open part of a lies in t' i *)
  SUBGOAL_THEN `a DIFF P SUBSET (t':num->real^3->bool) i` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_DIFF] THEN X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(z:real^3) IN (dd:(real^N->bool)->real^3->bool) s /\
                  z IN IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk (vx(i:num)))`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(z:real^3) IN a` THEN EXPAND_TAC "a" THEN REWRITE_TAC[IN_INTER];
      ALL_TAC] THEN
    SUBGOAL_THEN `!m. m < 4 /\ ~(m = i)
                      ==> ~((z:real^3) IN IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk (vx m)))`
    ASSUME_TAC THENL
     [X_GEN_TAC `m:num` THEN STRIP_TAC THEN DISCH_TAC THEN
      ASM_CASES_TAC `(vx:num->real^N) m IN s` THENL
       [UNDISCH_TAC `~((z:real^3) IN P)` THEN REWRITE_TAC[] THEN EXPAND_TAC "P" THEN
        REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM] THEN
        EXISTS_TAC `segment[(vx:num->real^N) i,vx m]` THEN
        MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `r:real^N->bool`;
                       `vx:num->real^N`; `i:num`; `m:num`] MOI_S4X_RV_EDGE) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[];
          DISCH_THEN(fun th -> ASSUME_TAC(CONJUNCT1 th) THEN ASSUME_TAC(CONJUNCT1(CONJUNCT2 th)))] THEN
        ASM_REWRITE_TAC[ENDS_IN_SEGMENT] THEN CONJ_TAC THENL
         [ASM_SIMP_TAC[CONVEX_CONTAINS_SEGMENT_IMP]; ALL_TAC] THEN
        MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                       `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                       `r:real^N->bool`; `vx:num->real^N`; `i:num`; `m:num`] MOI_S4X_RC_EDGE) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT1)] THEN
        ASM_REWRITE_TAC[IN_INTER];
        FIRST_X_ASSUM(MP_TAC o SPEC `(vx:num->real^N) m` o check (fun th -> is_forall(concl th) &&
          can (find_term ((=) `DISJOINT:(real^3->bool)->(real^3->bool)->bool`)) (concl th))) THEN
        ASM_SIMP_TAC[] THEN
        MAP_EVERY UNDISCH_TAC
         [`(z:real^3) IN (dd:(real^N->bool)->real^3->bool) s`;
          `(z:real^3) IN IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk (vx(m:num)))`] THEN
        SET_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `~((z:real^3) IN (t:num->real^3->bool) i)` ASSUME_TAC THENL
     [DISCH_TAC THEN
      MP_TAC(REWRITE_RULE[GSYM moi_s4x_rS] (BETA_RULE(ISPECL
        [`\i. IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk ((vx:num->real^N) i))`;
         `\i j. IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk (segment[(vx:num->real^N) i,vx j]) INTER
                                         moi_s34_bd tt kk)`;
         `\l. (dd:(real^N->bool)->real^3->bool) (moi_s4x_rface (vx:num->real^N) l)`;
         `\l. (dd:(real^N->bool)->real^3->bool) (moi_s4x_rface (vx:num->real^N) l) INTER
              IMAGE (f1:real^N->real^3) (moi_s34_bd tt kk)`;
         `C:num->num->real^3->bool`; `C':num->num->real^3->bool`;
         `t:num->real^3->bool`; `t':num->real^3->bool`; `i:num`;
         `(dd:(real^N->bool)->real^3->bool) s`;
         `(dd:(real^N->bool)->real^3->bool) s INTER IMAGE (f1:real^N->real^3) (moi_s34_bd tt kk)`;
         `z:real^3`] MOI_S4X_TB_FACE_PT))) THEN
      REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
       [SUBGOAL_THEN `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk (vx(i:num))) SUBSET
                      IMAGE f1 (moi_s34_nb tt kk)` MP_TAC THENL
         [MATCH_MP_TAC IMAGE_SUBSET THEN
          FIRST_ASSUM(MP_TAC o MATCH_MP MOI_S4L_GRAPH_TUBE) THEN
          DISCH_THEN(MP_TAC o SPEC `(vx:num->real^N) i` o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
          ASM_SIMP_TAC[];
          ALL_TAC] THEN
        UNDISCH_TAC
         `((dd:(real^N->bool)->real^3->bool) s DIFF (dd s INTER IMAGE (f1:real^N->real^3) (moi_s34_bd tt kk))) INTER
          IMAGE f1 (moi_s34_nb tt kk) = {}` THEN
        MATCH_ACCEPT_TAC(SET_RULE `!e n v:real^3->bool. e INTER n = {} ==> v SUBSET n ==> e INTER v = {}`);
        X_GEN_TAC `l:num` THEN DISCH_TAC THEN
        SUBGOAL_THEN `(dd:(real^N->bool)->real^3->bool) s INTER dd (moi_s4x_rface vx l) = {}`
        MP_TAC THENL
         [UNDISCH_TAC `!l. l < 4 ==> (dd:(real^N->bool)->real^3->bool) s INTER dd (moi_s4x_rface vx l) = {}` THEN
          ASM_SIMP_TAC[];
          ALL_TAC] THEN
        UNDISCH_TAC `(z:real^3) IN (dd:(real^N->bool)->real^3->bool) s` THEN SET_TAC[]];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) &&
      rhs(concl th) = `frontier(IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk (vx(i:num))))`)) THEN
    DISCH_THEN(MP_TAC o AP_TERM `\u:real^3->bool. (z:real^3) IN u`) THEN BETA_TAC THEN
    MATCH_MP_TAC(TAUT `b /\ (a ==> c) ==> (a <=> b) ==> c`) THEN CONJ_TAC THENL
     [UNDISCH_TAC `a SUBSET frontier(IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk (vx(i:num))))` THEN
      UNDISCH_TAC `(z:real^3) IN a` THEN SET_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[IN_UNION; UNIONS_GSPEC; IN_ELIM_THM; IN_INTER] THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(DISJ_CASES_THEN2 ACCEPT_TAC (X_CHOOSE_THEN `m:num` STRIP_ASSUME_TAC)) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `m:num` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `z:real^3`)) (concl th) &&
      is_imp(snd(dest_forall(concl th))))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `a SUBSET (t':num->real^3->bool) i` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `closure(a DIFF P:real^3->bool)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC MOI_S4X_CELL1_DENSE THEN FIRST_ASSUM ACCEPT_TAC;
      MATCH_MP_TAC CLOSURE_MINIMAL THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(x:real^3) IN (t:num->real^3->bool) i INTER t' i` MP_TAC THENL
   [ASM_REWRITE_TAC[IN_INTER] THEN
    UNDISCH_TAC `a SUBSET (t':num->real^3->bool) i` THEN
    UNDISCH_TAC `(dd:(real^N->bool)->real^3->bool) s INTER
                 IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk (vx(i:num))) = a` THEN
    UNDISCH_TAC `(t:num->real^3->bool) i SUBSET IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk (vx(i:num)))` THEN
    UNDISCH_TAC `(x:real^3) IN (dd:(real^N->bool)->real^3->bool) s` THEN
    UNDISCH_TAC `(x:real^3) IN (t:num->real^3->bool) i` THEN
    MATCH_ACCEPT_TAC(SET_RULE `!x:real^3 d u v a w. x IN u ==> x IN d ==> u SUBSET v ==>
                                 d INTER v = a ==> a SUBSET w ==> x IN w`);
    ALL_TAC] THEN
  FIRST_ASSUM((fun th -> REWRITE_TAC[th]) o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `(t:num->real^3->bool) i INTER t' i`)) THEN
  REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM; IN_INTER] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:num` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `!l. l < 4 ==> (dd:(real^N->bool)->real^3->bool) s INTER dd (moi_s4x_rface vx l) = {}` THEN
  DISCH_THEN(MP_TAC o SPEC `m:num`) THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `(x:real^3) IN (dd:(real^N->bool)->real^3->bool) s` THEN
  UNDISCH_TAC `(x:real^3) IN (dd:(real^N->bool)->real^3->bool) (moi_s4x_rface vx m)` THEN
  SET_TAC[]);;

(* Clause: the tetra ball misses the face disks of the faces not in r. *)

let MOI_S4X_RB_FFACE = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car dd r vx C C' t t' s.
     moi_s4x_rball tt kk h ep f1 car dd r vx C C' t t' /\
     s IN moi_s34_simp kk (&2) /\ ~(s SUBSET r)
     ==> DISJOINT (moi_s4x_rS dd vx t UNION inside(moi_s4x_rS dd vx t)) (dd s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                 `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                 `dd:(real^N->bool)->real^3->bool`; `r:real^N->bool`; `vx:num->real^N`;
                 `C:num->num->real^3->bool`; `C':num->num->real^3->bool`;
                 `t:num->real^3->bool`; `t':num->real^3->bool`; `s:real^N->bool`] MOI_S4X_RB_FF_OUT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `!m. m < 4 ==> (dd:(real^N->bool)->real^3->bool) s INTER (t:num->real^3->bool) m = {}`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_S4X_RB_FF_T THEN
    MAP_EVERY EXISTS_TAC [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                          `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                          `r:real^N->bool`; `vx:num->real^N`; `C:num->num->real^3->bool`;
                          `C':num->num->real^3->bool`; `t':num->real^3->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o
    MATCH_MP MOI_S4X_RB_BASIC) THEN
  DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN
   `(dd:(real^N->bool)->real^3->bool) s INTER (t:num->real^3->bool) 0 = {} /\ dd s INTER t 1 = {} /\
    dd s INTER t 2 = {} /\ dd s INTER t 3 = {} /\
    dd s INTER dd (moi_s4x_rface (vx:num->real^N) 0) = {} /\ dd s INTER dd (moi_s4x_rface vx 1) = {} /\
    dd s INTER dd (moi_s4x_rface vx 2) = {} /\ dd s INTER dd (moi_s4x_rface vx 3) = {}`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[ARITH]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) &&
    can (find_term ((=) `inside:(real^3->bool)->real^3->bool`)) (lhs(concl th)))) THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o
    MATCH_MP MOI_S4X_RB_BASIC) THEN
  DISCH_THEN SUBST1_TAC THEN
  MAP_EVERY UNDISCH_TAC
   [`(dd:(real^N->bool)->real^3->bool) s INTER (t:num->real^3->bool) 0 = {}`;
    `(dd:(real^N->bool)->real^3->bool) s INTER (t:num->real^3->bool) 1 = {}`;
    `(dd:(real^N->bool)->real^3->bool) s INTER (t:num->real^3->bool) 2 = {}`;
    `(dd:(real^N->bool)->real^3->bool) s INTER (t:num->real^3->bool) 3 = {}`;
    `(dd:(real^N->bool)->real^3->bool) s INTER dd (moi_s4x_rface (vx:num->real^N) 0) = {}`;
    `(dd:(real^N->bool)->real^3->bool) s INTER dd (moi_s4x_rface (vx:num->real^N) 1) = {}`;
    `(dd:(real^N->bool)->real^3->bool) s INTER dd (moi_s4x_rface (vx:num->real^N) 2) = {}`;
    `(dd:(real^N->bool)->real^3->bool) s INTER dd (moi_s4x_rface (vx:num->real^N) 3) = {}`] THEN
  SET_TAC[]);;

(* The tetra ball C''(r): all clauses of moi_s4x_local. *)

let MOI_S4X_LOCAL_EX = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car dd r.
     PL_SCHOENFLIES_3_STATEMENT /\ moi_s34_tube tt kk /\ moi_s34_frame tt kk h ep f1 car /\
     moi_s34_fdisk tt kk f1 car dd /\ r IN moi_s34_simp kk (&3)
     ==> ?b. moi_s4x_local tt kk f1 car dd r b`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_S4X_RB_EX) THEN
  DISCH_THEN(X_CHOOSE_THEN `vx:num->real^N` (X_CHOOSE_THEN `C:num->num->real^3->bool`
    (X_CHOOSE_THEN `C':num->num->real^3->bool` (X_CHOOSE_THEN `t:num->real^3->bool`
    (X_CHOOSE_TAC `t':num->real^3->bool`))))) THEN
  EXISTS_TAC `moi_s4x_rS dd (vx:num->real^N) t UNION inside(moi_s4x_rS dd vx t)` THEN
  REWRITE_TAC[moi_s4x_local] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4X_RB_FRONT) THEN
  REPEAT CONJ_TAC THENL
   [FIRST_ASSUM(ACCEPT_TAC o CONJUNCT1 o CONJUNCT2 o MATCH_MP MOI_S4X_RB_BASIC);
    FIRST_ASSUM(ACCEPT_TAC o MATCH_MP MOI_S4X_RB_HULL);
    FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    X_GEN_TAC `v:real^N` THEN STRIP_TAC THEN MATCH_MP_TAC MOI_S4X_RB_PATCH THEN
    MAP_EVERY EXISTS_TAC [`h:real^N->real^3`; `ep:real^N->real`; `car:(real^N->bool)->real^3->bool`;
                          `C:num->num->real^3->bool`;
                          `C':num->num->real^3->bool`; `t':num->real^3->bool`] THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `g:real^N->bool` THEN STRIP_TAC THEN MATCH_MP_TAC MOI_S4X_RB_EDGE THEN
    MAP_EVERY EXISTS_TAC [`h:real^N->real^3`; `ep:real^N->real`; `car:(real^N->bool)->real^3->bool`;
                          `C:num->num->real^3->bool`;
                          `C':num->num->real^3->bool`; `t':num->real^3->bool`] THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `w:real^N` THEN STRIP_TAC THEN MATCH_MP_TAC MOI_S4X_RB_FOREIGN THEN
    MAP_EVERY EXISTS_TAC [`h:real^N->real^3`; `ep:real^N->real`; `car:(real^N->bool)->real^3->bool`;
                          `r:real^N->bool`;
                          `C:num->num->real^3->bool`; `C':num->num->real^3->bool`;
                          `t':num->real^3->bool`] THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `s:real^N->bool` THEN STRIP_TAC THEN MATCH_MP_TAC MOI_S4X_RB_FFACE THEN
    MAP_EVERY EXISTS_TAC [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                          `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                          `r:real^N->bool`; `C:num->num->real^3->bool`;
                          `C':num->num->real^3->bool`; `t':num->real^3->bool`] THEN
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The main theorem RESID_A.                                                 *)
(* ------------------------------------------------------------------------- *)

let RESID_A = prove
 (MOI_S4X_RESID_A,
  DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC MOI_S4X_LOCAL_EX THEN
  MAP_EVERY EXISTS_TAC [`h:real^N->real^3`; `ep:real^N->real`] THEN
  ASM_REWRITE_TAC[]);;

