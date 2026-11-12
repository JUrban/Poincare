(* ========================================================================= *)
(* pc_moi_sch3_tilt: REDUCE_FROM_COUNT : |- MOI_STL_CAP_COUNT ==>            *)
(* MOI_SCH3_REDUCE (Moise GTM 47, proof of 17.12, Lemma 1, pp.122-123): a    *)
(* PL 2-sphere with a generic height of positive index is carried by an      *)
(* ambient PLH (the identity off w) onto two PL 2-spheres glued along a      *)
(* plane 2-cell, each with a generic height of smaller index, given the cap  *)
(* count MOI_STL_CAP_COUNT (proved as CAP_COUNT in pc_moi_sch3_capc).        *)
(* Route: a singular vertex p with at least two level polygons; INMOST gives *)
(* an inmost polygon with its plane disk; LEVEL_CONVEXIFY makes the disk a   *)
(* triangle t; the image sphere splits along the boundary of t into two      *)
(* disks; the caps are disk UNION t; the heights are tilted about f p in     *)
(* opposite directions so that t leaves the level; the index comparison is   *)
(* MOI_SCD_INDEX_COMPARE with MOI_SCD_FAR_LEVELS.                            *)
(* ========================================================================= *)

needs "src/pc_moi_sch3_stmt.ml";;
needs "src/pc_moi_sch3_lev.ml";;
needs "src/pc_moi_sch3_cvx.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* The cap count statement MOI_STL_CAP_COUNT (proved as CAP_COUNT in        *)
(* pc_moi_sch3_capc): a cap d UNION t of the image sphere, with the disk d  *)
(* locally on the side sigma of the boundary of the triangle t off f p, and *)
(* any triangulation c1 of the cap: for every small tilt of the height in   *)
(* direction sigma b (b positive on t minus f p) and every generic height   *)
(* a1 close to it relative to the tilt, the level through f p has at least  *)
(* one level polygon fewer than the original level of p.                    *)
(* ------------------------------------------------------------------------- *)

let MOI_STL_CAP_COUNT =
 `!c (a:real^3) p (f:real^3->real^3) (g:real^3->real^3) (t:real^3->bool)
   (d:real^3->bool) (b:real^3) (sigma:real) (c1:(real^3->bool)->bool).
     moi_sch3_generic c a /\ pl_sphere 2 (UNIONS c) /\ {p} IN c /\
     4 <= moi_sch3_crossings c a p /\
     pl_homeomorphism ((:real^3),(:real^3)) (f,g) /\
     (!x. a dot f x = a dot x) /\
     &2 simplex t /\ t SUBSET {x | a dot x = a dot p} /\
     IMAGE f (UNIONS c) INTER t = relative_frontier t /\
     (f p IN t ==> {f p} face_of t) /\
     d SUBSET IMAGE f (UNIONS c) /\
     pl_cell_with_boundary 2 d (relative_frontier t) /\
     (sigma = &1 \/ sigma = -- &1) /\
     (!x. x IN relative_frontier t /\ ~(x = f p)
          ==> ?r. &0 < r /\
                  !y. y IN d /\ dist(x,y) < r
                      ==> &0 <= sigma * (a dot y - a dot p)) /\
     (!x. x IN t /\ ~(x = f p) ==> &0 < b dot (x - f p)) /\
     simplicial_complex c1 /\ UNIONS c1 = d UNION t /\ {f p} IN c1
     ==> ?e. &0 < e /\
             !(a1:real^3) (eta:real).
               &0 < eta /\ eta < e /\
               norm(a1 - (a + (sigma * eta) % b)) < e * eta /\
               moi_sch3_generic c1 a1
               ==> CARD (moi_sch3_level_polygons (d UNION t) a1 (a1 dot f p)) + 1 <=
                   CARD (moi_sch3_level_polygons (UNIONS c) a (a dot p))`;;

(* ------------------------------------------------------------------------- *)
(* 1. The construction: a singular vertex with at least two level polygons, *)
(* a gap to the other vertex levels, the inmost polygon with its plane disk *)
(* and the level-preserving PLH that makes the disk a triangle.             *)
(* ------------------------------------------------------------------------- *)

let MOI_STL_POSITIVE_SUMMAND = prove
 (`!c (a:real^3).
     0 < moi_sch3_index c a
     ==> ?p. {p} IN c /\ 4 <= moi_sch3_crossings c a p /\
             2 <= CARD (moi_sch3_level_polygons (UNIONS c) a (a dot p))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_sch3_index] THEN
  ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
  REWRITE_TAC[NOT_EXISTS_THM; ARITH_RULE `~(0 < n) <=> n = 0`] THEN
  DISCH_TAC THEN MATCH_MP_TAC NSUM_EQ_0 THEN
  REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `v:real^3` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `v:real^3`) THEN ASM_REWRITE_TAC[] THEN ARITH_TAC);;

let MOI_STL_VERTEX_GAP = prove
 (`!c (a:real^3) p.
     moi_sch3_generic c a /\ {p} IN c
     ==> ?del. &0 < del /\
               !v. {v} IN c /\ ~(v = p) ==> &4 * del <= abs(a dot v - a dot p)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_sch3_generic] THEN STRIP_TAC THEN
  SUBGOAL_THEN `FINITE {v:real^3 | {v} IN c /\ ~(v = p)}` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{v:real^3 | {v} IN c}` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MOI_SCD_VERTICES_FINITE THEN
      ASM_MESON_TAC[simplicial_complex];
      SET_TAC[]];
    ALL_TAC] THEN
  ASM_CASES_TAC `{v:real^3 | {v} IN c /\ ~(v = p)} = {}` THENL
   [EXISTS_TAC `&1` THEN REWRITE_TAC[REAL_LT_01] THEN ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPEC `IMAGE (\v:real^3. abs(a dot v - a dot p))
                      {v:real^3 | {v} IN c /\ ~(v = p)}` INF_FINITE) THEN
  ASM_SIMP_TAC[FINITE_IMAGE; IMAGE_EQ_EMPTY; FORALL_IN_IMAGE; IN_IMAGE] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `v0:real^3` STRIP_ASSUME_TAC)
    (LABEL_TAC "inf")) THEN
  EXISTS_TAC `inf (IMAGE (\v:real^3. abs(a dot v - a dot p))
                         {v:real^3 | {v} IN c /\ ~(v = p)}) / &4` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN REWRITE_TAC[REAL_OF_NUM_LT; ARITH] THEN
    FIRST_X_ASSUM SUBST1_TAC THEN
    REWRITE_TAC[GSYM REAL_ABS_NZ; REAL_SUB_0] THEN ASM_MESON_TAC[];
    X_GEN_TAC `v:real^3` THEN STRIP_TAC THEN
    USE_THEN "inf" (fun th -> MP_TAC(MATCH_MP th
      (CONJ (ASSUME `{v:real^3} IN c`) (ASSUME `~(v:real^3 = p)`)))) THEN
    MATCH_ACCEPT_TAC(REAL_ARITH `!m y. m <= y ==> &4 * m / &4 <= y`)]);;

let MOI_STL_CONVEXIFIED = prove
 (`!c (a:real^3) p w.
     moi_sch3_generic c a /\ pl_sphere 2 (UNIONS c) /\ {p} IN c /\
     4 <= moi_sch3_crossings c a p /\
     convex w /\ open w /\ UNIONS c SUBSET w
     ==> ?del j0 d0 (f:real^3->real^3) g t.
           &0 < del /\
           (!v. {v} IN c /\ ~(v = p) ==> &4 * del <= abs(a dot v - a dot p)) /\
           j0 IN moi_sch3_level_polygons (UNIONS c) a (a dot p) /\
           pl_cell_with_boundary 2 d0 j0 /\ d0 SUBSET {x | a dot x = a dot p} /\
           d0 INTER UNIONS c = j0 /\
           pl_homeomorphism ((:real^3),(:real^3)) (f,g) /\
           (!x. a dot f x = a dot x) /\
           (!x. ~(x IN w) \/ del <= abs(a dot x - a dot p) ==> f x = x) /\
           &2 simplex t /\ IMAGE f d0 = t /\ IMAGE f j0 = relative_frontier t /\
           (p IN j0 ==> {f p} face_of t) /\ (p IN j0 \/ ~(p IN d0))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `a:real^3`; `p:real^3`]
    MOI_STL_VERTEX_GAP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `del:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `a:real^3`; `p:real^3`] INMOST) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `j0:real^3->bool` (X_CHOOSE_THEN `d0:real^3->bool`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `(p:real^3) IN j0 \/ ~(p IN d0)` ASSUME_TAC THENL
   [SUBGOAL_THEN `(p:real^3) IN UNIONS c` MP_TAC THENL
     [REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `{p:real^3}` THEN
      ASM_REWRITE_TAC[IN_SING];
      UNDISCH_TAC `d0 INTER UNIONS c = (j0:real^3->bool)` THEN SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`UNIONS c:real^3->bool`; `a:real^3`; `a dot (p:real^3)`;
                 `j0:real^3->bool`; `d0:real^3->bool`; `p:real^3`;
                 `w:real^3->bool`; `del:real`] LEVEL_CONVEXIFY) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[MOI_SCD_PL_SPHERE_POLYHEDRON; pl_polyhedron; COMPACT_UNIONS;
                    POLYTOPE_IMP_COMPACT];
      ASM_MESON_TAC[moi_sch3_generic];
      REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `{p:real^3}` THEN
      ASM_REWRITE_TAC[IN_SING]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^3->real^3` (X_CHOOSE_THEN `g:real^3->real^3`
    (X_CHOOSE_THEN `t:real^3->bool` STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`del:real`; `j0:real^3->bool`; `d0:real^3->bool`;
    `f:real^3->real^3`; `g:real^3->real^3`; `t:real^3->bool`] THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* 2. The image sphere, its split along the boundary of the triangle, and   *)
(* the two caps disk UNION triangle.                                         *)
(* ------------------------------------------------------------------------- *)

let MOI_STL_SIMPLEX_CELL = prove
 (`!t:real^N->bool. &2 simplex t ==> pl_cell_with_boundary 2 t (relative_frontier t)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pl_cell_with_boundary] THEN
  MAP_EVERY EXISTS_TAC [`t:real^N->bool`; `\x:real^N. x`; `\x:real^N. x`] THEN
  ASM_REWRITE_TAC[pl_homeomorphism; HOMEOMORPHISM_ID; IMAGE_ID] THEN
  REWRITE_TAC[GSYM LOCALLY_POLYHEDRAL_EQ_PL_MAP_ON_ID] THEN
  ASM_MESON_TAC[LOCALLY_POLYHEDRAL_POLYTOPE; SIMPLEX_IMP_POLYTOPE]);;

let MOI_STL_SPHERE_IMAGE = prove
 (`!n s (f:real^3->real^3) g.
     pl_sphere n s /\ pl_homeomorphism ((:real^3),(:real^3)) (f,g)
     ==> pl_sphere n (IMAGE f s)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC PL_SPHERE_PL_HOMEOMORPHIC THEN
  MAP_EVERY EXISTS_TAC [`s:real^3->bool`; `f:real^3->real^3`;
                        `g:real^3->real^3`] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_FSA_PL_HOMEO_RESTRICT THEN
  EXISTS_TAC `(:real^3)` THEN ASM_REWRITE_TAC[SUBSET_UNIV] THEN
  ASM_MESON_TAC[LOCALLY_POLYHEDRAL_PL_POLYHEDRON; MOI_SCD_PL_SPHERE_POLYHEDRON]);;

let MOI_STL_CAP_SPHERES = prove
 (`!s t d1 d2:real^3->bool.
     &2 simplex t /\ s INTER t = relative_frontier t /\
     pl_cell_with_boundary 2 d1 (relative_frontier t) /\
     pl_cell_with_boundary 2 d2 (relative_frontier t) /\
     d1 UNION d2 = s /\ d1 INTER d2 = relative_frontier t
     ==> pl_sphere 2 (d1 UNION t) /\ pl_sphere 2 (d2 UNION t) /\
         d1 INTER t = relative_frontier t /\ d2 INTER t = relative_frontier t /\
         (d1 UNION t) INTER (d2 UNION t) = t /\
         ((d1 UNION t) UNION (d2 UNION t)) DIFF (t DIFF relative_frontier t) = s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `relative_frontier t SUBSET (t:real^3->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC RELATIVE_FRONTIER_SUBSET THEN
    ASM_MESON_TAC[SIMPLEX_IMP_CLOSED];
    ALL_TAC] THEN
  SUBGOAL_THEN `relative_frontier t SUBSET (d1:real^3->bool) /\
                relative_frontier t SUBSET (d2:real^3->bool)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_SS2_CELL_FACTS]; ALL_TAC] THEN
  SUBGOAL_THEN `(d1:real^3->bool) INTER t = relative_frontier t /\
                (d2:real^3->bool) INTER t = relative_frontier t`
    STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`s INTER t:real^3->bool = relative_frontier t`;
      `d1 UNION d2:real^3->bool = s`;
      `relative_frontier t SUBSET (t:real^3->bool)`;
      `relative_frontier t SUBSET (d1:real^3->bool)`;
      `relative_frontier t SUBSET (d2:real^3->bool)`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_cell_with_boundary 2 t (relative_frontier (t:real^3->bool))`
    ASSUME_TAC THENL
   [ASM_SIMP_TAC[MOI_STL_SIMPLEX_CELL]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC DISK_UNION THEN
    EXISTS_TAC `relative_frontier t:real^3->bool` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC DISK_UNION THEN
    EXISTS_TAC `relative_frontier t:real^3->bool` THEN ASM_REWRITE_TAC[];
    MAP_EVERY UNDISCH_TAC
     [`d1 INTER d2:real^3->bool = relative_frontier t`;
      `relative_frontier t SUBSET (t:real^3->bool)`] THEN
    SET_TAC[];
    MAP_EVERY UNDISCH_TAC
     [`s INTER t:real^3->bool = relative_frontier t`;
      `d1 UNION d2:real^3->bool = s`;
      `relative_frontier t SUBSET (t:real^3->bool)`;
      `relative_frontier t SUBSET (d1:real^3->bool)`] THEN
    SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* 3. The level set of the original sphere at the singular level: finitely *)
(* many level polygons, covering the level set, pairwise meeting at most in *)
(* p; near a point of a level polygon other than p the level set is just  *)
(* that polygon.                                                            *)
(* ------------------------------------------------------------------------- *)

let MOI_STL_LEVEL_STRUCTURE = prove
 (`!c (a:real^3) p.
     moi_sch3_generic c a /\ pl_sphere 2 (UNIONS c) /\ {p} IN c /\
     4 <= moi_sch3_crossings c a p
     ==> FINITE (moi_sch3_level_polygons (UNIONS c) a (a dot p)) /\
         (!x. x IN UNIONS c /\ a dot x = a dot p
              ==> ?q. q IN moi_sch3_level_polygons (UNIONS c) a (a dot p) /\ x IN q) /\
         (!q1 q2. q1 IN moi_sch3_level_polygons (UNIONS c) a (a dot p) /\
                  q2 IN moi_sch3_level_polygons (UNIONS c) a (a dot p) /\
                  ~(q1 = q2)
                  ==> q1 INTER q2 SUBSET {p})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `a:real^3`; `a dot (p:real^3)`]
    MOI_SLV_LEVEL_COMPLEX) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `a:real^3`; `p:real^3`]
    MOI_SLV_LEVEL_GRAPH2) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `~({s | s IN {s INTER {x:real^3 | a dot x = a dot p} | s IN c} /\
           aff_dim s = &1 /\ p IN s} = {})`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `a:real^3`; `p:real^3`]
      MOI_SLV_LEVEL_STAR) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o SYM) THEN DISCH_TAC THEN
    UNDISCH_TAC `4 <= moi_sch3_crossings c a p` THEN
    ASM_REWRITE_TAC[CARD_CLAUSES] THEN ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC LEVEL_POLYGONS_FINITE THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`{s INTER {x:real^3 | a dot x = a dot p} | s IN c}`;
                   `p:real^3`; `x:real^3`] MOI_SLV_G2_POINT_COVER) THEN
    ASM_REWRITE_TAC[DIMINDEX_3; ARITH; IN_INTER; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `q:real^3->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `q:real^3->bool` THEN
    REWRITE_TAC[MOI_SLV_LEVEL_POLYGONS_EQ; IN_ELIM_THM] THEN ASM_MESON_TAC[];
    REWRITE_TAC[MOI_SLV_LEVEL_POLYGONS_EQ; IN_ELIM_THM] THEN
    MAP_EVERY X_GEN_TAC [`q1:real^3->bool`; `q2:real^3->bool`] THEN STRIP_TAC THEN
    REWRITE_TAC[SUBSET; IN_INTER; IN_SING] THEN X_GEN_TAC `x:real^3` THEN
    STRIP_TAC THEN ASM_CASES_TAC `x:real^3 = p` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `~(q1:real^3->bool = q2)` THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_SLV_G2_UNIQUE THEN
    MAP_EVERY EXISTS_TAC [`{s INTER {x:real^3 | a dot x = a dot p} | s IN c}`;
                          `p:real^3`; `x:real^3`] THEN
    ASM_REWRITE_TAC[]]);;

let MOI_STL_LEVEL_NEAR_POLYGON = prove
 (`!c (a:real^3) p j0 x.
     moi_sch3_generic c a /\ pl_sphere 2 (UNIONS c) /\ {p} IN c /\
     4 <= moi_sch3_crossings c a p /\
     j0 IN moi_sch3_level_polygons (UNIONS c) a (a dot p) /\
     x IN j0 /\ ~(x = p)
     ==> ?r. &0 < r /\
             UNIONS c INTER {y | a dot y = a dot p} INTER ball(x,r) SUBSET j0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `a:real^3`; `p:real^3`]
    MOI_STL_LEVEL_STRUCTURE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "cov")
    (LABEL_TAC "dis"))) THEN
  ABBREV_TAC `Q = UNIONS {q | q IN moi_sch3_level_polygons (UNIONS c) a (a dot p) /\
                              ~(q = j0:real^3->bool)}` THEN
  SUBGOAL_THEN `closed (Q:real^3->bool) /\ ~((x:real^3) IN Q)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "Q" THEN CONJ_TAC THENL
     [MATCH_MP_TAC CLOSED_UNIONS THEN CONJ_TAC THENL
       [MATCH_MP_TAC FINITE_SUBSET THEN
        EXISTS_TAC `moi_sch3_level_polygons (UNIONS c) a (a dot (p:real^3))` THEN
        ASM_REWRITE_TAC[] THEN SET_TAC[];
        REWRITE_TAC[IN_ELIM_THM; MOI_SLV_LEVEL_POLYGONS_EQ] THEN
        MESON_TAC[MOI_SLV_CIRCLE_CLOSED]];
      REWRITE_TAC[IN_UNIONS; IN_ELIM_THM; NOT_EXISTS_THM] THEN
      X_GEN_TAC `q:real^3->bool` THEN STRIP_TAC THEN
      USE_THEN "dis" (fun th -> MP_TAC(MATCH_MP th (CONJ
        (ASSUME `q IN moi_sch3_level_polygons (UNIONS c) a (a dot (p:real^3))`)
        (CONJ (ASSUME `j0 IN moi_sch3_level_polygons (UNIONS c) a (a dot (p:real^3))`)
              (ASSUME `~(q:real^3->bool = j0)`))))) THEN
      UNDISCH_TAC `~(x:real^3 = p)` THEN
      UNDISCH_TAC `(x:real^3) IN q` THEN UNDISCH_TAC `(x:real^3) IN j0` THEN
      SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `open((:real^3) DIFF Q)` MP_TAC THENL
   [ASM_REWRITE_TAC[GSYM closed]; ALL_TAC] THEN
  REWRITE_TAC[OPEN_CONTAINS_BALL] THEN
  DISCH_THEN(MP_TAC o SPEC `x:real^3`) THEN ASM_REWRITE_TAC[IN_DIFF; IN_UNIV] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `r:real` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[SUBSET; IN_INTER; IN_ELIM_THM] THEN
  X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
  USE_THEN "cov" (fun th -> MP_TAC(MATCH_MP th (CONJ
    (ASSUME `(z:real^3) IN UNIONS c`) (ASSUME `(a:real^3) dot z = a dot p`)))) THEN
  DISCH_THEN(X_CHOOSE_THEN `q:real^3->bool` STRIP_ASSUME_TAC) THEN
  ASM_CASES_TAC `q:real^3->bool = j0` THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(z:real^3) IN Q` MP_TAC THENL
   [EXPAND_TAC "Q" THEN REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
    EXISTS_TAC `q:real^3->bool` THEN ASM_REWRITE_TAC[];
    UNDISCH_TAC `ball(x:real^3,r) SUBSET (:real^3) DIFF Q` THEN
    UNDISCH_TAC `(z:real^3) IN ball(x,r)` THEN SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* 4. The side lemma: the two disks into which the boundary of the triangle *)
(* splits the image sphere lie locally on opposite sides of the level plane *)
(* at every boundary point other than f p.                                  *)
(* ------------------------------------------------------------------------- *)

let MOI_STL_SEGMENT_NEAR = prove
 (`!(z:real^N) w e. ~(w = z) /\ &0 < e ==> ?y. y IN segment(z,w) /\ dist(z,y) < e`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(z:real^N) IN closure(segment(z,w))` MP_TAC THENL
   [ASM_REWRITE_TAC[CLOSURE_SEGMENT; ENDS_IN_SEGMENT]; ALL_TAC] THEN
  REWRITE_TAC[CLOSURE_APPROACHABLE] THEN DISCH_THEN(MP_TAC o SPEC `e:real`) THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[DIST_SYM]);;

let MOI_STL_OPEN_SEGMENT_LEVEL = prove
 (`!(a:real^N) z w y.
     y IN segment(z,w) /\ a dot z < a dot w ==> a dot z < a dot y /\ a dot y < a dot w`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_SEGMENT] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[DOT_RADD; DOT_RMUL] THEN
  MP_TAC(SPECL [`u:real`; `(a:real^N) dot w - a dot z`] REAL_LT_MUL) THEN
  MP_TAC(SPECL [`&1 - u`; `(a:real^N) dot w - a dot z`] REAL_LT_MUL) THEN
  ASM_REAL_ARITH_TAC);;

let MOI_STL_TRANSVERSE_POINT = prove
 (`!c (a:real^3) p z.
     moi_sch3_generic c a /\ {p} IN c /\ z IN UNIONS c /\ a dot z = a dot p /\
     ~(z = p)
     ==> (?w. a dot p < a dot w /\ segment[z,w] SUBSET UNIONS c) /\
         (?w. a dot w < a dot p /\ segment[z,w] SUBSET UNIONS c)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `(z:real^3) IN UNIONS c` THEN REWRITE_TAC[IN_UNIONS] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real^3->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `simplicial_complex (c:(real^3->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[moi_sch3_generic]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `s:real^3->bool`]
    MOI_SLV_SC_SIMPLEX_VERTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `W:real^3->bool` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP AFFINE_INDEPENDENT_IMP_FINITE) THEN
  SUBGOAL_THEN `{w:real^3 | w IN W /\ a dot w = a dot p} SUBSET {p}`
    ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_SING] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC MOI_SLV_GENERIC_VERTEX THEN
    EXISTS_TAC `c:(real^3->bool)->bool` THEN EXISTS_TAC `a:real^3` THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(z:real^3) IN s INTER {x | a dot x = a dot p}` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!w:real^3. w IN W ==> segment[z,w] SUBSET UNIONS c`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `s:real^3->bool` THEN CONJ_TAC THENL
     [REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN
      MATCH_MP_TAC HULL_MINIMAL THEN
      REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET] THEN
      SUBGOAL_THEN `(w:real^3) IN s /\ convex(s:real^3->bool)` STRIP_ASSUME_TAC THENL
       [ASM_REWRITE_TAC[CONVEX_CONVEX_HULL] THEN ASM_MESON_TAC[HULL_SUBSET; SUBSET];
        ASM_REWRITE_TAC[]];
      UNDISCH_TAC `(s:real^3->bool) IN c` THEN SET_TAC[]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [ASM_CASES_TAC `?w:real^3. w IN W /\ a dot p < a dot w` THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`W:real^3->bool`; `a:real^3`; `a dot (p:real^3)`]
      MOI_SLV_HALF_SLICE_LE);
    ASM_CASES_TAC `?w:real^3. w IN W /\ a dot w < a dot p` THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`W:real^3->bool`; `a:real^3`; `a dot (p:real^3)`]
      MOI_SLV_HALF_SLICE)] THEN
  (ANTS_TAC THENL [ASM_MESON_TAC[REAL_NOT_LT]; ALL_TAC]) THEN
  DISCH_TAC THEN
  (SUBGOAL_THEN `(z:real^3) IN convex hull {p}` MP_TAC THENL
   [MATCH_MP_TAC(SET_RULE `!s t:real^3->bool. x IN s /\ s SUBSET t ==> x IN t`) THEN
    EXISTS_TAC `convex hull {w:real^3 | w IN W /\ a dot w = a dot p}` THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        is_eq(concl th) && is_comb(rhs(concl th)) &&
        can (find_term ((=) `W:real^3->bool`)) (rhs(concl th)))) THEN
      UNDISCH_TAC `(z:real^3) IN s INTER {x | a dot x = a dot p}` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC HULL_MONO THEN ASM_REWRITE_TAC[]];
    ASM_REWRITE_TAC[CONVEX_HULL_SING; IN_SING]]));;

let MOI_STL_DISK_BOUNDARY_NBHD = prove
 (`!(d:real^N->bool) j x r.
     pl_cell_with_boundary 2 d j /\ x IN j /\ &0 < r
     ==> ?u e. &0 < e /\ d INTER ball(x,e) SUBSET u /\ u SUBSET d INTER ball(x,r) /\
               connected (u DIFF j) /\
               (!e'. &0 < e' ==> ~((u DIFF j) INTER ball(x,e') = {}))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_cell_with_boundary] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN
    `ff:real^N->real^N` (X_CHOOSE_THEN `gg:real^N->real^N` STRIP_ASSUME_TAC)))
    STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [pl_homeomorphism]) THEN
  REWRITE_TAC[homeomorphism] THEN STRIP_TAC THEN
  SUBGOAL_THEN `closed(k:real^N->bool) /\ convex k` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[SIMPLEX_IMP_CLOSED; SIMPLEX_IMP_CONVEX]; ALL_TAC] THEN
  SUBGOAL_THEN `relative_frontier k SUBSET (k:real^N->bool)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[RELATIVE_FRONTIER_SUBSET]; ALL_TAC] THEN
  ABBREV_TAC `y0 = (gg:real^N->real^N) x` THEN
  SUBGOAL_THEN `(y0:real^N) IN relative_frontier k /\ (ff:real^N->real^N) y0 = x`
    STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(x:real^N) IN j` THEN ASM_REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC) THEN
    EXPAND_TAC "y0" THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(gg:real^N->real^N) (ff y) = y` (fun th -> ASM_REWRITE_TAC[th]) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y0:real^N) IN k` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o REWRITE_RULE[continuous_on] o check (fun th ->
    concl th = `(ff:real^N->real^N) continuous_on k`)) THEN
  DISCH_THEN(LABEL_TAC "Fc" o SPEC `y0:real^N`) THEN
  USE_THEN "Fc" (MP_TAC o SPEC `r:real` o REWRITE_RULE[ASSUME `(y0:real^N) IN k`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `del:real` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `(gg:real^N->real^N) continuous_on d` THEN
  REWRITE_TAC[continuous_on] THEN
  DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN
  SUBGOAL_THEN `(x:real^N) IN d` (fun th -> REWRITE_TAC[th]) THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `del:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `IMAGE (ff:real^N->real^N) (k INTER ball(y0,del))` THEN
  EXISTS_TAC `e:real` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `IMAGE (ff:real^N->real^N) (k INTER ball(y0,del)) DIFF
    IMAGE ff (relative_frontier k) =
    IMAGE ff (relative_interior k INTER ball(y0,del))` SUBST1_TAC THENL
   [
    SUBGOAL_THEN `relative_interior k = k DIFF relative_frontier (k:real^N->bool)`
      SUBST1_TAC THENL
     [REWRITE_TAC[relative_frontier] THEN ASM_SIMP_TAC[CLOSURE_CLOSED] THEN
      MP_TAC(ISPEC `k:real^N->bool` RELATIVE_INTERIOR_SUBSET) THEN SET_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `!x:real^N. x IN k ==> (gg:real^N->real^N) (ff x) = x` THEN
    UNDISCH_TAC `relative_frontier k SUBSET (k:real^N->bool)` THEN SET_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_INTER; IN_BALL; IN_IMAGE] THEN X_GEN_TAC `z:real^N` THEN
    STRIP_TAC THEN EXISTS_TAC `(gg:real^N->real^N) z` THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `IMAGE (gg:real^N->real^N) d = k` THEN
      UNDISCH_TAC `(z:real^N) IN d` THEN SET_TAC[];
      ALL_TAC] THEN
    ONCE_REWRITE_TAC[DIST_SYM] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTER; IN_BALL] THEN
    X_GEN_TAC `z:real^N` THEN STRIP_TAC THEN CONJ_TAC THENL
     [UNDISCH_TAC `IMAGE (ff:real^N->real^N) k = d` THEN
      UNDISCH_TAC `(z:real^N) IN k` THEN SET_TAC[];
      ALL_TAC] THEN
    ONCE_REWRITE_TAC[DIST_SYM] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `k:real^N->bool` THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPEC `k:real^N->bool` RELATIVE_INTERIOR_SUBSET) THEN SET_TAC[];
      MATCH_MP_TAC CONVEX_CONNECTED THEN
      ASM_SIMP_TAC[CONVEX_INTER; CONVEX_RELATIVE_INTERIOR; CONVEX_BALL]];
    X_GEN_TAC `e':real` THEN DISCH_TAC THEN
    USE_THEN "Fc" (MP_TAC o SPEC `e':real` o REWRITE_RULE[ASSUME `(y0:real^N) IN k`]) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `del':real` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(y0:real^N) IN closure(relative_interior k)` MP_TAC THENL
     [ASM_SIMP_TAC[CONVEX_CLOSURE_RELATIVE_INTERIOR; CLOSURE_CLOSED]; ALL_TAC] THEN
    REWRITE_TAC[CLOSURE_APPROACHABLE] THEN
    DISCH_THEN(MP_TAC o SPEC `min del del':real`) THEN
    ASM_REWRITE_TAC[REAL_LT_MIN] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC) THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_IMAGE; IN_BALL] THEN
    EXISTS_TAC `(ff:real^N->real^N) y` THEN CONJ_TAC THENL
     [EXISTS_TAC `y:real^N` THEN ASM_REWRITE_TAC[] THEN
      ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REWRITE_TAC[];
      ONCE_REWRITE_TAC[DIST_SYM] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPEC `k:real^N->bool` RELATIVE_INTERIOR_SUBSET) THEN
      UNDISCH_TAC `(y:real^N) IN relative_interior k` THEN SET_TAC[]]]);;

let MOI_STL_IMAGE_LEVEL_NEAR = prove
 (`!s j0 (a:real^3) h (f:real^3->real^3) g x r0.
     pl_homeomorphism ((:real^3),(:real^3)) (f,g) /\ (!x. a dot f x = a dot x) /\
     &0 < r0 /\ s INTER {y | a dot y = h} INTER ball(g x,r0) SUBSET j0
     ==> ?r. &0 < r /\
             IMAGE f s INTER {y | a dot y = h} INTER ball(x,r) SUBSET IMAGE f j0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [pl_homeomorphism]) THEN
  REWRITE_TAC[homeomorphism; IN_UNIV] THEN STRIP_TAC THEN
  UNDISCH_TAC `(g:real^3->real^3) continuous_on (:real^3)` THEN
  REWRITE_TAC[continuous_on; IN_UNIV] THEN
  DISCH_THEN(MP_TAC o SPECL [`x:real^3`; `r0:real`]) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `r:real` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[SUBSET; IN_INTER; IN_ELIM_THM; IN_IMAGE; IN_BALL] THEN
  X_GEN_TAC `y:real^3` THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC)
    STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `z:real^3` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(g:real^3->real^3) y = z` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `s INTER {y:real^3 | a dot y = h} INTER ball((g:real^3->real^3) x,r0)
                SUBSET j0` THEN
  REWRITE_TAC[SUBSET; IN_INTER; IN_ELIM_THM; IN_BALL] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  ONCE_REWRITE_TAC[DIST_SYM] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
    concl th = `(g:real^3->real^3) y = z`)) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ONCE_REWRITE_TAC[DIST_SYM] THEN
  ASM_REWRITE_TAC[]);;

let MOI_STL_LOCAL_SIDE = prove
 (`!d j (a:real^3) h x r.
     pl_cell_with_boundary 2 d j /\ x IN j /\ &0 < r /\
     j SUBSET {y | a dot y = h} /\
     d INTER {y | a dot y = h} INTER ball(x,r) SUBSET j
     ==> ((?e. &0 < e /\ !y. y IN d /\ dist(x,y) < e ==> h <= a dot y) \/
          (?e. &0 < e /\ !y. y IN d /\ dist(x,y) < e ==> a dot y <= h)) /\
         ~((?e. &0 < e /\ !y. y IN d /\ dist(x,y) < e ==> h <= a dot y) /\
           (?e. &0 < e /\ !y. y IN d /\ dist(x,y) < e ==> a dot y <= h))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`d:real^3->bool`; `j:real^3->bool`; `x:real^3`; `r:real`]
    MOI_STL_DISK_BOUNDARY_NBHD) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^3->bool` (X_CHOOSE_THEN `e:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "acc"))))))) THEN
  SUBGOAL_THEN `!y:real^3. y IN u DIFF j ==> ~(a dot y = h)` (LABEL_TAC "off") THENL
   [X_GEN_TAC `y:real^3` THEN REWRITE_TAC[IN_DIFF] THEN STRIP_TAC THEN
    DISCH_TAC THEN UNDISCH_TAC `~((y:real^3) IN j)` THEN REWRITE_TAC[] THEN
    UNDISCH_TAC `d INTER {y:real^3 | a dot y = h} INTER ball(x,r) SUBSET j` THEN
    UNDISCH_TAC `u SUBSET d INTER ball(x:real^3,r)` THEN
    UNDISCH_TAC `(y:real^3) IN u` THEN UNDISCH_TAC `(a:real^3) dot y = h` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(!y:real^3. y IN u DIFF j ==> h < a dot y) \/
                (!y:real^3. y IN u DIFF j ==> a dot y < h)` ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p /\ ~q ==> F) ==> p \/ q`) THEN
    REWRITE_TAC[NOT_FORALL_THM; NOT_IMP; REAL_NOT_LT] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `y1:real^3` STRIP_ASSUME_TAC)
      (X_CHOOSE_THEN `y2:real^3` STRIP_ASSUME_TAC)) THEN
    MP_TAC(ISPECL [`u DIFF j:real^3->bool`; `y1:real^3`; `y2:real^3`; `a:real^3`;
                   `h:real`] CONNECTED_IVT_HYPERPLANE) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^3. y IN j ==> a dot y = h` ASSUME_TAC THENL
   [UNDISCH_TAC `j SUBSET {y:real^3 | a dot y = h}` THEN SET_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM DISJ_CASES_TAC THENL [DISJ1_TAC; DISJ2_TAC] THEN
    (EXISTS_TAC `e:real` THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(y:real^3) IN u` ASSUME_TAC THENL
     [UNDISCH_TAC `d INTER ball(x:real^3,e) SUBSET u` THEN
      REWRITE_TAC[SUBSET; IN_INTER; IN_BALL] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    (ASM_CASES_TAC `(y:real^3) IN j` THENL
     [ASM_SIMP_TAC[REAL_LE_REFL];
      FIRST_X_ASSUM(MP_TAC o SPEC `y:real^3` o check (is_forall o concl)) THEN
      ASM_REWRITE_TAC[IN_DIFF] THEN REAL_ARITH_TAC]));
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `e1:real` STRIP_ASSUME_TAC)
      (X_CHOOSE_THEN `e2:real` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `&0 < min e (min e1 e2)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[REAL_LT_MIN]; ALL_TAC] THEN
    USE_THEN "acc" (fun th -> MP_TAC(REWRITE_RULE
      [GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_BALL; REAL_LT_MIN]
      (MATCH_MP th (ASSUME `&0 < min e (min e1 e2)`)))) THEN
    DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
    USE_THEN "off" (fun th -> MP_TAC(MATCH_MP th
      (ASSUME `(y:real^3) IN u DIFF j`))) THEN
    SUBGOAL_THEN `(y:real^3) IN d` ASSUME_TAC THENL
     [UNDISCH_TAC `u SUBSET d INTER ball(x:real^3,r)` THEN
      UNDISCH_TAC `(y:real^3) IN u DIFF j` THEN SET_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `h <= x /\ x <= h ==> x = h`) THEN
    ASM_MESON_TAC[]]);;

let MOI_STL_IMAGE_NEAR_SIDE = prove
 (`!s (f:real^3->real^3) g (a:real^3) z w h e.
     pl_homeomorphism ((:real^3),(:real^3)) (f,g) /\ (!x. a dot f x = a dot x) /\
     segment[z,w] SUBSET s /\ a dot z = h /\ h < a dot w /\ &0 < e
     ==> ?y. y IN IMAGE f s /\ dist(f z,y) < e /\ h < a dot y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [pl_homeomorphism]) THEN
  REWRITE_TAC[homeomorphism; IN_UNIV] THEN STRIP_TAC THEN
  UNDISCH_TAC `(f:real^3->real^3) continuous_on (:real^3)` THEN
  REWRITE_TAC[continuous_on; IN_UNIV] THEN
  DISCH_THEN(MP_TAC o SPECL [`z:real^3`; `e:real`]) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `del:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`z:real^3`; `w:real^3`; `del:real`] MOI_STL_SEGMENT_NEAR) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `(f:real^3->real^3) y` THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC FUN_IN_IMAGE THEN
    ASM_MESON_TAC[SEGMENT_OPEN_SUBSET_CLOSED; SUBSET];
    ONCE_REWRITE_TAC[DIST_SYM] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`a:real^3`; `z:real^3`; `w:real^3`; `y:real^3`]
      MOI_STL_OPEN_SEGMENT_LEVEL) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]);;

let MOI_STL_NOT_BOTH_UP = prove
 (`!d1 d2 s (a:real^3) h x.
     d1 UNION d2 = s /\
     (!e. &0 < e ==> ?y. y IN s /\ dist(x,y) < e /\ a dot y < h)
     ==> ~((?e. &0 < e /\ !y. y IN d1 /\ dist(x,y) < e ==> h <= a dot y) /\
           (?e. &0 < e /\ !y. y IN d2 /\ dist(x,y) < e ==> h <= a dot y))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "app")) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `e1:real` (CONJUNCTS_THEN2
    ASSUME_TAC (LABEL_TAC "u1"))) (X_CHOOSE_THEN `e2:real` (CONJUNCTS_THEN2
    ASSUME_TAC (LABEL_TAC "u2")))) THEN
  REMOVE_THEN "app" (MP_TAC o SPEC `min e1 e2:real`) THEN
  ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(y:real^3) IN d1 \/ y IN d2` DISJ_CASES_TAC THENL
   [ASM SET_TAC[];
    REMOVE_THEN "u1" (MP_TAC o SPEC `y:real^3`) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    REMOVE_THEN "u2" (MP_TAC o SPEC `y:real^3`) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

let MOI_STL_SIDE_POINT = prove
 (`!c (a:real^3) p j0 (f:real^3->real^3) g d1 d2 x.
     moi_sch3_generic c a /\ pl_sphere 2 (UNIONS c) /\ {p} IN c /\
     4 <= moi_sch3_crossings c a p /\
     j0 IN moi_sch3_level_polygons (UNIONS c) a (a dot p) /\
     pl_homeomorphism ((:real^3),(:real^3)) (f,g) /\ (!x. a dot f x = a dot x) /\
     pl_cell_with_boundary 2 d1 (IMAGE f j0) /\
     pl_cell_with_boundary 2 d2 (IMAGE f j0) /\
     d1 UNION d2 = IMAGE f (UNIONS c) /\
     x IN IMAGE f j0 /\ ~(x = f p)
     ==> (((?e. &0 < e /\ !y. y IN d1 /\ dist(x,y) < e ==> a dot p <= a dot y) /\
           (?e. &0 < e /\ !y. y IN d2 /\ dist(x,y) < e ==> a dot y <= a dot p)) \/
          ((?e. &0 < e /\ !y. y IN d1 /\ dist(x,y) < e ==> a dot y <= a dot p) /\
           (?e. &0 < e /\ !y. y IN d2 /\ dist(x,y) < e ==> a dot p <= a dot y))) /\
         ~((?e. &0 < e /\ !y. y IN d1 /\ dist(x,y) < e ==> a dot p <= a dot y) /\
           (?e. &0 < e /\ !y. y IN d1 /\ dist(x,y) < e ==> a dot y <= a dot p))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [pl_homeomorphism]) THEN
  REWRITE_TAC[homeomorphism; IN_UNIV] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(g:real^3->real^3) x IN j0 /\ ~(g x = p)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(x:real^3) IN IMAGE (f:real^3->real^3) j0` THEN REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `j0 SUBSET UNIONS c INTER {y:real^3 | a dot y = a dot p}`
    ASSUME_TAC THENL
   [UNDISCH_TAC `j0 IN moi_sch3_level_polygons (UNIONS c) a (a dot (p:real^3))` THEN
    SIMP_TAC[MOI_SLV_LEVEL_POLYGONS_EQ; IN_ELIM_THM];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `a:real^3`; `p:real^3`; `j0:real^3->bool`;
                 `(g:real^3->real^3) x`] MOI_STL_LEVEL_NEAR_POLYGON) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r0:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`UNIONS c:real^3->bool`; `j0:real^3->bool`; `a:real^3`;
                 `a dot (p:real^3)`; `f:real^3->real^3`; `g:real^3->real^3`;
                 `x:real^3`; `r0:real`] MOI_STL_IMAGE_LEVEL_NEAR) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `IMAGE (f:real^3->real^3) j0 SUBSET {y | a dot y = a dot p}`
    ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `j0 SUBSET UNIONS c INTER {y:real^3 | a dot y = a dot p}` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!d. d SUBSET IMAGE (f:real^3->real^3) (UNIONS c) /\
        pl_cell_with_boundary 2 d (IMAGE f j0)
        ==> ((?e. &0 < e /\ !y. y IN d /\ dist(x,y) < e ==> a dot p <= a dot y) \/
             (?e. &0 < e /\ !y. y IN d /\ dist(x,y) < e ==> a dot y <= a dot p)) /\
            ~((?e. &0 < e /\ !y. y IN d /\ dist(x,y) < e ==> a dot p <= a dot y) /\
              (?e. &0 < e /\ !y. y IN d /\ dist(x,y) < e ==> a dot y <= a dot p))`
  (LABEL_TAC "loc") THENL
   [GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC MOI_STL_LOCAL_SIDE THEN
    EXISTS_TAC `IMAGE (f:real^3->real^3) j0` THEN EXISTS_TAC `r:real` THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `IMAGE (f:real^3->real^3) (UNIONS c) INTER {y | a dot y = a dot p}
                 INTER ball(x,r) SUBSET IMAGE f j0` THEN
    UNDISCH_TAC `d SUBSET IMAGE (f:real^3->real^3) (UNIONS c)` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `d1 SUBSET IMAGE (f:real^3->real^3) (UNIONS c) /\
                d2 SUBSET IMAGE (f:real^3->real^3) (UNIONS c)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `d1 UNION d2 = IMAGE (f:real^3->real^3) (UNIONS c)` THEN SET_TAC[];
    ALL_TAC] THEN
  USE_THEN "loc" (fun th -> MP_TAC(MATCH_MP th (CONJ
    (ASSUME `d1 SUBSET IMAGE (f:real^3->real^3) (UNIONS c)`)
    (ASSUME `pl_cell_with_boundary 2 d1 (IMAGE (f:real^3->real^3) j0)`)))) THEN
  USE_THEN "loc" (fun th -> MP_TAC(MATCH_MP th (CONJ
    (ASSUME `d2 SUBSET IMAGE (f:real^3->real^3) (UNIONS c)`)
    (ASSUME `pl_cell_with_boundary 2 d2 (IMAGE (f:real^3->real^3) j0)`)))) THEN
  SUBGOAL_THEN
   `!e. &0 < e ==> (?y. y IN IMAGE (f:real^3->real^3) (UNIONS c) /\ dist(x,y) < e /\
                        a dot p < a dot y) /\
                   (?y. y IN IMAGE (f:real^3->real^3) (UNIONS c) /\ dist(x,y) < e /\
                        a dot y < a dot p)`
  ASSUME_TAC THENL
   [X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `a:real^3`; `p:real^3`;
                   `(g:real^3->real^3) x`] MOI_STL_TRANSVERSE_POINT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `j0 SUBSET UNIONS c INTER {y:real^3 | a dot y = a dot p}` THEN
      UNDISCH_TAC `(g:real^3->real^3) x IN j0` THEN SET_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `w1:real^3` STRIP_ASSUME_TAC)
      (X_CHOOSE_THEN `w2:real^3` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `(a:real^3) dot ((g:real^3->real^3) x) = a dot p` ASSUME_TAC THENL
     [UNDISCH_TAC `j0 SUBSET UNIONS c INTER {y:real^3 | a dot y = a dot p}` THEN
      UNDISCH_TAC `(g:real^3->real^3) x IN j0` THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(f:real^3->real^3) ((g:real^3->real^3) x) = x` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`UNIONS c:real^3->bool`; `f:real^3->real^3`; `g:real^3->real^3`;
                     `a:real^3`; `(g:real^3->real^3) x`; `w1:real^3`;
                     `a dot (p:real^3)`; `e:real`] MOI_STL_IMAGE_NEAR_SIDE) THEN
      ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`UNIONS c:real^3->bool`; `f:real^3->real^3`; `g:real^3->real^3`;
                     `--a:real^3`; `(g:real^3->real^3) x`; `w2:real^3`;
                     `--(a dot (p:real^3))`; `e:real`] MOI_STL_IMAGE_NEAR_SIDE) THEN
      ASM_REWRITE_TAC[DOT_LNEG; REAL_EQ_NEG2; REAL_LT_NEG2]];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "s2") ASSUME_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "s1") ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`d1:real^3->bool`; `d2:real^3->bool`;
                 `IMAGE (f:real^3->real^3) (UNIONS c)`; `a:real^3`;
                 `a dot (p:real^3)`; `x:real^3`] MOI_STL_NOT_BOTH_UP) THEN
  MP_TAC(ISPECL [`d1:real^3->bool`; `d2:real^3->bool`;
                 `IMAGE (f:real^3->real^3) (UNIONS c)`; `--a:real^3`;
                 `--(a dot (p:real^3))`; `x:real^3`] MOI_STL_NOT_BOTH_UP) THEN
  ASM_REWRITE_TAC[DOT_LNEG; REAL_LE_NEG2; REAL_LT_NEG2] THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN DISCH_TAC THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN DISCH_TAC THEN
  REMOVE_THEN "s1" MP_TAC THEN REMOVE_THEN "s2" MP_TAC THEN
  POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN CONV_TAC TAUT);;

let MOI_STL_CONSTANT_ALTERNATIVE = prove
 (`!J (P:real^N->bool) Q.
     connected J /\
     (!x. x IN J ==> (P x \/ Q x) /\ ~(P x /\ Q x)) /\
     (!x. x IN J /\ P x ==> ?e. &0 < e /\ !x'. x' IN J /\ dist(x,x') < e ==> P x') /\
     (!x. x IN J /\ Q x ==> ?e. &0 < e /\ !x'. x' IN J /\ dist(x,x') < e ==> Q x')
     ==> (!x. x IN J ==> P x) \/ (!x. x IN J ==> Q x)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[CONNECTED_OPEN_IN] THEN
  MATCH_MP_TAC(TAUT `(~r ==> p) ==> ~p ==> r`) THEN DISCH_TAC THEN
  MAP_EVERY EXISTS_TAC [`{x:real^N | x IN J /\ P x}`; `{x:real^N | x IN J /\ Q x}`] THEN
  REWRITE_TAC[OPEN_IN_CONTAINS_BALL; SUBSET; IN_ELIM_THM; IN_INTER; IN_BALL;
              IN_UNION; EXTENSION; NOT_IN_EMPTY] THEN
  REPEAT CONJ_TAC THENL
   [SIMP_TAC[];
    X_GEN_TAC `x:real^N` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N` o check (fun th ->
      can (find_term ((=) `P:real^N->bool`)) (concl th) &&
      not (can (find_term ((=) `Q:real^N->bool`)) (concl th)) &&
      is_forall (concl th))) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN MESON_TAC[];
    SIMP_TAC[];
    X_GEN_TAC `x:real^N` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N` o check (fun th ->
      can (find_term ((=) `Q:real^N->bool`)) (concl th) &&
      not (can (find_term ((=) `P:real^N->bool`)) (concl th)) &&
      is_forall (concl th))) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN MESON_TAC[];
    ASM_MESON_TAC[];
    ASM_MESON_TAC[];
    ASM_MESON_TAC[];
    ASM_MESON_TAC[]]);;

let MOI_STL_SIDES = prove
 (`!c (a:real^3) p j0 (f:real^3->real^3) g d1 d2.
     moi_sch3_generic c a /\ pl_sphere 2 (UNIONS c) /\ {p} IN c /\
     4 <= moi_sch3_crossings c a p /\
     j0 IN moi_sch3_level_polygons (UNIONS c) a (a dot p) /\
     pl_homeomorphism ((:real^3),(:real^3)) (f,g) /\ (!x. a dot f x = a dot x) /\
     pl_cell_with_boundary 2 d1 (IMAGE f j0) /\
     pl_cell_with_boundary 2 d2 (IMAGE f j0) /\
     d1 UNION d2 = IMAGE f (UNIONS c)
     ==> ?sigma. (sigma = &1 \/ sigma = -- &1) /\
                 (!x. x IN IMAGE f j0 /\ ~(x = f p)
                      ==> ?r. &0 < r /\
                              !y. y IN d1 /\ dist(x,y) < r
                                  ==> &0 <= sigma * (a dot y - a dot p)) /\
                 (!x. x IN IMAGE f j0 /\ ~(x = f p)
                      ==> ?r. &0 < r /\
                              !y. y IN d2 /\ dist(x,y) < r
                                  ==> &0 <= --sigma * (a dot y - a dot p))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `a:real^3`; `p:real^3`; `j0:real^3->bool`;
                 `f:real^3->real^3`; `g:real^3->real^3`; `d1:real^3->bool`;
                 `d2:real^3->bool`] MOI_STL_SIDE_POINT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "pt") THEN
  MP_TAC(ISPECL [`IMAGE (f:real^3->real^3) j0 DELETE f p`;
    `\x:real^3. ?e. &0 < e /\ !y. y IN d1 /\ dist(x,y) < e ==> a dot p <= a dot y`;
    `\x:real^3. ?e. &0 < e /\ !y. y IN d1 /\ dist(x,y) < e ==> a dot y <= a dot p`]
    MOI_STL_CONSTANT_ALTERNATIVE) THEN
  REWRITE_TAC[IN_DELETE] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MOI_SLV_CIRCLE_DELETE_ANY THEN
      ASM_MESON_TAC[MOI_SCX_CELL_SPHERE];
      X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
      USE_THEN "pt" (fun th -> MP_TAC(MATCH_MP th
        (CONJ (ASSUME `(x:real^3) IN IMAGE (f:real^3->real^3) j0`)
              (ASSUME `~((x:real^3) = (f:real^3->real^3) p)`)))) THEN
      CONV_TAC TAUT;
      ALL_TAC; ALL_TAC] THEN
    X_GEN_TAC `x:real^3` THEN
    DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC
      (X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC)) THEN
    EXISTS_TAC `e / &2` THEN ASM_REWRITE_TAC[REAL_HALF] THEN
    X_GEN_TAC `x':real^3` THEN STRIP_TAC THEN EXISTS_TAC `e / &2` THEN
    ASM_REWRITE_TAC[REAL_HALF] THEN X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `dist(x:real^3,x') < e / &2` THEN
    UNDISCH_TAC `dist(x':real^3,y) < e / &2` THEN NORM_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN DISJ_CASES_TAC THENL
   [EXISTS_TAC `&1`; EXISTS_TAC `-- &1`] THEN
  REWRITE_TAC[REAL_MUL_LID; REAL_MUL_LNEG; REAL_NEG_NEG; REAL_SUB_LE] THEN
  REWRITE_TAC[REAL_ARITH `&0 <= --(x - y) <=> x <= y`] THEN
  CONJ_TAC THEN X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
  USE_THEN "pt" (fun th -> MP_TAC(MATCH_MP th
    (CONJ (ASSUME `(x:real^3) IN IMAGE (f:real^3->real^3) j0`)
          (ASSUME `~((x:real^3) = (f:real^3->real^3) p)`)))) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:real^3` o check (is_forall o concl)) THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* 5. Links: points of the link of u see u along segments of the complex,  *)
(* no two link points lie on one ray from u, and the crossing number for a  *)
(* height b is at most the number of level points of the link for a height *)
(* a with the same signs, provided every link vertex at the level of u has *)
(* its link neighbours on opposite sides.                                   *)
(* ------------------------------------------------------------------------- *)

let MOI_STL_LINK_POINT = prove
 (`!K (u:real^N) x.
     simplicial_complex K /\ x IN UNIONS (simplicial_link K u)
     ==> ~(x = u) /\ ?t. t IN K /\ u IN t /\ x IN t`,
  REWRITE_TAC[simplicial_link; IN_UNIONS; IN_ELIM_THM] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC)) THEN
  CONJ_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  EXISTS_TAC `t':real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `(s:real^N->bool) face_of t'` THEN
  DISCH_THEN(MP_TAC o MATCH_MP FACE_OF_IMP_SUBSET) THEN ASM SET_TAC[]);;

let MOI_STL_LINK_RAY = prove
 (`!K (u:real^N) z z'.
     simplicial_complex K /\ z IN UNIONS (simplicial_link K u) /\
     z' IN UNIONS (simplicial_link K u) /\ z' IN segment(u,z)
     ==> F`,
  REWRITE_TAC[simplicial_link; IN_UNIONS; IN_ELIM_THM] THEN
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `s:real^N->bool` (CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `t:real^N->bool`
        STRIP_ASSUME_TAC))) ASSUME_TAC))
    (CONJUNCTS_THEN2 (X_CHOOSE_THEN `s':real^N->bool` (CONJUNCTS_THEN2
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
        (X_CHOOSE_THEN `t':real^N->bool` STRIP_ASSUME_TAC))) ASSUME_TAC))
      ASSUME_TAC))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SLV_SC_BASIC) THEN
  SUBGOAL_THEN `(t INTER s':real^N->bool) face_of t` MP_TAC THENL
   [ASM_MESON_TAC[MOI_SLV_SC_INTER]; ALL_TAC] THEN
  REWRITE_TAC[face_of] THEN
  DISCH_THEN(MP_TAC o SPECL [`u:real^N`; `z:real^N`; `z':real^N`] o
    CONJUNCT2 o CONJUNCT2) THEN
  SUBGOAL_THEN `(z:real^N) IN t /\ (z':real^N) IN s'` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[FACE_OF_IMP_SUBSET; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `(z':real^N) IN t` ASSUME_TAC THENL
   [SUBGOAL_THEN `convex(t:real^N->bool)` MP_TAC THENL
     [ASM_MESON_TAC[MOI_PTR_SIMPLICIAL_COMPLEX_POLYTOPE; POLYTOPE_IMP_CONVEX];
      ALL_TAC] THEN
    REWRITE_TAC[CONVEX_CONTAINS_SEGMENT] THEN
    DISCH_THEN(MP_TAC o SPECL [`u:real^N`; `z:real^N`]) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`u:real^N`; `z:real^N`] SEGMENT_OPEN_SUBSET_CLOSED) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[IN_INTER] THEN ASM_MESON_TAC[]);;

let MOI_STL_LINK_FACE_CLOSED = prove
 (`!c (u:real^N) s r.
     simplicial_complex c /\ s IN simplicial_link c u /\ r face_of s /\ ~(r = {})
     ==> r IN simplicial_link c u`,
  REWRITE_TAC[simplicial_link; IN_ELIM_THM] THEN REPEAT STRIP_TAC THENL
   [ASM_MESON_TAC[simplicial_complex];
    ASM_MESON_TAC[FACE_OF_IMP_SUBSET; SUBSET];
    EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[FACE_OF_TRANS]]);;

let MOI_STL_EDGES_SHARE = prove
 (`!c (e:real^N->bool) e' z.
     simplicial_complex c /\ e IN c /\ e' IN c /\
     aff_dim e = &1 /\ aff_dim e' = &1 /\
     z IN relative_interior e /\ z IN e'
     ==> e = e'`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `e:real^N->bool`; `e':real^N->bool`]
    MOI_SLV_SC_INTER) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(e:real^N->bool) SUBSET e INTER e'` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_OF_FACE_OF THEN EXISTS_TAC `e:real^N->bool` THEN
    ASM_REWRITE_TAC[SUBSET_REFL; DISJOINT; GSYM MEMBER_NOT_EMPTY] THEN
    EXISTS_TAC `z:real^N` THEN ASM_REWRITE_TAC[IN_INTER] THEN
    ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN `e INTER e':real^N->bool = e` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `e:real^N->bool = e'` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`e:real^N->bool`; `e':real^N->bool`] FACE_OF_AFF_DIM_LT) THEN
  ANTS_TAC THENL
   [ASM_MESON_TAC[MOI_PTR_SIMPLICIAL_COMPLEX_POLYTOPE; POLYTOPE_IMP_CONVEX];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN INT_ARITH_TAC);;

let MOI_STL_CROSSINGS_LE = prove
 (`!c (a:real^3) b u.
     simplicial_complex c /\ {u} IN c /\
     FINITE (UNIONS (simplicial_link c u) INTER {x | a dot x = a dot u}) /\
     (!x. {x} IN simplicial_link c u
          ==> ~(b dot x = b dot u) /\
              (a dot x < a dot u ==> b dot x < b dot u) /\
              (a dot u < a dot x ==> b dot u < b dot x)) /\
     (!x y1 y2. segment[x,y1] IN simplicial_link c u /\
                segment[x,y2] IN simplicial_link c u /\
                a dot x = a dot u /\ ~(y1 = x) /\ ~(y2 = x) /\ ~(y1 = y2)
                ==> (a dot y1 < a dot u <=> a dot u < a dot y2))
     ==> moi_sch3_crossings c b u <=
         CARD (UNIONS (simplicial_link c u) INTER {x | a dot x = a dot u})`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "sg")
    (LABEL_TAC "tr"))))) THEN
  REWRITE_TAC[moi_sch3_crossings] THEN
  ABBREV_TAC `E = {e | e IN simplicial_link c u /\
                       ?x y:real^3. e = segment[x,y] /\ b dot x < b dot u /\
                                    b dot u < b dot y}` THEN
  ABBREV_TAC `Z = UNIONS (simplicial_link c u) INTER {x:real^3 | a dot x = a dot u}` THEN
  SUBGOAL_THEN `FINITE (E:(real^3->bool)->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `c:(real^3->bool)->bool` THEN
    CONJ_TAC THENL [ASM_MESON_TAC[simplicial_complex]; ALL_TAC] THEN
    EXPAND_TAC "E" THEN REWRITE_TAC[SUBSET; IN_ELIM_THM; simplicial_link] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!e. e IN E ==> ?x y:real^3. e = segment[x,y] /\ ~(x = y) /\
                                {x} IN simplicial_link c u /\
                                {y} IN simplicial_link c u /\
                                b dot x < b dot u /\ b dot u < b dot y /\
                                a dot x <= a dot u /\ a dot u <= a dot y /\
                                e IN simplicial_link c u`
  (LABEL_TAC "ends") THENL
   [X_GEN_TAC `e:real^3->bool` THEN EXPAND_TAC "E" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `x:real^3`
      (X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC))) THEN
    MAP_EVERY EXISTS_TAC [`x:real^3`; `y:real^3`] THEN
    SUBGOAL_THEN `~(x:real^3 = y)` ASSUME_TAC THENL
     [DISCH_THEN SUBST_ALL_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `{x:real^3} IN simplicial_link c u /\ {y:real^3} IN simplicial_link c u`
      STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC MOI_STL_LINK_FACE_CLOSED THEN
      EXISTS_TAC `e:real^3->bool` THEN ASM_REWRITE_TAC[NOT_INSERT_EMPTY] THEN
      ASM_REWRITE_TAC[FACE_OF_SING; EXTREME_POINT_OF_SEGMENT];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    USE_THEN "sg" (MP_TAC o SPEC `x:real^3`) THEN
    USE_THEN "sg" (MP_TAC o SPEC `y:real^3`) THEN
    REWRITE_TAC[ASSUME `{x:real^3} IN simplicial_link c u`;
                ASSUME `{y:real^3} IN simplicial_link c u`] THEN
    UNDISCH_TAC `(b:real^3) dot x < b dot u` THEN
    UNDISCH_TAC `(b:real^3) dot u < b dot y` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!e. e IN E ==> ?z:real^3. z IN e /\ z IN Z` (LABEL_TAC "pt") THENL
   [X_GEN_TAC `e:real^3->bool` THEN DISCH_TAC THEN
    USE_THEN "ends" (fun th -> MP_TAC(MATCH_MP th
      (ASSUME `(e:real^3->bool) IN E`))) THEN
    DISCH_THEN(X_CHOOSE_THEN `x:real^3` (X_CHOOSE_THEN `y:real^3`
      STRIP_ASSUME_TAC)) THEN
    MP_TAC(ISPECL [`segment[x:real^3,y]`; `x:real^3`; `y:real^3`; `a:real^3`;
                   `a dot (u:real^3)`] CONNECTED_IVT_HYPERPLANE) THEN
    ASM_REWRITE_TAC[CONNECTED_SEGMENT; ENDS_IN_SEGMENT] THEN
    DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `z:real^3` THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "Z" THEN REWRITE_TAC[IN_INTER; IN_UNIONS; IN_ELIM_THM] THEN
    ASM_REWRITE_TAC[] THEN EXISTS_TAC `segment[x:real^3,y]` THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!e e' z:real^3. e IN E /\ e' IN E /\ z IN e /\ z IN e' /\ z IN Z ==> e = e'`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    USE_THEN "ends" (fun th -> MP_TAC(MATCH_MP th
      (ASSUME `(e:real^3->bool) IN E`))) THEN
    DISCH_THEN(X_CHOOSE_THEN `x:real^3` (X_CHOOSE_THEN `y:real^3`
      STRIP_ASSUME_TAC)) THEN
    USE_THEN "ends" (fun th -> MP_TAC(MATCH_MP th
      (ASSUME `(e':real^3->bool) IN E`))) THEN
    DISCH_THEN(X_CHOOSE_THEN `x':real^3` (X_CHOOSE_THEN `y':real^3`
      STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `(e:real^3->bool) IN c /\ (e':real^3->bool) IN c /\
                  aff_dim e = &1 /\ aff_dim e' = &1` STRIP_ASSUME_TAC THENL
     [ASM_REWRITE_TAC[AFF_DIM_SEGMENT] THEN
      UNDISCH_TAC `(e:real^3->bool) IN simplicial_link c u` THEN
      UNDISCH_TAC `(e':real^3->bool) IN simplicial_link c u` THEN
      REWRITE_TAC[simplicial_link; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
      SIMP_TAC[];
      ALL_TAC] THEN
    ASM_CASES_TAC `(z:real^3) IN relative_interior e` THENL
     [MATCH_MP_TAC MOI_STL_EDGES_SHARE THEN
      MAP_EVERY EXISTS_TAC [`c:(real^3->bool)->bool`; `z:real^3`] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_CASES_TAC `(z:real^3) IN relative_interior e'` THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOI_STL_EDGES_SHARE THEN
      MAP_EVERY EXISTS_TAC [`c:(real^3->bool)->bool`; `z:real^3`] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `!f1 x1 y1:real^3. f1 IN E /\ f1 = segment[x1,y1] /\ ~(x1 = y1) /\
                     {x1} IN simplicial_link c u /\ {y1} IN simplicial_link c u /\
                     b dot x1 < b dot u /\ b dot u < b dot y1 /\
                     z IN f1 /\ ~(z IN relative_interior f1)
                     ==> ?w. f1 = segment[z,w] /\ ~(w = z) /\
                             {w} IN simplicial_link c u /\
                             (b dot z < b dot u <=> b dot u < b dot w)`
    ASSUME_TAC THENL
     [MAP_EVERY X_GEN_TAC [`f1:real^3->bool`; `x1:real^3`; `y1:real^3`] THEN
      STRIP_TAC THEN
      SUBGOAL_THEN `(z:real^3) = x1 \/ z = y1` DISJ_CASES_TAC THENL
       [UNDISCH_TAC `~((z:real^3) IN relative_interior f1)` THEN
        UNDISCH_TAC `(z:real^3) IN f1` THEN
        ASM_REWRITE_TAC[RELATIVE_INTERIOR_SEGMENT] THEN
        REWRITE_TAC[open_segment; IN_DIFF; IN_INSERT; NOT_IN_EMPTY] THEN
        MESON_TAC[];
        FIRST_X_ASSUM SUBST_ALL_TAC THEN
        EXISTS_TAC `y1:real^3` THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
        FIRST_X_ASSUM SUBST_ALL_TAC THEN
        EXISTS_TAC `x1:real^3` THEN ASM_REWRITE_TAC[SEGMENT_SYM] THEN
        ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o SPECL [`e:real^3->bool`; `x:real^3`; `y:real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `w:real^3` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`e':real^3->bool`; `x':real^3`; `y':real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `w':real^3` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    SUBGOAL_THEN `~(w:real^3 = w')` ASSUME_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC `~(e:real^3->bool = e')` THEN
      REWRITE_TAC[ASSUME `e = segment[z:real^3,w]`;
                  ASSUME `e' = segment[z:real^3,w']`;
                  ASSUME `w:real^3 = w'`];
      ALL_TAC] THEN
    SUBGOAL_THEN `(a:real^3) dot z = a dot u` ASSUME_TAC THENL
     [UNDISCH_TAC `(z:real^3) IN Z` THEN EXPAND_TAC "Z" THEN
      REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN SIMP_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `segment[z:real^3,w] IN simplicial_link c u /\
                  segment[z:real^3,w'] IN simplicial_link c u` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [UNDISCH_TAC `(e:real^3->bool) IN simplicial_link c u` THEN
        REWRITE_TAC[ASSUME `e = segment[z:real^3,w]`];
        UNDISCH_TAC `(e':real^3->bool) IN simplicial_link c u` THEN
        REWRITE_TAC[ASSUME `e' = segment[z:real^3,w']`]];
      ALL_TAC] THEN
    SUBGOAL_THEN `!v:real^3. segment[z,v] IN simplicial_link c u /\ ~(v = z)
                             ==> ~(a dot v = a dot u)` ASSUME_TAC THENL
     [X_GEN_TAC `v:real^3` THEN STRIP_TAC THEN DISCH_TAC THEN
      SUBGOAL_THEN `segment[z:real^3,v] SUBSET Z` ASSUME_TAC THENL
       [EXPAND_TAC "Z" THEN REWRITE_TAC[SUBSET_INTER] THEN CONJ_TAC THENL
         [MATCH_MP_TAC(SET_RULE
           `!s k:(real^3->bool)->bool. s IN k ==> s SUBSET UNIONS k`) THEN
          ASM_REWRITE_TAC[];
          REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN MATCH_MP_TAC HULL_MINIMAL THEN
          REWRITE_TAC[CONVEX_HYPERPLANE; INSERT_SUBSET; EMPTY_SUBSET;
                      IN_ELIM_THM] THEN
          ASM_REWRITE_TAC[]];
        ALL_TAC] THEN
      SUBGOAL_THEN `FINITE(segment[z:real^3,v])` MP_TAC THENL
       [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `Z:real^3->bool` THEN
        ASM_REWRITE_TAC[];
        REWRITE_TAC[FINITE_SEGMENT] THEN ASM_MESON_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `{z:real^3} IN simplicial_link c u` ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_STL_LINK_FACE_CLOSED THEN
      EXISTS_TAC `segment[z:real^3,w]` THEN
      ASM_REWRITE_TAC[NOT_INSERT_EMPTY; FACE_OF_SING; EXTREME_POINT_OF_SEGMENT];
      ALL_TAC] THEN
    USE_THEN "tr" (MP_TAC o SPECL [`z:real^3`; `w:real^3`; `w':real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `~((a:real^3) dot w = a dot u) /\ ~(a dot w' = a dot u)`
      STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    USE_THEN "sg" (MP_TAC o SPEC `w:real^3`) THEN
    USE_THEN "sg" (MP_TAC o SPEC `w':real^3`) THEN
    USE_THEN "sg" (MP_TAC o SPEC `z:real^3`) THEN
    REWRITE_TAC[ASSUME `{z:real^3} IN simplicial_link c u`;
                ASSUME `{w:real^3} IN simplicial_link c u`;
                ASSUME `{w':real^3} IN simplicial_link c u`] THEN
    UNDISCH_TAC `(b:real^3) dot z < b dot u <=> b dot u < b dot w` THEN
    UNDISCH_TAC `(b:real^3) dot z < b dot u <=> b dot u < b dot w'` THEN
    UNDISCH_TAC `~((a:real^3) dot w = a dot u)` THEN
    UNDISCH_TAC `~((a:real^3) dot w' = a dot u)` THEN
    MP_TAC(REAL_ARITH `~((b:real^3) dot w < b dot u /\ b dot u < b dot w)`) THEN
    MP_TAC(REAL_ARITH `~((b:real^3) dot w' < b dot u /\ b dot u < b dot w')`) THEN
    MP_TAC(REAL_ARITH `~((a:real^3) dot w = a dot u)
                       ==> (a dot u < a dot w <=> ~(a dot w < a dot u))`) THEN
    MP_TAC(REAL_ARITH `~((a:real^3) dot w' = a dot u)
                       ==> (a dot u < a dot w' <=> ~(a dot w' < a dot u))`) THEN
    CONV_TAC TAUT;
    ALL_TAC] THEN
  MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC `CARD (IMAGE (\e:real^3->bool. @z:real^3. z IN e /\ z IN Z) E)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC EQ_IMP_LE THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC CARD_IMAGE_INJ THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`e:real^3->bool`; `e':real^3->bool`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    EXISTS_TAC `@z:real^3. z IN e /\ z IN Z` THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "pt" (fun th -> MP_TAC(SELECT_RULE(MATCH_MP th
      (ASSUME `(e:real^3->bool) IN E`)))) THEN
    USE_THEN "pt" (fun th -> MP_TAC(SELECT_RULE(MATCH_MP th
      (ASSUME `(e':real^3->bool) IN E`)))) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    MATCH_MP_TAC CARD_SUBSET THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `e:real^3->bool` THEN
    DISCH_TAC THEN
    USE_THEN "pt" (fun th -> MP_TAC(SELECT_RULE(MATCH_MP th
      (ASSUME `(e:real^3->bool) IN E`)))) THEN
    SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* 6. Level rays.  If the level set of a surface near a point lies in       *)
(* finitely many rays from the point, the level points of the link of a    *)
(* vertex there are at most as many as the rays; level-preserving PL        *)
(* homeomorphisms carry rays to rays; a generic height has at most two      *)
(* level rays at a non-vertex point and at most crossings-many at a vertex. *)
(* ------------------------------------------------------------------------- *)

let MOI_STL_RAY_ORDER = prove
 (`!K (u:real^3) d k1 k2.
     simplicial_complex K /\ &0 < k1 /\ k1 < k2 /\
     u + k1 % d IN UNIONS (simplicial_link K u) /\
     u + k2 % d IN UNIONS (simplicial_link K u)
     ==> F`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`K:(real^3->bool)->bool`; `u:real^3`; `u + k2 % d:real^3`;
                 `u + k1 % d:real^3`] MOI_STL_LINK_RAY) THEN
  ASM_REWRITE_TAC[IN_SEGMENT] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`K:(real^3->bool)->bool`; `u:real^3`; `u + k2 % d:real^3`]
      MOI_STL_LINK_POINT) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < k2` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  EXISTS_TAC `k1 / k2` THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_LT_LDIV_EQ; REAL_MUL_LID] THEN
  SUBGOAL_THEN `k1 / k2 * k2 = k1` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_DIV_RMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[VECTOR_ADD_LDISTRIB; VECTOR_MUL_ASSOC] THEN
  ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC);;

let MOI_STL_RAY_COUNT = prove
 (`!K (u:real^3) X (R:real^3->bool).
     simplicial_complex K /\ FINITE R /\
     X SUBSET UNIONS (simplicial_link K u) /\
     (!z. z IN X ==> ?d k. d IN R /\ &0 < k /\ z = u + k % d)
     ==> FINITE X /\ CARD X <= CARD R`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!z1 z2 (d:real^3) k1 k2.
      z1 IN X /\ z2 IN X /\ &0 < k1 /\ &0 < k2 /\
      z1 = u + k1 % d /\ z2 = u + k2 % d ==> z1 = z2`
  (LABEL_TAC "rinj") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `(u + k1 % d:real^3) IN UNIONS (simplicial_link K u) /\
                  (u + k2 % d:real^3) IN UNIONS (simplicial_link K u)`
      STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
    DISJ_CASES_TAC(SPECL [`k1:real`; `k2:real`] REAL_LT_TOTAL) THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC(TAUT `F ==> p`) THEN
    FIRST_X_ASSUM DISJ_CASES_TAC THENL
     [MATCH_MP_TAC MOI_STL_RAY_ORDER THEN
      MAP_EVERY EXISTS_TAC [`K:(real^3->bool)->bool`; `u:real^3`; `d:real^3`;
                            `k1:real`; `k2:real`] THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC MOI_STL_RAY_ORDER THEN
      MAP_EVERY EXISTS_TAC [`K:(real^3->bool)->bool`; `u:real^3`; `d:real^3`;
                            `k2:real`; `k1:real`] THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `h = \z:real^3. @d:real^3. d IN R /\ ?k. &0 < k /\ z = u + k % d` THEN
  SUBGOAL_THEN
   `!z. z IN X ==> (h:real^3->real^3) z IN R /\ ?k. &0 < k /\ z = u + k % h z`
  (LABEL_TAC "hz") THENL
   [X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN EXPAND_TAC "h" THEN
    CONV_TAC(ONCE_DEPTH_CONV BETA_CONV) THEN CONV_TAC SELECT_CONV THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z1 z2. z1 IN X /\ z2 IN X /\ (h:real^3->real^3) z1 = h z2 ==> z1 = z2`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    USE_THEN "hz" (MP_TAC o C MATCH_MP (ASSUME `(z1:real^3) IN X`)) THEN
    USE_THEN "hz" (MP_TAC o C MATCH_MP (ASSUME `(z2:real^3) IN X`)) THEN
    REWRITE_TAC[ASSUME `(h:real^3->real^3) z1 = h z2`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `k2:real`
      STRIP_ASSUME_TAC)) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `k1:real`
      STRIP_ASSUME_TAC)) THEN
    USE_THEN "rinj" MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`(h:real^3->real^3) z2`; `k1:real`; `k2:real`] THEN
    REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (h:real^3->real^3) X SUBSET R` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `FINITE (X:real^3->bool)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`h:real^3->real^3`; `X:real^3->bool`] FINITE_IMAGE_INJ_EQ) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
    ASM_MESON_TAC[FINITE_SUBSET];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC `CARD(IMAGE (h:real^3->real^3) X)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC EQ_IMP_LE THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC CARD_IMAGE_INJ THEN ASM_MESON_TAC[];
    MATCH_MP_TAC CARD_SUBSET THEN ASM_REWRITE_TAC[]]);;

let MOI_STL_RAYS_TRANSPORT = prove
 (`!s (f:real^3->real^3) g (a:real^3) y (R:real^3->bool) r.
     pl_homeomorphism ((:real^3),(:real^3)) (f,g) /\ (!x. a dot f x = a dot x) /\
     FINITE R /\ &0 < r /\
     (!x. x IN s /\ a dot x = a dot y /\ dist(y,x) < r /\ ~(x = y)
          ==> ?d k. d IN R /\ &0 < k /\ x = y + k % d)
     ==> ?R' r'. FINITE R' /\ CARD R' <= CARD R /\ &0 < r' /\
                 !x. x IN IMAGE f s /\ a dot x = a dot f y /\ dist(f y,x) < r' /\
                     ~(x = f y)
                     ==> ?d k. d IN R' /\ &0 < k /\ x = f y + k % d`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (LABEL_TAC "rays"))))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [pl_homeomorphism]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  SUBGOAL_THEN `!z:real^3. (g:real^3->real^3) (f z) = z` ASSUME_TAC THENL
   [ASM_MESON_TAC[IN_UNIV]; ALL_TAC] THEN
  MP_TAC(ISPECL [`(:real^3)`; `f:real^3->real^3`; `y:real^3`]
    MOI_CMB_PL_LOCALLY_CONIC) THEN
  ASM_REWRITE_TAC[IN_UNIV] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "lc"))) THEN
  ABBREV_TAC `r1 = min r e / &2` THEN
  SUBGOAL_THEN `&0 < r1 /\ r1 < r /\ r1 < e` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "r1" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(g:real^3->real^3) continuous (at (f(y:real^3)))` MP_TAC THENL
   [MP_TAC(ISPECL [`g:real^3->real^3`; `(:real^3)`]
      CONTINUOUS_ON_EQ_CONTINUOUS_AT) THEN
    ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[continuous_at] THEN DISCH_THEN(MP_TAC o SPEC `r1:real`) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "gc"))) THEN
  EXISTS_TAC `IMAGE (\d:real^3. f(y + (r1 / norm d) % d) - (f:real^3->real^3) y) R` THEN
  EXISTS_TAC `r2:real` THEN ASM_SIMP_TAC[FINITE_IMAGE; CARD_IMAGE_LE] THEN
  X_GEN_TAC `x:real^3` THEN REWRITE_TAC[IN_IMAGE] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `x0:real^3` STRIP_ASSUME_TAC)
    STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `x:real^3 = (f:real^3->real^3) x0` THEN DISCH_THEN SUBST_ALL_TAC THEN
  SUBGOAL_THEN `dist(y:real^3,x0) < r1` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[DIST_SYM] THEN
    SUBGOAL_THEN `dist((g:real^3->real^3)((f:real^3->real^3) x0),y:real^3) < r1`
      MP_TAC THENL
     [USE_THEN "gc" MATCH_MP_TAC THEN ONCE_REWRITE_TAC[DIST_SYM] THEN
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(x0:real^3 = y)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `~((f:real^3->real^3) y = f y)` THEN REWRITE_TAC[];
    ALL_TAC] THEN
  USE_THEN "rays" (MP_TAC o SPEC `x0:real^3`) THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      UNDISCH_TAC `(a:real^3) dot (f:real^3->real^3) x0 = a dot y` THEN
      ASM_REWRITE_TAC[];
      ASM_REAL_ARITH_TAC;
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real^3` (X_CHOOSE_THEN `k:real` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `~(d:real^3 = vec 0)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC `~(x0:real^3 = y)` THEN
    ASM_REWRITE_TAC[VECTOR_MUL_RZERO; VECTOR_ADD_RID];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < norm(d:real^3)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `k * norm(d:real^3) < r1` ASSUME_TAC THENL
   [UNDISCH_TAC `dist(y:real^3,x0) < r1` THEN
    ASM_REWRITE_TAC[dist; VECTOR_ARITH `y - (y + k % d):real^3 = --(k % d)`;
                    NORM_NEG; NORM_MUL] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < k ==> abs k = k`];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < r1 / norm(d:real^3)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `y + ((k * norm(d:real^3)) / r1) % ((y + (r1 / norm d) % d) - y) = x0`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[VECTOR_ARITH `(y + c % d) - y:real^3 = c % d`;
                    VECTOR_MUL_ASSOC] THEN
    AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    UNDISCH_TAC `&0 < norm(d:real^3)` THEN UNDISCH_TAC `&0 < r1` THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  USE_THEN "lc" (MP_TAC o SPECL [`y + (r1 / norm d) % d:real^3`;
                                 `(k * norm(d:real^3)) / r1`]) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REWRITE_TAC[dist; VECTOR_ARITH `y - (y + c % d):real^3 = --(c % d)`;
                  NORM_NEG; NORM_MUL] THEN
      ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`; REAL_DIV_RMUL;
                   REAL_LT_IMP_NZ];
      MATCH_MP_TAC REAL_LE_DIV THEN
      ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE; NORM_POS_LE];
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_MUL_LID; REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[IN_UNIV] THEN DISCH_TAC THEN
  EXISTS_TAC `f(y + (r1 / norm d) % d) - (f:real^3->real^3) y` THEN
  EXISTS_TAC `(k * norm(d:real^3)) / r1` THEN REPEAT CONJ_TAC THENL
   [EXISTS_TAC `d:real^3` THEN BETA_TAC THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_LT_DIV THEN ASM_SIMP_TAC[REAL_LT_MUL];
    ASM_REWRITE_TAC[]]);;

let MOI_STL_TRANSVERSE_ANY = prove
 (`!c (a:real^3) z.
     moi_sch3_generic c a /\ z IN UNIONS c /\ ~({z} IN c)
     ==> (?w. a dot z < a dot w /\ segment[z,w] SUBSET UNIONS c) /\
         (?w. a dot w < a dot z /\ segment[z,w] SUBSET UNIONS c)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `(z:real^3) IN UNIONS c` THEN REWRITE_TAC[IN_UNIONS] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real^3->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `simplicial_complex (c:(real^3->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[moi_sch3_generic]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `s:real^3->bool`]
    MOI_SLV_SC_SIMPLEX_VERTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `W:real^3->bool` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP AFFINE_INDEPENDENT_IMP_FINITE) THEN
  SUBGOAL_THEN `~((z:real^3) IN convex hull {w | w IN W /\ a dot w = a dot z})`
    ASSUME_TAC THENL
   [DISCH_TAC THEN
    ASM_CASES_TAC `?w:real^3. w IN W /\ a dot w = a dot z` THENL
     [FIRST_X_ASSUM(X_CHOOSE_THEN `w0:real^3` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `{w:real^3 | w IN W /\ a dot w = a dot z} = {w0}`
        SUBST_ALL_TAC THENL
       [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_SING] THEN
        X_GEN_TAC `w:real^3` THEN EQ_TAC THENL
         [STRIP_TAC THEN MATCH_MP_TAC MOI_SLV_GENERIC_VERTEX THEN
          MAP_EVERY EXISTS_TAC [`c:(real^3->bool)->bool`; `a:real^3`] THEN
          ASM_SIMP_TAC[];
          DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]];
        ALL_TAC] THEN
      UNDISCH_TAC `(z:real^3) IN convex hull {w0}` THEN
      REWRITE_TAC[CONVEX_HULL_SING; IN_SING] THEN DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `~({w0:real^3} IN c)` THEN ASM_SIMP_TAC[];
      SUBGOAL_THEN `{w:real^3 | w IN W /\ a dot w = a dot z} = {}` SUBST_ALL_TAC THENL
       [REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN ASM_MESON_TAC[];
        ALL_TAC] THEN
      UNDISCH_TAC `(z:real^3) IN convex hull {}` THEN
      REWRITE_TAC[CONVEX_HULL_EMPTY; NOT_IN_EMPTY]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!w:real^3. w IN W ==> segment[z,w] SUBSET UNIONS c`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `s:real^3->bool` THEN CONJ_TAC THENL
     [REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN
      MATCH_MP_TAC HULL_MINIMAL THEN
      REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET] THEN
      SUBGOAL_THEN `(w:real^3) IN s /\ convex(s:real^3->bool)` STRIP_ASSUME_TAC THENL
       [ASM_REWRITE_TAC[CONVEX_CONVEX_HULL] THEN ASM_MESON_TAC[HULL_SUBSET; SUBSET];
        ASM_REWRITE_TAC[]];
      UNDISCH_TAC `(s:real^3->bool) IN c` THEN SET_TAC[]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [ASM_CASES_TAC `?w:real^3. w IN W /\ a dot z < a dot w` THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`W:real^3->bool`; `a:real^3`; `a dot (z:real^3)`]
      MOI_SLV_HALF_SLICE_LE);
    ASM_CASES_TAC `?w:real^3. w IN W /\ a dot w < a dot z` THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`W:real^3->bool`; `a:real^3`; `a dot (z:real^3)`]
      MOI_SLV_HALF_SLICE)] THEN
  (ANTS_TAC THENL [ASM_MESON_TAC[REAL_NOT_LT]; ALL_TAC]) THEN
  DISCH_TAC THEN
  UNDISCH_TAC `~((z:real^3) IN convex hull {w | w IN W /\ a dot w = a dot z})` THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
    is_eq(concl th) && is_comb(rhs(concl th)) &&
    can (find_term ((=) `W:real^3->bool`)) (rhs(concl th)))) THEN
  REWRITE_TAC[IN_INTER; IN_ELIM_THM;
              GSYM(ASSUME `s = convex hull (W:real^3->bool)`);
              ASSUME `(z:real^3) IN s`]);;

let MOI_STL_CARD_PAIR_LE = prove
 (`!x y:A. FINITE {x,y} /\ CARD {x,y} <= 2`,
  REPEAT GEN_TAC THEN
  SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY; IN_INSERT; NOT_IN_EMPTY] THEN
  COND_CASES_TAC THEN ARITH_TAC);;

let MOI_STL_LINE_RAYS = prove
 (`!S (y:real^3).
     aff_dim S <= &1 /\ y IN S
     ==> ?R. FINITE R /\ CARD R <= 2 /\
             !x. x IN S /\ ~(x = y) ==> ?d k. d IN R /\ &0 < k /\ x = y + k % d`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `?x1:real^3. x1 IN S /\ ~(x1 = y)` THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `x1:real^3` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `{x1 - y:real^3, y - x1}` THEN
    REWRITE_TAC[MOI_STL_CARD_PAIR_LE] THEN
    X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
    SUBGOAL_THEN `~(y:real^3 = x1)` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `collinear {y:real^3, x1, x}` MP_TAC THENL
     [REWRITE_TAC[COLLINEAR_AFF_DIM] THEN MATCH_MP_TAC INT_LE_TRANS THEN
      EXISTS_TAC `aff_dim(S:real^3->bool)` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC AFF_DIM_SUBSET THEN ASM_REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET];
      ALL_TAC] THEN
    ASM_SIMP_TAC[COLLINEAR_3_AFFINE_HULL; AFFINE_HULL_2_ALT] THEN
    REWRITE_TAC[IN_ELIM_THM; IN_UNIV] THEN
    DISCH_THEN(X_CHOOSE_THEN `l:real` SUBST_ALL_TAC) THEN
    ASM_CASES_TAC `l = &0` THENL
     [UNDISCH_TAC `~(y + l % (x1 - y):real^3 = y)` THEN
      ASM_REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_RID];
      ALL_TAC] THEN
    ASM_CASES_TAC `&0 < l` THENL
     [MAP_EVERY EXISTS_TAC [`x1 - y:real^3`; `l:real`] THEN
      ASM_REWRITE_TAC[IN_INSERT];
      MAP_EVERY EXISTS_TAC [`y - x1:real^3`; `--l`] THEN
      REWRITE_TAC[IN_INSERT] THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; VECTOR_ARITH_TAC]];
    EXISTS_TAC `{}:real^3->bool` THEN
    REWRITE_TAC[FINITE_EMPTY; CARD_CLAUSES; ARITH_RULE `0 <= 2`] THEN
    ASM_MESON_TAC[]]);;

let MOI_STL_HALF_RAY = prove
 (`!tr (a:real^3) w1 w2 y.
     segment[w1,w2] face_of tr /\ y IN segment(w1,w2) /\
     ~(a dot w1 = a dot w2) /\
     aff_dim (tr INTER {x | a dot x = a dot y}) <= &1
     ==> ?R. FINITE R /\ CARD R <= 1 /\
             !x. x IN tr /\ a dot x = a dot y /\ ~(x = y)
                 ==> ?d k. d IN R /\ &0 < k /\ x = y + k % d`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!x:real^3. x IN segment[w1,w2] /\ a dot x = a dot y ==> x = y`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^3` THEN UNDISCH_TAC `(y:real^3) IN segment(w1,w2)` THEN
    REWRITE_TAC[IN_SEGMENT] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `t:real`
      STRIP_ASSUME_TAC)) THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `s:real` STRIP_ASSUME_TAC)
      MP_TAC) THEN
    ASM_REWRITE_TAC[DOT_RADD; DOT_RMUL] THEN DISCH_TAC THEN
    SUBGOAL_THEN `s:real = t` SUBST1_TAC THENL
     [UNDISCH_TAC `~((a:real^3) dot w1 = a dot w2)` THEN
      POP_ASSUM MP_TAC THEN CONV_TAC REAL_RING;
      REFL_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^3) IN segment[w1,w2] /\ segment[w1,w2] SUBSET tr`
    STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [ASM_MESON_TAC[SEGMENT_OPEN_SUBSET_CLOSED; SUBSET];
      ASM_MESON_TAC[FACE_OF_IMP_SUBSET]];
    ALL_TAC] THEN
  ASM_CASES_TAC `?x1:real^3. x1 IN tr /\ a dot x1 = a dot y /\ ~(x1 = y)` THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `x1:real^3` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `{x1 - y:real^3}` THEN
    REWRITE_TAC[FINITE_SING; CARD_SING; LE_REFL; IN_SING] THEN
    X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
    SUBGOAL_THEN `~(y:real^3 = x1)` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `collinear {y:real^3, x1, x}` MP_TAC THENL
     [REWRITE_TAC[COLLINEAR_AFF_DIM] THEN MATCH_MP_TAC INT_LE_TRANS THEN
      EXISTS_TAC `aff_dim(tr INTER {x:real^3 | a dot x = a dot y})` THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC AFF_DIM_SUBSET THEN
      REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET; IN_INTER; IN_ELIM_THM] THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `segment[w1:real^3,w2] SUBSET tr` THEN
      UNDISCH_TAC `(y:real^3) IN segment[w1,w2]` THEN SET_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[MATCH_MP COLLINEAR_3_AFFINE_HULL (ASSUME `~(y:real^3 = x1)`);
                AFFINE_HULL_2_ALT] THEN
    REWRITE_TAC[IN_ELIM_THM; IN_UNIV] THEN
    DISCH_THEN(X_CHOOSE_THEN `l:real` SUBST_ALL_TAC) THEN
    ASM_CASES_TAC `l = &0` THENL
     [UNDISCH_TAC `~(y + l % (x1 - y):real^3 = y)` THEN
      ASM_REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_RID];
      ALL_TAC] THEN
    ASM_CASES_TAC `&0 < l` THENL
     [MAP_EVERY EXISTS_TAC [`x1 - y:real^3`; `l:real`] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC(TAUT `F ==> p`) THEN
    SUBGOAL_THEN `(y:real^3) IN segment(y + l % (x1 - y),x1)` ASSUME_TAC THENL
     [REWRITE_TAC[IN_SEGMENT] THEN CONJ_TAC THENL
       [REWRITE_TAC[VECTOR_ARITH
         `y + l % (x1 - y):real^3 = x1 <=> (&1 - l) % (x1 - y) = vec 0`] THEN
        REWRITE_TAC[VECTOR_MUL_EQ_0; VECTOR_SUB_EQ] THEN
        ASM_MESON_TAC[REAL_ARITH `~(&0 < l) ==> ~(&1 - l = &0)`];
        ALL_TAC] THEN
      EXISTS_TAC `--l / (&1 - l)` THEN
      SUBGOAL_THEN `&0 < &1 - l` ASSUME_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      CONJ_TAC THENL
       [REWRITE_TAC[MATCH_MP REAL_LT_LDIV_EQ (ASSUME `&0 < &1 - l`)] THEN
        ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      REWRITE_TAC[VECTOR_ARITH
       `(&1 - u) % (y + l % (x1 - y)) + u % x1:real^3 =
        y + ((&1 - u) * l + u) % (x1 - y)`] THEN
      SUBGOAL_THEN `(&1 - --l / (&1 - l)) * l + --l / (&1 - l) = &0`
        SUBST1_TAC THENL
       [UNDISCH_TAC `&0 < &1 - l` THEN CONV_TAC REAL_FIELD;
        VECTOR_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `(x1:real^3) IN segment[w1,w2]` MP_TAC THENL
     [UNDISCH_TAC `segment[w1:real^3,w2] face_of tr` THEN
      REWRITE_TAC[face_of] THEN
      DISCH_THEN(MP_TAC o SPECL [`y + l % (x1 - y):real^3`; `x1:real^3`; `y:real^3`]
        o CONJUNCT2 o CONJUNCT2) THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[];
      ALL_TAC] THEN
    DISCH_TAC THEN UNDISCH_TAC `~(x1:real^3 = y)` THEN REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    EXISTS_TAC `{}:real^3->bool` THEN
    REWRITE_TAC[FINITE_EMPTY; CARD_CLAUSES; LE_0] THEN
    ASM_MESON_TAC[]]);;

let MOI_STL_EDGE_LEVEL_UNIQUE = prove
 (`!(a:real^3) w1 w2 y x.
     y IN segment(w1,w2) /\ ~(a dot w1 = a dot w2) /\
     x IN segment[w1,w2] /\ a dot x = a dot y
     ==> x = y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_SEGMENT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC)) (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (X_CHOOSE_THEN `s:real` STRIP_ASSUME_TAC) MP_TAC))) THEN
  ASM_REWRITE_TAC[DOT_RADD; DOT_RMUL] THEN DISCH_TAC THEN
  SUBGOAL_THEN `s:real = t` SUBST1_TAC THENL
   [UNDISCH_TAC `~((a:real^3) dot w1 = a dot w2)` THEN
    POP_ASSUM MP_TAC THEN CONV_TAC REAL_RING;
    REFL_TAC]);;

let MOI_STL_NONVERTEX_RAYS = prove
 (`!c (a:real^3) y.
     moi_sch3_generic c a /\ pl_sphere 2 (UNIONS c) /\ y IN UNIONS c /\
     ~({y} IN c)
     ==> ?R r. FINITE R /\ CARD R <= 2 /\ &0 < r /\
               !x. x IN UNIONS c /\ a dot x = a dot y /\ dist(y,x) < r /\
                   ~(x = y)
                   ==> ?d k. d IN R /\ &0 < k /\ x = y + k % d`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_sch3_generic]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SLV_SC_BASIC) THEN
  MP_TAC(ISPEC `c:(real^3->bool)->bool` MOI_SLV_SPHERE_SURFACE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "dim2") (LABEL_TAC "two")) THEN
  SUBGOAL_THEN `?s:real^3->bool. s IN c /\ y IN s` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[IN_UNIONS]; ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `y:real^3`] IN_RELATIVE_INTERIOR_OF_FACE) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `sg:real^3->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(sg:real^3->bool) IN c` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^3) IN sg` ASSUME_TAC THENL
   [ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `y:real^3`] MOI_SLV_LOCAL_BALL) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "lb"))) THEN
  SUBGOAL_THEN
   `!x:real^3. x IN UNIONS c /\ dist(y,x) < r
               ==> ?t. t IN c /\ sg SUBSET t /\ x IN t`
  (LABEL_TAC "near") THENL
   [X_GEN_TAC `x:real^3` THEN REWRITE_TAC[IN_UNIONS] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `t:real^3->bool` STRIP_ASSUME_TAC)
      ASSUME_TAC) THEN
    EXISTS_TAC `t:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_SCF_RELINT_SUBSET THEN
    MAP_EVERY EXISTS_TAC [`c:(real^3->bool)->bool`; `y:real^3`] THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "lb" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_BALL] THEN
    EXISTS_TAC `x:real^3` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `aff_dim(sg:real^3->bool) <= &2` ASSUME_TAC THENL
   [USE_THEN "dim2" (fun th -> MP_TAC(MATCH_MP th
      (ASSUME `(sg:real^3->bool) IN c`))) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `aff_dim(sg:real^3->bool) = &1 \/ aff_dim sg = &2` MP_TAC THENL
   [SUBGOAL_THEN `~(aff_dim(sg:real^3->bool) = -- &1)` MP_TAC THENL
     [REWRITE_TAC[AFF_DIM_EQ_MINUS1; GSYM MEMBER_NOT_EMPTY] THEN
      EXISTS_TAC `y:real^3` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `~(aff_dim(sg:real^3->bool) = &0)` MP_TAC THENL
     [REWRITE_TAC[AFF_DIM_EQ_0] THEN
      DISCH_THEN(X_CHOOSE_THEN `v:real^3` SUBST_ALL_TAC) THEN
      UNDISCH_TAC `(y:real^3) IN {v}` THEN REWRITE_TAC[IN_SING] THEN
      DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `~({v:real^3} IN c)` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPEC `sg:real^3->bool` AFF_DIM_GE) THEN
    UNDISCH_TAC `aff_dim(sg:real^3->bool) <= &2` THEN
    SPEC_TAC(`aff_dim(sg:real^3->bool)`,`d:int`) THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  STRIP_TAC THENL
   [MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `sg:real^3->bool`] MOI_SLV_EDGE) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `w1:real^3` (X_CHOOSE_THEN `w2:real^3`
      STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `(y:real^3) IN segment(w1,w2)` ASSUME_TAC THENL
     [UNDISCH_TAC `(y:real^3) IN relative_interior sg` THEN
      ASM_REWRITE_TAC[RELATIVE_INTERIOR_SEGMENT];
      ALL_TAC] THEN
    SUBGOAL_THEN `~((a:real^3) dot w1 = a dot w2)` ASSUME_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC `~(w1:real^3 = w2)` THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC MOI_SLV_GENERIC_VERTEX THEN
      MAP_EVERY EXISTS_TAC [`c:(real^3->bool)->bool`; `a:real^3`] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `{t:real^3->bool | t IN c /\ aff_dim t = &2 /\ sg SUBSET t} HAS_SIZE 2`
    MP_TAC THENL
     [REWRITE_TAC[HAS_SIZE] THEN CONJ_TAC THENL
       [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `c:(real^3->bool)->bool` THEN
        ASM_REWRITE_TAC[] THEN SET_TAC[];
        USE_THEN "two" (fun th -> MATCH_MP_TAC th) THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    REWRITE_TAC[MOI_SCF_HAS_SIZE_2] THEN
    DISCH_THEN(X_CHOOSE_THEN `t1:real^3->bool` (X_CHOOSE_THEN `t2:real^3->bool`
      STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN
     `!t:real^3->bool. t IN c /\ aff_dim t = &2 /\ sg SUBSET t ==> t = t1 \/ t = t2`
    (LABEL_TAC "t12") THENL
     [GEN_TAC THEN DISCH_TAC THEN
      SUBGOAL_THEN `(t:real^3->bool) IN {t1,t2}` MP_TAC THENL
       [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[IN_ELIM_THM];
        REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY]];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `(t1:real^3->bool) IN c /\ aff_dim t1 = &2 /\ sg SUBSET t1 /\
      (t2:real^3->bool) IN c /\ aff_dim t2 = &2 /\ sg SUBSET t2`
    STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN `(t1:real^3->bool) IN {t1,t2} /\ (t2:real^3->bool) IN {t1,t2}`
      MP_TAC THENL
       [REWRITE_TAC[IN_INSERT]; ALL_TAC] THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[IN_ELIM_THM] THEN
      SIMP_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`t1:real^3->bool`; `a:real^3`; `w1:real^3`; `w2:real^3`;
                   `y:real^3`] MOI_STL_HALF_RAY) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [UNDISCH_TAC `sg = segment[w1:real^3,w2]` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
        MATCH_MP_TAC MOI_SCF_SUBSET_FACE THEN
        EXISTS_TAC `c:(real^3->bool)->bool` THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC MOI_SLV_LEVEL_DIM THEN
        EXISTS_TAC `c:(real^3->bool)->bool` THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `R1:real^3->bool` (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "r1")))) THEN
    MP_TAC(ISPECL [`t2:real^3->bool`; `a:real^3`; `w1:real^3`; `w2:real^3`;
                   `y:real^3`] MOI_STL_HALF_RAY) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [UNDISCH_TAC `sg = segment[w1:real^3,w2]` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
        MATCH_MP_TAC MOI_SCF_SUBSET_FACE THEN
        EXISTS_TAC `c:(real^3->bool)->bool` THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC MOI_SLV_LEVEL_DIM THEN
        EXISTS_TAC `c:(real^3->bool)->bool` THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `R2:real^3->bool` (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "r2")))) THEN
    MAP_EVERY EXISTS_TAC [`R1 UNION R2:real^3->bool`; `r:real`] THEN
    MP_TAC(ISPECL [`R1:real^3->bool`; `R2:real^3->bool`; `1`; `1`]
      FINITE_CARD_LE_UNION) THEN
    ASM_REWRITE_TAC[ARITH_RULE `1 + 1 = 2`] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
    USE_THEN "near" (MP_TAC o C MATCH_MP (CONJ (ASSUME `(x:real^3) IN UNIONS c`)
      (ASSUME `dist(y:real^3,x) < r`))) THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real^3->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `aff_dim(t:real^3->bool) = &1 \/ aff_dim t = &2` MP_TAC THENL
     [SUBGOAL_THEN `aff_dim(t:real^3->bool) <= &2` MP_TAC THENL
       [USE_THEN "dim2" (fun th -> MP_TAC(MATCH_MP th
          (ASSUME `(t:real^3->bool) IN c`))) THEN REWRITE_TAC[];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`sg:real^3->bool`; `t:real^3->bool`] AFF_DIM_SUBSET) THEN
      ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
      ALL_TAC] THEN
    STRIP_TAC THENL
     [SUBGOAL_THEN `sg:real^3->bool = t` SUBST_ALL_TAC THENL
       [MATCH_MP_TAC MOI_SCF_SUBSET_DIM_EQ THEN
        EXISTS_TAC `c:(real^3->bool)->bool` THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      MATCH_MP_TAC(TAUT `F ==> p`) THEN UNDISCH_TAC `~(x:real^3 = y)` THEN
      REWRITE_TAC[] THEN MATCH_MP_TAC MOI_STL_EDGE_LEVEL_UNIQUE THEN
      MAP_EVERY EXISTS_TAC [`a:real^3`; `w1:real^3`; `w2:real^3`] THEN
      ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(x:real^3) IN t` THEN
      ASM_REWRITE_TAC[];
      USE_THEN "t12" (MP_TAC o C MATCH_MP (CONJ (ASSUME `(t:real^3->bool) IN c`)
        (CONJ (ASSUME `aff_dim(t:real^3->bool) = &2`)
              (ASSUME `(sg:real^3->bool) SUBSET t`)))) THEN
      STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THENL
       [USE_THEN "r1" (MP_TAC o C MATCH_MP (CONJ (ASSUME `(x:real^3) IN t1`)
          (CONJ (ASSUME `(a:real^3) dot x = a dot y`) (ASSUME `~(x:real^3 = y)`))));
        USE_THEN "r2" (MP_TAC o C MATCH_MP (CONJ (ASSUME `(x:real^3) IN t2`)
          (CONJ (ASSUME `(a:real^3) dot x = a dot y`) (ASSUME `~(x:real^3 = y)`))))] THEN
      REWRITE_TAC[IN_UNION] THEN MESON_TAC[]];
    MP_TAC(ISPECL [`sg INTER {x:real^3 | a dot x = a dot y}`; `y:real^3`]
      MOI_STL_LINE_RAYS) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC MOI_SLV_LEVEL_DIM THEN
        EXISTS_TAC `c:(real^3->bool)->bool` THEN ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM]];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `R:real^3->bool` (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "lr")))) THEN
    MAP_EVERY EXISTS_TAC [`R:real^3->bool`; `r:real`] THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
    USE_THEN "lr" MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN
    USE_THEN "near" (MP_TAC o C MATCH_MP (CONJ (ASSUME `(x:real^3) IN UNIONS c`)
      (ASSUME `dist(y:real^3,x) < r`))) THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real^3->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `sg:real^3->bool = t` (fun th -> ASM_REWRITE_TAC[th]) THEN
    MATCH_MP_TAC MOI_SCF_SUBSET_DIM_EQ THEN
    EXISTS_TAC `c:(real^3->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `aff_dim(t:real^3->bool) <= &2` MP_TAC THENL
     [USE_THEN "dim2" (fun th -> MP_TAC(MATCH_MP th
        (ASSUME `(t:real^3->bool) IN c`))) THEN REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`sg:real^3->bool`; `t:real^3->bool`] AFF_DIM_SUBSET) THEN
    ASM_REWRITE_TAC[] THEN INT_ARITH_TAC]);;

let MOI_STL_VERTEX_RAYS = prove
 (`!c (a:real^3) u.
     moi_sch3_generic c a /\ pl_sphere 2 (UNIONS c) /\ {u} IN c
     ==> ?R r. FINITE R /\ CARD R <= moi_sch3_crossings c a u /\ &0 < r /\
               !x. x IN UNIONS c /\ a dot x = a dot u /\ dist(u,x) < r /\
                   ~(x = u)
                   ==> ?d k. d IN R /\ &0 < k /\ x = u + k % d`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `a:real^3`; `a dot (u:real^3)`]
    MOI_SLV_LEVEL_COMPLEX) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `L = {s INTER {x:real^3 | a dot x = a dot u} | s IN c}` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "ld")
    ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `a:real^3`; `u:real^3`]
    MOI_SLV_LEVEL_STAR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `E = {s:real^3->bool | s IN L /\ aff_dim s = &1 /\ u IN s}` THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SLV_SC_BASIC o check (fun th ->
    concl th = `simplicial_complex (L:(real^3->bool)->bool)`)) THEN
  SUBGOAL_THEN `{u:real^3} IN L` ASSUME_TAC THENL
   [EXPAND_TAC "L" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    EXISTS_TAC `{u:real^3}` THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE (E:(real^3->bool)->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `L:(real^3->bool)->bool` THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "E" THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!e. e IN E ==> ?w:real^3. e = segment[u,w] /\ ~(w = u)`
  (LABEL_TAC "seg") THENL
   [X_GEN_TAC `e:real^3->bool` THEN EXPAND_TAC "E" THEN
    REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`L:(real^3->bool)->bool`; `e:real^3->bool`] MOI_SLV_EDGE) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `w1:real^3` (X_CHOOSE_THEN `w2:real^3`
      STRIP_ASSUME_TAC)) THEN
    MP_TAC(ISPECL [`L:(real^3->bool)->bool`; `u:real^3`; `w1:real^3`; `w2:real^3`]
      MOI_SLV_VERTEX_IN_SEGMENT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    STRIP_TAC THENL
     [EXISTS_TAC `w2:real^3` THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
      EXISTS_TAC `w1:real^3` THEN ASM_REWRITE_TAC[SEGMENT_SYM] THEN
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `oth = \e:real^3->bool. @w:real^3. e = segment[u,w] /\ ~(w = u)` THEN
  SUBGOAL_THEN
   `!e. e IN E ==> e = segment[u:real^3,oth e] /\ ~(oth e = u)`
  (LABEL_TAC "oth") THENL
   [X_GEN_TAC `e:real^3->bool` THEN DISCH_TAC THEN EXPAND_TAC "oth" THEN
    CONV_TAC(ONCE_DEPTH_CONV BETA_CONV) THEN CONV_TAC SELECT_CONV THEN
    USE_THEN "seg" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`L:(real^3->bool)->bool`; `u:real^3`] MOI_SLV_LOCAL_BALL) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "lb"))) THEN
  MAP_EVERY EXISTS_TAC
   [`IMAGE (\e:real^3->bool. (oth:(real^3->bool)->real^3) e - u) E`; `r:real`] THEN
  ASM_SIMP_TAC[FINITE_IMAGE] THEN CONJ_TAC THENL
   [MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `CARD(E:(real^3->bool)->bool)` THEN
    ASM_SIMP_TAC[CARD_IMAGE_LE] THEN
    UNDISCH_TAC `CARD(E:(real^3->bool)->bool) = moi_sch3_crossings c a u` THEN
    ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
  SUBGOAL_THEN `?t:real^3->bool. t IN L /\ x IN t` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `(x:real^3) IN UNIONS L` MP_TAC THENL
     [ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM]; REWRITE_TAC[IN_UNIONS]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(u:real^3) IN t` ASSUME_TAC THENL
   [USE_THEN "lb" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_BALL] THEN
    EXISTS_TAC `x:real^3` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(t:real^3->bool) IN E` ASSUME_TAC THENL
   [EXPAND_TAC "E" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `aff_dim(t:real^3->bool) <= &1` MP_TAC THENL
     [USE_THEN "ld" (fun th -> MP_TAC(MATCH_MP th
        (ASSUME `(t:real^3->bool) IN L`))) THEN REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `~(aff_dim(t:real^3->bool) = -- &1)` MP_TAC THENL
     [REWRITE_TAC[AFF_DIM_EQ_MINUS1; GSYM MEMBER_NOT_EMPTY] THEN
      EXISTS_TAC `u:real^3` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `~(aff_dim(t:real^3->bool) = &0)` MP_TAC THENL
     [REWRITE_TAC[AFF_DIM_EQ_0] THEN
      DISCH_THEN(X_CHOOSE_THEN `v:real^3` SUBST_ALL_TAC) THEN
      UNDISCH_TAC `~(x:real^3 = u)` THEN
      UNDISCH_TAC `(x:real^3) IN {v}` THEN UNDISCH_TAC `(u:real^3) IN {v}` THEN
      REWRITE_TAC[IN_SING] THEN MESON_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPEC `t:real^3->bool` AFF_DIM_GE) THEN
    SPEC_TAC(`aff_dim(t:real^3->bool)`,`d:int`) THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "oth" (MP_TAC o C MATCH_MP (ASSUME `(t:real^3->bool) IN E`)) THEN
  STRIP_TAC THEN
  UNDISCH_TAC `(x:real^3) IN t` THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THEN
  REWRITE_TAC[IN_SEGMENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`(oth:(real^3->bool)->real^3) t - u`; `k:real`] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `t:real^3->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [ASM_CASES_TAC `k = &0` THENL
     [UNDISCH_TAC `~(x:real^3 = u)` THEN
      REWRITE_TAC[ASSUME `x = (&1 - k) % u + k % (oth:(real^3->bool)->real^3) t`;
                  ASSUME `k = &0`] THEN
      REWRITE_TAC[REAL_SUB_RZERO; VECTOR_MUL_LID; VECTOR_MUL_LZERO;
                  VECTOR_ADD_RID];
      ASM_REAL_ARITH_TAC];
    REWRITE_TAC[ASSUME `x = (&1 - k) % u + k % (oth:(real^3->bool)->real^3) t`] THEN
    VECTOR_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* 7. Rays in a triangle, crossing bounds from rays, link splitting along   *)
(* a fold, and transversality of a level link vertex on a surface.          *)
(* ------------------------------------------------------------------------- *)

let MOI_STL_SEGMENT_LEVEL_UNIQUE = prove
 (`!(a:real^3) p q x y.
     ~(a dot p = a dot q) /\ x IN segment[p,q] /\ y IN segment[p,q] /\
     a dot x = a dot y
     ==> x = y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_SEGMENT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `s:real` STRIP_ASSUME_TAC) (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC) MP_TAC))) THEN
  ASM_REWRITE_TAC[DOT_RADD; DOT_RMUL] THEN DISCH_TAC THEN
  SUBGOAL_THEN `s:real = t` SUBST1_TAC THENL
   [UNDISCH_TAC `~((a:real^3) dot p = a dot q)` THEN
    POP_ASSUM MP_TAC THEN CONV_TAC REAL_RING;
    REFL_TAC]);;

let MOI_STL_HALF_RAY_FACE = prove
 (`!tr fc (a:real^3) y.
     fc face_of tr /\ y IN fc /\ (!x. x IN fc /\ a dot x = a dot y ==> x = y) /\
     aff_dim (tr INTER {x | a dot x = a dot y}) <= &1
     ==> ?R. FINITE R /\ CARD R <= 1 /\
             !x. x IN tr /\ a dot x = a dot y /\ ~(x = y)
                 ==> ?d k. d IN R /\ &0 < k /\ x = y + k % d`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "uq") ASSUME_TAC))) THEN
  SUBGOAL_THEN `(fc:real^3->bool) SUBSET tr` ASSUME_TAC THENL
   [ASM_MESON_TAC[FACE_OF_IMP_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^3) IN tr` ASSUME_TAC THENL
   [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
  ASM_CASES_TAC `?x1:real^3. x1 IN tr /\ a dot x1 = a dot y /\ ~(x1 = y)` THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `x1:real^3` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `{x1 - y:real^3}` THEN
    REWRITE_TAC[FINITE_SING; CARD_SING; LE_REFL; IN_SING] THEN
    X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
    SUBGOAL_THEN `~(y:real^3 = x1)` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `collinear {y:real^3, x1, x}` MP_TAC THENL
     [REWRITE_TAC[COLLINEAR_AFF_DIM] THEN MATCH_MP_TAC INT_LE_TRANS THEN
      EXISTS_TAC `aff_dim(tr INTER {x:real^3 | a dot x = a dot y})` THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC AFF_DIM_SUBSET THEN
      REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET; IN_INTER; IN_ELIM_THM] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[MATCH_MP COLLINEAR_3_AFFINE_HULL (ASSUME `~(y:real^3 = x1)`);
                AFFINE_HULL_2_ALT] THEN
    REWRITE_TAC[IN_ELIM_THM; IN_UNIV] THEN
    DISCH_THEN(X_CHOOSE_THEN `l:real` SUBST_ALL_TAC) THEN
    ASM_CASES_TAC `l = &0` THENL
     [UNDISCH_TAC `~(y + l % (x1 - y):real^3 = y)` THEN
      ASM_REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_RID];
      ALL_TAC] THEN
    ASM_CASES_TAC `&0 < l` THENL
     [MAP_EVERY EXISTS_TAC [`x1 - y:real^3`; `l:real`] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC(TAUT `F ==> p`) THEN
    SUBGOAL_THEN `(y:real^3) IN segment(y + l % (x1 - y),x1)` ASSUME_TAC THENL
     [REWRITE_TAC[IN_SEGMENT] THEN CONJ_TAC THENL
       [REWRITE_TAC[VECTOR_ARITH
         `y + l % (x1 - y):real^3 = x1 <=> (&1 - l) % (x1 - y) = vec 0`] THEN
        REWRITE_TAC[VECTOR_MUL_EQ_0; VECTOR_SUB_EQ] THEN
        ASM_MESON_TAC[REAL_ARITH `~(&0 < l) ==> ~(&1 - l = &0)`];
        ALL_TAC] THEN
      EXISTS_TAC `--l / (&1 - l)` THEN
      SUBGOAL_THEN `&0 < &1 - l` ASSUME_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      CONJ_TAC THENL
       [REWRITE_TAC[MATCH_MP REAL_LT_LDIV_EQ (ASSUME `&0 < &1 - l`)] THEN
        ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      REWRITE_TAC[VECTOR_ARITH
       `(&1 - u) % (y + l % (x1 - y)) + u % x1:real^3 =
        y + ((&1 - u) * l + u) % (x1 - y)`] THEN
      SUBGOAL_THEN `(&1 - --l / (&1 - l)) * l + --l / (&1 - l) = &0`
        SUBST1_TAC THENL
       [UNDISCH_TAC `&0 < &1 - l` THEN CONV_TAC REAL_FIELD;
        VECTOR_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `(x1:real^3) IN fc` MP_TAC THENL
     [UNDISCH_TAC `(fc:real^3->bool) face_of tr` THEN
      REWRITE_TAC[face_of] THEN
      DISCH_THEN(MP_TAC o SPECL [`y + l % (x1 - y):real^3`; `x1:real^3`; `y:real^3`]
        o CONJUNCT2 o CONJUNCT2) THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[];
      ALL_TAC] THEN
    DISCH_TAC THEN UNDISCH_TAC `~(x1:real^3 = y)` THEN REWRITE_TAC[] THEN
    USE_THEN "uq" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    EXISTS_TAC `{}:real^3->bool` THEN
    REWRITE_TAC[FINITE_EMPTY; CARD_CLAUSES; LE_0] THEN
    ASM_MESON_TAC[]]);;

let MOI_STL_TRIANGLE_SIMPLEX = prove
 (`!A B C:real^3.
     ~affine_dependent {A,B,C} /\ ~(A = B) /\ ~(A = C) /\ ~(B = C)
     ==> &2 simplex (convex hull {A,B,C})`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[simplex] THEN
  EXISTS_TAC `{A:real^3,B,C}` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `CARD {A:real^3,B,C} = 3` SUBST1_TAC THENL
   [SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN
    ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN CONV_TAC NUM_REDUCE_CONV;
    INT_ARITH_TAC]);;

let MOI_STL_TRIANGLE_CORNERS = prove
 (`!t:real^3->bool.
     &2 simplex t
     ==> ?A B C. ~(A = B) /\ ~(A = C) /\ ~(B = C) /\
                 ~affine_dependent {A,B,C} /\ ~collinear {A,B,C} /\
                 t = convex hull {A,B,C}`,
  GEN_TAC THEN REWRITE_TAC[simplex] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^3->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(k:real^3->bool) HAS_SIZE 3` MP_TAC THENL
   [REWRITE_TAC[HAS_SIZE] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[AFFINE_INDEPENDENT_IMP_FINITE];
      UNDISCH_TAC `&(CARD(k:real^3->bool)):int = &2 + &1` THEN
      REWRITE_TAC[INT_OF_NUM_ADD; INT_OF_NUM_EQ] THEN ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[MOI_SCF_HAS_SIZE_3] THEN
  DISCH_THEN(X_CHOOSE_THEN `A:real^3` (X_CHOOSE_THEN `B:real^3`
    (X_CHOOSE_THEN `C:real^3` STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`A:real^3`; `B:real^3`; `C:real^3`] THEN
  UNDISCH_TAC `~affine_dependent (k:real^3->bool)` THEN ASM_REWRITE_TAC[] THEN
  SIMP_TAC[COLLINEAR_3_EQ_AFFINE_DEPENDENT] THEN ASM_REWRITE_TAC[]);;

let MOI_STL_TRIANGLE_LEVEL_DIM = prove
 (`!t A B (b:real^3) h.
     &2 simplex t /\ A IN t /\ B IN t /\ ~(b dot A = b dot B)
     ==> aff_dim (t INTER {x | b dot x = h}) <= &1`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[INT_ARITH `x:int <= &1 <=> ~(&2 <= x)`] THEN DISCH_TAC THEN
  SUBGOAL_THEN `aff_dim(t:real^3->bool) = &2` ASSUME_TAC THENL
   [ASM_MESON_TAC[AFF_DIM_SIMPLEX]; ALL_TAC] THEN
  MP_TAC(ISPECL [`t INTER {x:real^3 | b dot x = h}`; `t:real^3->bool`]
    AFF_DIM_EQ_AFFINE_HULL) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[INTER_SUBSET] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `affine hull (t INTER {x:real^3 | b dot x = h}) SUBSET {x | b dot x = h}`
  MP_TAC THENL
   [MATCH_MP_TAC HULL_MINIMAL THEN REWRITE_TAC[AFFINE_HYPERPLANE; INTER_SUBSET];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`affine:(real^3->bool)->bool`; `t:real^3->bool`] HULL_SUBSET) THEN
  UNDISCH_TAC `(A:real^3) IN t` THEN UNDISCH_TAC `(B:real^3) IN t` THEN
  UNDISCH_TAC `~((b:real^3) dot A = b dot B)` THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[]);;

let MOI_STL_TRIANGLE_INTERIOR_RAYS = prove
 (`!t A B (b:real^3) u.
     &2 simplex t /\ A IN t /\ B IN t /\ ~(b dot A = b dot B) /\ u IN t
     ==> ?R. FINITE R /\ CARD R <= 2 /\
             !x. x IN t /\ b dot x = b dot u /\ ~(x = u)
                 ==> ?d k. d IN R /\ &0 < k /\ x = u + k % d`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`t INTER {x:real^3 | b dot x = b dot u}`; `u:real^3`]
    MOI_STL_LINE_RAYS) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC MOI_STL_TRIANGLE_LEVEL_DIM THEN
      MAP_EVERY EXISTS_TAC [`A:real^3`; `B:real^3`] THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `R:real^3->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `R:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM]);;

let MOI_STL_TRIANGLE_BOUNDARY_RAY = prove
 (`!A B C (b:real^3) u.
     ~affine_dependent {A,B,C} /\
     ~(b dot A = b dot B) /\ ~(b dot A = b dot C) /\ ~(b dot B = b dot C) /\
     u IN relative_frontier(convex hull {A,B,C})
     ==> ?R. FINITE R /\ CARD R <= 1 /\
             !x. x IN convex hull {A,B,C} /\ b dot x = b dot u /\ ~(x = u)
                 ==> ?d k. d IN R /\ &0 < k /\ x = u + k % d`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(A:real^3 = B) /\ ~(A = C) /\ ~(B = C)` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~collinear {A:real^3,B,C}` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[COLLINEAR_3_EQ_AFFINE_DEPENDENT]; ALL_TAC] THEN
  SUBGOAL_THEN `&2 simplex (convex hull {A:real^3,B,C})` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_STL_TRIANGLE_SIMPLEX THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `aff_dim (convex hull {A:real^3,B,C} INTER {x | b dot x = b dot u})
                <= &1` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_STL_TRIANGLE_LEVEL_DIM THEN
    MAP_EVERY EXISTS_TAC [`A:real^3`; `B:real^3`] THEN
    ASM_SIMP_TAC[HULL_INC; IN_INSERT];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!P Q:real^3. P IN {A,B,C} /\ Q IN {A,B,C} /\ ~(b dot P = b dot Q) /\
                 u IN segment[P,Q]
                 ==> ?R. FINITE R /\ CARD R <= 1 /\
                         !x. x IN convex hull {A,B,C} /\ b dot x = b dot u /\
                             ~(x = u)
                             ==> ?d k. d IN R /\ &0 < k /\ x = u + k % d`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_STL_HALF_RAY_FACE THEN
    EXISTS_TAC `segment[P:real^3,Q]` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
      EXISTS_TAC `{P:real^3,Q}` THEN REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN
      ASM SET_TAC[];
      REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_STL_SEGMENT_LEVEL_UNIQUE THEN
      MAP_EVERY EXISTS_TAC [`b:real^3`; `P:real^3`; `Q:real^3`] THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  UNDISCH_TAC `(u:real^3) IN relative_frontier(convex hull {A,B,C})` THEN
  ASM_SIMP_TAC[RELATIVE_FRONTIER_OF_TRIANGLE; IN_UNION] THEN STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THENL
   [MAP_EVERY EXISTS_TAC [`A:real^3`; `B:real^3`];
    MAP_EVERY EXISTS_TAC [`B:real^3`; `C:real^3`];
    MAP_EVERY EXISTS_TAC [`C:real^3`; `A:real^3`]] THEN
  ASM_REWRITE_TAC[IN_INSERT] THEN ASM_MESON_TAC[]);;

let MOI_STL_LINK_LEVEL_RAYS = prove
 (`!K (u:real^3) (b:real^3) R r.
     simplicial_complex K /\ FINITE R /\ &0 < r /\
     (!x. x IN UNIONS K /\ b dot x = b dot u /\ dist(u,x) < r /\ ~(x = u)
          ==> ?d k. d IN R /\ &0 < k /\ x = u + k % d)
     ==> FINITE (UNIONS (simplicial_link K u) INTER {x | b dot x = b dot u}) /\
         CARD (UNIONS (simplicial_link K u) INTER {x | b dot x = b dot u})
         <= CARD R`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "rays")))) THEN
  MATCH_MP_TAC MOI_STL_RAY_COUNT THEN
  MAP_EVERY EXISTS_TAC [`K:(real^3->bool)->bool`; `u:real^3`] THEN
  ASM_REWRITE_TAC[INTER_SUBSET] THEN
  X_GEN_TAC `z:real^3` THEN REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`K:(real^3->bool)->bool`; `u:real^3`; `z:real^3`]
    MOI_STL_LINK_POINT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `tau:real^3->bool`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`u:real^3`; `z:real^3`; `r:real`] MOI_STL_SEGMENT_NEAR) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `(y:real^3) IN segment(u,z)` THEN REWRITE_TAC[IN_SEGMENT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `s:real`
    STRIP_ASSUME_TAC)) THEN
  USE_THEN "rays" (MP_TAC o SPEC `y:real^3`) THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `tau:real^3->bool` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IN_CONVEX_SET THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
      ASM_MESON_TAC[MOI_SLV_SC_BASIC];
      ASM_REWRITE_TAC[DOT_RADD; DOT_RMUL] THEN REAL_ARITH_TAC;
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[VECTOR_ARITH
       `(&1 - s) % u + s % z:real^3 = u <=> s % (z - u) = vec 0`] THEN
      ASM_REWRITE_TAC[VECTOR_MUL_EQ_0; VECTOR_SUB_EQ] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real^3` (X_CHOOSE_THEN `k:real`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`d:real^3`; `k / s`] THEN ASM_SIMP_TAC[REAL_LT_DIV] THEN
  SUBGOAL_THEN `s % (z - u:real^3) = s % ((k / s) % d)` MP_TAC THENL
   [REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
    SUBGOAL_THEN `s * k / s = k` SUBST1_TAC THENL
     [MATCH_MP_TAC REAL_DIV_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `y:real^3 = u + k % d` THEN
    ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[VECTOR_MUL_LCANCEL] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < s ==> ~(s = &0)`] THEN VECTOR_ARITH_TAC);;

let MOI_STL_CROSSINGS_RAYS = prove
 (`!K (u:real^3) (b:real^3) R r.
     simplicial_complex K /\ {u} IN K /\
     (!x. {x} IN K /\ ~(x = u) ==> ~(b dot x = b dot u)) /\
     FINITE R /\ &0 < r /\
     (!x. x IN UNIONS K /\ b dot x = b dot u /\ dist(u,x) < r /\ ~(x = u)
          ==> ?d k. d IN R /\ &0 < k /\ x = u + k % d)
     ==> moi_sch3_crossings K b u <= CARD R`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "gen") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "rays")))))) THEN
  MP_TAC(ISPECL [`K:(real^3->bool)->bool`; `u:real^3`; `b:real^3`;
                 `R:real^3->bool`; `r:real`] MOI_STL_LINK_LEVEL_RAYS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC `CARD (UNIONS (simplicial_link K u) INTER
                    {x:real^3 | b dot x = b dot u})` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_STL_CROSSINGS_LE THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!x:real^3. {x} IN simplicial_link K u ==> ~(b dot x = b dot u)`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^3` THEN REWRITE_TAC[simplicial_link; IN_ELIM_THM] THEN
    STRIP_TAC THEN USE_THEN "gen" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `~((u:real^3) IN {x})` THEN REWRITE_TAC[IN_SING] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `{x:real^3} IN simplicial_link K u` MP_TAC THENL
   [MATCH_MP_TAC MOI_STL_LINK_FACE_CLOSED THEN
    EXISTS_TAC `segment[x:real^3,y1]` THEN
    ASM_REWRITE_TAC[NOT_INSERT_EMPTY; FACE_OF_SING; EXTREME_POINT_OF_SEGMENT];
    DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o C MATCH_MP
      (ASSUME `{x:real^3} IN simplicial_link K u`)) THEN
    ASM_REWRITE_TAC[]]);;

let MOI_STL_SUBCOMPLEX = prove
 (`!K (X:real^N->bool).
     simplicial_complex K ==> simplicial_complex {s | s IN K /\ s SUBSET X}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_LFO_SUBCOMPLEX THEN
  EXISTS_TAC `K:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  CONJ_TAC THENL
   [ASM_MESON_TAC[MOI_SLV_SC_BASIC];
    ASM_MESON_TAC[FACE_OF_IMP_SUBSET; SUBSET_TRANS]]);;

let MOI_STL_LINK_SPLIT = prove
 (`!K X1 X2 (u:real^N) e.
     (!s. s IN K ==> s SUBSET X1 \/ s SUBSET X2) /\ e IN simplicial_link K u
     ==> e IN simplicial_link {s | s IN K /\ s SUBSET X1} u \/
         e IN simplicial_link {s | s IN K /\ s SUBSET X2} u`,
  REWRITE_TAC[simplicial_link; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FACE_OF_IMP_SUBSET) THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o C MATCH_MP (ASSUME `(t:real^N->bool) IN K`)) THENL
   [DISJ1_TAC; DISJ2_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  (CONJ_TAC THENL [ASM_MESON_TAC[SUBSET_TRANS]; ALL_TAC]) THEN
  EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[]);;

let MOI_STL_CROSSINGS_SPLIT = prove
 (`!K X1 X2 (u:real^3) (b:real^3).
     simplicial_complex K /\ (!s. s IN K ==> s SUBSET X1 \/ s SUBSET X2)
     ==> moi_sch3_crossings K b u <=
         moi_sch3_crossings {s | s IN K /\ s SUBSET X1} b u +
         moi_sch3_crossings {s | s IN K /\ s SUBSET X2} b u`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[moi_sch3_crossings] THEN
  ABBREV_TAC `P = \e:real^3->bool. ?x y. e = segment[x,y] /\ b dot x < b dot u /\
                                         b dot u < b dot y` THEN
  SUBGOAL_THEN
   `!L:(real^3->bool)->bool.
      {e | e IN simplicial_link L u /\
           ?x y. e = segment[x,y] /\ b dot x < b dot u /\ b dot u < b dot y} =
      {e | e IN simplicial_link L u /\ P e}`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN EXPAND_TAC "P" THEN REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!L:(real^3->bool)->bool. L SUBSET K ==> FINITE {e | e IN simplicial_link L u /\ P e}`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `K:(real^3->bool)->bool` THEN
    CONJ_TAC THENL [ASM_MESON_TAC[MOI_SLV_SC_BASIC]; ALL_TAC] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM; simplicial_link] THEN
    REPEAT STRIP_TAC THEN ASM_MESON_TAC[SUBSET];
    ALL_TAC] THEN
  MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC `CARD ({e | e IN simplicial_link {s | s IN K /\ s SUBSET X1} u /\
                         (P:(real^3->bool)->bool) e}
                    UNION
                    {e | e IN simplicial_link {s | s IN K /\ s SUBSET X2} u /\
                         P e})` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CARD_SUBSET THEN CONJ_TAC THENL
     [GEN_REWRITE_TAC I [SUBSET] THEN REWRITE_TAC[IN_UNION; IN_ELIM_THM] THEN
      X_GEN_TAC `e:real^3->bool` THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`K:(real^3->bool)->bool`; `X1:real^3->bool`;
                     `X2:real^3->bool`; `u:real^3`; `e:real^3->bool`]
        MOI_STL_LINK_SPLIT) THEN
      ASM_REWRITE_TAC[] THEN MESON_TAC[];
      MATCH_MP_TAC FINITE_UNION_IMP THEN CONJ_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN SET_TAC[]];
    MATCH_MP_TAC CARD_UNION_LE THEN CONJ_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN SET_TAC[]]);;

let MOI_STL_JOIN_CONVEX_SUBSET = prove
 (`!H (u:real^3) z y.
     convex H /\ u IN H /\ z IN H /\ y IN H
     ==> segment[u,z] SUBSET H /\ convex hull (u INSERT segment[z,y]) SUBSET H`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN
  MATCH_MP_TAC HULL_MINIMAL THEN ASM_REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET] THEN
  MATCH_MP_TAC HULL_MINIMAL THEN ASM_REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET]);;

let MOI_STL_JOIN_LOCAL = prove
 (`!H (u:real^3) z y1 y2 x.
     convex H /\ u IN H /\ z IN H /\ y1 IN H /\ y2 IN H /\
     (x IN segment[u,z] \/ x IN convex hull (u INSERT segment[z,y1]) \/
      x IN convex hull (u INSERT segment[z,y2]))
     ==> x IN H`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`H:real^3->bool`; `u:real^3`; `z:real^3`; `y1:real^3`]
    MOI_STL_JOIN_CONVEX_SUBSET) THEN
  MP_TAC(ISPECL [`H:real^3->bool`; `u:real^3`; `z:real^3`; `y2:real^3`]
    MOI_STL_JOIN_CONVEX_SUBSET) THEN
  ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

let MOI_STL_TRANSVERSAL_LINK = prove
 (`!K (u:real^3) z y1 y2 (a:real^3) m.
     simplicial_complex K /\ pl_sphere 2 (UNIONS K) /\ {u} IN K /\
     segment[z,y1] IN simplicial_link K u /\
     segment[z,y2] IN simplicial_link K u /\
     ~(y1 = z) /\ ~(y2 = z) /\ ~(y1 = y2) /\ a dot z = a dot u /\
     ~(a dot y1 = a dot u) /\ ~(a dot y2 = a dot u) /\
     m IN segment(u,z) /\
     (!r. &0 < r ==> ?x. x IN UNIONS K /\ dist(m,x) < r /\ a dot x < a dot u) /\
     (!r. &0 < r ==> ?x. x IN UNIONS K /\ dist(m,x) < r /\ a dot u < a dot x)
     ==> (a dot y1 < a dot u <=> a dot u < a dot y2)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (LABEL_TAC "below") (LABEL_TAC "above")))))))))))))) THEN
  SUBGOAL_THEN `~(u:real^3 = z)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC `(m:real^3) IN segment(z,z)` THEN
    REWRITE_TAC[SEGMENT_REFL; NOT_IN_EMPTY];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(z:real^3 = y1) /\ ~(z = y2)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SLV_SC_BASIC) THEN
  MP_TAC(ISPEC `K:(real^3->bool)->bool` MOI_SLV_SPHERE_SURFACE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "dim2") (LABEL_TAC "two")) THEN
  ABBREV_TAC `T1 = convex hull (u INSERT segment[z:real^3,y1])` THEN
  ABBREV_TAC `T2 = convex hull (u INSERT segment[z:real^3,y2])` THEN
  MP_TAC(ISPECL [`K:(real^3->bool)->bool`; `u:real^3`; `segment[z:real^3,y1]`]
    MOI_SCF_LINK_JOIN) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`K:(real^3->bool)->bool`; `u:real^3`; `segment[z:real^3,y2]`]
    MOI_SCF_LINK_JOIN) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `aff_dim(T1:real^3->bool) = &2 /\ aff_dim(T2:real^3->bool) = &2`
    STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN REWRITE_TAC[AFF_DIM_SEGMENT] THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC INT_REDUCE_CONV;
    ALL_TAC] THEN
  UNDISCH_THEN `aff_dim(T1:real^3->bool) = aff_dim(segment[z:real^3,y1]) + &1`
    (K ALL_TAC) THEN
  UNDISCH_THEN `aff_dim(T2:real^3->bool) = aff_dim(segment[z:real^3,y2]) + &1`
    (K ALL_TAC) THEN
  SUBGOAL_THEN `{z:real^3} IN simplicial_link K u` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_STL_LINK_FACE_CLOSED THEN
    EXISTS_TAC `segment[z:real^3,y1]` THEN
    ASM_REWRITE_TAC[NOT_INSERT_EMPTY; FACE_OF_SING; EXTREME_POINT_OF_SEGMENT];
    ALL_TAC] THEN
  SUBGOAL_THEN `segment[u:real^3,z] IN K` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`K:(real^3->bool)->bool`; `u:real^3`; `{z:real^3}`]
      MOI_SCF_LINK_JOIN) THEN
    ASM_REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(T1:real^3->bool = T2)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    MP_TAC(ISPECL [`K:(real^3->bool)->bool`; `u:real^3`; `segment[z:real^3,y1]`;
                   `segment[z:real^3,y2]`] MOI_SCF_LINK_JOIN_INJ) THEN
    ASM_REWRITE_TAC[SEGMENT_EQ] THEN
    UNDISCH_TAC `~(y1:real^3 = y2)` THEN UNDISCH_TAC `~(y1:real^3 = z)` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `segment[u:real^3,z] SUBSET T1 /\ segment[u,z] SUBSET T2`
    STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN
    MATCH_MP_TAC HULL_MINIMAL THEN
    REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET] THEN
    MAP_EVERY EXPAND_TAC ["T1"; "T2"] THEN
    SIMP_TAC[CONVEX_CONVEX_HULL; HULL_INC; IN_INSERT; ENDS_IN_SEGMENT];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t:real^3->bool. t IN K /\ aff_dim t = &2 /\ segment[u,z] SUBSET t
                     ==> t = T1 \/ t = T2`
  (LABEL_TAC "t12") THENL
   [SUBGOAL_THEN
     `{t:real^3->bool | t IN K /\ aff_dim t = &2 /\ segment[u,z] SUBSET t}
      HAS_SIZE 2` MP_TAC THENL
     [REWRITE_TAC[HAS_SIZE] THEN CONJ_TAC THENL
       [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `K:(real^3->bool)->bool` THEN
        ASM_REWRITE_TAC[] THEN SET_TAC[];
        USE_THEN "two" MATCH_MP_TAC THEN ASM_REWRITE_TAC[AFF_DIM_SEGMENT]];
      ALL_TAC] THEN
    REWRITE_TAC[MOI_SCF_HAS_SIZE_2] THEN
    DISCH_THEN(X_CHOOSE_THEN `p1:real^3->bool` (X_CHOOSE_THEN `p2:real^3->bool`
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "seteq")))) THEN
    SUBGOAL_THEN `(T1:real^3->bool) IN {p1,p2} /\ (T2:real^3->bool) IN {p1,p2}`
    MP_TAC THENL
     [USE_THEN "seteq" (SUBST1_TAC o SYM) THEN REWRITE_TAC[IN_ELIM_THM] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
    X_GEN_TAC `t:real^3->bool` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(t:real^3->bool) IN {p1,p2}` MP_TAC THENL
     [USE_THEN "seteq" (SUBST1_TAC o SYM) THEN REWRITE_TAC[IN_ELIM_THM] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
    UNDISCH_TAC `~(T1:real^3->bool = T2)` THEN
    UNDISCH_TAC `(T1:real^3->bool) = p1 \/ T1 = p2` THEN
    UNDISCH_TAC `(T2:real^3->bool) = p1 \/ T2 = p2` THEN
    MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`K:(real^3->bool)->bool`; `m:real^3`] MOI_SLV_LOCAL_BALL) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "lb"))) THEN
  SUBGOAL_THEN
   `!x:real^3. x IN UNIONS K /\ dist(m,x) < r0
               ==> x IN segment[u,z] \/ x IN T1 \/ x IN T2`
  (LABEL_TAC "loc") THENL
   [X_GEN_TAC `x:real^3` THEN REWRITE_TAC[IN_UNIONS] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `sg:real^3->bool`
      STRIP_ASSUME_TAC) ASSUME_TAC) THEN
    SUBGOAL_THEN `(m:real^3) IN sg` ASSUME_TAC THENL
     [USE_THEN "lb" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_BALL] THEN
      EXISTS_TAC `x:real^3` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `segment[u:real^3,z] SUBSET sg` ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_SCF_RELINT_SUBSET THEN
      MAP_EVERY EXISTS_TAC [`K:(real^3->bool)->bool`; `m:real^3`] THEN
      ASM_REWRITE_TAC[RELATIVE_INTERIOR_SEGMENT];
      ALL_TAC] THEN
    SUBGOAL_THEN `aff_dim(sg:real^3->bool) <= &2` ASSUME_TAC THENL
     [USE_THEN "dim2" (fun th -> MP_TAC(MATCH_MP th
        (ASSUME `(sg:real^3->bool) IN K`))) THEN REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`segment[u:real^3,z]`; `sg:real^3->bool`] AFF_DIM_SUBSET) THEN
    ASM_REWRITE_TAC[AFF_DIM_SEGMENT] THEN DISCH_TAC THEN
    ASM_CASES_TAC `aff_dim(sg:real^3->bool) = &2` THENL
     [USE_THEN "t12" (MP_TAC o C MATCH_MP (CONJ (ASSUME `(sg:real^3->bool) IN K`)
        (CONJ (ASSUME `aff_dim(sg:real^3->bool) = &2`)
              (ASSUME `segment[u:real^3,z] SUBSET sg`)))) THEN
      STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_REWRITE_TAC[];
      SUBGOAL_THEN `segment[u:real^3,z] = sg` (fun th -> ASM_REWRITE_TAC[th]) THEN
      MATCH_MP_TAC MOI_SCF_SUBSET_DIM_EQ THEN
      EXISTS_TAC `K:(real^3->bool)->bool` THEN ASM_REWRITE_TAC[AFF_DIM_SEGMENT] THEN
      UNDISCH_TAC `~(aff_dim(sg:real^3->bool) = &2)` THEN
      UNDISCH_TAC `aff_dim(sg:real^3->bool) <= &2` THEN
      UNDISCH_TAC `&1 <= aff_dim(sg:real^3->bool)` THEN INT_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((a:real^3) dot u < a dot y1 /\ a dot u < a dot y2)` ASSUME_TAC THENL
   [STRIP_TAC THEN
    USE_THEN "below" (MP_TAC o C MATCH_MP (ASSUME `&0 < r0`)) THEN
    DISCH_THEN(X_CHOOSE_THEN `x:real^3` STRIP_ASSUME_TAC) THEN
    MP_TAC(REWRITE_RULE[IN_ELIM_THM; real_ge;
                        ASSUME `convex hull (u INSERT segment[z:real^3,y1]) = T1`;
                        ASSUME `convex hull (u INSERT segment[z:real^3,y2]) = T2`]
     (REWRITE_RULE[CONVEX_HALFSPACE_GE]
      (ISPECL [`{x:real^3 | a dot x >= a dot u}`; `u:real^3`; `z:real^3`;
               `y1:real^3`; `y2:real^3`; `x:real^3`] MOI_STL_JOIN_LOCAL))) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
        USE_THEN "loc" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((a:real^3) dot y1 < a dot u /\ a dot y2 < a dot u)` ASSUME_TAC THENL
   [STRIP_TAC THEN
    USE_THEN "above" (MP_TAC o C MATCH_MP (ASSUME `&0 < r0`)) THEN
    DISCH_THEN(X_CHOOSE_THEN `x:real^3` STRIP_ASSUME_TAC) THEN
    MP_TAC(REWRITE_RULE[IN_ELIM_THM;
                        ASSUME `convex hull (u INSERT segment[z:real^3,y1]) = T1`;
                        ASSUME `convex hull (u INSERT segment[z:real^3,y2]) = T2`]
     (REWRITE_RULE[CONVEX_HALFSPACE_LE]
      (ISPECL [`{x:real^3 | a dot x <= a dot u}`; `u:real^3`; `z:real^3`;
               `y1:real^3`; `y2:real^3`; `x:real^3`] MOI_STL_JOIN_LOCAL))) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
        USE_THEN "loc" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  UNDISCH_TAC `~((a:real^3) dot y1 = a dot u)` THEN
  UNDISCH_TAC `~((a:real^3) dot y2 = a dot u)` THEN
  UNDISCH_TAC `~((a:real^3) dot u < a dot y1 /\ a dot u < a dot y2)` THEN
  UNDISCH_TAC `~((a:real^3) dot y1 < a dot u /\ a dot y2 < a dot u)` THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* 8. Crossing bounds at the vertices of a cap triangulation: vertices of   *)
(* the disk off the triangle (transported level rays and transversality),   *)
(* vertices inside the triangle, vertices on its boundary (split along the  *)
(* fold, evenness), and far vertices (comparison with the sphere).           *)
(* ------------------------------------------------------------------------- *)

let MOI_STL_IMAGE_SIDES = prove
 (`!c (a:real^3) (f:real^3->real^3) g x.
     moi_sch3_generic c a /\
     pl_homeomorphism ((:real^3),(:real^3)) (f,g) /\ (!x. a dot f x = a dot x) /\
     x IN IMAGE f (UNIONS c) /\ ~({g x} IN c)
     ==> (!e. &0 < e ==> ?y. y IN IMAGE f (UNIONS c) /\ dist(x,y) < e /\
                             a dot x < a dot y) /\
         (!e. &0 < e ==> ?y. y IN IMAGE f (UNIONS c) /\ dist(x,y) < e /\
                             a dot y < a dot x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(g:real^3->real^3) x IN UNIONS c /\ (f:real^3->real^3) (g x) = x`
    STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(x:real^3) IN IMAGE (f:real^3->real^3) (UNIONS c)` THEN
    REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `x0:real^3` STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC `pl_homeomorphism ((:real^3),(:real^3)) (f:real^3->real^3,g)` THEN
    REWRITE_TAC[pl_homeomorphism; homeomorphism; IN_UNIV] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(a:real^3) dot (g:real^3->real^3) x = a dot x` ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [SYM th]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `a:real^3`; `(g:real^3->real^3) x`]
    MOI_STL_TRANSVERSE_ANY) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `w1:real^3` STRIP_ASSUME_TAC)
    (X_CHOOSE_THEN `w2:real^3` STRIP_ASSUME_TAC)) THEN
  CONJ_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THENL
   [MP_TAC(ISPECL [`UNIONS c:real^3->bool`; `f:real^3->real^3`; `g:real^3->real^3`;
                   `a:real^3`; `(g:real^3->real^3) x`; `w1:real^3`;
                   `(a:real^3) dot (g:real^3->real^3) x`; `e:real`]
      MOI_STL_IMAGE_NEAR_SIDE) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    MP_TAC(ISPECL [`UNIONS c:real^3->bool`; `f:real^3->real^3`; `g:real^3->real^3`;
                   `--a:real^3`; `(g:real^3->real^3) x`; `w2:real^3`;
                   `(--a:real^3) dot (g:real^3->real^3) x`; `e:real`]
      MOI_STL_IMAGE_NEAR_SIDE) THEN
    ASM_REWRITE_TAC[DOT_LNEG; REAL_LT_NEG2] THEN MESON_TAC[]]);;

let MOI_STL_LEVEL_EDGE_INFINITE = prove
 (`!K (u:real^3) (a:real^3) x y.
     segment[x,y] IN simplicial_link K u /\ a dot x = a dot u /\
     a dot y = a dot u /\ ~(x = y)
     ==> ~FINITE (UNIONS (simplicial_link K u) INTER {z | a dot z = a dot u})`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `FINITE(segment[x:real^3,y])` MP_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `UNIONS (simplicial_link K u) INTER {z:real^3 | a dot z = a dot u}` THEN
    ASM_REWRITE_TAC[SUBSET_INTER] THEN CONJ_TAC THENL
     [MATCH_MP_TAC(SET_RULE
       `!s k:(real^3->bool)->bool. s IN k ==> s SUBSET UNIONS k`) THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN MATCH_MP_TAC HULL_MINIMAL THEN
      REWRITE_TAC[CONVEX_HYPERPLANE; INSERT_SUBSET; EMPTY_SUBSET; IN_ELIM_THM] THEN
      ASM_REWRITE_TAC[]];
    ASM_REWRITE_TAC[FINITE_SEGMENT]]);;

let MOI_STL_EDGE_STAR = prove
 (`!K (u:real^3) z y1 y2 m.
     simplicial_complex K /\ pl_sphere 2 (UNIONS K) /\ {u} IN K /\
     segment[z,y1] IN simplicial_link K u /\
     segment[z,y2] IN simplicial_link K u /\
     ~(y1 = z) /\ ~(y2 = z) /\ ~(y1 = y2) /\ m IN segment(u,z)
     ==> ?r0. &0 < r0 /\
              !x. x IN UNIONS K /\ dist(m,x) < r0
                  ==> x IN segment[u,z] \/
                      x IN convex hull (u INSERT segment[z,y1]) \/
                      x IN convex hull (u INSERT segment[z,y2])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(u:real^3 = z)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC `(m:real^3) IN segment(z,z)` THEN
    REWRITE_TAC[SEGMENT_REFL; NOT_IN_EMPTY];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(z:real^3 = y1) /\ ~(z = y2)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SLV_SC_BASIC) THEN
  MP_TAC(ISPEC `K:(real^3->bool)->bool` MOI_SLV_SPHERE_SURFACE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "dim2") (LABEL_TAC "two")) THEN
  ABBREV_TAC `T1 = convex hull (u INSERT segment[z:real^3,y1])` THEN
  ABBREV_TAC `T2 = convex hull (u INSERT segment[z:real^3,y2])` THEN
  MP_TAC(ISPECL [`K:(real^3->bool)->bool`; `u:real^3`; `segment[z:real^3,y1]`]
    MOI_SCF_LINK_JOIN) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`K:(real^3->bool)->bool`; `u:real^3`; `segment[z:real^3,y2]`]
    MOI_SCF_LINK_JOIN) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `aff_dim(T1:real^3->bool) = &2 /\ aff_dim(T2:real^3->bool) = &2`
    STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN REWRITE_TAC[AFF_DIM_SEGMENT] THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC INT_REDUCE_CONV;
    ALL_TAC] THEN
  UNDISCH_THEN `aff_dim(T1:real^3->bool) = aff_dim(segment[z:real^3,y1]) + &1`
    (K ALL_TAC) THEN
  UNDISCH_THEN `aff_dim(T2:real^3->bool) = aff_dim(segment[z:real^3,y2]) + &1`
    (K ALL_TAC) THEN
  SUBGOAL_THEN `{z:real^3} IN simplicial_link K u` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_STL_LINK_FACE_CLOSED THEN
    EXISTS_TAC `segment[z:real^3,y1]` THEN
    ASM_REWRITE_TAC[NOT_INSERT_EMPTY; FACE_OF_SING; EXTREME_POINT_OF_SEGMENT];
    ALL_TAC] THEN
  SUBGOAL_THEN `segment[u:real^3,z] IN K` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`K:(real^3->bool)->bool`; `u:real^3`; `{z:real^3}`]
      MOI_SCF_LINK_JOIN) THEN
    ASM_REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(T1:real^3->bool = T2)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    MP_TAC(ISPECL [`K:(real^3->bool)->bool`; `u:real^3`; `segment[z:real^3,y1]`;
                   `segment[z:real^3,y2]`] MOI_SCF_LINK_JOIN_INJ) THEN
    ASM_REWRITE_TAC[SEGMENT_EQ] THEN
    UNDISCH_TAC `~(y1:real^3 = y2)` THEN UNDISCH_TAC `~(y1:real^3 = z)` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `segment[u:real^3,z] SUBSET T1 /\ segment[u,z] SUBSET T2`
    STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN
    MATCH_MP_TAC HULL_MINIMAL THEN
    REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET] THEN
    MAP_EVERY EXPAND_TAC ["T1"; "T2"] THEN
    SIMP_TAC[CONVEX_CONVEX_HULL; HULL_INC; IN_INSERT; ENDS_IN_SEGMENT];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t:real^3->bool. t IN K /\ aff_dim t = &2 /\ segment[u,z] SUBSET t
                     ==> t = T1 \/ t = T2`
  (LABEL_TAC "t12") THENL
   [SUBGOAL_THEN
     `{t:real^3->bool | t IN K /\ aff_dim t = &2 /\ segment[u,z] SUBSET t}
      HAS_SIZE 2` MP_TAC THENL
     [REWRITE_TAC[HAS_SIZE] THEN CONJ_TAC THENL
       [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `K:(real^3->bool)->bool` THEN
        ASM_REWRITE_TAC[] THEN SET_TAC[];
        USE_THEN "two" MATCH_MP_TAC THEN ASM_REWRITE_TAC[AFF_DIM_SEGMENT]];
      ALL_TAC] THEN
    REWRITE_TAC[MOI_SCF_HAS_SIZE_2] THEN
    DISCH_THEN(X_CHOOSE_THEN `p1:real^3->bool` (X_CHOOSE_THEN `p2:real^3->bool`
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "seteq")))) THEN
    SUBGOAL_THEN `(T1:real^3->bool) IN {p1,p2} /\ (T2:real^3->bool) IN {p1,p2}`
    MP_TAC THENL
     [USE_THEN "seteq" (SUBST1_TAC o SYM) THEN REWRITE_TAC[IN_ELIM_THM] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
    X_GEN_TAC `t:real^3->bool` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(t:real^3->bool) IN {p1,p2}` MP_TAC THENL
     [USE_THEN "seteq" (SUBST1_TAC o SYM) THEN REWRITE_TAC[IN_ELIM_THM] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
    UNDISCH_TAC `~(T1:real^3->bool = T2)` THEN
    UNDISCH_TAC `(T1:real^3->bool) = p1 \/ T1 = p2` THEN
    UNDISCH_TAC `(T2:real^3->bool) = p1 \/ T2 = p2` THEN
    MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`K:(real^3->bool)->bool`; `m:real^3`] MOI_SLV_LOCAL_BALL) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "lb"))) THEN
  SUBGOAL_THEN
   `!x:real^3. x IN UNIONS K /\ dist(m,x) < r0
               ==> x IN segment[u,z] \/ x IN T1 \/ x IN T2`
  (LABEL_TAC "loc") THENL
   [X_GEN_TAC `x:real^3` THEN REWRITE_TAC[IN_UNIONS] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `sg:real^3->bool`
      STRIP_ASSUME_TAC) ASSUME_TAC) THEN
    SUBGOAL_THEN `(m:real^3) IN sg` ASSUME_TAC THENL
     [USE_THEN "lb" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_BALL] THEN
      EXISTS_TAC `x:real^3` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `segment[u:real^3,z] SUBSET sg` ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_SCF_RELINT_SUBSET THEN
      MAP_EVERY EXISTS_TAC [`K:(real^3->bool)->bool`; `m:real^3`] THEN
      ASM_REWRITE_TAC[RELATIVE_INTERIOR_SEGMENT];
      ALL_TAC] THEN
    SUBGOAL_THEN `aff_dim(sg:real^3->bool) <= &2` ASSUME_TAC THENL
     [USE_THEN "dim2" (fun th -> MP_TAC(MATCH_MP th
        (ASSUME `(sg:real^3->bool) IN K`))) THEN REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`segment[u:real^3,z]`; `sg:real^3->bool`] AFF_DIM_SUBSET) THEN
    ASM_REWRITE_TAC[AFF_DIM_SEGMENT] THEN DISCH_TAC THEN
    ASM_CASES_TAC `aff_dim(sg:real^3->bool) = &2` THENL
     [USE_THEN "t12" (MP_TAC o C MATCH_MP (CONJ (ASSUME `(sg:real^3->bool) IN K`)
        (CONJ (ASSUME `aff_dim(sg:real^3->bool) = &2`)
              (ASSUME `segment[u:real^3,z] SUBSET sg`)))) THEN
      STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_REWRITE_TAC[];
      SUBGOAL_THEN `segment[u:real^3,z] = sg` (fun th -> ASM_REWRITE_TAC[th]) THEN
      MATCH_MP_TAC MOI_SCF_SUBSET_DIM_EQ THEN
      EXISTS_TAC `K:(real^3->bool)->bool` THEN ASM_REWRITE_TAC[AFF_DIM_SEGMENT] THEN
      UNDISCH_TAC `~(aff_dim(sg:real^3->bool) = &2)` THEN
      UNDISCH_TAC `aff_dim(sg:real^3->bool) <= &2` THEN
      UNDISCH_TAC `&1 <= aff_dim(sg:real^3->bool)` THEN INT_ARITH_TAC];
    ALL_TAC] THEN
  EXISTS_TAC `r0:real` THEN ASM_REWRITE_TAC[] THEN
  USE_THEN "loc" MATCH_ACCEPT_TAC);;

let MOI_STL_FOLD_SIDE_EDGE = prove
 (`!K (u:real^3) x y1 y2 D t m.
     simplicial_complex K /\ pl_sphere 2 (UNIONS K) /\ {u} IN K /\
     segment[x,y1] IN simplicial_link K u /\
     segment[x,y2] IN simplicial_link K u /\
     ~(y1 = x) /\ ~(y2 = x) /\ ~(y1 = y2) /\ m IN segment(u,x) /\
     convex hull (u INSERT segment[x,y1]) SUBSET D /\
     convex hull (u INSERT segment[x,y2]) SUBSET D /\
     convex t /\ closed t /\ t SUBSET UNIONS K /\
     D INTER t SUBSET relative_frontier t /\ m IN t
     ==> F`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`K:(real^3->bool)->bool`; `u:real^3`; `x:real^3`; `y1:real^3`;
                 `y2:real^3`; `m:real^3`] MOI_STL_EDGE_STAR) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "st"))) THEN
  SUBGOAL_THEN `segment[u:real^3,x] SUBSET D` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `convex hull (u INSERT segment[x:real^3,y1])` THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`convex hull (u INSERT segment[x:real^3,y1])`; `u:real^3`;
                   `x:real^3`; `y1:real^3`] MOI_STL_JOIN_CONVEX_SUBSET) THEN
    SIMP_TAC[CONVEX_CONVEX_HULL; HULL_INC; IN_INSERT; ENDS_IN_SEGMENT];
    ALL_TAC] THEN
  SUBGOAL_THEN `(m:real^3) IN closure(relative_interior t)` MP_TAC THENL
   [ASM_SIMP_TAC[CONVEX_CLOSURE_RELATIVE_INTERIOR; CLOSURE_CLOSED]; ALL_TAC] THEN
  REWRITE_TAC[CLOSURE_APPROACHABLE] THEN DISCH_THEN(MP_TAC o SPEC `r0:real`) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(w:real^3) IN t` ASSUME_TAC THENL
   [ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `(w:real^3) IN D` ASSUME_TAC THENL
   [USE_THEN "st" (MP_TAC o SPEC `w:real^3`) THEN ANTS_TAC THENL
     [CONJ_TAC THENL
       [ASM_MESON_TAC[SUBSET]; ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    ASM_MESON_TAC[SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN `(w:real^3) IN relative_frontier t` MP_TAC THENL
   [ASM_MESON_TAC[SUBSET; IN_INTER]; ALL_TAC] THEN
  REWRITE_TAC[relative_frontier; IN_DIFF] THEN ASM_REWRITE_TAC[]);;

let MOI_STL_BOUND_D = prove
 (`!c (a:real^3) (f:real^3->real^3) g K (b:real^3) u r0.
     moi_sch3_generic c a /\ pl_sphere 2 (UNIONS c) /\
     pl_homeomorphism ((:real^3),(:real^3)) (f,g) /\ (!x. a dot f x = a dot x) /\
     simplicial_complex K /\ pl_sphere 2 (UNIONS K) /\ {u} IN K /\
     (!x. {x} IN K /\ ~(x = u) ==> ~(b dot x = b dot u)) /\
     (!x. {x} IN K ==> (a dot x < a dot u ==> b dot x < b dot u) /\
                       (a dot u < a dot x ==> b dot u < b dot x)) /\
     &0 < r0 /\
     (!x. dist(u,x) < r0 ==> (x IN UNIONS K <=> x IN IMAGE f (UNIONS c))) /\
     (!x. x IN IMAGE f (UNIONS c) /\ dist(u,x) < r0 /\ a dot x = a dot u
          ==> ~({g x} IN c))
     ==> moi_sch3_crossings K b u <= 2`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "gen") (CONJUNCTS_THEN2 (LABEL_TAC "sgn") (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "loc") (LABEL_TAC "nv")))))))))))) THEN
  SUBGOAL_THEN `dist(u:real^3,u) < r0` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[DIST_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN `(u:real^3) IN UNIONS K` ASSUME_TAC THENL
   [REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `{u:real^3}` THEN
    ASM_REWRITE_TAC[IN_SING];
    ALL_TAC] THEN
  SUBGOAL_THEN `(u:real^3) IN IMAGE (f:real^3->real^3) (UNIONS c)` ASSUME_TAC THENL
   [USE_THEN "loc" (MP_TAC o C MATCH_MP (ASSUME `dist(u:real^3,u) < r0`)) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(g:real^3->real^3) u IN UNIONS c /\ (f:real^3->real^3) (g u) = u`
    STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(u:real^3) IN IMAGE (f:real^3->real^3) (UNIONS c)` THEN
    REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `x0:real^3` STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC `pl_homeomorphism ((:real^3),(:real^3)) (f:real^3->real^3,g)` THEN
    REWRITE_TAC[pl_homeomorphism; homeomorphism; IN_UNIV] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(a:real^3) dot (g:real^3->real^3) u = a dot u` ASSUME_TAC THENL
   [MP_TAC(SPEC `(g:real^3->real^3) u`
      (ASSUME `!x. (a:real^3) dot (f:real^3->real^3) x = a dot x`)) THEN
    REWRITE_TAC[ASSUME `(f:real^3->real^3) ((g:real^3->real^3) u) = u`] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~({(g:real^3->real^3) u} IN c)` ASSUME_TAC THENL
   [USE_THEN "nv" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `a:real^3`; `(g:real^3->real^3) u`]
    MOI_STL_NONVERTEX_RAYS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `R:real^3->bool` (X_CHOOSE_THEN `r:real`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`UNIONS c:real^3->bool`; `f:real^3->real^3`; `g:real^3->real^3`;
                 `a:real^3`; `(g:real^3->real^3) u`; `R:real^3->bool`; `r:real`]
    MOI_STL_RAYS_TRANSPORT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `R':real^3->bool` (X_CHOOSE_THEN `r':real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "rays")))))) THEN
  MP_TAC(ISPECL [`K:(real^3->bool)->bool`; `u:real^3`; `a:real^3`;
                 `R':real^3->bool`; `min r' r0`] MOI_STL_LINK_LEVEL_RAYS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_LT_MIN] THEN X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
    USE_THEN "rays" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "loc" (fun th -> MP_TAC(MATCH_MP th
      (ASSUME `dist(u:real^3,x) < r0`))) THEN
    ASM_REWRITE_TAC[];
    STRIP_TAC] THEN
  MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC `CARD (UNIONS (simplicial_link K u) INTER
                    {x:real^3 | a dot x = a dot u})` THEN
  CONJ_TAC THENL [ALL_TAC; ASM_ARITH_TAC] THEN
  MATCH_MP_TAC MOI_STL_CROSSINGS_LE THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `x:real^3` THEN
    REWRITE_TAC[simplicial_link; IN_ELIM_THM; IN_SING] THEN STRIP_TAC THEN
    CONJ_TAC THENL
     [USE_THEN "gen" MATCH_MP_TAC THEN ASM_MESON_TAC[];
      USE_THEN "sgn" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`x:real^3`; `y1:real^3`; `y2:real^3`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(x:real^3) IN UNIONS (simplicial_link K u)` ASSUME_TAC THENL
   [REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `segment[x:real^3,y1]` THEN
    ASM_REWRITE_TAC[ENDS_IN_SEGMENT];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`K:(real^3->bool)->bool`; `u:real^3`; `x:real^3`]
    MOI_STL_LINK_POINT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `tau:real^3->bool`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`u:real^3`; `x:real^3`; `r0 / &2`] MOI_STL_SEGMENT_NEAR) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(a:real^3) dot m = a dot u /\ (m:real^3) IN tau` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(m:real^3) IN segment(u,x)` THEN REWRITE_TAC[IN_SEGMENT] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `s:real`
      STRIP_ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[DOT_RADD; DOT_RMUL] THEN CONJ_TAC THENL
     [REAL_ARITH_TAC;
      MATCH_MP_TAC IN_CONVEX_SET THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
      ASM_MESON_TAC[MOI_SLV_SC_BASIC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(m:real^3) IN UNIONS K` ASSUME_TAC THENL
   [REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `tau:real^3->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `dist(u:real^3,m) < r0` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(m:real^3) IN IMAGE (f:real^3->real^3) (UNIONS c)` ASSUME_TAC THENL
   [USE_THEN "loc" (fun th -> MP_TAC(MATCH_MP th
      (ASSUME `dist(u:real^3,m) < r0`))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `a:real^3`; `f:real^3->real^3`;
                 `g:real^3->real^3`; `m:real^3`] MOI_STL_IMAGE_SIDES) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN USE_THEN "nv" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "up") (LABEL_TAC "dn")) THEN
  MATCH_MP_TAC MOI_STL_TRANSVERSAL_LINK THEN
  MAP_EVERY EXISTS_TAC [`K:(real^3->bool)->bool`; `x:real^3`; `m:real^3`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [DISCH_TAC THEN
    MP_TAC(ISPECL [`K:(real^3->bool)->bool`; `u:real^3`; `a:real^3`; `x:real^3`;
                   `y1:real^3`] MOI_STL_LEVEL_EDGE_INFINITE) THEN
    ASM_MESON_TAC[];
    DISCH_TAC THEN
    MP_TAC(ISPECL [`K:(real^3->bool)->bool`; `u:real^3`; `a:real^3`; `x:real^3`;
                   `y2:real^3`] MOI_STL_LEVEL_EDGE_INFINITE) THEN
    ASM_MESON_TAC[];
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    USE_THEN "dn" (MP_TAC o SPEC `min e (r0 / &2)`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `w:real^3` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `w:real^3` THEN CONJ_TAC THENL
     [SUBGOAL_THEN `dist(u:real^3,w) < r0` ASSUME_TAC THENL
       [UNDISCH_TAC `dist(m:real^3,w) < min e (r0 / &2)` THEN
        UNDISCH_TAC `dist(u:real^3,m) < r0 / &2` THEN
        MP_TAC(ISPECL [`u:real^3`; `m:real^3`; `w:real^3`] DIST_TRIANGLE) THEN
        REAL_ARITH_TAC;
        ALL_TAC] THEN
      USE_THEN "loc" (fun th -> MP_TAC(MATCH_MP th
        (ASSUME `dist(u:real^3,w) < r0`))) THEN
      ASM_REWRITE_TAC[];
      ASM_REAL_ARITH_TAC];
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    USE_THEN "up" (MP_TAC o SPEC `min e (r0 / &2)`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `w:real^3` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `w:real^3` THEN CONJ_TAC THENL
     [SUBGOAL_THEN `dist(u:real^3,w) < r0` ASSUME_TAC THENL
       [UNDISCH_TAC `dist(m:real^3,w) < min e (r0 / &2)` THEN
        UNDISCH_TAC `dist(u:real^3,m) < r0 / &2` THEN
        MP_TAC(ISPECL [`u:real^3`; `m:real^3`; `w:real^3`] DIST_TRIANGLE) THEN
        REAL_ARITH_TAC;
        ALL_TAC] THEN
      USE_THEN "loc" (fun th -> MP_TAC(MATCH_MP th
        (ASSUME `dist(u:real^3,w) < r0`))) THEN
      ASM_REWRITE_TAC[];
      ASM_REAL_ARITH_TAC]]);;

let MOI_STL_BOUND_T = prove
 (`!K (b:real^3) u t A B r0.
     simplicial_complex K /\ {u} IN K /\
     (!x. {x} IN K /\ ~(x = u) ==> ~(b dot x = b dot u)) /\
     &2 simplex t /\ A IN t /\ B IN t /\ ~(b dot A = b dot B) /\ u IN t /\
     &0 < r0 /\ (!x. x IN UNIONS K /\ dist(u,x) < r0 ==> x IN t)
     ==> moi_sch3_crossings K b u <= 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:real^3->bool`; `A:real^3`; `B:real^3`; `b:real^3`; `u:real^3`]
    MOI_STL_TRIANGLE_INTERIOR_RAYS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `R:real^3->bool` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "rays")))) THEN
  MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `CARD(R:real^3->bool)` THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MOI_STL_CROSSINGS_RAYS THEN EXISTS_TAC `r0:real` THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  USE_THEN "rays" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

let MOI_STL_BOUND_FAR = prove
 (`!c (b:real^3) K u r0.
     moi_sch3_generic c b /\ pl_sphere 2 (UNIONS c) /\
     simplicial_complex K /\ {u} IN K /\
     (!x. {x} IN K /\ ~(x = u) ==> ~(b dot x = b dot u)) /\
     &0 < r0 /\ (!x. x IN UNIONS K /\ dist(u,x) < r0 ==> x IN UNIONS c)
     ==> moi_sch3_crossings K b u <=
         (if {u} IN c then moi_sch3_crossings c b u else 2)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (LABEL_TAC "loc"))))))) THEN
  SUBGOAL_THEN `(u:real^3) IN UNIONS c` ASSUME_TAC THENL
   [USE_THEN "loc" MATCH_MP_TAC THEN ASM_REWRITE_TAC[DIST_REFL] THEN
    REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `{u:real^3}` THEN
    ASM_REWRITE_TAC[IN_SING];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?R r. FINITE R /\
          CARD R <= (if {u} IN c then moi_sch3_crossings c b u else 2) /\
          &0 < r /\
          !x. x IN UNIONS c /\ b dot x = b dot u /\ dist(u,x) < r /\ ~(x = u)
              ==> ?d k. d IN R /\ &0 < k /\ x = u + k % d`
  STRIP_ASSUME_TAC THENL
   [COND_CASES_TAC THENL
     [MATCH_MP_TAC MOI_STL_VERTEX_RAYS THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC MOI_STL_NONVERTEX_RAYS THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `CARD(R:real^3->bool)` THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MOI_STL_CROSSINGS_RAYS THEN EXISTS_TAC `min r r0` THEN
  ASM_REWRITE_TAC[REAL_LT_MIN] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  USE_THEN "loc" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let MOI_STL_BOUND_J = prove
 (`!K (a:real^3) (b:real^3) u D A B C R r.
     moi_sch3_generic K b /\ pl_sphere 2 (UNIONS K) /\ {u} IN K /\
     UNIONS K = D UNION convex hull {A,B,C} /\
     D INTER convex hull {A,B,C} = relative_frontier (convex hull {A,B,C}) /\
     (!s. s IN K ==> s SUBSET convex hull {A,B,C} \/ s SUBSET D) /\
     ~affine_dependent {A,B,C} /\ ~(A = B) /\ ~(A = C) /\ ~(B = C) /\
     {A} IN K /\ {B} IN K /\ {C} IN K /\
     u IN relative_frontier (convex hull {A,B,C}) /\
     (!x. {x} IN K ==> (a dot x < a dot u ==> b dot x < b dot u) /\
                       (a dot u < a dot x ==> b dot u < b dot x)) /\
     FINITE R /\ CARD R <= 2 /\ &0 < r /\
     (!x. x IN D /\ a dot x = a dot u /\ dist(u,x) < r /\ ~(x = u)
          ==> ?d k. d IN R /\ &0 < k /\ x = u + k % d) /\
     (!x. x IN D /\ a dot x = a dot u /\ dist(u,x) < r
          ==> x IN relative_frontier (convex hull {A,B,C}))
     ==> moi_sch3_crossings K b u <= 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_sch3_generic]) THEN
  SUBGOAL_THEN `!x:real^3. {x} IN K /\ ~(x = u) ==> ~(b dot x = b dot u)`
  (LABEL_TAC "gen") THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~((b:real^3) dot A = b dot B) /\ ~(b dot A = b dot C) /\
                ~(b dot B = b dot C)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`A:real^3`; `B:real^3`; `C:real^3`; `b:real^3`; `u:real^3`]
    MOI_STL_TRIANGLE_BOUNDARY_RAY) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `Rt:real^3->bool` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "rt")))) THEN
  ABBREV_TAC `t = convex hull {A:real^3,B,C}` THEN
  SUBGOAL_THEN `closed(t:real^3->bool) /\ convex t` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "t" THEN REWRITE_TAC[CONVEX_CONVEX_HULL] THEN
    MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
    MATCH_MP_TAC FINITE_IMP_COMPACT_CONVEX_HULL THEN
    REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY];
    ALL_TAC] THEN
  SUBGOAL_THEN `relative_frontier t SUBSET (t:real^3->bool)` ASSUME_TAC THENL
   [REWRITE_TAC[relative_frontier] THEN ASM_SIMP_TAC[CLOSURE_CLOSED] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(u:real^3) IN t /\ u IN D` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `D INTER t = relative_frontier (t:real^3->bool)` THEN
    UNDISCH_TAC `(u:real^3) IN relative_frontier t` THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`K:(real^3->bool)->bool`; `t:real^3->bool`; `D:real^3->bool`;
                 `u:real^3`; `b:real^3`] MOI_STL_CROSSINGS_SPLIT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN `moi_sch3_crossings {s | s IN K /\ s SUBSET t} b (u:real^3) <= 1`
  ASSUME_TAC THENL
   [MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `CARD(Rt:real^3->bool)` THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_STL_CROSSINGS_RAYS THEN EXISTS_TAC `&1` THEN
    ASM_SIMP_TAC[MOI_STL_SUBCOMPLEX; REAL_LT_01] THEN
    REWRITE_TAC[IN_ELIM_THM; SING_SUBSET] THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
      USE_THEN "gen" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    X_GEN_TAC `x:real^3` THEN REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
    STRIP_TAC THEN USE_THEN "rt" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[SUBSET];
    ALL_TAC] THEN
  ABBREV_TAC `KD = {s:real^3->bool | s IN K /\ s SUBSET D}` THEN
  SUBGOAL_THEN `simplicial_complex (KD:(real^3->bool)->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "KD" THEN ASM_SIMP_TAC[MOI_STL_SUBCOMPLEX]; ALL_TAC] THEN
  SUBGOAL_THEN `!s:real^3->bool. s IN KD <=> s IN K /\ s SUBSET D` (LABEL_TAC "kd") THENL
   [EXPAND_TAC "KD" THEN REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  MP_TAC(ISPECL [`KD:(real^3->bool)->bool`; `u:real^3`; `a:real^3`;
                 `R:real^3->bool`; `r:real`] MOI_STL_LINK_LEVEL_RAYS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (find_term ((=) `R:real^3->bool`)) (concl th) && is_forall(concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(x:real^3) IN UNIONS KD` THEN REWRITE_TAC[IN_UNIONS] THEN
    ASM_MESON_TAC[SUBSET];
    STRIP_TAC] THEN
  SUBGOAL_THEN `moi_sch3_crossings KD b (u:real^3) <= 2` ASSUME_TAC THENL
   [MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC `CARD (UNIONS (simplicial_link KD u) INTER
                      {x:real^3 | a dot x = a dot u})` THEN
    CONJ_TAC THENL [ALL_TAC; ASM_ARITH_TAC] THEN
    MATCH_MP_TAC MOI_STL_CROSSINGS_LE THEN ASM_REWRITE_TAC[SING_SUBSET] THEN
    CONJ_TAC THENL
     [X_GEN_TAC `x:real^3` THEN
      REWRITE_TAC[simplicial_link; IN_ELIM_THM; IN_SING] THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN CONJ_TAC THENL
       [USE_THEN "gen" MATCH_MP_TAC THEN ASM_MESON_TAC[];
        FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
          can (find_term ((=) `(b:real^3) dot u`)) (concl th) &&
          is_forall(concl th) && not(can (find_term ((=) `R:real^3->bool`)) (concl th)) &&
          can (find_term ((=) `(a:real^3) dot u`)) (concl th))) THEN
        ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`x:real^3`; `y1:real^3`; `y2:real^3`] THEN STRIP_TAC THEN
    MATCH_MP_TAC(TAUT `F ==> p`) THEN
    SUBGOAL_THEN `!s:real^3->bool. s IN simplicial_link KD u ==> s IN simplicial_link K u`
    (LABEL_TAC "lk") THENL
     [REWRITE_TAC[simplicial_link; IN_ELIM_THM] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`KD:(real^3->bool)->bool`; `u:real^3`; `segment[x:real^3,y1]`]
      MOI_SCF_LINK_JOIN) THEN
    ASM_REWRITE_TAC[SING_SUBSET] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`KD:(real^3->bool)->bool`; `u:real^3`; `segment[x:real^3,y2]`]
      MOI_SCF_LINK_JOIN) THEN
    ASM_REWRITE_TAC[SING_SUBSET] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(x:real^3) IN UNIONS (simplicial_link KD u)` ASSUME_TAC THENL
     [REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `segment[x:real^3,y1]` THEN
      ASM_REWRITE_TAC[ENDS_IN_SEGMENT];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`KD:(real^3->bool)->bool`; `u:real^3`; `x:real^3`]
      MOI_STL_LINK_POINT) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`u:real^3`; `x:real^3`; `r:real`] MOI_STL_SEGMENT_NEAR) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `m:real^3` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `segment[u:real^3,x] SUBSET D` ASSUME_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `convex hull (u INSERT segment[x:real^3,y1])` THEN
      CONJ_TAC THENL
       [MP_TAC(ISPECL [`convex hull (u INSERT segment[x:real^3,y1])`; `u:real^3`;
                       `x:real^3`; `y1:real^3`] MOI_STL_JOIN_CONVEX_SUBSET) THEN
        SIMP_TAC[CONVEX_CONVEX_HULL; HULL_INC; IN_INSERT; ENDS_IN_SEGMENT];
        ASM_MESON_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `(m:real^3) IN D /\ (a:real^3) dot m = a dot u` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [ASM_MESON_TAC[SUBSET; SEGMENT_OPEN_SUBSET_CLOSED];
        UNDISCH_TAC `(m:real^3) IN segment(u,x)` THEN REWRITE_TAC[IN_SEGMENT] THEN
        STRIP_TAC THEN ASM_REWRITE_TAC[DOT_RADD; DOT_RMUL] THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `(m:real^3) IN t` ASSUME_TAC THENL
     [SUBGOAL_THEN `(m:real^3) IN relative_frontier t` MP_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
          can (find_term ((=) `relative_frontier(t:real^3->bool)`)) (concl th))) THEN
        ASM_REWRITE_TAC[];
        ASM_MESON_TAC[SUBSET]];
      ALL_TAC] THEN
    USE_THEN "lk" (fun th -> ASSUME_TAC(MATCH_MP th
      (ASSUME `segment[x:real^3,y1] IN simplicial_link KD u`))) THEN
    USE_THEN "lk" (fun th -> ASSUME_TAC(MATCH_MP th
      (ASSUME `segment[x:real^3,y2] IN simplicial_link KD u`))) THEN
    SUBGOAL_THEN `t SUBSET UNIONS (K:(real^3->bool)->bool) /\
                  D INTER t SUBSET relative_frontier (t:real^3->bool)`
      STRIP_ASSUME_TAC THENL
     [ASM_REWRITE_TAC[SUBSET_REFL] THEN SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC MOI_STL_FOLD_SIDE_EDGE THEN
    MAP_EVERY EXISTS_TAC [`K:(real^3->bool)->bool`; `u:real^3`; `x:real^3`;
      `y1:real^3`; `y2:real^3`; `D:real^3->bool`; `t:real^3->bool`; `m:real^3`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`K:(real^3->bool)->bool`; `b:real^3`; `u:real^3`]
    SINGULAR_POLYGONS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT2) THEN REWRITE_TAC[EVEN_EXISTS] THEN
  DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN
  UNDISCH_TAC `moi_sch3_crossings KD b (u:real^3) <= 2` THEN
  UNDISCH_TAC `moi_sch3_crossings {s | s IN K /\ s SUBSET t} b (u:real^3) <= 1` THEN
  UNDISCH_TAC `moi_sch3_crossings K b u <=
               moi_sch3_crossings {s | s IN K /\ s SUBSET t} b (u:real^3) +
               moi_sch3_crossings KD b u` THEN
  UNDISCH_TAC `moi_sch3_crossings K b (u:real^3) = 2 * n` THEN
  ASM_CASES_TAC `n <= 1` THEN POP_ASSUM MP_TAC THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* 9. Triangulations of the caps: a simplicial complex on D UNION t that    *)
(* refines the pieces of D, the triangle t and given points, so that every  *)
(* simplex lies in t or in D (fold) and the corners of t are vertices.      *)
(* ------------------------------------------------------------------------- *)

let MOI_STL_CELL_POLYHEDRON = prove
 (`!n (d:real^N->bool) j. pl_cell_with_boundary n d j ==> pl_polyhedron d`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_cell_with_boundary; pl_homeomorphism] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
    (X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC))) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
    is_eq(concl th) && is_comb(lhs(concl th)) &&
    fst(dest_const(fst(strip_comb(lhs(concl th))))) = "IMAGE" &&
    rand(lhs(concl th)) = `k:real^N->bool`)) THEN
  MATCH_MP_TAC PL_POLYHEDRON_PL_IMAGE THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC POLYTOPE_IMP_PL_POLYHEDRON THEN
  ASM_MESON_TAC[SIMPLEX_IMP_POLYTOPE]);;

let MOI_STL_SING_UNIONS = prove
 (`!K f (a:real^N). f SUBSET K /\ {a} = UNIONS f ==> {a} IN K`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(a:real^N) IN UNIONS f` MP_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[IN_SING]; ALL_TAC] THEN
  REWRITE_TAC[IN_UNIONS] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `s = {a:real^N}` (fun th -> ASM_MESON_TAC[th; SUBSET]) THEN
  UNDISCH_TAC `{a:real^N} = UNIONS f` THEN UNDISCH_TAC `(s:real^N->bool) IN f` THEN
  UNDISCH_TAC `(a:real^N) IN s` THEN SET_TAC[]);;

let MOI_STL_CAP_TRIANGULATION = prove
 (`!D A B C (q:real^3).
     pl_polyhedron D /\ (q IN D \/ q IN convex hull {A,B,C})
     ==> ?K. simplicial_complex K /\ UNIONS K = D UNION convex hull {A,B,C} /\
             (!s. s IN K ==> s SUBSET convex hull {A,B,C} \/ s SUBSET D) /\
             {A} IN K /\ {B} IN K /\ {C} IN K /\ {q} IN K`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
  ABBREV_TAC `t = convex hull {A:real^3,B,C}` THEN
  SUBGOAL_THEN `polytope(t:real^3->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "t" THEN MATCH_MP_TAC POLYTOPE_CONVEX_HULL THEN
    REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY];
    ALL_TAC] THEN
  SUBGOAL_THEN `(A:real^3) IN t /\ (B:real^3) IN t /\ (C:real^3) IN t`
    STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "t" THEN SIMP_TAC[HULL_INC; IN_INSERT]; ALL_TAC] THEN
  SUBGOAL_THEN `pl_polyhedron (D UNION t:real^3->bool)` MP_TAC THENL
   [MATCH_MP_TAC PL_POLYHEDRON_UNION THEN ASM_SIMP_TAC[POLYTOPE_IMP_PL_POLYHEDRON];
    ALL_TAC] THEN
  REWRITE_TAC[PL_POLYHEDRON_EQ_SIMPLICIAL_COMPLEX] THEN
  DISCH_THEN(X_CHOOSE_THEN `c0:(real^3->bool)->bool` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `pl_polyhedron(D:real^3->bool)` THEN REWRITE_TAC[pl_polyhedron] THEN
  DISCH_THEN(X_CHOOSE_THEN `PD:(real^3->bool)->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`c0:(real^3->bool)->bool`;
                 `t INSERT {A:real^3} INSERT {B} INSERT {C} INSERT {q} INSERT PD`]
    SIMPLICIAL_COMPLEX_REFINE_POLYTOPES) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[FINITE_INSERT; FORALL_IN_INSERT; POLYTOPE_SING] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `K:(real^3->bool)->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `K:(real^3->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!k:real^3->bool. k IN t INSERT {A} INSERT {B} INSERT {C} INSERT {q} INSERT PD
                     ==> ?f. f SUBSET K /\ k = UNIONS f`
  (LABEL_TAC "ref") THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `s:real^3->bool` THEN DISCH_TAC THEN
    ASM_CASES_TAC `s:real^3->bool = {}` THENL
     [ASM_REWRITE_TAC[EMPTY_SUBSET]; ALL_TAC] THEN
    SUBGOAL_THEN `?x:real^3. x IN relative_interior s` STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[MEMBER_NOT_EMPTY] THEN
      ASM_MESON_TAC[RELATIVE_INTERIOR_EQ_EMPTY; MOI_SLV_SC_BASIC];
      ALL_TAC] THEN
    SUBGOAL_THEN `(x:real^3) IN D UNION t` MP_TAC THENL
     [SUBGOAL_THEN `(x:real^3) IN s` MP_TAC THENL
       [ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET]; ALL_TAC] THEN
      UNDISCH_TAC `UNIONS K = UNIONS (c0:(real^3->bool)->bool)` THEN
      UNDISCH_TAC `UNIONS c0 = D UNION (t:real^3->bool)` THEN
      UNDISCH_TAC `(s:real^3->bool) IN K` THEN SET_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[IN_UNION] THEN STRIP_TAC THENL
     [DISJ2_TAC THEN
      UNDISCH_TAC `(x:real^3) IN D` THEN ASM_REWRITE_TAC[IN_UNIONS] THEN
      DISCH_THEN(X_CHOOSE_THEN `P:real^3->bool` STRIP_ASSUME_TAC) THEN
      USE_THEN "ref" (MP_TAC o SPEC `P:real^3->bool`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[IN_INSERT]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `fP:(real^3->bool)->bool` STRIP_ASSUME_TAC) THEN
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `P:real^3->bool` THEN
      CONJ_TAC THENL
       [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_PLT_SIMPLEX_SUBSET_UNIONS THEN
        EXISTS_TAC `K:(real^3->bool)->bool` THEN EXISTS_TAC `x:real^3` THEN
        ASM_MESON_TAC[];
        UNDISCH_TAC `(P:real^3->bool) IN PD` THEN SET_TAC[]];
      DISJ1_TAC THEN
      USE_THEN "ref" (MP_TAC o SPEC `t:real^3->bool`) THEN
      REWRITE_TAC[IN_INSERT] THEN
      DISCH_THEN(X_CHOOSE_THEN `ft:(real^3->bool)->bool` STRIP_ASSUME_TAC) THEN
      FIRST_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [th]) THEN
      MATCH_MP_TAC MOI_PLT_SIMPLEX_SUBSET_UNIONS THEN
      EXISTS_TAC `K:(real^3->bool)->bool` THEN EXISTS_TAC `x:real^3` THEN
      ASM_MESON_TAC[]];
    USE_THEN "ref" (MP_TAC o SPEC `{A:real^3}`) THEN REWRITE_TAC[IN_INSERT] THEN
    MESON_TAC[MOI_STL_SING_UNIONS];
    USE_THEN "ref" (MP_TAC o SPEC `{B:real^3}`) THEN REWRITE_TAC[IN_INSERT] THEN
    MESON_TAC[MOI_STL_SING_UNIONS];
    USE_THEN "ref" (MP_TAC o SPEC `{C:real^3}`) THEN REWRITE_TAC[IN_INSERT] THEN
    MESON_TAC[MOI_STL_SING_UNIONS];
    USE_THEN "ref" (MP_TAC o SPEC `{q:real^3}`) THEN REWRITE_TAC[IN_INSERT] THEN
    MESON_TAC[MOI_STL_SING_UNIONS]]);;

(* ------------------------------------------------------------------------- *)
(* 10. The tilt: sign stability of nearby heights on a finite vertex set,   *)
(* a direction b increasing away from f p on the triangle, and the index    *)
(* of one cap (Moise p.123): the tilted generic height of the triangulated  *)
(* cap has smaller index, by MOI_SCD_INDEX_COMPARE with CAP_COUNT at f p.   *)
(* ------------------------------------------------------------------------- *)

let MOI_STL_SIGN_CLOSE = prove
 (`!(V:real^3->bool) (a:real^3).
     FINITE V
     ==> ?e. &0 < e /\
             !a1. norm(a1 - a) < e
                  ==> !x y. x IN V /\ y IN V /\ a dot x < a dot y
                            ==> a1 dot x < a1 dot y`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP FINITE_IMP_BOUNDED) THEN
  REWRITE_TAC[BOUNDED_POS] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC
   `P = {a dot y - a dot (x:real^3) | x,y | x IN V /\ y IN V /\ a dot x < a dot y}` THEN
  SUBGOAL_THEN `FINITE (P:real->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "P" THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{a dot y - a dot (x:real^3) | x,y | x IN V /\ y IN V}` THEN
    CONJ_TAC THENL
     [MP_TAC(BETA_RULE(ISPECL [`\x y:real^3. a dot y - a dot (x:real^3)`;
                               `V:real^3->bool`; `\x:real^3. V:real^3->bool`]
        FINITE_PRODUCT_DEPENDENT)) THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(TAUT `(p <=> q) ==> p ==> q`) THEN
      AP_TERM_TAC THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN MESON_TAC[];
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[]];
    ALL_TAC] THEN
  ASM_CASES_TAC `P:real->bool = {}` THENL
   [EXISTS_TAC `&1` THEN REWRITE_TAC[REAL_LT_01] THEN REPEAT STRIP_TAC THEN
    UNDISCH_TAC `P:real->bool = {}` THEN EXPAND_TAC "P" THEN
    REWRITE_TAC[EXTENSION; NOT_IN_EMPTY; IN_ELIM_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `a dot (y:real^3) - a dot (x:real^3)`) THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `P:real->bool` INF_FINITE) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "inf")) THEN
  SUBGOAL_THEN `&0 < inf P` ASSUME_TAC THENL
   [UNDISCH_TAC `inf P IN P` THEN EXPAND_TAC "P" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    STRIP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `inf P / (&2 * B + &1)` THEN
  SUBGOAL_THEN `&0 < &2 * B + &1` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LT_DIV] THEN
  X_GEN_TAC `a1:real^3` THEN DISCH_TAC THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `inf P <= a dot y - a dot (x:real^3)` ASSUME_TAC THENL
   [USE_THEN "inf" MATCH_MP_TAC THEN EXPAND_TAC "P" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `abs((a1 - a) dot (y - x:real^3)) <= norm(a1 - a) * (&2 * B)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `norm(a1 - a:real^3) * norm(y - x:real^3)` THEN
    REWRITE_TAC[NORM_CAUCHY_SCHWARZ_ABS] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
    MATCH_MP_TAC(NORM_ARITH
     `norm(x:real^3) <= B /\ norm(y:real^3) <= B ==> norm(y - x) <= &2 * B`) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `norm(a1 - a:real^3) * (&2 * B) < inf P` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `inf P / (&2 * B + &1) * (&2 * B)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
      ASM_REAL_ARITH_TAC;
      SUBGOAL_THEN `inf P / (&2 * B + &1) * (&2 * B) =
                    (inf P * (&2 * B)) / (&2 * B + &1)` SUBST1_TAC THENL
       [REWRITE_TAC[real_div] THEN REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  UNDISCH_TAC `abs((a1 - a) dot (y - x:real^3)) <= norm(a1 - a) * (&2 * B)` THEN
  REWRITE_TAC[DOT_LSUB; DOT_RSUB] THEN ASM_REAL_ARITH_TAC);;

let MOI_STL_TILT_DIRECTION = prove
 (`!t (q:real^3).
     &2 simplex t /\ (q IN t ==> {q} face_of t)
     ==> ?b. !x. x IN t /\ ~(x = q) ==> &0 < b dot (x - q)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `polytope(t:real^3->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[SIMPLEX_IMP_POLYTOPE]; ALL_TAC] THEN
  ASM_CASES_TAC `(q:real^3) IN t` THENL
   [FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(q:real^3) IN t`)) THEN
    ASM_SIMP_TAC[GSYM EXPOSED_FACE_OF_POLYHEDRON; POLYTOPE_IMP_POLYHEDRON] THEN
    REWRITE_TAC[exposed_face_of] THEN
    DISCH_THEN(X_CHOOSE_THEN `a':real^3` (X_CHOOSE_THEN `beta:real`
      STRIP_ASSUME_TAC) o CONJUNCT2) THEN
    EXISTS_TAC `--a':real^3` THEN X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(a':real^3) dot q = beta` ASSUME_TAC THENL
     [UNDISCH_TAC `{q:real^3} = t INTER {x | a' dot x = beta}` THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(a':real^3) dot x <= beta /\ ~(a' dot x = beta)` MP_TAC THENL
     [CONJ_TAC THENL
       [UNDISCH_TAC `t SUBSET {x:real^3 | a' dot x <= beta}` THEN
        UNDISCH_TAC `(x:real^3) IN t` THEN SET_TAC[];
        DISCH_TAC THEN UNDISCH_TAC `~(x:real^3 = q)` THEN REWRITE_TAC[] THEN
        UNDISCH_TAC `{q:real^3} = t INTER {x | a' dot x = beta}` THEN
        UNDISCH_TAC `(x:real^3) IN t` THEN UNDISCH_TAC `(a':real^3) dot x = beta` THEN
        SET_TAC[]];
      ALL_TAC] THEN
    REWRITE_TAC[DOT_LNEG; DOT_RSUB] THEN ASM_REAL_ARITH_TAC;
    MP_TAC(ISPECL [`t:real^3->bool`; `q:real^3`]
      SEPARATING_HYPERPLANE_CLOSED_POINT) THEN
    ASM_SIMP_TAC[POLYTOPE_IMP_CONVEX; POLYTOPE_IMP_CLOSED] THEN
    DISCH_THEN(X_CHOOSE_THEN `a':real^3` (X_CHOOSE_THEN `beta:real`
      STRIP_ASSUME_TAC)) THEN
    EXISTS_TAC `a':real^3` THEN X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^3`) THEN ASM_REWRITE_TAC[DOT_RSUB] THEN
    ASM_REAL_ARITH_TAC]);;

let MOI_STL_CLOSED_AVOID = prove
 (`!s (x:real^3). closed s /\ ~(x IN s)
                  ==> ?e. &0 < e /\ !y. dist(x,y) < e ==> ~(y IN s)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`x:real^3`; `s:real^3->bool`] CLOSED_APPROACHABLE) THEN
  ASM_REWRITE_TAC[NOT_FORALL_THM; NOT_IMP] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `e:real` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `y:real^3` THEN REPEAT STRIP_TAC THEN
  UNDISCH_TAC `~(?y:real^3. y IN s /\ dist(y,x) < e)` THEN REWRITE_TAC[] THEN
  EXISTS_TAC `y:real^3` THEN ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REWRITE_TAC[]);;

let MOI_STL_FAR_IN_SPHERE = prove
 (`!c (a:real^3) h (f:real^3->real^3) D t del x.
     (!x. a dot f x = a dot x) /\ (!x. del <= abs(a dot x - h) ==> f x = x) /\
     t SUBSET {x | a dot x = h} /\ D SUBSET IMAGE f (UNIONS c) /\ &0 < del /\
     x IN D UNION t /\ del <= abs(a dot x - h)
     ==> x IN UNIONS c`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(x:real^3) IN D` MP_TAC THENL
   [UNDISCH_TAC `(x:real^3) IN D UNION t` THEN REWRITE_TAC[IN_UNION] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(a:real^3) dot x = h` MP_TAC THENL
     [ASM SET_TAC[]; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `(x:real^3) IN IMAGE (f:real^3->real^3) (UNIONS c)` MP_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(f:real^3->real^3) y = y` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `del <= abs((a:real^3) dot x - h)` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_MESON_TAC[]);;

let MOI_STL_SLAB_VERTEX = prove
 (`!c (a:real^3) p j0 del (f:real^3->real^3) g A B C D D' K (a1:real^3) u.
     moi_sch3_generic c a /\ pl_sphere 2 (UNIONS c) /\ {p} IN c /\
     4 <= moi_sch3_crossings c a p /\
     j0 IN moi_sch3_level_polygons (UNIONS c) a (a dot p) /\
     &0 < del /\
     (!v. {v} IN c /\ ~(v = p) ==> &4 * del <= abs(a dot v - a dot p)) /\
     pl_homeomorphism ((:real^3),(:real^3)) (f,g) /\ (!x. a dot f x = a dot x) /\
     ~affine_dependent {A,B,C} /\ ~(A = B) /\ ~(A = C) /\ ~(B = C) /\
     convex hull {A,B,C} SUBSET {x | a dot x = a dot p} /\
     IMAGE f j0 = relative_frontier(convex hull {A,B,C}) /\
     closed D /\ closed D' /\
     D UNION D' = IMAGE f (UNIONS c) /\
     D INTER D' = relative_frontier(convex hull {A,B,C}) /\
     D INTER convex hull {A,B,C} = relative_frontier(convex hull {A,B,C}) /\
     moi_sch3_generic K a1 /\ pl_sphere 2 (UNIONS K) /\
     UNIONS K = D UNION convex hull {A,B,C} /\
     (!s. s IN K ==> s SUBSET convex hull {A,B,C} \/ s SUBSET D) /\
     {A} IN K /\ {B} IN K /\ {C} IN K /\
     (!x y. {x} IN K /\ {y} IN K /\ a dot x < a dot y ==> a1 dot x < a1 dot y) /\
     {u} IN K /\ ~(u = f p) /\ abs(a dot u - a dot p) < &2 * del
     ==> moi_sch3_crossings K a1 u <= 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!v w:real^3. {v} IN K /\ {w} IN K /\ a1 dot v = a1 dot w ==> v = w`
  (LABEL_TAC "kgen") THENL
   [UNDISCH_TAC `moi_sch3_generic K (a1:real^3)` THEN
    REWRITE_TAC[moi_sch3_generic] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `simplicial_complex (K:(real^3->bool)->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `moi_sch3_generic K (a1:real^3)` THEN
    REWRITE_TAC[moi_sch3_generic] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^3. {x} IN K /\ ~(x = u) ==> ~(a1 dot x = a1 dot u)`
  (LABEL_TAC "vgen") THENL
   [REPEAT STRIP_TAC THEN UNDISCH_TAC `~(x:real^3 = u)` THEN REWRITE_TAC[] THEN
    USE_THEN "kgen" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x:real^3. {x} IN K ==> (a dot x < a dot u ==> a1 dot x < a1 dot u) /\
                           (a dot u < a dot x ==> a1 dot u < a1 dot x)`
  (LABEL_TAC "sgn") THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (find_term ((=) `(a1:real^3) dot y`)) (concl th) && is_forall(concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z:real^3. (g:real^3->real^3) (f z) = z /\ f (g z) = z`
  (LABEL_TAC "fg") THENL
   [UNDISCH_TAC `pl_homeomorphism ((:real^3),(:real^3)) (f:real^3->real^3,g)` THEN
    REWRITE_TAC[pl_homeomorphism; homeomorphism; IN_UNIV] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z:real^3. (a:real^3) dot (g:real^3->real^3) z = a dot z`
  (LABEL_TAC "glev") THENL
   [GEN_TAC THEN
    MP_TAC(SPEC `(g:real^3->real^3) z`
      (ASSUME `!x. (a:real^3) dot (f:real^3->real^3) x = a dot x`)) THEN
    USE_THEN "fg" (fun th -> REWRITE_TAC[CONJUNCT2(SPEC `z:real^3` th)]) THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y:real^3. abs(a dot y - a dot p) < &2 * del /\ ~(y = p) ==> ~({y} IN c)`
  (LABEL_TAC "nvx") THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:real^3` o check (fun th ->
      can (find_term ((=) `&4 * del`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `t = convex hull {A:real^3,B,C}` THEN
  SUBGOAL_THEN `closed(t:real^3->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "t" THEN MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
    MATCH_MP_TAC FINITE_IMP_COMPACT_CONVEX_HULL THEN
    REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY];
    ALL_TAC] THEN
  SUBGOAL_THEN `relative_frontier t SUBSET (t:real^3->bool)` ASSUME_TAC THENL
   [REWRITE_TAC[relative_frontier] THEN ASM_SIMP_TAC[CLOSURE_CLOSED] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(u:real^3) IN D UNION t` ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `UNIONS K = D UNION (t:real^3->bool)`)) THEN
    REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `{u:real^3}` THEN
    ASM_REWRITE_TAC[IN_SING];
    ALL_TAC] THEN
  ASM_CASES_TAC `(u:real^3) IN t` THENL
   [ALL_TAC;
    SUBGOAL_THEN `(u:real^3) IN D` ASSUME_TAC THENL
     [UNDISCH_TAC `(u:real^3) IN D UNION t` THEN ASM_REWRITE_TAC[IN_UNION];
      ALL_TAC] THEN
    SUBGOAL_THEN `~((u:real^3) IN D')` ASSUME_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC `~((u:real^3) IN t)` THEN REWRITE_TAC[] THEN
      UNDISCH_TAC `relative_frontier t SUBSET (t:real^3->bool)` THEN
      UNDISCH_TAC `D INTER D' = relative_frontier (t:real^3->bool)` THEN
      UNDISCH_TAC `(u:real^3) IN D` THEN UNDISCH_TAC `(u:real^3) IN D'` THEN
      SET_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`t:real^3->bool`; `u:real^3`] MOI_STL_CLOSED_AVOID) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `e1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "av1"))) THEN
    MP_TAC(ISPECL [`D':real^3->bool`; `u:real^3`] MOI_STL_CLOSED_AVOID) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `e2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "av2"))) THEN
    SUBGOAL_THEN `&0 < dist(u:real^3,(f:real^3->real^3) p)` ASSUME_TAC THENL
     [MATCH_MP_TAC DIST_POS_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `!x:real^3. dist(u,x) < min e1 (min e2 (dist(u,(f:real^3->real^3) p)))
                 ==> (x IN UNIONS K <=> x IN IMAGE f (UNIONS c))`
    ASSUME_TAC THENL
     [X_GEN_TAC `x:real^3` THEN REWRITE_TAC[REAL_LT_MIN] THEN STRIP_TAC THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        concl th = `D UNION D' = IMAGE (f:real^3->real^3) (UNIONS c)`)) THEN
      FIRST_X_ASSUM(SUBST1_TAC o check (fun th ->
        concl th = `UNIONS K = D UNION (t:real^3->bool)`)) THEN
      SUBGOAL_THEN `~((x:real^3) IN t) /\ ~(x IN D')` MP_TAC THENL
       [CONJ_TAC THENL
         [USE_THEN "av1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
          USE_THEN "av2" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
        REWRITE_TAC[IN_UNION] THEN MESON_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `!x:real^3. x IN IMAGE f (UNIONS c) /\
                 dist(u,x) < min e1 (min e2 (dist(u,(f:real^3->real^3) p))) /\
                 a dot x = a dot u
                 ==> ~({(g:real^3->real^3) x} IN c)`
    ASSUME_TAC THENL
     [X_GEN_TAC `x:real^3` THEN REWRITE_TAC[REAL_LT_MIN] THEN STRIP_TAC THEN
      USE_THEN "nvx" MATCH_MP_TAC THEN
      USE_THEN "glev" (fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[] THEN
      DISCH_TAC THEN
      SUBGOAL_THEN `x:real^3 = (f:real^3->real^3) p` SUBST_ALL_TAC THENL
       [USE_THEN "fg" (MP_TAC o CONJUNCT2 o SPEC `x:real^3`) THEN
        REWRITE_TAC[ASSUME `(g:real^3->real^3) x = p`] THEN MESON_TAC[];
        ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    MATCH_MP_TAC MOI_STL_BOUND_D THEN
    MAP_EVERY EXISTS_TAC [`c:(real^3->bool)->bool`; `a:real^3`; `f:real^3->real^3`;
      `g:real^3->real^3`; `min e1 (min e2 (dist(u:real^3,(f:real^3->real^3) p)))`] THEN
    ASM_REWRITE_TAC[REAL_LT_MIN]] THEN
  ASM_CASES_TAC `(u:real^3) IN relative_frontier t` THENL
   [ALL_TAC;
    SUBGOAL_THEN `~((u:real^3) IN D)` ASSUME_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC `~((u:real^3) IN relative_frontier t)` THEN
      REWRITE_TAC[] THEN
      UNDISCH_TAC `D INTER t = relative_frontier (t:real^3->bool)` THEN
      UNDISCH_TAC `(u:real^3) IN D` THEN UNDISCH_TAC `(u:real^3) IN t` THEN
      SET_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`D:real^3->bool`; `u:real^3`] MOI_STL_CLOSED_AVOID) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `e1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "av1"))) THEN
    SUBGOAL_THEN `&2 simplex (t:real^3->bool) /\ (A:real^3) IN t /\ (B:real^3) IN t`
      STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "t" THEN SIMP_TAC[HULL_INC; IN_INSERT] THEN
      MATCH_MP_TAC MOI_STL_TRIANGLE_SIMPLEX THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `~((a1:real^3) dot A = a1 dot B)` ASSUME_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC `~(A:real^3 = B)` THEN REWRITE_TAC[] THEN
      USE_THEN "kgen" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `!x:real^3. x IN UNIONS K /\ dist(u,x) < e1 ==> x IN t`
    ASSUME_TAC THENL
     [X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
      SUBGOAL_THEN `~((x:real^3) IN D)` MP_TAC THENL
       [USE_THEN "av1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `(x:real^3) IN UNIONS K` THEN
      FIRST_X_ASSUM(SUBST1_TAC o check (fun th ->
        concl th = `UNIONS K = D UNION (t:real^3->bool)`)) THEN
      REWRITE_TAC[IN_UNION] THEN MESON_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC MOI_STL_BOUND_T THEN
    MAP_EVERY EXISTS_TAC [`t:real^3->bool`; `A:real^3`; `B:real^3`; `e1:real`] THEN
    ASM_REWRITE_TAC[]] THEN
  SUBGOAL_THEN `(u:real^3) IN IMAGE (f:real^3->real^3) j0` MP_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `y0:real^3` (CONJUNCTS_THEN2 (ASSUME_TAC o SYM)
    ASSUME_TAC)) THEN
  SUBGOAL_THEN `(g:real^3->real^3) u = y0` ASSUME_TAC THENL
   [UNDISCH_TAC `(f:real^3->real^3) y0 = u` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    USE_THEN "fg" (fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  SUBGOAL_THEN `j0 SUBSET UNIONS c INTER {x:real^3 | a dot x = a dot p}`
    ASSUME_TAC THENL
   [UNDISCH_TAC `j0 IN moi_sch3_level_polygons (UNIONS c) a (a dot (p:real^3))` THEN
    REWRITE_TAC[moi_sch3_level_polygons; IN_ELIM_THM] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y0:real^3) IN UNIONS c` ASSUME_TAC THENL
   [UNDISCH_TAC `(y0:real^3) IN j0` THEN
    UNDISCH_TAC `j0 SUBSET UNIONS c INTER {x:real^3 | a dot x = a dot p}` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(y0:real^3 = p)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC `~(u:real^3 = (f:real^3->real^3) p)` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(a:real^3) dot u = a dot p` ASSUME_TAC THENL
   [UNDISCH_TAC `(u:real^3) IN relative_frontier t` THEN
    UNDISCH_TAC `relative_frontier t SUBSET (t:real^3->bool)` THEN
    UNDISCH_TAC `t SUBSET {x:real^3 | a dot x = a dot p}` THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~({y0:real^3} IN c)` ASSUME_TAC THENL
   [USE_THEN "nvx" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(a:real^3) dot y0 = a dot u` SUBST1_TAC THENL
     [UNDISCH_TAC `(g:real^3->real^3) u = y0` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN USE_THEN "glev" (fun th -> REWRITE_TAC[th]);
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `a:real^3`; `y0:real^3`]
    MOI_STL_NONVERTEX_RAYS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `R0:real^3->bool` (X_CHOOSE_THEN `r0:real`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`UNIONS c:real^3->bool`; `f:real^3->real^3`; `g:real^3->real^3`;
                 `a:real^3`; `y0:real^3`; `R0:real^3->bool`; `r0:real`]
    MOI_STL_RAYS_TRANSPORT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `R:real^3->bool` (X_CHOOSE_THEN `r:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "rays0")))))) THEN
  USE_THEN "rays0" (fun th -> LABEL_TAC "rays"
    (REWRITE_RULE[ASSUME `(f:real^3->real^3) y0 = u`] th)) THEN
  MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `a:real^3`; `p:real^3`; `j0:real^3->bool`;
                 `y0:real^3`] MOI_STL_LEVEL_NEAR_POLYGON) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r1:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`UNIONS c:real^3->bool`; `j0:real^3->bool`; `a:real^3`;
                 `(a:real^3) dot p`; `f:real^3->real^3`; `g:real^3->real^3`;
                 `u:real^3`; `r1:real`] MOI_STL_IMAGE_LEVEL_NEAR) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "lev"))) THEN
  SUBGOAL_THEN `CARD(R:real^3->bool) <= 2` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!x:real^3. x IN D /\ a dot x = a dot u /\ dist(u,x) < min r r2 /\ ~(x = u)
               ==> ?d k. d IN R /\ &0 < k /\ x = u + k % d`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^3` THEN REWRITE_TAC[REAL_LT_MIN] THEN STRIP_TAC THEN
    USE_THEN "rays" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(x:real^3) IN D` THEN
    UNDISCH_TAC `D UNION D' = IMAGE (f:real^3->real^3) (UNIONS c)` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x:real^3. x IN D /\ a dot x = a dot u /\ dist(u,x) < min r r2
               ==> x IN relative_frontier t`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^3` THEN REWRITE_TAC[REAL_LT_MIN] THEN STRIP_TAC THEN
    USE_THEN "lev" (MP_TAC o REWRITE_RULE[SUBSET]) THEN
    DISCH_THEN(MP_TAC o SPEC `x:real^3`) THEN
    ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM; IN_BALL] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    UNDISCH_TAC `(x:real^3) IN D` THEN
    UNDISCH_TAC `D UNION D' = IMAGE (f:real^3->real^3) (UNIONS c)` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < min r r2` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_LT_MIN]; ALL_TAC] THEN
  MATCH_MP_TAC MOI_STL_BOUND_J THEN
  MAP_EVERY EXISTS_TAC [`a:real^3`; `D:real^3->bool`; `A:real^3`; `B:real^3`;
    `C:real^3`; `R:real^3->bool`; `min r r2`] THEN
  REWRITE_TAC[ASSUME `convex hull {A:real^3,B,C} = t`] THEN
  ASM_REWRITE_TAC[]);;

let MOI_STL_CAP_VERTEX_BOUNDS = prove
 (`!c (a:real^3) p j0 del (f:real^3->real^3) g A B C D D' K (a1:real^3).
     moi_sch3_generic c a /\ pl_sphere 2 (UNIONS c) /\ {p} IN c /\
     4 <= moi_sch3_crossings c a p /\
     j0 IN moi_sch3_level_polygons (UNIONS c) a (a dot p) /\
     &0 < del /\
     (!v. {v} IN c /\ ~(v = p) ==> &4 * del <= abs(a dot v - a dot p)) /\
     pl_homeomorphism ((:real^3),(:real^3)) (f,g) /\ (!x. a dot f x = a dot x) /\
     (!x. del <= abs(a dot x - a dot p) ==> f x = x) /\
     ~affine_dependent {A,B,C} /\ ~(A = B) /\ ~(A = C) /\ ~(B = C) /\
     convex hull {A,B,C} SUBSET {x | a dot x = a dot p} /\
     IMAGE f j0 = relative_frontier(convex hull {A,B,C}) /\
     closed D /\ closed D' /\
     D UNION D' = IMAGE f (UNIONS c) /\
     D INTER D' = relative_frontier(convex hull {A,B,C}) /\
     D INTER convex hull {A,B,C} = relative_frontier(convex hull {A,B,C}) /\
     moi_sch3_generic K a1 /\ pl_sphere 2 (UNIONS K) /\
     UNIONS K = D UNION convex hull {A,B,C} /\
     (!s. s IN K ==> s SUBSET convex hull {A,B,C} \/ s SUBSET D) /\
     {A} IN K /\ {B} IN K /\ {C} IN K /\
     (!x y. {x} IN K /\ {y} IN K /\ a dot x < a dot y ==> a1 dot x < a1 dot y) /\
     moi_sch3_generic c a1 /\
     (!v. {v} IN c ==> moi_sch3_crossings c a1 v = moi_sch3_crossings c a v) /\
     (!q. {q} IN c /\ &2 * del <= abs(a dot q - a dot p)
          ==> CARD (moi_sch3_level_polygons (UNIONS K) a1 (a1 dot q)) <=
              CARD (moi_sch3_level_polygons (UNIONS c) a (a dot q)))
     ==> !u. {u} IN K /\ 4 <= moi_sch3_crossings K a1 u /\ ~(u = f p)
             ==> {u} IN c /\ 4 <= moi_sch3_crossings c a u /\ ~(u = p) /\
                 CARD (moi_sch3_level_polygons (UNIONS K) a1 (a1 dot u)) <=
                 CARD (moi_sch3_level_polygons (UNIONS c) a (a dot u))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `u:real^3` THEN STRIP_TAC THEN
  ASM_CASES_TAC `abs((a:real^3) dot u - a dot p) < &2 * del` THENL
   [MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `a:real^3`; `p:real^3`;
      `j0:real^3->bool`; `del:real`; `f:real^3->real^3`; `g:real^3->real^3`;
      `A:real^3`; `B:real^3`; `C:real^3`; `D:real^3->bool`; `D':real^3->bool`;
      `K:(real^3->bool)->bool`; `a1:real^3`; `u:real^3`] MOI_STL_SLAB_VERTEX) THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `simplicial_complex (K:(real^3->bool)->bool) /\
                (!x:real^3. {x} IN K /\ ~(x = u) ==> ~(a1 dot x = a1 dot u))`
    STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `{u:real^3} IN K` THEN
    UNDISCH_TAC `moi_sch3_generic K (a1:real^3)` THEN
    REWRITE_TAC[moi_sch3_generic] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?r0. &0 < r0 /\ norm(a:real^3) * r0 < del` STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `del / (norm(a:real^3) + &1)` THEN
    SUBGOAL_THEN `&0 < norm(a:real^3) + &1` ASSUME_TAC THENL
     [MP_TAC(ISPEC `a:real^3` NORM_POS_LE) THEN REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `norm(a:real^3) * del / (norm a + &1) =
                  del * (norm a / (norm a + &1))` SUBST1_TAC THENL
     [REWRITE_TAC[real_div] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MATCH_MP REAL_LT_LDIV_EQ (ASSUME `&0 < norm(a:real^3) + &1`)] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x:real^3. x IN UNIONS K /\ dist(u,x) < r0 ==> x IN UNIONS c`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
    MATCH_MP_TAC MOI_STL_FAR_IN_SPHERE THEN
    MAP_EVERY EXISTS_TAC [`a:real^3`; `(a:real^3) dot p`; `f:real^3->real^3`;
      `D:real^3->bool`; `convex hull {A:real^3,B,C}`; `del:real`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `D UNION D' = IMAGE (f:real^3->real^3) (UNIONS c)` THEN SET_TAC[];
      ASM_MESON_TAC[];
      SUBGOAL_THEN `abs((a:real^3) dot x - a dot u) <= norm a * dist(u,x)`
      MP_TAC THENL
       [REWRITE_TAC[dist; GSYM DOT_RSUB] THEN ONCE_REWRITE_TAC[NORM_SUB] THEN
        REWRITE_TAC[NORM_CAUCHY_SCHWARZ_ABS];
        ALL_TAC] THEN
      SUBGOAL_THEN `norm(a:real^3) * dist(u:real^3,x) <= norm a * r0` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[NORM_POS_LE; REAL_LT_IMP_LE];
        ALL_TAC] THEN
      UNDISCH_TAC `~(abs((a:real^3) dot u - a dot p) < &2 * del)` THEN
      UNDISCH_TAC `norm(a:real^3) * r0 < del` THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `a1:real^3`; `K:(real^3->bool)->bool`;
                 `u:real^3`; `r0:real`] MOI_STL_BOUND_FAR) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `{u:real^3} IN c` THENL
   [REWRITE_TAC[ASSUME `{u:real^3} IN c`] THEN DISCH_TAC THEN
    SUBGOAL_THEN `moi_sch3_crossings c (a1:real^3) u = moi_sch3_crossings c a u`
    ASSUME_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        is_forall(concl th) &&
        can (find_term ((=) `moi_sch3_crossings c (a1:real^3)`)) (concl th) &&
        can (find_term ((=) `moi_sch3_crossings c (a:real^3)`)) (concl th))) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [ASM_ARITH_TAC;
      DISCH_THEN SUBST_ALL_TAC THEN ASM_REAL_ARITH_TAC;
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        is_forall(concl th) && can (find_term ((=) `&2 * del`)) (concl th) &&
        can (find_term ((=)
          `moi_sch3_level_polygons (UNIONS K) (a1:real^3)`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]);;

let MOI_STL_CAP_INDEX = prove
 (mk_imp(MOI_STL_CAP_COUNT,
  `!c (a:real^3) p del j0 (f:real^3->real^3) g t D D' sigma.
     moi_sch3_generic c a /\ pl_sphere 2 (UNIONS c) /\ {p} IN c /\
     4 <= moi_sch3_crossings c a p /\
     2 <= CARD (moi_sch3_level_polygons (UNIONS c) a (a dot p)) /\
     &0 < del /\
     (!v. {v} IN c /\ ~(v = p) ==> &4 * del <= abs(a dot v - a dot p)) /\
     j0 IN moi_sch3_level_polygons (UNIONS c) a (a dot p) /\
     pl_homeomorphism ((:real^3),(:real^3)) (f,g) /\ (!x. a dot f x = a dot x) /\
     (!x. del <= abs(a dot x - a dot p) ==> f x = x) /\
     &2 simplex t /\ t SUBSET {x | a dot x = a dot p} /\
     IMAGE f (UNIONS c) INTER t = relative_frontier t /\
     IMAGE f j0 = relative_frontier t /\
     (f p IN t ==> {f p} face_of t) /\
     pl_cell_with_boundary 2 D (relative_frontier t) /\
     pl_cell_with_boundary 2 D' (relative_frontier t) /\
     D UNION D' = IMAGE f (UNIONS c) /\ D INTER D' = relative_frontier t /\
     D INTER t = relative_frontier t /\ pl_sphere 2 (D UNION t) /\
     (sigma = &1 \/ sigma = -- &1) /\
     (!x. x IN relative_frontier t /\ ~(x = f p)
          ==> ?r. &0 < r /\
                  !y. y IN D /\ dist(x,y) < r ==> &0 <= sigma * (a dot y - a dot p))
     ==> ?K (a1:real^3). moi_sch3_generic K a1 /\ UNIONS K = D UNION t /\
                         moi_sch3_index K a1 < moi_sch3_index c a`),
  DISCH_THEN(LABEL_TAC "cc") THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[REAL_ARITH `sigma = &1 \/ sigma = -- &1 <=> abs sigma = &1`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `sigma = &1 \/ sigma = -- &1` ASSUME_TAC THENL
   [UNDISCH_TAC `abs sigma = &1` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`t:real^3->bool`; `(f:real^3->real^3) p`] MOI_STL_TILT_DIRECTION) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `b:real^3`) THEN
  MP_TAC(ISPEC `t:real^3->bool` MOI_STL_TRIANGLE_CORNERS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `A:real^3` (X_CHOOSE_THEN `B:real^3`
    (X_CHOOSE_THEN `C:real^3` STRIP_ASSUME_TAC))) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
    concl th = `t = convex hull {A:real^3,B,C}`)) THEN
  SUBGOAL_THEN `D SUBSET IMAGE (f:real^3->real^3) (UNIONS c)` ASSUME_TAC THENL
   [UNDISCH_TAC `D UNION D' = IMAGE (f:real^3->real^3) (UNIONS c)` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `closed(D:real^3->bool) /\ closed(D':real^3->bool)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
    MATCH_MP_TAC PL_POLYHEDRON_IMP_COMPACT THEN
    REMOVE_THEN "cc" (K ALL_TAC) THEN ASM_MESON_TAC[MOI_STL_CELL_POLYHEDRON];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`D:real^3->bool`; `A:real^3`; `B:real^3`; `C:real^3`;
                 `if (f:real^3->real^3) p IN D UNION convex hull {A,B,C}
                  then f p else A`] MOI_STL_CAP_TRIANGULATION) THEN
  ANTS_TAC THENL
   [REMOVE_THEN "cc" (K ALL_TAC) THEN
    CONJ_TAC THENL [ASM_MESON_TAC[MOI_STL_CELL_POLYHEDRON]; ALL_TAC] THEN
    COND_CASES_TAC THENL
     [ASM_MESON_TAC[IN_UNION];
      DISJ2_TAC THEN SIMP_TAC[HULL_INC; IN_INSERT]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `K:(real^3->bool)->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(f:real^3->real^3) p IN D UNION convex hull {A,B,C} ==> {f p} IN K`
  ASSUME_TAC THENL
   [DISCH_TAC THEN
    UNDISCH_TAC `{(if (f:real^3->real^3) p IN D UNION convex hull {A,B,C}
                   then f p else A)} IN K` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_sphere 2 (UNIONS K:real^3->bool)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `?e. &0 < e /\
        !(a1:real^3) eta.
          &0 < eta /\ eta < e /\ norm(a1 - (a + (sigma * eta) % b)) < e * eta /\
          moi_sch3_generic K a1 /\ {(f:real^3->real^3) p} IN K
          ==> CARD (moi_sch3_level_polygons (D UNION convex hull {A,B,C}) a1
                     (a1 dot f p)) + 1 <=
              CARD (moi_sch3_level_polygons (UNIONS c) a (a dot p))`
  STRIP_ASSUME_TAC THENL
   [ASM_CASES_TAC `(f:real^3->real^3) p IN D UNION convex hull {A,B,C}` THENL
     [USE_THEN "cc" (MP_TAC o SPECL
       [`c:(real^3->bool)->bool`; `a:real^3`; `p:real^3`; `f:real^3->real^3`;
        `g:real^3->real^3`; `convex hull {A:real^3,B,C}`; `D:real^3->bool`;
        `b:real^3`; `sigma:real`; `K:(real^3->bool)->bool`]) THEN
      ANTS_TAC THENL
       [REMOVE_THEN "cc" (K ALL_TAC) THEN
        ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[MOI_SLV_SC_BASIC];
        ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `e:real` THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `eta:real` THEN ASM_REWRITE_TAC[];
      EXISTS_TAC `&1` THEN REWRITE_TAC[REAL_LT_01] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC(TAUT `F ==> p`) THEN
      UNDISCH_TAC `~((f:real^3->real^3) p IN D UNION convex hull {A,B,C})` THEN
      REWRITE_TAC[] THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        concl th = `UNIONS K = D UNION convex hull {A:real^3,B,C}`)) THEN
      REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `{(f:real^3->real^3) p}` THEN
      ASM_REWRITE_TAC[IN_SING]];
    ALL_TAC] THEN
  REMOVE_THEN "cc" (K ALL_TAC) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP CROSSINGS_STABLE o check (fun th ->
    concl th = `moi_sch3_generic c (a:real^3)`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `ecs:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "cs"))) THEN
  SUBGOAL_THEN
   `?R0. &0 < R0 /\ UNIONS c SUBSET cball(vec 0:real^3,R0) /\
         D UNION convex hull {A,B,C} SUBSET cball(vec 0:real^3,R0)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`UNIONS c UNION D UNION convex hull {A:real^3,B,C}`; `vec 0:real^3`]
      BOUNDED_SUBSET_CBALL) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[BOUNDED_UNION] THEN REPEAT CONJ_TAC THEN
      MATCH_MP_TAC COMPACT_IMP_BOUNDED THENL
       [MATCH_MP_TAC PL_POLYHEDRON_IMP_COMPACT THEN
        MATCH_MP_TAC MOI_SCD_PL_SPHERE_POLYHEDRON THEN EXISTS_TAC `2` THEN
        ASM_REWRITE_TAC[];
        MATCH_MP_TAC PL_POLYHEDRON_IMP_COMPACT THEN
        MATCH_MP_TAC MOI_STL_CELL_POLYHEDRON THEN
        MAP_EVERY EXISTS_TAC
         [`2`; `relative_frontier(convex hull {A:real^3,B,C})`] THEN
        ASM_REWRITE_TAC[];
        MATCH_MP_TAC FINITE_IMP_COMPACT_CONVEX_HULL THEN
        REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY]];
      ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(MATCH_MP MOI_SCD_FAR_LEVELS
    (CONJ LEVEL_STABLE (CONJ LEVEL_POLYGONS_FINITE CROSSINGS_STABLE))) THEN
  DISCH_THEN(MP_TAC o SPECL [`c:(real^3->bool)->bool`; `a:real^3`;
    `(a:real^3) dot p`; `&2 * del`; `R0:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `efar:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "far"))) THEN
  MP_TAC(ISPECL [`{v:real^3 | {v} IN K}`; `a:real^3`] MOI_STL_SIGN_CLOSE) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC MOI_SLV_VERTICES_FINITE THEN
    UNDISCH_TAC `simplicial_complex (K:(real^3->bool)->bool)` THEN
    SIMP_TAC[simplicial_complex];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `esg:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "sg"))) THEN
  SUBGOAL_THEN `&0 < min ecs (min efar esg)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_LT_MIN]; ALL_TAC] THEN
  ABBREV_TAC `E = min ecs (min efar esg)` THEN
  SUBGOAL_THEN `?eta. &0 < eta /\ eta < e /\ eta * (norm(b:real^3) + e) < E`
  STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `min (e / &2) (E / (&2 * (norm(b:real^3) + e + &1)))` THEN
    SUBGOAL_THEN `&0 < &2 * (norm(b:real^3) + e + &1)` ASSUME_TAC THENL
     [MP_TAC(ISPEC `b:real^3` NORM_POS_LE) THEN UNDISCH_TAC `&0 < e` THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[REAL_LT_MIN] THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LT_DIV THEN
      UNDISCH_TAC `&0 < e` THEN UNDISCH_TAC `&0 < E` THEN
      UNDISCH_TAC `&0 < &2 * (norm(b:real^3) + e + &1)` THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `e / &2` THEN
      REWRITE_TAC[REAL_MIN_LE; REAL_LE_REFL] THEN UNDISCH_TAC `&0 < e` THEN
      REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LET_TRANS THEN
      EXISTS_TAC `E / (&2 * (norm(b:real^3) + e + &1)) * (norm b + e)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_MIN_LE; REAL_LE_REFL] THEN
        MP_TAC(ISPEC `b:real^3` NORM_POS_LE) THEN UNDISCH_TAC `&0 < e` THEN
        REAL_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `E / (&2 * (norm(b:real^3) + e + &1)) * (norm b + e) =
                    (E * (norm b + e)) / (&2 * (norm b + e + &1))` SUBST1_TAC THENL
       [REWRITE_TAC[real_div] THEN REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[MATCH_MP REAL_LT_LDIV_EQ
        (ASSUME `&0 < &2 * (norm(b:real^3) + e + &1)`)] THEN
      SUBGOAL_THEN `&0 <= E * (norm(b:real^3) + e)` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN MP_TAC(ISPEC `b:real^3` NORM_POS_LE) THEN
        UNDISCH_TAC `&0 < e` THEN UNDISCH_TAC `&0 < E` THEN REAL_ARITH_TAC;
        UNDISCH_TAC `&0 < E` THEN REAL_ARITH_TAC]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`K:(real^3->bool)->bool`; `a + (sigma * eta) % b:real^3`;
                 `e * eta`] GENERIC_NEAR) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [ASM_REWRITE_TAC[]; MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `a1:real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `norm(a1 - a:real^3) < E` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `norm(a1 - (a + (sigma * eta) % b:real^3)) +
                norm((sigma * eta) % b:real^3)` THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`a1 - (a + (sigma * eta) % b:real^3)`;
                     `(sigma * eta) % b:real^3`] NORM_TRIANGLE) THEN
      REWRITE_TAC[VECTOR_ARITH `(a1 - (a + v)) + v:real^3 = a1 - a`];
      ALL_TAC] THEN
    REWRITE_TAC[NORM_MUL; REAL_ABS_MUL] THEN
    SUBGOAL_THEN `abs sigma = &1 /\ abs eta = eta` (fun th -> REWRITE_TAC[th]) THENL
     [CONJ_TAC THENL [ASM_REWRITE_TAC[]; UNDISCH_TAC `&0 < eta` THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    UNDISCH_TAC `norm(a1 - (a + (sigma * eta) % b:real^3)) < e * eta` THEN
    UNDISCH_TAC `eta * (norm(b:real^3) + e) < E` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `norm(a1 - a:real^3) < ecs /\ norm(a1 - a:real^3) < efar /\
                norm(a1 - a:real^3) < esg` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `norm(a1 - a:real^3) < E` THEN EXPAND_TAC "E" THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "cs" (MP_TAC o C MATCH_MP (ASSUME `norm(a1 - a:real^3) < ecs`)) THEN
  STRIP_TAC THEN
  USE_THEN "sg" (MP_TAC o C MATCH_MP (ASSUME `norm(a1 - a:real^3) < esg`)) THEN
  REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!q:real^3. {q} IN c /\ &2 * del <= abs(a dot q - a dot p)
               ==> CARD (moi_sch3_level_polygons (UNIONS K) a1 (a1 dot q)) <=
                   CARD (moi_sch3_level_polygons (UNIONS c) a (a dot q))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN USE_THEN "far" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[REAL_FIELD `(&2 * del) / &2 = del`; SUBSET; IN_INTER; IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
    MATCH_MP_TAC MOI_STL_FAR_IN_SPHERE THEN
    MAP_EVERY EXISTS_TAC [`a:real^3`; `(a:real^3) dot p`; `f:real^3->real^3`;
      `D:real^3->bool`; `convex hull {A:real^3,B,C}`; `del:real`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`K:(real^3->bool)->bool`; `a1:real^3`] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MOI_SCD_INDEX_COMPARE THEN
  MAP_EVERY EXISTS_TAC [`p:real^3`; `(f:real^3->real^3) p`] THEN
  REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `moi_sch3_generic c (a:real^3)` THEN
    SIMP_TAC[moi_sch3_generic; simplicial_complex];
    UNDISCH_TAC `simplicial_complex (K:(real^3->bool)->bool)` THEN
    SIMP_TAC[simplicial_complex];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOI_STL_CAP_VERTEX_BOUNDS THEN
    MAP_EVERY EXISTS_TAC [`j0:real^3->bool`; `del:real`; `g:real^3->real^3`;
      `A:real^3`; `B:real^3`; `C:real^3`; `D:real^3->bool`; `D':real^3->bool`] THEN
    ASM_REWRITE_TAC[];
    STRIP_TAC THEN
    SUBGOAL_THEN `CARD (moi_sch3_level_polygons (D UNION convex hull {A:real^3,B,C})
                    a1 (a1 dot (f:real^3->real^3) p)) + 1 <=
                  CARD (moi_sch3_level_polygons (UNIONS c) a (a dot p))` MP_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `sigma:real`)) (concl th) &&
        can (find_term ((=) `b:real^3`)) (concl th))) THEN
      EXISTS_TAC `eta:real` THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* 11. Moise 17.12 Lemma 1 (REDUCE) from the cap count: convexify the inmost *)
(* disk at a singular vertex of positive summand, split the image sphere     *)
(* along the triangle boundary, and tilt each cap in the direction of its    *)
(* side.  This file proves REDUCE_FROM_COUNT; with CAP_COUNT of              *)
(* pc_moi_sch3_capc it gives REDUCE (composed in pc_moi_sch3_all).           *)
(* ------------------------------------------------------------------------- *)

let REDUCE_FROM_COUNT = prove
 (mk_imp(MOI_STL_CAP_COUNT, MOI_SCH3_REDUCE),
  DISCH_THEN(LABEL_TAC "cc") THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `a:real^3`] MOI_STL_POSITIVE_SUMMAND) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^3` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `a:real^3`; `p:real^3`; `w:real^3->bool`]
    MOI_STL_CONVEXIFIED) THEN
  ASM_REWRITE_TAC[TAUT `p \/ ~q <=> (q ==> p)`] THEN
  DISCH_THEN(X_CHOOSE_THEN `del:real` (X_CHOOSE_THEN `j0:real^3->bool`
    (X_CHOOSE_THEN `d0:real^3->bool` (X_CHOOSE_THEN `f:real^3->real^3`
    (X_CHOOSE_THEN `g:real^3->real^3` (X_CHOOSE_THEN `t:real^3->bool`
    STRIP_ASSUME_TAC)))))) THEN
  SUBGOAL_THEN `!x y. (f:real^3->real^3) x = f y ==> x = y` ASSUME_TAC THENL
   [UNDISCH_TAC `pl_homeomorphism ((:real^3),(:real^3)) (f:real^3->real^3,g)` THEN
    REWRITE_TAC[pl_homeomorphism; homeomorphism; IN_UNIV] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x. del <= abs((a:real^3) dot x - a dot p) ==> (f:real^3->real^3) x = x`
  ASSUME_TAC THENL [REMOVE_THEN "cc" (K ALL_TAC) THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!x. ~(x IN w) ==> (f:real^3->real^3) x = x` ASSUME_TAC THENL
   [REMOVE_THEN "cc" (K ALL_TAC) THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `t SUBSET {x:real^3 | a dot x = a dot p}` ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `IMAGE (f:real^3->real^3) d0 = t`)) THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `d0 SUBSET {x:real^3 | a dot x = a dot p}` THEN
    UNDISCH_TAC `(x:real^3) IN d0` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (f:real^3->real^3) (UNIONS c) INTER t = relative_frontier t`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `IMAGE (f:real^3->real^3) j0 = relative_frontier t`)) THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `IMAGE (f:real^3->real^3) d0 = t`)) THEN
    REWRITE_TAC[GSYM(MATCH_MP IMAGE_INTER_INJ
      (ASSUME `!x y. (f:real^3->real^3) x = f y ==> x = y`))] THEN
    AP_TERM_TAC THEN ONCE_REWRITE_TAC[INTER_COMM] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(f:real^3->real^3) p IN t ==> {f p} face_of t` ASSUME_TAC THENL
   [DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `(f:real^3->real^3) p IN t` THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `IMAGE (f:real^3->real^3) d0 = t`)) THEN
    REWRITE_TAC[IN_IMAGE] THEN REMOVE_THEN "cc" (K ALL_TAC) THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `j0 SUBSET UNIONS c /\ pl_sphere 1 (j0:real^3->bool)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `j0 IN moi_sch3_level_polygons (UNIONS c) a (a dot (p:real^3))` THEN
    REWRITE_TAC[moi_sch3_level_polygons; IN_ELIM_THM] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_sphere 2 (IMAGE (f:real^3->real^3) (UNIONS c)) /\
                pl_sphere 1 (relative_frontier t:real^3->bool)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC MOI_STL_SPHERE_IMAGE THEN EXISTS_TAC `g:real^3->real^3` THEN
      ASM_REWRITE_TAC[];
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        concl th = `IMAGE (f:real^3->real^3) j0 = relative_frontier t`)) THEN
      MATCH_MP_TAC MOI_STL_SPHERE_IMAGE THEN EXISTS_TAC `g:real^3->real^3` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (f:real^3->real^3) (UNIONS c)`; `relative_frontier t:real^3->bool`]
    SPHERE_SPLIT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `IMAGE (f:real^3->real^3) (UNIONS c) INTER t = relative_frontier t` THEN
    SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `D1:real^3->bool` (X_CHOOSE_THEN `D2:real^3->bool`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`IMAGE (f:real^3->real^3) (UNIONS c)`; `t:real^3->bool`;
                 `D1:real^3->bool`; `D2:real^3->bool`] MOI_STL_CAP_SPHERES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `a:real^3`; `p:real^3`; `j0:real^3->bool`;
                 `f:real^3->real^3`; `g:real^3->real^3`; `D1:real^3->bool`;
                 `D2:real^3->bool`] MOI_STL_SIDES) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `sigma:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC))) THEN
  USE_THEN "cc" (fun th -> LABEL_TAC "ci" (MATCH_MP MOI_STL_CAP_INDEX th)) THEN
  USE_THEN "ci" (MP_TAC o SPECL [`c:(real^3->bool)->bool`; `a:real^3`; `p:real^3`;
    `del:real`; `j0:real^3->bool`; `f:real^3->real^3`; `g:real^3->real^3`;
    `t:real^3->bool`; `D1:real^3->bool`; `D2:real^3->bool`; `sigma:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `K1:(real^3->bool)->bool` (X_CHOOSE_THEN `a1:real^3`
    STRIP_ASSUME_TAC)) THEN
  USE_THEN "ci" (MP_TAC o SPECL [`c:(real^3->bool)->bool`; `a:real^3`; `p:real^3`;
    `del:real`; `j0:real^3->bool`; `f:real^3->real^3`; `g:real^3->real^3`;
    `t:real^3->bool`; `D2:real^3->bool`; `D1:real^3->bool`; `--sigma`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ONCE_REWRITE_TAC[UNION_COMM] THEN ASM_REWRITE_TAC[];
      ONCE_REWRITE_TAC[INTER_COMM] THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `sigma = &1 \/ sigma = -- &1` THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `K2:(real^3->bool)->bool` (X_CHOOSE_THEN `a2:real^3`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`f:real^3->real^3`; `g:real^3->real^3`;
    `K1:(real^3->bool)->bool`; `a1:real^3`; `K2:(real^3->bool)->bool`; `a2:real^3`;
    `t:real^3->bool`; `relative_frontier t:real^3->bool`] THEN
  ASM_REWRITE_TAC[moi_sch3_plane_cell] THEN CONJ_TAC THENL
   [MATCH_MP_TAC MOI_STL_SIMPLEX_CELL THEN ASM_REWRITE_TAC[];
    MAP_EVERY EXISTS_TAC [`a:real^3`; `(a:real^3) dot p`] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `moi_sch3_generic c (a:real^3)` THEN
    REWRITE_TAC[moi_sch3_generic] THEN MESON_TAC[]]);;

