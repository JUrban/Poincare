(* ========================================================================= *)
(* pc_moi_sch3_stmt: the PL Schoenflies theorem in real^3, Moise GTM 47,     *)
(* Sec 17 (printed pp.117-126, Theorems 1-12), broken into statements.       *)
(* Section 1 gives the definitions (prefix moi_sch3), section 2 the          *)
(* statement terms (OCaml values MOI_SCH3_...), each the exact statement of  *)
(* a theorem proved in one of the pc_moi_sch3 files, section 3 the glue      *)
(* theorems (MOI_SCD_...), which derive PL_SCHOENFLIES_3_STATEMENT and       *)
(* PL_SCHOENFLIES_3_AMBIENT_STATEMENT of pc_moi_stmt.ml and their            *)
(* corollaries from the statement terms taken as hypotheses, and section 4   *)
(* sanity theorems.  pc_moi_sch3_all discharges the hypotheses.              *)
(* ========================================================================= *)

needs "src/pc_moi_core_stmt.ml";;
needs "src/pc_moi_fnd1.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* 1. Definitions.                                                           *)
(* ------------------------------------------------------------------------- *)

(* Simply imbedded (Moise p.120; DG IsSimplyEmbedded without its sphere      *)
(* conjunct): for every convex open w containing s there is a PL            *)
(* homeomorphism of real^3, the identity off w, carrying s onto the         *)
(* boundary of a 3-simplex.  PL_SCHOENFLIES_3_AMBIENT_STATEMENT says that   *)
(* every PL 2-sphere is simply imbedded.                                     *)

let moi_sch3_simple = new_definition
 `moi_sch3_simple (s:real^3->bool) <=>
    !w. convex w /\ open w /\ s SUBSET w
        ==> ?(k:real^3->bool) f g.
              &3 simplex k /\ pl_homeomorphism ((:real^3),(:real^3)) (f,g) /\
              (!x. ~(x IN w) ==> f x = x) /\ IMAGE f s = relative_frontier k`;;

(* The push property of a cell c at a disk d with boundary j in its         *)
(* frontier (Moise p.118, reformulated): for every open u containing c and  *)
(* every polyhedron v meeting c only inside j, a PL homeomorphism of real^3 *)
(* that is the identity off u and on v carries d onto the complementary     *)
(* disk (frontier c DIFF d) UNION j.  The book quantifies over polyhedral   *)
(* closed neighbourhoods N of c minus j; the form with u and v is what the  *)
(* deletion steps use (v is the rest of the sphere being pushed) and it is  *)
(* true for simplices because polyhedra meet at positive angles.            *)

let moi_sch3_push = new_definition
 `moi_sch3_push (c:real^3->bool) (d:real^3->bool) (j:real^3->bool) <=>
    !u v. open u /\ c SUBSET u /\ pl_polyhedron v /\ v INTER c SUBSET j
          ==> ?f g. pl_homeomorphism ((:real^3),(:real^3)) (f,g) /\
                    (!x. ~(x IN u) ==> f x = x) /\
                    (!x. x IN v ==> f x = x) /\
                    IMAGE f d = (frontier c DIFF d) UNION j`;;

(* Height functions x |-> a dot x in general position for a triangulation  *)
(* c (Moise p.122: no horizontal plane contains two vertices).              *)

let moi_sch3_generic = new_definition
 `moi_sch3_generic (c:(real^3->bool)->bool) (a:real^3) <=>
    simplicial_complex c /\ ~(a = vec 0) /\
    !v w. {v} IN c /\ {w} IN c /\ a dot v = a dot w ==> v = w`;;

(* Number of link edges of the vertex v that cross the level of v.  For a   *)
(* generic height on a combinatorial surface it is 2k, where k is the       *)
(* number of level polygons through v (k = 0: extremum, k = 1: regular,     *)
(* k >= 2: singular point of Moise p.122).                                  *)

let moi_sch3_crossings = new_definition
 `moi_sch3_crossings (c:(real^3->bool)->bool) (a:real^3) (v:real^3) =
    CARD {e | e IN simplicial_link c v /\
              ?x y. e = segment[x,y] /\ a dot x < a dot v /\ a dot v < a dot y}`;;

(* The polygons (PL 1-spheres) in a level set (DG levelPolygons).           *)

let moi_sch3_level_polygons = new_definition
 `moi_sch3_level_polygons (s:real^3->bool) (a:real^3) (t:real) =
    {p | pl_sphere 1 p /\ p SUBSET s INTER {x | a dot x = t}}`;;

(* Moise's index (p.122): the sum over the singular vertices v of the       *)
(* number of polygons in the level set through v, minus one.                *)

let moi_sch3_index = new_definition
 `moi_sch3_index (c:(real^3->bool)->bool) (a:real^3) =
    nsum {v | {v} IN c /\ 4 <= moi_sch3_crossings c a v}
         (\v. CARD (moi_sch3_level_polygons (UNIONS c) a (a dot v)) - 1)`;;

(* Index zero in combinatorial form: generic, no singular vertex.           *)

let moi_sch3_saddle_free = new_definition
 `moi_sch3_saddle_free (c:(real^3->bool)->bool) (a:real^3) <=>
    moi_sch3_generic c a /\
    !v. {v} IN c ==> moi_sch3_crossings c a v <= 2`;;

(* A plane 2-cell with boundary j (Moise p.121, Theorem 11).                *)

let moi_sch3_plane_cell = new_definition
 `moi_sch3_plane_cell (d:real^3->bool) (j:real^3->bool) <=>
    pl_cell_with_boundary 2 d j /\
    ?b r. ~(b = vec 0) /\ d SUBSET {x:real^3 | b dot x = r}`;;

(* The fibred structure of an index-zero sphere (conclusion of Moise        *)
(* Lemmas 2-3, p.123): the lowest and highest levels meet s in single       *)
(* points and every level in between meets s in a PL circle that bounds the *)
(* fibre of the filled sphere, a plane 2-cell.                              *)

let moi_sch3_fibred = new_definition
 `moi_sch3_fibred (s:real^3->bool) (a:real^3) (lo:real) (hi:real) <=>
    ~(a = vec 0) /\ lo < hi /\
    (!x. x IN s ==> lo <= a dot x /\ a dot x <= hi) /\
    (?p. s INTER {x | a dot x = lo} = {p}) /\
    (?q. s INTER {x | a dot x = hi} = {q}) /\
    (!t. lo < t /\ t < hi
         ==> pl_cell_with_boundary 2 ((s UNION inside s) INTER {x | a dot x = t})
                                     (s INTER {x | a dot x = t}))`;;


(* ------------------------------------------------------------------------- *)
(* 2. Statement terms.  Each term is the exact statement of a theorem proved *)
(* in one of the pc_moi_sch3 files; the glue of section 3 takes them as      *)
(* hypotheses.                                                               *)
(* Book anchors: Moise GTM 47 (PDF page = printed page + 9).                *)
(* ------------------------------------------------------------------------- *)

(* 2D foundations (pc_moi_sch3_amb2, pc_moi_sch3_s2).  Moise Sec 3 Thm 7    *)
(* (p.29) with the PLH proofs of Thms 3.4-3.7; a PL circle splits a PL      *)
(* 2-sphere into two PL disks (DG PL/SphereSchoenflies.lean:169); gluing    *)
(* two PL disks along their boundary; a plane disk lies in the hull of its  *)
(* boundary.                                                                *)

let MOI_SCH3_AMB2 = `PL_SCHOENFLIES_2_AMBIENT_STATEMENT`;;

let MOI_SCH3_AMB2_VERTEX =
 `!s w (p:real^2).
     pl_sphere 1 s /\ open w /\ s UNION inside s SUBSET w /\ p IN s
     ==> ?(t:real^2->bool) f g.
           &2 simplex t /\ pl_homeomorphism ((:real^2),(:real^2)) (f,g) /\
           (!x. ~(x IN w) ==> f x = x) /\ IMAGE f s = relative_frontier t /\
           {f p} face_of t`;;

let MOI_SCH3_SPHERE_SPLIT =
 `!s j:real^3->bool.
     pl_sphere 2 s /\ pl_sphere 1 j /\ j SUBSET s
     ==> ?d1 d2. pl_cell_with_boundary 2 d1 j /\ pl_cell_with_boundary 2 d2 j /\
                 d1 UNION d2 = s /\ d1 INTER d2 = j`;;

let MOI_SCH3_DISK_COMPLEMENT =
 `!s d j:real^3->bool.
     pl_sphere 2 s /\ pl_cell_with_boundary 2 d j /\ d SUBSET s
     ==> pl_cell_with_boundary 2 ((s DIFF d) UNION j) j`;;

let MOI_SCH3_DISK_UNION =
 `!d1 d2 j:real^3->bool.
     pl_cell_with_boundary 2 d1 j /\ pl_cell_with_boundary 2 d2 j /\
     d1 INTER d2 = j
     ==> pl_sphere 2 (d1 UNION d2)`;;

let MOI_SCH3_PLANE_CELL_HULL =
 `!d j:real^3->bool. moi_sch3_plane_cell d j ==> d SUBSET convex hull j`;;

(* pc_moi_sch3_push: Thm 4 (p.118, a 3-simplex has the push property at a   *)
(* 2-face) and Thms 5-6 (pp.119-120, at every PL disk in its boundary).     *)
(* Thms 7-8 are proved below from these (MOI_SCD_PUSH_PLH,                  *)
(* MOI_SCD_SIMPLE_PUSH).                                                    *)

let MOI_SCH3_FACE_PUSH =
 `!k f:real^3->bool.
     &3 simplex k /\ f face_of k /\ aff_dim f = &2
     ==> moi_sch3_push k f (relative_frontier f)`;;

let MOI_SCH3_SIMPLEX_PUSH =
 `!k d j:real^3->bool.
     &3 simplex k /\ pl_cell_with_boundary 2 d j /\ d SUBSET relative_frontier k
     ==> moi_sch3_push k d j`;;

(* pc_moi_sch3_free: Thms 2-3 (p.118) for polygonal cell decompositions of  *)
(* a PL 2-cell in the plane, with the deletion of a free cell (the          *)
(* remaining cells still form a PL 2-cell).  Users transfer their level     *)
(* planes and boundary disks to real^2 by affine maps and PLHs.             *)

let MOI_SCH3_FREE_CELL =
 `!g g0 (j:real^2->bool).
     FINITE g /\ 2 <= CARD g /\
     (!c. c IN g ==> polytope c /\ aff_dim c = &2) /\
     (!c c'. c IN g /\ c' IN g
             ==> (c INTER c') face_of c /\ (c INTER c') face_of c') /\
     pl_cell_with_boundary 2 (UNIONS g) j /\
     g0 SUBSET g /\ (g0 = {} \/ ?j0. pl_cell_with_boundary 2 (UNIONS g0) j0) /\
     ~(g0 = g)
     ==> ?c. c IN g /\ ~(c IN g0) /\
             pl_ball 1 (relative_frontier c INTER j) /\
             pl_cell_with_boundary 2 (UNIONS (g DELETE c))
               (closure ((j UNION relative_frontier c) DIFF
                         (relative_frontier c INTER j)))`;;

(* pc_moi_sch3_glue: Thm 9 (p.121) for cones over PL 2-spheres from an      *)
(* interior point (convex cells are the case of a polytope), Thm 10 (p.121, *)
(* cones over PL 2-disks) and Thm 11 (pp.121-122, gluing two simply         *)
(* imbedded spheres along a plane 2-cell, both nesting cases).              *)

let MOI_SCH3_STAR_SIMPLE =
 `!s (v:real^3).
     pl_sphere 2 s /\ v IN inside s /\
     (!x y. x IN s /\ y IN s /\ y IN segment[v,x] ==> y = x)
     ==> moi_sch3_simple s`;;

let MOI_SCH3_CONE_DISK_SIMPLE =
 `!d j (v:real^3).
     pl_cell_with_boundary 2 d j /\ ~(v IN d) /\
     (!x y. x IN d /\ y IN d /\ y IN segment[v,x] ==> y = x)
     ==> moi_sch3_simple (d UNION UNIONS {segment[v,x] | x IN j})`;;

let MOI_SCH3_THM11 =
 `!s1 s2 d j:real^3->bool.
     moi_sch3_simple s1 /\ moi_sch3_simple s2 /\ moi_sch3_plane_cell d j /\
     s1 INTER s2 = d
     ==> moi_sch3_simple ((s1 UNION s2) DIFF (d DIFF j))`;;

(* pc_moi_sch3_gen and pc_moi_sch3_lev: height functions on triangulated PL *)
(* 2-spheres (Moise p.122): general position, stability of crossing data,   *)
(* the index vanishing only for saddle-free heights, inmost polygons at     *)
(* singular levels, the filled sphere is triangulable.                      *)

let MOI_SCH3_GENERIC_NEAR =
 `!c (a0:real^3) e.
     simplicial_complex c /\ &0 < e
     ==> ?a. moi_sch3_generic c a /\ norm(a - a0) < e`;;

let MOI_SCH3_CROSSINGS_STABLE =
 `!c (a:real^3).
     moi_sch3_generic c a
     ==> ?e. &0 < e /\
             !a'. norm(a' - a) < e
                  ==> moi_sch3_generic c a' /\
                      !v. {v} IN c
                          ==> moi_sch3_crossings c a' v = moi_sch3_crossings c a v`;;

let MOI_SCH3_FILLING_TRIANGULATION =
 `!s:real^3->bool.
     pl_sphere 2 s
     ==> ?k. simplicial_complex k /\ UNIONS k = s UNION inside s`;;

let MOI_SCH3_INDEX_ZERO =
 `!c (a:real^3).
     moi_sch3_generic c a /\ pl_sphere 2 (UNIONS c) /\ moi_sch3_index c a = 0
     ==> moi_sch3_saddle_free c a`;;

let MOI_SCH3_INMOST =
 `!c (a:real^3) v.
     moi_sch3_generic c a /\ pl_sphere 2 (UNIONS c) /\ {v} IN c /\
     4 <= moi_sch3_crossings c a v
     ==> ?j d. j IN moi_sch3_level_polygons (UNIONS c) a (a dot v) /\
               pl_cell_with_boundary 2 d j /\ d SUBSET {x | a dot x = a dot v} /\
               d INTER UNIONS c = j`;;

let MOI_SCH3_LEVEL_POLYGONS_FINITE =
 `!c (a:real^3) t.
     moi_sch3_generic c a /\ pl_sphere 2 (UNIONS c)
     ==> FINITE (moi_sch3_level_polygons (UNIONS c) a t)`;;

let MOI_SCH3_SINGULAR_POLYGONS =
 `!c (a:real^3) v.
     moi_sch3_generic c a /\ pl_sphere 2 (UNIONS c) /\ {v} IN c
     ==> CARD {p | p IN moi_sch3_level_polygons (UNIONS c) a (a dot v) /\ v IN p} =
         moi_sch3_crossings c a v DIV 2 /\
         EVEN (moi_sch3_crossings c a v)`;;

let MOI_SCH3_LEVEL_STABLE =
 `!c (a:real^3).
     moi_sch3_generic c a /\ pl_sphere 2 (UNIONS c)
     ==> ?e. &0 < e /\
             !a' v. norm(a' - a) < e /\ {v} IN c
                    ==> CARD (moi_sch3_level_polygons (UNIONS c) a' (a' dot v)) =
                        CARD (moi_sch3_level_polygons (UNIONS c) a (a dot v))`;;

(* pc_moi_sch3_cvx: the first step of Lemma 1 (p.123): a PLH of the level   *)
(* plane makes the inmost disk a triangle with the singular point at a      *)
(* vertex (or outside it), extended to real^3 preserving every level, the   *)
(* identity off w and off a thin slab around the level.                     *)

let MOI_SCH3_LEVEL_CONVEXIFY =
 `!s (a:real^3) h j d p w del.
     compact s /\ ~(a = vec 0) /\ pl_cell_with_boundary 2 d j /\
     d SUBSET {x | a dot x = h} /\ d INTER s = j /\
     p IN s /\ a dot p = h /\ (p IN j \/ ~(p IN d)) /\
     convex w /\ open w /\ s SUBSET w /\ &0 < del
     ==> ?f g t. pl_homeomorphism ((:real^3),(:real^3)) (f,g) /\
                 (!x. a dot f x = a dot x) /\
                 (!x. ~(x IN w) \/ del <= abs(a dot x - h) ==> f x = x) /\
                 &2 simplex t /\ IMAGE f d = t /\
                 IMAGE f j = relative_frontier t /\
                 (p IN j ==> {f p} face_of t)`;;

(* pc_moi_sch3_tilt with pc_moi_sch3_capc: Lemma 1 (pp.122-123): if the     *)
(* index is positive, an ambient PLH (identity off w) carries s onto the    *)
(* union of two PL 2-spheres glued along a plane 2-cell, each with a        *)
(* generic height of smaller index (the axes rotated about a line through   *)
(* the singular point, in opposite directions).                             *)

let MOI_SCH3_REDUCE =
 `!c (a:real^3) w.
     moi_sch3_generic c a /\ pl_sphere 2 (UNIONS c) /\ 0 < moi_sch3_index c a /\
     convex w /\ open w /\ UNIONS c SUBSET w
     ==> ?f g c1 (a1:real^3) c2 (a2:real^3) d j.
           pl_homeomorphism ((:real^3),(:real^3)) (f,g) /\
           (!x. ~(x IN w) ==> f x = x) /\
           moi_sch3_generic c1 a1 /\ pl_sphere 2 (UNIONS c1) /\
           moi_sch3_index c1 a1 < moi_sch3_index c a /\
           moi_sch3_generic c2 a2 /\ pl_sphere 2 (UNIONS c2) /\
           moi_sch3_index c2 a2 < moi_sch3_index c a /\
           moi_sch3_plane_cell d j /\ UNIONS c1 INTER UNIONS c2 = d /\
           IMAGE f (UNIONS c) = (UNIONS c1 UNION UNIONS c2) DIFF (d DIFF j)`;;

(* pc_moi_sch3_fib: Lemmas 2-3 (pp.123-124) and the paragraph after them: a *)
(* saddle-free generic sphere is fibred by its levels.                      *)

let MOI_SCH3_SADDLE_FREE_FIBRED =
 `!c (a:real^3).
     moi_sch3_saddle_free c a /\ pl_sphere 2 (UNIONS c)
     ==> ?lo hi. moi_sch3_fibred (UNIONS c) a lo hi`;;

(* pc_moi_sch3_slab, pc_moi_sch3_slabb and pc_moi_sch3_slabc: Lemmas 4-6    *)
(* (pp.124-125) and the final gluing (p.125): a fibred sphere whose filling *)
(* is triangulated with a generic height is simply imbedded (slabs M_i,     *)
(* free cell deletion, cones, Thm 11).                                      *)

let MOI_SCH3_FIBRED_SIMPLE =
 `!s (a:real^3) lo hi k.
     pl_sphere 2 s /\ moi_sch3_fibred s a lo hi /\
     simplicial_complex k /\ UNIONS k = s UNION inside s /\
     (!v w. {v} IN k /\ {w} IN k /\ a dot v = a dot w ==> v = w)
     ==> moi_sch3_simple s`;;

let MOI_SCH3_TARGETS =
  [MOI_SCH3_AMB2; MOI_SCH3_AMB2_VERTEX; MOI_SCH3_SPHERE_SPLIT;
   MOI_SCH3_DISK_COMPLEMENT; MOI_SCH3_DISK_UNION; MOI_SCH3_PLANE_CELL_HULL;
   MOI_SCH3_FACE_PUSH; MOI_SCH3_SIMPLEX_PUSH; MOI_SCH3_FREE_CELL;
   MOI_SCH3_STAR_SIMPLE; MOI_SCH3_CONE_DISK_SIMPLE; MOI_SCH3_THM11;
   MOI_SCH3_GENERIC_NEAR; MOI_SCH3_CROSSINGS_STABLE;
   MOI_SCH3_FILLING_TRIANGULATION; MOI_SCH3_INDEX_ZERO; MOI_SCH3_INMOST;
   MOI_SCH3_LEVEL_POLYGONS_FINITE; MOI_SCH3_SINGULAR_POLYGONS;
   MOI_SCH3_LEVEL_STABLE; MOI_SCH3_LEVEL_CONVEXIFY; MOI_SCH3_REDUCE;
   MOI_SCH3_SADDLE_FREE_FIBRED; MOI_SCH3_FIBRED_SIMPLE];;

(* Every statement term is a closed boolean term. *)
map (fun t -> type_of t = bool_ty && frees t = []) MOI_SCH3_TARGETS;;

(* Two statements are derived from the others by the glue of section 3h:    *)
(* MOI_SCH3_AMB2 (from MOI_SCH3_AMB2_VERTEX) and MOI_SCH3_INDEX_ZERO (from  *)
(* MOI_SCH3_SINGULAR_POLYGONS and MOI_SCH3_LEVEL_POLYGONS_FINITE).  The     *)
(* other 22 (MOI_SCH3_UNIT_TARGETS) are proved in the pc_moi_sch3 files.    *)

let MOI_SCH3_DERIVED = [MOI_SCH3_AMB2; MOI_SCH3_INDEX_ZERO];;

let MOI_SCH3_UNIT_TARGETS =
  filter (fun t -> not (mem t MOI_SCH3_DERIVED)) MOI_SCH3_TARGETS;;

length MOI_SCH3_UNIT_TARGETS;;

(* ------------------------------------------------------------------------- *)
(* 3. Glue: the statement terms imply PL_SCHOENFLIES_3_STATEMENT and         *)
(* PL_SCHOENFLIES_3_AMBIENT_STATEMENT (pc_moi_stmt.ml), and the corollaries  *)
(* used by the PL core.                                                      *)
(* ------------------------------------------------------------------------- *)

(* 3a. PL homeomorphisms of real^3, simply imbedded spheres, inside.         *)

let MOI_SCD_PL_HOMEO_UNIV = prove
 (`!(f:real^3->real^3) g.
     pl_homeomorphism ((:real^3),(:real^3)) (f,g)
     ==> homeomorphism ((:real^3),(:real^3)) (f,g) /\
         (!x. g (f x) = x) /\ (!y. f (g y) = y) /\
         f continuous_on (:real^3) /\ g continuous_on (:real^3) /\
         pl_map_on (:real^3) f /\ pl_map_on (:real^3) g`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_homeomorphism; homeomorphism; IN_UNIV] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[]);;

let MOI_SCD_PL_MAP_ON_POLYHEDRON = prove
 (`!(f:real^3->real^3) s.
     pl_map_on (:real^3) f /\ pl_polyhedron s ==> pl_map_on s f`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC PL_MAP_ON_SUBSET THEN
  EXISTS_TAC `(:real^3)` THEN
  ASM_SIMP_TAC[SUBSET_UNIV; LOCALLY_POLYHEDRAL_PL_POLYHEDRON]);;

let MOI_SCD_PLH_RESTRICT = prove
 (`!(f:real^3->real^3) g s.
     pl_homeomorphism ((:real^3),(:real^3)) (f,g) /\ pl_polyhedron s
     ==> pl_homeomorphism (s,IMAGE f s) (f,g)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SCD_PL_HOMEO_UNIV) THEN
  REWRITE_TAC[pl_homeomorphism] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC HOMEOMORPHISM_OF_SUBSETS THEN
    MAP_EVERY EXISTS_TAC [`(:real^3)`; `(:real^3)`] THEN
    ASM_REWRITE_TAC[SUBSET_UNIV];
    ASM_MESON_TAC[MOI_SCD_PL_MAP_ON_POLYHEDRON];
    MATCH_MP_TAC MOI_SCD_PL_MAP_ON_POLYHEDRON THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC PL_POLYHEDRON_PL_IMAGE THEN
    ASM_MESON_TAC[MOI_SCD_PL_MAP_ON_POLYHEDRON]]);;

let MOI_SCD_SIMPLE_IMP_SPHERE = prove
 (`!s:real^3->bool. moi_sch3_simple s ==> pl_sphere 2 s`,
  GEN_TAC THEN REWRITE_TAC[moi_sch3_simple] THEN
  DISCH_THEN(MP_TAC o SPEC `(:real^3)`) THEN
  REWRITE_TAC[CONVEX_UNIV; OPEN_UNIV; SUBSET_UNIV; IN_UNIV] THEN
  REWRITE_TAC[pl_sphere; ARITH_RULE `2 + 1 = 3`] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^3->bool` (X_CHOOSE_THEN `f:real^3->real^3`
    (X_CHOOSE_THEN `g:real^3->real^3` STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC
   [`k:real^3->bool`; `g:real^3->real^3`; `f:real^3->real^3`] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SCD_PL_HOMEO_UNIV) THEN
  SUBGOAL_THEN `pl_polyhedron (relative_frontier k:real^3->bool)` ASSUME_TAC
  THENL [ASM_MESON_TAC[MOI_CMB_PL_POLYHEDRON_RELATIVE_FRONTIER;
                       SIMPLEX_IMP_POLYTOPE]; ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (g:real^3->real^3) (relative_frontier k) = s`
  ASSUME_TAC THENL
   [UNDISCH_TAC `IMAGE (f:real^3->real^3) s = relative_frontier k` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[GSYM IMAGE_o; o_DEF] THEN ASM_REWRITE_TAC[IMAGE_ID];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `f:real^3->real^3`;
                 `relative_frontier k:real^3->bool`] MOI_SCD_PLH_RESTRICT) THEN
  ANTS_TAC THENL
   [ONCE_REWRITE_TAC[PL_HOMEOMORPHISM_SYM] THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[]]);;

let MOI_SCD_PL_HOMEO_ID = prove
 (`pl_homeomorphism ((:real^3),(:real^3)) ((\x. x),(\x. x))`,
  REWRITE_TAC[pl_homeomorphism; HOMEOMORPHISM_ID;
              GSYM LOCALLY_POLYHEDRAL_EQ_PL_MAP_ON_ID] THEN
  SIMP_TAC[LOCALLY_POLYHEDRAL_OPEN; OPEN_UNIV]);;

let MOI_SCD_SIMPLE_SIMPLEX = prove
 (`!k:real^3->bool. &3 simplex k ==> moi_sch3_simple (relative_frontier k)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[moi_sch3_simple] THEN
  REPEAT STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC
   [`k:real^3->bool`; `\x:real^3. x`; `\x:real^3. x`] THEN
  ASM_REWRITE_TAC[MOI_SCD_PL_HOMEO_ID; IMAGE_ID]);;

let MOI_SCD_PL_SPHERE_NONEMPTY = prove
 (`!n s:real^N->bool. pl_sphere n s ==> ~(s = {})`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_sphere; pl_homeomorphism] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
    (X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC))) THEN
  FIRST_X_ASSUM(MP_TAC o CONJUNCT1 o CONJUNCT2 o
    REWRITE_RULE[homeomorphism]) THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[IMAGE_EQ_EMPTY; RELATIVE_FRONTIER_EQ_EMPTY] THEN DISCH_TAC THEN
  MP_TAC(ISPEC `k:real^N->bool` AFFINE_BOUNDED_EQ_TRIVIAL) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `bounded(k:real^N->bool)` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_MESON_TAC[SIMPLEX_IMP_COMPACT; COMPACT_IMP_BOUNDED]; ALL_TAC] THEN
  STRIP_TAC THENL
   [UNDISCH_TAC `&(n + 1) simplex (k:real^N->bool)` THEN
    ASM_REWRITE_TAC[SIMPLEX_EMPTY] THEN
    MP_TAC(SPEC `n + 1` INT_POS) THEN INT_ARITH_TAC;
    UNDISCH_TAC `&(n + 1) simplex (k:real^N->bool)` THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o MATCH_MP AFF_DIM_SIMPLEX) THEN
    REWRITE_TAC[AFF_DIM_SING; INT_OF_NUM_EQ] THEN ARITH_TAC]);;

let MOI_SCD_NOT_SIMPLE_EMPTY = prove
 (`~(moi_sch3_simple ({}:real^3->bool))`,
  MESON_TAC[MOI_SCD_SIMPLE_IMP_SPHERE; MOI_SCD_PL_SPHERE_NONEMPTY]);;

let MOI_SCD_BOUNDED_HOMEO = prove
 (`!(f:real^N->real^N) g c.
     homeomorphism ((:real^N),(:real^N)) (f,g) /\ bounded c
     ==> bounded (IMAGE f c)`,
  REWRITE_TAC[homeomorphism; IN_UNIV] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC BOUNDED_SUBSET THEN
  EXISTS_TAC `IMAGE (f:real^N->real^N) (closure c)` THEN
  SIMP_TAC[IMAGE_SUBSET; CLOSURE_SUBSET] THEN
  MATCH_MP_TAC COMPACT_IMP_BOUNDED THEN
  MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
  ASM_SIMP_TAC[COMPACT_CLOSURE] THEN
  ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_UNIV]);;

let MOI_SCD_INSIDE_HOMEOMORPHISM = prove
 (`!(f:real^N->real^N) g s.
     homeomorphism ((:real^N),(:real^N)) (f,g)
     ==> IMAGE f (inside s) = inside (IMAGE f s)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[homeomorphism; IN_UNIV]) THEN
  SUBGOAL_THEN `IMAGE (f:real^N->real^N) ((:real^N) DIFF s) =
                (:real^N) DIFF IMAGE f s` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `homeomorphism ((:real^N) DIFF s,(:real^N) DIFF IMAGE f s) (f,g)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HOMEOMORPHISM_OF_SUBSETS THEN
    MAP_EVERY EXISTS_TAC [`(:real^N)`; `(:real^N)`] THEN
    ASM_REWRITE_TAC[SUBSET_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN `homeomorphism ((:real^N),(:real^N)) (g,f)` ASSUME_TAC THENL
   [ASM_MESON_TAC[HOMEOMORPHISM_SYM]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. ~(x IN s)
        ==> connected_component ((:real^N) DIFF IMAGE f s) (f x) =
            IMAGE f (connected_component ((:real^N) DIFF s) x)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`f:real^N->real^N`; `g:real^N->real^N`;
                   `(:real^N) DIFF (s:real^N->bool)`;
                   `(:real^N) DIFF IMAGE (f:real^N->real^N) s`; `x:real^N`]
                  HOMEOMORPHISM_CONNECTED_COMPONENT) THEN
    ASM_REWRITE_TAC[IN_DIFF; IN_UNIV];
    ALL_TAC] THEN
  REWRITE_TAC[inside; EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN
  X_GEN_TAC `y:real^N` THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `x:real^N` STRIP_ASSUME_TAC) THEN
    ASM_SIMP_TAC[] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[]; ASM_MESON_TAC[MOI_SCD_BOUNDED_HOMEO]];
    STRIP_TAC THEN EXISTS_TAC `(g:real^N->real^N) y` THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~((g:real^N->real^N) y IN s)` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ASM_REWRITE_TAC[]] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `(g:real^N->real^N) y`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`g:real^N->real^N`; `f:real^N->real^N`;
       `connected_component ((:real^N) DIFF IMAGE (f:real^N->real^N) s) y`]
       MOI_SCD_BOUNDED_HOMEO) THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM IMAGE_o; o_DEF] THEN ASM_REWRITE_TAC[IMAGE_ID]]);;

(* 3b. Theorem 12 (p.122): the induction on the index, from Lemma 1         *)
(* (MOI_SCH3_REDUCE), the index-zero case and Theorem 11.                    *)

let MOI_SCD_PL_SPHERE_POLYHEDRON = prove
 (`!n s:real^N->bool. pl_sphere n s ==> pl_polyhedron s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_sphere; pl_homeomorphism] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
    (X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC))) THEN
  FIRST_X_ASSUM(MP_TAC o CONJUNCT1 o CONJUNCT2 o
    REWRITE_RULE[homeomorphism]) THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC PL_POLYHEDRON_PL_IMAGE THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[MOI_CMB_PL_POLYHEDRON_RELATIVE_FRONTIER; SIMPLEX_IMP_POLYTOPE]);;

let MOI_SCD_FIX_OFF = prove
 (`!(f:real^3->real^3) g w s.
     pl_homeomorphism ((:real^3),(:real^3)) (f,g) /\
     (!x. ~(x IN w) ==> f x = x)
     ==> (!x. ~(x IN w) ==> g x = x) /\
         (s SUBSET w ==> IMAGE f s SUBSET w)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP MOI_SCD_PL_HOMEO_UNIV) THEN
  CONJ_TAC THENL
   [X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(f:real^3->real^3) x = x` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ASM_MESON_TAC[]];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN REPEAT STRIP_TAC THEN
    ASM_MESON_TAC[]]);;

let MOI_SCD_INDEX0_TERM =
 `!c (a:real^3).
     moi_sch3_saddle_free c a /\ pl_sphere 2 (UNIONS c)
     ==> moi_sch3_simple (UNIONS c)`;;

let MOI_SCD_SIMPLE_ALL = prove
 (mk_imp(list_mk_conj [MOI_SCH3_REDUCE; MOI_SCH3_INDEX_ZERO; MOI_SCH3_THM11;
                       MOI_SCH3_GENERIC_NEAR; MOI_SCD_INDEX0_TERM],
         `!s:real^3->bool. pl_sphere 2 s ==> moi_sch3_simple s`),
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "reduce") (CONJUNCTS_THEN2
    (LABEL_TAC "zero") (CONJUNCTS_THEN2 (LABEL_TAC "thm11")
    (CONJUNCTS_THEN2 (LABEL_TAC "near") (LABEL_TAC "index0"))))) THEN
  SUBGOAL_THEN
   `!n c (a:real^3). moi_sch3_generic c a /\ pl_sphere 2 (UNIONS c) /\
                     moi_sch3_index c a = n
                     ==> moi_sch3_simple (UNIONS c)`
  (LABEL_TAC "ind") THENL
   [MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN
    DISCH_THEN(LABEL_TAC "ih") THEN
    MAP_EVERY X_GEN_TAC [`c:(real^3->bool)->bool`; `a:real^3`] THEN
    STRIP_TAC THEN ASM_CASES_TAC `n = 0` THENL
     [USE_THEN "index0" MATCH_MP_TAC THEN EXISTS_TAC `a:real^3` THEN
      ASM_REWRITE_TAC[] THEN USE_THEN "zero" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[moi_sch3_simple] THEN X_GEN_TAC `w:real^3->bool` THEN
    STRIP_TAC THEN
    USE_THEN "reduce" (MP_TAC o SPECL
      [`c:(real^3->bool)->bool`; `a:real^3`; `w:real^3->bool`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC
     [`f:real^3->real^3`; `g:real^3->real^3`; `c1:(real^3->bool)->bool`;
      `a1:real^3`; `c2:(real^3->bool)->bool`; `a2:real^3`;
      `d:real^3->bool`; `j:real^3->bool`] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `moi_sch3_simple (UNIONS c1:real^3->bool) /\
                  moi_sch3_simple (UNIONS c2:real^3->bool)`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [USE_THEN "ih" (MP_TAC o SPEC `moi_sch3_index c1 (a1:real^3)`) THEN
        ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
        DISCH_THEN(MP_TAC o SPECL [`c1:(real^3->bool)->bool`; `a1:real^3`]) THEN
        ASM_REWRITE_TAC[];
        USE_THEN "ih" (MP_TAC o SPEC `moi_sch3_index c2 (a2:real^3)`) THEN
        ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
        DISCH_THEN(MP_TAC o SPECL [`c2:(real^3->bool)->bool`; `a2:real^3`]) THEN
        ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `moi_sch3_simple (IMAGE (f:real^3->real^3) (UNIONS c))`
    MP_TAC THENL
     [ASM_REWRITE_TAC[] THEN USE_THEN "thm11" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[moi_sch3_simple] THEN
    DISCH_THEN(MP_TAC o SPEC `w:real^3->bool`) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[];
        MP_TAC(ISPECL [`f:real^3->real^3`; `g:real^3->real^3`; `w:real^3->bool`;
                       `UNIONS c:real^3->bool`] MOI_SCD_FIX_OFF) THEN
        ASM_SIMP_TAC[]];
      ALL_TAC] THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC
     [`k:real^3->bool`; `f':real^3->real^3`; `g':real^3->real^3`] THEN
    STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC
     [`k:real^3->bool`; `(f':real^3->real^3) o (f:real^3->real^3)`;
       `(g:real^3->real^3) o (g':real^3->real^3)`] THEN
    ASM_REWRITE_TAC[IMAGE_o; o_THM] THEN CONJ_TAC THENL
     [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
      EXISTS_TAC `(:real^3)` THEN ASM_REWRITE_TAC[];
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  X_GEN_TAC `s:real^3->bool` THEN DISCH_TAC THEN
  SUBGOAL_THEN `pl_polyhedron (s:real^3->bool)` MP_TAC THENL
   [ASM_MESON_TAC[MOI_SCD_PL_SPHERE_POLYHEDRON]; ALL_TAC] THEN
  REWRITE_TAC[PL_POLYHEDRON_EQ_SIMPLICIAL_COMPLEX] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:(real^3->bool)->bool` STRIP_ASSUME_TAC) THEN
  USE_THEN "near" (MP_TAC o SPECL
    [`c:(real^3->bool)->bool`; `vec 0:real^3`; `&1`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LT_01]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^3` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `UNIONS c = (s:real^3->bool)` THEN
  DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
  USE_THEN "ind" MATCH_MP_TAC THEN
  MAP_EVERY EXISTS_TAC [`moi_sch3_index c (a:real^3)`; `a:real^3`] THEN
  ASM_REWRITE_TAC[]);;

(* 3c. The index-zero case from Lemmas 2-3 (fibred) and Lemmas 4-6 (slabs). *)

let MOI_SCD_INDEX0 = prove
 (mk_imp(list_mk_conj [MOI_SCH3_FILLING_TRIANGULATION; MOI_SCH3_GENERIC_NEAR;
                       MOI_SCH3_CROSSINGS_STABLE; MOI_SCH3_SADDLE_FREE_FIBRED;
                       MOI_SCH3_FIBRED_SIMPLE],
         MOI_SCD_INDEX0_TERM),
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "fill") (CONJUNCTS_THEN2
    (LABEL_TAC "near") (CONJUNCTS_THEN2 (LABEL_TAC "stable")
    (CONJUNCTS_THEN2 (LABEL_TAC "fib") (LABEL_TAC "slab"))))) THEN
  MAP_EVERY X_GEN_TAC [`c:(real^3->bool)->bool`; `a:real^3`] THEN
  STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_sch3_saddle_free]) THEN
  USE_THEN "fill" (MP_TAC o SPEC `UNIONS c:real^3->bool`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:(real^3->bool)->bool` STRIP_ASSUME_TAC) THEN
  USE_THEN "stable" (MP_TAC o SPECL [`c:(real^3->bool)->bool`; `a:real^3`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (LABEL_TAC "st"))) THEN
  USE_THEN "near" (MP_TAC o SPECL [`k:(real^3->bool)->bool`; `a:real^3`; `e:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `b:real^3` STRIP_ASSUME_TAC) THEN
  USE_THEN "st" (MP_TAC o SPEC `b:real^3`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `moi_sch3_saddle_free c (b:real^3)` ASSUME_TAC THENL
   [REWRITE_TAC[moi_sch3_saddle_free] THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  USE_THEN "fib" (MP_TAC o SPECL [`c:(real^3->bool)->bool`; `b:real^3`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`lo:real`; `hi:real`] THEN DISCH_TAC THEN
  USE_THEN "slab" MATCH_MP_TAC THEN
  MAP_EVERY EXISTS_TAC
   [`b:real^3`; `lo:real`; `hi:real`; `k:(real^3->bool)->bool`] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `moi_sch3_generic k (b:real^3)` THEN
  REWRITE_TAC[moi_sch3_generic] THEN MESON_TAC[]);;

(* 3d. The PL Schoenflies statements of pc_moi_stmt.ml.                      *)

let MOI_SCD_AMBIENT_EQ = prove
 (`PL_SCHOENFLIES_3_AMBIENT_STATEMENT <=>
   !s:real^3->bool. pl_sphere 2 s ==> moi_sch3_simple s`,
  REWRITE_TAC[PL_SCHOENFLIES_3_AMBIENT_STATEMENT; moi_sch3_simple] THEN
  MESON_TAC[]);;

let MOI_SCD_SIMPLEX_FILL = prove
 (`!k:real^3->bool.
     &3 simplex k
     ==> relative_frontier k = frontier k /\
         inside (relative_frontier k) = interior k /\
         relative_frontier k UNION inside (relative_frontier k) = k`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(interior k:real^3->bool = {})` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FN1_SIMPLEX_3_INTERIOR; MEMBER_NOT_EMPTY]; ALL_TAC] THEN
  SUBGOAL_THEN `convex (k:real^3->bool) /\ compact k` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[SIMPLEX_IMP_CONVEX; SIMPLEX_IMP_COMPACT]; ALL_TAC] THEN
  ASM_SIMP_TAC[RELATIVE_FRONTIER_NONEMPTY_INTERIOR] THEN
  ASM_SIMP_TAC[INSIDE_FRONTIER_EQ_INTERIOR; COMPACT_IMP_BOUNDED] THEN
  REWRITE_TAC[FRONTIER_UNION_INTERIOR] THEN
  ASM_SIMP_TAC[CLOSURE_CLOSED; COMPACT_IMP_CLOSED]);;

let MOI_SCD_SCHOENFLIES = prove
 (`PL_SCHOENFLIES_3_AMBIENT_STATEMENT ==> PL_SCHOENFLIES_3_STATEMENT`,
  REWRITE_TAC[PL_SCHOENFLIES_3_AMBIENT_STATEMENT; PL_SCHOENFLIES_3_STATEMENT] THEN
  DISCH_TAC THEN X_GEN_TAC `s:real^3->bool` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`s:real^3->bool`; `(:real^3)`]) THEN
  ASM_REWRITE_TAC[CONVEX_UNIV; OPEN_UNIV; SUBSET_UNIV; IN_UNIV] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`k:real^3->bool`; `f:real^3->real^3`; `g:real^3->real^3`] THEN
  STRIP_TAC THEN REWRITE_TAC[pl_ball] THEN
  MAP_EVERY EXISTS_TAC [`k:real^3->bool`; `g:real^3->real^3`; `f:real^3->real^3`] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `pl_homeomorphism ((:real^3),(:real^3)) (g,f)` ASSUME_TAC THENL
   [ASM_MESON_TAC[PL_HOMEOMORPHISM_SYM]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SCD_PL_HOMEO_UNIV) THEN
  SUBGOAL_THEN `IMAGE (g:real^3->real^3) (relative_frontier k) = s` ASSUME_TAC
  THENL
   [UNDISCH_TAC `IMAGE (f:real^3->real^3) s = relative_frontier k` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[GSYM IMAGE_o; o_DEF] THEN ASM_REWRITE_TAC[IMAGE_ID];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (g:real^3->real^3) k = s UNION inside s` ASSUME_TAC THENL
   [MP_TAC(MATCH_MP MOI_SCD_SIMPLEX_FILL
      (ASSUME `&3 simplex (k:real^3->bool)`)) THEN
    DISCH_THEN(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV)
      [GSYM(CONJUNCT2(CONJUNCT2 th))]) THEN
    REWRITE_TAC[IMAGE_UNION] THEN
    MP_TAC(ISPECL [`g:real^3->real^3`; `f:real^3->real^3`;
                   `relative_frontier k:real^3->bool`]
                  MOI_SCD_INSIDE_HOMEOMORPHISM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
    concl th = `IMAGE (g:real^3->real^3) k = s UNION inside s`)) THEN
  MATCH_MP_TAC MOI_SCD_PLH_RESTRICT THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[POLYTOPE_IMP_PL_POLYHEDRON; SIMPLEX_IMP_POLYTOPE]);;

(* 3e. Closure: the eight statements of MOI_SCD_TOP_TARGETS give both PL    *)
(* Schoenflies statements.                                                  *)

let MOI_SCD_TOP_TARGETS =
  [MOI_SCH3_REDUCE; MOI_SCH3_INDEX_ZERO; MOI_SCH3_THM11;
   MOI_SCH3_GENERIC_NEAR; MOI_SCH3_FILLING_TRIANGULATION;
   MOI_SCH3_CROSSINGS_STABLE; MOI_SCH3_SADDLE_FREE_FIBRED;
   MOI_SCH3_FIBRED_SIMPLE];;

let MOI_SCD_CLOSURE = prove
 (mk_imp(list_mk_conj MOI_SCD_TOP_TARGETS,
         `PL_SCHOENFLIES_3_AMBIENT_STATEMENT /\ PL_SCHOENFLIES_3_STATEMENT`),
  STRIP_TAC THEN
  SUBGOAL_THEN MOI_SCD_INDEX0_TERM ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_SCD_INDEX0 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!s:real^3->bool. pl_sphere 2 s ==> moi_sch3_simple s`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_SCD_SIMPLE_ALL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `PL_SCHOENFLIES_3_AMBIENT_STATEMENT` ASSUME_TAC THENL
   [REWRITE_TAC[MOI_SCD_AMBIENT_EQ] THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[MOI_SCD_SCHOENFLIES]);;

(* 3f. Corollaries for the PL core: a PL 2-sphere in a convex set, or in    *)
(* the interior of a PL 3-ball, bounds a PL 3-ball inside it; the ambient   *)
(* form also carries the filled sphere onto the simplex; PLH extension from *)
(* the boundary over PL 3-balls (the step cited as 18.2 on p.238, which is  *)
(* coning only) and over filled PL 2-spheres (17.12 plus coning).            *)

let MOI_SCD_PL_BALL_FACTS = prove
 (`!n c:real^N->bool.
     pl_ball n c ==> ?k:real^N->bool. &n simplex k /\ c homeomorphic k /\ compact c`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_ball; pl_homeomorphism] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
    (X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC))) THEN
  EXISTS_TAC `k:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(c:real^N->bool) homeomorphic (k:real^N->bool)` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[HOMEOMORPHIC_SYM] THEN REWRITE_TAC[homeomorphic] THEN
    ASM_MESON_TAC[];
    ASM_REWRITE_TAC[]] THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP HOMEOMORPHIC_COMPACTNESS) THEN
  ASM_MESON_TAC[SIMPLEX_IMP_COMPACT]);;

let MOI_SCD_COR_CONVEX = prove
 (`PL_SCHOENFLIES_3_STATEMENT
   ==> !s w:real^3->bool.
         pl_sphere 2 s /\ convex w /\ s SUBSET w
         ==> pl_ball 3 (s UNION inside s) /\ s UNION inside s SUBSET w`,
  REWRITE_TAC[PL_SCHOENFLIES_3_STATEMENT] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[] THEN REWRITE_TAC[UNION_SUBSET] THEN
  ASM_MESON_TAC[INSIDE_SUBSET_CONVEX]);;

let MOI_SCD_COR_CELL = prove
 (`PL_SCHOENFLIES_3_STATEMENT
   ==> !s c:real^3->bool.
         pl_sphere 2 s /\ pl_ball 3 c /\ s SUBSET interior c
         ==> pl_ball 3 (s UNION inside s) /\
             s UNION inside s SUBSET interior c`,
  REWRITE_TAC[PL_SCHOENFLIES_3_STATEMENT] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[] THEN REWRITE_TAC[UNION_SUBSET] THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `k:real^3->bool` STRIP_ASSUME_TAC o
    MATCH_MP MOI_SCD_PL_BALL_FACTS) THEN
  SUBGOAL_THEN `connected ((:real^3) DIFF interior c)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM CLOSURE_COMPLEMENT] THEN MATCH_MP_TAC CONNECTED_CLOSURE THEN
    MP_TAC(ISPECL [`c:real^3->bool`; `k:real^3->bool`]
      CONNECTED_COMPLEMENT_HOMEOMORPHIC_CONVEX_COMPACT) THEN
    DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[DIMINDEX_3; ARITH] THEN
    ASM_MESON_TAC[SIMPLEX_IMP_CONVEX; SIMPLEX_IMP_COMPACT];
    ALL_TAC] THEN
  SUBGOAL_THEN `~bounded ((:real^3) DIFF interior c)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `bounded ((:real^3))` (fun th -> MESON_TAC[th; NOT_BOUNDED_UNIV]) THEN
    MATCH_MP_TAC BOUNDED_SUBSET THEN
    EXISTS_TAC `c UNION ((:real^3) DIFF interior c)` THEN
    ASM_SIMP_TAC[BOUNDED_UNION; COMPACT_IMP_BOUNDED] THEN
    MP_TAC(ISPEC `c:real^3->bool` INTERIOR_SUBSET) THEN SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `interior c DIFF (s:real^3->bool)` THEN
  REWRITE_TAC[SUBSET_DIFF] THEN MATCH_MP_TAC INSIDE_SUBSET THEN
  EXISTS_TAC `(:real^3) DIFF interior c` THEN ASM_REWRITE_TAC[] THEN
  ASM SET_TAC[]);;

let MOI_SCD_COR_AMBIENT_BALL = prove
 (`PL_SCHOENFLIES_3_AMBIENT_STATEMENT
   ==> !s w:real^3->bool.
         pl_sphere 2 s /\ convex w /\ open w /\ s SUBSET w
         ==> ?k f g. &3 simplex k /\
                     pl_homeomorphism ((:real^3),(:real^3)) (f,g) /\
                     (!x. ~(x IN w) ==> f x = x) /\
                     IMAGE f s = relative_frontier k /\
                     IMAGE f (s UNION inside s) = k /\ k SUBSET w`,
  REWRITE_TAC[PL_SCHOENFLIES_3_AMBIENT_STATEMENT] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`s:real^3->bool`; `w:real^3->bool`]) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`k:real^3->bool`; `f:real^3->real^3`; `g:real^3->real^3`] THEN
  STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`k:real^3->bool`; `f:real^3->real^3`; `g:real^3->real^3`] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `IMAGE (f:real^3->real^3) (s UNION inside s) = k` ASSUME_TAC THENL
   [REWRITE_TAC[IMAGE_UNION] THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SCD_PL_HOMEO_UNIV) THEN
    MP_TAC(ISPECL [`f:real^3->real^3`; `g:real^3->real^3`; `s:real^3->bool`]
      MOI_SCD_INSIDE_HOMEOMORPHISM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[MOI_SCD_SIMPLEX_FILL];
    ASM_REWRITE_TAC[]] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  MP_TAC(ISPECL [`f:real^3->real^3`; `g:real^3->real^3`; `w:real^3->bool`;
                 `s UNION inside s:real^3->bool`] MOI_SCD_FIX_OFF) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN
  REWRITE_TAC[UNION_SUBSET] THEN ASM_MESON_TAC[INSIDE_SUBSET_CONVEX]);;

let MOI_SCD_PLH_SUBSET = prove
 (`!(f:real^M->real^N) g s t s'.
     pl_homeomorphism (s,t) (f,g) /\ s' SUBSET s /\
     locally_polyhedral s' /\ locally_polyhedral (IMAGE f s')
     ==> pl_homeomorphism (s',IMAGE f s') (f,g)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_homeomorphism] THEN STRIP_TAC THEN
  SUBGOAL_THEN `IMAGE (f:real^M->real^N) s' SUBSET t` ASSUME_TAC THENL
   [UNDISCH_TAC `homeomorphism (s:real^M->bool,t:real^N->bool) (f,g)` THEN
    REWRITE_TAC[homeomorphism] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC HOMEOMORPHISM_OF_SUBSETS THEN
    MAP_EVERY EXISTS_TAC [`s:real^M->bool`; `t:real^N->bool`] THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC PL_MAP_ON_SUBSET THEN EXISTS_TAC `s:real^M->bool` THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC PL_MAP_ON_SUBSET THEN EXISTS_TAC `t:real^N->bool` THEN
    ASM_REWRITE_TAC[]]);;

let MOI_SCD_BALL_FRONTIER = prove
 (`!k c (p:real^3->real^3) q.
     &3 simplex k /\ pl_homeomorphism (k,c) (p,q)
     ==> IMAGE p (relative_frontier k) = frontier c`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_homeomorphism] THEN STRIP_TAC THEN
  MP_TAC(MATCH_MP MOI_SCD_SIMPLEX_FILL (ASSUME `&3 simplex (k:real^3->bool)`)) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(k:real^3->bool) homeomorphic (c:real^3->bool)` ASSUME_TAC THENL
   [REWRITE_TAC[homeomorphic] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `compact (k:real^3->bool) /\ compact (c:real^3->bool)`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[SIMPLEX_IMP_COMPACT; HOMEOMORPHIC_COMPACTNESS]; ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (p:real^3->real^3) (interior k) = interior c`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [ASM_MESON_TAC[MOI_FN1_HOMEOMORPHISM_INTERIOR];
      MP_TAC(ISPECL [`c:real^3->bool`; `k:real^3->bool`; `q:real^3->real^3`;
                     `p:real^3->real^3`] MOI_FN1_HOMEOMORPHISM_INTERIOR) THEN
      ANTS_TAC THENL [ASM_MESON_TAC[HOMEOMORPHISM_SYM]; ALL_TAC] THEN
      UNDISCH_TAC `homeomorphism (k:real^3->bool,c:real^3->bool) (p:real^3->real^3,q)` THEN
      REWRITE_TAC[homeomorphism] THEN
      MP_TAC(ISPEC `c:real^3->bool` INTERIOR_SUBSET) THEN SET_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[frontier] THEN ASM_SIMP_TAC[CLOSURE_CLOSED; COMPACT_IMP_CLOSED] THEN
  UNDISCH_TAC `homeomorphism (k:real^3->bool,c:real^3->bool) (p:real^3->real^3,q)` THEN
  REWRITE_TAC[homeomorphism] THEN
  MP_TAC(ISPEC `k:real^3->bool` INTERIOR_SUBSET) THEN
  UNDISCH_TAC `IMAGE (p:real^3->real^3) (interior k) = interior c` THEN
  SET_TAC[]);;

let MOI_SCD_BALL_BOUNDARY_PLH = prove
 (`!k c (p:real^3->real^3) q.
     &3 simplex k /\ pl_homeomorphism (k,c) (p,q)
     ==> pl_homeomorphism (relative_frontier k,frontier c) (p,q)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:real^3->bool`; `c:real^3->bool`; `p:real^3->real^3`;
                 `q:real^3->real^3`] MOI_SCD_BALL_FRONTIER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC MOI_SCD_PLH_SUBSET THEN
  MAP_EVERY EXISTS_TAC [`k:real^3->bool`; `c:real^3->bool`] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `pl_polyhedron (relative_frontier k:real^3->bool)` ASSUME_TAC
  THENL [ASM_MESON_TAC[MOI_CMB_PL_POLYHEDRON_RELATIVE_FRONTIER;
                       SIMPLEX_IMP_POLYTOPE]; ALL_TAC] THEN
  ASM_SIMP_TAC[LOCALLY_POLYHEDRAL_PL_POLYHEDRON] THEN
  SUBGOAL_THEN `relative_frontier k SUBSET (k:real^3->bool)` ASSUME_TAC THENL
   [MP_TAC(MATCH_MP MOI_SCD_SIMPLEX_FILL (ASSUME `&3 simplex (k:real^3->bool)`)) THEN
    SET_TAC[];
    ASM_REWRITE_TAC[]] THEN
  MATCH_MP_TAC LOCALLY_POLYHEDRAL_PL_POLYHEDRON THEN
  MATCH_MP_TAC PL_POLYHEDRON_PL_IMAGE THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC PL_MAP_ON_SUBSET THEN EXISTS_TAC `k:real^3->bool` THEN
  ASM_SIMP_TAC[LOCALLY_POLYHEDRAL_PL_POLYHEDRON] THEN
  ASM_MESON_TAC[pl_homeomorphism]);;

let MOI_SCD_COR_EXTEND_BALL = prove
 (`!c c' (h:real^3->real^3) h'.
     pl_ball 3 c /\ pl_ball 3 c' /\
     pl_homeomorphism (frontier c,frontier c') (h,h')
     ==> ?f g. pl_homeomorphism (c,c') (f,g) /\
               !x. x IN frontier c ==> f x = h x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_ball] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `k:real^3->bool` (X_CHOOSE_THEN `p:real^3->real^3`
     (X_CHOOSE_THEN `q:real^3->real^3` STRIP_ASSUME_TAC)))
   (CONJUNCTS_THEN2
   (X_CHOOSE_THEN `k':real^3->bool` (X_CHOOSE_THEN `p':real^3->real^3`
     (X_CHOOSE_THEN `q':real^3->real^3` STRIP_ASSUME_TAC)))
   ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`k:real^3->bool`; `c:real^3->bool`; `p:real^3->real^3`;
                 `q:real^3->real^3`] MOI_SCD_BALL_BOUNDARY_PLH) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`k':real^3->bool`; `c':real^3->bool`; `p':real^3->real^3`;
                 `q':real^3->real^3`] MOI_SCD_BALL_BOUNDARY_PLH) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `pl_homeomorphism (relative_frontier k,relative_frontier k')
      ((q':real^3->real^3) o ((h:real^3->real^3) o (p:real^3->real^3)),
       ((q:real^3->real^3) o (h':real^3->real^3)) o (p':real^3->real^3))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
    EXISTS_TAC `frontier c':real^3->bool` THEN CONJ_TAC THENL
     [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
      EXISTS_TAC `frontier c:real^3->bool` THEN ASM_REWRITE_TAC[];
      ONCE_REWRITE_TAC[PL_HOMEOMORPHISM_SYM] THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:real^3->bool`; `k':real^3->bool`; `3`;
     `(q':real^3->real^3) o ((h:real^3->real^3) o (p:real^3->real^3))`;
     `((q:real^3->real^3) o (h':real^3->real^3)) o (p':real^3->real^3)`]
     PL_HOMEOMORPHISM_CONE_EXTENSION) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `ff:real^3->real^3` (X_CHOOSE_THEN `gg:real^3->real^3`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC
   [`(p':real^3->real^3) o (ff:real^3->real^3) o (q:real^3->real^3)`;
    `((p:real^3->real^3) o (gg:real^3->real^3)) o (q':real^3->real^3)`] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
    EXISTS_TAC `k':real^3->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
    EXISTS_TAC `k:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[PL_HOMEOMORPHISM_SYM] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT1 o REWRITE_RULE[pl_homeomorphism; homeomorphism] o
    check (fun th -> concl th =
      `pl_homeomorphism (relative_frontier k,frontier c)
                        (p:real^3->real^3,q)`)) THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT1 o REWRITE_RULE[pl_homeomorphism; homeomorphism] o
    check (fun th -> concl th =
      `pl_homeomorphism (relative_frontier k',frontier c')
                        (p':real^3->real^3,q')`)) THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT1 o REWRITE_RULE[pl_homeomorphism; homeomorphism] o
    check (fun th -> concl th =
      `pl_homeomorphism (frontier c,frontier c') (h:real^3->real^3,h')`)) THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(q:real^3->real^3) x IN relative_frontier k /\
                (p:real^3->real^3) (q x) = x`
  STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(q:real^3->real^3) x` o
    check (fun th -> is_forall(concl th) &&
           can (find_term ((=) `ff:real^3->real^3`)) (concl th))) THEN
  ASM_REWRITE_TAC[o_THM] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `(h:real^3->real^3) x IN frontier c'` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  ASM SET_TAC[]);;

let MOI_SCD_PL_SPHERE_2_HOMEOMORPHIC = prove
 (`!s:real^3->bool. pl_sphere 2 s ==> s homeomorphic sphere(vec 0:real^3,&1)`,
  GEN_TAC THEN REWRITE_TAC[pl_sphere; ARITH_RULE `2 + 1 = 3`] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^3->bool` (X_CHOOSE_THEN `f:real^3->real^3`
    (X_CHOOSE_THEN `g:real^3->real^3` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `relative_frontier k:real^3->bool`;
                 `sphere(vec 0:real^3,&1)`] HOMEOMORPHIC_TRANS) THEN
  DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
   [ONCE_REWRITE_TAC[HOMEOMORPHIC_SYM] THEN REWRITE_TAC[homeomorphic] THEN
    ASM_MESON_TAC[pl_homeomorphism];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`vec 0:real^3`; `&1`] RELATIVE_FRONTIER_CBALL) THEN
  REWRITE_TAC[REAL_OF_NUM_EQ; ARITH] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC HOMEOMORPHIC_RELATIVE_FRONTIERS_CONVEX_BOUNDED_SETS THEN
  ASM_SIMP_TAC[CONVEX_CBALL; BOUNDED_CBALL; SIMPLEX_IMP_CONVEX;
               SIMPLEX_IMP_COMPACT; COMPACT_IMP_BOUNDED] THEN
  TRY(CONJ_TAC THENL [ASM_MESON_TAC[SIMPLEX_IMP_CONVEX]; ALL_TAC]) THEN
  TRY(CONJ_TAC THENL [ASM_MESON_TAC[SIMPLEX_IMP_COMPACT; COMPACT_IMP_BOUNDED];
                      ALL_TAC]) THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP AFF_DIM_SIMPLEX) THEN
  REWRITE_TAC[AFF_DIM_CBALL; REAL_LT_01; DIMINDEX_3]);;

let MOI_SCD_FILLED_FRONTIER = prove
 (`!s:real^3->bool.
     pl_sphere 2 s
     ==> frontier (s UNION inside s) = s /\
         interior (s UNION inside s) = inside s /\
         s UNION inside s = (:real^3) DIFF outside s`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPEC `s:real^3->bool` JORDAN_INSIDE_OUTSIDE_GEN) THEN
  ASM_SIMP_TAC[MOI_SCD_PL_SPHERE_2_HOMEOMORPHIC; DIMINDEX_3; ARITH] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `s UNION inside s = (:real^3) DIFF outside s` ASSUME_TAC THENL
   [MP_TAC(ISPEC `s:real^3->bool` OUTSIDE_NO_OVERLAP) THEN ASM SET_TAC[];
    ASM_REWRITE_TAC[FRONTIER_COMPLEMENT]] THEN
  REWRITE_TAC[INTERIOR_COMPLEMENT] THEN
  MP_TAC(ISPEC `outside s:real^3->bool` CLOSURE_UNION_FRONTIER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPEC `s:real^3->bool` OUTSIDE_NO_OVERLAP) THEN ASM SET_TAC[]);;

let MOI_SCD_COR_EXTEND = prove
 (`PL_SCHOENFLIES_3_STATEMENT
   ==> !s s' (h:real^3->real^3) h'.
         pl_sphere 2 s /\ pl_sphere 2 s' /\ pl_homeomorphism (s,s') (h,h')
         ==> ?f g. pl_homeomorphism (s UNION inside s,s' UNION inside s') (f,g) /\
                   !x. x IN s ==> f x = h x`,
  REWRITE_TAC[PL_SCHOENFLIES_3_STATEMENT] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s UNION inside s:real^3->bool`; `s' UNION inside s':real^3->bool`;
                 `h:real^3->real^3`; `h':real^3->real^3`]
                MOI_SCD_COR_EXTEND_BALL) THEN
  ASM_SIMP_TAC[MOI_SCD_FILLED_FRONTIER]);;

(* 3g. Book theorems that follow from the definitions: Thm 7 (pushes are    *)
(* transported by PLHs), Thm 8 (simply imbedded spheres have the push       *)
(* property, given the simplex statement MOI_SCH3_SIMPLEX_PUSH), the        *)
(* deletion tool used in Thms 9-11 and Lemma 6, and Thm 9 for convex cells  *)
(* from the cone statement MOI_SCH3_STAR_SIMPLE.                            *)

let MOI_SCD_FRONTIER_HOMEO = prove
 (`!(f:real^3->real^3) g c.
     homeomorphism ((:real^3),(:real^3)) (f,g)
     ==> IMAGE f (frontier c) = frontier (IMAGE f c)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^3->real^3`; `g:real^3->real^3`; `(:real^3)`;
                 `(:real^3)`; `c:real^3->bool`] HOMEOMORPHISM_FRONTIER_OF) THEN
  ASM_REWRITE_TAC[SUBTOPOLOGY_UNIV; EUCLIDEAN_FRONTIER_OF; SUBSET_UNIV]);;

let MOI_SCD_OPEN_HOMEO = prove
 (`!(f:real^3->real^3) g u.
     homeomorphism ((:real^3),(:real^3)) (f,g) /\ open u ==> open (IMAGE f u)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^3->real^3`; `g:real^3->real^3`; `(:real^3)`;
                 `(:real^3)`; `u:real^3->bool`] HOMEOMORPHISM_IMP_OPEN_MAP) THEN
  ASM_REWRITE_TAC[SUBTOPOLOGY_UNIV; GSYM OPEN_IN]);;

let MOI_SCD_PUSH_PLH = prove
 (`!c d j (f:real^3->real^3) g.
     moi_sch3_push c d j /\ pl_homeomorphism ((:real^3),(:real^3)) (f,g)
     ==> moi_sch3_push (IMAGE f c) (IMAGE f d) (IMAGE f j)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_sch3_push] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "push") ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SCD_PL_HOMEO_UNIV) THEN
  MAP_EVERY X_GEN_TAC [`u:real^3->bool`; `v:real^3->bool`] THEN STRIP_TAC THEN
  USE_THEN "push" (MP_TAC o SPECL
    [`IMAGE (g:real^3->real^3) u`; `IMAGE (g:real^3->real^3) v`]) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MOI_SCD_OPEN_HOMEO THEN EXISTS_TAC `f:real^3->real^3` THEN
      ASM_MESON_TAC[HOMEOMORPHISM_SYM];
      UNDISCH_TAC `IMAGE (f:real^3->real^3) c SUBSET u` THEN ASM SET_TAC[];
      MATCH_MP_TAC PL_POLYHEDRON_PL_IMAGE THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC MOI_SCD_PL_MAP_ON_POLYHEDRON THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `v INTER IMAGE (f:real^3->real^3) c SUBSET IMAGE f j` THEN
      ASM SET_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`h:real^3->real^3`; `h':real^3->real^3`] THEN
  STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC
   [`(f:real^3->real^3) o ((h:real^3->real^3) o (g:real^3->real^3))`;
    `((f:real^3->real^3) o (h':real^3->real^3)) o (g:real^3->real^3)`] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `(:real^3)` THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `(:real^3)` THEN
    ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[PL_HOMEOMORPHISM_SYM] THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN
    SUBGOAL_THEN `~((g:real^3->real^3) x IN IMAGE g u)` ASSUME_TAC THENL
     [ASM SET_TAC[]; ASM_SIMP_TAC[]];
    X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN
    SUBGOAL_THEN `(g:real^3->real^3) x IN IMAGE g v` ASSUME_TAC THENL
     [ASM SET_TAC[]; ASM_SIMP_TAC[]];
    REWRITE_TAC[IMAGE_o] THEN
    SUBGOAL_THEN `IMAGE (g:real^3->real^3) (IMAGE f d) = d` SUBST1_TAC THENL
     [REWRITE_TAC[GSYM IMAGE_o; o_DEF] THEN ASM_REWRITE_TAC[IMAGE_ID];
      ASM_REWRITE_TAC[]] THEN
    MP_TAC(ISPECL [`f:real^3->real^3`; `g:real^3->real^3`; `c:real^3->bool`]
      MOI_SCD_FRONTIER_HOMEO) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    ASM SET_TAC[]]);;

let MOI_SCD_CELL_IMAGE = prove
 (`!n d j (f:real^3->real^3) g.
     pl_cell_with_boundary n d j /\ pl_homeomorphism ((:real^3),(:real^3)) (f,g)
     ==> pl_cell_with_boundary n (IMAGE f d) (IMAGE f j)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_cell_with_boundary] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `t:real^3->bool`
    (X_CHOOSE_THEN `p:real^3->real^3` (X_CHOOSE_THEN `q:real^3->real^3`
      STRIP_ASSUME_TAC))) ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`t:real^3->bool`; `(f:real^3->real^3) o (p:real^3->real^3)`;
                        `(q:real^3->real^3) o (g:real^3->real^3)`] THEN
  ASM_REWRITE_TAC[IMAGE_o] THEN
  MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `d:real^3->bool` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_SCD_PLH_RESTRICT THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `d = IMAGE (p:real^3->real^3) t` SUBST1_TAC THENL
   [ASM_MESON_TAC[pl_homeomorphism; homeomorphism]; ALL_TAC] THEN
  MATCH_MP_TAC PL_POLYHEDRON_PL_IMAGE THEN
  CONJ_TAC THENL [ASM_MESON_TAC[POLYTOPE_IMP_PL_POLYHEDRON; SIMPLEX_IMP_POLYTOPE];
                  ASM_MESON_TAC[pl_homeomorphism]]);;

let MOI_SCD_SIMPLE_PUSH = prove
 (mk_imp(MOI_SCH3_SIMPLEX_PUSH,
   `!s d j:real^3->bool.
      moi_sch3_simple s /\ pl_cell_with_boundary 2 d j /\ d SUBSET s
      ==> moi_sch3_push (s UNION inside s) d j`),
  DISCH_THEN(LABEL_TAC "spush") THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(:real^3)` o REWRITE_RULE[moi_sch3_simple]) THEN
  REWRITE_TAC[CONVEX_UNIV; OPEN_UNIV; SUBSET_UNIV; IN_UNIV] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`k:real^3->bool`; `f:real^3->real^3`; `g:real^3->real^3`] THEN
  STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SCD_PL_HOMEO_UNIV) THEN
  SUBGOAL_THEN `pl_homeomorphism ((:real^3),(:real^3)) (g:real^3->real^3,f)`
  ASSUME_TAC THENL [ASM_MESON_TAC[PL_HOMEOMORPHISM_SYM]; ALL_TAC] THEN
  USE_THEN "spush" (MP_TAC o SPECL [`k:real^3->bool`;
    `IMAGE (f:real^3->real^3) d`; `IMAGE (f:real^3->real^3) j`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC MOI_SCD_CELL_IMAGE THEN EXISTS_TAC `g:real^3->real^3` THEN
      ASM_REWRITE_TAC[];
      UNDISCH_TAC `IMAGE (f:real^3->real^3) s = relative_frontier k` THEN
      UNDISCH_TAC `d SUBSET (s:real^3->bool)` THEN SET_TAC[]];
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `!t:real^3->bool. IMAGE (g:real^3->real^3) (IMAGE f t) = t`
  ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[GSYM IMAGE_o; o_DEF] THEN ASM_REWRITE_TAC[IMAGE_ID];
    ALL_TAC] THEN
  SUBGOAL_THEN `homeomorphism ((:real^3),(:real^3)) (g:real^3->real^3,f)`
  ASSUME_TAC THENL [ASM_MESON_TAC[HOMEOMORPHISM_SYM]; ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (g:real^3->real^3) k = s UNION inside s` ASSUME_TAC THENL
   [MP_TAC(MATCH_MP MOI_SCD_SIMPLEX_FILL
      (ASSUME `&3 simplex (k:real^3->bool)`)) THEN
    DISCH_THEN(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV)
      [GSYM(CONJUNCT2(CONJUNCT2 th))]) THEN
    REWRITE_TAC[IMAGE_UNION] THEN
    MP_TAC(ISPECL [`g:real^3->real^3`; `f:real^3->real^3`;
                   `relative_frontier k:real^3->bool`]
                  MOI_SCD_INSIDE_HOMEOMORPHISM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    UNDISCH_TAC `IMAGE (f:real^3->real^3) s = relative_frontier k` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:real^3->bool`; `IMAGE (f:real^3->real^3) d`;
                 `IMAGE (f:real^3->real^3) j`; `g:real^3->real^3`;
                 `f:real^3->real^3`] MOI_SCD_PUSH_PLH) THEN
  ASM_REWRITE_TAC[]);;

let MOI_SCD_PUSH_SIMPLE = prove
 (`!c d j s:real^3->bool.
     moi_sch3_push c d j /\ closed c /\ j SUBSET d /\ d SUBSET s /\
     c SUBSET convex hull s /\
     pl_polyhedron ((s DIFF d) UNION j) /\ ((s DIFF d) UNION j) INTER c SUBSET j /\
     moi_sch3_simple ((s DIFF d) UNION (frontier c DIFF d) UNION j)
     ==> moi_sch3_simple s`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "push") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "simp")))))))) THEN
  REWRITE_TAC[moi_sch3_simple] THEN X_GEN_TAC `w:real^3->bool` THEN STRIP_TAC THEN
  SUBGOAL_THEN `convex hull s SUBSET (w:real^3->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC HULL_MINIMAL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  USE_THEN "push" (MP_TAC o SPECL [`w:real^3->bool`;
    `(s DIFF d) UNION j:real^3->bool`] o REWRITE_RULE[moi_sch3_push]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`f:real^3->real^3`; `g:real^3->real^3`] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `IMAGE (f:real^3->real^3) s = (s DIFF d) UNION (frontier c DIFF d) UNION j`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  USE_THEN "simp" (MP_TAC o SPEC `w:real^3->bool` o
    REWRITE_RULE[moi_sch3_simple]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `c:real^3->bool` FRONTIER_SUBSET_CLOSED) THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`k:real^3->bool`; `f':real^3->real^3`; `g':real^3->real^3`] THEN
  STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC
   [`k:real^3->bool`; `(f':real^3->real^3) o (f:real^3->real^3)`;
    `(g:real^3->real^3) o (g':real^3->real^3)`] THEN
  ASM_REWRITE_TAC[IMAGE_o; o_THM] THEN CONJ_TAC THENL
   [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `(:real^3)` THEN
    ASM_REWRITE_TAC[];
    ASM_MESON_TAC[]]);;

let MOI_SCD_RAY_SEGMENT = prove
 (`!(v:real^3) u d r.
     ~(u = vec 0) /\ &0 < d /\ d < r
     ==> v + d % u IN segment(v,v + r % u)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[IN_SEGMENT] THEN CONJ_TAC THENL
   [REWRITE_TAC[VECTOR_ARITH `v:real^3 = v + r % u <=> r % u = vec 0`] THEN
    ASM_REWRITE_TAC[VECTOR_MUL_EQ_0] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `d / r` THEN
  SUBGOAL_THEN `&0 < r` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_LT_LDIV_EQ; REAL_MUL_LID] THEN
  REWRITE_TAC[VECTOR_ADD_LDISTRIB; VECTOR_MUL_ASSOC] THEN
  ASM_SIMP_TAC[REAL_DIV_RMUL; REAL_LT_IMP_NZ] THEN VECTOR_ARITH_TAC);;

let MOI_SCD_CONVEX_FRONTIER_FACTS = prove
 (`!c (v:real^3).
     polytope c /\ v IN interior c
     ==> pl_sphere 2 (frontier c) /\ v IN inside (frontier c) /\
         (!x y. x IN frontier c /\ y IN frontier c /\ y IN segment[v,x]
                ==> y = x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `convex (c:real^3->bool) /\ bounded c /\ closed c`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[POLYTOPE_IMP_CONVEX; POLYTOPE_IMP_BOUNDED; POLYTOPE_IMP_CLOSED];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN frontier c ==> segment(v,x) SUBSET interior (c:real^3->bool)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC IN_INTERIOR_CLOSURE_CONVEX_SEGMENT THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[frontier; IN_DIFF];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x. x IN frontier c ==> ~(x IN interior (c:real^3->bool))`
  ASSUME_TAC THENL [REWRITE_TAC[frontier; IN_DIFF] THEN MESON_TAC[]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC STAR_SHAPED_PL_SPHERE THEN EXISTS_TAC `v:real^3` THEN
    REPEAT CONJ_TAC THENL
     [SUBGOAL_THEN `frontier c = relative_frontier (c:real^3->bool)` SUBST1_TAC
      THENL
       [ASM_MESON_TAC[RELATIVE_FRONTIER_NONEMPTY_INTERIOR; MEMBER_NOT_EMPTY];
        ASM_SIMP_TAC[MOI_CMB_PL_POLYHEDRON_RELATIVE_FRONTIER]];
      ASM_MESON_TAC[];
      X_GEN_TAC `u:real^3` THEN DISCH_TAC THEN REWRITE_TAC[EXISTS_UNIQUE] THEN
      MP_TAC(ISPECL [`c:real^3->bool`; `v:real^3`; `u:real^3`] RAY_TO_FRONTIER) THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `r:real` THEN STRIP_TAC THEN
      REWRITE_TAC[GSYM REAL_LE_ANTISYM; GSYM REAL_NOT_LT] THEN
      CONJ_TAC THEN DISCH_TAC THENL
       [SUBGOAL_THEN `(v:real^3) + d % u IN interior c` MP_TAC THENL
         [SUBGOAL_THEN `(v:real^3) + d % u IN segment(v,v + r % u)` MP_TAC THENL
           [MATCH_MP_TAC MOI_SCD_RAY_SEGMENT THEN ASM_REWRITE_TAC[];
            ASM SET_TAC[]];
          ASM_MESON_TAC[]];
        ASM_MESON_TAC[REAL_LT_IMP_LE]]];
    ASM_SIMP_TAC[INSIDE_FRONTIER_EQ_INTERIOR];
    MAP_EVERY X_GEN_TAC [`x:real^3`; `y:real^3`] THEN STRIP_TAC THEN
    UNDISCH_TAC `(y:real^3) IN segment[v,x]` THEN
    REWRITE_TAC[SEGMENT_CLOSED_OPEN; IN_UNION; IN_INSERT; NOT_IN_EMPTY] THEN
    ASM SET_TAC[]]);;

let MOI_SCD_CONVEX_SIMPLE = prove
 (mk_imp(MOI_SCH3_STAR_SIMPLE,
   `!c:real^3->bool. polytope c /\ ~(interior c = {})
                     ==> moi_sch3_simple (frontier c)`),
  DISCH_THEN(LABEL_TAC "star") THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `v:real^3` o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  MP_TAC(ISPECL [`c:real^3->bool`; `v:real^3`] MOI_SCD_CONVEX_FRONTIER_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  USE_THEN "star" MATCH_MP_TAC THEN EXISTS_TAC `v:real^3` THEN
  ASM_REWRITE_TAC[]);;

(* 3h. Index facts: index zero from the polygon counts (so                   *)
(* MOI_SCH3_INDEX_ZERO follows from the other statements), the converse, the *)
(* abstract comparison used in Lemma 1 (DG                                   *)
(* heightIndex_lt_of_singular_comparison), the 2D ambient statement          *)
(* PL_SCHOENFLIES_2_AMBIENT_STATEMENT from its vertex form, and the closure  *)
(* MOI_SCD_CLOSURE_LEAVES over the nine statements of MOI_SCD_LEAF_TARGETS.  *)

let MOI_SCD_VERTICES_FINITE = prove
 (`!c:(real^3->bool)->bool. FINITE c ==> FINITE {v | {v} IN c}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\v:real^3. {v}`; `c:(real^3->bool)->bool`] FINITE_IMAGE_INJ) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN SET_TAC[]);;

let MOI_SCD_INDEX_ZERO = prove
 (mk_imp(list_mk_conj [MOI_SCH3_SINGULAR_POLYGONS; MOI_SCH3_LEVEL_POLYGONS_FINITE],
         MOI_SCH3_INDEX_ZERO),
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "sing") (LABEL_TAC "fin")) THEN
  MAP_EVERY X_GEN_TAC [`c:(real^3->bool)->bool`; `a:real^3`] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[moi_sch3_saddle_free] THEN
  X_GEN_TAC `v:real^3` THEN DISCH_TAC THEN
  USE_THEN "sing" (MP_TAC o SPECL
    [`c:(real^3->bool)->bool`; `a:real^3`; `v:real^3`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM NOT_LT] THEN DISCH_TAC THEN
  SUBGOAL_THEN `4 <= moi_sch3_crossings c a v` ASSUME_TAC THENL
   [UNDISCH_TAC `EVEN (moi_sch3_crossings c a v)` THEN
    UNDISCH_TAC `2 < moi_sch3_crossings c a v` THEN
    SPEC_TAC(`moi_sch3_crossings c a v`,`n:num`) THEN
    GEN_TAC THEN REWRITE_TAC[EVEN_EXISTS] THEN DISCH_TAC THEN
    DISCH_THEN(X_CHOOSE_THEN `m:num` SUBST_ALL_TAC) THEN
    UNDISCH_TAC `2 < 2 * m` THEN
    DISCH_THEN(MP_TAC o MATCH_MP (ARITH_RULE `2 < 2 * m ==> 1 < m`)) THEN
    ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE {v:real^3 | {v} IN c /\ 4 <= moi_sch3_crossings c a v}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{v:real^3 | {v} IN c}` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MOI_SCD_VERTICES_FINITE THEN
      ASM_MESON_TAC[moi_sch3_generic; simplicial_complex];
      SET_TAC[]];
    ALL_TAC] THEN
  UNDISCH_TAC `moi_sch3_index c (a:real^3) = 0` THEN
  ASM_SIMP_TAC[moi_sch3_index; NSUM_EQ_0_IFF] THEN
  DISCH_THEN(MP_TAC o SPEC `v:real^3`) THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
  USE_THEN "fin" (MP_TAC o SPECL
    [`c:(real^3->bool)->bool`; `a:real^3`; `(a:real^3) dot v`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN DISCH_TAC THEN
  MP_TAC(ISPECL
    [`{p | p IN moi_sch3_level_polygons (UNIONS c) a ((a:real^3) dot v) /\ v IN p}`;
     `moi_sch3_level_polygons (UNIONS c) a ((a:real^3) dot v)`] CARD_SUBSET) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN SET_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `4 <= moi_sch3_crossings c a v` THEN ARITH_TAC);;

let MOI_SCD_SADDLE_FREE_INDEX = prove
 (`!c (a:real^3). moi_sch3_saddle_free c a ==> moi_sch3_index c a = 0`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_sch3_saddle_free; moi_sch3_index] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `{v:real^3 | {v} IN c /\ 4 <= moi_sch3_crossings c a v} = {}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN
    X_GEN_TAC `v:real^3` THEN
    ASM_CASES_TAC `{v:real^3} IN c` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `v:real^3`) THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
    REWRITE_TAC[NSUM_CLAUSES]]);;

let MOI_SCD_AMB2 = prove
 (mk_imp(MOI_SCH3_AMB2_VERTEX, MOI_SCH3_AMB2),
  REWRITE_TAC[PL_SCHOENFLIES_2_AMBIENT_STATEMENT] THEN
  DISCH_THEN(LABEL_TAC "vertex") THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?p:real^2. p IN s` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_SCD_PL_SPHERE_NONEMPTY; MEMBER_NOT_EMPTY]; ALL_TAC] THEN
  USE_THEN "vertex" (MP_TAC o SPECL
    [`s:real^2->bool`; `w:real^2->bool`; `p:real^2`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MESON_TAC[]);;

let MOI_SCD_LEAF_TARGETS =
  [MOI_SCH3_REDUCE; MOI_SCH3_SINGULAR_POLYGONS; MOI_SCH3_LEVEL_POLYGONS_FINITE;
   MOI_SCH3_THM11; MOI_SCH3_GENERIC_NEAR; MOI_SCH3_FILLING_TRIANGULATION;
   MOI_SCH3_CROSSINGS_STABLE; MOI_SCH3_SADDLE_FREE_FIBRED;
   MOI_SCH3_FIBRED_SIMPLE];;

let MOI_SCD_CLOSURE_LEAVES = prove
 (mk_imp(list_mk_conj MOI_SCD_LEAF_TARGETS,
         `PL_SCHOENFLIES_3_AMBIENT_STATEMENT /\ PL_SCHOENFLIES_3_STATEMENT`),
  STRIP_TAC THEN MATCH_MP_TAC MOI_SCD_CLOSURE THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MOI_SCD_INDEX_ZERO THEN ASM_REWRITE_TAC[]);;

let MOI_SCD_NSUM_COMPARE = prove
 (`!s s' (f:A->num) f' p q.
     FINITE s /\ FINITE s' /\ p IN s /\ 1 <= f p /\
     (!u. u IN s' /\ ~(u = q) ==> u IN s /\ ~(u = p) /\ f' u <= f u) /\
     (q IN s' ==> f' q + 1 <= f p)
     ==> nsum s' f' < nsum s f`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:A->num`; `s:A->bool`; `p:A`] NSUM_DELETE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  SUBGOAL_THEN `nsum (s' DELETE (q:A)) f' <= nsum (s DELETE p) (f:A->num)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `nsum (s' DELETE (q:A)) (f:A->num)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC NSUM_LE THEN ASM_SIMP_TAC[FINITE_DELETE; IN_DELETE];
      MATCH_MP_TAC NSUM_SUBSET_SIMPLE THEN
      ASM_SIMP_TAC[FINITE_DELETE] THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  ASM_CASES_TAC `(q:A) IN s'` THENL
   [MP_TAC(ISPECL [`f':A->num`; `s':A->bool`; `q:A`] NSUM_DELETE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    SUBGOAL_THEN `s' DELETE (q:A) = s'` (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))
    THENL [ASM SET_TAC[]; ASM_ARITH_TAC]]);;

let MOI_SCD_INDEX_COMPARE = prove
 (`!c (a:real^3) c' (a':real^3) p q.
     FINITE c /\ FINITE c' /\
     {p} IN c /\ 4 <= moi_sch3_crossings c a p /\
     2 <= CARD (moi_sch3_level_polygons (UNIONS c) a (a dot p)) /\
     (!u. {u} IN c' /\ 4 <= moi_sch3_crossings c' a' u /\ ~(u = q)
          ==> {u} IN c /\ 4 <= moi_sch3_crossings c a u /\ ~(u = p) /\
              CARD (moi_sch3_level_polygons (UNIONS c') a' (a' dot u)) <=
              CARD (moi_sch3_level_polygons (UNIONS c) a (a dot u))) /\
     ({q} IN c' /\ 4 <= moi_sch3_crossings c' a' q
      ==> CARD (moi_sch3_level_polygons (UNIONS c') a' (a' dot q)) + 1 <=
          CARD (moi_sch3_level_polygons (UNIONS c) a (a dot p)))
     ==> moi_sch3_index c' a' < moi_sch3_index c a`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[moi_sch3_index] THEN
  MATCH_MP_TAC MOI_SCD_NSUM_COMPARE THEN
  MAP_EVERY EXISTS_TAC [`p:real^3`; `q:real^3`] THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{v:real^3 | {v} IN c}` THEN
    ASM_SIMP_TAC[MOI_SCD_VERTICES_FINITE] THEN SET_TAC[];
    MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{v:real^3 | {v} IN c'}` THEN
    ASM_SIMP_TAC[MOI_SCD_VERTICES_FINITE] THEN SET_TAC[];
    ASM_ARITH_TAC;
    X_GEN_TAC `u:real^3` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `u:real^3`) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(ARITH_RULE `x <= y ==> x - 1 <= y - 1`) THEN ASM_REWRITE_TAC[];
    STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]);;

let MOI_SCD_LEVEL_POLYGONS_MONO = prove
 (`!s s' (a:real^3) t.
     s' INTER {x | a dot x = t} SUBSET s
     ==> moi_sch3_level_polygons s' a t SUBSET moi_sch3_level_polygons s a t`,
  REWRITE_TAC[moi_sch3_level_polygons] THEN SET_TAC[]);;

let MOI_SCD_FAR_LEVELS = prove
 (mk_imp(list_mk_conj [MOI_SCH3_LEVEL_STABLE; MOI_SCH3_LEVEL_POLYGONS_FINITE;
                       MOI_SCH3_CROSSINGS_STABLE],
  `!c (a:real^3) h del r.
     moi_sch3_generic c a /\ pl_sphere 2 (UNIONS c) /\ &0 < del /\ &0 < r /\
     UNIONS c SUBSET cball(vec 0,r)
     ==> ?e. &0 < e /\
             !a' s' q. norm(a' - a) < e /\ {q} IN c /\ del <= abs(a dot q - h) /\
                       s' SUBSET cball(vec 0,r) /\
                       s' INTER {x | del / &2 <= abs(a dot x - h)} SUBSET UNIONS c
                       ==> CARD (moi_sch3_level_polygons s' a' (a' dot q)) <=
                           CARD (moi_sch3_level_polygons (UNIONS c) a (a dot q))`),
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "stable") (CONJUNCTS_THEN2
    (LABEL_TAC "fin") (LABEL_TAC "cross"))) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  USE_THEN "stable" (MP_TAC o SPECL [`c:(real^3->bool)->bool`; `a:real^3`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "e1"))) THEN
  USE_THEN "cross" (MP_TAC o SPECL [`c:(real^3->bool)->bool`; `a:real^3`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "e2"))) THEN
  EXISTS_TAC `min e1 (min e2 (del / (&4 * r)))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[REAL_LT_MIN] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`b:real^3`; `s':real^3->bool`; `q:real^3`] THEN
  REWRITE_TAC[REAL_LT_MIN] THEN STRIP_TAC THEN
  USE_THEN "e2" (MP_TAC o SPEC `b:real^3`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  USE_THEN "e1" (MP_TAC o SPECL [`b:real^3`; `q:real^3`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
  MATCH_MP_TAC CARD_SUBSET THEN CONJ_TAC THENL
   [ALL_TAC;
    USE_THEN "fin" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]] THEN
  MATCH_MP_TAC MOI_SCD_LEVEL_POLYGONS_MONO THEN
  REWRITE_TAC[SUBSET; IN_INTER; IN_ELIM_THM] THEN
  X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
    can (find_term ((=) `del / &2`)) (concl th))) THEN
  ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN
  SUBGOAL_THEN `(q:real^3) IN UNIONS c` ASSUME_TAC THENL
   [REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `{q:real^3}` THEN
    ASM_REWRITE_TAC[IN_SING];
    ALL_TAC] THEN
  SUBGOAL_THEN `norm(x:real^3) <= r /\ norm(q:real^3) <= r` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM IN_CBALL_0] THEN ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `abs((a:real^3) dot x - a dot q) <= del / &2` MP_TAC THENL
   [SUBGOAL_THEN `(a:real^3) dot x - a dot q = (a - b) dot (x - q)` SUBST1_TAC THENL
     [UNDISCH_TAC `(b:real^3) dot x = b dot q` THEN
      REWRITE_TAC[DOT_LSUB; DOT_RSUB] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `norm(a - b:real^3) * norm(x - q:real^3)` THEN
    REWRITE_TAC[NORM_CAUCHY_SCHWARZ_ABS] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `del / (&4 * r) * (&2 * r)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[NORM_POS_LE] THEN CONJ_TAC THENL
       [ONCE_REWRITE_TAC[NORM_SUB] THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
        UNDISCH_TAC `norm(x:real^3) <= r` THEN UNDISCH_TAC `norm(q:real^3) <= r` THEN
        NORM_ARITH_TAC];
      SUBGOAL_THEN `del / (&4 * r) * (&2 * r) = del / &2` SUBST1_TAC THENL
       [UNDISCH_TAC `&0 < r` THEN CONV_TAC REAL_FIELD; REAL_ARITH_TAC]];
    UNDISCH_TAC `del <= abs((a:real^3) dot q - h)` THEN REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* 4. Sanity: the push definition has teeth, the tetrahedron case of both   *)
(* PL Schoenflies statements holds outright, empty and finite sets are not  *)
(* PL 2-spheres (so the PL Schoenflies statements are vacuous there).       *)
(* ------------------------------------------------------------------------- *)

let MOI_SCD_PL_POLYHEDRON_EMPTY = prove
 (`pl_polyhedron ({}:real^3->bool)`,
  REWRITE_TAC[pl_polyhedron] THEN EXISTS_TAC `{}:(real^3->bool)->bool` THEN
  REWRITE_TAC[FINITE_EMPTY; NOT_IN_EMPTY; UNIONS_0]);;

let MOI_SCD_PUSH_TEETH = prove
 (`!k:real^3->bool. &3 simplex k ==> ~(moi_sch3_push k (relative_frontier k) {})`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[moi_sch3_push] THEN
  DISCH_THEN(MP_TAC o SPECL [`(:real^3)`; `{}:real^3->bool`]) THEN
  REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV; MOI_SCD_PL_POLYHEDRON_EMPTY;
              INTER_EMPTY; EMPTY_SUBSET; NOT_IN_EMPTY; IN_UNIV; UNION_EMPTY] THEN
  MP_TAC(MATCH_MP MOI_SCD_SIMPLEX_FILL (ASSUME `&3 simplex (k:real^3->bool)`)) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM(CONJUNCT1 th)]) THEN
  REWRITE_TAC[DIFF_EQ_EMPTY; IMAGE_EQ_EMPTY] THEN
  MP_TAC(ISPECL [`2`; `k:real^3->bool`] PL_SPHERE_RELATIVE_FRONTIER_SIMPLEX) THEN
  ASM_REWRITE_TAC[ARITH_RULE `2 + 1 = 3`] THEN
  MESON_TAC[MOI_SCD_PL_SPHERE_NONEMPTY]);;

let MOI_SCD_TETRA_CASE = prove
 (`!k:real^3->bool.
     &3 simplex k
     ==> pl_sphere 2 (relative_frontier k) /\
         pl_ball 3 (relative_frontier k UNION inside (relative_frontier k)) /\
         moi_sch3_simple (relative_frontier k)`,
  REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC PL_SPHERE_RELATIVE_FRONTIER_SIMPLEX THEN
    ASM_REWRITE_TAC[ARITH_RULE `2 + 1 = 3`];
    ASM_SIMP_TAC[MOI_SCD_SIMPLEX_FILL] THEN MATCH_MP_TAC PL_BALL_SIMPLEX THEN
    ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[MOI_SCD_SIMPLE_SIMPLEX]]);;

let MOI_SCD_NOT_PL_SPHERE_FINITE = prove
 (`!s:real^3->bool. FINITE s ==> ~(pl_sphere 2 s)`,
  GEN_TAC THEN DISCH_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP MOI_SCD_PL_SPHERE_2_HOMEOMORPHIC) THEN
  DISCH_THEN(MP_TAC o MATCH_MP HOMEOMORPHIC_FINITENESS) THEN
  ASM_REWRITE_TAC[FINITE_SPHERE; DIMINDEX_3; ARITH] THEN REAL_ARITH_TAC);;

(* Summary: hypothesis count and conclusion of every glue and sanity theorem. *)

let MOI_SCD_THEOREMS =
  [MOI_SCD_SIMPLE_IMP_SPHERE; MOI_SCD_SIMPLE_SIMPLEX; MOI_SCD_NOT_SIMPLE_EMPTY;
   MOI_SCD_INSIDE_HOMEOMORPHISM; MOI_SCD_SIMPLE_ALL; MOI_SCD_INDEX0;
   MOI_SCD_AMBIENT_EQ; MOI_SCD_SCHOENFLIES; MOI_SCD_CLOSURE;
   MOI_SCD_COR_CONVEX; MOI_SCD_COR_CELL; MOI_SCD_COR_AMBIENT_BALL;
   MOI_SCD_COR_EXTEND_BALL; MOI_SCD_FILLED_FRONTIER; MOI_SCD_COR_EXTEND;
   MOI_SCD_PUSH_PLH; MOI_SCD_SIMPLE_PUSH; MOI_SCD_PUSH_SIMPLE;
   MOI_SCD_CONVEX_SIMPLE; MOI_SCD_INDEX_ZERO; MOI_SCD_SADDLE_FREE_INDEX;
   MOI_SCD_AMB2; MOI_SCD_CLOSURE_LEAVES; MOI_SCD_INDEX_COMPARE;
   MOI_SCD_FAR_LEVELS;
   MOI_SCD_PUSH_TEETH; MOI_SCD_TETRA_CASE; MOI_SCD_NOT_PL_SPHERE_FINITE];;

map (fun th -> length (hyp th)) MOI_SCD_THEOREMS;;
length (axioms());;

