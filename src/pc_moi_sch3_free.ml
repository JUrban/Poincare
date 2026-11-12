(* ========================================================================= *)
(* pc_moi_sch3_free: free cells of polygonal cell decompositions of a PL     *)
(* 2-cell in the plane, Moise GTM 47, Sec 17 Thms 2-3 (p.118) and Sec 3 Thm  *)
(* 3.3 (p.27).  The main theorem FREE_CELL proves the statement              *)
(* MOI_SCH3_FREE_CELL of pc_moi_sch3_stmt.ml.                                *)
(* Route (as in the book and DG FreeDiskCell.lean): induction on the number *)
(* of cells; a cell c outside g0 meeting the boundary j in two or more      *)
(* points but not in an arc has a crosscut arc of the disk in its frontier; *)
(* the theta-curve split gives two smaller disks U (containing c) and V,    *)
(* and the pieces U and c UNION V both contain c; a free cell other than c  *)
(* of the piece away from g0 is free in the whole decomposition.            *)
(* ========================================================================= *)

needs "src/pc_moi_sch3_stmt.ml";;
needs "src/pc_moi_pl2.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* 1. Convex polygons (2-dimensional polytopes) in real^2.                   *)
(* ------------------------------------------------------------------------- *)

let MOI_SFR_POLYGON_FACTS = prove
 (`!c:real^2->bool.
     polytope c /\ aff_dim c = &2
     ==> compact c /\ convex c /\ closed c /\ bounded c /\
         ~(interior c = {}) /\
         relative_frontier c = frontier c /\
         relative_interior c = interior c /\
         closure(interior c) = c /\
         inside(frontier c) = interior c /\
         frontier c SUBSET c /\ interior c SUBSET c /\
         frontier c UNION interior c = c /\
         frontier c INTER interior c = {}`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `compact (c:real^2->bool) /\ convex c` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[POLYTOPE_IMP_COMPACT; POLYTOPE_IMP_CONVEX]; ALL_TAC] THEN
  SUBGOAL_THEN `closed (c:real^2->bool) /\ bounded c` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[COMPACT_IMP_CLOSED; COMPACT_IMP_BOUNDED]; ALL_TAC] THEN
  SUBGOAL_THEN `~(interior (c:real^2->bool) = {})` ASSUME_TAC THENL
   [ASM_SIMP_TAC[GSYM AFF_DIM_NONEMPTY_INTERIOR_EQ; DIMINDEX_2]; ALL_TAC] THEN
  ASM_SIMP_TAC[RELATIVE_FRONTIER_NONEMPTY_INTERIOR;
               RELATIVE_INTERIOR_NONEMPTY_INTERIOR;
               CONVEX_CLOSURE_INTERIOR; CLOSURE_CLOSED;
               INSIDE_FRONTIER_EQ_INTERIOR; INTERIOR_SUBSET;
               FRONTIER_SUBSET_CLOSED] THEN
  REWRITE_TAC[frontier] THEN ASM_SIMP_TAC[CLOSURE_CLOSED] THEN
  MP_TAC(ISPEC `c:real^2->bool` INTERIOR_SUBSET) THEN SET_TAC[]);;

(* The cell decompositions of the main theorem: finitely many convex        *)
(* polygons meeting pairwise in common faces.                               *)

let moi_sfr_cplx = new_definition
 `moi_sfr_cplx (g:(real^2->bool)->bool) <=>
    FINITE g /\
    (!c. c IN g ==> polytope c /\ aff_dim c = &2) /\
    (!c c'. c IN g /\ c' IN g
            ==> (c INTER c') face_of c /\ (c INTER c') face_of c')`;;

let MOI_SFR_CPLX_SUBSET = prove
 (`!g h:(real^2->bool)->bool. moi_sfr_cplx g /\ h SUBSET g ==> moi_sfr_cplx h`,
  REWRITE_TAC[moi_sfr_cplx] THEN REPEAT STRIP_TAC THENL
   [ASM_MESON_TAC[FINITE_SUBSET];
    ASM_MESON_TAC[SUBSET];
    ASM_MESON_TAC[SUBSET];
    ASM_MESON_TAC[SUBSET];
    ASM_MESON_TAC[SUBSET]]);;

let MOI_SFR_CPLX_CELL = prove
 (`!g c:real^2->bool.
     moi_sfr_cplx g /\ c IN g ==> polytope c /\ aff_dim c = &2`,
  REWRITE_TAC[moi_sfr_cplx] THEN MESON_TAC[]);;

let MOI_SFR_CPLX_INTER = prove
 (`!g c c':real^2->bool.
     moi_sfr_cplx g /\ c IN g /\ c' IN g /\ ~(c = c')
     ==> c INTER c' SUBSET frontier c /\ interior c INTER c' = {} /\
         ~(c SUBSET c')`,
  REWRITE_TAC[moi_sfr_cplx] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `polytope (c:real^2->bool) /\ aff_dim c = &2 /\
                polytope (c':real^2->bool) /\ aff_dim c' = &2`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~((c:real^2->bool) SUBSET c')` ASSUME_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `(c:real^2->bool) face_of c'` ASSUME_TAC THENL
     [SUBGOAL_THEN `(c:real^2->bool) INTER c' = c` (fun th -> ASM_MESON_TAC[th]) THEN
      ASM SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `aff_dim (c:real^2->bool) < aff_dim (c':real^2->bool)` MP_TAC THENL
     [MATCH_MP_TAC FACE_OF_AFF_DIM_LT THEN ASM_SIMP_TAC[POLYTOPE_IMP_CONVEX];
      ASM_REWRITE_TAC[INT_LT_REFL]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(c:real^2->bool) INTER c' SUBSET frontier c` ASSUME_TAC THENL
   [SUBGOAL_THEN `frontier c = relative_frontier (c:real^2->bool)` SUBST1_TAC THENL
     [ASM_MESON_TAC[MOI_SFR_POLYGON_FACTS]; ALL_TAC] THEN
    MATCH_MP_TAC FACE_OF_SUBSET_RELATIVE_FRONTIER THEN
    CONJ_TAC THENL [ASM_MESON_TAC[]; ASM SET_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `c:real^2->bool` MOI_SFR_POLYGON_FACTS) THEN
  ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

(* A real^N copy of MOI_SCD_RAY_SEGMENT (pc_moi_sch3_stmt.ml, real^3).      *)

let MOI_SFR_RAY_SEGMENT = prove
 (`!(v:real^N) u d r.
     ~(u = vec 0) /\ &0 < d /\ d < r
     ==> v + d % u IN segment(v,v + r % u)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[IN_SEGMENT] THEN CONJ_TAC THENL
   [REWRITE_TAC[VECTOR_ARITH `v:real^N = v + r % u <=> r % u = vec 0`] THEN
    ASM_REWRITE_TAC[VECTOR_MUL_EQ_0] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `d / r` THEN
  SUBGOAL_THEN `&0 < r` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_LT_LDIV_EQ; REAL_MUL_LID] THEN
  REWRITE_TAC[VECTOR_ADD_LDISTRIB; VECTOR_MUL_ASSOC] THEN
  ASM_SIMP_TAC[REAL_DIV_RMUL; REAL_LT_IMP_NZ] THEN VECTOR_ARITH_TAC);;

(* The frontier of a convex polygon is a PL 1-sphere (the real^2 analogue  *)
(* of MOI_SCD_CONVEX_FRONTIER_FACTS, from MOI_CMB_STAR_SHAPED_PL_SPHERE_0).  *)

let MOI_SFR_POLYGON_SPHERE = prove
 (`!c:real^2->bool. polytope c /\ aff_dim c = &2 ==> pl_sphere 1 (frontier c)`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SFR_POLYGON_FACTS) THEN
  FIRST_ASSUM(X_CHOOSE_TAC `v:real^2` o
    GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  SUBGOAL_THEN
   `!x. x IN frontier c ==> segment(v,x) SUBSET interior (c:real^2->bool)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC IN_INTERIOR_CLOSURE_CONVEX_SEGMENT THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[frontier; IN_DIFF];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x. x IN frontier c ==> ~(x IN interior (c:real^2->bool))`
  ASSUME_TAC THENL [REWRITE_TAC[frontier; IN_DIFF] THEN MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!y:real^2. y IN IMAGE (\x. --v + x) (frontier c) <=> v + y IN frontier c`
  ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[IN_IMAGE] THEN EQ_TAC THENL
     [STRIP_TAC THEN ASM_REWRITE_TAC[VECTOR_ARITH `v + --v + x:real^N = x`];
      DISCH_TAC THEN EXISTS_TAC `v + y:real^2` THEN ASM_REWRITE_TAC[] THEN
      VECTOR_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_polyhedron (frontier c:real^2->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_CMB_PL_POLYHEDRON_RELATIVE_FRONTIER]; ALL_TAC] THEN
  MP_TAC(ISPEC `IMAGE (\x:real^2. --v + x) (frontier c)`
    MOI_CMB_STAR_SHAPED_PL_SPHERE_0) THEN
  ASM_REWRITE_TAC[VECTOR_ADD_RID; DIMINDEX_2] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_SIMP_TAC[PL_POLYHEDRON_TRANSLATION];
      ASM_MESON_TAC[];
      X_GEN_TAC `u:real^2` THEN DISCH_TAC THEN REWRITE_TAC[EXISTS_UNIQUE] THEN
      MP_TAC(ISPECL [`c:real^2->bool`; `v:real^2`; `u:real^2`]
        RAY_TO_FRONTIER) THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
      X_GEN_TAC `d:real` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `r:real` THEN STRIP_TAC THEN
      REWRITE_TAC[GSYM REAL_LE_ANTISYM; GSYM REAL_NOT_LT] THEN
      CONJ_TAC THEN DISCH_TAC THENL
       [SUBGOAL_THEN `(v:real^2) + d % u IN interior c` MP_TAC THENL
         [SUBGOAL_THEN `(v:real^2) + d % u IN segment(v,v + r % u)` MP_TAC
          THENL
           [MATCH_MP_TAC MOI_SFR_RAY_SEGMENT THEN ASM_REWRITE_TAC[];
            ASM SET_TAC[]];
          ASM_MESON_TAC[]];
        ASM_MESON_TAC[REAL_LT_IMP_LE]]];
    DISCH_TAC THEN MATCH_MP_TAC PL_SPHERE_PL_HOMEOMORPHIC THEN
    MAP_EVERY EXISTS_TAC [`IMAGE (\x:real^2. --v + x) (frontier c)`;
                          `\x:real^2. v + x`; `\x:real^2. --v + x`] THEN
    ASM_SIMP_TAC[MOI_CMB_TRANSLATION_PL_HOMEOMORPHISM]]);;

(* PL 2-balls in the plane are PL 2-cells with boundary their frontier.     *)

let MOI_SFR_PL_BALL_CELL = prove
 (`!d:real^2->bool. pl_ball 2 d ==> pl_cell_with_boundary 2 d (frontier d)`,
  GEN_TAC THEN REWRITE_TAC[pl_ball; pl_cell_with_boundary] THEN
  REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[MOI_PL2_FRONTIER_PL_BALL_2]);;

let MOI_SFR_CELL_BALL = prove
 (`!d j:real^2->bool.
     pl_cell_with_boundary 2 d j ==> pl_ball 2 d /\ j = frontier d`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_cell_with_boundary; pl_ball] THEN
  STRIP_TAC THEN CONJ_TAC THENL
   [ASM_MESON_TAC[]; ASM_MESON_TAC[MOI_PL2_FRONTIER_PL_BALL_2]]);;

let MOI_SFR_POLYGON_CELL = prove
 (`!c:real^2->bool.
     polytope c /\ aff_dim c = &2
     ==> pl_cell_with_boundary 2 c (frontier c) /\ pl_ball 2 c /\
         pl_sphere 1 (frontier c)`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SFR_POLYGON_FACTS) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MOI_SFR_POLYGON_SPHERE) THEN
  SUBGOAL_THEN `pl_ball 2 (c:real^2->bool)` ASSUME_TAC THENL
   [MP_TAC PL_SCHOENFLIES_2 THEN REWRITE_TAC[PL_SCHOENFLIES_2_STATEMENT] THEN
    DISCH_THEN(MP_TAC o SPEC `frontier c:real^2->bool`) THEN ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[MOI_SFR_PL_BALL_CELL]]);;

(* ------------------------------------------------------------------------- *)
(* 2. PL arcs and PL circles in the plane; Jordan regions; the structure of *)
(* a PL 2-cell in real^2 (its boundary is a PL simple closed curve j and    *)
(* the cell is j UNION inside j).                                           *)
(* ------------------------------------------------------------------------- *)

let MOI_SFR_ARC_PL_BALL = prove
 (`!h:real^1->real^N.
     arc h /\ pl_map_on (interval[vec 0,vec 1]) h ==> pl_ball 1 (path_image h)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `h:real^1->real^N` MOI_PL2_ARC_PL_HOMEOMORPHISM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `h':real^N->real^1`) THEN
  SUBGOAL_THEN `~(vec 0:real^N = basis 1)` ASSUME_TAC THENL
   [GEN_REWRITE_TAC RAND_CONV [EQ_SYM_EQ] THEN
    SIMP_TAC[BASIS_NONZERO; DIMINDEX_GE_1; LE_REFL];
    ALL_TAC] THEN
  MP_TAC(ISPEC `linepath(vec 0:real^N,basis 1)` MOI_PL2_ARC_PL_HOMEOMORPHISM) THEN
  ASM_SIMP_TAC[ARC_LINEPATH_EQ; MOI_PL2_PL_LINEPATH;
               MOI_PL2_LOCALLY_POLYHEDRAL_INTERVAL; PATH_IMAGE_LINEPATH] THEN
  DISCH_THEN(X_CHOOSE_TAC `l:real^N->real^1`) THEN
  REWRITE_TAC[pl_ball] THEN
  MAP_EVERY EXISTS_TAC [`segment[vec 0:real^N,basis 1]`;
                        `(h:real^1->real^N) o (l:real^N->real^1)`;
                        `linepath(vec 0:real^N,basis 1) o (h':real^N->real^1)`] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[MOI_PL2_SIMPLEX_1] THEN ASM_MESON_TAC[];
    MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
    EXISTS_TAC `interval[vec 0:real^1,vec 1]` THEN
    ONCE_REWRITE_TAC[PL_HOMEOMORPHISM_SYM] THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[PL_HOMEOMORPHISM_SYM] THEN ASM_REWRITE_TAC[]]);;

let MOI_SFR_ARCS_LOOP = prove
 (`!h1 h2:real^1->real^N.
     arc h1 /\ pl_map_on (interval[vec 0,vec 1]) h1 /\
     arc h2 /\ pl_map_on (interval[vec 0,vec 1]) h2 /\
     pathstart h2 = pathstart h1 /\ pathfinish h2 = pathfinish h1 /\
     path_image h1 INTER path_image h2 = {pathstart h1,pathfinish h1}
     ==> simple_path(h1 ++ reversepath h2) /\
         pathfinish(h1 ++ reversepath h2) = pathstart(h1 ++ reversepath h2) /\
         pl_map_on (interval[vec 0,vec 1]) (h1 ++ reversepath h2) /\
         path_image(h1 ++ reversepath h2) = path_image h1 UNION path_image h2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_SIMP_TAC[SIMPLE_PATH_JOIN_LOOP_EQ; PATHSTART_REVERSEPATH;
               PATHFINISH_REVERSEPATH; PATHSTART_JOIN; PATHFINISH_JOIN;
               ARC_REVERSEPATH; PATH_IMAGE_REVERSEPATH; PATH_IMAGE_JOIN;
               MOI_PL2_PL_JOINPATHS; MOI_PL2_PL_REVERSEPATH] THEN
  ASM SET_TAC[]);;

(* Two PL arcs with common ends and no other common point form a PL         *)
(* 1-sphere: glue PL homeomorphisms from the two arcs [e0,e1] and          *)
(* [e0,e2] UNION [e2,e1] of the boundary of the standard triangle.          *)

let MOI_SFR_ARCS_SPHERE = prove
 (`!h1 h2:real^1->real^2.
     arc h1 /\ pl_map_on (interval[vec 0,vec 1]) h1 /\
     arc h2 /\ pl_map_on (interval[vec 0,vec 1]) h2 /\
     pathstart h2 = pathstart h1 /\ pathfinish h2 = pathfinish h1 /\
     path_image h1 INTER path_image h2 = {pathstart h1,pathfinish h1}
     ==> pl_sphere 1 (path_image h1 UNION path_image h2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~collinear{vec 0:real^2,basis 1,basis 2}` ASSUME_TAC THENL
   [REWRITE_TAC[MOI_PL2_STD_TRIANGLES]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_PL2_NONCOLLINEAR_DISTINCT) THEN
  SUBGOAL_THEN
   `arc(linepath(vec 0:real^2,basis 1)) /\
    pl_map_on (interval[vec 0,vec 1]) (linepath(vec 0:real^2,basis 1)) /\
    pathstart(linepath(vec 0:real^2,basis 1)) = vec 0 /\
    pathfinish(linepath(vec 0:real^2,basis 1)) = basis 1 /\
    path_image(linepath(vec 0:real^2,basis 1)) = segment[vec 0,basis 1]`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[ARC_LINEPATH_EQ; PATHSTART_LINEPATH; PATHFINISH_LINEPATH;
                    PATH_IMAGE_LINEPATH] THEN
    SIMP_TAC[MOI_PL2_PL_LINEPATH; MOI_PL2_LOCALLY_POLYHEDRAL_INTERVAL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `arc(polygonal_path[vec 0:real^2;basis 2;basis 1]) /\
    pl_map_on (interval[vec 0,vec 1]) (polygonal_path[vec 0:real^2;basis 2;basis 1]) /\
    pathstart(polygonal_path[vec 0:real^2;basis 2;basis 1]) = vec 0 /\
    pathfinish(polygonal_path[vec 0:real^2;basis 2;basis 1]) = basis 1 /\
    path_image(polygonal_path[vec 0:real^2;basis 2;basis 1]) =
      segment[vec 0,basis 2] UNION segment[basis 2,basis 1]`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[MOI_PL2_PL_POLYGONAL_PATH] THEN REWRITE_TAC[polygonal_path] THEN
    SIMP_TAC[ARC_JOIN_EQ; PATHSTART_JOIN; PATHFINISH_JOIN; PATH_IMAGE_JOIN;
             PATHSTART_LINEPATH; PATHFINISH_LINEPATH; PATH_IMAGE_LINEPATH] THEN
    ASM_REWRITE_TAC[ARC_LINEPATH_EQ] THEN
    SUBGOAL_THEN `segment[vec 0:real^2,basis 2] INTER segment[basis 2,basis 1] =
                  {basis 2}` (fun th -> REWRITE_TAC[th; SUBSET_REFL]) THEN
    MATCH_MP_TAC INTER_SEGMENT THEN DISJ2_TAC THEN
    UNDISCH_TAC `~collinear{vec 0:real^2,basis 1,basis 2}` THEN
    REWRITE_TAC[INSERT_AC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `segment[vec 0:real^2,basis 1] INTER
    (segment[vec 0,basis 2] UNION segment[basis 2,basis 1]) = {vec 0,basis 1}`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `segment[vec 0:real^2,basis 1] INTER segment[vec 0,basis 2] =
                  {vec 0} /\
                  segment[vec 0:real^2,basis 1] INTER segment[basis 2,basis 1] =
                  {basis 1}`
    MP_TAC THENL
     [CONJ_TAC THENL
       [SUBST1_TAC(ISPECL [`vec 0:real^2`; `basis 1:real^2`] (CONJUNCT1 SEGMENT_SYM));
        SUBST1_TAC(ISPECL [`basis 2:real^2`; `basis 1:real^2`] (CONJUNCT1 SEGMENT_SYM))] THEN
      MATCH_MP_TAC INTER_SEGMENT THEN DISJ2_TAC THEN
      UNDISCH_TAC `~collinear{vec 0:real^2,basis 1,basis 2}` THEN
      REWRITE_TAC[INSERT_AC];
      ALL_TAC] THEN
    SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `linepath(vec 0:real^2,basis 1)` MOI_PL2_ARC_PL_HOMEOMORPHISM_ENDS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `l1:real^2->real^1`
    STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPEC `polygonal_path[vec 0:real^2;basis 2;basis 1]`
    MOI_PL2_ARC_PL_HOMEOMORPHISM_ENDS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `l2:real^2->real^1`
    STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPEC `h1:real^1->real^2` MOI_PL2_ARC_PL_HOMEOMORPHISM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `k1:real^2->real^1`) THEN
  MP_TAC(ISPEC `h2:real^1->real^2` MOI_PL2_ARC_PL_HOMEOMORPHISM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `k2:real^2->real^1`) THEN
  SUBGOAL_THEN
   `pl_homeomorphism (segment[vec 0:real^2,basis 1],path_image h1)
      ((h1:real^1->real^2) o (l1:real^2->real^1),
       linepath(vec 0:real^2,basis 1) o (k1:real^2->real^1)) /\
    pl_homeomorphism (segment[vec 0:real^2,basis 2] UNION segment[basis 2,basis 1],
                      path_image h2)
      ((h2:real^1->real^2) o (l2:real^2->real^1),
       polygonal_path[vec 0:real^2;basis 2;basis 1] o (k2:real^2->real^1))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
    EXISTS_TAC `interval[vec 0:real^1,vec 1]` THEN
    ONCE_REWRITE_TAC[PL_HOMEOMORPHISM_SYM] THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[PL_HOMEOMORPHISM_SYM] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`segment[vec 0:real^2,basis 1]`;
    `segment[vec 0:real^2,basis 2] UNION segment[basis 2,basis 1]`;
    `path_image(h1:real^1->real^2)`; `path_image(h2:real^1->real^2)`;
    `(h1:real^1->real^2) o (l1:real^2->real^1)`;
    `linepath(vec 0:real^2,basis 1) o (k1:real^2->real^1)`;
    `(h2:real^1->real^2) o (l2:real^2->real^1)`;
    `polygonal_path[vec 0:real^2;basis 2;basis 1] o (k2:real^2->real^1)`]
   MOI_PL2_PL_HOMEOMORPHISM_UNION) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    SIMP_TAC[CLOSED_UNION; CLOSED_SEGMENT] THEN
    ASM_SIMP_TAC[CLOSED_PATH_IMAGE; ARC_IMP_PATH] THEN
    REWRITE_TAC[FORALL_IN_INSERT; NOT_IN_EMPTY; IMAGE_CLAUSES; o_THM] THEN
    SUBGOAL_THEN `(l1:real^2->real^1) (vec 0) = vec 0 /\ l1 (basis 1) = vec 1 /\
                  (l2:real^2->real^1) (vec 0) = vec 0 /\ l2 (basis 1) = vec 1`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `pathstart (h2:real^1->real^2) = pathstart h1` THEN
    UNDISCH_TAC `pathfinish (h2:real^1->real^2) = pathfinish h1` THEN
    REWRITE_TAC[pathstart; pathfinish] THEN
    REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[];
    DISCH_TAC] THEN
  REWRITE_TAC[pl_sphere] THEN
  EXISTS_TAC `convex hull {vec 0:real^2,basis 1,basis 2}` THEN
  REWRITE_TAC[RIGHT_EXISTS_AND_THM] THEN CONJ_TAC THENL
   [REWRITE_TAC[ARITH_RULE `1 + 1 = 2`; MOI_PL2_SIMPLEX_2] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[RELATIVE_FRONTIER_OF_TRIANGLE] THEN
  SUBGOAL_THEN
   `segment[vec 0:real^2,basis 1] UNION segment[basis 1,basis 2] UNION
    segment[basis 2,vec 0] =
    segment[vec 0,basis 1] UNION
    (segment[vec 0,basis 2] UNION segment[basis 2,basis 1])`
  SUBST1_TAC THENL
   [REWRITE_TAC[ISPECL [`basis 1:real^2`; `basis 2:real^2`] (CONJUNCT1 SEGMENT_SYM);
                ISPECL [`basis 2:real^2`; `vec 0:real^2`] (CONJUNCT1 SEGMENT_SYM)] THEN
    SET_TAC[];
    ASM_MESON_TAC[]]);;

let MOI_SFR_JORDAN_REGION = prove
 (`!(c:real^1->real^2) s.
     simple_path c /\ pathfinish c = pathstart c /\ path_image c = s
     ==> compact s /\ compact(s UNION inside s) /\
         frontier(s UNION inside s) = s /\
         interior(s UNION inside s) = inside s /\
         closure(inside s) = s UNION inside s /\
         (:real^2) DIFF outside s = s UNION inside s /\
         ~(inside s = {}) /\ open(inside s) /\ connected(inside s) /\
         bounded(inside s) /\ connected(outside s) /\ ~bounded(outside s) /\
         inside s INTER s = {} /\ outside s INTER s = {} /\
         inside s INTER outside s = {} /\
         inside s UNION outside s = (:real^2) DIFF s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
  MP_TAC(ISPEC `c:real^1->real^2` JORDAN_INSIDE_OUTSIDE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[INSIDE_NO_OVERLAP; OUTSIDE_NO_OVERLAP] THEN
  SUBGOAL_THEN `compact(path_image(c:real^1->real^2))` ASSUME_TAC THENL
   [ASM_MESON_TAC[COMPACT_PATH_IMAGE; SIMPLE_PATH_IMP_PATH]; ALL_TAC] THEN
  SUBGOAL_THEN `path_image c UNION inside(path_image c) =
                (:real^2) DIFF outside(path_image(c:real^1->real^2))`
  ASSUME_TAC THENL
   [MP_TAC(ISPEC `path_image(c:real^1->real^2)` INSIDE_NO_OVERLAP) THEN
    MP_TAC(ISPEC `path_image(c:real^1->real^2)` OUTSIDE_NO_OVERLAP) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `frontier(path_image c UNION inside(path_image c)) =
    path_image(c:real^1->real^2)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_PL2_FRONTIER_JORDAN_REGION THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `compact(path_image c UNION inside(path_image(c:real^1->real^2)))`
  ASSUME_TAC THENL
   [REWRITE_TAC[COMPACT_EQ_BOUNDED_CLOSED] THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[BOUNDED_UNION; COMPACT_IMP_BOUNDED];
      ASM_REWRITE_TAC[] THEN ASM_REWRITE_TAC[GSYM OPEN_CLOSED]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `interior(path_image c UNION inside(path_image c)) =
    inside(path_image(c:real^1->real^2))`
  ASSUME_TAC THENL
   [MP_TAC(ISPEC `path_image c UNION inside(path_image(c:real^1->real^2))`
      INTERIOR_SUBSET) THEN
    UNDISCH_TAC
     `frontier(path_image c UNION inside(path_image c)) =
      path_image(c:real^1->real^2)` THEN
    REWRITE_TAC[frontier] THEN
    SUBGOAL_THEN
     `closure(path_image c UNION inside(path_image(c:real^1->real^2))) =
      path_image c UNION inside(path_image c)`
    SUBST1_TAC THENL
     [ASM_MESON_TAC[CLOSURE_CLOSED; COMPACT_IMP_CLOSED]; ALL_TAC] THEN
    MP_TAC(ISPEC `path_image(c:real^1->real^2)` INSIDE_NO_OVERLAP) THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `closure(inside(path_image c)) =
    path_image c UNION inside(path_image(c:real^1->real^2))`
  ASSUME_TAC THENL
   [REWRITE_TAC[CLOSURE_UNION_FRONTIER] THEN
    REWRITE_TAC[ASSUME `frontier(inside(path_image c)) =
                        path_image(c:real^1->real^2)`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THEN
  (FIRST_ASSUM ACCEPT_TAC ORELSE
   (CONV_TAC SYM_CONV THEN FIRST_ASSUM ACCEPT_TAC)));;

let MOI_SFR_ARCS_CELL = prove
 (`!(h1:real^1->real^2) h2 s.
     arc h1 /\ pl_map_on (interval[vec 0,vec 1]) h1 /\
     arc h2 /\ pl_map_on (interval[vec 0,vec 1]) h2 /\
     pathstart h2 = pathstart h1 /\ pathfinish h2 = pathfinish h1 /\
     path_image h1 INTER path_image h2 = {pathstart h1,pathfinish h1} /\
     path_image h1 UNION path_image h2 = s
     ==> pl_cell_with_boundary 2 (s UNION inside s) s /\
         pl_ball 2 (s UNION inside s) /\
         frontier(s UNION inside s) = s /\
         interior(s UNION inside s) = inside s /\
         closure(inside s) = s UNION inside s /\
         compact(s UNION inside s) /\
         ~(inside s = {}) /\ open(inside s) /\ connected(inside s) /\
         inside s INTER s = {}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`h1:real^1->real^2`; `h2:real^1->real^2`] MOI_SFR_ARCS_LOOP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`(h1:real^1->real^2) ++ reversepath h2`; `s:real^2->bool`]
    MOI_SFR_JORDAN_REGION) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `pl_sphere 1 (s:real^2->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `path_image h1 UNION path_image h2 = (s:real^2->bool)` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC MOI_SFR_ARCS_SPHERE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_ball 2 (s UNION inside s:real^2->bool)` ASSUME_TAC THENL
   [MP_TAC PL_SCHOENFLIES_2 THEN REWRITE_TAC[PL_SCHOENFLIES_2_STATEMENT] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_SFR_PL_BALL_CELL) THEN ASM_REWRITE_TAC[]);;

(* A PL 2-cell d in real^2 with boundary j: j is a PL simple closed curve   *)
(* and d = j UNION inside j (via the connected complement of a cell).        *)

let MOI_SFR_CELL_FACTS = prove
 (`!d j:real^2->bool.
     pl_cell_with_boundary 2 d j
     ==> (?gam:real^1->real^2.
              simple_path gam /\ pathfinish gam = pathstart gam /\
              pl_map_on (interval[vec 0,vec 1]) gam /\ path_image gam = j) /\
         d = j UNION inside j /\ frontier d = j /\ interior d = inside j /\
         compact d /\ pl_ball 2 d /\ ~(inside j = {}) /\ connected(inside j) /\
         closure(inside j) = d /\ inside j INTER j = {} /\ j SUBSET d`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_SFR_CELL_BALL) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o SYM)) THEN
  UNDISCH_TAC `pl_cell_with_boundary 2 (d:real^2->bool) j` THEN
  REWRITE_TAC[pl_cell_with_boundary; MOI_PL2_SIMPLEX_2; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`k:real^2->bool`; `f:real^2->real^2`; `g:real^2->real^2`] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `a:real^2` (X_CHOOSE_THEN `b:real^2`
     (X_CHOOSE_THEN `c:real^2` STRIP_ASSUME_TAC)))
   (CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o SYM))) THEN
  UNDISCH_TAC `k = convex hull {a:real^2,b,c}` THEN
  DISCH_THEN SUBST_ALL_TAC THEN
  SUBGOAL_THEN `compact(convex hull {a:real^2,b,c}) /\ convex(convex hull {a,b,c})`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[CONVEX_CONVEX_HULL] THEN MATCH_MP_TAC COMPACT_CONVEX_HULL THEN
    MATCH_MP_TAC FINITE_IMP_COMPACT THEN REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY];
    ALL_TAC] THEN
  SUBGOAL_THEN `relative_frontier(convex hull {a:real^2,b,c}) SUBSET
                convex hull {a,b,c}` ASSUME_TAC THENL
   [REWRITE_TAC[relative_frontier] THEN
    ASM_SIMP_TAC[CLOSURE_CLOSED; COMPACT_IMP_CLOSED] THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ASSUME `pl_homeomorphism (convex hull {a:real^2,b,c},d:real^2->bool)
                 (f:real^2->real^2,g:real^2->real^2)`) THEN
  REWRITE_TAC[pl_homeomorphism; homeomorphism] THEN STRIP_TAC THEN
  SUBGOAL_THEN `compact(d:real^2->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_PL2_PL_HOMEO_COMPACT]; ALL_TAC] THEN
  MP_TAC(ISPECL [`a:real^2`; `b:real^2`; `c:real^2`] MOI_PL2_TRIANGLE_POLYGON) THEN
  ASM_SIMP_TAC[GSYM RELATIVE_FRONTIER_OF_TRIANGLE] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `simple_path((f:real^2->real^2) o polygonal_path[a;b;c;a]) /\
    pathfinish(f o polygonal_path[a;b;c;a]) =
      pathstart(f o polygonal_path[a;b;c;a]) /\
    pl_map_on (interval[vec 0,vec 1]) (f o polygonal_path[a;b;c;a]) /\
    path_image(f o polygonal_path[a;b;c;a]) = (j:real^2->bool)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[PATHSTART_COMPOSE; PATHFINISH_COMPOSE; PATH_IMAGE_COMPOSE] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SIMPLE_PATH_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL
       [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
        ASM_MESON_TAC[SUBSET]];
      MATCH_MP_TAC PL_MAP_ON_COMPOSE THEN
      EXISTS_TAC `convex hull {a:real^2,b,c}` THEN
      ASM_REWRITE_TAC[MOI_PL2_PL_POLYGONAL_PATH; GSYM path_image]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(f:real^2->real^2) o polygonal_path[a;b;c;a]`; `j:real^2->bool`]
    MOI_SFR_JORDAN_REGION) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(j:real^2->bool) SUBSET d` ASSUME_TAC THENL
   [ASM_MESON_TAC[FRONTIER_SUBSET_CLOSED; COMPACT_IMP_CLOSED]; ALL_TAC] THEN
  SUBGOAL_THEN `connected((:real^2) DIFF d)` ASSUME_TAC THENL
   [MATCH_MP_TAC(ISPECL [`d:real^2->bool`; `convex hull {a:real^2,b,c}`]
      CONNECTED_COMPLEMENT_HOMEOMORPHIC_CONVEX_COMPACT) THEN
    ASM_REWRITE_TAC[DIMINDEX_2; LE_REFL] THEN
    REWRITE_TAC[homeomorphic] THEN
    MAP_EVERY EXISTS_TAC [`g:real^2->real^2`; `f:real^2->real^2`] THEN
    ONCE_REWRITE_TAC[HOMEOMORPHISM_SYM] THEN ASM_REWRITE_TAC[homeomorphism];
    ALL_TAC] THEN
  SUBGOAL_THEN `~bounded((:real^2) DIFF d)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `bounded((d:real^2->bool) UNION ((:real^2) DIFF d))` MP_TAC THENL
     [ASM_SIMP_TAC[BOUNDED_UNION; COMPACT_IMP_BOUNDED];
      REWRITE_TAC[SET_RULE `(s:real^2->bool) UNION (UNIV DIFF s) = UNIV`;
                  NOT_BOUNDED_UNIV]];
    ALL_TAC] THEN
  SUBGOAL_THEN `inside j SUBSET (d:real^2->bool) DIFF j` ASSUME_TAC THENL
   [MATCH_MP_TAC INSIDE_SUBSET THEN EXISTS_TAC `(:real^2) DIFF d` THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `interior d INTER outside j = {}:real^2->bool` ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
    DISCH_TAC THEN
    MP_TAC(ISPECL [`outside j:real^2->bool`; `interior d:real^2->bool`]
      CONNECTED_INTER_FRONTIER) THEN
    ASM_REWRITE_TAC[NOT_IMP] THEN REPEAT CONJ_TAC THENL
     [ASM SET_TAC[];
      DISCH_TAC THEN
      UNDISCH_TAC `~bounded(outside j:real^2->bool)` THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC BOUNDED_SUBSET THEN EXISTS_TAC `d:real^2->bool` THEN
      ASM_SIMP_TAC[COMPACT_IMP_BOUNDED] THEN
      MP_TAC(ISPEC `d:real^2->bool` INTERIOR_SUBSET) THEN ASM SET_TAC[];
      MP_TAC(ISPEC `d:real^2->bool` FRONTIER_INTERIOR_SUBSET) THEN
      ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `interior d SUBSET inside(j:real^2->bool)` ASSUME_TAC THENL
   [SUBGOAL_THEN `interior d INTER (j:real^2->bool) = {}` MP_TAC THENL
     [UNDISCH_TAC `frontier d = (j:real^2->bool)` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[frontier] THEN SET_TAC[];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `d = (j:real^2->bool) UNION inside j` ASSUME_TAC THENL
   [MP_TAC(ISPEC `d:real^2->bool` INTERIOR_SUBSET) THEN
    UNDISCH_TAC `frontier d = (j:real^2->bool)` THEN
    REWRITE_TAC[frontier] THEN ASM_SIMP_TAC[CLOSURE_CLOSED; COMPACT_IMP_CLOSED] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `interior d = inside(j:real^2->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [EXISTS_TAC `(f:real^2->real^2) o polygonal_path[a;b;c;a]` THEN
    ASM_REWRITE_TAC[];
    ASM_MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* 3. Splitting a PL simple closed curve at two points; crosscuts: an arc   *)
(* of a PL simple closed curve meeting a closed set j exactly in its ends.  *)
(* ------------------------------------------------------------------------- *)

let MOI_SFR_LOOP_SPLIT = prove
 (`!(gam:real^1->real^N) p q.
     simple_path gam /\ pathfinish gam = pathstart gam /\
     pl_map_on (interval[vec 0,vec 1]) gam /\
     p IN path_image gam /\ q IN path_image gam /\ ~(p = q)
     ==> ?a1 a2. arc a1 /\ pl_map_on (interval[vec 0,vec 1]) a1 /\
                 arc a2 /\ pl_map_on (interval[vec 0,vec 1]) a2 /\
                 pathstart a1 = p /\ pathfinish a1 = q /\
                 pathstart a2 = p /\ pathfinish a2 = q /\
                 path_image a1 UNION path_image a2 = path_image gam /\
                 path_image a1 INTER path_image a2 = {p,q}`,
  REPEAT STRIP_TAC THEN
  UNDISCH_TAC `(p:real^N) IN path_image gam` THEN
  REWRITE_TAC[path_image; IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^1`
    (CONJUNCTS_THEN2 (ASSUME_TAC o SYM) ASSUME_TAC)) THEN
  REWRITE_TAC[GSYM path_image] THEN
  SUBGOAL_THEN `&0 <= drop t /\ drop t <= &1` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[IN_INTERVAL_1; DROP_VEC]; ALL_TAC] THEN
  SUBGOAL_THEN
   `simple_path(shiftpath t (gam:real^1->real^N)) /\
    pathstart(shiftpath t gam) = p /\ pathfinish(shiftpath t gam) = p /\
    pl_map_on (interval[vec 0,vec 1]) (shiftpath t gam) /\
    path_image(shiftpath t gam) = path_image gam`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SIMPLE_PATH_SHIFTPATH; PATHSTART_SHIFTPATH; PATHFINISH_SHIFTPATH;
                 PATH_IMAGE_SHIFTPATH; MOI_PL2_PL_SHIFTPATH];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?s. s IN interval[vec 0,vec 1] /\ shiftpath t (gam:real^1->real^N) s = q`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(q:real^N) IN path_image gam` THEN
    UNDISCH_TAC `path_image(shiftpath t gam) = path_image(gam:real^1->real^N)` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[path_image; IN_IMAGE] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `arc(subpath (vec 0) s (shiftpath t (gam:real^1->real^N)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC ARC_SIMPLE_PATH_SUBPATH THEN
    ASM_REWRITE_TAC[ENDS_IN_UNIT_INTERVAL] THEN ASM_MESON_TAC[pathstart];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`shiftpath t (gam:real^1->real^N)`;
                 `subpath (vec 0) s (shiftpath t (gam:real^1->real^N))`]
    MOI_PL2_ARC_IN_LOOP) THEN
  SUBGOAL_THEN
   `path_image(subpath (vec 0) s (shiftpath t gam)) SUBSET
    path_image(shiftpath t (gam:real^1->real^N))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC PATH_IMAGE_SUBPATH_SUBSET THEN
    ASM_SIMP_TAC[SIMPLE_PATH_IMP_PATH; ENDS_IN_UNIT_INTERVAL];
    ALL_TAC] THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[PATHSTART_SUBPATH; PATHFINISH_SUBPATH] THEN
  SUBGOAL_THEN `shiftpath t (gam:real^1->real^N) (vec 0) = p` SUBST1_TAC THENL
   [ASM_MESON_TAC[pathstart]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^1->real^N` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC
   [`subpath (vec 0) s (shiftpath t (gam:real^1->real^N))`;
    `reversepath(k:real^1->real^N)`] THEN
  ASM_SIMP_TAC[ARC_REVERSEPATH; MOI_PL2_PL_REVERSEPATH; MOI_PL2_PL_SUBPATH;
               PATHSTART_REVERSEPATH; PATHFINISH_REVERSEPATH;
               PATH_IMAGE_REVERSEPATH; PATHSTART_SUBPATH; PATHFINISH_SUBPATH;
               ENDS_IN_UNIT_INTERVAL] THEN
  ASM_MESON_TAC[pathstart]);;

(* A crosscut: if a PL simple closed curve meets the closed set j in two    *)
(* distinct points u, w and also has a point y off j, then it contains a    *)
(* PL arc through y meeting j exactly in its two ends (start the loop at u  *)
(* and take the last zero before y and the first one after y).               *)

let MOI_SFR_CROSSCUT = prove
 (`!(gam:real^1->real^N) j u w y.
     simple_path gam /\ pathfinish gam = pathstart gam /\
     pl_map_on (interval[vec 0,vec 1]) gam /\ closed j /\
     u IN path_image gam /\ u IN j /\ w IN path_image gam /\ w IN j /\
     ~(u = w) /\ y IN path_image gam /\ ~(y IN j)
     ==> ?b. arc b /\ pl_map_on (interval[vec 0,vec 1]) b /\
             path_image b SUBSET path_image gam /\
             path_image b INTER j = {pathstart b,pathfinish b}`,
  REPEAT STRIP_TAC THEN
  UNDISCH_TAC `(u:real^N) IN path_image gam` THEN
  REWRITE_TAC[path_image; IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^1`
    (CONJUNCTS_THEN2 (ASSUME_TAC o SYM) ASSUME_TAC)) THEN
  REWRITE_TAC[GSYM path_image] THEN
  SUBGOAL_THEN `&0 <= drop t /\ drop t <= &1` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[IN_INTERVAL_1; DROP_VEC]; ALL_TAC] THEN
  SUBGOAL_THEN
   `simple_path(shiftpath t (gam:real^1->real^N)) /\
    pathstart(shiftpath t gam) = u /\ pathfinish(shiftpath t gam) = u /\
    pl_map_on (interval[vec 0,vec 1]) (shiftpath t gam) /\
    path_image(shiftpath t gam) = path_image gam`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SIMPLE_PATH_SHIFTPATH; PATHSTART_SHIFTPATH; PATHFINISH_SHIFTPATH;
                 PATH_IMAGE_SHIFTPATH; MOI_PL2_PL_SHIFTPATH];
    ALL_TAC] THEN
  ABBREV_TAC `gg = shiftpath t (gam:real^1->real^N)` THEN
  SUBGOAL_THEN `(gg:real^1->real^N) continuous_on interval[vec 0,vec 1]`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[path; SIMPLE_PATH_IMP_PATH]; ALL_TAC] THEN
  SUBGOAL_THEN `(gg:real^1->real^N) (vec 0) = u /\ gg (vec 1) = u`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[pathstart; pathfinish]; ALL_TAC] THEN
  SUBGOAL_THEN
   `?s0. s0 IN interval[vec 0,vec 1] /\ (gg:real^1->real^N) s0 = y`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(y:real^N) IN path_image gam` THEN
    UNDISCH_TAC `path_image gg = path_image(gam:real^1->real^N)` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[path_image; IN_IMAGE] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < drop s0 /\ drop s0 < &1` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `s0 IN interval[vec 0:real^1,vec 1]` THEN
    REWRITE_TAC[IN_INTERVAL_1; DROP_VEC] THEN
    SUBGOAL_THEN `~(s0 = vec 0:real^1) /\ ~(s0 = vec 1:real^1)` MP_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[GSYM DROP_EQ; DROP_VEC] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`drop`; `{x | x IN interval[vec 0,s0] /\ (gg:real^1->real^N) x IN j}`]
   CONTINUOUS_ATTAINS_SUP) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[o_DEF; LIFT_DROP; CONTINUOUS_ON_ID] THEN CONJ_TAC THENL
     [REWRITE_TAC[COMPACT_EQ_BOUNDED_CLOSED] THEN CONJ_TAC THENL
       [MATCH_MP_TAC BOUNDED_SUBSET THEN
        EXISTS_TAC `interval[vec 0:real^1,s0]` THEN
        REWRITE_TAC[BOUNDED_INTERVAL] THEN SET_TAC[];
        MATCH_MP_TAC CONTINUOUS_CLOSED_PREIMAGE THEN
        ASM_REWRITE_TAC[CLOSED_INTERVAL] THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
          CONTINUOUS_ON_SUBSET)) THEN
        REWRITE_TAC[SUBSET_INTERVAL_1; DROP_VEC] THEN ASM_REAL_ARITH_TAC];
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
      EXISTS_TAC `vec 0:real^1` THEN
      ASM_REWRITE_TAC[IN_INTERVAL_1; DROP_VEC] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^1` (CONJUNCTS_THEN2 STRIP_ASSUME_TAC
    (LABEL_TAC "amax"))) THEN
  MP_TAC(ISPECL
   [`drop`; `{x | x IN interval[s0,vec 1] /\ (gg:real^1->real^N) x IN j}`]
   CONTINUOUS_ATTAINS_INF) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[o_DEF; LIFT_DROP; CONTINUOUS_ON_ID] THEN CONJ_TAC THENL
     [REWRITE_TAC[COMPACT_EQ_BOUNDED_CLOSED] THEN CONJ_TAC THENL
       [MATCH_MP_TAC BOUNDED_SUBSET THEN
        EXISTS_TAC `interval[s0,vec 1:real^1]` THEN
        REWRITE_TAC[BOUNDED_INTERVAL] THEN SET_TAC[];
        MATCH_MP_TAC CONTINUOUS_CLOSED_PREIMAGE THEN
        ASM_REWRITE_TAC[CLOSED_INTERVAL] THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
          CONTINUOUS_ON_SUBSET)) THEN
        REWRITE_TAC[SUBSET_INTERVAL_1; DROP_VEC] THEN ASM_REAL_ARITH_TAC];
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
      EXISTS_TAC `vec 1:real^1` THEN
      ASM_REWRITE_TAC[IN_INTERVAL_1; DROP_VEC] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `b:real^1` (CONJUNCTS_THEN2 STRIP_ASSUME_TAC
    (LABEL_TAC "bmin"))) THEN
  SUBGOAL_THEN `&0 <= drop a /\ drop a < drop s0 /\ drop s0 < drop b /\
                drop b <= &1`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`a IN interval[vec 0:real^1,s0]`;
                           `b IN interval[s0,vec 1:real^1]`] THEN
    REWRITE_TAC[IN_INTERVAL_1; DROP_VEC] THEN
    SUBGOAL_THEN `~(a:real^1 = s0) /\ ~(b:real^1 = s0)` MP_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[GSYM DROP_EQ] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(a:real^1) IN interval[vec 0,vec 1] /\ (b:real^1) IN interval[vec 0,vec 1]`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[IN_INTERVAL_1; DROP_VEC] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN interval[a,b] /\ (gg:real^1->real^N) x IN j ==> x = a \/ x = b`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^1` THEN REWRITE_TAC[IN_INTERVAL_1] THEN STRIP_TAC THEN
    ASM_CASES_TAC `drop x <= drop s0` THENL
     [DISJ1_TAC THEN REWRITE_TAC[GSYM DROP_EQ] THEN
      REMOVE_THEN "amax" (MP_TAC o SPEC `x:real^1`) THEN
      ASM_REWRITE_TAC[IN_INTERVAL_1; DROP_VEC] THEN ASM_REAL_ARITH_TAC;
      DISJ2_TAC THEN REWRITE_TAC[GSYM DROP_EQ] THEN
      REMOVE_THEN "bmin" (MP_TAC o SPEC `x:real^1`) THEN
      ASM_REWRITE_TAC[IN_INTERVAL_1; DROP_VEC] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((gg:real^1->real^N) a = gg b)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `a = vec 0:real^1 /\ b = vec 1:real^1` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `simple_path(gg:real^1->real^N)` THEN
      REWRITE_TAC[simple_path] THEN
      DISCH_THEN(MP_TAC o SPECL [`a:real^1`; `b:real^1`] o CONJUNCT2) THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[GSYM DROP_EQ; DROP_VEC] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    UNDISCH_TAC `(w:real^N) IN path_image gam` THEN
    UNDISCH_TAC `path_image gg = path_image(gam:real^1->real^N)` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[path_image; IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:real^1` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^1`) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(gg:real^1->real^N) x IN j` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `subpath a b (gg:real^1->real^N)` THEN
  ASM_SIMP_TAC[ARC_SIMPLE_PATH_SUBPATH; MOI_PL2_PL_SUBPATH;
               PATHSTART_SUBPATH; PATHFINISH_SUBPATH] THEN
  SUBGOAL_THEN `path_image(subpath a b (gg:real^1->real^N)) =
                IMAGE gg (interval[a,b])` SUBST1_TAC THENL
   [MATCH_MP_TAC PATH_IMAGE_SUBPATH THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [UNDISCH_TAC `path_image gg = path_image(gam:real^1->real^N)` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[path_image] THEN
    MATCH_MP_TAC IMAGE_SUBSET THEN
    REWRITE_TAC[SUBSET_INTERVAL_1; DROP_VEC] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[EXTENSION; IN_INTER; IN_IMAGE; IN_INSERT; NOT_IN_EMPTY] THEN
  X_GEN_TAC `z:real^N` THEN EQ_TAC THENL
   [DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `x:real^1` STRIP_ASSUME_TAC)
      ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^1`) THEN ASM_MESON_TAC[];
    STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
     [EXISTS_TAC `a:real^1`; EXISTS_TAC `b:real^1`] THEN
    ASM_REWRITE_TAC[IN_INTERVAL_1] THEN ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* 4. The theta-curve split of a PL 2-cell along a PL crosscut.              *)
(* ------------------------------------------------------------------------- *)

let MOI_SFR_CONNECTED_SIDE = prove
 (`!s u v b:real^N->bool.
     connected s /\ closed u /\ closed v /\ s SUBSET u UNION v /\
     u INTER v = b /\ s INTER b = {}
     ==> s SUBSET u \/ s SUBSET v`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_neg o concl) o
    GEN_REWRITE_RULE I [CONNECTED_CLOSED_IN_EQ]) THEN
  REWRITE_TAC[NOT_EXISTS_THM] THEN
  DISCH_THEN(MP_TAC o SPECL [`s INTER u:real^N->bool`; `s INTER v:real^N->bool`]) THEN
  ASM_SIMP_TAC[CLOSED_IN_CLOSED_INTER] THEN ASM SET_TAC[]);;

let MOI_SFR_ARC_MIDPOINT = prove
 (`!b:real^1->real^N.
     arc b ==> ?z. z IN path_image b /\ ~(z = pathstart b) /\ ~(z = pathfinish b)`,
  GEN_TAC THEN REWRITE_TAC[arc; path_image; pathstart; pathfinish] THEN
  STRIP_TAC THEN EXISTS_TAC `(b:real^1->real^N)(lift(&1 / &2))` THEN
  SUBGOAL_THEN `lift(&1 / &2) IN interval[vec 0,vec 1] /\
                ~(lift(&1 / &2) = vec 0) /\ ~(lift(&1 / &2) = vec 1)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[IN_INTERVAL_1; GSYM DROP_EQ; LIFT_DROP; DROP_VEC] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[FUN_IN_IMAGE] THEN ASM_MESON_TAC[ENDS_IN_UNIT_INTERVAL]);;

let MOI_SFR_THETA_SETS = prove
 (`!(a1:real^2->bool) a2 b j i i1 i2 u v p q.
     a1 INTER a2 = {p,q} /\ a1 UNION a2 = j /\ b INTER j = {p,q} /\
     p IN a1 /\ q IN a1 /\
     i INTER j = {} /\ i1 INTER (a1 UNION b) = {} /\ i2 INTER (a2 UNION b) = {} /\
     i1 INTER i2 = {} /\ i1 UNION i2 UNION (b DIFF {p,q}) = i /\
     (a1 UNION b) UNION i1 = u /\ (a2 UNION b) UNION i2 = v
     ==> u UNION v = j UNION i /\ u INTER v = b /\
         u INTER a2 = {p,q} /\ v INTER a1 = {p,q}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th ->
    let l,r = dest_eq(concl th) in is_var r && (r = `u:real^2->bool` || r = `v:real^2->bool` ||
                       r = `j:real^2->bool` || r = `i:real^2->bool`)))) THEN
  ASM SET_TAC[]);;

(* The split.  j = a1 UNION a2 is the boundary of the 2-cell j UNION inside j *)
(* (two PL arcs from p to q), b a PL crosscut from p to q inside it.  The    *)
(* two closed sides u and v are PL 2-cells meeting exactly in b, covering   *)
(* the cell, and every connected subset of the cell missing b lies on one   *)
(* side.                                                                     *)

let MOI_SFR_THETA = prove
 (`!(a1:real^1->real^2) a2 b j u v.
     arc a1 /\ pl_map_on (interval[vec 0,vec 1]) a1 /\
     arc a2 /\ pl_map_on (interval[vec 0,vec 1]) a2 /\
     arc b /\ pl_map_on (interval[vec 0,vec 1]) b /\
     pathstart a2 = pathstart a1 /\ pathfinish a2 = pathfinish a1 /\
     pathstart b = pathstart a1 /\ pathfinish b = pathfinish a1 /\
     path_image a1 INTER path_image a2 = {pathstart a1,pathfinish a1} /\
     path_image a1 UNION path_image a2 = j /\
     path_image b INTER j = {pathstart a1,pathfinish a1} /\
     path_image b SUBSET j UNION inside j /\
     (path_image a1 UNION path_image b) UNION
       inside(path_image a1 UNION path_image b) = u /\
     (path_image a2 UNION path_image b) UNION
       inside(path_image a2 UNION path_image b) = v
     ==> pl_cell_with_boundary 2 u (path_image a1 UNION path_image b) /\
         pl_cell_with_boundary 2 v (path_image a2 UNION path_image b) /\
         frontier u = path_image a1 UNION path_image b /\
         frontier v = path_image a2 UNION path_image b /\
         interior u = inside(path_image a1 UNION path_image b) /\
         interior v = inside(path_image a2 UNION path_image b) /\
         ~(interior u = {}) /\ ~(interior v = {}) /\
         closure(interior u) = u /\ closure(interior v) = v /\
         compact u /\ compact v /\
         u UNION v = j UNION inside j /\ u INTER v = path_image b /\
         u INTER path_image a2 = {pathstart a1,pathfinish a1} /\
         v INTER path_image a1 = {pathstart a1,pathfinish a1} /\
         (!s. connected s /\ s SUBSET j UNION inside j /\
              s INTER path_image b = {}
              ==> s SUBSET u \/ s SUBSET v)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `p = pathstart(a1:real^1->real^2)` THEN
  ABBREV_TAC `q = pathfinish(a1:real^1->real^2)` THEN
  SUBGOAL_THEN `~(p:real^2 = q)` ASSUME_TAC THENL
   [ASM_MESON_TAC[ARC_DISTINCT_ENDS]; ALL_TAC] THEN
  SUBGOAL_THEN `(p:real^2) IN path_image a1 /\ q IN path_image a1 /\
                p IN path_image a2 /\ q IN path_image a2 /\
                p IN path_image b /\ q IN path_image (b:real^1->real^2)`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[PATHSTART_IN_PATH_IMAGE; PATHFINISH_IN_PATH_IMAGE]; ALL_TAC] THEN
  SUBGOAL_THEN `path_image a1 INTER path_image b = {p:real^2,q} /\
                path_image a2 INTER path_image (b:real^1->real^2) = {p,q}`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`path_image a1 UNION path_image a2 = (j:real^2->bool)`;
      `path_image b INTER j = {p:real^2,q}`] THEN
    MAP_EVERY UNDISCH_TAC
     [`(p:real^2) IN path_image a1`; `(q:real^2) IN path_image a1`;
      `(p:real^2) IN path_image a2`; `(q:real^2) IN path_image a2`;
      `(p:real^2) IN path_image b`; `(q:real^2) IN path_image b`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`a1:real^1->real^2`; `b:real^1->real^2`;
                 `path_image a1 UNION path_image(b:real^1->real^2)`]
    MOI_SFR_ARCS_CELL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`a2:real^1->real^2`; `b:real^1->real^2`;
                 `path_image a2 UNION path_image(b:real^1->real^2)`]
    MOI_SFR_ARCS_CELL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`a1:real^1->real^2`; `a2:real^1->real^2`] MOI_SFR_ARCS_LOOP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`(a1:real^1->real^2) ++ reversepath a2`; `j:real^2->bool`]
    MOI_SFR_JORDAN_REGION) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(path_image b INTER inside(j:real^2->bool) = {})` ASSUME_TAC THENL
   [MP_TAC(ISPEC `b:real^1->real^2` MOI_SFR_ARC_MIDPOINT) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `z:real^2` STRIP_ASSUME_TAC) THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `z:real^2` THEN
    MAP_EVERY UNDISCH_TAC
     [`path_image b INTER j = {p:real^2,q}`;
      `path_image b SUBSET (j:real^2->bool) UNION inside j`;
      `(z:real^2) IN path_image b`; `~(z:real^2 = p)`; `~(z:real^2 = q)`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`a1:real^1->real^2`; `a2:real^1->real^2`; `b:real^1->real^2`;
                 `p:real^2`; `q:real^2`] SPLIT_INSIDE_SIMPLE_CLOSED_CURVE) THEN
  ASM_SIMP_TAC[ARC_IMP_SIMPLE_PATH] THEN STRIP_TAC THEN
  MP_TAC(ISPECL
   [`path_image(a1:real^1->real^2)`; `path_image(a2:real^1->real^2)`;
    `path_image(b:real^1->real^2)`; `j:real^2->bool`; `inside(j:real^2->bool)`;
    `inside(path_image a1 UNION path_image(b:real^1->real^2))`;
    `inside(path_image a2 UNION path_image(b:real^1->real^2))`;
    `u:real^2->bool`; `v:real^2->bool`; `p:real^2`; `q:real^2`]
   MOI_SFR_THETA_SETS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `closed(u:real^2->bool) /\ closed(v:real^2->bool)`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[COMPACT_IMP_CLOSED]; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC MOI_SFR_CONNECTED_SIDE THEN
  EXISTS_TAC `path_image(b:real^1->real^2)` THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* 5. Local facts: an arc stays dense after removing finitely many points;  *)
(* the common face of two cells is interior to their union apart from      *)
(* finitely many points; a free cell of a piece is free in the whole.       *)
(* ------------------------------------------------------------------------- *)

let MOI_SFR_ARC_DENSE = prove
 (`!(h:real^1->real^N) k.
     arc h /\ FINITE k ==> path_image h SUBSET closure(path_image h DIFF k)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:real^N` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `(x:real^N) limit_point_of path_image h` MP_TAC THENL
   [MATCH_MP_TAC CONNECTED_IMP_PERFECT THEN
    ASM_SIMP_TAC[CONNECTED_PATH_IMAGE; ARC_IMP_PATH] THEN
    DISCH_THEN(X_CHOOSE_TAC `a:real^N`) THEN
    MP_TAC(ISPEC `h:real^1->real^N` ARC_DISTINCT_ENDS) THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `h:real^1->real^N` PATHSTART_IN_PATH_IMAGE) THEN
    MP_TAC(ISPEC `h:real^1->real^N` PATHFINISH_IN_PATH_IMAGE) THEN
    ASM_REWRITE_TAC[IN_SING] THEN MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[LIMPT_INFINITE_OPEN] THEN DISCH_TAC THEN
  REWRITE_TAC[closure; IN_UNION; IN_ELIM_THM] THEN DISJ2_TAC THEN
  REWRITE_TAC[LIMPT_INFINITE_OPEN] THEN X_GEN_TAC `t:real^N->bool` THEN
  STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `t:real^N->bool`) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o C CONJ (ASSUME `FINITE(k:real^N->bool)`)) THEN
  DISCH_THEN(MP_TAC o MATCH_MP INFINITE_DIFF_FINITE) THEN
  REWRITE_TAC[INFINITE; CONTRAPOS_THM] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] FINITE_SUBSET) THEN SET_TAC[]);;

let MOI_SFR_FACE_CASES = prove
 (`!g c e:real^2->bool.
     moi_sfr_cplx g /\ c IN g /\ e IN g /\ ~(c = e)
     ==> c INTER e = {} \/ (?u. c INTER e = {u}) \/
         (?u v. ~(u = v) /\ c INTER e = segment[u,v])`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(c INTER e) face_of (c:real^2->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[moi_sfr_cplx]; ALL_TAC] THEN
  SUBGOAL_THEN `polytope (c:real^2->bool) /\ aff_dim c = &2` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_SFR_CPLX_CELL]; ALL_TAC] THEN
  SUBGOAL_THEN `~((c:real^2->bool) INTER e = c)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`g:(real^2->bool)->bool`; `c:real^2->bool`; `e:real^2->bool`]
      MOI_SFR_CPLX_INTER) THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `aff_dim((c:real^2->bool) INTER e) < aff_dim c` MP_TAC THENL
   [MATCH_MP_TAC FACE_OF_AFF_DIM_LT THEN ASM_SIMP_TAC[POLYTOPE_IMP_CONVEX];
    ASM_REWRITE_TAC[] THEN DISCH_TAC] THEN
  SUBGOAL_THEN `polytope((c:real^2->bool) INTER e)` ASSUME_TAC THENL
   [ASM_MESON_TAC[FACE_OF_POLYTOPE_POLYTOPE]; ALL_TAC] THEN
  ASM_CASES_TAC `(c:real^2->bool) INTER e = {}` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `(c:real^2->bool) INTER e` COMPACT_CONVEX_COLLINEAR_SEGMENT) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[POLYTOPE_IMP_COMPACT; POLYTOPE_IMP_CONVEX; COLLINEAR_AFF_DIM] THEN
    MATCH_MP_TAC(INT_ARITH `x:int < &2 ==> x <= &1`) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^2` (X_CHOOSE_THEN `v:real^2` ASSUME_TAC)) THEN
  ASM_CASES_TAC `u:real^2 = v` THENL
   [DISJ1_TAC THEN EXISTS_TAC `u:real^2` THEN ASM_REWRITE_TAC[SEGMENT_REFL];
    DISJ2_TAC THEN MAP_EVERY EXISTS_TAC [`u:real^2`; `v:real^2`] THEN
    ASM_REWRITE_TAC[]]);;

(* Two PL 2-balls glued along a PL arc in both frontiers: the open arc is   *)
(* interior to the union.  The glued homeomorphism is the one built in the *)
(* proof of PL_BALL_2_UNION (pc_moi_pl2.ml), from the triangle             *)
(* conv{e1,e2,-e2}; the open segment from 0 to e1 is interior to it.        *)

let MOI_SFR_BALL_UNION_INTERIOR = prove
 (`!d1 d2:real^2->bool h.
     pl_ball 2 d1 /\ pl_ball 2 d2 /\ arc h /\
     pl_map_on (interval[vec 0,vec 1]) h /\
     path_image h = d1 INTER d2 /\
     d1 INTER d2 SUBSET frontier d1 INTER frontier d2
     ==> path_image h DIFF {pathstart h,pathfinish h} SUBSET interior(d1 UNION d2)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`d1:real^2->bool`; `h:real^1->real^2`; `vec 0:real^2`;
                 `basis 1:real^2`; `basis 2:real^2`]
    MOI_PL2_BALL_BOUNDARY_ARC) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[MOI_PL2_STD_TRIANGLES] THEN ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `f1:real^2->real^2`
   (X_CHOOSE_THEN `g1:real^2->real^2` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`d2:real^2->bool`; `h:real^1->real^2`; `vec 0:real^2`;
                 `basis 1:real^2`; `--basis 2:real^2`]
    MOI_PL2_BALL_BOUNDARY_ARC) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[MOI_PL2_STD_TRIANGLES] THEN ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `f2:real^2->real^2`
   (X_CHOOSE_THEN `g2:real^2->real^2` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN
   `compact(convex hull {vec 0:real^2,basis 1,basis 2}) /\
    compact(convex hull {vec 0:real^2,basis 1,--basis 2}) /\
    compact(convex hull {basis 1:real^2,basis 2,--basis 2})`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC COMPACT_CONVEX_HULL THEN
    MATCH_MP_TAC FINITE_IMP_COMPACT THEN
    REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY];
    ALL_TAC] THEN
  SUBGOAL_THEN `compact(d1:real^2->bool) /\ compact(d2:real^2->bool)`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_PL2_PL_HOMEO_COMPACT]; ALL_TAC] THEN
  MP_TAC(ISPECL
   [`convex hull {vec 0:real^2,basis 1,basis 2}`;
    `convex hull {vec 0:real^2,basis 1,--basis 2}`;
    `d1:real^2->bool`; `d2:real^2->bool`;
    `f1:real^2->real^2`; `g1:real^2->real^2`;
    `f2:real^2->real^2`; `g2:real^2->real^2`]
   MOI_PL2_PL_HOMEOMORPHISM_UNION) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[MOI_PL2_STD_TRIANGLES] THEN
    ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN
    REWRITE_TAC[GSYM PATH_IMAGE_LINEPATH; path_image; FORALL_IN_IMAGE] THEN
    ASM_SIMP_TAC[] THEN
    UNDISCH_TAC `path_image h = (d1:real^2->bool) INTER d2` THEN
    REWRITE_TAC[path_image] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[GSYM IMAGE_o; o_DEF] THEN
    MATCH_MP_TAC(SET_RULE
     `(!x:real^1. x IN s ==> (f:real^1->real^2) x = g x)
      ==> IMAGE f s = IMAGE g s`) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[MOI_PL2_STD_TRIANGLES] THEN
  ABBREV_TAC `ff = \x:real^2. if x IN convex hull {vec 0:real^2,basis 1,basis 2}
                            then (f1:real^2->real^2) x else f2 x` THEN
  ABBREV_TAC `gg = \y:real^2. if y IN d1 then (g1:real^2->real^2) y else g2 y` THEN
  DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[pl_homeomorphism]) THEN
  SUBGOAL_THEN
   `IMAGE (ff:real^2->real^2) (frontier(convex hull {basis 1:real^2,basis 2,--basis 2})) =
    frontier(d1 UNION d2)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_PL2_HOMEOMORPHISM_FRONTIER THEN
    EXISTS_TAC `gg:real^2->real^2` THEN
    ASM_SIMP_TAC[COMPACT_IMP_CLOSED; COMPACT_UNION];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET; IN_DIFF; IN_INSERT; NOT_IN_EMPTY; DE_MORGAN_THM] THEN
  X_GEN_TAC `x:real^2` THEN REWRITE_TAC[path_image; IN_IMAGE] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `t:real^1` STRIP_ASSUME_TAC)
    STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `&0 < drop t /\ drop t < &1` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `t IN interval[vec 0:real^1,vec 1]` THEN
    REWRITE_TAC[IN_INTERVAL_1; DROP_VEC] THEN
    SUBGOAL_THEN `~(t = vec 0:real^1) /\ ~(t = vec 1:real^1)` MP_TAC THENL
     [ASM_MESON_TAC[pathstart; pathfinish]; ALL_TAC] THEN
    REWRITE_TAC[GSYM DROP_EQ; DROP_VEC] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `linepath(vec 0:real^2,basis 1) t = drop t % basis 1`
  ASSUME_TAC THENL
   [REWRITE_TAC[linepath] THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `drop t % basis 1 IN convex hull {vec 0:real^2,basis 1,basis 2}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC(SET_RULE `!s t x:real^2. x IN s /\ s SUBSET t ==> x IN t`) THEN
    EXISTS_TAC `segment[vec 0:real^2,basis 1]` THEN CONJ_TAC THENL
     [REWRITE_TAC[GSYM PATH_IMAGE_LINEPATH; path_image] THEN
      UNDISCH_TAC `linepath(vec 0:real^2,basis 1) t = drop t % basis 1` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_SIMP_TAC[FUN_IN_IMAGE];
      REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN MATCH_MP_TAC HULL_MONO THEN
      SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(ff:real^2->real^2) (drop t % basis 1) = x` ASSUME_TAC THENL
   [EXPAND_TAC "ff" THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `drop t % basis 1 IN interior(convex hull {basis 1:real^2,basis 2,--basis 2})`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`basis 1:real^2`; `basis 2:real^2`; `--basis 2:real^2`]
      INTERIOR_CONVEX_HULL_3_MINIMAL) THEN
    REWRITE_TAC[MOI_PL2_STD_TRIANGLES] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[IN_ELIM_THM] THEN
    MAP_EVERY EXISTS_TAC [`drop t`; `(&1 - drop t) / &2`; `(&1 - drop t) / &2`] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC; VECTOR_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `interior(d1 UNION d2:real^2->bool) =
                (d1 UNION d2) DIFF frontier(d1 UNION d2)`
  SUBST1_TAC THENL
   [REWRITE_TAC[frontier] THEN
    ASM_SIMP_TAC[CLOSURE_CLOSED; COMPACT_IMP_CLOSED; CLOSED_UNION] THEN
    MP_TAC(ISPEC `d1 UNION d2:real^2->bool` INTERIOR_SUBSET) THEN SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[IN_DIFF] THEN CONJ_TAC THENL
   [SUBGOAL_THEN `(x:real^2) IN path_image h` MP_TAC THENL
     [REWRITE_TAC[path_image; IN_IMAGE] THEN EXISTS_TAC `t:real^1` THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[ASSUME `path_image h = (d1:real^2->bool) INTER d2`] THEN
      SET_TAC[]];
    ALL_TAC] THEN
  UNDISCH_TAC
   `IMAGE (ff:real^2->real^2) (frontier(convex hull {basis 1:real^2,basis 2,--basis 2})) =
    frontier(d1 UNION d2)` THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:real^2` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `z IN convex hull {basis 1:real^2,basis 2,--basis 2} /\
                drop t % basis 1 IN convex hull {basis 1:real^2,basis 2,--basis 2}`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPEC `convex hull {basis 1:real^2,basis 2,--basis 2}`
        FRONTIER_SUBSET_CLOSED) THEN
      ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN ASM SET_TAC[];
      MP_TAC(ISPEC `convex hull {basis 1:real^2,basis 2,--basis 2}`
        INTERIOR_SUBSET) THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ASSUME `homeomorphism
    (convex hull {basis 1:real^2,basis 2,--basis 2},d1 UNION d2:real^2->bool)
    (ff:real^2->real^2,gg:real^2->real^2)`) THEN
  REWRITE_TAC[homeomorphism] THEN DISCH_THEN(LABEL_TAC "linv" o CONJUNCT1) THEN
  SUBGOAL_THEN `z = drop t % basis 1:real^2` SUBST_ALL_TAC THENL
   [USE_THEN "linv" (MP_TAC o SPEC `z:real^2`) THEN
    USE_THEN "linv" (MP_TAC o SPEC `drop t % basis 1:real^2`) THEN
    MP_TAC(ASSUME `x = (ff:real^2->real^2) z`) THEN
    MP_TAC(ASSUME `(ff:real^2->real^2) (drop t % basis 1) = x`) THEN
    MP_TAC(ASSUME `z IN convex hull {basis 1:real^2,basis 2,--basis 2}`) THEN
    MP_TAC(ASSUME `drop t % basis 1 IN convex hull {basis 1:real^2,basis 2,--basis 2}`) THEN
    MESON_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `drop t % basis 1 IN
               frontier(convex hull {basis 1:real^2,basis 2,--basis 2})` THEN
  REWRITE_TAC[frontier; IN_DIFF] THEN ASM_REWRITE_TAC[]);;

let MOI_SFR_PAIR_INTERIOR = prove
 (`!g c e:real^2->bool.
     moi_sfr_cplx g /\ c IN g /\ e IN g /\ ~(c = e)
     ==> ?k. FINITE k /\ (c INTER e) DIFF k SUBSET interior(c UNION e)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`g:(real^2->bool)->bool`; `c:real^2->bool`; `e:real^2->bool`]
    MOI_SFR_FACE_CASES) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
   [EXISTS_TAC `{}:real^2->bool` THEN ASM_REWRITE_TAC[FINITE_EMPTY] THEN SET_TAC[];
    EXISTS_TAC `{u:real^2}` THEN ASM_REWRITE_TAC[FINITE_SING] THEN SET_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `{u:real^2,v}` THEN REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY] THEN
  SUBGOAL_THEN
   `path_image(linepath(u:real^2,v)) DIFF
    {pathstart(linepath(u,v)),pathfinish(linepath(u,v))} SUBSET
    interior(c UNION e)`
  MP_TAC THENL
   [MATCH_MP_TAC MOI_SFR_BALL_UNION_INTERIOR THEN
    ASM_REWRITE_TAC[ARC_LINEPATH_EQ; PATH_IMAGE_LINEPATH] THEN
    SIMP_TAC[MOI_PL2_PL_LINEPATH; MOI_PL2_LOCALLY_POLYHEDRAL_INTERVAL] THEN
    REPEAT CONJ_TAC THENL
     [MP_TAC(ISPEC `c:real^2->bool` MOI_SFR_POLYGON_CELL) THEN
      ANTS_TAC THENL [ASM_MESON_TAC[MOI_SFR_CPLX_CELL]; SIMP_TAC[]];
      MP_TAC(ISPEC `e:real^2->bool` MOI_SFR_POLYGON_CELL) THEN
      ANTS_TAC THENL [ASM_MESON_TAC[MOI_SFR_CPLX_CELL]; SIMP_TAC[]];
      MP_TAC(ISPECL [`g:(real^2->bool)->bool`; `c:real^2->bool`; `e:real^2->bool`]
        MOI_SFR_CPLX_INTER) THEN
      MP_TAC(ISPECL [`g:(real^2->bool)->bool`; `e:real^2->bool`; `c:real^2->bool`]
        MOI_SFR_CPLX_INTER) THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[]];
    REWRITE_TAC[PATHSTART_LINEPATH; PATHFINISH_LINEPATH; PATH_IMAGE_LINEPATH] THEN
    ASM_REWRITE_TAC[]]);;

(* A cell e other than c of a piece w (a closed subset of the decomposed    *)
(* disk, containing c and e, whose frontier lies in j UNION c) meeting the  *)
(* frontier of w in a PL arc meets j in the same arc.                       *)

let MOI_SFR_FREE_LIFT = prove
 (`!g c e w j:real^2->bool.
     moi_sfr_cplx g /\ c IN g /\ e IN g /\ ~(e = c) /\
     frontier(UNIONS g) = j /\
     w SUBSET UNIONS g /\ closed w /\ c SUBSET w /\ e SUBSET w /\
     frontier w SUBSET j UNION c /\
     pl_ball 1 (frontier e INTER frontier w)
     ==> frontier e INTER j = frontier e INTER frontier w`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `frontier e INTER j SUBSET frontier e INTER frontier (w:real^2->bool)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `interior w SUBSET interior(UNIONS g:real^2->bool)` MP_TAC THENL
     [MATCH_MP_TAC SUBSET_INTERIOR THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `frontier e SUBSET (e:real^2->bool)` MP_TAC THENL
     [ASM_MESON_TAC[MOI_SFR_POLYGON_FACTS; MOI_SFR_CPLX_CELL]; ALL_TAC] THEN
    UNDISCH_TAC `frontier(UNIONS g) = (j:real^2->bool)` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[frontier] THEN ASM_SIMP_TAC[CLOSURE_CLOSED] THEN
    UNDISCH_TAC `(e:real^2->bool) SUBSET w` THEN SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `h:real^1->real^2` STRIP_ASSUME_TAC o
    MATCH_MP MOI_PL2_PL_BALL_1_ARC) THEN
  MP_TAC(ISPECL [`g:(real^2->bool)->bool`; `e:real^2->bool`; `c:real^2->bool`]
    MOI_SFR_PAIR_INTERIOR) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^2->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `interior(e UNION c) SUBSET interior(w:real^2->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_INTERIOR THEN ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `path_image h DIFF k SUBSET (j:real^2->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `path_image h = frontier e INTER frontier (w:real^2->bool)` THEN
    DISCH_THEN SUBST1_TAC THEN
    SUBGOAL_THEN `frontier e SUBSET (e:real^2->bool)` MP_TAC THENL
     [ASM_MESON_TAC[MOI_SFR_POLYGON_FACTS; MOI_SFR_CPLX_CELL]; ALL_TAC] THEN
    MP_TAC(ISPEC `w:real^2->bool` INTERIOR_SUBSET) THEN
    UNDISCH_TAC `frontier w SUBSET (j:real^2->bool) UNION c` THEN
    UNDISCH_TAC `(e INTER c) DIFF k SUBSET interior(e UNION c:real^2->bool)` THEN
    UNDISCH_TAC `interior(e UNION c) SUBSET interior(w:real^2->bool)` THEN
    REWRITE_TAC[frontier] THEN ASM_SIMP_TAC[CLOSURE_CLOSED] THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`h:real^1->real^2`; `k:real^2->bool`] MOI_SFR_ARC_DENSE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `closure(path_image h DIFF k) SUBSET (j:real^2->bool)` MP_TAC THENL
   [MATCH_MP_TAC CLOSURE_MINIMAL THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `frontier(UNIONS g) = (j:real^2->bool)` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[FRONTIER_CLOSED];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `frontier e INTER frontier w SUBSET
               closure(frontier e INTER frontier w DIFF (k:real^2->bool))` THEN
  SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* 6. A cell outside g0 meeting the boundary j in infinitely many points.    *)
(* ------------------------------------------------------------------------- *)

let MOI_SFR_TWO_POINTS = prove
 (`!s:A->bool. INFINITE s ==> ?u w. u IN s /\ w IN s /\ ~(u = w)`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(s:A->bool = {})` MP_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN ASM_MESON_TAC[INFINITE; FINITE_EMPTY];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN DISCH_THEN(X_CHOOSE_TAC `u:A`) THEN
  SUBGOAL_THEN `~(s DELETE (u:A) = {})` MP_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `INFINITE(s:A->bool)` THEN REWRITE_TAC[INFINITE] THEN
    MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{u:A}` THEN
    REWRITE_TAC[FINITE_SING] THEN ASM SET_TAC[];
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_DELETE] THEN ASM_MESON_TAC[]]);;

let MOI_SFR_LOOP_NOT_SING = prove
 (`!gam:real^1->real^N. simple_path gam ==> ~(?a. path_image gam = {a})`,
  GEN_TAC THEN REWRITE_TAC[simple_path; path_image] THEN
  DISCH_THEN(MP_TAC o SPECL [`vec 0:real^1`; `lift(&1 / &2)`] o CONJUNCT2) THEN
  SUBGOAL_THEN `lift(&1 / &2) IN interval[vec 0,vec 1] /\
                ~(vec 0 = lift(&1 / &2)) /\ ~(vec 1 = lift(&1 / &2)) /\
                ~(vec 0 = vec 1:real^1)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[IN_INTERVAL_1; GSYM DROP_EQ; LIFT_DROP; DROP_VEC] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[ENDS_IN_UNIT_INTERVAL] THEN
  DISCH_TAC THEN DISCH_THEN(X_CHOOSE_TAC `a:real^N`) THEN
  UNDISCH_TAC `~((gam:real^1->real^N) (vec 0) = gam (lift(&1 / &2)))` THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN `(gam:real^1->real^N) (vec 0) IN {a} /\ gam (lift(&1 / &2)) IN {a}`
  MP_TAC THENL
   [UNDISCH_TAC `IMAGE (gam:real^1->real^N) (interval[vec 0,vec 1]) = {a}` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_SIMP_TAC[FUN_IN_IMAGE; ENDS_IN_UNIT_INTERVAL];
    REWRITE_TAC[IN_SING] THEN MESON_TAC[]]);;

let MOI_SFR_BOUNDARY_CELL = prove
 (`!(g:(real^2->bool)->bool) g0 j.
     moi_sfr_cplx g /\ pl_cell_with_boundary 2 (UNIONS g) j /\
     g0 SUBSET g /\ (g0 = {} \/ ?j0. pl_cell_with_boundary 2 (UNIONS g0) j0) /\
     ~(g0 = g)
     ==> ?c. c IN g /\ ~(c IN g0) /\ INFINITE(frontier c INTER j)`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_SFR_CELL_FACTS) THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `gam:real^1->real^2` STRIP_ASSUME_TAC) STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `FINITE(g:(real^2->bool)->bool) /\ FINITE(g0:(real^2->bool)->bool)`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[moi_sfr_cplx; FINITE_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `!e:real^2->bool. e IN g ==> polytope e /\ aff_dim e = &2`
  ASSUME_TAC THENL [ASM_MESON_TAC[MOI_SFR_CPLX_CELL]; ALL_TAC] THEN
  SUBGOAL_THEN `closed(UNIONS g0:real^2->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC CLOSED_UNIONS THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[SUBSET; POLYTOPE_IMP_CLOSED];
    ALL_TAC] THEN
  SUBGOAL_THEN `?e:real^2->bool. e IN g /\ ~(e IN g0)` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `?x:real^2. x IN j /\ ~(x IN UNIONS g0)` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
    DISCH_THEN(ASSUME_TAC o REWRITE_RULE[GSYM SUBSET] o
      REWRITE_RULE[NOT_EXISTS_THM; TAUT `~(p /\ ~q) <=> p ==> q`]) THEN
    FIRST_X_ASSUM(DISJ_CASES_THEN MP_TAC) THENL
     [DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `(j:real^2->bool) SUBSET UNIONS {}` THEN
      REWRITE_TAC[UNIONS_0; SUBSET_EMPTY] THEN
      UNDISCH_TAC `path_image(gam:real^1->real^2) = j` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[PATH_IMAGE_NONEMPTY];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `j0:real^2->bool` ASSUME_TAC) THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP MOI_SFR_CELL_FACTS) THEN
    DISCH_THEN(CONJUNCTS_THEN2
      (X_CHOOSE_THEN `gam0:real^1->real^2` STRIP_ASSUME_TAC) STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`gam0:real^1->real^2`; `j0:real^2->bool`] MOI_SFR_JORDAN_REGION) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `inside j SUBSET UNIONS g0 DIFF (j:real^2->bool)` ASSUME_TAC THENL
     [MATCH_MP_TAC INSIDE_SUBSET THEN EXISTS_TAC `outside(j0:real^2->bool)` THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(:real^2) DIFF outside j0 = j0 UNION inside j0` THEN
      UNDISCH_TAC `UNIONS g0 = (j0:real^2->bool) UNION inside j0` THEN
      UNDISCH_TAC `(j:real^2->bool) SUBSET UNIONS g0` THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(e:real^2->bool) SUBSET UNIONS g0` ASSUME_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `UNIONS g:real^2->bool` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC(SET_RULE `(e:A->bool) IN g ==> e SUBSET UNIONS g`) THEN
        ASM_REWRITE_TAC[];
        REWRITE_TAC[ASSUME `UNIONS g = (j:real^2->bool) UNION inside j`] THEN
        UNDISCH_TAC `inside j SUBSET UNIONS g0 DIFF (j:real^2->bool)` THEN
        UNDISCH_TAC `(j:real^2->bool) SUBSET UNIONS g0` THEN SET_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `~(interior(e:real^2->bool) = {})` MP_TAC THENL
     [ASM_MESON_TAC[MOI_SFR_POLYGON_FACTS]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_TAC `z:real^2` o REWRITE_RULE[GSYM MEMBER_NOT_EMPTY]) THEN
    SUBGOAL_THEN `(z:real^2) IN UNIONS g0` MP_TAC THENL
     [MP_TAC(ISPEC `e:real^2->bool` INTERIOR_SUBSET) THEN
      UNDISCH_TAC `(e:real^2->bool) SUBSET UNIONS g0` THEN
      UNDISCH_TAC `(z:real^2) IN interior e` THEN SET_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[IN_UNIONS] THEN
    DISCH_THEN(X_CHOOSE_THEN `e':real^2->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(e':real^2->bool) IN g /\ ~(e:real^2->bool = e')`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [UNDISCH_TAC `(g0:(real^2->bool)->bool) SUBSET g` THEN
        UNDISCH_TAC `(e':real^2->bool) IN g0` THEN SET_TAC[];
        UNDISCH_TAC `~((e:real^2->bool) IN g0)` THEN
        UNDISCH_TAC `(e':real^2->bool) IN g0` THEN MESON_TAC[]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`g:(real^2->bool)->bool`; `e:real^2->bool`; `e':real^2->bool`]
      MOI_SFR_CPLX_INTER) THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(z:real^2) IN interior e` THEN UNDISCH_TAC `(z:real^2) IN e'` THEN
    SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `(:real^2) DIFF UNIONS g0` OPEN_CONTAINS_BALL) THEN
  ASM_REWRITE_TAC[GSYM closed] THEN
  DISCH_THEN(MP_TAC o SPEC `x:real^2`) THEN ASM_REWRITE_TAC[IN_DIFF; IN_UNIV] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `INFINITE((j:real^2->bool) INTER ball(x,r))` ASSUME_TAC THENL
   [SUBGOAL_THEN `(x:real^2) limit_point_of j` MP_TAC THENL
     [MATCH_MP_TAC CONNECTED_IMP_PERFECT THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `path_image(gam:real^1->real^2) = j` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      ASM_SIMP_TAC[CONNECTED_PATH_IMAGE; SIMPLE_PATH_IMP_PATH; MOI_SFR_LOOP_NOT_SING];
      REWRITE_TAC[LIMPT_INFINITE_OPEN] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[OPEN_BALL; CENTRE_IN_BALL]];
    ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
  DISCH_THEN(ASSUME_TAC o REWRITE_RULE[INFINITE] o
    REWRITE_RULE[NOT_EXISTS_THM; TAUT `~(p /\ ~q /\ r) <=> p /\ ~q ==> ~r`]) THEN
  UNDISCH_TAC `INFINITE((j:real^2->bool) INTER ball(x,r))` THEN
  REWRITE_TAC[INFINITE] THEN
  MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `UNIONS (IMAGE (\c:real^2->bool. frontier c INTER j) (g DIFF g0))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[FINITE_UNIONS] THEN
    ASM_SIMP_TAC[FINITE_IMAGE; FINITE_DIFF; FORALL_IN_IMAGE; IN_DIFF];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET; IN_INTER; UNIONS_IMAGE; IN_ELIM_THM; IN_DIFF] THEN
  X_GEN_TAC `y:real^2` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(y:real^2) IN UNIONS g` MP_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[IN_UNIONS] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `c:real^2->bool` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `(y:real^2) IN UNIONS g0` MP_TAC THENL
     [ASM SET_TAC[]; ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `interior c SUBSET interior(UNIONS g:real^2->bool)` MP_TAC THENL
   [MATCH_MP_TAC SUBSET_INTERIOR THEN ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `closed(c:real^2->bool)` MP_TAC THENL
   [ASM_MESON_TAC[POLYTOPE_IMP_CLOSED]; ALL_TAC] THEN
  REWRITE_TAC[frontier] THEN SIMP_TAC[CLOSURE_CLOSED] THEN
  ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* 7. Counting helpers; a cell frontier is not inside j; the induction step  *)
(* on one piece of the split.                                                *)
(* ------------------------------------------------------------------------- *)

let MOI_SFR_TWO_CELLS = prove
 (`!s c:A. FINITE s /\ 2 <= CARD s /\ c IN s ==> ?e. e IN s /\ ~(e = c)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
  DISCH_THEN(ASSUME_TAC o REWRITE_RULE[NOT_EXISTS_THM; TAUT
    `~(p /\ ~q) <=> p ==> q`]) THEN
  SUBGOAL_THEN `CARD(s:A->bool) <= CARD {c:A}` MP_TAC THENL
   [MATCH_MP_TAC CARD_SUBSET THEN REWRITE_TAC[FINITE_SING] THEN ASM SET_TAC[];
    SIMP_TAC[CARD_SING] THEN ASM_ARITH_TAC]);;

let MOI_SFR_CARD2 = prove
 (`!s c e:A. FINITE s /\ c IN s /\ e IN s /\ ~(c = e) ==> 2 <= CARD s`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `CARD {c:A,e} <= CARD(s:A->bool)` MP_TAC THENL
   [MATCH_MP_TAC CARD_SUBSET THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ASM_SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY; IN_INSERT;
                 NOT_IN_EMPTY] THEN ARITH_TAC]);;

let MOI_SFR_NOT_FRONTIER_SUBSET = prove
 (`!(g:(real^2->bool)->bool) c j.
     moi_sfr_cplx g /\ 2 <= CARD g /\ c IN g /\
     pl_cell_with_boundary 2 (UNIONS g) j
     ==> ~(frontier c SUBSET j)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_SFR_CELL_FACTS) THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`g:(real^2->bool)->bool`; `c:real^2->bool`] MOI_SFR_TWO_CELLS) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[moi_sfr_cplx]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real^2->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `~(interior(c:real^2->bool) = {}) /\ ~(interior(e:real^2->bool) = {})`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_SFR_POLYGON_FACTS; MOI_SFR_CPLX_CELL]; ALL_TAC] THEN
  SUBGOAL_THEN `interior c SUBSET inside(j:real^2->bool) /\
                interior e SUBSET inside(j:real^2->bool)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `interior(UNIONS g) = inside(j:real^2->bool)` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN CONJ_TAC THEN
    MATCH_MP_TAC SUBSET_INTERIOR THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`g:(real^2->bool)->bool`; `e:real^2->bool`; `c:real^2->bool`]
    MOI_SFR_CPLX_INTER) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`inside(j:real^2->bool)`; `c:real^2->bool`]
    CONNECTED_INTER_FRONTIER) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `c:real^2->bool` INTERIOR_SUBSET) THEN
  MP_TAC(ISPEC `e:real^2->bool` INTERIOR_SUBSET) THEN
  UNDISCH_TAC `~(interior(c:real^2->bool) = {})` THEN
  UNDISCH_TAC `~(interior(e:real^2->bool) = {})` THEN
  UNDISCH_TAC `interior e INTER (c:real^2->bool) = {}` THEN
  UNDISCH_TAC `interior c SUBSET inside(j:real^2->bool)` THEN
  UNDISCH_TAC `interior e SUBSET inside(j:real^2->bool)` THEN
  UNDISCH_TAC `inside j INTER (j:real^2->bool) = {}` THEN
  UNDISCH_TAC `frontier c SUBSET (j:real^2->bool)` THEN
  SET_TAC[]);;

(* The induction step on one piece w of the split: the cells inside w form *)
(* a smaller decomposition of the PL 2-cell w with at least two cells; the *)
(* induction hypothesis with g0 = {c} gives a free cell of w other than c, *)
(* which is free in g by MOI_SFR_FREE_LIFT.                                 *)

let MOI_SFR_PIECE = prove
 (`!(g:(real^2->bool)->bool) c w j.
     (!g' g0' j'. CARD g' < CARD g /\ moi_sfr_cplx g' /\ 2 <= CARD g' /\
                  pl_cell_with_boundary 2 (UNIONS g') j' /\ g0' SUBSET g' /\
                  (g0' = {} \/ ?j0. pl_cell_with_boundary 2 (UNIONS g0') j0) /\
                  ~(g0' = g')
                  ==> ?c'. c' IN g' /\ ~(c' IN g0') /\
                           pl_ball 1 (frontier c' INTER j')) /\
     moi_sfr_cplx g /\ c IN g /\ frontier(UNIONS g) = j /\
     w SUBSET UNIONS g /\ closed w /\ c SUBSET w /\
     (!e. e IN g ==> e SUBSET w \/ e INTER w SUBSET c) /\
     pl_cell_with_boundary 2 w (frontier w) /\
     frontier w SUBSET j UNION c /\
     (?e. e IN g /\ ~(e SUBSET w)) /\ (?e. e IN g /\ e SUBSET w /\ ~(e = c))
     ==> ?e. e IN g /\ e SUBSET w /\ ~(e = c) /\ pl_ball 1 (frontier e INTER j)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih")
    (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
  SUBGOAL_THEN `FINITE(g:(real^2->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[moi_sfr_cplx]; ALL_TAC] THEN
  ABBREV_TAC `gw = {e:real^2->bool | e IN g /\ e SUBSET w}` THEN
  SUBGOAL_THEN `(gw:(real^2->bool)->bool) SUBSET g` ASSUME_TAC THENL
   [EXPAND_TAC "gw" THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!e:real^2->bool. e IN gw <=> e IN g /\ e SUBSET w`
  ASSUME_TAC THENL
   [EXPAND_TAC "gw" THEN REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `FINITE(gw:(real^2->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[FINITE_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `UNIONS gw = w:real^2->bool` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:real^2) IN UNIONS g` MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_UNIONS] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real^2->bool` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(DISJ_CASES_TAC o C MATCH_MP (ASSUME `(e:real^2->bool) IN g`)) THENL
     [EXISTS_TAC `e:real^2->bool` THEN ASM_REWRITE_TAC[];
      EXISTS_TAC `c:real^2->bool` THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(c:real^2->bool) IN gw` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `e2:real^2->bool` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `e1:real^2->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `CARD(gw:(real^2->bool)->bool) < CARD(g:(real^2->bool)->bool)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CARD_PSUBSET THEN ASM_REWRITE_TAC[PSUBSET] THEN
    DISCH_TAC THEN
    UNDISCH_TAC `!e:real^2->bool. e IN gw <=> e IN g /\ e SUBSET w` THEN
    DISCH_THEN(MP_TAC o SPEC `e1:real^2->bool`) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `2 <= CARD(gw:(real^2->bool)->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_SFR_CARD2 THEN
    MAP_EVERY EXISTS_TAC [`c:real^2->bool`; `e2:real^2->bool`] THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  REMOVE_THEN "ih" (MP_TAC o SPECL
    [`gw:(real^2->bool)->bool`; `{c:real^2->bool}`; `frontier w:real^2->bool`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[MOI_SFR_CPLX_SUBSET];
      ASM SET_TAC[];
      DISJ2_TAC THEN EXISTS_TAC `frontier c:real^2->bool` THEN
      REWRITE_TAC[UNIONS_1] THEN
      ASM_MESON_TAC[MOI_SFR_POLYGON_CELL; MOI_SFR_CPLX_CELL];
      DISCH_TAC THEN
      SUBGOAL_THEN `(e2:real^2->bool) IN {c}` MP_TAC THENL
       [ASM_REWRITE_TAC[]; REWRITE_TAC[IN_SING] THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  REWRITE_TAC[IN_SING] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real^2->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `e:real^2->bool` THEN
  SUBGOAL_THEN `(e:real^2->bool) IN g /\ e SUBSET w` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`g:(real^2->bool)->bool`; `c:real^2->bool`; `e:real^2->bool`;
                 `w:real^2->bool`; `j:real^2->bool`] MOI_SFR_FREE_LIFT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* 8. The split step: every cell, and the 2-cell UNIONS g0, lies on one     *)
(* side of a crosscut in the frontier of a cell c; then one of the pieces  *)
(* u (the side containing c) or c UNION v yields a free cell outside g0.    *)
(* ------------------------------------------------------------------------- *)

let MOI_SFR_INTERIOR_MISS = prove
 (`!u v b:real^N->bool.
     u INTER v = b /\ b SUBSET frontier v ==> interior v INTER u = {}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[frontier] THEN
  MP_TAC(ISPEC `v:real^N->bool` INTERIOR_SUBSET) THEN SET_TAC[]);;

let MOI_SFR_CELLS_SIDE = prove
 (`!(g:(real^2->bool)->bool) c b u v d.
     moi_sfr_cplx g /\ c IN g /\ UNIONS g = d /\ b SUBSET frontier c /\
     closed u /\ closed v /\
     (!s. connected s /\ s SUBSET d /\ s INTER b = {}
          ==> s SUBSET u \/ s SUBSET v)
     ==> !e. e IN g ==> e SUBSET u \/ e SUBSET v`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  X_GEN_TAC `e:real^2->bool` THEN DISCH_TAC THEN
  SUBGOAL_THEN `polytope (e:real^2->bool) /\ aff_dim e = &2` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_SFR_CPLX_CELL THEN EXISTS_TAC `g:(real^2->bool)->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SFR_POLYGON_FACTS) THEN
  SUBGOAL_THEN `interior e SUBSET u \/ interior (e:real^2->bool) SUBSET v`
  MP_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (is_forall o concl)) THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONVEX_CONNECTED THEN MATCH_MP_TAC CONVEX_INTERIOR THEN
      ASM_REWRITE_TAC[];
      UNDISCH_TAC `UNIONS g = (d:real^2->bool)` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      UNDISCH_TAC `interior e SUBSET (e:real^2->bool)` THEN
      UNDISCH_TAC `(e:real^2->bool) IN g` THEN SET_TAC[];
      ASM_CASES_TAC `e:real^2->bool = c` THENL
       [FIRST_X_ASSUM SUBST_ALL_TAC THEN
        UNDISCH_TAC `b SUBSET frontier(c:real^2->bool)` THEN
        UNDISCH_TAC `frontier c INTER interior(c:real^2->bool) = {}` THEN
        SET_TAC[];
        MP_TAC(ISPECL [`g:(real^2->bool)->bool`; `e:real^2->bool`; `c:real^2->bool`]
          MOI_SFR_CPLX_INTER) THEN
        ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
        MP_TAC(ISPEC `c:real^2->bool` MOI_SFR_POLYGON_FACTS) THEN
        ANTS_TAC THENL
         [MATCH_MP_TAC MOI_SFR_CPLX_CELL THEN
          EXISTS_TAC `g:(real^2->bool)->bool` THEN ASM_REWRITE_TAC[];
          STRIP_TAC] THEN
        UNDISCH_TAC `b SUBSET frontier(c:real^2->bool)` THEN
        UNDISCH_TAC `frontier c SUBSET (c:real^2->bool)` THEN
        UNDISCH_TAC `interior e INTER (c:real^2->bool) = {}` THEN
        SET_TAC[]]];
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `closure(interior e) SUBSET u \/
                closure(interior (e:real^2->bool)) SUBSET v`
  MP_TAC THENL
   [FIRST_X_ASSUM DISJ_CASES_TAC THENL [DISJ1_TAC; DISJ2_TAC] THEN
    MATCH_MP_TAC CLOSURE_MINIMAL THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[]]);;

let MOI_SFR_G0_SIDE = prove
 (`!(g:(real^2->bool)->bool) g0 c b u v d j0.
     moi_sfr_cplx g /\ c IN g /\ ~(c IN g0) /\ g0 SUBSET g /\ UNIONS g = d /\
     b SUBSET frontier c /\ closed u /\ closed v /\
     (!s. connected s /\ s SUBSET d /\ s INTER b = {}
          ==> s SUBSET u \/ s SUBSET v) /\
     pl_cell_with_boundary 2 (UNIONS g0) j0
     ==> UNIONS g0 SUBSET u \/ UNIONS g0 SUBSET v`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_SFR_CELL_FACTS) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `polytope (c:real^2->bool) /\ aff_dim c = &2` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_SFR_CPLX_CELL THEN EXISTS_TAC `g:(real^2->bool)->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SFR_POLYGON_FACTS) THEN
  SUBGOAL_THEN `open(inside(j0:real^2->bool))` ASSUME_TAC THENL
   [UNDISCH_TAC `interior(UNIONS g0) = inside(j0:real^2->bool)` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[OPEN_INTERIOR];
    ALL_TAC] THEN
  SUBGOAL_THEN `inside j0 INTER (c:real^2->bool) = {}` ASSUME_TAC THENL
   [UNDISCH_TAC `closure(interior c) = (c:real^2->bool)` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    ASM_SIMP_TAC[OPEN_INTER_CLOSURE_EQ_EMPTY] THEN
    REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
    X_GEN_TAC `y:real^2` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(y:real^2) IN UNIONS g0` MP_TAC THENL
     [UNDISCH_TAC `UNIONS g0 = (j0:real^2->bool) UNION inside j0` THEN
      DISCH_THEN SUBST1_TAC THEN
      UNDISCH_TAC `(y:real^2) IN inside j0` THEN SET_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[IN_UNIONS] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real^2->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(e:real^2->bool) IN g /\ ~(c:real^2->bool = e)`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [UNDISCH_TAC `(g0:(real^2->bool)->bool) SUBSET g` THEN
        UNDISCH_TAC `(e:real^2->bool) IN g0` THEN SET_TAC[];
        UNDISCH_TAC `~((c:real^2->bool) IN g0)` THEN
        UNDISCH_TAC `(e:real^2->bool) IN g0` THEN MESON_TAC[]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`g:(real^2->bool)->bool`; `c:real^2->bool`; `e:real^2->bool`]
      MOI_SFR_CPLX_INTER) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(y:real^2) IN interior c` THEN UNDISCH_TAC `(y:real^2) IN e` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `inside j0 SUBSET u \/ inside (j0:real^2->bool) SUBSET v`
  MP_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (is_forall o concl)) THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [UNDISCH_TAC `UNIONS g = (d:real^2->bool)` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      UNDISCH_TAC `UNIONS g0 = (j0:real^2->bool) UNION inside j0` THEN
      UNDISCH_TAC `(g0:(real^2->bool)->bool) SUBSET g` THEN SET_TAC[];
      UNDISCH_TAC `b SUBSET frontier(c:real^2->bool)` THEN
      UNDISCH_TAC `frontier c SUBSET (c:real^2->bool)` THEN
      UNDISCH_TAC `inside j0 INTER (c:real^2->bool) = {}` THEN SET_TAC[]];
    ALL_TAC] THEN
  UNDISCH_TAC `closure(inside j0) = UNIONS(g0:(real^2->bool)->bool)` THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  STRIP_TAC THENL [DISJ1_TAC; DISJ2_TAC] THEN
  MATCH_MP_TAC CLOSURE_MINIMAL THEN ASM_REWRITE_TAC[]);;

(* The split step, with the crosscut b in the frontier of c, the boundary   *)
(* j = a1 UNION a2 split at the ends of b, and c on the side u.  If g0      *)
(* lies in v (or is empty) the piece u gives the free cell; otherwise g0    *)
(* lies in u and the piece c UNION v gives it.                               *)

let MOI_SFR_SPLIT_CASE = prove
 (`!(g:(real^2->bool)->bool) g0 j c (a1:real^1->real^2) a2 b u v.
     (!g' g0' j'. CARD g' < CARD g /\ moi_sfr_cplx g' /\ 2 <= CARD g' /\
                  pl_cell_with_boundary 2 (UNIONS g') j' /\ g0' SUBSET g' /\
                  (g0' = {} \/ ?j0. pl_cell_with_boundary 2 (UNIONS g0') j0) /\
                  ~(g0' = g')
                  ==> ?c'. c' IN g' /\ ~(c' IN g0') /\
                           pl_ball 1 (frontier c' INTER j')) /\
     moi_sfr_cplx g /\ frontier(UNIONS g) = j /\ UNIONS g = j UNION inside j /\
     c IN g /\ ~(c IN g0) /\ g0 SUBSET g /\
     (g0 = {} \/ ?j0. pl_cell_with_boundary 2 (UNIONS g0) j0) /\
     ~pl_ball 1 (frontier c INTER j) /\
     arc a1 /\ pl_map_on (interval[vec 0,vec 1]) a1 /\
     arc a2 /\ pl_map_on (interval[vec 0,vec 1]) a2 /\
     arc b /\ pl_map_on (interval[vec 0,vec 1]) b /\
     pathstart a2 = pathstart a1 /\ pathfinish a2 = pathfinish a1 /\
     pathstart b = pathstart a1 /\ pathfinish b = pathfinish a1 /\
     path_image a1 INTER path_image a2 = {pathstart a1,pathfinish a1} /\
     path_image a1 UNION path_image a2 = j /\
     path_image b INTER j = {pathstart a1,pathfinish a1} /\
     path_image b SUBSET frontier c /\
     (path_image a1 UNION path_image b) UNION
       inside(path_image a1 UNION path_image b) = u /\
     (path_image a2 UNION path_image b) UNION
       inside(path_image a2 UNION path_image b) = v /\
     c SUBSET u
     ==> ?c'. c' IN g /\ ~(c' IN g0) /\ pl_ball 1 (frontier c' INTER j)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih")
    (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
  SUBGOAL_THEN `polytope (c:real^2->bool) /\ aff_dim c = &2` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_SFR_CPLX_CELL THEN EXISTS_TAC `g:(real^2->bool)->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SFR_POLYGON_FACTS) THEN
  SUBGOAL_THEN `pl_ball 2 (c:real^2->bool)` ASSUME_TAC THENL
   [MP_TAC(ISPEC `c:real^2->bool` MOI_SFR_POLYGON_CELL) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `path_image b SUBSET (j:real^2->bool) UNION inside j` ASSUME_TAC THENL
   [UNDISCH_TAC `UNIONS g = (j:real^2->bool) UNION inside j` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    UNDISCH_TAC `path_image b SUBSET frontier(c:real^2->bool)` THEN
    UNDISCH_TAC `frontier c SUBSET (c:real^2->bool)` THEN
    UNDISCH_TAC `(c:real^2->bool) IN g` THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`a1:real^1->real^2`; `a2:real^1->real^2`; `b:real^1->real^2`;
                 `j:real^2->bool`; `u:real^2->bool`; `v:real^2->bool`]
    MOI_SFR_THETA) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `closed(u:real^2->bool) /\ closed(v:real^2->bool)`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[COMPACT_IMP_CLOSED]; ALL_TAC] THEN
  SUBGOAL_THEN `!e:real^2->bool. e IN g ==> e SUBSET u \/ e SUBSET v`
  (LABEL_TAC "cside") THENL
   [MATCH_MP_TAC MOI_SFR_CELLS_SIDE THEN
    MAP_EVERY EXISTS_TAC [`c:real^2->bool`; `path_image(b:real^1->real^2)`;
                          `(j:real^2->bool) UNION inside j`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `g0 = {} \/ UNIONS g0 SUBSET v \/
                UNIONS (g0:(real^2->bool)->bool) SUBSET u`
  ASSUME_TAC THENL
   [ASM_CASES_TAC `g0:(real^2->bool)->bool = {}` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `g0 = {} \/ ?j0. pl_cell_with_boundary 2 (UNIONS g0) (j0:real^2->bool)` THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `j0:real^2->bool`) THEN
    MP_TAC(ISPECL [`g:(real^2->bool)->bool`; `g0:(real^2->bool)->bool`;
                   `c:real^2->bool`; `path_image(b:real^1->real^2)`;
                   `u:real^2->bool`; `v:real^2->bool`;
                   `(j:real^2->bool) UNION inside j`; `j0:real^2->bool`]
      MOI_SFR_G0_SIDE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `interior v INTER (u:real^2->bool) = {} /\
                interior u INTER (v:real^2->bool) = {}`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC MOI_SFR_INTERIOR_MISS THEN
    EXISTS_TAC `path_image(b:real^1->real^2)` THENL
     [ASM_REWRITE_TAC[] THEN SET_TAC[];
      ONCE_REWRITE_TAC[INTER_COMM] THEN ASM_REWRITE_TAC[] THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(u:real^2->bool) SUBSET UNIONS g /\ v SUBSET UNIONS g`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[ASSUME `UNIONS g = (j:real^2->bool) UNION inside j`] THEN
    UNDISCH_TAC `u UNION v = (j:real^2->bool) UNION inside j` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?e1:real^2->bool. e1 IN g /\ e1 SUBSET v /\ ~(e1 SUBSET u) /\ ~(e1 = c)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `~(interior v = {}:real^2->bool)` THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    DISCH_THEN(X_CHOOSE_TAC `z:real^2`) THEN
    SUBGOAL_THEN `(z:real^2) IN UNIONS g` MP_TAC THENL
     [MP_TAC(ISPEC `v:real^2->bool` INTERIOR_SUBSET) THEN
      UNDISCH_TAC `(v:real^2->bool) SUBSET UNIONS g` THEN
      UNDISCH_TAC `(z:real^2) IN interior v` THEN SET_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[IN_UNIONS] THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC `e:real^2->bool` THEN STRIP_TAC THEN
    SUBGOAL_THEN `~((e:real^2->bool) SUBSET u)` ASSUME_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC `interior v INTER (u:real^2->bool) = {}` THEN
      UNDISCH_TAC `(z:real^2) IN interior v` THEN
      UNDISCH_TAC `(z:real^2) IN e` THEN
      UNDISCH_TAC `(e:real^2->bool) SUBSET u` THEN SET_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [USE_THEN "cside" (MP_TAC o C MATCH_MP (ASSUME `(e:real^2->bool) IN g`)) THEN
      ASM_REWRITE_TAC[];
      DISCH_TAC THEN UNDISCH_TAC `~((e:real^2->bool) SUBSET u)` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(u = c:real^2->bool)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    UNDISCH_TAC `~pl_ball 1 (frontier c INTER (j:real^2->bool))` THEN
    REWRITE_TAC[] THEN
    SUBGOAL_THEN `frontier c = path_image a1 UNION path_image(b:real^1->real^2)`
    SUBST1_TAC THENL
     [UNDISCH_TAC `frontier u = path_image a1 UNION path_image(b:real^1->real^2)` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `(path_image a1 UNION path_image b) INTER (j:real^2->bool) =
      path_image(a1:real^1->real^2)`
    SUBST1_TAC THENL
     [MP_TAC(ISPEC `a1:real^1->real^2` PATHSTART_IN_PATH_IMAGE) THEN
      MP_TAC(ISPEC `a1:real^1->real^2` PATHFINISH_IN_PATH_IMAGE) THEN
      UNDISCH_TAC `path_image a1 UNION path_image a2 = (j:real^2->bool)` THEN
      UNDISCH_TAC `path_image b INTER j =
                   {pathstart a1,pathfinish(a1:real^1->real^2)}` THEN
      SET_TAC[];
      MATCH_MP_TAC MOI_SFR_ARC_PL_BALL THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?e2:real^2->bool. e2 IN g /\ e2 SUBSET u /\ ~(e2 = c) /\ ~(e2 SUBSET c UNION v)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `?z:real^2. z IN interior u /\ ~(z IN c)` STRIP_ASSUME_TAC THENL
     [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
      DISCH_THEN(ASSUME_TAC o REWRITE_RULE[NOT_EXISTS_THM;
        TAUT `~(p /\ ~q) <=> p ==> q`]) THEN
      UNDISCH_TAC `~(u = c:real^2->bool)` THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC SUBSET_ANTISYM THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `closure(interior u) = (u:real^2->bool)` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      MATCH_MP_TAC CLOSURE_MINIMAL THEN ASM_REWRITE_TAC[SUBSET];
      ALL_TAC] THEN
    SUBGOAL_THEN `(z:real^2) IN UNIONS g` MP_TAC THENL
     [MP_TAC(ISPEC `u:real^2->bool` INTERIOR_SUBSET) THEN
      UNDISCH_TAC `(u:real^2->bool) SUBSET UNIONS g` THEN
      UNDISCH_TAC `(z:real^2) IN interior u` THEN SET_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[IN_UNIONS] THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC `e:real^2->bool` THEN STRIP_TAC THEN
    SUBGOAL_THEN `~((z:real^2) IN v)` ASSUME_TAC THENL
     [UNDISCH_TAC `interior u INTER (v:real^2->bool) = {}` THEN
      UNDISCH_TAC `(z:real^2) IN interior u` THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(e:real^2->bool) SUBSET u` ASSUME_TAC THENL
     [USE_THEN "cside" (MP_TAC o C MATCH_MP (ASSUME `(e:real^2->bool) IN g`)) THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(z:real^2) IN e` THEN UNDISCH_TAC `~((z:real^2) IN v)` THEN
      SET_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC `~((z:real^2) IN c)` THEN
      UNDISCH_TAC `(z:real^2) IN e` THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `~((z:real^2) IN c)` THEN UNDISCH_TAC `~((z:real^2) IN v)` THEN
      UNDISCH_TAC `(z:real^2) IN e` THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `path_image b SUBSET (c:real^2->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `path_image b SUBSET frontier(c:real^2->bool)` THEN
    UNDISCH_TAC `frontier c SUBSET (c:real^2->bool)` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!e:real^2->bool. e IN g /\ ~(e = c) ==> ~(e SUBSET c)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`g:(real^2->bool)->bool`; `e:real^2->bool`; `c:real^2->bool`]
      MOI_SFR_CPLX_INTER) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o REWRITE_RULE[DISJ_ASSOC] o check (fun th ->
    is_disj(concl th) && can (find_term ((=) `v:real^2->bool`)) (concl th))) THENL
   [SUBGOAL_THEN `!e:real^2->bool. e IN g0 ==> e SUBSET v` (LABEL_TAC "g0v") THENL
     [X_GEN_TAC `e:real^2->bool` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
       [UNDISCH_TAC `(e:real^2->bool) IN g0` THEN ASM_REWRITE_TAC[NOT_IN_EMPTY];
        UNDISCH_TAC `UNIONS g0 SUBSET (v:real^2->bool)` THEN
        UNDISCH_TAC `(e:real^2->bool) IN g0` THEN SET_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `!e:real^2->bool. e IN g ==> e SUBSET u \/ e INTER u SUBSET c`
    ASSUME_TAC THENL
     [X_GEN_TAC `e:real^2->bool` THEN DISCH_TAC THEN
      USE_THEN "cside" (MP_TAC o C MATCH_MP (ASSUME `(e:real^2->bool) IN g`)) THEN
      UNDISCH_TAC `u INTER v = path_image(b:real^1->real^2)` THEN
      UNDISCH_TAC `path_image b SUBSET (c:real^2->bool)` THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `pl_cell_with_boundary 2 u (frontier u:real^2->bool)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `frontier u SUBSET (j:real^2->bool) UNION c` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `path_image a1 UNION path_image a2 = (j:real^2->bool)` THEN
      UNDISCH_TAC `path_image b SUBSET (c:real^2->bool)` THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `?e:real^2->bool. e IN g /\ ~(e SUBSET u)` ASSUME_TAC THENL
     [EXISTS_TAC `e1:real^2->bool` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `?e:real^2->bool. e IN g /\ e SUBSET u /\ ~(e = c)` ASSUME_TAC THENL
     [EXISTS_TAC `e2:real^2->bool` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`g:(real^2->bool)->bool`; `c:real^2->bool`; `u:real^2->bool`;
                   `j:real^2->bool`] MOI_SFR_PIECE) THEN
    ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real^2->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `e:real^2->bool` THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    USE_THEN "g0v" (MP_TAC o C MATCH_MP (ASSUME `(e:real^2->bool) IN g0`)) THEN
    SUBGOAL_THEN `~((e:real^2->bool) SUBSET c)` MP_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (term_match [] `!e:real^2->bool. e IN g /\ ~(e = c) ==> ~(e SUBSET c)`)
            (concl th))) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `(e:real^2->bool) SUBSET u` THEN
    UNDISCH_TAC `u INTER v = path_image(b:real^1->real^2)` THEN
    UNDISCH_TAC `path_image b SUBSET (c:real^2->bool)` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!e:real^2->bool. e IN g0 ==> e SUBSET u` (LABEL_TAC "g0u") THENL
   [X_GEN_TAC `e:real^2->bool` THEN DISCH_TAC THEN
    UNDISCH_TAC `UNIONS g0 SUBSET (u:real^2->bool)` THEN
    UNDISCH_TAC `(e:real^2->bool) IN g0` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(c:real^2->bool) INTER v = path_image b` ASSUME_TAC THENL
   [UNDISCH_TAC `u INTER v = path_image(b:real^1->real^2)` THEN
    UNDISCH_TAC `path_image b SUBSET (c:real^2->bool)` THEN
    UNDISCH_TAC `(c:real^2->bool) SUBSET u` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_ball 2 (c UNION v:real^2->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC PL_BALL_2_UNION THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL [`v:real^2->bool`;
                     `path_image a2 UNION path_image(b:real^1->real^2)`]
        MOI_SFR_CELL_BALL) THEN ASM_SIMP_TAC[];
      MATCH_MP_TAC MOI_SFR_ARC_PL_BALL THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[SUBSET_INTER] THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!e:real^2->bool. e IN g ==> e SUBSET c UNION v \/
                                   e INTER (c UNION v) SUBSET c`
  ASSUME_TAC THENL
   [X_GEN_TAC `e:real^2->bool` THEN DISCH_TAC THEN
    USE_THEN "cside" (MP_TAC o C MATCH_MP (ASSUME `(e:real^2->bool) IN g`)) THEN
    UNDISCH_TAC `u INTER v = path_image(b:real^1->real^2)` THEN
    UNDISCH_TAC `path_image b SUBSET (c:real^2->bool)` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_cell_with_boundary 2 (c UNION v)
                  (frontier(c UNION v):real^2->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_SFR_PL_BALL_CELL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `frontier(c UNION v) SUBSET (j:real^2->bool) UNION c` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`c:real^2->bool`; `v:real^2->bool`] FRONTIER_UNION_SUBSET) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `path_image a1 UNION path_image a2 = (j:real^2->bool)` THEN
    UNDISCH_TAC `path_image b SUBSET (c:real^2->bool)` THEN
    UNDISCH_TAC `frontier c SUBSET (c:real^2->bool)` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `c UNION v SUBSET UNIONS(g:(real^2->bool)->bool) /\
                closed(c UNION v:real^2->bool) /\ c SUBSET c UNION v`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `(v:real^2->bool) SUBSET UNIONS g` THEN
      UNDISCH_TAC `(c:real^2->bool) IN g` THEN SET_TAC[];
      MATCH_MP_TAC CLOSED_UNION THEN ASM_REWRITE_TAC[];
      SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `?e:real^2->bool. e IN g /\ ~(e SUBSET c UNION v)` ASSUME_TAC THENL
   [EXISTS_TAC `e2:real^2->bool` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `?e:real^2->bool. e IN g /\ e SUBSET c UNION v /\ ~(e = c)`
  ASSUME_TAC THENL
   [EXISTS_TAC `e1:real^2->bool` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(e1:real^2->bool) SUBSET v` THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`g:(real^2->bool)->bool`; `c:real^2->bool`; `c UNION v:real^2->bool`;
                 `j:real^2->bool`] MOI_SFR_PIECE) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real^2->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `e:real^2->bool` THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  USE_THEN "g0u" (MP_TAC o C MATCH_MP (ASSUME `(e:real^2->bool) IN g0`)) THEN
  SUBGOAL_THEN `~((e:real^2->bool) SUBSET c)` MP_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (term_match [] `!e:real^2->bool. e IN g /\ ~(e = c) ==> ~(e SUBSET c)`)
          (concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `(e:real^2->bool) SUBSET c UNION v` THEN
  UNDISCH_TAC `u INTER v = path_image(b:real^1->real^2)` THEN
  UNDISCH_TAC `path_image b SUBSET (c:real^2->bool)` THEN SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* 9. The induction: existence of a free cell outside g0.                    *)
(* ------------------------------------------------------------------------- *)

(* A cell c outside g0 meeting j in infinitely many points but not in an    *)
(* arc: a crosscut b of the disk in the frontier of c (MOI_SFR_CROSSCUT),   *)
(* the split of j at its ends, the theta split, and MOI_SFR_SPLIT_CASE on   *)
(* the side containing c.                                                    *)

let MOI_SFR_SPLIT_STEP = prove
 (`!(g:(real^2->bool)->bool) g0 j c.
     (!g' g0' j'. CARD g' < CARD g /\ moi_sfr_cplx g' /\ 2 <= CARD g' /\
                  pl_cell_with_boundary 2 (UNIONS g') j' /\ g0' SUBSET g' /\
                  (g0' = {} \/ ?j0. pl_cell_with_boundary 2 (UNIONS g0') j0) /\
                  ~(g0' = g')
                  ==> ?c'. c' IN g' /\ ~(c' IN g0') /\
                           pl_ball 1 (frontier c' INTER j')) /\
     moi_sfr_cplx g /\ 2 <= CARD g /\ pl_cell_with_boundary 2 (UNIONS g) j /\
     c IN g /\ ~(c IN g0) /\ g0 SUBSET g /\
     (g0 = {} \/ ?j0. pl_cell_with_boundary 2 (UNIONS g0) j0) /\
     INFINITE(frontier c INTER j) /\ ~pl_ball 1 (frontier c INTER j)
     ==> ?c'. c' IN g /\ ~(c' IN g0) /\ pl_ball 1 (frontier c' INTER j)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih")
    (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_SFR_CELL_FACTS) THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `gam:real^1->real^2` STRIP_ASSUME_TAC) STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `polytope (c:real^2->bool) /\ aff_dim c = &2` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_SFR_CPLX_CELL THEN EXISTS_TAC `g:(real^2->bool)->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SFR_POLYGON_FACTS) THEN
  MP_TAC(ISPECL [`c:real^2->bool`; `frontier c:real^2->bool`] MOI_SFR_CELL_FACTS) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[MOI_SFR_POLYGON_CELL]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `gamc:real^1->real^2` STRIP_ASSUME_TAC o CONJUNCT1) THEN
  SUBGOAL_THEN `?y:real^2. y IN frontier c /\ ~(y IN j)` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`g:(real^2->bool)->bool`; `c:real^2->bool`; `j:real^2->bool`]
      MOI_SFR_NOT_FRONTIER_SUBSET) THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(X_CHOOSE_THEN `u0:real^2` (X_CHOOSE_THEN `w0:real^2`
    STRIP_ASSUME_TAC) o MATCH_MP MOI_SFR_TWO_POINTS) THEN
  MP_TAC(ISPECL [`gamc:real^1->real^2`; `j:real^2->bool`; `u0:real^2`; `w0:real^2`;
                 `y:real^2`] MOI_SFR_CROSSCUT) THEN
  SUBGOAL_THEN `closed(j:real^2->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `frontier(UNIONS g) = (j:real^2->bool)` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[FRONTIER_CLOSED];
    ALL_TAC] THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(u0:real^2) IN frontier c INTER j` THEN
    UNDISCH_TAC `(w0:real^2) IN frontier c INTER j` THEN SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `b:real^1->real^2` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `path_image b SUBSET frontier(c:real^2->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `path_image b SUBSET path_image(gamc:real^1->real^2)` THEN
    REWRITE_TAC[ASSUME `path_image gamc = frontier(c:real^2->bool)`];
    ALL_TAC] THEN
  SUBGOAL_THEN `pathstart(b:real^1->real^2) IN path_image gam /\
                pathfinish b IN path_image gam /\ ~(pathstart b = pathfinish b)`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `path_image b INTER j =
                   {pathstart b,pathfinish(b:real^1->real^2)}` THEN SET_TAC[];
      UNDISCH_TAC `path_image b INTER j =
                   {pathstart b,pathfinish(b:real^1->real^2)}` THEN SET_TAC[];
      MP_TAC(ISPEC `b:real^1->real^2` ARC_DISTINCT_ENDS) THEN
      ASM_REWRITE_TAC[] THEN MESON_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`gam:real^1->real^2`; `pathstart(b:real^1->real^2)`;
                 `pathfinish(b:real^1->real^2)`] MOI_SFR_LOOP_SPLIT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `a1:real^1->real^2` (X_CHOOSE_THEN `a2:real^1->real^2`
    STRIP_ASSUME_TAC)) THEN
  ABBREV_TAC `u = (path_image a1 UNION path_image b) UNION
                  inside(path_image a1 UNION path_image(b:real^1->real^2))` THEN
  ABBREV_TAC `v = (path_image a2 UNION path_image b) UNION
                  inside(path_image a2 UNION path_image(b:real^1->real^2))` THEN
  SUBGOAL_THEN `path_image b SUBSET (j:real^2->bool) UNION inside j` ASSUME_TAC THENL
   [UNDISCH_TAC `UNIONS g = (j:real^2->bool) UNION inside j` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    UNDISCH_TAC `path_image b SUBSET frontier(c:real^2->bool)` THEN
    UNDISCH_TAC `frontier c SUBSET (c:real^2->bool)` THEN
    UNDISCH_TAC `(c:real^2->bool) IN g` THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`a1:real^1->real^2`; `a2:real^1->real^2`; `b:real^1->real^2`;
                 `j:real^2->bool`; `u:real^2->bool`; `v:real^2->bool`]
    MOI_SFR_THETA) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `(c:real^2->bool) SUBSET u \/ c SUBSET v` MP_TAC THENL
   [SUBGOAL_THEN `interior c SUBSET u \/ interior(c:real^2->bool) SUBSET v`
    MP_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        is_forall(concl th) &&
        can (find_term ((=) `connected:(real^2->bool)->bool`)) (concl th))) THEN
      REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC CONVEX_CONNECTED THEN MATCH_MP_TAC CONVEX_INTERIOR THEN
        ASM_REWRITE_TAC[];
        UNDISCH_TAC `UNIONS g = (j:real^2->bool) UNION inside j` THEN
        DISCH_THEN(SUBST1_TAC o SYM) THEN
        UNDISCH_TAC `interior c SUBSET (c:real^2->bool)` THEN
        UNDISCH_TAC `(c:real^2->bool) IN g` THEN SET_TAC[];
        UNDISCH_TAC `path_image b SUBSET frontier(c:real^2->bool)` THEN
        UNDISCH_TAC `frontier c INTER interior(c:real^2->bool) = {}` THEN
        SET_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `closed(u:real^2->bool) /\ closed(v:real^2->bool)`
    STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[COMPACT_IMP_CLOSED]; ALL_TAC] THEN
    UNDISCH_TAC `closure(interior c) = (c:real^2->bool)` THEN
    DISCH_THEN(fun th -> GEN_REWRITE_TAC (RAND_CONV o BINOP_CONV o LAND_CONV)
      [SYM th]) THEN
    STRIP_TAC THENL [DISJ1_TAC; DISJ2_TAC] THEN
    MATCH_MP_TAC CLOSURE_MINIMAL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THENL
   [MP_TAC(ISPECL [`g:(real^2->bool)->bool`; `g0:(real^2->bool)->bool`;
                   `j:real^2->bool`; `c:real^2->bool`; `a1:real^1->real^2`;
                   `a2:real^1->real^2`; `b:real^1->real^2`; `u:real^2->bool`;
                   `v:real^2->bool`] MOI_SFR_SPLIT_CASE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[]];
    MP_TAC(ISPECL [`g:(real^2->bool)->bool`; `g0:(real^2->bool)->bool`;
                   `j:real^2->bool`; `c:real^2->bool`; `a2:real^1->real^2`;
                   `a1:real^1->real^2`; `b:real^1->real^2`; `v:real^2->bool`;
                   `u:real^2->bool`] MOI_SFR_SPLIT_CASE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      ONCE_REWRITE_TAC[INTER_COMM; UNION_COMM] THEN ASM_REWRITE_TAC[] THEN
      ONCE_REWRITE_TAC[INSERT_AC] THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[]]]);;

(* Moise 17.3 (with 17.2): a decomposition with at least two cells has a    *)
(* free cell outside any proper sub-2-cell g0 (or g0 empty).  Strong       *)
(* induction on the number of cells.                                         *)

let MOI_SFR_EXISTS = prove
 (`!n (g:(real^2->bool)->bool) g0 j.
     CARD g = n /\ moi_sfr_cplx g /\ 2 <= CARD g /\
     pl_cell_with_boundary 2 (UNIONS g) j /\ g0 SUBSET g /\
     (g0 = {} \/ ?j0. pl_cell_with_boundary 2 (UNIONS g0) j0) /\ ~(g0 = g)
     ==> ?c. c IN g /\ ~(c IN g0) /\ pl_ball 1 (frontier c INTER j)`,
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN DISCH_THEN(LABEL_TAC "wf") THEN
  MAP_EVERY X_GEN_TAC [`g:(real^2->bool)->bool`; `g0:(real^2->bool)->bool`;
                       `j:real^2->bool`] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!g' g0' j'. CARD g' < CARD(g:(real^2->bool)->bool) /\ moi_sfr_cplx g' /\
                2 <= CARD g' /\
                pl_cell_with_boundary 2 (UNIONS g') j' /\ g0' SUBSET g' /\
                (g0' = {} \/ ?j0. pl_cell_with_boundary 2 (UNIONS g0') j0) /\
                ~(g0' = g')
                ==> ?c'. c' IN g' /\ ~(c' IN g0') /\
                         pl_ball 1 (frontier c' INTER (j':real^2->bool))`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`g':(real^2->bool)->bool`; `g0':(real^2->bool)->bool`;
                         `j':real^2->bool`] THEN
    DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
    SUBGOAL_THEN `CARD(g':(real^2->bool)->bool) < n` ASSUME_TAC THENL
     [UNDISCH_TAC `CARD(g':(real^2->bool)->bool) < CARD(g:(real^2->bool)->bool)` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REMOVE_THEN "wf" (MP_TAC o SPEC `CARD(g':(real^2->bool)->bool)`) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL [`g':(real^2->bool)->bool`;
                               `g0':(real^2->bool)->bool`; `j':real^2->bool`]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`g:(real^2->bool)->bool`; `g0:(real^2->bool)->bool`;
                 `j:real^2->bool`] MOI_SFR_BOUNDARY_CELL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real^2->bool` STRIP_ASSUME_TAC) THEN
  ASM_CASES_TAC `pl_ball 1 (frontier c INTER (j:real^2->bool))` THENL
   [EXISTS_TAC `c:real^2->bool` THEN ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`g:(real^2->bool)->bool`; `g0:(real^2->bool)->bool`;
                   `j:real^2->bool`; `c:real^2->bool`] MOI_SFR_SPLIT_STEP) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* 10. Deleting a free cell leaves a PL 2-cell with the expected boundary;  *)
(* the main theorem FREE_CELL.                                               *)
(* ------------------------------------------------------------------------- *)

let MOI_SFR_ARC_CLOSURE_DIFF = prove
 (`!(h:real^1->real^N) k.
     arc h /\ FINITE k ==> closure(path_image h DIFF k) = path_image h`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [MATCH_MP_TAC CLOSURE_MINIMAL THEN
    ASM_SIMP_TAC[CLOSED_PATH_IMAGE; ARC_IMP_PATH] THEN SET_TAC[];
    ASM_SIMP_TAC[MOI_SFR_ARC_DENSE]]);;

(* c meets j in the PL arc A = image h; its complementary arcs kc in the     *)
(* frontier of c and kj in j give the theta split of the disk along kc:     *)
(* the side bounded by A and kc is c, the other side is the union of the    *)
(* other cells, bounded by kj UNION kc = closure((j UNION frontier c) - A).  *)

let MOI_SFR_DELETE = prove
 (`!(g:(real^2->bool)->bool) j c.
     moi_sfr_cplx g /\ pl_cell_with_boundary 2 (UNIONS g) j /\ c IN g /\
     pl_ball 1 (frontier c INTER j)
     ==> pl_cell_with_boundary 2 (UNIONS (g DELETE c))
           (closure ((j UNION frontier c) DIFF (frontier c INTER j)))`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_SFR_CELL_FACTS) THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `gam:real^1->real^2` STRIP_ASSUME_TAC) STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `polytope (c:real^2->bool) /\ aff_dim c = &2` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_SFR_CPLX_CELL THEN EXISTS_TAC `g:(real^2->bool)->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SFR_POLYGON_FACTS) THEN
  MP_TAC(ISPECL [`c:real^2->bool`; `frontier c:real^2->bool`] MOI_SFR_CELL_FACTS) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[MOI_SFR_POLYGON_CELL]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `gamc:real^1->real^2` STRIP_ASSUME_TAC o CONJUNCT1) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `h:real^1->real^2`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o SYM))) o
    MATCH_MP MOI_PL2_PL_BALL_1_ARC) THEN
  MP_TAC(ISPECL [`gam:real^1->real^2`; `h:real^1->real^2`] MOI_PL2_ARC_IN_LOOP) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `frontier c INTER (j:real^2->bool) = path_image h` THEN SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `kj:real^1->real^2` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`gamc:real^1->real^2`; `h:real^1->real^2`] MOI_PL2_ARC_IN_LOOP) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `frontier c INTER (j:real^2->bool) = path_image h` THEN SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `kc:real^1->real^2` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `pathstart(h:real^1->real^2) IN path_image kc /\
                pathfinish h IN path_image kc /\
                pathstart h IN path_image kj /\ pathfinish h IN path_image kj`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[PATHSTART_IN_PATH_IMAGE; PATHFINISH_IN_PATH_IMAGE]; ALL_TAC] THEN
  SUBGOAL_THEN `path_image kc INTER (j:real^2->bool) = {pathstart h,pathfinish h}`
  ASSUME_TAC THENL
   [MP_TAC(ISPEC `h:real^1->real^2` PATHSTART_IN_PATH_IMAGE) THEN
    MP_TAC(ISPEC `h:real^1->real^2` PATHFINISH_IN_PATH_IMAGE) THEN
    UNDISCH_TAC `path_image h UNION path_image kc = path_image(gamc:real^1->real^2)` THEN
    UNDISCH_TAC `path_image h INTER path_image kc =
                 {pathstart h,pathfinish(h:real^1->real^2)}` THEN
    UNDISCH_TAC `frontier c INTER (j:real^2->bool) = path_image h` THEN
    UNDISCH_TAC `path_image gamc = frontier(c:real^2->bool)` THEN
    UNDISCH_TAC `pathstart(h:real^1->real^2) IN path_image kc` THEN
    UNDISCH_TAC `pathfinish(h:real^1->real^2) IN path_image kc` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `path_image kc SUBSET (j:real^2->bool) UNION inside j` ASSUME_TAC THENL
   [UNDISCH_TAC `UNIONS g = (j:real^2->bool) UNION inside j` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    UNDISCH_TAC `path_image h UNION path_image kc = path_image(gamc:real^1->real^2)` THEN
    UNDISCH_TAC `path_image gamc = frontier(c:real^2->bool)` THEN
    UNDISCH_TAC `frontier c SUBSET (c:real^2->bool)` THEN
    UNDISCH_TAC `(c:real^2->bool) IN g` THEN SET_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `u = (path_image h UNION path_image kc) UNION
                  inside(path_image h UNION path_image(kc:real^1->real^2))` THEN
  ABBREV_TAC `v = (path_image kj UNION path_image kc) UNION
                  inside(path_image kj UNION path_image(kc:real^1->real^2))` THEN
  SUBGOAL_THEN `u = c:real^2->bool` ASSUME_TAC THENL
   [UNDISCH_TAC `(path_image h UNION path_image kc) UNION
                 inside(path_image h UNION path_image(kc:real^1->real^2)) =
                 (u:real^2->bool)` THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`h:real^1->real^2`; `reversepath(kj:real^1->real^2)`;
                 `reversepath(kc:real^1->real^2)`; `j:real^2->bool`;
                 `u:real^2->bool`; `v:real^2->bool`] MOI_SFR_THETA) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[PATH_IMAGE_REVERSEPATH; PATHSTART_REVERSEPATH;
                PATHFINISH_REVERSEPATH] THEN
    REPEAT CONJ_TAC THEN
    TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    ASM_SIMP_TAC[ARC_REVERSEPATH; MOI_PL2_PL_REVERSEPATH] THEN
    UNDISCH_TAC `path_image h UNION path_image kj = path_image(gam:real^1->real^2)` THEN
    UNDISCH_TAC `path_image gam = (j:real^2->bool)` THEN MESON_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `u = c:real^2->bool`)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[PATH_IMAGE_REVERSEPATH]) THEN
  UNDISCH_THEN `frontier c = path_image h UNION path_image(kc:real^1->real^2)`
    (K ALL_TAC) THEN
  UNDISCH_THEN `interior c = inside(path_image h UNION path_image(kc:real^1->real^2))`
    (K ALL_TAC) THEN
  REWRITE_TAC[ASSUME `frontier c INTER (j:real^2->bool) = path_image h`] THEN
  SUBGOAL_THEN `closed(v:real^2->bool)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[COMPACT_IMP_CLOSED]; ALL_TAC] THEN
  SUBGOAL_THEN `!e:real^2->bool. e IN g ==> e SUBSET c \/ e SUBSET v`
  (LABEL_TAC "cside") THENL
   [MATCH_MP_TAC MOI_SFR_CELLS_SIDE THEN
    MAP_EVERY EXISTS_TAC [`c:real^2->bool`; `path_image(kc:real^1->real^2)`;
                          `(j:real^2->bool) UNION inside j`] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `path_image h UNION path_image kc = path_image(gamc:real^1->real^2)` THEN
    UNDISCH_TAC `path_image gamc = frontier(c:real^2->bool)` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `interior v INTER (c:real^2->bool) = {}` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_SFR_INTERIOR_MISS THEN
    EXISTS_TAC `path_image(kc:real^1->real^2)` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `UNIONS (g DELETE c) = v:real^2->bool` SUBST1_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [REWRITE_TAC[UNIONS_SUBSET; IN_DELETE] THEN
      X_GEN_TAC `e:real^2->bool` THEN STRIP_TAC THEN
      USE_THEN "cside" (MP_TAC o C MATCH_MP (ASSUME `(e:real^2->bool) IN g`)) THEN
      MP_TAC(ISPECL [`g:(real^2->bool)->bool`; `e:real^2->bool`; `c:real^2->bool`]
        MOI_SFR_CPLX_INTER) THEN
      ASM_REWRITE_TAC[] THEN MESON_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `closure(interior v) = (v:real^2->bool)` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC CLOSURE_MINIMAL THEN
    CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_UNIONS; IN_DELETE] THEN X_GEN_TAC `z:real^2` THEN
      DISCH_TAC THEN
      SUBGOAL_THEN `(z:real^2) IN UNIONS g` MP_TAC THENL
       [UNDISCH_TAC `UNIONS g = (j:real^2->bool) UNION inside j` THEN
        DISCH_THEN SUBST1_TAC THEN
        MP_TAC(ISPEC `v:real^2->bool` INTERIOR_SUBSET) THEN
        UNDISCH_TAC `c UNION v = (j:real^2->bool) UNION inside j` THEN
        UNDISCH_TAC `(z:real^2) IN interior v` THEN SET_TAC[];
        ALL_TAC] THEN
      REWRITE_TAC[IN_UNIONS] THEN MATCH_MP_TAC MONO_EXISTS THEN
      X_GEN_TAC `e:real^2->bool` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      DISCH_TAC THEN
      UNDISCH_TAC `interior v INTER (c:real^2->bool) = {}` THEN
      UNDISCH_TAC `(z:real^2) IN interior v` THEN UNDISCH_TAC `(z:real^2) IN e` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      MATCH_MP_TAC CLOSED_UNIONS THEN
      SUBGOAL_THEN `FINITE(g:(real^2->bool)->bool)` ASSUME_TAC THENL
       [ASM_MESON_TAC[moi_sfr_cplx]; ALL_TAC] THEN
      ASM_SIMP_TAC[FINITE_DELETE; IN_DELETE] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC POLYTOPE_IMP_CLOSED THEN
      ASM_MESON_TAC[MOI_SFR_CPLX_CELL]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `closure ((j UNION frontier c) DIFF path_image h) =
    path_image kj UNION path_image(kc:real^1->real^2)`
  SUBST1_TAC THENL
   [SUBGOAL_THEN
     `(j UNION frontier c) DIFF path_image h =
      (path_image kj DIFF {pathstart h,pathfinish h}) UNION
      (path_image kc DIFF {pathstart h,pathfinish(h:real^1->real^2)})`
    SUBST1_TAC THENL
     [UNDISCH_TAC `path_image h UNION path_image kc = path_image(gamc:real^1->real^2)` THEN
      UNDISCH_TAC `path_image gamc = frontier(c:real^2->bool)` THEN
      UNDISCH_TAC `path_image h UNION path_image kj = path_image(gam:real^1->real^2)` THEN
      UNDISCH_TAC `path_image gam = (j:real^2->bool)` THEN
      UNDISCH_TAC `path_image h INTER path_image kj =
                   {pathstart h,pathfinish(h:real^1->real^2)}` THEN
      UNDISCH_TAC `path_image h INTER path_image kc =
                   {pathstart h,pathfinish(h:real^1->real^2)}` THEN
      SET_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[CLOSURE_UNION] THEN
    ASM_SIMP_TAC[MOI_SFR_ARC_CLOSURE_DIFF; FINITE_INSERT; FINITE_EMPTY];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[]);;

(* The main theorem (Moise 17.2-17.3 with the deletion of the free cell),   *)
(* the statement MOI_SCH3_FREE_CELL of pc_moi_sch3_stmt.ml.                 *)

let FREE_CELL = prove
 (MOI_SCH3_FREE_CELL,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `moi_sfr_cplx (g:(real^2->bool)->bool)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[moi_sfr_cplx]; ALL_TAC] THEN
  MP_TAC(ISPECL [`CARD(g:(real^2->bool)->bool)`; `g:(real^2->bool)->bool`;
                 `g0:(real^2->bool)->bool`; `j:real^2->bool`] MOI_SFR_EXISTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real^2->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `c:real^2->bool` THEN
  SUBGOAL_THEN `relative_frontier c = frontier(c:real^2->bool)` SUBST1_TAC THENL
   [MP_TAC(ISPEC `c:real^2->bool` MOI_SFR_POLYGON_FACTS) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_SFR_DELETE THEN ASM_REWRITE_TAC[]);;

