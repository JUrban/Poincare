(* ========================================================================= *)
(* pc_moi_lt_model2d: the 2D model step of the arc case of the cut step of   *)
(* the loop theorem (used in pc_moi_lt_cutb).  Main theorem LT_MODEL_2D: two *)
(* disjoint PL crosscuts p, q of the standard triangle are the images of the *)
(* chords x = 1, x = 2 of the model rectangle [0,3] x [0,1] under a PL       *)
(* homeomorphism carrying the boundary loop to the standard loop.  Route:    *)
(* theta curves cut the triangle into three PL disks; boundary PL            *)
(* homeomorphisms of the three unit squares extend over them and glue        *)
(* (GLUE).  The orientation: GLUE also gives a second map with every         *)
(* boundary piece reversed; the two boundary loops have opposite winding     *)
(* numbers about an interior point, so one of them is homotopic to the       *)
(* standard loop (CONVEX_LOOPS_WN).                                          *)
(* ========================================================================= *)

needs "src/pc_moi_lt_cutbstmt.ml";;
needs "src/pc_moi_sch3_free.ml";;
needs "src/pc_moi_pl2.ml";;
needs "src/pc_moi_lt_cuta2.ml";;
needs "src/pc_moi_lt_cutb0.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* The standard triangle T: a convex polytope with nonempty                 *)
(* interior whose relative frontier is its frontier, the inside of which is *)
(* its interior; the standard loop is a simple PL loop onto it.             *)
(* ========================================================================= *)

let MOI_LM2_T_FACTS = prove
 (`compact std_triangle /\ convex std_triangle /\ polytope std_triangle /\
   bounded std_triangle /\ closed std_triangle /\
   ~(interior std_triangle = {}) /\
   relative_frontier std_triangle = frontier std_triangle /\
   inside (frontier std_triangle) = interior std_triangle /\
   frontier std_triangle UNION interior std_triangle = std_triangle /\
   frontier std_triangle SUBSET std_triangle /\
   simple_path std_triangle_loop /\
   pathfinish std_triangle_loop = pathstart std_triangle_loop /\
   path_image std_triangle_loop = frontier std_triangle /\
   pl_map_on (interval[vec 0,vec 1]) std_triangle_loop`,
  MP_TAC MOI_LTD_STD_TRIANGLE_BASIC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(interior std_triangle = {})` ASSUME_TAC THENL
   [MP_TAC(ISPEC `std_triangle` AFF_DIM_NONEMPTY_INTERIOR_EQ) THEN
    ASM_REWRITE_TAC[DIMINDEX_2] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MP_TAC MOI_LTD_STD_TRIANGLE_SIMPLEX THEN MESON_TAC[AFF_DIM_SIMPLEX];
    ALL_TAC] THEN
  SUBGOAL_THEN `relative_frontier std_triangle = frontier std_triangle` ASSUME_TAC THENL
   [ASM_SIMP_TAC[RELATIVE_FRONTIER_NONEMPTY_INTERIOR]; ALL_TAC] THEN
  ASM_SIMP_TAC[COMPACT_IMP_BOUNDED; INSIDE_FRONTIER_EQ_INTERIOR] THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(ISPEC `std_triangle` INTERIOR_SUBSET) THEN
    ASM_SIMP_TAC[FRONTIER_SUBSET_CLOSED] THEN
    REWRITE_TAC[frontier] THEN ASM_SIMP_TAC[CLOSURE_CLOSED] THEN SET_TAC[];
    ASM_SIMP_TAC[FRONTIER_SUBSET_CLOSED];
    ACCEPT_TAC MOI_S6F_LOOP_SIMPLE;
    MP_TAC MOI_LTD_STD_TRIANGLE_LOOP THEN SIMP_TAC[];
    MP_TAC MOI_LTD_STD_TRIANGLE_LOOP THEN ASM_SIMP_TAC[];
    REWRITE_TAC[std_triangle_loop] THEN
    REPEAT(MATCH_MP_TAC MOI_PL2_PL_JOINPATHS THEN
           REWRITE_TAC[PATHSTART_JOIN; PATHFINISH_JOIN; PATHSTART_LINEPATH;
                       PATHFINISH_LINEPATH] THEN CONJ_TAC) THEN
    SIMP_TAC[MOI_PL2_PL_LINEPATH; MOI_PL2_LOCALLY_POLYHEDRAL_INTERVAL]]);;

(* ========================================================================= *)
(* An arc cut at two interior parameters 0 < s < t < 1 into                *)
(* three PL arcs meeting only at the cut points.                            *)
(* ========================================================================= *)

let MOI_LM2_ARC_THREE = prove
 (`!(g:real^1->real^N) s t.
     arc g /\ pl_map_on (interval[vec 0,vec 1]) g /\
     &0 < drop s /\ drop s < drop t /\ drop t < &1
     ==> arc (subpath (vec 0) s g) /\ arc (subpath s t g) /\ arc (subpath t (vec 1) g) /\
         pl_map_on (interval[vec 0,vec 1]) (subpath (vec 0) s g) /\
         pl_map_on (interval[vec 0,vec 1]) (subpath s t g) /\
         pl_map_on (interval[vec 0,vec 1]) (subpath t (vec 1) g) /\
         pathstart (subpath (vec 0) s g) = pathstart g /\
         pathfinish (subpath (vec 0) s g) = g s /\
         pathstart (subpath s t g) = g s /\ pathfinish (subpath s t g) = g t /\
         pathstart (subpath t (vec 1) g) = g t /\
         pathfinish (subpath t (vec 1) g) = pathfinish g /\
         path_image (subpath (vec 0) s g) UNION path_image (subpath s t g) UNION
         path_image (subpath t (vec 1) g) = path_image g /\
         path_image (subpath (vec 0) s g) INTER path_image (subpath s t g) = {g s} /\
         path_image (subpath s t g) INTER path_image (subpath t (vec 1) g) = {g t} /\
         path_image (subpath (vec 0) s g) INTER path_image (subpath t (vec 1) g) = {}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(s:real^1) IN interval[vec 0,vec 1] /\ (t:real^1) IN interval[vec 0,vec 1]`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[IN_INTERVAL_1; DROP_VEC] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~(vec 0:real^1 = s) /\ ~(s:real^1 = t) /\ ~(t:real^1 = vec 1)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM DROP_EQ; DROP_VEC] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!x y. x IN interval[vec 0,vec 1] /\ y IN interval[vec 0,vec 1] /\
                      (g:real^1->real^N) x = g y ==> x = y` ASSUME_TAC THENL
   [ASM_MESON_TAC[arc]; ALL_TAC] THEN
  ASM_SIMP_TAC[ARC_SUBPATH_ARC; ENDS_IN_UNIT_INTERVAL; MOI_PL2_PL_SUBPATH;
               PATHSTART_SUBPATH; PATHFINISH_SUBPATH] THEN
  REWRITE_TAC[pathstart; pathfinish] THEN
  SUBGOAL_THEN
   `path_image (subpath (vec 0) s (g:real^1->real^N)) = IMAGE g (interval[vec 0,s]) /\
    path_image (subpath s t g) = IMAGE g (interval[s,t]) /\
    path_image (subpath t (vec 1) g) = IMAGE g (interval[t,vec 1]) /\
    path_image g = IMAGE g (interval[vec 0,vec 1])`
  (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[path_image] THEN REPEAT CONJ_TAC THEN
    REWRITE_TAC[GSYM path_image] THEN MATCH_MP_TAC PATH_IMAGE_SUBPATH THEN
    REWRITE_TAC[DROP_VEC] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[GSYM IMAGE_UNION] THEN AP_TERM_TAC THEN
    REWRITE_TAC[EXTENSION; IN_UNION; IN_INTERVAL_1; DROP_VEC] THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC(SET_RULE
     `!f:real^1->real^N a b c. (!x y. x IN c /\ y IN c /\ f x = f y ==> x = y) /\
        a SUBSET c /\ b SUBSET c /\ a INTER b = {s}
        ==> IMAGE f a INTER IMAGE f b = {f s}`) THEN
    EXISTS_TAC `interval[vec 0:real^1,vec 1]` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; EXTENSION; IN_INTER; IN_SING; IN_INTERVAL_1; DROP_VEC;
                GSYM DROP_EQ] THEN
    ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC(SET_RULE
     `!f:real^1->real^N a b c. (!x y. x IN c /\ y IN c /\ f x = f y ==> x = y) /\
        a SUBSET c /\ b SUBSET c /\ a INTER b = {t}
        ==> IMAGE f a INTER IMAGE f b = {f t}`) THEN
    EXISTS_TAC `interval[vec 0:real^1,vec 1]` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; EXTENSION; IN_INTER; IN_SING; IN_INTERVAL_1; DROP_VEC;
                GSYM DROP_EQ] THEN
    ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC(SET_RULE
     `!f:real^1->real^N a b c. (!x y. x IN c /\ y IN c /\ f x = f y ==> x = y) /\
        a SUBSET c /\ b SUBSET c /\ a INTER b = {}
        ==> IMAGE f a INTER IMAGE f b = {}`) THEN
    EXISTS_TAC `interval[vec 0:real^1,vec 1]` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_INTERVAL_1; DROP_VEC] THEN
    ASM_REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* The three regions, in the ordered case.  a1, a2 are the two              *)
(* arcs of the triangle frontier between the ends of the crosscut p; q is   *)
(* a crosscut on the a2 side whose ends are a2 s, a2 t with 0 < s < t < 1. *)
(* The first theta curve (a1, a2, p) gives R1 (bounded by a1 and p); the    *)
(* second (a2 between s and t versus the rest of the a2-side frontier, with *)
(* crosscut q) gives R2 (bounded by a2[s,t] and q) and R0.                  *)
(* ========================================================================= *)

let MOI_LM2_REGIONS_ORD = prove
 (`!(a1:real^1->real^2) a2 p q s t.
     arc a1 /\ pl_map_on (interval[vec 0,vec 1]) a1 /\
     arc a2 /\ pl_map_on (interval[vec 0,vec 1]) a2 /\
     arc p /\ pl_map_on (interval[vec 0,vec 1]) p /\
     arc q /\ pl_map_on (interval[vec 0,vec 1]) q /\
     pathstart a1 = pathstart p /\ pathfinish a1 = pathfinish p /\
     pathstart a2 = pathstart p /\ pathfinish a2 = pathfinish p /\
     path_image a1 INTER path_image a2 = {pathstart p,pathfinish p} /\
     path_image a1 UNION path_image a2 = frontier std_triangle /\
     path_image p SUBSET std_triangle /\
     path_image p INTER frontier std_triangle = {pathstart p,pathfinish p} /\
     path_image q INTER frontier std_triangle = {pathstart q,pathfinish q} /\
     path_image p INTER path_image q = {} /\
     path_image q SUBSET
       (path_image a2 UNION path_image p) UNION inside (path_image a2 UNION path_image p) /\
     &0 < drop s /\ drop s < drop t /\ drop t < &1 /\
     pathstart q = a2 s /\ pathfinish q = a2 t
     ==> ?R1 R0 R2.
           pl_cell_with_boundary 2 R1 (path_image a1 UNION path_image p) /\
           pl_cell_with_boundary 2 R0
             (path_image (subpath (vec 0) s a2) UNION path_image p UNION
              path_image (subpath t (vec 1) a2) UNION path_image q) /\
           pl_cell_with_boundary 2 R2 (path_image (subpath s t a2) UNION path_image q) /\
           R1 UNION R0 UNION R2 = std_triangle /\
           R1 INTER R0 = path_image p /\ R0 INTER R2 = path_image q /\
           R1 INTER R2 = {}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC MOI_LM2_T_FACTS THEN STRIP_TAC THEN
  (* the first theta curve *)
  MP_TAC(ISPECL [`a1:real^1->real^2`; `a2:real^1->real^2`; `p:real^1->real^2`;
                 `frontier std_triangle`;
                 `(path_image a1 UNION path_image p) UNION
                  inside(path_image a1 UNION path_image (p:real^1->real^2))`;
                 `(path_image a2 UNION path_image p) UNION
                  inside(path_image a2 UNION path_image (p:real^1->real^2))`]
    MOI_SFR_THETA) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `path_image (p:real^1->real^2) SUBSET std_triangle` THEN
    UNDISCH_TAC `frontier std_triangle UNION interior std_triangle = std_triangle` THEN
    SET_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `u = (path_image a1 UNION path_image p) UNION
                  inside(path_image a1 UNION path_image (p:real^1->real^2))` THEN
  ABBREV_TAC `v = (path_image a2 UNION path_image p) UNION
                  inside(path_image a2 UNION path_image (p:real^1->real^2))` THEN
  STRIP_TAC THEN
  (* the three arcs of a2 *)
  MP_TAC(ISPECL [`a2:real^1->real^2`; `s:real^1`; `t:real^1`] MOI_LM2_ARC_THREE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  ABBREV_TAC `bt = subpath (vec 0) s (a2:real^1->real^2)` THEN
  ABBREV_TAC `bu = subpath s t (a2:real^1->real^2)` THEN
  ABBREV_TAC `bv = subpath t (vec 1) (a2:real^1->real^2)` THEN
  (* point facts *)
  SUBGOAL_THEN
   `~((pathstart q:real^2) IN path_image p) /\ ~((pathfinish q:real^2) IN path_image p) /\
    (pathstart p:real^2) IN path_image p /\ (pathfinish p:real^2) IN path_image p /\
    (pathstart q:real^2) IN path_image q /\ (pathfinish q:real^2) IN path_image q /\
    (pathstart p:real^2) IN path_image bt /\ (pathfinish p:real^2) IN path_image bv /\
    ~((pathstart p:real^2) IN path_image bu) /\ ~((pathfinish p:real^2) IN path_image bu) /\
    ~((pathstart p:real^2) IN path_image bv) /\ ~((pathfinish p:real^2) IN path_image bt)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[PATHSTART_IN_PATH_IMAGE; PATHFINISH_IN_PATH_IMAGE] THEN
    SUBGOAL_THEN `(pathstart p:real^2) IN path_image bt /\ (pathfinish p:real^2) IN path_image bv /\
                  (a2 (s:real^1):real^2) IN path_image bt /\ (a2 (t:real^1):real^2) IN path_image bv /\
                  (a2 s:real^2) IN path_image bu /\ (a2 t:real^2) IN path_image bu`
    STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[PATHSTART_IN_PATH_IMAGE; PATHFINISH_IN_PATH_IMAGE]; ALL_TAC] THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
     [UNDISCH_TAC `path_image p INTER path_image q = {}:real^2->bool` THEN
      MP_TAC(ISPEC `q:real^1->real^2` PATHSTART_IN_PATH_IMAGE) THEN SET_TAC[];
      UNDISCH_TAC `path_image p INTER path_image q = {}:real^2->bool` THEN
      MP_TAC(ISPEC `q:real^1->real^2` PATHFINISH_IN_PATH_IMAGE) THEN SET_TAC[];
      DISCH_TAC THEN
      UNDISCH_TAC `path_image bt INTER path_image bu = {(a2:real^1->real^2) s}` THEN
      UNDISCH_TAC `(pathstart p:real^2) IN path_image bt` THEN
      UNDISCH_TAC `(pathstart p:real^2) IN path_image bu` THEN
      SUBGOAL_THEN `~((a2:real^1->real^2) s = pathstart p)` MP_TAC THENL
       [UNDISCH_TAC `pathstart q = (a2:real^1->real^2) s` THEN
        DISCH_THEN(SUBST1_TAC o SYM) THEN
        UNDISCH_TAC `path_image p INTER path_image q = {}:real^2->bool` THEN
        MP_TAC(ISPEC `q:real^1->real^2` PATHSTART_IN_PATH_IMAGE) THEN
        MP_TAC(ISPEC `p:real^1->real^2` PATHSTART_IN_PATH_IMAGE) THEN SET_TAC[];
        SET_TAC[]];
      DISCH_TAC THEN
      UNDISCH_TAC `path_image bu INTER path_image bv = {(a2:real^1->real^2) t}` THEN
      UNDISCH_TAC `(pathfinish p:real^2) IN path_image bv` THEN
      UNDISCH_TAC `(pathfinish p:real^2) IN path_image bu` THEN
      SUBGOAL_THEN `~((a2:real^1->real^2) t = pathfinish p)` MP_TAC THENL
       [UNDISCH_TAC `pathfinish q = (a2:real^1->real^2) t` THEN
        DISCH_THEN(SUBST1_TAC o SYM) THEN
        UNDISCH_TAC `path_image p INTER path_image q = {}:real^2->bool` THEN
        MP_TAC(ISPEC `q:real^1->real^2` PATHFINISH_IN_PATH_IMAGE) THEN
        MP_TAC(ISPEC `p:real^1->real^2` PATHFINISH_IN_PATH_IMAGE) THEN SET_TAC[];
        SET_TAC[]];
      UNDISCH_TAC `path_image bt INTER path_image bv = {}:real^2->bool` THEN
      UNDISCH_TAC `(pathstart p:real^2) IN path_image bt` THEN SET_TAC[];
      UNDISCH_TAC `path_image bt INTER path_image bv = {}:real^2->bool` THEN
      UNDISCH_TAC `(pathfinish p:real^2) IN path_image bv` THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `path_image p INTER path_image (a2:real^1->real^2) =
                {pathstart p,pathfinish p}` ASSUME_TAC THENL
   [UNDISCH_TAC `path_image p INTER frontier std_triangle = {pathstart p,pathfinish (p:real^1->real^2)}` THEN
    UNDISCH_TAC `path_image a1 UNION path_image a2 = frontier std_triangle` THEN
    MP_TAC(ISPEC `a2:real^1->real^2` PATHSTART_IN_PATH_IMAGE) THEN
    MP_TAC(ISPEC `a2:real^1->real^2` PATHFINISH_IN_PATH_IMAGE) THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `path_image p INTER path_image bt = {pathstart (p:real^1->real^2)} /\
    path_image p INTER path_image bu = {} /\
    path_image p INTER path_image bv = {pathfinish (p:real^1->real^2)}`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `path_image p INTER path_image (a2:real^1->real^2) =
                 {pathstart p,pathfinish p}` THEN
    UNDISCH_TAC `path_image bt UNION path_image bu UNION path_image bv =
                 path_image (a2:real^1->real^2)` THEN
    MAP_EVERY UNDISCH_TAC
     [`(pathstart p:real^2) IN path_image p`; `(pathfinish p:real^2) IN path_image p`;
      `(pathstart p:real^2) IN path_image bt`; `(pathfinish p:real^2) IN path_image bv`;
      `~((pathstart p:real^2) IN path_image bu)`; `~((pathfinish p:real^2) IN path_image bu)`;
      `~((pathstart p:real^2) IN path_image bv)`; `~((pathfinish p:real^2) IN path_image bt)`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  (* the arc a2' = rev bt ++ p ++ rev bv from a2 s to a2 t *)
  SUBGOAL_THEN
   `arc (reversepath bt ++ p ++ reversepath (bv:real^1->real^2)) /\
    pl_map_on (interval[vec 0,vec 1]) (reversepath bt ++ p ++ reversepath bv) /\
    pathstart (reversepath bt ++ p ++ reversepath bv) = a2 (s:real^1) /\
    pathfinish (reversepath bt ++ p ++ reversepath bv) = a2 (t:real^1) /\
    path_image (reversepath bt ++ p ++ reversepath bv) =
    path_image bt UNION path_image p UNION path_image bv`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[PATHSTART_JOIN; PATHFINISH_JOIN; PATHSTART_REVERSEPATH;
                 PATHFINISH_REVERSEPATH; PATH_IMAGE_JOIN; PATH_IMAGE_REVERSEPATH] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC ARC_JOIN THEN
      ASM_SIMP_TAC[ARC_REVERSEPATH; PATHSTART_JOIN; PATHFINISH_REVERSEPATH;
                   PATHSTART_REVERSEPATH; PATH_IMAGE_JOIN; PATH_IMAGE_REVERSEPATH] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC ARC_JOIN THEN
        ASM_SIMP_TAC[ARC_REVERSEPATH; PATHSTART_REVERSEPATH; PATH_IMAGE_REVERSEPATH] THEN
        UNDISCH_TAC `path_image p INTER path_image bv = {pathfinish (p:real^1->real^2)}` THEN
        SET_TAC[];
        UNDISCH_TAC `path_image p INTER path_image bt = {pathstart (p:real^1->real^2)}` THEN
        UNDISCH_TAC `path_image bt INTER path_image bv = {}:real^2->bool` THEN
        SET_TAC[]];
      MATCH_MP_TAC MOI_PL2_PL_JOINPATHS THEN
      ASM_SIMP_TAC[MOI_PL2_PL_REVERSEPATH; PATHFINISH_REVERSEPATH; PATHSTART_JOIN] THEN
      MATCH_MP_TAC MOI_PL2_PL_JOINPATHS THEN
      ASM_SIMP_TAC[MOI_PL2_PL_REVERSEPATH; PATHSTART_REVERSEPATH]];
    ALL_TAC] THEN
  SUBGOAL_THEN `path_image bu UNION (path_image bt UNION path_image p UNION path_image bv) =
                path_image a2 UNION path_image (p:real^1->real^2)` ASSUME_TAC THENL
   [UNDISCH_TAC `path_image bt UNION path_image bu UNION path_image bv =
                 path_image (a2:real^1->real^2)` THEN SET_TAC[];
    ALL_TAC] THEN
  (* the second theta curve *)
  MP_TAC(ISPECL [`bu:real^1->real^2`; `reversepath bt ++ p ++ reversepath (bv:real^1->real^2)`;
                 `q:real^1->real^2`;
                 `path_image bu UNION (path_image bt UNION path_image p UNION
                                       path_image (bv:real^1->real^2))`;
                 `(path_image bu UNION path_image q) UNION
                  inside(path_image bu UNION path_image (q:real^1->real^2))`;
                 `(path_image (reversepath bt ++ p ++ reversepath bv) UNION path_image q) UNION
                  inside(path_image (reversepath bt ++ p ++ reversepath bv) UNION
                         path_image (q:real^1->real^2))`]
    MOI_SFR_THETA) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `path_image bt INTER path_image bu = {(a2:real^1->real^2) s}` THEN
      UNDISCH_TAC `path_image bu INTER path_image bv = {(a2:real^1->real^2) t}` THEN
      UNDISCH_TAC `path_image p INTER path_image bu = {}:real^2->bool` THEN
      MP_TAC(ISPEC `bu:real^1->real^2` PATHSTART_IN_PATH_IMAGE) THEN
      MP_TAC(ISPEC `bu:real^1->real^2` PATHFINISH_IN_PATH_IMAGE) THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      UNDISCH_TAC `path_image q INTER frontier std_triangle = {pathstart q,pathfinish (q:real^1->real^2)}` THEN
      UNDISCH_TAC `path_image a1 UNION path_image a2 = frontier std_triangle` THEN
      UNDISCH_TAC `path_image bt UNION path_image bu UNION path_image bv =
                   path_image (a2:real^1->real^2)` THEN
      UNDISCH_TAC `path_image p INTER path_image q = {}:real^2->bool` THEN
      MP_TAC(ISPEC `bu:real^1->real^2` PATHSTART_IN_PATH_IMAGE) THEN
      MP_TAC(ISPEC `bu:real^1->real^2` PATHFINISH_IN_PATH_IMAGE) THEN
      MP_TAC(ISPEC `q:real^1->real^2` PATHSTART_IN_PATH_IMAGE) THEN
      MP_TAC(ISPEC `q:real^1->real^2` PATHFINISH_IN_PATH_IMAGE) THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC
   [`u:real^2->bool`;
    `(path_image bt UNION path_image p UNION path_image bv UNION path_image q) UNION
     inside(path_image bt UNION path_image p UNION path_image bv UNION
            path_image (q:real^1->real^2))`;
    `(path_image bu UNION path_image q) UNION
     inside(path_image bu UNION path_image (q:real^1->real^2))`] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[UNION_ASSOC]) THEN REWRITE_TAC[UNION_ASSOC] THEN
  ABBREV_TAC `r0 = path_image bt UNION path_image p UNION path_image bv UNION path_image q
                   UNION inside (path_image bt UNION path_image p UNION path_image bv UNION
                                 path_image (q:real^1->real^2))` THEN
  ABBREV_TAC `r2 = path_image bu UNION path_image q UNION
                   inside (path_image bu UNION path_image (q:real^1->real^2))` THEN
  SUBGOAL_THEN `path_image (p:real^1->real^2) SUBSET r0` ASSUME_TAC THENL
   [EXPAND_TAC "r0" THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `u UNION r0 UNION r2 = std_triangle /\ u INTER r0 = path_image (p:real^1->real^2) /\
    r0 INTER r2 = path_image (q:real^1->real^2) /\ u INTER r2 = {}`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `u UNION v = frontier std_triangle UNION inside (frontier std_triangle)` THEN
    UNDISCH_TAC `u INTER v = path_image (p:real^1->real^2)` THEN
    UNDISCH_TAC `path_image bu UNION path_image q UNION
                 inside (path_image bu UNION path_image q) UNION r0 = (v:real^2->bool)` THEN
    UNDISCH_TAC `r2 INTER r0 = path_image (q:real^1->real^2)` THEN
    UNDISCH_TAC `path_image (p:real^1->real^2) SUBSET r0` THEN
    UNDISCH_TAC `path_image p INTER path_image q = {}:real^2->bool` THEN
    UNDISCH_TAC `inside (frontier std_triangle) = interior std_triangle` THEN
    UNDISCH_TAC `frontier std_triangle UNION interior std_triangle = std_triangle` THEN
    EXPAND_TAC "r2" THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `u UNION r0 UNION r2 = std_triangle` THEN
  EXPAND_TAC "r0" THEN REWRITE_TAC[UNION_ASSOC]);;

(* ========================================================================= *)
(* The three regions in general.  The ends of q lie on the side arc a2 (off  *)
(* the ends of p); order them along a2, reversing q if necessary; then the   *)
(* ordered case.  The side of p containing q is chosen by the theta curve    *)
(* (a1 and a2 swapped if needed).                                            *)
(* ========================================================================= *)

let MOI_LM2_REGIONS_SIDE = prove
 (`!(a1:real^1->real^2) a2 p q.
     arc a1 /\ pl_map_on (interval[vec 0,vec 1]) a1 /\
     arc a2 /\ pl_map_on (interval[vec 0,vec 1]) a2 /\
     arc p /\ pl_map_on (interval[vec 0,vec 1]) p /\
     arc q /\ pl_map_on (interval[vec 0,vec 1]) q /\
     pathstart a1 = pathstart p /\ pathfinish a1 = pathfinish p /\
     pathstart a2 = pathstart p /\ pathfinish a2 = pathfinish p /\
     path_image a1 INTER path_image a2 = {pathstart p,pathfinish p} /\
     path_image a1 UNION path_image a2 = frontier std_triangle /\
     path_image p SUBSET std_triangle /\
     path_image p INTER frontier std_triangle = {pathstart p,pathfinish p} /\
     path_image q INTER frontier std_triangle = {pathstart q,pathfinish q} /\
     path_image p INTER path_image q = {} /\
     path_image q SUBSET
       (path_image a2 UNION path_image p) UNION inside (path_image a2 UNION path_image p)
     ==> ?s t q' R1 R0 R2.
           (q' = q \/ q' = reversepath q) /\
           &0 < drop s /\ drop s < drop t /\ drop t < &1 /\
           pathstart q' = a2 s /\ pathfinish q' = a2 t /\
           pl_cell_with_boundary 2 R1 (path_image a1 UNION path_image p) /\
           pl_cell_with_boundary 2 R0
             (path_image (subpath (vec 0) s a2) UNION path_image p UNION
              path_image (subpath t (vec 1) a2) UNION path_image q) /\
           pl_cell_with_boundary 2 R2 (path_image (subpath s t a2) UNION path_image q) /\
           R1 UNION R0 UNION R2 = std_triangle /\
           R1 INTER R0 = path_image p /\ R0 INTER R2 = path_image q /\
           R1 INTER R2 = {}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC MOI_LM2_T_FACTS THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`a1:real^1->real^2`; `a2:real^1->real^2`; `p:real^1->real^2`;
                 `frontier std_triangle`;
                 `(path_image a1 UNION path_image p) UNION
                  inside(path_image a1 UNION path_image (p:real^1->real^2))`;
                 `(path_image a2 UNION path_image p) UNION
                  inside(path_image a2 UNION path_image (p:real^1->real^2))`]
    MOI_SFR_THETA) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `path_image (p:real^1->real^2) SUBSET std_triangle` THEN
    UNDISCH_TAC `frontier std_triangle UNION interior std_triangle = std_triangle` THEN
    SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(fun th -> ASSUME_TAC(el 15 (CONJUNCTS th))) THEN
  (* the ends of q lie on a2 off the ends of p *)
  SUBGOAL_THEN
   `!x. x IN path_image q /\ x IN frontier std_triangle
        ==> ?r. &0 < drop r /\ drop r < &1 /\ (a2:real^1->real^2) r = x`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^2` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(x:real^2) IN path_image a2 /\ ~(x = pathstart p) /\ ~(x = pathfinish p)`
    STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN `~((x:real^2) IN path_image p)` ASSUME_TAC THENL
       [UNDISCH_TAC `path_image p INTER path_image q = {}:real^2->bool` THEN
        UNDISCH_TAC `(x:real^2) IN path_image q` THEN SET_TAC[];
        ALL_TAC] THEN
      MP_TAC(ISPEC `p:real^1->real^2` PATHSTART_IN_PATH_IMAGE) THEN
      MP_TAC(ISPEC `p:real^1->real^2` PATHFINISH_IN_PATH_IMAGE) THEN
      UNDISCH_TAC `((path_image a2 UNION path_image p) UNION
                    inside(path_image a2 UNION path_image (p:real^1->real^2))) INTER
                   path_image a1 = {pathstart a1,pathfinish (a1:real^1->real^2)}` THEN
      UNDISCH_TAC `path_image a1 UNION path_image a2 = frontier std_triangle` THEN
      UNDISCH_TAC `path_image (q:real^1->real^2) SUBSET
                   (path_image a2 UNION path_image p) UNION
                   inside (path_image a2 UNION path_image p)` THEN
      UNDISCH_TAC `(x:real^2) IN path_image q` THEN
      UNDISCH_TAC `(x:real^2) IN frontier std_triangle` THEN
      UNDISCH_TAC `~((x:real^2) IN path_image p)` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `(x:real^2) IN path_image a2` THEN
    REWRITE_TAC[path_image; IN_IMAGE; IN_INTERVAL_1; DROP_VEC] THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real^1` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `r:real^1` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~(r = vec 0:real^1) /\ ~(r = vec 1:real^1)` MP_TAC THENL
     [CONJ_TAC THEN DISCH_THEN SUBST_ALL_TAC THENL
       [UNDISCH_TAC `~(x:real^2 = pathstart p)` THEN
        UNDISCH_TAC `pathstart a2 = pathstart (p:real^1->real^2)` THEN
        REWRITE_TAC[pathstart] THEN ASM_MESON_TAC[];
        UNDISCH_TAC `~(x:real^2 = pathfinish p)` THEN
        UNDISCH_TAC `pathfinish a2 = pathfinish (p:real^1->real^2)` THEN
        REWRITE_TAC[pathfinish] THEN ASM_MESON_TAC[]];
      REWRITE_TAC[GSYM DROP_EQ; DROP_VEC] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  FIRST_X_ASSUM(fun th ->
    MP_TAC(SPEC `pathstart (q:real^1->real^2)` th) THEN
    MP_TAC(SPEC `pathfinish (q:real^1->real^2)` th)) THEN
  ASM_REWRITE_TAC[PATHSTART_IN_PATH_IMAGE; PATHFINISH_IN_PATH_IMAGE] THEN
  SUBGOAL_THEN `pathstart (q:real^1->real^2) IN frontier std_triangle /\
                pathfinish (q:real^1->real^2) IN frontier std_triangle`
  (fun th -> REWRITE_TAC[th]) THENL
   [UNDISCH_TAC `path_image q INTER frontier std_triangle =
                 {pathstart q,pathfinish (q:real^1->real^2)}` THEN SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `rb:real^1` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `ra:real^1` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `~(drop ra = drop rb)` ASSUME_TAC THENL
   [REWRITE_TAC[DROP_EQ] THEN DISCH_THEN SUBST_ALL_TAC THEN
    MP_TAC(ISPEC `q:real^1->real^2` ARC_DISTINCT_ENDS) THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `drop ra < drop rb \/ drop rb < drop ra` DISJ_CASES_TAC THENL
   [UNDISCH_TAC `~(drop ra = drop rb)` THEN REAL_ARITH_TAC;
    MP_TAC(ISPECL [`a1:real^1->real^2`; `a2:real^1->real^2`; `p:real^1->real^2`;
                   `q:real^1->real^2`; `ra:real^1`; `rb:real^1`] MOI_LM2_REGIONS_ORD) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `R1:real^2->bool` (X_CHOOSE_THEN `R0:real^2->bool`
      (X_CHOOSE_THEN `R2:real^2->bool` STRIP_ASSUME_TAC))) THEN
    MAP_EVERY EXISTS_TAC [`ra:real^1`; `rb:real^1`; `q:real^1->real^2`;
                          `R1:real^2->bool`; `R0:real^2->bool`; `R2:real^2->bool`] THEN
    ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`a1:real^1->real^2`; `a2:real^1->real^2`; `p:real^1->real^2`;
                   `reversepath q:real^1->real^2`; `rb:real^1`; `ra:real^1`]
      MOI_LM2_REGIONS_ORD) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[ARC_REVERSEPATH; MOI_PL2_PL_REVERSEPATH; PATH_IMAGE_REVERSEPATH;
                   PATHSTART_REVERSEPATH; PATHFINISH_REVERSEPATH] THEN
      UNDISCH_TAC `path_image q INTER frontier std_triangle =
                   {pathstart q,pathfinish (q:real^1->real^2)}` THEN
      SET_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[PATH_IMAGE_REVERSEPATH] THEN
    DISCH_THEN(X_CHOOSE_THEN `R1:real^2->bool` (X_CHOOSE_THEN `R0:real^2->bool`
      (X_CHOOSE_THEN `R2:real^2->bool` STRIP_ASSUME_TAC))) THEN
    MAP_EVERY EXISTS_TAC [`rb:real^1`; `ra:real^1`; `reversepath q:real^1->real^2`;
                          `R1:real^2->bool`; `R0:real^2->bool`; `R2:real^2->bool`] THEN
    ASM_REWRITE_TAC[PATHSTART_REVERSEPATH; PATHFINISH_REVERSEPATH]]);;

(* ========================================================================= *)
(* The three regions for two disjoint crosscuts of the                      *)
(* triangle.  Split the standard loop at the ends of p (MOI_SFR_LOOP_SPLIT) *)
(* and let the theta curve decide on which side q lies.                     *)
(* ========================================================================= *)

let MOI_LM2_REGIONS = prove
 (`!(p:real^1->real^2) (q:real^1->real^2).
     arc p /\ pl_map_on (interval[vec 0,vec 1]) p /\
     arc q /\ pl_map_on (interval[vec 0,vec 1]) q /\
     path_image p SUBSET std_triangle /\ path_image q SUBSET std_triangle /\
     path_image p INTER frontier std_triangle = {pathstart p,pathfinish p} /\
     path_image q INTER frontier std_triangle = {pathstart q,pathfinish q} /\
     path_image p INTER path_image q = {}
     ==> ?a1 a2 s t q' R1 R0 R2.
           arc a1 /\ pl_map_on (interval[vec 0,vec 1]) a1 /\
           arc a2 /\ pl_map_on (interval[vec 0,vec 1]) a2 /\
           pathstart a1 = pathstart p /\ pathfinish a1 = pathfinish p /\
           pathstart a2 = pathstart p /\ pathfinish a2 = pathfinish p /\
           path_image a1 INTER path_image a2 = {pathstart p,pathfinish p} /\
           path_image a1 UNION path_image a2 = frontier std_triangle /\
           (q' = q \/ q' = reversepath q) /\
           &0 < drop s /\ drop s < drop t /\ drop t < &1 /\
           pathstart q' = a2 s /\ pathfinish q' = a2 t /\
           pl_cell_with_boundary 2 R1 (path_image a1 UNION path_image p) /\
           pl_cell_with_boundary 2 R0
             (path_image (subpath (vec 0) s a2) UNION path_image p UNION
              path_image (subpath t (vec 1) a2) UNION path_image q) /\
           pl_cell_with_boundary 2 R2 (path_image (subpath s t a2) UNION path_image q) /\
           R1 UNION R0 UNION R2 = std_triangle /\
           R1 INTER R0 = path_image p /\ R0 INTER R2 = path_image q /\
           R1 INTER R2 = {}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC MOI_LM2_T_FACTS THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`std_triangle_loop`; `pathstart (p:real^1->real^2)`;
                 `pathfinish (p:real^1->real^2)`] MOI_SFR_LOOP_SPLIT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `p:real^1->real^2` ARC_DISTINCT_ENDS) THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `path_image p INTER frontier std_triangle =
                 {pathstart p,pathfinish (p:real^1->real^2)}` THEN SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `b1:real^1->real^2` (X_CHOOSE_THEN `b2:real^1->real^2`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`b1:real^1->real^2`; `b2:real^1->real^2`; `p:real^1->real^2`;
                 `frontier std_triangle`;
                 `(path_image b1 UNION path_image p) UNION
                  inside(path_image b1 UNION path_image (p:real^1->real^2))`;
                 `(path_image b2 UNION path_image p) UNION
                  inside(path_image b2 UNION path_image (p:real^1->real^2))`]
    MOI_SFR_THETA) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `path_image (p:real^1->real^2) SUBSET std_triangle` THEN
    UNDISCH_TAC `frontier std_triangle UNION interior std_triangle = std_triangle` THEN
    SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `path_image (q:real^1->real^2)` o last o CONJUNCTS) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[CONNECTED_PATH_IMAGE; ARC_IMP_PATH] THEN
    UNDISCH_TAC `path_image (q:real^1->real^2) SUBSET std_triangle` THEN
    UNDISCH_TAC `frontier std_triangle UNION interior std_triangle = std_triangle` THEN
    UNDISCH_TAC `path_image p INTER path_image q = {}:real^2->bool` THEN SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN DISJ_CASES_TAC THENL
   [SUBGOAL_THEN `path_image b2 INTER path_image b1 = {pathstart p,pathfinish (p:real^1->real^2)} /\
                  path_image b2 UNION path_image b1 = frontier std_triangle`
    STRIP_ASSUME_TAC THENL
     [ONCE_REWRITE_TAC[INTER_COMM; UNION_COMM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`b2:real^1->real^2`; `b1:real^1->real^2`; `p:real^1->real^2`;
                   `q:real^1->real^2`] MOI_LM2_REGIONS_SIDE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `s:real^1` (X_CHOOSE_THEN `t:real^1`
      (X_CHOOSE_THEN `q':real^1->real^2` (X_CHOOSE_THEN `R1:real^2->bool`
      (X_CHOOSE_THEN `R0:real^2->bool` (X_CHOOSE_THEN `R2:real^2->bool`
      STRIP_ASSUME_TAC)))))) THEN
    MAP_EVERY EXISTS_TAC [`b2:real^1->real^2`; `b1:real^1->real^2`; `s:real^1`; `t:real^1`;
                          `q':real^1->real^2`; `R1:real^2->bool`; `R0:real^2->bool`;
                          `R2:real^2->bool`] THEN
    ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`b1:real^1->real^2`; `b2:real^1->real^2`; `p:real^1->real^2`;
                   `q:real^1->real^2`] MOI_LM2_REGIONS_SIDE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `s:real^1` (X_CHOOSE_THEN `t:real^1`
      (X_CHOOSE_THEN `q':real^1->real^2` (X_CHOOSE_THEN `R1:real^2->bool`
      (X_CHOOSE_THEN `R0:real^2->bool` (X_CHOOSE_THEN `R2:real^2->bool`
      STRIP_ASSUME_TAC)))))) THEN
    MAP_EVERY EXISTS_TAC [`b1:real^1->real^2`; `b2:real^1->real^2`; `s:real^1`; `t:real^1`;
                          `q':real^1->real^2`; `R1:real^2->bool`; `R0:real^2->bool`;
                          `R2:real^2->bool`] THEN
    ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* The model rectangle.  MOI_LM2_MR_ARCS (also used in pc_moi_lt_cutb): the  *)
(* four boundary arcs are PL arcs in the frontier and their product is a     *)
(* simple loop onto it.  Then the membership in rectangles, and arc maps (a  *)
(* PL homeomorphism between the images of two PL arcs).                      *)
(* ========================================================================= *)

let MOI_LM2_MR_ARCS = prove
 (`moi_lcus_as = moi_lc0_larc (&0) (&1) /\ moi_lcus_au = moi_lc0_rarc (&2) (&3) /\
   moi_lcus_mr = interval[vector[&0; &0],vector[&3; &1]] /\
   relative_frontier moi_lcus_mr = frontier moi_lcus_mr /\
   polytope moi_lcus_mr /\ convex moi_lcus_mr /\ compact moi_lcus_mr /\
   ~(interior moi_lcus_mr = {}) /\
   arc moi_lcus_as /\ arc moi_lcus_at /\ arc moi_lcus_au /\ arc moi_lcus_av /\
   pl_map_on (interval[vec 0,vec 1]) moi_lcus_as /\
   pl_map_on (interval[vec 0,vec 1]) moi_lcus_at /\
   pl_map_on (interval[vec 0,vec 1]) moi_lcus_au /\
   pl_map_on (interval[vec 0,vec 1]) moi_lcus_av /\
   path_image moi_lcus_as SUBSET relative_frontier moi_lcus_mr /\
   path_image moi_lcus_at SUBSET relative_frontier moi_lcus_mr /\
   path_image moi_lcus_au SUBSET relative_frontier moi_lcus_mr /\
   path_image moi_lcus_av SUBSET relative_frontier moi_lcus_mr /\
   simple_path (moi_lcus_as ++ moi_lcus_at ++ moi_lcus_au ++ moi_lcus_av) /\
   pathfinish (moi_lcus_as ++ moi_lcus_at ++ moi_lcus_au ++ moi_lcus_av) =
   pathstart (moi_lcus_as ++ moi_lcus_at ++ moi_lcus_au ++ moi_lcus_av) /\
   path_image (moi_lcus_as ++ moi_lcus_at ++ moi_lcus_au ++ moi_lcus_av) =
   relative_frontier moi_lcus_mr`,
  SUBGOAL_THEN `moi_lcus_as = moi_lc0_larc (&0) (&1) /\ moi_lcus_au = moi_lc0_rarc (&2) (&3) /\
                moi_lcus_mr = interval[vector[&0; &0],vector[&3; &1]]`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[moi_lcus_as; moi_lcus_au; moi_lc0_larc; moi_lc0_rarc; moi_lcus_mr;
                MOI_LC0_VEC0];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[moi_lcus_at; moi_lcus_av] THEN
  MP_TAC(SPECL [`&0`; `&3`] MOI_LC0_RECT_FACTS) THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (butlast (CONJUNCTS th))) THEN
  MP_TAC(SPECL [`&0`; `&1`; `&2`; `&3`] MOI_LC0_RECT_ARCS) THEN
  MP_TAC(SPECL [`&0`; `&1`] MOI_LC0_LARC) THEN
  MP_TAC(SPECL [`&2`; `&3`] MOI_LC0_RARC) THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (butlast (CONJUNCTS th))) THEN
  DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (butlast (CONJUNCTS th))) THEN
  DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  ASM_REWRITE_TAC[] THEN
  SIMP_TAC[MOI_PL2_PL_LINEPATH; MOI_PL2_LOCALLY_POLYHEDRAL_INTERVAL] THEN
  MP_TAC(ISPECL [`moi_lc0_larc (&0) (&1)`; `linepath(vector[&1; &0]:real^2,vector[&2; &0])`;
                 `moi_lc0_rarc (&2) (&3)`; `linepath(vector[&2; &1]:real^2,vector[&1; &1])`]
    MOI_LC0_FOUR_ARCS) THEN
  ASM_REWRITE_TAC[PATHSTART_LINEPATH; PATHFINISH_LINEPATH] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
    is_comb(lhs(concl th)) && is_comb(rator(lhs(concl th))) &&
    rator(rator(lhs(concl th))) = `(UNION):(real^2->bool)->(real^2->bool)->real^2->bool`)) THEN
  SET_TAC[]);;

let MOI_LM2_IN_RECT = prove
 (`!a b (x:real^2).
     x IN interval[vector[a; &0],vector[b; &1]] <=>
     a <= x$1 /\ x$1 <= b /\ &0 <= x$2 /\ x$2 <= &1`,
  REWRITE_TAC[IN_INTERVAL; DIMINDEX_2; FORALL_2; VECTOR_2] THEN REAL_ARITH_TAC);;

(* An arc map: a PL homeomorphism between the images of two PL arcs        *)
(* sending a(x) to b(x).                                                     *)

let MOI_LM2_ARC_MAP = prove
 (`!(a:real^1->real^M) (b:real^1->real^N).
     arc a /\ pl_map_on (interval[vec 0,vec 1]) a /\
     arc b /\ pl_map_on (interval[vec 0,vec 1]) b
     ==> ?f f'. pl_homeomorphism (path_image a,path_image b) (f,f') /\
                !x. x IN interval[vec 0,vec 1] ==> f(a x) = b x`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `a:real^1->real^M` MOI_PL2_ARC_PL_HOMEOMORPHISM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `ha:real^M->real^1`) THEN
  MP_TAC(ISPEC `b:real^1->real^N` MOI_PL2_ARC_PL_HOMEOMORPHISM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `hb:real^N->real^1`) THEN
  MAP_EVERY EXISTS_TAC [`(b:real^1->real^N) o (ha:real^M->real^1)`;
                        `(a:real^1->real^M) o (hb:real^N->real^1)`] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
    EXISTS_TAC `interval[vec 0:real^1,vec 1]` THEN
    CONJ_TAC THENL
     [ONCE_REWRITE_TAC[PL_HOMEOMORPHISM_SYM] THEN FIRST_ASSUM ACCEPT_TAC;
      FIRST_ASSUM ACCEPT_TAC];
    X_GEN_TAC `x:real^1` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN
    AP_TERM_TAC THEN
    UNDISCH_TAC `pl_homeomorphism (interval[vec 0,vec 1],path_image a)
                   ((a:real^1->real^M),(ha:real^M->real^1))` THEN
    REWRITE_TAC[pl_homeomorphism; homeomorphism] THEN ASM_MESON_TAC[]]);;

(* The union of two PL homeomorphisms agreeing on the overlap, with its     *)
(* values on each piece.                                                     *)

let MOI_LM2_PLH_UNION = prove
 (`!(s1:real^M->bool) s2 (t1:real^N->bool) t2 f1 g1 f2 g2.
     pl_homeomorphism (s1,t1) (f1,g1) /\ pl_homeomorphism (s2,t2) (f2,g2) /\
     closed s1 /\ closed s2 /\ closed t1 /\ closed t2 /\
     (!x. x IN s1 INTER s2 ==> f1 x = f2 x) /\ IMAGE f1 (s1 INTER s2) = t1 INTER t2
     ==> ?h h'. pl_homeomorphism (s1 UNION s2,t1 UNION t2) (h,h') /\
                (!x. x IN s1 ==> h x = f1 x) /\ (!x. x IN s2 ==> h x = f2 x)`,
  REPEAT STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`\x. if x IN s1 then (f1:real^M->real^N) x else f2 x`;
                        `\y. if y IN t1 then (g1:real^N->real^M) y else g2 y`] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC MOI_PL2_PL_HOMEOMORPHISM_UNION THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[] THEN CONJ_TAC THEN X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
    ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]]);;

(* ========================================================================= *)
(* Boundary maps of the three unit squares of the model.                    *)
(* Adding an arc to a PL homeomorphism of closed sets (ARC_ADD); the        *)
(* coordinate descriptions of the model arcs, chords and squares; the      *)
(* boundary maps of S1 = [0,1]x[0,1], S0 = [1,2]x[0,1], S2 = [2,3]x[0,1].  *)
(* ========================================================================= *)

let MOI_LM2_ARC_ADD = prove
 (`!(X:real^M->bool) (Y:real^N->bool) f f' (al:real^1->real^M) (be:real^1->real^N).
     pl_homeomorphism (X,Y) (f,f') /\ closed X /\ closed Y /\
     arc al /\ pl_map_on (interval[vec 0,vec 1]) al /\
     arc be /\ pl_map_on (interval[vec 0,vec 1]) be /\
     path_image al INTER X SUBSET {pathstart al,pathfinish al} /\
     (pathstart al IN X ==> f(pathstart al) = pathstart be) /\
     (pathfinish al IN X ==> f(pathfinish al) = pathfinish be) /\
     path_image be INTER Y = IMAGE f (path_image al INTER X)
     ==> ?h h'. pl_homeomorphism (X UNION path_image al,Y UNION path_image be) (h,h') /\
                (!x. x IN X ==> h x = f x) /\
                (!x. x IN interval[vec 0,vec 1] ==> h(al x) = be x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`al:real^1->real^M`; `be:real^1->real^N`] MOI_LM2_ARC_MAP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `fa:real^M->real^N` (X_CHOOSE_THEN `fa':real^N->real^M`
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "fav")))) THEN
  MP_TAC(ISPECL [`X:real^M->bool`; `path_image(al:real^1->real^M)`; `Y:real^N->bool`;
                 `path_image(be:real^1->real^N)`; `f:real^M->real^N`; `f':real^N->real^M`;
                 `fa:real^M->real^N`; `fa':real^N->real^M`] MOI_LM2_PLH_UNION) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[CLOSED_PATH_IMAGE; ARC_IMP_PATH] THEN CONJ_TAC THENL
     [X_GEN_TAC `y:real^M` THEN REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN
      SUBGOAL_THEN `y = pathstart (al:real^1->real^M) \/ y = pathfinish al`
      STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `path_image al INTER X SUBSET {pathstart (al:real^1->real^M),pathfinish al}` THEN
        UNDISCH_TAC `(y:real^M) IN X` THEN UNDISCH_TAC `(y:real^M) IN path_image al` THEN
        REWRITE_TAC[SUBSET; IN_INTER; IN_INSERT; NOT_IN_EMPTY] THEN MESON_TAC[];
        FIRST_X_ASSUM SUBST_ALL_TAC THEN
        FIRST_X_ASSUM(fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `pathstart (al:real^1->real^M) IN X`)]) THEN
        REWRITE_TAC[pathstart] THEN CONV_TAC SYM_CONV THEN
        USE_THEN "fav" MATCH_MP_TAC THEN REWRITE_TAC[ENDS_IN_UNIT_INTERVAL];
        FIRST_X_ASSUM SUBST_ALL_TAC THEN
        FIRST_X_ASSUM(fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `pathfinish (al:real^1->real^M) IN X`)]) THEN
        REWRITE_TAC[pathfinish] THEN CONV_TAC SYM_CONV THEN
        USE_THEN "fav" MATCH_MP_TAC THEN REWRITE_TAC[ENDS_IN_UNIT_INTERVAL]];
      ONCE_REWRITE_TAC[INTER_COMM] THEN FIRST_ASSUM(ACCEPT_TAC o SYM)];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^M->real^N` (X_CHOOSE_THEN `h':real^N->real^M`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`h:real^M->real^N`; `h':real^N->real^M`] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:real^1` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(al:real^1->real^M) x IN path_image al` ASSUME_TAC THENL
   [REWRITE_TAC[path_image] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `(al:real^1->real^M) x IN path_image al`)]) THEN
  USE_THEN "fav" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC);;

(* Coordinates of the model arcs and squares.                               *)

let MOI_LM2_SQ_FACTS = prove
 (`path_image moi_lcus_as =
     {x:real^2 | x$1 = &0 /\ &0 <= x$2 /\ x$2 <= &1 \/
                 (x$2 = &0 \/ x$2 = &1) /\ &0 <= x$1 /\ x$1 <= &1} /\
   path_image moi_lcus_au =
     {x:real^2 | x$1 = &3 /\ &0 <= x$2 /\ x$2 <= &1 \/
                 (x$2 = &0 \/ x$2 = &1) /\ &2 <= x$1 /\ x$1 <= &3} /\
   path_image moi_lcus_at = {x:real^2 | x$2 = &0 /\ &1 <= x$1 /\ x$1 <= &2} /\
   path_image moi_lcus_av = {x:real^2 | x$2 = &1 /\ &1 <= x$1 /\ x$1 <= &2} /\
   path_image (linepath(vector[&1; &0]:real^2,vector[&1; &1])) =
     {x:real^2 | x$1 = &1 /\ &0 <= x$2 /\ x$2 <= &1} /\
   path_image (linepath(vector[&2; &0]:real^2,vector[&2; &1])) =
     {x:real^2 | x$1 = &2 /\ &0 <= x$2 /\ x$2 <= &1} /\
   (!a b. a < b
          ==> frontier (interval[vector[a; &0],vector[b; &1]]:real^2->bool) =
              {x | a <= x$1 /\ x$1 <= b /\ &0 <= x$2 /\ x$2 <= &1 /\
                   (x$1 = a \/ x$1 = b \/ x$2 = &0 \/ x$2 = &1)})`,
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[MOI_LM2_MR_ARCS] THEN
    MP_TAC(SPECL [`&0`; `&1`] MOI_LC0_LARC) THEN
    CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN SIMP_TAC[];
    REWRITE_TAC[MOI_LM2_MR_ARCS] THEN
    MP_TAC(SPECL [`&2`; `&3`] MOI_LC0_RARC) THEN
    CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN SIMP_TAC[];
    REWRITE_TAC[moi_lcus_at; PATH_IMAGE_LINEPATH] THEN
    MP_TAC(SPECL [`&1`; `&2`; `&0`] MOI_LC0_HSEG) THEN
    CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN SIMP_TAC[];
    REWRITE_TAC[moi_lcus_av; PATH_IMAGE_LINEPATH] THEN
    MP_TAC(SPECL [`&1`; `&2`; `&1`] MOI_LC0_HSEG) THEN
    CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN SIMP_TAC[];
    REWRITE_TAC[PATH_IMAGE_LINEPATH] THEN
    MP_TAC(SPECL [`&0`; `&1`; `&1`] MOI_LC0_VSEG) THEN
    CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN SIMP_TAC[];
    REWRITE_TAC[PATH_IMAGE_LINEPATH] THEN
    MP_TAC(SPECL [`&0`; `&1`; `&2`] MOI_LC0_VSEG) THEN
    CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN SIMP_TAC[];
    SIMP_TAC[MOI_LC0_RECT_FACTS]]);;

(* The set identities of the three squares used below.                     *)

let MOI_LM2_SQ_SETS = prove
 (`frontier(interval[vector[&0; &0],vector[&1; &1]]:real^2->bool) =
     path_image moi_lcus_as UNION path_image (linepath(vector[&1; &0],vector[&1; &1])) /\
   path_image (linepath(vector[&1; &0]:real^2,vector[&1; &1])) INTER path_image moi_lcus_as =
     {vector[&1; &0],vector[&1; &1]} /\
   frontier(interval[vector[&1; &0],vector[&2; &1]]:real^2->bool) =
     ((path_image (linepath(vector[&1; &0],vector[&1; &1])) UNION path_image moi_lcus_at) UNION
      path_image (linepath(vector[&2; &0],vector[&2; &1]))) UNION path_image moi_lcus_av /\
   path_image moi_lcus_at INTER path_image (linepath(vector[&1; &0]:real^2,vector[&1; &1])) =
     {vector[&1; &0]} /\
   path_image (linepath(vector[&2; &0]:real^2,vector[&2; &1])) INTER
     (path_image (linepath(vector[&1; &0],vector[&1; &1])) UNION path_image moi_lcus_at) =
     {vector[&2; &0]} /\
   path_image moi_lcus_av INTER
     ((path_image (linepath(vector[&1; &0]:real^2,vector[&1; &1])) UNION path_image moi_lcus_at)
      UNION path_image (linepath(vector[&2; &0],vector[&2; &1]))) =
     {vector[&2; &1],vector[&1; &1]} /\
   frontier(interval[vector[&2; &0],vector[&3; &1]]:real^2->bool) =
     path_image moi_lcus_au UNION path_image (linepath(vector[&2; &0],vector[&2; &1])) /\
   path_image (linepath(vector[&2; &0]:real^2,vector[&2; &1])) INTER path_image moi_lcus_au =
     {vector[&2; &0],vector[&2; &1]} /\
   interval[vector[&0; &0],vector[&1; &1]] INTER interval[vector[&1; &0],vector[&2; &1]] =
     path_image (linepath(vector[&1; &0]:real^2,vector[&1; &1])) /\
   (interval[vector[&0; &0],vector[&1; &1]] UNION interval[vector[&1; &0],vector[&2; &1]]) INTER
     interval[vector[&2; &0],vector[&3; &1]] =
     path_image (linepath(vector[&2; &0]:real^2,vector[&2; &1])) /\
   (interval[vector[&0; &0],vector[&1; &1]] UNION interval[vector[&1; &0],vector[&2; &1]]) UNION
     interval[vector[&2; &0],vector[&3; &1]] = moi_lcus_mr /\
   relative_frontier moi_lcus_mr =
     path_image moi_lcus_as UNION path_image moi_lcus_at UNION
     path_image moi_lcus_au UNION path_image moi_lcus_av`,
  MP_TAC(CONJUNCT1(CONJUNCT2(CONJUNCT2 MOI_LM2_MR_ARCS))) THEN
  MP_TAC(CONJUNCT1(CONJUNCT2(CONJUNCT2(CONJUNCT2 MOI_LM2_MR_ARCS)))) THEN
  REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[MOI_LM2_SQ_FACTS] THEN
  SUBGOAL_THEN `&0 < &1 /\ &1 < &2 /\ &2 < &3 /\ &0 < &3` STRIP_ASSUME_TAC THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[MOI_LM2_SQ_FACTS] THEN
  REWRITE_TAC[EXTENSION; IN_UNION; IN_INTER; IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY;
              MOI_LM2_IN_RECT; MOI_LC0_VECTOR2_EQ] THEN
  REPEAT CONJ_TAC THEN GEN_TAC THEN REAL_ARITH_TAC);;

(* Arcs, endpoints and cells of the model pieces.                           *)

let MOI_LM2_SQ_ARCS = prove
 (`arc moi_lcus_as /\ arc moi_lcus_at /\ arc moi_lcus_au /\ arc moi_lcus_av /\
   pl_map_on (interval[vec 0,vec 1]) moi_lcus_as /\
   pl_map_on (interval[vec 0,vec 1]) moi_lcus_at /\
   pl_map_on (interval[vec 0,vec 1]) moi_lcus_au /\
   pl_map_on (interval[vec 0,vec 1]) moi_lcus_av /\
   arc (linepath(vector[&1; &0]:real^2,vector[&1; &1])) /\
   pl_map_on (interval[vec 0,vec 1]) (linepath(vector[&1; &0]:real^2,vector[&1; &1])) /\
   arc (linepath(vector[&2; &0]:real^2,vector[&2; &1])) /\
   pl_map_on (interval[vec 0,vec 1]) (linepath(vector[&2; &0]:real^2,vector[&2; &1])) /\
   pathstart moi_lcus_as = vector[&1; &1] /\ pathfinish moi_lcus_as = vector[&1; &0] /\
   pathstart moi_lcus_at = vector[&1; &0] /\ pathfinish moi_lcus_at = vector[&2; &0] /\
   pathstart moi_lcus_au = vector[&2; &0] /\ pathfinish moi_lcus_au = vector[&2; &1] /\
   pathstart moi_lcus_av = vector[&2; &1] /\ pathfinish moi_lcus_av = vector[&1; &1]`,
  REPEAT CONJ_TAC THEN
  TRY(FIRST(map ACCEPT_TAC (CONJUNCTS MOI_LM2_MR_ARCS))) THEN
  TRY(MATCH_MP_TAC MOI_PL2_PL_LINEPATH THEN
      REWRITE_TAC[MOI_PL2_LOCALLY_POLYHEDRAL_INTERVAL] THEN NO_TAC) THEN
  TRY(MATCH_MP_TAC ARC_LINEPATH THEN REWRITE_TAC[MOI_LC0_VECTOR2_INJ] THEN
      REAL_ARITH_TAC) THEN
  REWRITE_TAC[moi_lcus_as; moi_lcus_at; moi_lcus_au; moi_lcus_av; PATHSTART_JOIN;
              PATHFINISH_JOIN; PATHSTART_LINEPATH; PATHFINISH_LINEPATH]);;

let MOI_LM2_SQ_CELL = prove
 (`!a b. a < b
         ==> pl_cell_with_boundary 2 (interval[vector[a; &0],vector[b; &1]]:real^2->bool)
               (frontier(interval[vector[a; &0],vector[b; &1]])) /\
             compact (interval[vector[a; &0],vector[b; &1]]:real^2->bool) /\
             frontier(interval[vector[a; &0],vector[b; &1]]:real^2->bool) SUBSET
             interval[vector[a; &0],vector[b; &1]]`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_LC0_RECT_FACTS) THEN
  DISCH_THEN(fun th -> let ths = CONJUNCTS th in
    ASSUME_TAC(el 0 ths) THEN ASSUME_TAC(el 2 ths) THEN ASSUME_TAC(el 4 ths)) THEN
  ASM_SIMP_TAC[FRONTIER_SUBSET_CLOSED; COMPACT_IMP_CLOSED] THEN
  MP_TAC(ISPEC `interval[vector[a; &0],vector[b; &1]]:real^2->bool` MOI_SFR_POLYGON_CELL) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[AFF_DIM_NONEMPTY_INTERIOR; DIMINDEX_2]; SIMP_TAC[]]);;

let MOI_LM2_ENDS_VALUES = prove
 (`!(f:real^M->real^N) (a:real^1->real^M) b.
     (!x. x IN interval[vec 0,vec 1] ==> f(a x) = b x)
     ==> f(pathstart a) = pathstart b /\ f(pathfinish a) = pathfinish b`,
  REWRITE_TAC[pathstart; pathfinish] THEN MESON_TAC[ENDS_IN_UNIT_INTERVAL]);;

let MOI_LM2_IN_PATH_IMAGE = prove
 (`!(a:real^1->real^N) x. x IN interval[vec 0,vec 1] ==> a x IN path_image a`,
  REWRITE_TAC[path_image] THEN MESON_TAC[FUN_IN_IMAGE]);;

(* The boundary map of S1 = [0,1]x[0,1]: A_s onto bs, the chord x = 1 onto *)
(* c1.                                                                       *)

let MOI_LM2_BD1 = prove
 (`!(bs:real^1->real^2) c1.
     arc bs /\ pl_map_on (interval[vec 0,vec 1]) bs /\
     arc c1 /\ pl_map_on (interval[vec 0,vec 1]) c1 /\
     pathstart bs = pathfinish c1 /\ pathfinish bs = pathstart c1 /\
     path_image bs INTER path_image c1 = {pathstart c1,pathfinish c1}
     ==> ?f f'. pl_homeomorphism (frontier(interval[vector[&0; &0],vector[&1; &1]]),
                                  path_image bs UNION path_image c1) (f,f') /\
                !x. x IN interval[vec 0,vec 1]
                    ==> f(moi_lcus_as x) = bs x /\
                        f(linepath(vector[&1; &0],vector[&1; &1]) x) = c1 x`,
  REPEAT STRIP_TAC THEN
  MP_TAC MOI_LM2_SQ_ARCS THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`moi_lcus_as`; `bs:real^1->real^2`] MOI_LM2_ARC_MAP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `f0:real^2->real^2` (X_CHOOSE_THEN `f0':real^2->real^2`
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "v0")))) THEN
  USE_THEN "v0" (MP_TAC o MATCH_MP MOI_LM2_ENDS_VALUES) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`path_image moi_lcus_as`; `path_image(bs:real^1->real^2)`;
                 `f0:real^2->real^2`; `f0':real^2->real^2`;
                 `linepath(vector[&1; &0]:real^2,vector[&1; &1])`; `c1:real^1->real^2`]
                MOI_LM2_ARC_ADD) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[CLOSED_PATH_IMAGE; ARC_IMP_PATH] THEN
    REWRITE_TAC[el 1 (CONJUNCTS MOI_LM2_SQ_SETS); PATHSTART_LINEPATH; PATHFINISH_LINEPATH;
                IMAGE_CLAUSES; SUBSET_REFL] THEN
    ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[INTER_COMM] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^2->real^2` (X_CHOOSE_THEN `h':real^2->real^2`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "hX") (LABEL_TAC "hal"))))) THEN
  MAP_EVERY EXISTS_TAC [`h:real^2->real^2`; `h':real^2->real^2`] THEN
  ASM_REWRITE_TAC[el 0 (CONJUNCTS MOI_LM2_SQ_SETS)] THEN
  X_GEN_TAC `x:real^1` THEN DISCH_TAC THEN
  USE_THEN "hal" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `x IN interval[vec 0:real^1,vec 1]`)]) THEN
  USE_THEN "hX" (fun th -> REWRITE_TAC[MATCH_MP th (MP (ISPECL [`moi_lcus_as`; `x:real^1`]
    MOI_LM2_IN_PATH_IMAGE) (ASSUME `x IN interval[vec 0:real^1,vec 1]`))]) THEN
  USE_THEN "v0" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC);;

(* The boundary map of S2 = [2,3]x[0,1]: A_u onto bu, the chord x = 2 onto *)
(* c2.                                                                       *)

let MOI_LM2_BD2 = prove
 (`!(bu:real^1->real^2) c2.
     arc bu /\ pl_map_on (interval[vec 0,vec 1]) bu /\
     arc c2 /\ pl_map_on (interval[vec 0,vec 1]) c2 /\
     pathstart bu = pathstart c2 /\ pathfinish bu = pathfinish c2 /\
     path_image c2 INTER path_image bu = {pathstart c2,pathfinish c2}
     ==> ?f f'. pl_homeomorphism (frontier(interval[vector[&2; &0],vector[&3; &1]]),
                                  path_image bu UNION path_image c2) (f,f') /\
                !x. x IN interval[vec 0,vec 1]
                    ==> f(moi_lcus_au x) = bu x /\
                        f(linepath(vector[&2; &0],vector[&2; &1]) x) = c2 x`,
  REPEAT STRIP_TAC THEN
  MP_TAC MOI_LM2_SQ_ARCS THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`moi_lcus_au`; `bu:real^1->real^2`] MOI_LM2_ARC_MAP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `f0:real^2->real^2` (X_CHOOSE_THEN `f0':real^2->real^2`
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "v0")))) THEN
  USE_THEN "v0" (MP_TAC o MATCH_MP MOI_LM2_ENDS_VALUES) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`path_image moi_lcus_au`; `path_image(bu:real^1->real^2)`;
                 `f0:real^2->real^2`; `f0':real^2->real^2`;
                 `linepath(vector[&2; &0]:real^2,vector[&2; &1])`; `c2:real^1->real^2`]
                MOI_LM2_ARC_ADD) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[CLOSED_PATH_IMAGE; ARC_IMP_PATH] THEN
    REWRITE_TAC[el 7 (CONJUNCTS MOI_LM2_SQ_SETS); PATHSTART_LINEPATH; PATHFINISH_LINEPATH;
                IMAGE_CLAUSES; SUBSET_REFL] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^2->real^2` (X_CHOOSE_THEN `h':real^2->real^2`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "hX") (LABEL_TAC "hal"))))) THEN
  MAP_EVERY EXISTS_TAC [`h:real^2->real^2`; `h':real^2->real^2`] THEN
  ASM_REWRITE_TAC[el 6 (CONJUNCTS MOI_LM2_SQ_SETS)] THEN
  X_GEN_TAC `x:real^1` THEN DISCH_TAC THEN
  USE_THEN "hal" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `x IN interval[vec 0:real^1,vec 1]`)]) THEN
  USE_THEN "hX" (fun th -> REWRITE_TAC[MATCH_MP th (MP (ISPECL [`moi_lcus_au`; `x:real^1`]
    MOI_LM2_IN_PATH_IMAGE) (ASSUME `x IN interval[vec 0:real^1,vec 1]`))]) THEN
  USE_THEN "v0" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC);;

(* The boundary map of S0 = [1,2]x[0,1]: the chords onto c1, c2, A_t onto  *)
(* bt and A_v onto bv, added one arc at a time.                              *)

let MOI_LM2_BD0 = prove
 (`!(c1:real^1->real^2) bt c2 bv.
     arc c1 /\ pl_map_on (interval[vec 0,vec 1]) c1 /\
     arc bt /\ pl_map_on (interval[vec 0,vec 1]) bt /\
     arc c2 /\ pl_map_on (interval[vec 0,vec 1]) c2 /\
     arc bv /\ pl_map_on (interval[vec 0,vec 1]) bv /\
     pathstart bt = pathstart c1 /\ pathfinish bt = pathstart c2 /\
     pathstart bv = pathfinish c2 /\ pathfinish bv = pathfinish c1 /\
     path_image c1 INTER path_image bt = {pathstart c1} /\
     path_image bt INTER path_image c2 = {pathstart c2} /\
     path_image c2 INTER path_image bv = {pathfinish c2} /\
     path_image bv INTER path_image c1 = {pathfinish c1} /\
     path_image c1 INTER path_image c2 = {} /\
     path_image bt INTER path_image bv = {}
     ==> ?f f'. pl_homeomorphism (frontier(interval[vector[&1; &0],vector[&2; &1]]),
                  ((path_image c1 UNION path_image bt) UNION path_image c2) UNION path_image bv)
                  (f,f') /\
                !x. x IN interval[vec 0,vec 1]
                    ==> f(linepath(vector[&1; &0],vector[&1; &1]) x) = c1 x /\
                        f(moi_lcus_at x) = bt x /\
                        f(linepath(vector[&2; &0],vector[&2; &1]) x) = c2 x /\
                        f(moi_lcus_av x) = bv x`,
  REPEAT STRIP_TAC THEN
  MP_TAC MOI_LM2_SQ_ARCS THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `~(vector[&2; &0] IN path_image(linepath(vector[&1; &0]:real^2,vector[&1; &1]))) /\
    ~(vector[&2; &1] IN path_image(linepath(vector[&1; &0]:real^2,vector[&1; &1])) UNION
                        path_image moi_lcus_at) /\
    vector[&1; &1] IN path_image(linepath(vector[&1; &0]:real^2,vector[&1; &1]))`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[MOI_LM2_SQ_FACTS; IN_UNION; IN_ELIM_THM; VECTOR_2] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the chord x = 1 *)
  MP_TAC(ISPECL [`linepath(vector[&1; &0]:real^2,vector[&1; &1])`; `c1:real^1->real^2`]
    MOI_LM2_ARC_MAP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `f0:real^2->real^2` (X_CHOOSE_THEN `f0':real^2->real^2`
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "v0")))) THEN
  USE_THEN "v0" (MP_TAC o MATCH_MP MOI_LM2_ENDS_VALUES) THEN
  REWRITE_TAC[ETA_AX; PATHSTART_LINEPATH; PATHFINISH_LINEPATH] THEN STRIP_TAC THEN
  (* add A_t *)
  MP_TAC(ISPECL [`path_image(linepath(vector[&1; &0]:real^2,vector[&1; &1]))`;
                 `path_image(c1:real^1->real^2)`; `f0:real^2->real^2`; `f0':real^2->real^2`;
                 `moi_lcus_at`; `bt:real^1->real^2`] MOI_LM2_ARC_ADD) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[CLOSED_PATH_IMAGE; ARC_IMP_PATH] THEN
    REWRITE_TAC[el 3 (CONJUNCTS MOI_LM2_SQ_SETS); IMAGE_CLAUSES] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_INSERT; NOT_IN_EMPTY] THEN MESON_TAC[];
      ONCE_REWRITE_TAC[INTER_COMM] THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `h1:real^2->real^2` (X_CHOOSE_THEN `h1':real^2->real^2`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "h1X") (LABEL_TAC "h1a"))))) THEN
  USE_THEN "h1a" (MP_TAC o MATCH_MP MOI_LM2_ENDS_VALUES) THEN
  ASM_REWRITE_TAC[ETA_AX] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(h1:real^2->real^2)(vector[&1; &1]) = pathfinish c1` ASSUME_TAC THENL
   [USE_THEN "h1X" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME
      `vector[&1; &1] IN path_image(linepath(vector[&1; &0]:real^2,vector[&1; &1]))`)]) THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  (* add the chord x = 2 *)
  MP_TAC(ISPECL [`path_image(linepath(vector[&1; &0]:real^2,vector[&1; &1])) UNION
                  path_image moi_lcus_at`;
                 `path_image(c1:real^1->real^2) UNION path_image bt`;
                 `h1:real^2->real^2`; `h1':real^2->real^2`;
                 `linepath(vector[&2; &0]:real^2,vector[&2; &1])`; `c2:real^1->real^2`]
                MOI_LM2_ARC_ADD) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[CLOSED_UNION; CLOSED_PATH_IMAGE; ARC_IMP_PATH] THEN
    REWRITE_TAC[el 4 (CONJUNCTS MOI_LM2_SQ_SETS); IMAGE_CLAUSES;
                PATHSTART_LINEPATH; PATHFINISH_LINEPATH] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_INSERT; NOT_IN_EMPTY] THEN MESON_TAC[];
      UNDISCH_TAC `path_image (c1:real^1->real^2) INTER path_image c2 = {}` THEN
      UNDISCH_TAC `path_image (bt:real^1->real^2) INTER path_image c2 = {pathstart c2}` THEN
      SET_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `h2:real^2->real^2` (X_CHOOSE_THEN `h2':real^2->real^2`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "h2X") (LABEL_TAC "h2a"))))) THEN
  USE_THEN "h2a" (MP_TAC o MATCH_MP MOI_LM2_ENDS_VALUES) THEN
  REWRITE_TAC[ETA_AX; PATHSTART_LINEPATH; PATHFINISH_LINEPATH] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(h2:real^2->real^2)(vector[&1; &1]) = pathfinish c1` ASSUME_TAC THENL
   [USE_THEN "h2X" (fun th -> REWRITE_TAC[MATCH_MP th (REWRITE_RULE[GSYM IN_UNION]
      (DISJ1 (ASSUME `vector[&1; &1] IN path_image(linepath(vector[&1; &0]:real^2,vector[&1; &1]))`)
      `vector[&1; &1] IN path_image moi_lcus_at`))]) THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  (* add A_v *)
  MP_TAC(ISPECL [`(path_image(linepath(vector[&1; &0]:real^2,vector[&1; &1])) UNION
                   path_image moi_lcus_at) UNION
                  path_image(linepath(vector[&2; &0]:real^2,vector[&2; &1]))`;
                 `(path_image(c1:real^1->real^2) UNION path_image bt) UNION path_image c2`;
                 `h2:real^2->real^2`; `h2':real^2->real^2`;
                 `moi_lcus_av`; `bv:real^1->real^2`] MOI_LM2_ARC_ADD) THEN
  ANTS_TAC THENL
   [SUBGOAL_THEN
     `closed((path_image(linepath(vector[&1; &0]:real^2,vector[&1; &1])) UNION
              path_image moi_lcus_at) UNION
             path_image(linepath(vector[&2; &0]:real^2,vector[&2; &1]))) /\
      closed((path_image(c1:real^1->real^2) UNION path_image bt) UNION path_image c2)`
    (fun th -> REWRITE_TAC[th]) THENL
     [CONJ_TAC THEN REPEAT(MATCH_MP_TAC CLOSED_UNION THEN CONJ_TAC) THEN
      MATCH_MP_TAC CLOSED_PATH_IMAGE THEN MATCH_MP_TAC ARC_IMP_PATH THEN
      FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[CLOSED_UNION; CLOSED_PATH_IMAGE; ARC_IMP_PATH] THEN
    REWRITE_TAC[el 5 (CONJUNCTS MOI_LM2_SQ_SETS); IMAGE_CLAUSES; SUBSET_REFL] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `path_image (bv:real^1->real^2) INTER path_image c1 = {pathfinish c1}` THEN
    UNDISCH_TAC `path_image (bt:real^1->real^2) INTER path_image bv = {}` THEN
    UNDISCH_TAC `path_image (c2:real^1->real^2) INTER path_image bv = {pathfinish c2}` THEN
    SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `h3:real^2->real^2` (X_CHOOSE_THEN `h3':real^2->real^2`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "h3X") (LABEL_TAC "h3a"))))) THEN
  MAP_EVERY EXISTS_TAC [`h3:real^2->real^2`; `h3':real^2->real^2`] THEN
  ASM_REWRITE_TAC[el 2 (CONJUNCTS MOI_LM2_SQ_SETS)] THEN
  X_GEN_TAC `x:real^1` THEN DISCH_TAC THEN
  MAP_EVERY (fun t -> ASSUME_TAC(MP (ISPECL [t; `x:real^1`] MOI_LM2_IN_PATH_IMAGE)
                        (ASSUME `x IN interval[vec 0:real^1,vec 1]`)))
    [`linepath(vector[&1; &0]:real^2,vector[&1; &1])`; `moi_lcus_at`;
     `linepath(vector[&2; &0]:real^2,vector[&2; &1])`; `moi_lcus_av`] THEN
  REMOVE_THEN "h3X" (fun th -> ASM_SIMP_TAC[IN_UNION; th]) THEN
  REMOVE_THEN "h2X" (fun th -> ASM_SIMP_TAC[IN_UNION; th]) THEN
  REMOVE_THEN "h1X" (fun th -> ASM_SIMP_TAC[IN_UNION; th]));;

(* Points of the model arcs lie on the frontiers of the squares.            *)

let MOI_LM2_SQ_MEMBERS = prove
 (`!x. x IN interval[vec 0,vec 1]
       ==> moi_lcus_as x IN frontier(interval[vector[&0; &0],vector[&1; &1]]) /\
           linepath(vector[&1; &0]:real^2,vector[&1; &1]) x IN
             frontier(interval[vector[&0; &0],vector[&1; &1]]) /\
           linepath(vector[&1; &0]:real^2,vector[&1; &1]) x IN
             frontier(interval[vector[&1; &0],vector[&2; &1]]) /\
           moi_lcus_at x IN frontier(interval[vector[&1; &0],vector[&2; &1]]) /\
           linepath(vector[&2; &0]:real^2,vector[&2; &1]) x IN
             frontier(interval[vector[&1; &0],vector[&2; &1]]) /\
           moi_lcus_av x IN frontier(interval[vector[&1; &0],vector[&2; &1]]) /\
           moi_lcus_au x IN frontier(interval[vector[&2; &0],vector[&3; &1]]) /\
           linepath(vector[&2; &0]:real^2,vector[&2; &1]) x IN
             frontier(interval[vector[&2; &0],vector[&3; &1]]) /\
           moi_lcus_as x IN interval[vector[&0; &0],vector[&1; &1]] /\
           linepath(vector[&1; &0]:real^2,vector[&1; &1]) x IN
             interval[vector[&0; &0],vector[&1; &1]] /\
           linepath(vector[&1; &0]:real^2,vector[&1; &1]) x IN
             interval[vector[&1; &0],vector[&2; &1]] /\
           moi_lcus_at x IN interval[vector[&1; &0],vector[&2; &1]] /\
           linepath(vector[&2; &0]:real^2,vector[&2; &1]) x IN
             interval[vector[&1; &0],vector[&2; &1]] /\
           moi_lcus_av x IN interval[vector[&1; &0],vector[&2; &1]] /\
           moi_lcus_au x IN interval[vector[&2; &0],vector[&3; &1]] /\
           linepath(vector[&2; &0]:real^2,vector[&2; &1]) x IN
             interval[vector[&2; &0],vector[&3; &1]]`,
  GEN_TAC THEN DISCH_TAC THEN
  MAP_EVERY (fun t -> ASSUME_TAC(MP (ISPECL [t; `x:real^1`] MOI_LM2_IN_PATH_IMAGE)
                        (ASSUME `x IN interval[vec 0:real^1,vec 1]`)))
    [`linepath(vector[&1; &0]:real^2,vector[&1; &1])`; `moi_lcus_at`;
     `linepath(vector[&2; &0]:real^2,vector[&2; &1])`; `moi_lcus_av`;
     `moi_lcus_as`; `moi_lcus_au`] THEN
  SUBGOAL_THEN
   `frontier(interval[vector[&0; &0],vector[&1; &1]]:real^2->bool) SUBSET
    interval[vector[&0; &0],vector[&1; &1]] /\
    frontier(interval[vector[&1; &0],vector[&2; &1]]:real^2->bool) SUBSET
    interval[vector[&1; &0],vector[&2; &1]] /\
    frontier(interval[vector[&2; &0],vector[&3; &1]]:real^2->bool) SUBSET
    interval[vector[&2; &0],vector[&3; &1]]`
  MP_TAC THENL
   [SIMP_TAC[MOI_LM2_SQ_CELL; REAL_ARITH `&0 < &1 /\ &1 < &2 /\ &2 < &3`];
    ALL_TAC] THEN
  REWRITE_TAC[el 0 (CONJUNCTS MOI_LM2_SQ_SETS); el 2 (CONJUNCTS MOI_LM2_SQ_SETS);
              el 6 (CONJUNCTS MOI_LM2_SQ_SETS)] THEN
  REWRITE_TAC[SUBSET; IN_UNION] THEN ASM_MESON_TAC[]);;

let MOI_LM2_IMAGE_PATH = prove
 (`!(f:real^M->real^N) (a:real^1->real^M) b.
     (!x. x IN interval[vec 0,vec 1] ==> f(a x) = b x)
     ==> IMAGE f (path_image a) = path_image b`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[path_image; GSYM IMAGE_o] THEN
  MATCH_MP_TAC IMAGE_EQ THEN ASM_REWRITE_TAC[o_THM]);;

(* The model glued: boundary maps of the squares extended to the cells     *)
(* R1, R0, R2 (MOI_LA2_CELL_EXTENSION) and glued along the chords.          *)

let MOI_LM2_GLUE = prove
 (`!(bs:real^1->real^2) bt bu bv c1 c2 R1 R0 R2.
     arc bs /\ pl_map_on (interval[vec 0,vec 1]) bs /\
     arc bt /\ pl_map_on (interval[vec 0,vec 1]) bt /\
     arc bu /\ pl_map_on (interval[vec 0,vec 1]) bu /\
     arc bv /\ pl_map_on (interval[vec 0,vec 1]) bv /\
     arc c1 /\ pl_map_on (interval[vec 0,vec 1]) c1 /\
     arc c2 /\ pl_map_on (interval[vec 0,vec 1]) c2 /\
     pathstart bs = pathfinish c1 /\ pathfinish bs = pathstart c1 /\
     pathstart bt = pathstart c1 /\ pathfinish bt = pathstart c2 /\
     pathstart bu = pathstart c2 /\ pathfinish bu = pathfinish c2 /\
     pathstart bv = pathfinish c2 /\ pathfinish bv = pathfinish c1 /\
     path_image bs INTER path_image c1 = {pathstart c1,pathfinish c1} /\
     path_image c1 INTER path_image bt = {pathstart c1} /\
     path_image bt INTER path_image c2 = {pathstart c2} /\
     path_image c2 INTER path_image bv = {pathfinish c2} /\
     path_image bv INTER path_image c1 = {pathfinish c1} /\
     path_image c1 INTER path_image c2 = {} /\
     path_image bt INTER path_image bv = {} /\
     path_image c2 INTER path_image bu = {pathstart c2,pathfinish c2} /\
     pl_cell_with_boundary 2 R1 (path_image bs UNION path_image c1) /\
     pl_cell_with_boundary 2 R0
       (((path_image c1 UNION path_image bt) UNION path_image c2) UNION path_image bv) /\
     pl_cell_with_boundary 2 R2 (path_image bu UNION path_image c2) /\
     R1 INTER R0 = path_image c1 /\ (R1 UNION R0) INTER R2 = path_image c2
     ==> ?g g'. pl_homeomorphism (moi_lcus_mr,(R1 UNION R0) UNION R2) (g,g') /\
                !x. x IN interval[vec 0,vec 1]
                    ==> g(linepath(vector[&1; &0],vector[&1; &1]) x) = c1 x /\
                        g(linepath(vector[&2; &0],vector[&2; &1]) x) = c2 x /\
                        g(moi_lcus_as x) = bs x /\ g(moi_lcus_at x) = bt x /\
                        g(moi_lcus_au x) = bu x /\ g(moi_lcus_av x) = bv x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  (* boundary maps *)
  MP_TAC(SPECL [`bs:real^1->real^2`; `c1:real^1->real^2`] MOI_LM2_BD1) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `p1:real^2->real^2` (X_CHOOSE_THEN `p1':real^2->real^2`
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "p1v")))) THEN
  MP_TAC(SPECL [`c1:real^1->real^2`; `bt:real^1->real^2`; `c2:real^1->real^2`;
                `bv:real^1->real^2`] MOI_LM2_BD0) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `p0:real^2->real^2` (X_CHOOSE_THEN `p0':real^2->real^2`
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "p0v")))) THEN
  MP_TAC(SPECL [`bu:real^1->real^2`; `c2:real^1->real^2`] MOI_LM2_BD2) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `p2:real^2->real^2` (X_CHOOSE_THEN `p2':real^2->real^2`
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "p2v")))) THEN
  (* the squares as cells *)
  MP_TAC(SPECL [`&0`; `&1`] MOI_LM2_SQ_CELL) THEN
  MP_TAC(SPECL [`&1`; `&2`] MOI_LM2_SQ_CELL) THEN
  MP_TAC(SPECL [`&2`; `&3`] MOI_LM2_SQ_CELL) THEN
  REWRITE_TAC[REAL_ARITH `&0 < &1 /\ &1 < &2 /\ &2 < &3`] THEN
  REPEAT STRIP_TAC THEN
  (* extensions *)
  MP_TAC(ISPECL [`interval[vector[&0; &0],vector[&1; &1]]:real^2->bool`;
                 `frontier(interval[vector[&0; &0],vector[&1; &1]]:real^2->bool)`;
                 `R1:real^2->bool`; `path_image(bs:real^1->real^2) UNION path_image c1`;
                 `p1:real^2->real^2`; `p1':real^2->real^2`] MOI_LA2_CELL_EXTENSION) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `g1:real^2->real^2` (X_CHOOSE_THEN `g1':real^2->real^2`
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "g1v")))) THEN
  MP_TAC(ISPECL [`interval[vector[&1; &0],vector[&2; &1]]:real^2->bool`;
                 `frontier(interval[vector[&1; &0],vector[&2; &1]]:real^2->bool)`;
                 `R0:real^2->bool`;
                 `((path_image(c1:real^1->real^2) UNION path_image bt) UNION path_image c2)
                  UNION path_image bv`;
                 `p0:real^2->real^2`; `p0':real^2->real^2`] MOI_LA2_CELL_EXTENSION) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `g0:real^2->real^2` (X_CHOOSE_THEN `g0':real^2->real^2`
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "g0v")))) THEN
  MP_TAC(ISPECL [`interval[vector[&2; &0],vector[&3; &1]]:real^2->bool`;
                 `frontier(interval[vector[&2; &0],vector[&3; &1]]:real^2->bool)`;
                 `R2:real^2->bool`; `path_image(bu:real^1->real^2) UNION path_image c2`;
                 `p2:real^2->real^2`; `p2':real^2->real^2`] MOI_LA2_CELL_EXTENSION) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `g2:real^2->real^2` (X_CHOOSE_THEN `g2':real^2->real^2`
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "g2v")))) THEN
  SUBGOAL_THEN `compact(R1:real^2->bool) /\ compact(R0:real^2->bool) /\
                compact(R2:real^2->bool)` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC(INST_TYPE [`:2`,`:M`] MOI_PL2_PL_HOMEO_COMPACT) THENL
     [MAP_EVERY EXISTS_TAC [`interval[vector[&0; &0],vector[&1; &1]]:real^2->bool`;
                            `g1:real^2->real^2`; `g1':real^2->real^2`];
      MAP_EVERY EXISTS_TAC [`interval[vector[&1; &0],vector[&2; &1]]:real^2->bool`;
                            `g0:real^2->real^2`; `g0':real^2->real^2`];
      MAP_EVERY EXISTS_TAC [`interval[vector[&2; &0],vector[&3; &1]]:real^2->bool`;
                            `g2:real^2->real^2`; `g2':real^2->real^2`]] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* first glue along the chord x = 1 *)
  MP_TAC(ISPECL [`interval[vector[&0; &0],vector[&1; &1]]:real^2->bool`;
                 `interval[vector[&1; &0],vector[&2; &1]]:real^2->bool`;
                 `R1:real^2->bool`; `R0:real^2->bool`;
                 `g1:real^2->real^2`; `g1':real^2->real^2`;
                 `g0:real^2->real^2`; `g0':real^2->real^2`] MOI_LM2_PLH_UNION) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[COMPACT_IMP_CLOSED; el 8 (CONJUNCTS MOI_LM2_SQ_SETS)] THEN CONJ_TAC THENL
     [REWRITE_TAC[path_image; FORALL_IN_IMAGE] THEN X_GEN_TAC `y:real^1` THEN DISCH_TAC THEN
      MP_TAC(SPEC `y:real^1` MOI_LM2_SQ_MEMBERS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      ASM_SIMP_TAC[];
      MATCH_MP_TAC MOI_LM2_IMAGE_PATH THEN X_GEN_TAC `y:real^1` THEN DISCH_TAC THEN
      MP_TAC(SPEC `y:real^1` MOI_LM2_SQ_MEMBERS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `g10:real^2->real^2` (X_CHOOSE_THEN `g10':real^2->real^2`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "g10a") (LABEL_TAC "g10b"))))) THEN
  (* second glue along the chord x = 2 *)
  MP_TAC(ISPECL [`interval[vector[&0; &0],vector[&1; &1]] UNION
                  interval[vector[&1; &0],vector[&2; &1]]:real^2->bool`;
                 `interval[vector[&2; &0],vector[&3; &1]]:real^2->bool`;
                 `R1 UNION R0:real^2->bool`; `R2:real^2->bool`;
                 `g10:real^2->real^2`; `g10':real^2->real^2`;
                 `g2:real^2->real^2`; `g2':real^2->real^2`] MOI_LM2_PLH_UNION) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[COMPACT_IMP_CLOSED; CLOSED_UNION; el 9 (CONJUNCTS MOI_LM2_SQ_SETS)] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[path_image; FORALL_IN_IMAGE] THEN X_GEN_TAC `y:real^1` THEN DISCH_TAC THEN
      MP_TAC(SPEC `y:real^1` MOI_LM2_SQ_MEMBERS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      ASM_SIMP_TAC[];
      MATCH_MP_TAC MOI_LM2_IMAGE_PATH THEN X_GEN_TAC `y:real^1` THEN DISCH_TAC THEN
      MP_TAC(SPEC `y:real^1` MOI_LM2_SQ_MEMBERS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      ASM_SIMP_TAC[IN_UNION]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^2->real^2` (X_CHOOSE_THEN `g':real^2->real^2`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "ga") (LABEL_TAC "gb"))))) THEN
  MAP_EVERY EXISTS_TAC [`g:real^2->real^2`; `g':real^2->real^2`] THEN
  CONJ_TAC THENL
   [ASM_REWRITE_TAC[GSYM(el 10 (CONJUNCTS MOI_LM2_SQ_SETS))]; ALL_TAC] THEN
  X_GEN_TAC `y:real^1` THEN DISCH_TAC THEN
  MP_TAC(SPEC `y:real^1` MOI_LM2_SQ_MEMBERS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[IN_UNION]);;

(* ========================================================================= *)
(* Values on joined paths, the reversal flags, the winding                  *)
(* number of the reversed boundary loop, and the finishing step: a PL       *)
(* homeomorphism of the model onto T with prescribed values on the model    *)
(* arcs whose boundary loop is homotopic to std_triangle_loop gives the     *)
(* conclusion of LT_MODEL_2D.                                                *)
(* ========================================================================= *)

let MOI_LM2_JOIN_VALUES = prove
 (`!(f:real^M->real^N) (a1:real^1->real^M) a2 b1 b2.
     (!x. x IN interval[vec 0,vec 1] ==> f(a1 x) = b1 x) /\
     (!x. x IN interval[vec 0,vec 1] ==> f(a2 x) = b2 x)
     ==> !x. x IN interval[vec 0,vec 1] ==> f((a1 ++ a2) x) = (b1 ++ b2) x`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "v1") (LABEL_TAC "v2")) THEN
  X_GEN_TAC `x:real^1` THEN DISCH_TAC THEN REWRITE_TAC[joinpaths] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THENL
   [USE_THEN "v1" MATCH_MP_TAC; USE_THEN "v2" MATCH_MP_TAC] THEN
  UNDISCH_TAC `x IN interval[vec 0:real^1,vec 1]` THEN
  POP_ASSUM MP_TAC THEN
  REWRITE_TAC[IN_INTERVAL_1; DROP_CMUL; DROP_SUB; DROP_VEC] THEN REAL_ARITH_TAC);;

let MOI_LM2_FLAG = prove
 (`!(c:real^1->real^N) p.
     (c = p \/ c = reversepath p)
     ==> ?e. !t. c(lift t) = p(lift(if e then &1 - t else t))`,
  REPEAT GEN_TAC THEN DISCH_THEN(DISJ_CASES_THEN SUBST1_TAC) THENL
   [EXISTS_TAC `F` THEN REWRITE_TAC[];
    EXISTS_TAC `T` THEN REWRITE_TAC[reversepath] THEN GEN_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[LIFT_SUB; LIFT_NUM]]);;

let MOI_LM2_WN_REVERSE4 = prove
 (`!(a:real^1->real^2) x y w z.
     path a /\ path x /\ path y /\ path w /\
     pathstart x = pathstart a /\ pathfinish x = pathstart y /\
     pathfinish y = pathstart w /\ pathfinish w = pathfinish a /\
     ~(z IN path_image a) /\ ~(z IN path_image x) /\
     ~(z IN path_image y) /\ ~(z IN path_image w)
     ==> winding_number(a ++ reversepath w ++ reversepath y ++ reversepath x,z) =
         --winding_number(reversepath a ++ x ++ y ++ w,z)`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[WINDING_NUMBER_JOIN; PATH_JOIN; PATH_IMAGE_JOIN; PATHSTART_JOIN;
               PATHFINISH_JOIN; IN_UNION; PATH_REVERSEPATH; PATH_IMAGE_REVERSEPATH;
               PATHSTART_REVERSEPATH; PATHFINISH_REVERSEPATH;
               WINDING_NUMBER_REVERSEPATH] THEN
  CONV_TAC COMPLEX_RING);;

(* The finishing step.                                                      *)

let MOI_LM2_FINISH = prove
 (`!(g:real^2->real^2) g' (p:real^1->real^2) q bs bt bu bv c1 c2.
     pl_homeomorphism (moi_lcus_mr,std_triangle) (g,g') /\
     (!x. x IN interval[vec 0,vec 1]
          ==> g(linepath(vector[&1; &0],vector[&1; &1]) x) = c1 x /\
              g(linepath(vector[&2; &0],vector[&2; &1]) x) = c2 x /\
              g(moi_lcus_as x) = bs x /\ g(moi_lcus_at x) = bt x /\
              g(moi_lcus_au x) = bu x /\ g(moi_lcus_av x) = bv x) /\
     (c1 = p \/ c1 = reversepath p) /\ (c2 = q \/ c2 = reversepath q) /\
     path_image bs UNION path_image bt UNION path_image bu UNION path_image bv =
     frontier std_triangle /\
     homotopic_loops (frontier std_triangle) std_triangle_loop (bs ++ bt ++ bu ++ bv)
     ==> ?e1 e2.
           pl_homeomorphism (moi_lcus_mr,std_triangle) (g,g') /\
           IMAGE g (relative_frontier moi_lcus_mr) = relative_frontier std_triangle /\
           (!t. &0 <= t /\ t <= &1
                ==> g(vector[&1; t]) = p(lift(if e1 then &1 - t else t)) /\
                    g(vector[&2; t]) = q(lift(if e2 then &1 - t else t))) /\
           homotopic_loops (relative_frontier std_triangle) std_triangle_loop
             (g o (moi_lcus_as ++ moi_lcus_at ++ moi_lcus_au ++ moi_lcus_av))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "gv")
    (CONJUNCTS_THEN2 (X_CHOOSE_TAC `e1:bool` o MATCH_MP MOI_LM2_FLAG)
    (CONJUNCTS_THEN2 (X_CHOOSE_TAC `e2:bool` o MATCH_MP MOI_LM2_FLAG)
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "hom")))))) THEN
  MAP_EVERY EXISTS_TAC [`e1:bool`; `e2:bool`] THEN
  ASM_REWRITE_TAC[el 6 (CONJUNCTS MOI_LM2_T_FACTS)] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[el 11 (CONJUNCTS MOI_LM2_SQ_SETS); IMAGE_UNION] THEN
    SUBGOAL_THEN
     `IMAGE (g:real^2->real^2) (path_image moi_lcus_as) = path_image bs /\
      IMAGE g (path_image moi_lcus_at) = path_image bt /\
      IMAGE g (path_image moi_lcus_au) = path_image bu /\
      IMAGE g (path_image moi_lcus_av) = path_image bv`
    (fun th -> REWRITE_TAC[th]) THENL
     [REPEAT CONJ_TAC THEN MATCH_MP_TAC MOI_LM2_IMAGE_PATH THEN
      USE_THEN "gv" (fun th -> MESON_TAC[th]);
      ASM_REWRITE_TAC[]];
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `vector[&1; t]:real^2 = linepath(vector[&1; &0],vector[&1; &1]) (lift t) /\
                  vector[&2; t]:real^2 = linepath(vector[&2; &0],vector[&2; &1]) (lift t)`
    (fun th -> REWRITE_TAC[th]) THENL
     [REWRITE_TAC[linepath; LIFT_DROP; CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2;
                  VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `lift t IN interval[vec 0,vec 1]` ASSUME_TAC THENL
     [REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP; DROP_VEC] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    USE_THEN "gv" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `lift t IN interval[vec 0,vec 1]`)]) THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC HOMOTOPIC_LOOPS_TRANS THEN
    EXISTS_TAC `(bs:real^1->real^2) ++ bt ++ bu ++ bv` THEN
    USE_THEN "hom" (fun th -> REWRITE_TAC[th]) THEN
    MATCH_MP_TAC HOMOTOPIC_LOOPS_EQ THEN
    USE_THEN "hom" (fun th -> REWRITE_TAC[MATCH_MP HOMOTOPIC_LOOPS_IMP_PATH th;
      MATCH_MP HOMOTOPIC_LOOPS_IMP_SUBSET th; MATCH_MP HOMOTOPIC_LOOPS_IMP_LOOP th]) THEN
    X_GEN_TAC `x:real^1` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN
    CONV_TAC SYM_CONV THEN UNDISCH_TAC `x IN interval[vec 0:real^1,vec 1]` THEN
    SPEC_TAC(`x:real^1`,`x:real^1`) THEN
    REPEAT(MATCH_MP_TAC MOI_LM2_JOIN_VALUES THEN CONJ_TAC) THEN
    USE_THEN "gv" (fun th -> MESON_TAC[th])]);;

(* The intersection pattern of the pieces: a1, the three pieces X, Y, Z of  *)
(* a2 (from pathstart p over S0, T0 to pathfinish p) and the crosscuts p,  *)
(* q with ends P0, P1 and S0, T0.                                           *)

let MOI_LM2_SETS = prove
 (`!(A1:real^N->bool) PX PY PZ PP PQ FT P0 P1 S0 T0.
     A1 UNION (PX UNION PY UNION PZ) = FT /\
     A1 INTER (PX UNION PY UNION PZ) = {P0,P1} /\
     PP INTER FT = {P0,P1} /\ PQ INTER FT = {S0,T0} /\ PP INTER PQ = {} /\
     P0 IN PX /\ P1 IN PZ /\ S0 IN PX /\ S0 IN PY /\ T0 IN PY /\ T0 IN PZ /\
     P0 IN PP /\ P1 IN PP /\ S0 IN PQ /\ T0 IN PQ /\
     PX INTER PY = {S0} /\ PY INTER PZ = {T0} /\ PX INTER PZ = {}
     ==> A1 INTER PP = {P0,P1} /\
         PP INTER PX = {P0} /\ PX INTER PP = {P0} /\
         PX INTER PQ = {S0} /\ PQ INTER PX = {S0} /\
         PQ INTER PZ = {T0} /\ PZ INTER PQ = {T0} /\
         PZ INTER PP = {P1} /\ PP INTER PZ = {P1} /\
         PZ INTER PX = {} /\ PQ INTER PY = {S0,T0} /\
         A1 INTER PX = {P0} /\ PZ INTER A1 = {P1} /\ A1 INTER PY = {} /\
         A1 UNION PZ UNION PY UNION PX = FT /\
         ((PP UNION PX) UNION PQ) UNION PZ = PX UNION PP UNION PZ UNION PQ /\
         ((PP UNION PZ) UNION PQ) UNION PX = PX UNION PP UNION PZ UNION PQ`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(P0:real^N = S0) /\ ~(P0 = T0) /\ ~(P1:real^N = S0) /\ ~(P1 = T0)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `PP INTER PQ:real^N->bool = {}` THEN
    MAP_EVERY UNDISCH_TAC [`(P0:real^N) IN PP`; `(P1:real^N) IN PP`;
                           `(S0:real^N) IN PQ`; `(T0:real^N) IN PQ`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((P0:real^N) IN PY) /\ ~(P0 IN PZ) /\ ~((P1:real^N) IN PX) /\ ~(P1 IN PY) /\
                ~((S0:real^N) IN PZ) /\ ~((T0:real^N) IN PX)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`PX INTER PY:real^N->bool = {S0}`; `PY INTER PZ:real^N->bool = {T0}`;
      `PX INTER PZ:real^N->bool = {}`; `(P0:real^N) IN PX`; `(P1:real^N) IN PZ`;
      `(S0:real^N) IN PX`; `(T0:real^N) IN PZ`] THEN
    MAP_EVERY UNDISCH_TAC [`~(P0:real^N = S0)`; `~(P0:real^N = T0)`;
                           `~(P1:real^N = S0)`; `~(P1:real^N = T0)`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THEN ASM SET_TAC[]);;

(* ========================================================================= *)
(* The main theorem LT_MODEL_2D (its statement is the antecedent             *)
(* MOI_LCU_MODEL2D of pc_moi_lt_cutb).  REGIONS gives the cells; GLUE gives  *)
(* two PL homeomorphisms g1, g2 of the model onto T, the second with all     *)
(* boundary pieces reversed; the winding numbers of their boundary loops are *)
(* opposite, so one of them is that of std_triangle_loop                     *)
(* (MOI_LC0_CONVEX_LOOPS_WN); FINISH concludes.                              *)
(* ========================================================================= *)

let LT_MODEL_2D = prove
 (`!(p:real^1->real^2) (q:real^1->real^2).
     arc p /\ pl_map_on (interval[vec 0,vec 1]) p /\
     arc q /\ pl_map_on (interval[vec 0,vec 1]) q /\
     path_image p SUBSET std_triangle /\ path_image q SUBSET std_triangle /\
     path_image p INTER relative_frontier std_triangle = {pathstart p,pathfinish p} /\
     path_image q INTER relative_frontier std_triangle = {pathstart q,pathfinish q} /\
     path_image p INTER path_image q = {}
     ==> ?g g' e1 e2.
           pl_homeomorphism (moi_lcus_mr,std_triangle) (g,g') /\
           IMAGE g (relative_frontier moi_lcus_mr) = relative_frontier std_triangle /\
           (!t. &0 <= t /\ t <= &1
                ==> g(vector[&1; t]) = p(lift(if e1 then &1 - t else t)) /\
                    g(vector[&2; t]) = q(lift(if e2 then &1 - t else t))) /\
           homotopic_loops (relative_frontier std_triangle) std_triangle_loop
             (g o (moi_lcus_as ++ moi_lcus_at ++ moi_lcus_au ++ moi_lcus_av))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[el 6 (CONJUNCTS MOI_LM2_T_FACTS)]) THEN
  MP_TAC(SPECL [`p:real^1->real^2`; `q:real^1->real^2`] MOI_LM2_REGIONS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `a1:real^1->real^2` (X_CHOOSE_THEN `a2:real^1->real^2`
    (X_CHOOSE_THEN `s1:real^1` (X_CHOOSE_THEN `t1:real^1`
    (X_CHOOSE_THEN `q':real^1->real^2` (X_CHOOSE_THEN `R1:real^2->bool`
    (X_CHOOSE_THEN `R0:real^2->bool` (X_CHOOSE_THEN `R2:real^2->bool`
    (fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)))))))))) THEN
  MP_TAC(ISPECL [`a2:real^1->real^2`; `s1:real^1`; `t1:real^1`] MOI_LM2_ARC_THREE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  (* the crosscut q' *)
  SUBGOAL_THEN
   `arc (q':real^1->real^2) /\ pl_map_on (interval[vec 0,vec 1]) q' /\
    path_image q' = path_image q /\
    {pathstart q,pathfinish q} = {(a2:real^1->real^2) s1,a2 t1}`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ASSUME `pathstart (q':real^1->real^2) = a2 (s1:real^1)`) THEN
    MP_TAC(ASSUME `pathfinish (q':real^1->real^2) = a2 (t1:real^1)`) THEN
    MP_TAC(ASSUME `q' = q \/ q' = reversepath (q:real^1->real^2)`) THEN
    DISCH_THEN(DISJ_CASES_THEN SUBST1_TAC) THEN
    REWRITE_TAC[PATH_IMAGE_REVERSEPATH; PATHSTART_REVERSEPATH; PATHFINISH_REVERSEPATH] THEN
    REPEAT DISCH_TAC THEN ASM_SIMP_TAC[ARC_REVERSEPATH; MOI_PL2_PL_REVERSEPATH] THEN
    REWRITE_TAC[INSERT_AC];
    ALL_TAC] THEN
  SUBGOAL_THEN `reversepath q' = q \/ reversepath q' = reversepath (q:real^1->real^2)`
  ASSUME_TAC THENL
   [MP_TAC(ASSUME `q' = q \/ q' = reversepath (q:real^1->real^2)`) THEN
    DISCH_THEN(DISJ_CASES_THEN SUBST1_TAC) THEN REWRITE_TAC[REVERSEPATH_REVERSEPATH];
    ALL_TAC] THEN
  MAP_EVERY (fun t -> MP_TAC(CONJ (ISPEC t PATHSTART_IN_PATH_IMAGE)
                                  (ISPEC t PATHFINISH_IN_PATH_IMAGE)) THEN
                      ASM_REWRITE_TAC[] THEN STRIP_TAC)
    [`subpath (vec 0) s1 (a2:real^1->real^2)`; `subpath s1 t1 (a2:real^1->real^2)`;
     `subpath t1 (vec 1) (a2:real^1->real^2)`; `p:real^1->real^2`; `q':real^1->real^2`] THEN
  (* the intersection pattern *)
  MP_TAC(ISPECL [`path_image(a1:real^1->real^2)`;
                 `path_image(subpath (vec 0) s1 (a2:real^1->real^2))`;
                 `path_image(subpath s1 t1 (a2:real^1->real^2))`;
                 `path_image(subpath t1 (vec 1) (a2:real^1->real^2))`;
                 `path_image(p:real^1->real^2)`; `path_image(q:real^1->real^2)`;
                 `frontier std_triangle:real^2->bool`;
                 `pathstart(p:real^1->real^2)`; `pathfinish(p:real^1->real^2)`;
                 `(a2:real^1->real^2) s1`; `(a2:real^1->real^2) t1`] MOI_LM2_SETS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[];
    DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th))] THEN
  (* the first map: boundary pieces rev a1, X, Y, Z; chords p, q' *)
  MP_TAC(ISPECL [`reversepath a1:real^1->real^2`; `subpath (vec 0) s1 (a2:real^1->real^2)`;
                 `subpath s1 t1 (a2:real^1->real^2)`; `subpath t1 (vec 1) (a2:real^1->real^2)`;
                 `p:real^1->real^2`; `q':real^1->real^2`;
                 `R1:real^2->bool`; `R0:real^2->bool`; `R2:real^2->bool`] MOI_LM2_GLUE) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[ARC_REVERSEPATH; MOI_PL2_PL_REVERSEPATH; PATH_IMAGE_REVERSEPATH;
                 PATHSTART_REVERSEPATH; PATHFINISH_REVERSEPATH] THEN
    MP_TAC(ASSUME `R0 INTER R2 = path_image (q:real^1->real^2)`) THEN
    MP_TAC(ASSUME `R1 INTER R2:real^2->bool = {}`) THEN SET_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `g1:real^2->real^2` (X_CHOOSE_THEN `g1':real^2->real^2`
      (CONJUNCTS_THEN2 (ASSUME_TAC o REWRITE_RULE[UNION_ASSOC;
         ASSUME `R1 UNION R0 UNION R2:real^2->bool = std_triangle`]) (LABEL_TAC "g1v"))))] THEN
  (* the second map: everything reversed *)
  MP_TAC(ISPECL [`a1:real^1->real^2`; `reversepath(subpath t1 (vec 1) (a2:real^1->real^2))`;
                 `reversepath(subpath s1 t1 (a2:real^1->real^2))`;
                 `reversepath(subpath (vec 0) s1 (a2:real^1->real^2))`;
                 `reversepath p:real^1->real^2`; `reversepath q':real^1->real^2`;
                 `R1:real^2->bool`; `R0:real^2->bool`; `R2:real^2->bool`] MOI_LM2_GLUE) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[ARC_REVERSEPATH; MOI_PL2_PL_REVERSEPATH; PATH_IMAGE_REVERSEPATH;
                 PATHSTART_REVERSEPATH; PATHFINISH_REVERSEPATH] THEN
    REWRITE_TAC[INSERT_AC] THEN
    MP_TAC(ASSUME `R0 INTER R2 = path_image (q:real^1->real^2)`) THEN
    MP_TAC(ASSUME `R1 INTER R2:real^2->bool = {}`) THEN SET_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `g2:real^2->real^2` (X_CHOOSE_THEN `g2':real^2->real^2`
      (CONJUNCTS_THEN2 (ASSUME_TAC o REWRITE_RULE[UNION_ASSOC;
         ASSUME `R1 UNION R0 UNION R2:real^2->bool = std_triangle`]) (LABEL_TAC "g2v"))))] THEN
  (* winding numbers about a point z of the interior *)
  MP_TAC(el 5 (CONJUNCTS MOI_LM2_T_FACTS)) THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
  DISCH_THEN(X_CHOOSE_TAC `z:real^2`) THEN
  SUBGOAL_THEN `~((z:real^2) IN frontier std_triangle)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[frontier; IN_DIFF]; ALL_TAC] THEN
  SUBGOAL_THEN
   `~((z:real^2) IN path_image a1) /\
    ~(z IN path_image (subpath (vec 0) s1 (a2:real^1->real^2))) /\
    ~(z IN path_image (subpath s1 t1 (a2:real^1->real^2))) /\
    ~(z IN path_image (subpath t1 (vec 1) (a2:real^1->real^2)))`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ASSUME `~((z:real^2) IN frontier std_triangle)`) THEN
    MP_TAC(ASSUME `path_image a1 UNION path_image (a2:real^1->real^2) =
                   frontier std_triangle`) THEN
    MP_TAC(ASSUME `path_image (subpath (vec 0) s1 a2) UNION path_image (subpath s1 t1 a2) UNION
                   path_image (subpath t1 (vec 1) (a2:real^1->real^2)) = path_image a2`) THEN
    SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`reversepath a1:real^1->real^2`; `subpath (vec 0) s1 (a2:real^1->real^2)`;
                 `subpath s1 t1 (a2:real^1->real^2)`; `subpath t1 (vec 1) (a2:real^1->real^2)`]
                MOI_LC0_FOUR_ARCS) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[ARC_REVERSEPATH; PATH_IMAGE_REVERSEPATH; PATHSTART_REVERSEPATH;
                 PATHFINISH_REVERSEPATH];
    STRIP_TAC] THEN
  MP_TAC(ISPECL [`std_triangle:real^2->bool`; `z:real^2`; `std_triangle_loop`]
                MOI_LC0_SIMPLE_LOOP_WN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[MOI_LM2_T_FACTS]; DISCH_TAC] THEN
  MP_TAC(ISPECL [`std_triangle:real^2->bool`; `z:real^2`;
                 `reversepath a1 ++ subpath (vec 0) s1 a2 ++ subpath s1 t1 a2 ++
                  subpath t1 (vec 1) (a2:real^1->real^2)`] MOI_LC0_SIMPLE_LOOP_WN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[MOI_LM2_T_FACTS; PATH_IMAGE_REVERSEPATH]; DISCH_TAC] THEN
  MP_TAC(ISPECL [`a1:real^1->real^2`; `subpath (vec 0) s1 (a2:real^1->real^2)`;
                 `subpath s1 t1 (a2:real^1->real^2)`; `subpath t1 (vec 1) (a2:real^1->real^2)`;
                 `z:real^2`] MOI_LM2_WN_REVERSE4) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[ARC_IMP_PATH]; DISCH_TAC] THEN
  ASM_CASES_TAC
   `winding_number(reversepath a1 ++ subpath (vec 0) s1 a2 ++ subpath s1 t1 a2 ++
                   subpath t1 (vec 1) (a2:real^1->real^2),z) =
    winding_number(std_triangle_loop,z)` THENL
   [MAP_EVERY EXISTS_TAC [`g1:real^2->real^2`; `g1':real^2->real^2`] THEN
    MATCH_MP_TAC MOI_LM2_FINISH THEN
    MAP_EVERY EXISTS_TAC
     [`reversepath a1:real^1->real^2`; `subpath (vec 0) s1 (a2:real^1->real^2)`;
      `subpath s1 t1 (a2:real^1->real^2)`; `subpath t1 (vec 1) (a2:real^1->real^2)`;
      `p:real^1->real^2`; `q':real^1->real^2`] THEN
    ASM_REWRITE_TAC[PATH_IMAGE_REVERSEPATH] THEN
    MP_TAC(ISPECL [`std_triangle:real^2->bool`; `z:real^2`; `std_triangle_loop`;
                   `reversepath a1 ++ subpath (vec 0) s1 a2 ++ subpath s1 t1 a2 ++
                    subpath t1 (vec 1) (a2:real^1->real^2)`] MOI_LC0_CONVEX_LOOPS_WN) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[MOI_LM2_T_FACTS; SIMPLE_PATH_IMP_PATH; SUBSET_REFL; PATH_IMAGE_REVERSEPATH];
      DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]];
    MAP_EVERY EXISTS_TAC [`g2:real^2->real^2`; `g2':real^2->real^2`] THEN
    MATCH_MP_TAC MOI_LM2_FINISH THEN
    MAP_EVERY EXISTS_TAC
     [`a1:real^1->real^2`; `reversepath(subpath t1 (vec 1) (a2:real^1->real^2))`;
      `reversepath(subpath s1 t1 (a2:real^1->real^2))`;
      `reversepath(subpath (vec 0) s1 (a2:real^1->real^2))`;
      `reversepath p:real^1->real^2`; `reversepath q':real^1->real^2`] THEN
    ASM_REWRITE_TAC[PATH_IMAGE_REVERSEPATH] THEN
    MP_TAC(ISPECL [`std_triangle:real^2->bool`; `z:real^2`; `std_triangle_loop`;
                   `a1 ++ reversepath(subpath t1 (vec 1) a2) ++
                    reversepath(subpath s1 t1 a2) ++
                    reversepath(subpath (vec 0) s1 (a2:real^1->real^2))`]
                  MOI_LC0_CONVEX_LOOPS_WN) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[MOI_LM2_T_FACTS; SIMPLE_PATH_IMP_PATH; SUBSET_REFL; PATH_JOIN;
                   PATH_IMAGE_JOIN; PATHSTART_JOIN; PATHFINISH_JOIN; PATH_REVERSEPATH;
                   PATH_IMAGE_REVERSEPATH; PATHSTART_REVERSEPATH; PATHFINISH_REVERSEPATH;
                   ARC_IMP_PATH];
      DISCH_THEN SUBST1_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOI_LC0_UNIT_SIGNS THEN
    ASM_REWRITE_TAC[]]);;

