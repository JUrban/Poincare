(* ========================================================================= *)
(* pc_moi_s35_fina: the Sec 35 unit s35_fin_a, main theorem FINAL_CELLS =   *)
(* MOI_S35_FINAL_CELLS (pc_moi_s35_stmt.ml, section 7): after the circle    *)
(* removal the final cells D_v (the cell X_v minus the interiors of the     *)
(* A-cells of its B-side edges) are PL 3-balls meeting in the planar disks  *)
(* along edges only.  Method: sphere surgery (MOI_S5F_CUT_BALL: cutting the *)
(* interior of a PL 3-ball Y out of a PL 3-ball X leaves a PL 3-ball when   *)
(* the frontier of Y meets X in a 2-cell bounded by the circle of the two   *)
(* frontiers; SPHERE_SPLIT, DISK_UNION, MOI_S5C_FILL_CHAR, PL Schoenflies), *)
(* iterated over the finitely many B-side edges of a vertex                 *)
(* (MOI_S5F_MULTI_CUT), and the frame clauses of moi_s35_post.  Moise GTM   *)
(* 47, p.251.                                                               *)
(* ========================================================================= *)

needs "src/pc_moi_s35_ext.ml";;
needs "src/pc_moi_s35_cells.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* 1. Topology of PL 3-balls and 2-cells: interior, closure and complement  *)
(* of a PL 3-ball, the frontier of a closed set minus an open set, and a    *)
(* 2-cell is neither a 2-sphere nor its own boundary.                        *)
(* ------------------------------------------------------------------------- *)

let MOI_S5F_SUBSET_OUTSIDE = prove
 (`!c s:real^N->bool.
     connected c /\ ~bounded c /\ c INTER s = {} ==> c SUBSET outside s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SUBSET; outside; IN_ELIM_THM] THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN CONJ_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_TAC THEN UNDISCH_TAC `~bounded(c:real^N->bool)` THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC BOUNDED_SUBSET THEN
  EXISTS_TAC `connected_component ((:real^N) DIFF s) x` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONNECTED_COMPONENT_MAXIMAL THEN
  ASM SET_TAC[]);;

let MOI_S5F_FRONTIER_DIFF_OPEN = prove
 (`!x u:real^N->bool.
     closed x /\ open u
     ==> frontier(x DIFF u) = (frontier x DIFF u) UNION (x INTER frontier u)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `x DIFF u = x INTER ((:real^N) DIFF u)` SUBST1_TAC THENL
   [SET_TAC[]; ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) FRONTIER_INTER_CLOSED o lhand o snd) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[GSYM OPEN_CLOSED]; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[FRONTIER_COMPLEMENT] THEN SET_TAC[]);;

let MOI_S5F_BALL_FACTS = prove
 (`!x:real^3->bool.
     pl_ball 3 x
     ==> compact x /\ closed x /\ pl_sphere 2 (frontier x) /\
         interior x = inside(frontier x) /\
         frontier x UNION inside(frontier x) = x /\
         x DIFF interior x = frontier x /\
         frontier(interior x) = frontier x /\
         closure(interior x) = x /\
         ~(interior x = {}) /\ connected(interior x) /\ open(interior x) /\
         (:real^3) DIFF x = outside(frontier x) /\
         connected(outside(frontier x)) /\ ~bounded(outside(frontier x)) /\
         DISJOINT x (outside(frontier x))`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_S5C_PL_BALL_3_FILL) THEN
  ABBREV_TAC `s = frontier(x:real^3->bool)` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o SYM)))) THEN
  MP_TAC(ISPEC `s:real^3->bool` MOI_S5C_PLSPH_JB) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN
  REWRITE_TAC[CLOSURE_UNION_FRONTIER] THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `DISJOINT (s:real^3->bool) (inside s)` THEN
    UNDISCH_TAC `s UNION inside s:real^3->bool = x` THEN SET_TAC[];
    UNDISCH_TAC `s UNION inside s:real^3->bool = x` THEN SET_TAC[];
    MAP_EVERY UNDISCH_TAC
     [`s UNION inside s:real^3->bool = x`;
      `inside s INTER outside s:real^3->bool = {}`;
      `inside s UNION outside s = (:real^3) DIFF s`;
      `DISJOINT (s:real^3->bool) (outside s)`] THEN SET_TAC[];
    MAP_EVERY UNDISCH_TAC
     [`s UNION inside s:real^3->bool = x`;
      `inside s INTER outside s:real^3->bool = {}`;
      `DISJOINT (s:real^3->bool) (outside s)`] THEN SET_TAC[]]);;

let MOI_S5F_DIFF_INTERIOR = prove
 (`!x y:real^3->bool.
     closed x /\ pl_ball 3 y
     ==> closed(x DIFF interior y) /\
         interior(x DIFF interior y) = interior x DIFF y /\
         frontier(x DIFF interior y) =
         (frontier x DIFF interior y) UNION (x INTER frontier y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `closure(interior y) = (y:real^3->bool) /\
                frontier(interior y) = frontier y`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[MOI_S5F_BALL_FACTS]; ALL_TAC] THEN
  ASM_SIMP_TAC[CLOSED_DIFF; OPEN_INTERIOR; MOI_S5F_FRONTIER_DIFF_OPEN] THEN
  SUBGOAL_THEN `x DIFF interior y = x INTER ((:real^3) DIFF interior y)` SUBST1_TAC THENL
   [SET_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[INTERIOR_INTER; INTERIOR_COMPLEMENT] THEN SET_TAC[]);;

let MOI_S5F_CELL_NOT_SPHERE = prove
 (`!d j:real^3->bool. pl_cell_with_boundary 2 d j ==> ~pl_sphere 2 d`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^3->bool` (X_CHOOSE_THEN `f:real^3->real^3`
    (X_CHOOSE_THEN `g:real^3->real^3` STRIP_ASSUME_TAC)) o
    MATCH_MP MOI_SS2_CELL_FACTS) THEN
  SUBGOAL_THEN `contractible(d:real^3->bool)` MP_TAC THENL
   [MATCH_MP_TAC(ISPECL [`k:real^3->bool`; `d:real^3->bool`] HOMEOMORPHIC_CONTRACTIBLE) THEN
    CONJ_TAC THENL
     [REWRITE_TAC[homeomorphic] THEN
      MAP_EVERY EXISTS_TAC [`f:real^3->real^3`; `g:real^3->real^3`] THEN
      ASM_MESON_TAC[pl_homeomorphism];
      MATCH_MP_TAC CONVEX_IMP_CONTRACTIBLE THEN ASM_MESON_TAC[SIMPLEX_IMP_CONVEX]];
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP MOI_SCD_PL_SPHERE_2_HOMEOMORPHIC) THEN
  DISCH_THEN(MP_TAC o MATCH_MP HOMEOMORPHIC_CONTRACTIBLE_EQ) THEN
  ASM_REWRITE_TAC[CONTRACTIBLE_SPHERE] THEN REAL_ARITH_TAC);;

let MOI_S5F_CELL_NOT_BOUNDARY = prove
 (`!d j:real^3->bool. pl_cell_with_boundary 2 d j ==> j SUBSET d /\ ~(d SUBSET j)`,
  REPEAT GEN_TAC THEN DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP MOI_SS2_CELL_FACTS) THEN
  ASM SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* 2. Sphere surgery.  If the frontier of a PL 3-ball y meets a PL 3-ball x  *)
(* in a 2-cell d bounded by the circle j where the two frontiers meet, then  *)
(* x minus the interior of y is a PL 3-ball (given PL Schoenflies): j splits *)
(* the frontier of x into two disks, one inside y and one outside, and the   *)
(* outer disk together with d is the frontier of the difference.            *)
(* ------------------------------------------------------------------------- *)

let MOI_S5F_SPLIT_SIDE = prove
 (`!s j y d1 d2:real^N->bool.
     d1 UNION d2 = s /\ d1 INTER d2 = j /\ s INTER frontier y = j /\ closed y /\
     connected(d1 DIFF j) /\ connected(d2 DIFF j) /\
     ~(s INTER interior y = {}) /\ ~(s DIFF y = {})
     ==> s DIFF interior y = d1 \/ s DIFF interior y = d2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!d:real^N->bool. d SUBSET s /\ connected(d DIFF j)
                ==> (d DIFF j) INTER y = {} \/ (d DIFF j) DIFF y = {}`
  ASSUME_TAC THENL
   [X_GEN_TAC `d:real^N->bool` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`d DIFF j:real^N->bool`; `y:real^N->bool`] CONNECTED_INTER_FRONTIER) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(d DIFF j) INTER frontier y:real^N->bool = {}` (fun th -> REWRITE_TAC[th]) THENL
     [MAP_EVERY UNDISCH_TAC [`(d:real^N->bool) SUBSET s`; `s INTER frontier y:real^N->bool = j`] THEN
      SET_TAC[];
      CONV_TAC TAUT];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `d1:real^N->bool`) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `d2:real^N->bool`) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `d1 UNION d2:real^N->bool = s` THEN SET_TAC[];
    ALL_TAC] THEN
  DISCH_TAC THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `d1 UNION d2:real^N->bool = s` THEN SET_TAC[];
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `interior y SUBSET (y:real^N->bool) /\ frontier y = y DIFF interior y`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[INTERIOR_SUBSET] THEN ASM_SIMP_TAC[frontier; CLOSURE_CLOSED];
    ALL_TAC] THEN
  REPEAT(FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl))) THEN
  ASM SET_TAC[]);;

let MOI_S5F_CUT_BALL = prove
 (`!x y:real^3->bool.
     PL_SCHOENFLIES_3_STATEMENT /\ pl_ball 3 x /\ pl_ball 3 y /\
     pl_cell_with_boundary 2 (frontier y INTER x) (frontier x INTER frontier y)
     ==> pl_ball 3 (x DIFF interior y) /\
         frontier(x DIFF interior y) =
         (frontier x DIFF interior y) UNION (frontier y INTER x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `d = frontier y INTER (x:real^3->bool)` THEN
  ABBREV_TAC `j = frontier x INTER frontier (y:real^3->bool)` THEN
  SUBGOAL_THEN
   `closed(x DIFF interior y) /\ interior(x DIFF interior y) = interior x DIFF y /\
    frontier(x DIFF interior y) = (frontier x DIFF interior y) UNION (d:real^3->bool)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`x:real^3->bool`; `y:real^3->bool`] MOI_S5F_DIFF_INTERIOR) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[MOI_S5F_BALL_FACTS]; ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "d" THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  (* facts about the two balls *)
  SUBGOAL_THEN
   `compact (x:real^3->bool) /\ closed x /\ closed (y:real^3->bool) /\
    pl_sphere 2 (frontier x) /\ pl_sphere 2 (frontier y) /\
    closure(interior x) = x /\ closure(interior y) = y /\
    frontier(interior x) = frontier x /\
    x DIFF interior x = frontier x /\ y DIFF interior y = frontier y /\
    open(interior x) /\ connected(interior y) /\
    (:real^3) DIFF y = outside(frontier y) /\
    connected(outside(frontier y)) /\ ~bounded(outside(frontier y)) /\
    DISJOINT x (outside(frontier x))`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `x:real^3->bool` MOI_S5F_BALL_FACTS) THEN
    MP_TAC(ISPEC `y:real^3->bool` MOI_S5F_BALL_FACTS) THEN
    ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `frontier x SUBSET (x:real^3->bool) /\ frontier y SUBSET (y:real^3->bool) /\
                interior x SUBSET x /\ interior y SUBSET y`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[INTERIOR_SUBSET] THEN ASM_MESON_TAC[FRONTIER_SUBSET_CLOSED];
    ALL_TAC] THEN
  SUBGOAL_THEN `(j:real^3->bool) SUBSET d /\ ~(d SUBSET j) /\ ~pl_sphere 2 d /\
                pl_sphere 1 j /\ j SUBSET frontier x /\ j SUBSET frontier y`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[MOI_S5F_CELL_NOT_BOUNDARY];
      ASM_MESON_TAC[MOI_S5F_CELL_NOT_BOUNDARY];
      ASM_MESON_TAC[MOI_S5F_CELL_NOT_SPHERE];
      MATCH_MP_TAC MOI_S5E_CELL_SPHERE1 THEN EXISTS_TAC `d:real^3->bool` THEN
      ASM_REWRITE_TAC[];
      EXPAND_TAC "j" THEN SET_TAC[];
      EXPAND_TAC "j" THEN SET_TAC[]];
    ALL_TAC] THEN
  (* nondegeneracy *)
  SUBGOAL_THEN `~((x:real^3->bool) SUBSET y)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `interior x SUBSET interior (y:real^3->bool)` ASSUME_TAC THENL
     [MATCH_MP_TAC SUBSET_INTERIOR THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `~((d:real^3->bool) SUBSET j)` THEN REWRITE_TAC[] THEN
    MAP_EVERY EXPAND_TAC ["d"; "j"] THEN
    MAP_EVERY UNDISCH_TAC
     [`x DIFF interior x:real^3->bool = frontier x`;
      `y DIFF interior y:real^3->bool = frontier y`;
      `interior x SUBSET interior (y:real^3->bool)`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(frontier x INTER interior y:real^3->bool = {})` ASSUME_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `interior y INTER interior x:real^3->bool = {} \/
                  interior y DIFF interior x:real^3->bool = {}` MP_TAC THENL
     [MP_TAC(ISPECL [`interior y:real^3->bool`; `interior x:real^3->bool`]
        CONNECTED_INTER_FRONTIER) THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `frontier x INTER interior y:real^3->bool = {}` THEN SET_TAC[];
      ALL_TAC] THEN
    STRIP_TAC THENL
     [SUBGOAL_THEN `interior x INTER y:real^3->bool = {}` ASSUME_TAC THENL
       [MP_TAC(ISPECL [`interior x:real^3->bool`; `interior y:real^3->bool`]
          OPEN_INTER_CLOSURE_EQ_EMPTY) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
        UNDISCH_TAC `interior y INTER interior x:real^3->bool = {}` THEN SET_TAC[];
        ALL_TAC] THEN
      UNDISCH_TAC `~((d:real^3->bool) SUBSET j)` THEN REWRITE_TAC[] THEN
      MAP_EVERY EXPAND_TAC ["d"; "j"] THEN
      MAP_EVERY UNDISCH_TAC
       [`x DIFF interior x:real^3->bool = frontier x`;
        `frontier y SUBSET (y:real^3->bool)`;
        `interior x INTER y:real^3->bool = {}`] THEN
      SET_TAC[];
      SUBGOAL_THEN `(y:real^3->bool) SUBSET x` ASSUME_TAC THENL
       [UNDISCH_TAC `closure(interior y) = (y:real^3->bool)` THEN
        DISCH_THEN(SUBST1_TAC o SYM) THEN
        UNDISCH_TAC `closure(interior x) = (x:real^3->bool)` THEN
        DISCH_THEN(SUBST1_TAC o SYM) THEN
        MATCH_MP_TAC SUBSET_CLOSURE THEN
        UNDISCH_TAC `interior y DIFF interior x:real^3->bool = {}` THEN SET_TAC[];
        ALL_TAC] THEN
      UNDISCH_TAC `~pl_sphere 2 (d:real^3->bool)` THEN REWRITE_TAC[] THEN
      SUBGOAL_THEN `d:real^3->bool = frontier y` (fun th -> ASM_REWRITE_TAC[th]) THEN
      EXPAND_TAC "d" THEN
      MAP_EVERY UNDISCH_TAC
       [`(y:real^3->bool) SUBSET x`; `frontier y SUBSET (y:real^3->bool)`] THEN
      SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(frontier x DIFF y:real^3->bool = {})` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `~((x:real^3->bool) SUBSET y)` THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `outside(frontier y) SUBSET outside(frontier x:real^3->bool)` MP_TAC THENL
     [MATCH_MP_TAC MOI_S5F_SUBSET_OUTSIDE THEN ASM_REWRITE_TAC[] THEN
      MAP_EVERY UNDISCH_TAC
       [`frontier x DIFF y:real^3->bool = {}`;
        `(:real^3) DIFF y = outside(frontier y)`] THEN
      SET_TAC[];
      ALL_TAC] THEN
    MAP_EVERY UNDISCH_TAC
     [`DISJOINT x (outside(frontier x:real^3->bool))`;
      `(:real^3) DIFF y = outside(frontier y)`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(interior x DIFF y:real^3->bool = {})` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `~((x:real^3->bool) SUBSET y)` THEN REWRITE_TAC[] THEN
    UNDISCH_TAC `closure(interior x) = (x:real^3->bool)` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC CLOSURE_MINIMAL THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `interior x DIFF y:real^3->bool = {}` THEN SET_TAC[];
    ALL_TAC] THEN
  (* the outer disk *)
  MP_TAC(ISPECL [`frontier x:real^3->bool`; `j:real^3->bool`] SPHERE_SPLIT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real^3->bool` (X_CHOOSE_THEN `d2:real^3->bool`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `?e:real^3->bool. pl_cell_with_boundary 2 e j /\
                                 frontier x DIFF interior y = e`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`frontier x:real^3->bool`; `j:real^3->bool`; `y:real^3->bool`;
                   `d1:real^3->bool`; `d2:real^3->bool`] MOI_S5F_SPLIT_SIDE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[MOI_S4D_PL_CELL_OPEN_CONNECTED];
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_sphere 2 (e UNION d:real^3->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC DISK_UNION THEN EXISTS_TAC `j:real^3->bool` THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY (fun t -> UNDISCH_TAC t THEN DISCH_THEN(SUBST1_TAC o SYM))
     [`frontier x DIFF interior y:real^3->bool = e`;
      `frontier y INTER x:real^3->bool = d`;
      `frontier x INTER frontier y:real^3->bool = j`] THEN
    MAP_EVERY UNDISCH_TAC
     [`frontier x SUBSET (x:real^3->bool)`;
      `y DIFF interior y:real^3->bool = frontier y`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  (* the difference is the filled sphere *)
  MP_TAC(ISPECL [`e UNION d:real^3->bool`; `x DIFF interior y:real^3->bool`]
    MOI_S5C_FILL_CHAR) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[DIMINDEX_3; ARITH_RULE `2 <= 3`; MOI_SCD_PL_SPHERE_2_HOMEOMORPHIC;
                 COMPACT_DIFF; OPEN_INTERIOR];
    ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN
  UNDISCH_TAC `PL_SCHOENFLIES_3_STATEMENT` THEN
  REWRITE_TAC[PL_SCHOENFLIES_3_STATEMENT] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* 3. Finitely many cuts.  If the balls y i (i IN k, k finite) each meet x  *)
(* as in MOI_S5F_CUT_BALL and pairwise meet only outside x, then x minus    *)
(* the union of their interiors is a PL 3-ball (induction on k; the earlier *)
(* cuts do not change the disk and the circle of a new ball).               *)
(* ------------------------------------------------------------------------- *)

let MOI_S5F_MULTI_CUT = prove
 (`!(y:A->real^3->bool) x.
     PL_SCHOENFLIES_3_STATEMENT /\ pl_ball 3 x
     ==> !k. FINITE k
             ==> (!i. i IN k
                      ==> pl_ball 3 (y i) /\
                          pl_cell_with_boundary 2 (frontier(y i) INTER x)
                                                  (frontier x INTER frontier(y i))) /\
                 (!i i'. i IN k /\ i' IN k /\ ~(i = i') ==> x INTER y i INTER y i' = {})
                 ==> pl_ball 3 (x DIFF UNIONS {interior(y i) | i IN k})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
   [REWRITE_TAC[SIMPLE_IMAGE; IMAGE_CLAUSES; UNIONS_0; DIFF_EMPTY] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`a:A`; `k:A->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih") STRIP_ASSUME_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "yi") (LABEL_TAC "dj")) THEN
  SUBGOAL_THEN `pl_ball 3 (x DIFF UNIONS {interior((y:A->real^3->bool) i) | i IN k})`
  ASSUME_TAC THENL
   [USE_THEN "ih" MATCH_MP_TAC THEN CONJ_TAC THENL
     [X_GEN_TAC `i:A` THEN DISCH_TAC THEN USE_THEN "yi" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[IN_INSERT];
      MAP_EVERY X_GEN_TAC [`i:A`; `i':A`] THEN STRIP_TAC THEN
      USE_THEN "dj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_INSERT]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!i. i IN k ==> (x INTER (y:A->real^3->bool) a) INTER y i = {}`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:A` THEN DISCH_TAC THEN
    SUBGOAL_THEN `x INTER (y:A->real^3->bool) a INTER y i = {}` MP_TAC THENL
     [USE_THEN "dj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_INSERT] THEN ASM_MESON_TAC[];
      SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_ball 3 ((y:A->real^3->bool) a) /\
                pl_cell_with_boundary 2 (frontier(y a) INTER x)
                                        (frontier x INTER frontier(y a))`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "yi" MATCH_MP_TAC THEN REWRITE_TAC[IN_INSERT]; ALL_TAC] THEN
  SUBGOAL_THEN `!i. i IN k ==> closed((y:A->real^3->bool) i)` ASSUME_TAC THENL
   [X_GEN_TAC `i:A` THEN DISCH_TAC THEN
    SUBGOAL_THEN `pl_ball 3 ((y:A->real^3->bool) i)` MP_TAC THENL
     [USE_THEN "yi" (MP_TAC o SPEC `i:A`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[IN_INSERT]; SIMP_TAC[]];
      MESON_TAC[MOI_S5F_BALL_FACTS]];
    ALL_TAC] THEN
  ABBREV_TAC `u = UNIONS {interior((y:A->real^3->bool) i) | i IN k}` THEN
  ABBREV_TAC `v = UNIONS {(y:A->real^3->bool) i | i IN k}` THEN
  SUBGOAL_THEN `x DIFF UNIONS {interior((y:A->real^3->bool) i) | i IN a INSERT k} =
                (x DIFF u) DIFF interior(y a)` SUBST1_TAC THENL
   [EXPAND_TAC "u" THEN REWRITE_TAC[SIMPLE_IMAGE; IMAGE_CLAUSES; UNIONS_INSERT] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `open (u:real^3->bool) /\ closed (v:real^3->bool) /\ u SUBSET v /\
                closed (x:real^3->bool) /\ (x INTER (y:A->real^3->bool) a) INTER v = {}`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [EXPAND_TAC "u" THEN MATCH_MP_TAC OPEN_UNIONS THEN
      REWRITE_TAC[FORALL_IN_GSPEC; OPEN_INTERIOR];
      EXPAND_TAC "v" THEN MATCH_MP_TAC CLOSED_UNIONS THEN
      ASM_SIMP_TAC[SIMPLE_IMAGE; FINITE_IMAGE; FORALL_IN_IMAGE];
      MAP_EVERY EXPAND_TAC ["u"; "v"] THEN
      REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN
      MESON_TAC[INTERIOR_SUBSET; SUBSET];
      ASM_MESON_TAC[MOI_S5F_BALL_FACTS];
      EXPAND_TAC "v" THEN
      REWRITE_TAC[SET_RULE `(s:real^3->bool) INTER UNIONS f = {} <=>
                            !t. t IN f ==> s INTER t = {}`] THEN
      REWRITE_TAC[FORALL_IN_GSPEC] THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `frontier((y:A->real^3->bool) a) INTER (x DIFF u) = frontier(y a) INTER x /\
                frontier(x DIFF u) INTER frontier(y a) = frontier x INTER frontier(y a)`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[MOI_S5F_FRONTIER_DIFF_OPEN] THEN
    SUBGOAL_THEN `frontier(u:real^3->bool) SUBSET v /\
                  frontier((y:A->real^3->bool) a) SUBSET y a /\ frontier (x:real^3->bool) SUBSET x`
    MP_TAC THENL
     [REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `closure(u:real^3->bool)` THEN
        REWRITE_TAC[frontier; SUBSET_DIFF] THEN MATCH_MP_TAC CLOSURE_MINIMAL THEN
        ASM_REWRITE_TAC[];
        ASM_MESON_TAC[MOI_S5F_BALL_FACTS; FRONTIER_SUBSET_CLOSED];
        ASM_MESON_TAC[MOI_S5F_BALL_FACTS; FRONTIER_SUBSET_CLOSED]];
      MAP_EVERY UNDISCH_TAC
       [`(x INTER (y:A->real^3->bool) a) INTER v = {}`; `(u:real^3->bool) SUBSET v`] THEN
      SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`x DIFF u:real^3->bool`; `(y:A->real^3->bool) a`] MOI_S5F_CUT_BALL) THEN
  ASM_REWRITE_TAC[] THEN SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* 4. The edge disk after the circle removal (moi_s35_single): the frontier *)
(* of the A-cell meets the B-cell in the planar disk bounded by the polygon *)
(* j at the level c, carried by the A-side chart, a PL 2-cell bounded by    *)
(* the circle where the two frontiers meet; and the facts of moi_s35_post   *)
(* and moi_s35_charts used for the final cells.                             *)
(* ------------------------------------------------------------------------- *)

let MOI_S5F_LIFT_DOM = prove
 (`!c (y:real^2).
     abs c <= &1 / &512 /\ abs(y$1) <= &5 / &16 /\ abs(y$2) <= &5 / &16
     ==> moi_s35_lift c y IN moi_s35_dom`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[moi_s35_dom; moi_s35_cube; IN_ELIM_THM; IN_INTERVAL; moi_s35_lift] THEN
  REWRITE_TAC[DIMINDEX_3; FORALL_3; VECTOR_3; VECTOR_NEG_COMPONENT; VEC_COMPONENT] THEN
  ASM_REAL_ARITH_TAC);;

let MOI_S5F_DOM_COMPACT = prove
 (`compact moi_s35_dom`,
  SUBGOAL_THEN `moi_s35_dom = interval[--vec 1:real^3,vec 1] INTER {x:real^3 | x$3 <= &1 / &8}`
  SUBST1_TAC THENL
   [REWRITE_TAC[moi_s35_dom; moi_s35_cube] THEN SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC COMPACT_INTER_CLOSED THEN
  REWRITE_TAC[COMPACT_INTERVAL; CLOSED_HALFSPACE_COMPONENT_LE]);;

let MOI_S5F_SINGLE_DISK = prove
 (`!(phi:real^3->real^3) xa xb c.
     pl_map_on moi_s35_dom phi /\
     (!x y. x IN moi_s35_dom /\ y IN moi_s35_dom /\ phi x = phi y ==> x = y) /\
     abs c <= &1 / &512 /\ moi_s35_single phi xa xb c
     ==> pl_cell_with_boundary 2 (frontier xa INTER xb) (frontier xa INTER frontier xb)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s35_single] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `j:real^2->bool` STRIP_ASSUME_TAC)))) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `(j:real^2->bool) SUBSET interval[--vector[&5 / &16;&5 / &16],vector[&5 / &16;&5 / &16]]`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET] THEN X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN
    UNDISCH_TAC
     `IMAGE (moi_s35_lift c) j SUBSET
      moi_s35_aflat c DIFF (moi_s35_sq (&3 / &16) c UNION moi_s35_sq (&5 / &16) c)` THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN DISCH_THEN(MP_TAC o SPEC `z:real^2`) THEN
    ASM_REWRITE_TAC[IN_DIFF] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN
    REWRITE_TAC[moi_s35_aflat; IN_ELIM_THM; MOI_S5C_N_LIFT; IN_INTERVAL] THEN
    REWRITE_TAC[DIMINDEX_2; FORALL_2; VECTOR_2; VECTOR_NEG_COMPONENT] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (moi_s35_lift c) ((j:real^2->bool) UNION inside j) SUBSET moi_s35_dom`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `y:real^2` THEN DISCH_TAC THEN
    MATCH_MP_TAC MOI_S5F_LIFT_DOM THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `(y:real^2) IN interval[--vector[&5 / &16;&5 / &16],vector[&5 / &16;&5 / &16]]`
    MP_TAC THENL
     [SUBGOAL_THEN
       `inside(j:real^2->bool) SUBSET
        interval[--vector[&5 / &16;&5 / &16],vector[&5 / &16;&5 / &16]]`
      MP_TAC THENL
       [MATCH_MP_TAC INSIDE_SUBSET_CONVEX THEN ASM_REWRITE_TAC[CONVEX_INTERVAL];
        ALL_TAC] THEN
      MAP_EVERY UNDISCH_TAC
       [`(y:real^2) IN j UNION inside j`;
        `(j:real^2->bool) SUBSET
         interval[--vector[&5 / &16;&5 / &16],vector[&5 / &16;&5 / &16]]`] THEN
      SET_TAC[];
      REWRITE_TAC[IN_INTERVAL; DIMINDEX_2; FORALL_2; VECTOR_2; VECTOR_NEG_COMPONENT] THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `d = IMAGE (moi_s35_lift c) ((j:real^2->bool) UNION inside j)` THEN
  ABBREV_TAC `k = IMAGE (moi_s35_lift c) (j:real^2->bool)` THEN
  SUBGOAL_THEN `pl_cell_with_boundary 2 (d:real^3->bool) k` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["d"; "k"] THEN MATCH_MP_TAC MOI_S5C_LIFT_DISK THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`moi_s35_dom`; `phi:real^3->real^3`] MOI_S5C_PL_EMBED) THEN
  ASM_REWRITE_TAC[MOI_S5F_DOM_COMPACT] THEN
  DISCH_THEN(X_CHOOSE_TAC `g:real^3->real^3`) THEN
  SUBGOAL_THEN `pl_homeomorphism (d:real^3->bool,IMAGE (phi:real^3->real^3) d) (phi,g)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S5C_PLH_RESTRICT THEN
    MAP_EVERY EXISTS_TAC [`moi_s35_dom`; `IMAGE (phi:real^3->real^3) moi_s35_dom`] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LOCALLY_POLYHEDRAL_PL_POLYHEDRON THEN
    MATCH_MP_TAC MOI_S5C_CELL_POLYHEDRON THEN
    MAP_EVERY EXISTS_TAC [`2`; `k:real^3->bool`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_S5C_CELL_PLH THEN
  MAP_EVERY EXISTS_TAC [`d:real^3->bool`; `g:real^3->real^3`] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `pl_cell_with_boundary 2 (d:real^3->bool) k` THEN
  REWRITE_TAC[pl_cell_with_boundary] THEN MESON_TAC[]);;

let MOI_S5F_POST_FACTS = prove
 (`!(t:(real^N->bool)->bool) l (h:real^N->real^3) w g av bv psi ff xx cc.
     moi_s35_charts t l g av bv psi /\ moi_s35_post t l h w av bv psi ff xx cc
     ==> (!v. {v} IN l ==> pl_ball 3 (xx v)) /\
         (!e. moi_s35_edge l e
              ==> {av e} IN l /\ {bv e} IN l /\ ~(av e = bv e) /\
                  xx (av e) INTER xx (bv e) SUBSET
                  IMAGE (moi_s35_ach ff av psi e) moi_s35_slab /\
                  pl_cell_with_boundary 2 (frontier (xx (av e)) INTER xx (bv e))
                                          (frontier (xx (av e)) INTER frontier (xx (bv e)))) /\
         (!e e'. moi_s35_edge l e /\ moi_s35_edge l e' /\ ~(e = e')
                 ==> DISJOINT (IMAGE (moi_s35_ach ff av psi e) moi_s35_slab)
                              (IMAGE (moi_s35_ach ff av psi e') moi_s35_slab)) /\
         (!u v. {u} IN l /\ {v} IN l /\ ~(u = v) /\ ~(segment[u,v] IN l)
                ==> DISJOINT (xx u) (xx v))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ch") MP_TAC) THEN
  REWRITE_TAC[moi_s35_post; moi_s35_frame] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (CONJUNCTS_THEN2 (LABEL_TAC "fv") (CONJUNCTS_THEN2 (LABEL_TAC "fe")
     (CONJUNCTS_THEN2 (LABEL_TAC "fo") (CONJUNCTS_THEN2 (LABEL_TAC "fs")
       (CONJUNCTS_THEN2 (LABEL_TAC "fn") (LABEL_TAC "fg"))))))
   (CONJUNCTS_THEN2 (LABEL_TAC "pc") (LABEL_TAC "pe"))) THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN
    USE_THEN "fv" (MP_TAC o C MATCH_MP (ASSUME `{v:real^N} IN l`)) THEN
    SIMP_TAC[];
    X_GEN_TAC `e:real^N->bool` THEN DISCH_TAC THEN
    USE_THEN "ch" (MP_TAC o SPEC `e:real^N->bool` o CONJUNCT1 o
                   GEN_REWRITE_RULE I [moi_s35_charts]) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    DISCH_THEN(fun th -> MP_TAC(CONJUNCT1 th) THEN MP_TAC(CONJUNCT1(CONJUNCT2 th)) THEN
                         MP_TAC(CONJUNCT1(CONJUNCT2(CONJUNCT2 th)))) THEN
    REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [USE_THEN "fe" (MP_TAC o C MATCH_MP (ASSUME `moi_s35_edge l (e:real^N->bool)`)) THEN
      SIMP_TAC[];
      ALL_TAC] THEN
    USE_THEN "pe" (MP_TAC o C MATCH_MP (ASSUME `moi_s35_edge l (e:real^N->bool)`)) THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `b:real^3->bool` MP_TAC) ASSUME_TAC) THEN
    REWRITE_TAC[moi_s35_edge_conf] THEN STRIP_TAC THEN
    MATCH_MP_TAC MOI_S5F_SINGLE_DISK THEN
    MAP_EVERY EXISTS_TAC [`moi_s35_ach ff av psi (e:real^N->bool)`;
                          `(cc:(real^N->bool)->real) e`] THEN
    ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN
    USE_THEN "fs" (MP_TAC o SPECL [`e:real^N->bool`; `e':real^N->bool`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
    USE_THEN "fn" ACCEPT_TAC]);;

(* ------------------------------------------------------------------------- *)
(* 5. Final cells, abstractly: vertices vv, edges ee with ends av e, bv e,   *)
(* PL 3-balls x v, edge regions r e (pairwise disjoint) containing the      *)
(* overlaps x(av e) INTER x(bv e), each frontier x(av e) INTER x(bv e) a     *)
(* 2-cell bounded by the circle of the two frontiers.  D v = x v minus the   *)
(* removed set u v (the interiors of the A-cells of the B-side edges of v). *)
(* ------------------------------------------------------------------------- *)

let MOI_S5F_SEP = prove
 (`!(ee:B->bool) (av:B->A) bv (x:A->real^3->bool) r e e'.
     (!e. e IN ee ==> x (av e) INTER x (bv e) SUBSET r e) /\
     (!e e'. e IN ee /\ e' IN ee /\ ~(e = e') ==> DISJOINT (r e) (r e')) /\
     e IN ee /\ e' IN ee /\ ~(e = e')
     ==> (x (av e) INTER x (bv e)) INTER (x (av e') INTER x (bv e')) = {}`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ov") (CONJUNCTS_THEN2 (LABEL_TAC "dj")
    STRIP_ASSUME_TAC)) THEN
  USE_THEN "ov" (MP_TAC o C MATCH_MP (ASSUME `(e:B) IN ee`)) THEN
  USE_THEN "ov" (MP_TAC o C MATCH_MP (ASSUME `(e':B) IN ee`)) THEN
  USE_THEN "dj" (MP_TAC o SPECL [`e:B`; `e':B`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN SET_TAC[]);;

let MOI_S5F_INTERIOR_IN_UNIONS = prove
 (`!(ee:B->bool) (av:B->A) (bv:B->A) (x:A->real^3->bool) e.
     e IN ee
     ==> interior (x (av e)) SUBSET
         UNIONS {interior (x (av e')) | e' | e' IN ee /\ bv e' = bv e}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN
  X_GEN_TAC `p:real^3` THEN DISCH_TAC THEN
  EXISTS_TAC `interior((x:A->real^3->bool) (av(e:B)))` THEN ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `e:B` THEN ASM_REWRITE_TAC[]);;

let MOI_S5F_IN_UNIONS_EDGE = prove
 (`!(ee:B->bool) (av:B->A) (bv:B->A) (x:A->real^3->bool) v p.
     p IN UNIONS {interior (x (av e)) | e | e IN ee /\ bv e = v}
     ==> ?e. e IN ee /\ bv e = v /\ p IN interior (x (av e))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN MESON_TAC[]);;

let MOI_S5F_MEET = prove
 (`!(ee:B->bool) (av:B->A) bv (x:A->real^3->bool) r (u:A->real^3->bool).
     (!e. e IN ee ==> pl_ball 3 (x (av e)) /\ ~(av e = bv e) /\
                      x (av e) INTER x (bv e) SUBSET r e) /\
     (!e e'. e IN ee /\ e' IN ee /\ ~(e = e') ==> DISJOINT (r e) (r e')) /\
     (!e. e IN ee ==> interior (x (av e)) SUBSET u (bv e)) /\
     (!v p. p IN u v ==> ?e. e IN ee /\ bv e = v /\ p IN interior (x (av e)))
     ==> !e. e IN ee
             ==> (x (av e) DIFF u (av e)) INTER (x (bv e) DIFF u (bv e)) =
                 frontier (x (av e)) INTER x (bv e) /\
                 frontier (x (av e)) INTER x (bv e) SUBSET frontier (x (av e) DIFF u (av e)) /\
                 frontier (x (av e)) INTER x (bv e) SUBSET frontier (x (bv e) DIFF u (bv e))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ed") (CONJUNCTS_THEN2 (LABEL_TAC "dj")
    (CONJUNCTS_THEN2 (LABEL_TAC "u1") (LABEL_TAC "u2")))) THEN
  X_GEN_TAC `e:B` THEN DISCH_TAC THEN
  SUBGOAL_THEN `!e e':B. e IN ee /\ e' IN ee /\ ~(e = e')
                ==> ((x:A->real^3->bool) ((av:B->A) e) INTER x ((bv:B->A) e)) INTER
                    (x (av e') INTER x (bv e')) = {}`
  (LABEL_TAC "sep") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_S5F_SEP THEN
    EXISTS_TAC `ee:B->bool` THEN EXISTS_TAC `r:B->real^3->bool` THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  USE_THEN "ed" (MP_TAC o C MATCH_MP (ASSUME `(e:B) IN ee`)) THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `closed((x:A->real^3->bool) (av(e:B))) /\
    x (av e) DIFF interior (x (av e)) = frontier (x (av e)) /\
    closure (interior (x (av e))) = x (av e)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[MOI_S5F_BALL_FACTS]; ALL_TAC] THEN
  ABBREV_TAC `xa = (x:A->real^3->bool) (av(e:B))` THEN
  ABBREV_TAC `xb = (x:A->real^3->bool) (bv(e:B))` THEN
  ABBREV_TAC `ua = (u:A->real^3->bool) (av(e:B))` THEN
  ABBREV_TAC `ub = (u:A->real^3->bool) (bv(e:B))` THEN
  SUBGOAL_THEN `interior xa SUBSET (ub:real^3->bool)` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["xa"; "ub"] THEN USE_THEN "u1" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* no point of the disk is removed at either end *)
  SUBGOAL_THEN `(frontier xa INTER xb) INTER (ua:real^3->bool) = {}` ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN X_GEN_TAC `p:real^3` THEN
    STRIP_TAC THEN
    USE_THEN "u2" (MP_TAC o SPECL [`(av:B->A) e`; `p:real^3`]) THEN
    ANTS_TAC THENL [EXPAND_TAC "ua" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `e':B` STRIP_ASSUME_TAC) THEN
    USE_THEN "sep" (MP_TAC o SPECL [`e:B`; `e':B`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      UNDISCH_TAC `~((av:B->A) e = bv e)` THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `(x:A->real^3->bool) (av(e':B))` INTERIOR_SUBSET) THEN
    MAP_EVERY UNDISCH_TAC
     [`(p:real^3) IN frontier xa`; `(p:real^3) IN xb`;
      `(p:real^3) IN interior ((x:A->real^3->bool) (av(e':B)))`;
      `xa DIFF interior xa:real^3->bool = frontier xa`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(frontier xa INTER xb) INTER (ub:real^3->bool) = {}` ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN X_GEN_TAC `p:real^3` THEN
    STRIP_TAC THEN
    USE_THEN "u2" (MP_TAC o SPECL [`(bv:B->A) e`; `p:real^3`]) THEN
    ANTS_TAC THENL [EXPAND_TAC "ub" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `e':B` STRIP_ASSUME_TAC) THEN
    ASM_CASES_TAC `e':B = e` THENL
     [UNDISCH_TAC `(p:real^3) IN interior ((x:A->real^3->bool) (av(e':B)))` THEN
      ASM_REWRITE_TAC[] THEN
      MAP_EVERY UNDISCH_TAC
       [`(p:real^3) IN frontier xa`;
        `xa DIFF interior xa:real^3->bool = frontier xa`] THEN
      SET_TAC[];
      ALL_TAC] THEN
    USE_THEN "sep" (MP_TAC o SPECL [`e:B`; `e':B`]) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `(x:A->real^3->bool) (av(e':B))` INTERIOR_SUBSET) THEN
    MAP_EVERY UNDISCH_TAC
     [`(p:real^3) IN frontier xa`; `(p:real^3) IN xb`;
      `(p:real^3) IN interior ((x:A->real^3->bool) (av(e':B)))`;
      `xa DIFF interior xa:real^3->bool = frontier xa`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(xa DIFF ua) INTER (xb DIFF ub) = frontier xa INTER (xb:real^3->bool)`
  ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`interior xa SUBSET (ub:real^3->bool)`;
      `(frontier xa INTER xb) INTER (ua:real^3->bool) = {}`;
      `(frontier xa INTER xb) INTER (ub:real^3->bool) = {}`;
      `xa DIFF interior xa:real^3->bool = frontier xa`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [(* in the frontier of the A-side final cell *)
    GEN_REWRITE_TAC RAND_CONV [frontier] THEN
    MP_TAC(ISPEC `xa DIFF ua:real^3->bool` CLOSURE_SUBSET) THEN
    MP_TAC(ISPECL [`xa DIFF ua:real^3->bool`; `xa:real^3->bool`] SUBSET_INTERIOR) THEN
    REWRITE_TAC[SUBSET_DIFF] THEN
    MAP_EVERY UNDISCH_TAC
     [`(xa DIFF ua) INTER (xb DIFF ub) = frontier xa INTER (xb:real^3->bool)`;
      `xa DIFF interior xa:real^3->bool = frontier xa`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  (* in the frontier of the B-side final cell: frontier points of xa are limits *)
  (* of interior points of xa, which are removed from the B-side cell          *)
  SUBGOAL_THEN `interior(xb DIFF ub) INTER interior xa:real^3->bool = {}` ASSUME_TAC THENL
   [MP_TAC(ISPEC `xb DIFF ub:real^3->bool` INTERIOR_SUBSET) THEN
    UNDISCH_TAC `interior xa SUBSET (ub:real^3->bool)` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `interior(xb DIFF ub) INTER closure(interior xa):real^3->bool = {}`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`interior(xb DIFF ub):real^3->bool`; `interior xa:real^3->bool`]
      OPEN_INTER_CLOSURE_EQ_EMPTY) THEN
    REWRITE_TAC[OPEN_INTERIOR] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  GEN_REWRITE_TAC RAND_CONV [frontier] THEN
  MP_TAC(ISPEC `xb DIFF ub:real^3->bool` CLOSURE_SUBSET) THEN
  MAP_EVERY UNDISCH_TAC
   [`interior(xb DIFF ub) INTER closure(interior xa):real^3->bool = {}`;
    `closure (interior xa) = (xa:real^3->bool)`;
    `(xa DIFF ua) INTER (xb DIFF ub) = frontier xa INTER (xb:real^3->bool)`;
    `xa DIFF interior xa:real^3->bool = frontier xa`] THEN
  SET_TAC[]);;

let MOI_S5F_UNION_CELLS = prove
 (`!(vv:A->bool) (ee:B->bool) av bv (x:A->real^3->bool) r (u:A->real^3->bool).
     (!e. e IN ee ==> av e IN vv /\ ~(av e = bv e) /\
                      x (av e) INTER x (bv e) SUBSET r e) /\
     (!e e'. e IN ee /\ e' IN ee /\ ~(e = e') ==> DISJOINT (r e) (r e')) /\
     (!v p. p IN u v ==> ?e. e IN ee /\ bv e = v /\ p IN interior (x (av e)))
     ==> UNIONS {x v DIFF u v | v IN vv} = UNIONS {x v | v IN vv}`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ed") (CONJUNCTS_THEN2 (LABEL_TAC "dj")
    (LABEL_TAC "u2"))) THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [REWRITE_TAC[SIMPLE_IMAGE] THEN MATCH_MP_TAC UNIONS_MONO_IMAGE THEN
    GEN_TAC THEN DISCH_TAC THEN BETA_TAC THEN SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC] THEN
  X_GEN_TAC `v:A` THEN DISCH_TAC THEN REWRITE_TAC[SUBSET] THEN
  X_GEN_TAC `p:real^3` THEN DISCH_TAC THEN REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
  ASM_CASES_TAC `(p:real^3) IN (u:A->real^3->bool) v` THENL
   [ALL_TAC;
    EXISTS_TAC `(x:A->real^3->bool) v DIFF u v` THEN
    CONJ_TAC THENL
     [EXISTS_TAC `v:A` THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[IN_DIFF] THEN ASM_REWRITE_TAC[]]] THEN
  USE_THEN "u2" (MP_TAC o C MATCH_MP (ASSUME `(p:real^3) IN (u:A->real^3->bool) v`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `e:B` STRIP_ASSUME_TAC) THEN
  USE_THEN "ed" (MP_TAC o C MATCH_MP (ASSUME `(e:B) IN ee`)) THEN STRIP_TAC THEN
  EXISTS_TAC `(x:A->real^3->bool) (av(e:B)) DIFF u (av e)` THEN CONJ_TAC THENL
   [EXISTS_TAC `(av:B->A) e` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[IN_DIFF] THEN CONJ_TAC THENL
   [MP_TAC(ISPEC `(x:A->real^3->bool) (av(e:B))` INTERIOR_SUBSET) THEN
    UNDISCH_TAC `(p:real^3) IN interior ((x:A->real^3->bool) (av(e:B)))` THEN SET_TAC[];
    ALL_TAC] THEN
  DISCH_TAC THEN
  USE_THEN "u2" (MP_TAC o SPECL [`(av:B->A) e`; `p:real^3`]) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e':B` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`ee:B->bool`; `av:B->A`; `bv:B->A`; `x:A->real^3->bool`;
                 `r:B->real^3->bool`; `e:B`; `e':B`] MOI_S5F_SEP) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [X_GEN_TAC `f:B` THEN DISCH_TAC THEN
      USE_THEN "ed" (MP_TAC o C MATCH_MP (ASSUME `(f:B) IN ee`)) THEN SIMP_TAC[];
      USE_THEN "dj" ACCEPT_TAC;
      FIRST_ASSUM ACCEPT_TAC;
      FIRST_ASSUM ACCEPT_TAC;
      DISCH_TAC THEN UNDISCH_TAC `~((av:B->A) e = bv e)` THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `(x:A->real^3->bool) (av(e:B))` INTERIOR_SUBSET) THEN
  MP_TAC(ISPEC `(x:A->real^3->bool) (av(e':B))` INTERIOR_SUBSET) THEN
  MAP_EVERY UNDISCH_TAC
   [`(p:real^3) IN (x:A->real^3->bool) v`;
    `(p:real^3) IN interior ((x:A->real^3->bool) (av(e:B)))`;
    `(p:real^3) IN interior ((x:A->real^3->bool) (av(e':B)))`] THEN
  SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* 6. The main theorem FINAL_CELLS: the abstract lemmas of section 5 with   *)
(* the vertices {v} IN l, the edges moi_s35_edge l e, the cells xx v, the   *)
(* slab images of the A-side charts as edge regions and the removed sets of *)
(* the final cells; the balls by MOI_S5F_MULTI_CUT over the finitely many   *)
(* B-side edges of a vertex (MOI_S5V_EDGES_FINITE).                         *)
(* ------------------------------------------------------------------------- *)

let FINAL_CELLS = prove
 (MOI_S35_FINAL_CELLS,
  DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                       `h:real^N->real^3`; `w:real^N->real^3->bool`;
                       `g:real^N->real^N->bool`; `av:(real^N->bool)->real^N`;
                       `bv:(real^N->bool)->real^N`;
                       `psi:(real^N->bool)->real^3->real^N`;
                       `ff:real^N->real^N->real^3`; `xx:real^N->real^3->bool`;
                       `cc:(real^N->bool)->real`] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `w:real^N->real^3->bool`;
                 `g:real^N->real^N->bool`; `av:(real^N->bool)->real^N`;
                 `bv:(real^N->bool)->real^N`; `psi:(real^N->bool)->real^3->real^N`;
                 `ff:real^N->real^N->real^3`; `xx:real^N->real^3->bool`;
                 `cc:(real^N->bool)->real`] MOI_S5F_POST_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ball") (CONJUNCTS_THEN2 (LABEL_TAC "edge")
    (CONJUNCTS_THEN2 (LABEL_TAC "slab") (LABEL_TAC "far")))) THEN
  REWRITE_TAC[moi_s35_dcell; moi_s35_ddisk] THEN
  SUBGOAL_THEN
   `!e. moi_s35_edge l e
        ==> (xx:real^N->real^3->bool) ((av:(real^N->bool)->real^N) e) INTER
            xx ((bv:(real^N->bool)->real^N) e) SUBSET
            IMAGE (moi_s35_ach ff av psi e) moi_s35_slab`
  (LABEL_TAC "ov") THENL
   [X_GEN_TAC `e:real^N->bool` THEN DISCH_TAC THEN
    USE_THEN "edge" (MP_TAC o C MATCH_MP (ASSUME `moi_s35_edge l (e:real^N->bool)`)) THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!e e'. moi_s35_edge l e /\ moi_s35_edge l e' /\ ~(e = e')
           ==> ((xx:real^N->real^3->bool) ((av:(real^N->bool)->real^N) e) INTER
                xx ((bv:(real^N->bool)->real^N) e)) INTER
               (xx (av e') INTER xx (bv e')) = {}`
  (LABEL_TAC "sep") THENL
   [MAP_EVERY X_GEN_TAC [`e:real^N->bool`; `e':real^N->bool`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`{e:real^N->bool | moi_s35_edge l e}`; `av:(real^N->bool)->real^N`;
                   `bv:(real^N->bool)->real^N`; `xx:real^N->real^3->bool`;
                   `\e:real^N->bool. IMAGE (moi_s35_ach ff av psi e) moi_s35_slab`;
                   `e:real^N->bool`; `e':real^N->bool`] MOI_S5F_SEP) THEN
    REWRITE_TAC[IN_ELIM_THM] THEN BETA_TAC THEN DISCH_THEN MATCH_MP_TAC THEN
    REPEAT CONJ_TAC THENL
     [USE_THEN "ov" ACCEPT_TAC; USE_THEN "slab" ACCEPT_TAC;
      FIRST_ASSUM ACCEPT_TAC; FIRST_ASSUM ACCEPT_TAC; FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!e. moi_s35_edge l e
        ==> frontier ((xx:real^N->real^3->bool) ((av:(real^N->bool)->real^N) e)) SUBSET
            xx (av e)`
  (LABEL_TAC "fr") THENL
   [X_GEN_TAC `e:real^N->bool` THEN DISCH_TAC THEN
    MATCH_MP_TAC FRONTIER_SUBSET_CLOSED THEN
    SUBGOAL_THEN `pl_ball 3 ((xx:real^N->real^3->bool) ((av:(real^N->bool)->real^N) e))`
    MP_TAC THENL
     [USE_THEN "ball" MATCH_MP_TAC THEN
      USE_THEN "edge" (MP_TAC o C MATCH_MP (ASSUME `moi_s35_edge l (e:real^N->bool)`)) THEN
      SIMP_TAC[];
      MESON_TAC[MOI_S5F_BALL_FACTS]];
    ALL_TAC] THEN
  (* the meeting of the final cells along an edge *)
  MP_TAC(ISPECL [`{e:real^N->bool | moi_s35_edge l e}`; `av:(real^N->bool)->real^N`;
                 `bv:(real^N->bool)->real^N`; `xx:real^N->real^3->bool`;
                 `\e:real^N->bool. IMAGE (moi_s35_ach ff av psi e) moi_s35_slab`;
                 `\v:real^N. UNIONS {interior ((xx:real^N->real^3->bool) (av e)) | e |
                                     moi_s35_edge l e /\ (bv:(real^N->bool)->real^N) e = v}`]
    MOI_S5F_MEET) THEN
  REWRITE_TAC[IN_ELIM_THM] THEN BETA_TAC THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [X_GEN_TAC `e:real^N->bool` THEN DISCH_TAC THEN
      USE_THEN "edge" (MP_TAC o C MATCH_MP (ASSUME `moi_s35_edge l (e:real^N->bool)`)) THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN USE_THEN "ball" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      USE_THEN "slab" ACCEPT_TAC;
      MP_TAC(ISPECL [`{e:real^N->bool | moi_s35_edge l e}`; `av:(real^N->bool)->real^N`;
                     `bv:(real^N->bool)->real^N`; `xx:real^N->real^3->bool`]
        MOI_S5F_INTERIOR_IN_UNIONS) THEN
      REWRITE_TAC[IN_ELIM_THM] THEN DISCH_THEN ACCEPT_TAC;
      MP_TAC(ISPECL [`{e:real^N->bool | moi_s35_edge l e}`; `av:(real^N->bool)->real^N`;
                     `bv:(real^N->bool)->real^N`; `xx:real^N->real^3->bool`]
        MOI_S5F_IN_UNIONS_EDGE) THEN
      REWRITE_TAC[IN_ELIM_THM] THEN DISCH_THEN ACCEPT_TAC];
    ALL_TAC] THEN
  DISCH_THEN(LABEL_TAC "meet") THEN
  (* the union of the final cells *)
  MP_TAC(ISPECL [`{v:real^N | {v} IN l}`; `{e:real^N->bool | moi_s35_edge l e}`;
                 `av:(real^N->bool)->real^N`;
                 `bv:(real^N->bool)->real^N`; `xx:real^N->real^3->bool`;
                 `\e:real^N->bool. IMAGE (moi_s35_ach ff av psi e) moi_s35_slab`;
                 `\v:real^N. UNIONS {interior ((xx:real^N->real^3->bool) (av e)) | e |
                                     moi_s35_edge l e /\ (bv:(real^N->bool)->real^N) e = v}`]
    MOI_S5F_UNION_CELLS) THEN
  REWRITE_TAC[IN_ELIM_THM] THEN BETA_TAC THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [X_GEN_TAC `e:real^N->bool` THEN DISCH_TAC THEN
      USE_THEN "edge" (MP_TAC o C MATCH_MP (ASSUME `moi_s35_edge l (e:real^N->bool)`)) THEN
      SIMP_TAC[];
      USE_THEN "slab" ACCEPT_TAC;
      MP_TAC(ISPECL [`{e:real^N->bool | moi_s35_edge l e}`; `av:(real^N->bool)->real^N`;
                     `bv:(real^N->bool)->real^N`; `xx:real^N->real^3->bool`]
        MOI_S5F_IN_UNIONS_EDGE) THEN
      REWRITE_TAC[IN_ELIM_THM] THEN DISCH_THEN ACCEPT_TAC];
    ALL_TAC] THEN
  DISCH_THEN(LABEL_TAC "union") THEN
  REPEAT CONJ_TAC THENL
   [(* the final cells are PL 3-balls *)
    X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`\e:real^N->bool. (xx:real^N->real^3->bool) ((av:(real^N->bool)->real^N) e)`;
                   `(xx:real^N->real^3->bool) v`] MOI_S5F_MULTI_CUT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN USE_THEN "ball" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `{e:real^N->bool | moi_s35_edge l e /\
                                               (bv:(real^N->bool)->real^N) e = v}`) THEN
    REWRITE_TAC[IN_ELIM_THM] THEN BETA_TAC THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `{e:real^N->bool | moi_s35_edge l e /\
                                    ((av:(real^N->bool)->real^N) e = v \/
                                     (bv:(real^N->bool)->real^N) e = v)}` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC MOI_S5V_EDGES_FINITE THEN EXISTS_TAC `t:(real^N->bool)->bool` THEN
        ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `moi_s35_charts t l (g:real^N->real^N->bool) av bv psi` THEN
        REWRITE_TAC[moi_s35_charts] THEN MESON_TAC[];
        SET_TAC[]];
      ALL_TAC] THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [X_GEN_TAC `i:real^N->bool` THEN STRIP_TAC THEN
        USE_THEN "edge" (MP_TAC o C MATCH_MP (ASSUME `moi_s35_edge l (i:real^N->bool)`)) THEN
        STRIP_TAC THEN CONJ_TAC THENL
         [USE_THEN "ball" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
          UNDISCH_TAC
           `pl_cell_with_boundary 2
             (frontier ((xx:real^N->real^3->bool) ((av:(real^N->bool)->real^N) i)) INTER
              xx ((bv:(real^N->bool)->real^N) i))
             (frontier (xx (av i)) INTER frontier (xx (bv i)))` THEN
          ASM_REWRITE_TAC[] THEN MESON_TAC[INTER_COMM]];
        MAP_EVERY X_GEN_TAC [`i:real^N->bool`; `i':real^N->bool`] THEN STRIP_TAC THEN
        USE_THEN "sep" (MP_TAC o SPECL [`i:real^N->bool`; `i':real^N->bool`]) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        ASM_REWRITE_TAC[] THEN SET_TAC[]];
      DISCH_THEN ACCEPT_TAC];
    (* along an edge *)
    X_GEN_TAC `e:real^N->bool` THEN DISCH_TAC THEN
    USE_THEN "meet" (MP_TAC o C MATCH_MP (ASSUME `moi_s35_edge l (e:real^N->bool)`)) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `frontier ((xx:real^N->real^3->bool) ((av:(real^N->bool)->real^N) e)) INTER
                frontier (xx ((bv:(real^N->bool)->real^N) e))` THEN
    USE_THEN "edge" (MP_TAC o C MATCH_MP (ASSUME `moi_s35_edge l (e:real^N->bool)`)) THEN
    SIMP_TAC[];
    (* disks of distinct edges *)
    MAP_EVERY X_GEN_TAC [`e:real^N->bool`; `e':real^N->bool`] THEN STRIP_TAC THEN
    USE_THEN "sep" (MP_TAC o SPECL [`e:real^N->bool`; `e':real^N->bool`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    USE_THEN "fr" (MP_TAC o C MATCH_MP (ASSUME `moi_s35_edge l (e:real^N->bool)`)) THEN
    USE_THEN "fr" (MP_TAC o C MATCH_MP (ASSUME `moi_s35_edge l (e':real^N->bool)`)) THEN
    SET_TAC[];
    (* non-adjacent cells *)
    MAP_EVERY X_GEN_TAC [`u:real^N`; `v:real^N`] THEN STRIP_TAC THEN
    MATCH_MP_TAC(SET_RULE `!s t a b:real^3->bool.
                             DISJOINT s t ==> DISJOINT (s DIFF a) (t DIFF b)`) THEN
    USE_THEN "far" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    (* the union *)
    USE_THEN "union" ACCEPT_TAC]);;

