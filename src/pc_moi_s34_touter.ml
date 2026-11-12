needs "src/pc_moi_s34_recogb.ml";;
needs "src/pc_moi_s34_scellb.ml";;
needs "src/pc_moi_s34_outer.ml";;
needs "src/pc_moi_s34_tinf.ml";;
needs "src/pc_moi_s34_l910.ml";;
needs "src/pc_moi_pl1m.ml";;
needs "src/pc_moi_fnd_surfa.ml";;
needs "src/pc_moi_sch3_s2.ml";;
needs "src/pc_moi_sch3_lev.ml";;
needs "src/pc_moi_pl2.ml";;
needs "src/pc_moi_fnd_m3a.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* pc_moi_s34_touter: the outer target cells of the Sec 34 cell diagram at  *)
(* the boundary of kk (Moise, Geometric Topology in Dimensions 2 and 3,     *)
(* GTM 47, Sec 34, pp.244-246, the boundary case of 34.1, target side).     *)
(* Main theorem (pc_moi_s34_stmt.ml):                                       *)
(*   TOUTER = MOI_S34_OUTER                                                 *)
(* Notation at a vertex v of kk: C_v = f1(vb v), A_v = f1(vb v INTER Bd N), *)
(* D_g = f1(sd g), the rim R_g = f1(sd g INTER Bd N), Sigma_v = frontier    *)
(* C_v, the patches X_r = rr r INTER C_v, the face arcs dd s INTER C_v, the *)
(* rim arcs rr r INTER D_g.                                                  *)
(* Route.                                                                    *)
(* (E) At a boundary edge g the rim arcs of the 3-simplices at g cover R_g  *)
(* except near the points of the two boundary faces at g: a 1-dimensional   *)
(* covering argument in the circle R_g, then MOI_S4O_CIRCLE_ARC.            *)
(* (V) At a boundary vertex v the boundary face arcs and the outer arcs     *)
(* form a PL circle J_v (line charts and connectedness, from the link of v *)
(* in the boundary surface), the patches and splitting disks cover a       *)
(* neighbourhood of each of their points off J_v (disk gluing), and the     *)
(* outer patch is the side of J_v in the 2-sphere Sigma_v off the patches   *)
(* (MOI_S4O_SPHERE_PIECE).                                                  *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Generic facts on PL arcs, circles and disks.                              *)
(* ------------------------------------------------------------------------- *)

(* A PL arc is not a PL circle: removing its middle point disconnects it.   *)

let MOI_S4OT_ARC_NOT_CIRCLE = prove
 (`!a ba:real^N->bool. pl_cell_with_boundary 1 a ba ==> ~pl_sphere 1 a`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^1->real^N` STRIP_ASSUME_TAC o
    MATCH_MP MOI_S4L_CELL1_PL_ARC) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `path_image(h:real^1->real^N)`)) THEN
  DISCH_TAC THEN
  MP_TAC(ISPEC `h:real^1->real^N` HOMEOMORPHISM_ARC) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->real^1` MP_TAC) THEN
  REWRITE_TAC[homeomorphism] THEN STRIP_TAC THEN
  SUBGOAL_THEN `lift(&1 / &2) IN interval[vec 0:real^1,vec 1]` ASSUME_TAC THENL
   [REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; LIFT_DROP] THEN CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`path_image(h:real^1->real^N)`; `(h:real^1->real^N)(lift(&1 / &2))`]
    MOI_SLV_CIRCLE_DELETE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REWRITE_TAC[path_image] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
    ASM_REWRITE_TAC[];
    DISCH_TAC] THEN
  SUBGOAL_THEN `connected (IMAGE (k:real^N->real^1)
                  (path_image h DELETE (h:real^1->real^N)(lift(&1 / &2))))` MP_TAC THENL
   [MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `path_image(h:real^1->real^N)` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (k:real^N->real^1) (path_image h DELETE (h:real^1->real^N)(lift(&1 / &2))) =
    interval[vec 0,vec 1] DELETE lift(&1 / &2)` SUBST1_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`!x:real^1. x IN interval[vec 0,vec 1] ==> (k:real^N->real^1)(h x) = x`;
      `IMAGE (h:real^1->real^N) (interval[vec 0,vec 1]) = path_image h`;
      `!y:real^N. y IN path_image h ==> (h:real^1->real^N)(k y) = y`;
      `IMAGE (k:real^N->real^1) (path_image h) = interval[vec 0,vec 1]`;
      `lift(&1 / &2) IN interval[vec 0:real^1,vec 1]`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM IS_INTERVAL_CONNECTED_1; IS_INTERVAL_1] THEN
  DISCH_THEN(MP_TAC o SPECL [`vec 0:real^1`; `vec 1:real^1`; `lift(&1 / &2)`]) THEN
  REWRITE_TAC[IN_DELETE; IN_INTERVAL_1; DROP_VEC; LIFT_DROP; GSYM DROP_EQ] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV);;

(* An end of a PL arc in a PL circle has no circle neighbourhood inside the *)
(* arc (the 1-dimensional MOI_S4L_CELL_BOUNDARY_NOT_OPEN).                  *)

let MOI_S4OT_ARC_END_NOT_OPEN = prove
 (`!(K:real^N->bool) a ba x.
     pl_sphere 1 K /\ pl_cell_with_boundary 1 a ba /\ a SUBSET K /\ x IN ba
     ==> ~(?u. open_in (subtopology euclidean K) u /\ x IN u /\ u SUBSET a)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`K:real^N->bool`; `a:real^N->bool`; `ba:real^N->bool`] MOI_S4H_ARC_OPEN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `h:real^1->real^N` STRIP_ASSUME_TAC o
    MATCH_MP MOI_S4L_CELL1_PL_ARC) THEN
  SUBGOAL_THEN `compact(a:real^N->bool) /\ ba SUBSET a` STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `path_image(h:real^1->real^N)`)) THEN
    FIRST_ASSUM(SUBST1_TAC o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `ba:real^N->bool`)) THEN
    ASM_SIMP_TAC[COMPACT_PATH_IMAGE; ARC_IMP_PATH; INSERT_SUBSET; EMPTY_SUBSET;
                 PATHSTART_IN_PATH_IMAGE; PATHFINISH_IN_PATH_IMAGE];
    ALL_TAC] THEN
  SUBGOAL_THEN `?y:real^N. ~(y = x) /\ ba = {x,y}` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `h:real^1->real^N` ARC_DISTINCT_ENDS) THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(x:real^N) IN ba` THEN
    FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `ba:real^N->bool`)) THEN
    REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN STRIP_TAC THEN DISCH_TAC THENL
     [EXISTS_TAC `pathfinish(h:real^1->real^N)` THEN ASM_REWRITE_TAC[];
      EXISTS_TAC `pathstart(h:real^1->real^N)` THEN ASM_REWRITE_TAC[] THEN
      REPEAT CONJ_TAC THEN TRY(ASM_MESON_TAC[]) THEN SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`K:real^N->bool`; `y:real^N`] MOI_SLV_CIRCLE_DELETE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC [`ba = {x:real^N,y}`; `(ba:real^N->bool) SUBSET a`;
                           `(a:real^N->bool) SUBSET K`] THEN SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[CONNECTED_CLOPEN] THEN
  DISCH_THEN(MP_TAC o SPEC `a DELETE (y:real^N)`) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_IN_SUBSET_TRANS THEN
      EXISTS_TAC `K:real^N->bool` THEN
      SUBGOAL_THEN `a DELETE (y:real^N) = (u UNION (a DIFF ba)) DELETE y` SUBST1_TAC THENL
       [MAP_EVERY UNDISCH_TAC [`(x:real^N) IN u`; `(u:real^N->bool) SUBSET a`;
                               `ba = {x:real^N,y}`; `~(y:real^N = x)`] THEN SET_TAC[];
        ALL_TAC] THEN
      REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC OPEN_IN_DELETE THEN MATCH_MP_TAC OPEN_IN_UNION THEN ASM_REWRITE_TAC[];
        UNDISCH_TAC `(u:real^N->bool) SUBSET a` THEN UNDISCH_TAC `(a:real^N->bool) SUBSET K` THEN
        SET_TAC[];
        SET_TAC[]];
      SUBGOAL_THEN `a DELETE (y:real^N) = (K DELETE y) INTER a` SUBST1_TAC THENL
       [UNDISCH_TAC `(a:real^N->bool) SUBSET K` THEN SET_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC CLOSED_IN_CLOSED_INTER THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED]];
    ALL_TAC] THEN
  STRIP_TAC THENL
   [UNDISCH_TAC `a DELETE (y:real^N) = {}` THEN
    MAP_EVERY UNDISCH_TAC [`(x:real^N) IN u`; `(u:real^N->bool) SUBSET a`; `~(y:real^N = x)`] THEN
    SET_TAC[];
    MP_TAC(ISPECL [`a:real^N->bool`; `ba:real^N->bool`] MOI_S4OT_ARC_NOT_CIRCLE) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `a:real^N->bool = K` (fun th -> ASM_REWRITE_TAC[th]) THEN
    MAP_EVERY UNDISCH_TAC [`a DELETE (y:real^N) = K DELETE y`; `(a:real^N->bool) SUBSET K`;
                           `ba = {x:real^N,y}`; `(ba:real^N->bool) SUBSET a`] THEN
    SET_TAC[]]);;

(* Two PL arcs meeting exactly in a common end form a PL arc. *)

let MOI_S4OT_ARC_ORIENT = prove
 (`!(a:real^N->bool) p x.
     pl_cell_with_boundary 1 a {p,x}
     ==> ?h. arc h /\ pl_map_on (interval[vec 0,vec 1]) h /\
             path_image h = a /\ pathstart h = p /\ pathfinish h = x`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^1->real^N` STRIP_ASSUME_TAC o
    MATCH_MP MOI_S4L_CELL1_PL_ARC) THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o MATCH_MP MOI_S4O_PAIR_EQ) THENL
   [EXISTS_TAC `h:real^1->real^N` THEN ASM_REWRITE_TAC[];
    EXISTS_TAC `reversepath(h:real^1->real^N)` THEN
    ASM_SIMP_TAC[ARC_REVERSEPATH; MOI_PL2_PL_REVERSEPATH; PATH_IMAGE_REVERSEPATH;
                 PATHSTART_REVERSEPATH; PATHFINISH_REVERSEPATH]]);;

let MOI_S4OT_ARC_JOIN = prove
 (`!(a1:real^N->bool) a2 p x q.
     pl_cell_with_boundary 1 a1 {p,x} /\ pl_cell_with_boundary 1 a2 {x,q} /\
     a1 INTER a2 = {x}
     ==> pl_cell_with_boundary 1 (a1 UNION a2) {p,q}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`a1:real^N->bool`; `p:real^N`; `x:real^N`] MOI_S4OT_ARC_ORIENT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `h1:real^1->real^N` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`a2:real^N->bool`; `x:real^N`; `q:real^N`] MOI_S4OT_ARC_ORIENT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `h2:real^1->real^N` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPEC `(h1:real^1->real^N) ++ h2` MOI_S4O_ARC_CELL) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC ARC_JOIN THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      MATCH_MP_TAC MOI_PL2_PL_JOINPATHS THEN ASM_REWRITE_TAC[]];
    ASM_SIMP_TAC[PATH_IMAGE_JOIN; PATHSTART_JOIN; PATHFINISH_JOIN]]);;

(* Gluing two PL 2-cells in real^3 along a PL arc of both boundaries. *)

let MOI_S4OT_DISK_GLUE = prove
 (`!(d1:real^3->bool) j1 d2 j2 b bb.
     pl_cell_with_boundary 2 d1 j1 /\ pl_cell_with_boundary 2 d2 j2 /\
     pl_cell_with_boundary 1 b bb /\ d1 INTER d2 = b /\ b SUBSET j1 /\ b SUBSET j2
     ==> pl_cell_with_boundary 2 (d1 UNION d2) ((j1 UNION j2) DIFF (b DIFF bb))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MOI_SS2_CELL_EQ_FSA] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `al:real^1->real^3` STRIP_ASSUME_TAC o
    MATCH_MP MOI_S4L_CELL1_PL_ARC) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `bb:real^3->bool`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `path_image(al:real^1->real^3)`)) THEN
  MATCH_MP_TAC MOI_FSA_GLUE THEN ASM_REWRITE_TAC[]);;

(* In a PL 2-sphere the inner points of a gluing arc are inner points of    *)
(* the union of the two disks.                                              *)

let MOI_S4OT_GLUE_NBHD = prove
 (`!(s:real^3->bool) d1 j1 d2 j2 b bb x.
     pl_sphere 2 s /\ d1 SUBSET s /\ d2 SUBSET s /\
     pl_cell_with_boundary 2 d1 j1 /\ pl_cell_with_boundary 2 d2 j2 /\
     pl_cell_with_boundary 1 b bb /\ d1 INTER d2 = b /\ b SUBSET j1 /\ b SUBSET j2 /\
     x IN b /\ ~(x IN bb)
     ==> ?u. open_in (subtopology euclidean s) u /\ x IN u /\ u SUBSET d1 UNION d2`,
  REPEAT STRIP_TAC THEN
  EXISTS_TAC `(d1 UNION d2) DIFF ((j1 UNION j2) DIFF (b DIFF bb)):real^3->bool` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC MOI_S4H_DISK_OPEN THEN ASM_REWRITE_TAC[UNION_SUBSET] THEN
    MATCH_MP_TAC MOI_S4OT_DISK_GLUE THEN ASM_REWRITE_TAC[];
    MAP_EVERY UNDISCH_TAC [`(d1:real^3->bool) INTER d2 = b`; `(x:real^3) IN b`;
                           `~((x:real^3) IN bb)`] THEN
    SET_TAC[]]);;

(* A line chart at an inner point of a PL arc which is all of t near x. *)

let MOI_S4OT_LINE_CHART_AT = prove
 (`!(t:real^N->bool) c p q x u0.
     pl_cell_with_boundary 1 c {p,q} /\ x IN c /\ ~(x = p) /\ ~(x = q) /\
     open u0 /\ x IN u0 /\ t INTER u0 = c INTER u0
     ==> ?u (h:real^N->real^1) h'.
           open u /\ x IN u /\
           homeomorphism (t INTER u,IMAGE h (t INTER u)) (h,h') /\
           open (IMAGE h (t INTER u))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:real^N->bool`; `p:real^N`; `q:real^N`] MOI_S4OT_ARC_ORIENT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `g:real^1->real^N` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPEC `g:real^1->real^N` HOMEOMORPHISM_ARC) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->real^1` (LABEL_TAC "HOM")) THEN
  USE_THEN "HOM" (STRIP_ASSUME_TAC o REWRITE_RULE[homeomorphism]) THEN
  SUBGOAL_THEN `open(u0 DIFF {p:real^N,q})` ASSUME_TAC THENL
   [MATCH_MP_TAC OPEN_DIFF THEN ASM_SIMP_TAC[FINITE_IMP_CLOSED; FINITE_INSERT; FINITE_EMPTY];
    ALL_TAC] THEN
  EXISTS_TAC `u0 DIFF {p:real^N,q}` THEN
  MAP_EVERY EXISTS_TAC [`k:real^N->real^1`; `g:real^1->real^N`] THEN
  SUBGOAL_THEN `t INTER (u0 DIFF {p:real^N,q}) = c INTER (u0 DIFF {p,q})` SUBST1_TAC THENL
   [UNDISCH_TAC `(t:real^N->bool) INTER u0 = c INTER u0` THEN SET_TAC[]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[IN_DIFF; IN_INSERT; NOT_IN_EMPTY];
    MATCH_MP_TAC HOMEOMORPHISM_OF_SUBSETS THEN
    MAP_EVERY EXISTS_TAC [`c:real^N->bool`; `interval[vec 0:real^1,vec 1]`] THEN
    ONCE_REWRITE_TAC[HOMEOMORPHISM_SYM] THEN USE_THEN "HOM" (fun th -> REWRITE_TAC[th]) THEN
    UNDISCH_TAC `IMAGE (k:real^N->real^1) c = interval[vec 0,vec 1]` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (k:real^N->real^1) (c INTER (u0 DIFF {p,q})) =
                {s | s IN interval[vec 0,vec 1] /\ (g:real^1->real^N) s IN u0 DIFF {p,q}}`
  SUBST1_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`!x:real^1. x IN interval[vec 0,vec 1] ==> (k:real^N->real^1)(g x) = x`;
      `IMAGE (g:real^1->real^N) (interval[vec 0,vec 1]) = c`;
      `!y:real^N. y IN c ==> (g:real^1->real^N)(k y) = y`;
      `IMAGE (k:real^N->real^1) c = interval[vec 0,vec 1]`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`g:real^1->real^N`; `interval[vec 0:real^1,vec 1]`; `u0 DIFF {p:real^N,q}`]
    CONTINUOUS_OPEN_IN_PREIMAGE) THEN
  ASM_REWRITE_TAC[OPEN_IN_OPEN] THEN
  DISCH_THEN(X_CHOOSE_THEN `o1:real^1->bool` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "EQ"))) THEN
  USE_THEN "EQ" (fun th -> REWRITE_TAC[th]) THEN
  SUBGOAL_THEN `~((vec 0:real^1) IN o1) /\ ~((vec 1:real^1) IN o1)` ASSUME_TAC THENL
   [USE_THEN "EQ" (MP_TAC o GSYM) THEN
    REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM] THEN
    DISCH_THEN(fun th -> MP_TAC(SPEC `vec 0:real^1` th) THEN MP_TAC(SPEC `vec 1:real^1` th)) THEN
    REWRITE_TAC[ENDS_IN_UNIT_INTERVAL] THEN
    UNDISCH_TAC `pathstart (g:real^1->real^N) = p` THEN
    UNDISCH_TAC `pathfinish (g:real^1->real^N) = q` THEN
    REWRITE_TAC[pathstart; pathfinish] THEN REPEAT DISCH_TAC THEN
    ASM_REWRITE_TAC[IN_DIFF; IN_INSERT] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `interval[vec 0:real^1,vec 1] INTER o1 = interval(vec 0,vec 1) INTER o1`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`vec 0:real^1`; `vec 1:real^1`] CLOSED_OPEN_INTERVAL_1) THEN
    REWRITE_TAC[DROP_VEC; REAL_POS] THEN DISCH_THEN SUBST1_TAC THEN
    UNDISCH_TAC `~((vec 0:real^1) IN o1) /\ ~((vec 1:real^1) IN o1)` THEN SET_TAC[];
    MATCH_MP_TAC OPEN_INTER THEN ASM_REWRITE_TAC[OPEN_INTERVAL]]);;

(* ------------------------------------------------------------------------- *)
(* Combinatorics of kk at faces and edges; facts on the face disks          *)
(* and the tetra balls from fdisk and resid alone (moi_s34_outer is what    *)
(* this file proves, so the meeting lemmas of pc_moi_s34_recogb, which      *)
(* assume it, are not available here).                                      *)
(* ------------------------------------------------------------------------- *)

let MOI_S4OT_TUBE_LF = prove
 (`!(tt:(real^N->bool)->bool) kk.
     moi_s34_tube tt kk
     ==> lf_simplicial_complex kk /\ lf_simplicial_complex tt /\ kk SUBSET tt /\
         combinatorial_manifold_with_boundary 3 kk`,
  SIMP_TAC[moi_s34_tube; combinatorial_manifold_with_boundary; simplicial_subcomplex]);;

let MOI_S4OT_SIMP_VERTEX = prove
 (`!(tt:(real^N->bool)->bool) kk n s.
     moi_s34_tube tt kk /\ s IN moi_s34_simp kk (&n) ==> ?v. {v} IN kk /\ v IN s`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_FM3_LF_VERTEX THEN
  ASM_MESON_TAC[MOI_S4OT_TUBE_LF; MOI_S4H_SIMP_KK; MOI_S4H_SIMP_NE]);;

let MOI_S4OT_STAR_FINITE = prove
 (`!(tt:(real^N->bool)->bool) kk n q.
     moi_s34_tube tt kk /\ q IN kk /\ ~(q = {})
     ==> FINITE {r | r IN moi_s34_simp kk (&n) /\ q SUBSET r}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`kk:(real^N->bool)->bool`; `q:real^N->bool`] MOI_FM3_LF_VERTEX) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[MOI_S4OT_TUBE_LF]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real^N` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{t | t IN kk /\ (v:real^N) IN t}` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC MOI_FM3_STAR_FINITE THEN
    CONJ_TAC THENL [ASM_MESON_TAC[MOI_S4OT_TUBE_LF]; ASM SET_TAC[]];
    REWRITE_TAC[SUBSET; IN_ELIM_THM; moi_s34_simp] THEN ASM SET_TAC[]]);;

(* A 2-simplex of kk lies in one 3-simplex (boundary face) or two. *)

let MOI_S4OT_FACE_TETS = prove
 (`!(tt:(real^N->bool)->bool) kk s.
     moi_s34_tube tt kk /\ s IN moi_s34_simp kk (&2)
     ==> FINITE {r | r IN moi_s34_simp kk (&3) /\ s SUBSET r} /\
         (s SUBSET complex_boundary kk
          ==> ?r. {r' | r' IN moi_s34_simp kk (&3) /\ s SUBSET r'} = {r}) /\
         (~(s SUBSET complex_boundary kk)
          ==> ?r1 r2. ~(r1 = r2) /\
                      {r' | r' IN moi_s34_simp kk (&3) /\ s SUBSET r'} = {r1,r2})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4OT_TUBE_LF) THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `2`; `s:real^N->bool`]
    MOI_S4OT_SIMP_VERTEX) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `v:real^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(s:real^N->bool) IN kk /\ aff_dim s = &2` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(s:real^N->bool) IN moi_s34_simp kk (&2)` THEN
    REWRITE_TAC[moi_s34_simp; IN_ELIM_THM];
    ALL_TAC] THEN
  ABBREV_TAC `T3 = {r' | r' IN moi_s34_simp kk (&3) /\ (s:real^N->bool) SUBSET r'}` THEN
  SUBGOAL_THEN `T3 SUBSET {r | r IN tt /\ aff_dim r = &3 /\ (s:real^N->bool) SUBSET r}`
  ASSUME_TAC THENL
   [EXPAND_TAC "T3" THEN REWRITE_TAC[SUBSET; IN_ELIM_THM; moi_s34_simp] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE {r | r IN tt /\ aff_dim r = &3 /\ (s:real^N->bool) SUBSET r}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{r | r IN tt /\ (v:real^N) IN r}` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MOI_S4O_STAR_FINITE_TT THEN EXISTS_TAC `kk:(real^N->bool)->bool` THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE(T3:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[FINITE_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `CARD(T3:(real^N->bool)->bool) <= 2` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`;
                   `s:real^N->bool`] MOI_S4O_TT_TRI2) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
    MATCH_MP_TAC CARD_SUBSET THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(T3:(real^N->bool)->bool = {})` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`;
                   `s:real^N->bool`] MOI_S4O_KK_PURE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `r:real^N->bool` STRIP_ASSUME_TAC) THEN
    EXPAND_TAC "T3" THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM; moi_s34_simp] THEN
    EXISTS_TAC `r:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(s:real^N->bool) SUBSET complex_boundary kk <=> CARD(T3:(real^N->bool)->bool) = 1`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`kk:(real^N->bool)->bool`; `s:real^N->bool`] MOI_S4O_TRI_BOUNDARY) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN EXPAND_TAC "T3" THEN
    REWRITE_TAC[moi_s34_simp; IN_ELIM_THM; GSYM CONJ_ASSOC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [DISCH_TAC THEN ASM_MESON_TAC[MOI_FM3_CARD_EQ_1];
    DISCH_TAC THEN MATCH_MP_TAC MOI_S4O_CARD2 THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~(CARD(T3:(real^N->bool)->bool) = 0)` MP_TAC THENL
     [ASM_MESON_TAC[CARD_EQ_0]; UNDISCH_TAC `CARD(T3:(real^N->bool)->bool) <= 2` THEN
      UNDISCH_TAC `~(CARD(T3:(real^N->bool)->bool) = 1)` THEN ARITH_TAC]]);;

(* Two distinct 3-simplices of kk share at most one 2-face. *)

let MOI_S4OT_TETS_FACE = prove
 (`!(tt:(real^N->bool)->bool) kk r r' s s'.
     moi_s34_tube tt kk /\ r IN moi_s34_simp kk (&3) /\ r' IN moi_s34_simp kk (&3) /\
     ~(r = r') /\ s IN moi_s34_simp kk (&2) /\ s' IN moi_s34_simp kk (&2) /\
     s SUBSET r /\ s SUBSET r' /\ s' SUBSET r /\ s' SUBSET r'
     ==> s = s'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4OT_TUBE_LF) THEN
  SUBGOAL_THEN `(r:real^N->bool) IN kk /\ r' IN kk /\ aff_dim r = &3 /\ aff_dim r' = &3`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`(r:real^N->bool) IN moi_s34_simp kk (&3)`;
                           `(r':real^N->bool) IN moi_s34_simp kk (&3)`] THEN
    REWRITE_TAC[moi_s34_simp; IN_ELIM_THM] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`kk:(real^N->bool)->bool`; `r:real^N->bool`; `r':real^N->bool`]
    MOI_FM3_LF_INTER) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(r INTER r':real^N->bool) IN kk` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FM3_LF_FACE]; ALL_TAC] THEN
  SUBGOAL_THEN `~(r INTER r':real^N->bool = r)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `r:real^N->bool`;
                   `r':real^N->bool`; `3`] MOI_S4G_SUB_EQ) THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `aff_dim(r INTER r':real^N->bool) < &3` ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `aff_dim(r:real^N->bool) = &3`)) THEN
    MATCH_MP_TAC FACE_OF_AFF_DIM_LT THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[MOI_S4H_KK_CONVEX];
    ALL_TAC] THEN
  SUBGOAL_THEN `(r INTER r':real^N->bool) IN moi_s34_simp kk (&2)` ASSUME_TAC THENL
   [REWRITE_TAC[moi_s34_simp; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`s:real^N->bool`; `r INTER r':real^N->bool`] AFF_DIM_SUBSET) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `(s:real^N->bool) IN moi_s34_simp kk (&2)` THEN
    REWRITE_TAC[moi_s34_simp; IN_ELIM_THM] THEN
    UNDISCH_TAC `aff_dim(r INTER r':real^N->bool) < &3` THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `s:real^N->bool`;
                 `r INTER r':real^N->bool`; `2`] MOI_S4G_SUB_EQ) THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `s':real^N->bool`;
                 `r INTER r':real^N->bool`; `2`] MOI_S4G_SUB_EQ) THEN
  ASM_REWRITE_TAC[SUBSET_INTER] THEN MESON_TAC[]);;

(* Facts on a face disk dd s from fdisk. *)

let MOI_S4OT_DD_FACTS = prove
 (`!(tt:(real^N->bool)->bool) kk (f1:real^N->real^3) car dd s.
     moi_s34_tube tt kk /\ moi_s34_fdisk tt kk f1 car dd /\ s IN moi_s34_simp kk (&2)
     ==> compact (dd s) /\
         dd s INTER IMAGE f1 (moi_s34_nb tt kk) = dd s INTER IMAGE f1 (moi_s34_bd tt kk) /\
         (!w. {w} IN kk /\ ~(w IN s) ==> dd s INTER IMAGE f1 (moi_s34_vb tt kk w) = {}) /\
         (!v. {v} IN kk /\ v IN s
              ==> pl_cell_with_boundary 1 (dd s INTER IMAGE f1 (moi_s34_vb tt kk v))
                    (UNIONS {dd s INTER IMAGE f1 (moi_s34_sd tt kk g) | g |
                             g IN moi_s34_simp kk (&1) /\ v IN g /\ g SUBSET s})) /\
         (!g. g IN moi_s34_simp kk (&1) /\ g SUBSET s
              ==> ?p. dd s INTER IMAGE f1 (moi_s34_sd tt kk g) = {p}) /\
         (!g. g IN moi_s34_simp kk (&1) /\ ~(g SUBSET s)
              ==> dd s INTER IMAGE f1 (moi_s34_sd tt kk g) = {}) /\
         (!s'. s' IN moi_s34_simp kk (&2) /\ ~(s' = s) ==> dd s INTER dd s' = {})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(s:real^N->bool) IN kk` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_S4H_SIMP_KK]; ALL_TAC] THEN
  UNDISCH_TAC `moi_s34_fdisk tt kk (f1:real^N->real^3) car dd` THEN
  REWRITE_TAC[moi_s34_fdisk] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o SPEC `s:real^N->bool`) (LABEL_TAC "dd2")) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> let cs = CONJUNCTS th in
    LABEL_TAC "cell" (el 0 cs) THEN LABEL_TAC "nb" (el 1 cs) THEN
    LABEL_TAC "dj" (el 3 cs) THEN LABEL_TAC "arc" (el 4 cs) THEN LABEL_TAC "pt" (el 5 cs)) THEN
  SUBGOAL_THEN `!w. {w} IN kk /\ ~(w IN s)
                    ==> (dd:(real^N->bool)->real^3->bool) s INTER
                        IMAGE f1 (moi_s34_vb tt kk w) = {}`
  (LABEL_TAC "dvb") THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM DISJOINT] THEN USE_THEN "dj" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [USE_THEN "cell" (MP_TAC o MATCH_MP MOI_S4G_CELL_FACTS) THEN SIMP_TAC[];
    USE_THEN "nb" ACCEPT_TAC;
    USE_THEN "dvb" ACCEPT_TAC;
    USE_THEN "arc" ACCEPT_TAC;
    REPEAT STRIP_TAC THEN USE_THEN "pt" (MP_TAC o SPEC `g:real^N->bool`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; MESON_TAC[]];
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `g:real^N->bool`;
                   `s:real^N->bool`] MOI_S4H_EDGE_OUT) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `g:real^N->bool`;
                   `w:real^N`] MOI_S4G_SD_SUB_VB) THEN
    ASM_REWRITE_TAC[] THEN
    USE_THEN "dvb" (MP_TAC o SPEC `w:real^N`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SET_TAC[]];
    REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM DISJOINT] THEN USE_THEN "dd2" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[]]);;

(* Facts on a tetra ball rr r from resid. *)

let MOI_S4OT_RR_FACTS = prove
 (`!(tt:(real^N->bool)->bool) kk (f1:real^N->real^3) car dd rr r.
     moi_s34_tube tt kk /\ moi_s34_resid tt kk f1 car dd rr /\ r IN moi_s34_simp kk (&3)
     ==> compact (rr r) /\
         rr r INTER IMAGE f1 (moi_s34_nb tt kk) = rr r INTER IMAGE f1 (moi_s34_bd tt kk) /\
         (!v. {v} IN kk /\ v IN r
              ==> pl_cell_with_boundary 2 (rr r INTER IMAGE f1 (moi_s34_vb tt kk v))
                    (UNIONS {dd s INTER IMAGE f1 (moi_s34_vb tt kk v) | s |
                             s IN moi_s34_simp kk (&2) /\ v IN s /\ s SUBSET r} UNION
                     UNIONS {rr r INTER IMAGE f1 (moi_s34_sd tt kk g) | g |
                             g IN moi_s34_simp kk (&1) /\ v IN g /\ g SUBSET r})) /\
         (!g. g IN moi_s34_simp kk (&1) /\ g SUBSET r
              ==> pl_cell_with_boundary 1 (rr r INTER IMAGE f1 (moi_s34_sd tt kk g))
                    (UNIONS {dd s INTER IMAGE f1 (moi_s34_sd tt kk g) | s |
                             s IN moi_s34_simp kk (&2) /\ g SUBSET s /\ s SUBSET r})) /\
         (!w. {w} IN kk /\ ~(w IN r) ==> rr r INTER IMAGE f1 (moi_s34_vb tt kk w) = {}) /\
         (!s. s IN moi_s34_simp kk (&2) /\ ~(s SUBSET r) ==> rr r INTER dd s = {}) /\
         (!s. s IN moi_s34_simp kk (&2) /\ s SUBSET r ==> dd s SUBSET rr r) /\
         (!r'. r' IN moi_s34_simp kk (&3) /\ ~(r' = r)
               ==> rr r INTER rr r' =
                   UNIONS {dd s | s | s IN moi_s34_simp kk (&2) /\ s SUBSET r /\
                                      s SUBSET r'}) /\
         (!g. g IN moi_s34_simp kk (&1) /\ ~(g SUBSET r)
              ==> rr r INTER IMAGE f1 (moi_s34_sd tt kk g) = {})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `moi_s34_resid tt kk (f1:real^N->real^3) car dd rr` THEN
  REWRITE_TAC[moi_s34_resid] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o SPEC `r:real^N->bool`)
    (CONJUNCTS_THEN2 (LABEL_TAC "rr2") (K ALL_TAC))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> let cs = CONJUNCTS th in
    LABEL_TAC "ball" (el 0 cs) THEN LABEL_TAC "fr" (el 2 cs) THEN
    LABEL_TAC "nb" (el 3 cs) THEN LABEL_TAC "patch" (el 4 cs) THEN
    LABEL_TAC "rim" (el 5 cs) THEN LABEL_TAC "dj" (el 6 cs) THEN LABEL_TAC "djd" (el 7 cs)) THEN
  SUBGOAL_THEN `compact((rr:(real^N->bool)->real^3->bool) r)` (LABEL_TAC "cpt") THENL
   [MP_TAC(ISPEC `(rr:(real^N->bool)->real^3->bool) r` MOI_S4G_BALL_CELL) THEN
    ANTS_TAC THENL [USE_THEN "ball" ACCEPT_TAC; MESON_TAC[MOI_S4G_CELL_FACTS]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!w. {w} IN kk /\ ~(w IN r)
                    ==> (rr:(real^N->bool)->real^3->bool) r INTER
                        IMAGE f1 (moi_s34_vb tt kk w) = {}`
  (LABEL_TAC "rvb") THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM DISJOINT] THEN USE_THEN "dj" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [USE_THEN "cpt" ACCEPT_TAC;
    USE_THEN "nb" ACCEPT_TAC;
    USE_THEN "patch" ACCEPT_TAC;
    USE_THEN "rim" ACCEPT_TAC;
    USE_THEN "rvb" ACCEPT_TAC;
    REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM DISJOINT] THEN USE_THEN "djd" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `frontier((rr:(real^N->bool)->real^3->bool) r)` THEN CONJ_TAC THENL
     [USE_THEN "fr" SUBST1_TAC THEN
      MATCH_MP_TAC(SET_RULE `!a b c:real^3->bool. a SUBSET b ==> a SUBSET b UNION c`) THEN
      GEN_REWRITE_TAC I [SUBSET] THEN REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM] THEN
      ASM_MESON_TAC[];
      USE_THEN "cpt" (fun th -> SIMP_TAC[FRONTIER_SUBSET_CLOSED; COMPACT_IMP_CLOSED; th])];
    REPEAT STRIP_TAC THEN USE_THEN "rr2" MATCH_MP_TAC THEN ASM_MESON_TAC[];
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `g:real^N->bool`;
                   `r:real^N->bool`] MOI_S4H_EDGE_OUT) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[MOI_S4H_SIMP_KK]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `g:real^N->bool`;
                   `w:real^N`] MOI_S4G_SD_SUB_VB) THEN
    ASM_REWRITE_TAC[] THEN
    USE_THEN "rvb" (MP_TAC o SPEC `w:real^N`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SET_TAC[]]]);;

(* Arcs: an inner point, and the other end. *)

let MOI_S4OT_CELL1_FACTS = prove
 (`!a ba:real^N->bool.
     pl_cell_with_boundary 1 a ba
     ==> compact a /\ ba SUBSET a /\ (?z. z IN a /\ ~(z IN ba)) /\
         (!x. x IN ba ==> ?y. ~(y = x) /\ ba = {x,y})`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^1->real^N` STRIP_ASSUME_TAC o
    MATCH_MP MOI_S4L_CELL1_PL_ARC) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `path_image(h:real^1->real^N)`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `ba:real^N->bool`)) THEN
  MP_TAC(ISPEC `h:real^1->real^N` ARC_DISTINCT_ENDS) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ASM_SIMP_TAC[COMPACT_PATH_IMAGE; ARC_IMP_PATH; INSERT_SUBSET; EMPTY_SUBSET;
               PATHSTART_IN_PATH_IMAGE; PATHFINISH_IN_PATH_IMAGE] THEN
  CONJ_TAC THENL
   [EXISTS_TAC `(h:real^1->real^N)(lift(&1 / &2))` THEN
    REWRITE_TAC[path_image; IN_INSERT; NOT_IN_EMPTY; pathstart; pathfinish] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; LIFT_DROP] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV;
      ALL_TAC] THEN
    UNDISCH_TAC `arc(h:real^1->real^N)` THEN REWRITE_TAC[arc] THEN
    DISCH_THEN(MP_TAC o CONJUNCT2) THEN
    DISCH_THEN(fun th -> MP_TAC(SPECL [`lift(&1 / &2)`; `vec 0:real^1`] th) THEN
                         MP_TAC(SPECL [`lift(&1 / &2)`; `vec 1:real^1`] th)) THEN
    REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; LIFT_DROP; GSYM DROP_EQ] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN MESON_TAC[];
    REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN REPEAT STRIP_TAC THENL
     [EXISTS_TAC `pathfinish(h:real^1->real^N)` THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
      EXISTS_TAC `pathstart(h:real^1->real^N)` THEN ASM_REWRITE_TAC[] THEN
      REPEAT CONJ_TAC THEN TRY(ASM_MESON_TAC[]) THEN SET_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* The rim of an edge g.  D_g = f1(sd g) is a PL 2-cell bounded by          *)
(* the rim R_g, a PL circle; the rim arcs rr r INTER D_g of the 3-simplices *)
(* r at g lie in R_g, with ends the face points dd s INTER D_g.  Points of  *)
(* their union other than boundary-face points are inner points of it in    *)
(* R_g (one arc, or the two arcs at an interior face, joined), and the     *)
(* boundary-face points are limits of the rest of R_g.                      *)
(* ------------------------------------------------------------------------- *)

let MOI_S4OT_RIM_SETUP = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car dd rr g.
     moi_s34_tube tt kk /\ moi_s34_frame tt kk h ep f1 car /\
     moi_s34_fdisk tt kk f1 car dd /\ moi_s34_resid tt kk f1 car dd rr /\
     g IN moi_s34_simp kk (&1)
     ==> pl_cell_with_boundary 2 (IMAGE f1 (moi_s34_sd tt kk g))
           (IMAGE f1 (moi_s34_sd tt kk g INTER moi_s34_bd tt kk)) /\
         pl_sphere 1 (IMAGE f1 (moi_s34_sd tt kk g INTER moi_s34_bd tt kk)) /\
         compact (IMAGE f1 (moi_s34_sd tt kk g)) /\
         compact (IMAGE f1 (moi_s34_sd tt kk g INTER moi_s34_bd tt kk)) /\
         (!r. r IN moi_s34_simp kk (&3)
              ==> rr r INTER IMAGE f1 (moi_s34_sd tt kk g) SUBSET
                  IMAGE f1 (moi_s34_sd tt kk g INTER moi_s34_bd tt kk)) /\
         (!s. s IN moi_s34_simp kk (&2)
              ==> dd s INTER IMAGE f1 (moi_s34_sd tt kk g) SUBSET
                  IMAGE f1 (moi_s34_sd tt kk g INTER moi_s34_bd tt kk)) /\
         FINITE {r | r IN moi_s34_simp kk (&3) /\ g SUBSET r}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                 `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`]
    MOI_S4G_FRAME_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `g:real^N->bool` o CONJUNCT2 o
    CONJUNCT2 o CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `g:real^N->bool`]
    MOI_S4G_SD_NB) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`1`; `IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g)`;
                   `IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g INTER moi_s34_bd tt kk)`]
      MOI_S4O_CELL_SPHERE) THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[];
    FIRST_ASSUM(MP_TAC o MATCH_MP MOI_S4G_CELL_FACTS) THEN SIMP_TAC[];
    FIRST_ASSUM(MP_TAC o MATCH_MP MOI_S4G_CELL_BD_COMPACT) THEN SIMP_TAC[];
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                   `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                   `dd:(real^N->bool)->real^3->bool`; `rr:(real^N->bool)->real^3->bool`;
                   `r:real^N->bool`; `moi_s34_sd tt kk (g:real^N->bool)`] MOI_S4G_RR_SUB) THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                   `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                   `dd:(real^N->bool)->real^3->bool`; `s:real^N->bool`;
                   `moi_s34_sd tt kk (g:real^N->bool)`] MOI_S4G_DD_SUB) THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    MATCH_MP_TAC MOI_S4OT_STAR_FINITE THEN EXISTS_TAC `tt:(real^N->bool)->bool` THEN
    ASM_MESON_TAC[MOI_S4H_SIMP_KK; MOI_S4H_SIMP_NE]]);;

(* Inner points of the union of the rim arcs. *)

let MOI_S4OT_EDGE_LOC = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car dd rr g x.
     moi_s34_tube tt kk /\ moi_s34_frame tt kk h ep f1 car /\
     moi_s34_fdisk tt kk f1 car dd /\ moi_s34_resid tt kk f1 car dd rr /\
     g IN moi_s34_simp kk (&1) /\
     x IN UNIONS {rr r INTER IMAGE f1 (moi_s34_sd tt kk g) | r |
                  r IN moi_s34_simp kk (&3) /\ g SUBSET r} /\
     ~(x IN UNIONS {dd s INTER IMAGE f1 (moi_s34_sd tt kk g) | s |
                    s IN moi_s34_simp kk (&2) /\ g SUBSET s /\
                    s SUBSET complex_boundary kk})
     ==> ?u. open_in (subtopology euclidean
                       (IMAGE f1 (moi_s34_sd tt kk g INTER moi_s34_bd tt kk))) u /\
             x IN u /\
             u SUBSET UNIONS {rr r INTER IMAGE f1 (moi_s34_sd tt kk g) | r |
                              r IN moi_s34_simp kk (&3) /\ g SUBSET r}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                `dd:(real^N->bool)->real^3->bool`; `rr:(real^N->bool)->real^3->bool`;
                `g:real^N->bool`] MOI_S4OT_RIM_SETUP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `D = IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g)` THEN
  ABBREV_TAC `R = IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g INTER moi_s34_bd tt kk)` THEN
  FIRST_ASSUM(MP_TAC o REWRITE_RULE[UNIONS_GSPEC; IN_ELIM_THM] o check (fun th ->
    aconv (concl th) `x IN UNIONS {(rr:(real^N->bool)->real^3->bool) r INTER D | r |
                             r IN moi_s34_simp kk (&3) /\ (g:real^N->bool) SUBSET r}`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `dd:(real^N->bool)->real^3->bool`;
                 `rr:(real^N->bool)->real^3->bool`; `r:real^N->bool`] MOI_S4OT_RR_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> let cs = CONJUNCTS th in
    MP_TAC(SPEC `g:real^N->bool` (el 3 cs)) THEN LABEL_TAC "rrr" (el 7 cs) THEN
    LABEL_TAC "rdd" (el 5 cs) THEN LABEL_TAC "ddr" (el 6 cs)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ASM_CASES_TAC
   `(x:real^3) IN UNIONS {(dd:(real^N->bool)->real^3->bool) s INTER D | s |
                          s IN moi_s34_simp kk (&2) /\ (g:real^N->bool) SUBSET s /\
                          s SUBSET r}`
  THENL
   [ALL_TAC;
    EXISTS_TAC `((rr:(real^N->bool)->real^3->bool) r INTER D) DIFF
                UNIONS {(dd:(real^N->bool)->real^3->bool) s INTER D | s |
                        s IN moi_s34_simp kk (&2) /\ (g:real^N->bool) SUBSET s /\
                        s SUBSET r}` THEN
    CONJ_TAC THENL [MATCH_MP_TAC MOI_S4H_ARC_OPEN THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[IN_DIFF]; ALL_TAC] THEN
    GEN_REWRITE_TAC I [SUBSET] THEN REWRITE_TAC[IN_DIFF; UNIONS_GSPEC; IN_ELIM_THM] THEN
    X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN EXISTS_TAC `r:real^N->bool` THEN
    ASM_REWRITE_TAC[]] THEN
  (* x is the point of a face s of r at g; s is an interior face *)
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[UNIONS_GSPEC; IN_ELIM_THM] o check (fun th ->
    aconv (concl th) `(x:real^3) IN UNIONS {(dd:(real^N->bool)->real^3->bool) s INTER D | s |
                          s IN moi_s34_simp kk (&2) /\ (g:real^N->bool) SUBSET s /\
                          s SUBSET r}`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `~((s:real^N->bool) SUBSET complex_boundary kk)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    UNDISCH_TAC `~((x:real^3) IN UNIONS {(dd:(real^N->bool)->real^3->bool) s INTER D | s |
                   s IN moi_s34_simp kk (&2) /\ (g:real^N->bool) SUBSET s /\
                   s SUBSET complex_boundary kk})` THEN
    REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `s:real^N->bool`]
    MOI_S4OT_FACE_TETS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `ra:real^N->bool` (X_CHOOSE_THEN `rb:real^N->bool`
    STRIP_ASSUME_TAC) o CONJUNCT2) THEN
  SUBGOAL_THEN `?r'. r' IN moi_s34_simp kk (&3) /\ (s:real^N->bool) SUBSET r' /\ ~(r' = r)`
  STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[EXTENSION; IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY] o
      check (fun th -> is_eq(concl th) && rand(concl th) = `{ra:real^N->bool,rb}`)) THEN
    DISCH_THEN(fun th -> MP_TAC(SPEC `ra:real^N->bool` th) THEN
                         MP_TAC(SPEC `rb:real^N->bool` th)) THEN
    REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    ASM_CASES_TAC `r:real^N->bool = ra` THENL
     [EXISTS_TAC `rb:real^N->bool` THEN ASM_REWRITE_TAC[];
      EXISTS_TAC `ra:real^N->bool` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(g:real^N->bool) SUBSET r'` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `dd:(real^N->bool)->real^3->bool`;
                 `rr:(real^N->bool)->real^3->bool`; `r':real^N->bool`] MOI_S4OT_RR_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `g:real^N->bool` o el 3 o CONJUNCTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  (* the two rim arcs meet exactly at x *)
  SUBGOAL_THEN `((rr:(real^N->bool)->real^3->bool) r INTER D) INTER (rr r' INTER D) = {x}`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `(rr:(real^N->bool)->real^3->bool) r INTER rr r' =
                  (dd:(real^N->bool)->real^3->bool) s` ASSUME_TAC THENL
     [USE_THEN "rrr" (MP_TAC o SPEC `r':real^N->bool`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
      SUBGOAL_THEN `{(dd:(real^N->bool)->real^3->bool) s' | s' |
                     s' IN moi_s34_simp kk (&2) /\ s' SUBSET r /\ s' SUBSET r'} = {dd s}`
      (fun th -> REWRITE_TAC[th; UNIONS_1]) THEN
      GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_ELIM_THM; IN_SING] THEN
      X_GEN_TAC `y:real^3->bool` THEN
      EQ_TAC THENL
       [DISCH_THEN(X_CHOOSE_THEN `s':real^N->bool` STRIP_ASSUME_TAC) THEN
        SUBGOAL_THEN `s':real^N->bool = s` ASSUME_TAC THENL
         [MATCH_MP_TAC MOI_S4OT_TETS_FACE THEN
          MAP_EVERY EXISTS_TAC [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                                `r:real^N->bool`; `r':real^N->bool`] THEN
          ASM_REWRITE_TAC[];
          ASM_REWRITE_TAC[]];
        DISCH_THEN SUBST1_TAC THEN EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `f1:real^N->real^3`;
                   `car:(real^N->bool)->real^3->bool`; `dd:(real^N->bool)->real^3->bool`;
                   `s:real^N->bool`] MOI_S4OT_DD_FACTS) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `g:real^N->bool` o el 4 o CONJUNCTS) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `p:real^3`) THEN
    MAP_EVERY UNDISCH_TAC
     [`(dd:(real^N->bool)->real^3->bool) s INTER D = {p}`;
      `(x:real^3) IN (dd:(real^N->bool)->real^3->bool) s INTER D`;
      `(rr:(real^N->bool)->real^3->bool) r INTER rr r' =
       (dd:(real^N->bool)->real^3->bool) s`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  (* the ends of both arcs *)
  ABBREV_TAC `E = UNIONS {(dd:(real^N->bool)->real^3->bool) s INTER D | s |
                          s IN moi_s34_simp kk (&2) /\ (g:real^N->bool) SUBSET s /\
                          s SUBSET r}` THEN
  ABBREV_TAC `E' = UNIONS {(dd:(real^N->bool)->real^3->bool) s INTER D | s |
                           s IN moi_s34_simp kk (&2) /\ (g:real^N->bool) SUBSET s /\
                           s SUBSET r'}` THEN
  SUBGOAL_THEN `(x:real^3) IN E /\ x IN E'` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["E"; "E'"] THEN REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM] THEN
    CONJ_TAC THEN EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(rr:(real^N->bool)->real^3->bool) r INTER D`; `E:real^3->bool`]
    MOI_S4OT_CELL1_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `x:real^3` o last o CONJUNCTS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`(rr:(real^N->bool)->real^3->bool) r' INTER D`; `E':real^3->bool`]
    MOI_S4OT_CELL1_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `x:real^3` o last o CONJUNCTS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `y':real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `pl_cell_with_boundary 1 ((rr:(real^N->bool)->real^3->bool) r INTER D) {y,x}`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `{y:real^3,x} = E` SUBST1_TAC THENL
     [UNDISCH_TAC `E = {x:real^3,y}` THEN SET_TAC[]; FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_cell_with_boundary 1 ((rr:(real^N->bool)->real^3->bool) r' INTER D) {x,y'}`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `{x:real^3,y'} = E'` SUBST1_TAC THENL
     [UNDISCH_TAC `E' = {x:real^3,y'}` THEN SET_TAC[]; FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(rr:(real^N->bool)->real^3->bool) r INTER D`;
                 `(rr:(real^N->bool)->real^3->bool) r' INTER D`;
                 `y:real^3`; `x:real^3`; `y':real^3`] MOI_S4OT_ARC_JOIN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  EXISTS_TAC `((rr:(real^N->bool)->real^3->bool) r INTER D UNION rr r' INTER D) DIFF
              {y:real^3,y'}` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MOI_S4H_ARC_OPEN THEN ASM_REWRITE_TAC[UNION_SUBSET] THEN
    ASM_SIMP_TAC[];
    ASM_REWRITE_TAC[IN_DIFF; IN_UNION; IN_INSERT; NOT_IN_EMPTY];
    GEN_REWRITE_TAC I [SUBSET] THEN REWRITE_TAC[IN_DIFF; IN_UNION; UNIONS_GSPEC; IN_ELIM_THM] THEN
    X_GEN_TAC `z:real^3` THEN STRIP_TAC THENL
     [EXISTS_TAC `r:real^N->bool`; EXISTS_TAC `r':real^N->bool`] THEN
    ASM_REWRITE_TAC[]]);;

(* The point of a boundary face at g is a limit of the rest of the rim. *)

let MOI_S4OT_EDGE_END = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car dd rr g s.
     moi_s34_tube tt kk /\ moi_s34_frame tt kk h ep f1 car /\
     moi_s34_fdisk tt kk f1 car dd /\ moi_s34_resid tt kk f1 car dd rr /\
     g IN moi_s34_simp kk (&1) /\ s IN moi_s34_simp kk (&2) /\ g SUBSET s /\
     s SUBSET complex_boundary kk
     ==> dd s INTER IMAGE f1 (moi_s34_sd tt kk g) SUBSET
         closure (IMAGE f1 (moi_s34_sd tt kk g INTER moi_s34_bd tt kk) DIFF
                  UNIONS {rr r INTER IMAGE f1 (moi_s34_sd tt kk g) | r |
                          r IN moi_s34_simp kk (&3) /\ g SUBSET r})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                `dd:(real^N->bool)->real^3->bool`; `rr:(real^N->bool)->real^3->bool`;
                `g:real^N->bool`] MOI_S4OT_RIM_SETUP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `D = IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g)` THEN
  ABBREV_TAC `R = IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g INTER moi_s34_bd tt kk)` THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `dd:(real^N->bool)->real^3->bool`;
                 `s:real^N->bool`] MOI_S4OT_DD_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `g:real^N->bool` o el 4 o CONJUNCTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `p:real^3`) THEN
  ASM_REWRITE_TAC[SING_SUBSET] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `s:real^N->bool`]
    MOI_S4OT_FACE_TETS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r0:real^N->bool` MP_TAC o CONJUNCT2) THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [EXTENSION] THEN
  REWRITE_TAC[IN_ELIM_THM; IN_SING] THEN DISCH_THEN(LABEL_TAC "R0") THEN
  SUBGOAL_THEN `(r0:real^N->bool) IN moi_s34_simp kk (&3) /\ s SUBSET r0` STRIP_ASSUME_TAC THENL
   [USE_THEN "R0" (MP_TAC o SPEC `r0:real^N->bool`) THEN REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(g:real^N->bool) SUBSET r0` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`(g:real^N->bool) SUBSET s`; `(s:real^N->bool) SUBSET r0`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `dd:(real^N->bool)->real^3->bool`;
                 `rr:(real^N->bool)->real^3->bool`; `r0:real^N->bool`] MOI_S4OT_RR_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `g:real^N->bool` o el 3 o CONJUNCTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `E0 = UNIONS {(dd:(real^N->bool)->real^3->bool) s' INTER D | s' |
                           s' IN moi_s34_simp kk (&2) /\ (g:real^N->bool) SUBSET s' /\
                           s' SUBSET r0}` THEN
  SUBGOAL_THEN `(p:real^3) IN E0 /\ p IN R` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [EXPAND_TAC "E0" THEN REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM] THEN
      EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[IN_SING];
      SUBGOAL_THEN `(dd:(real^N->bool)->real^3->bool) s INTER D SUBSET R` MP_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
          can (find_term ((=) `dd:(real^N->bool)->real^3->bool`)) (concl th) &&
          can (find_term ((=) `R:real^3->bool`)) (concl th))) THEN
        ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[SING_SUBSET]]];
    ALL_TAC] THEN
  (* the other rim arcs miss p *)
  ABBREV_TAC `O0 = UNIONS {(rr:(real^N->bool)->real^3->bool) r INTER D | r |
                           r IN moi_s34_simp kk (&3) /\ (g:real^N->bool) SUBSET r /\
                           ~(r = r0)}` THEN
  SUBGOAL_THEN `closed(O0:real^3->bool) /\ ~((p:real^3) IN O0)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "O0" THEN CONJ_TAC THENL
     [MATCH_MP_TAC CLOSED_UNIONS THEN CONJ_TAC THENL
       [ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN MATCH_MP_TAC FINITE_IMAGE THEN
        MATCH_MP_TAC FINITE_SUBSET THEN
        EXISTS_TAC `{r | r IN moi_s34_simp kk (&3) /\ (g:real^N->bool) SUBSET r}` THEN
        ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[];
        REWRITE_TAC[FORALL_IN_GSPEC] THEN X_GEN_TAC `r:real^N->bool` THEN STRIP_TAC THEN
        MATCH_MP_TAC CLOSED_INTER THEN CONJ_TAC THEN MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
        ASM_REWRITE_TAC[] THEN
        MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                       `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                       `dd:(real^N->bool)->real^3->bool`; `rr:(real^N->bool)->real^3->bool`;
                       `r:real^N->bool`] MOI_S4OT_RR_FACTS) THEN
        ASM_REWRITE_TAC[] THEN SIMP_TAC[]];
      REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM; NOT_EXISTS_THM] THEN
      X_GEN_TAC `r:real^N->bool` THEN STRIP_TAC THEN
      SUBGOAL_THEN `(s:real^N->bool) SUBSET r` ASSUME_TAC THENL
       [MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                       `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                       `dd:(real^N->bool)->real^3->bool`; `rr:(real^N->bool)->real^3->bool`;
                       `r:real^N->bool`] MOI_S4OT_RR_FACTS) THEN
        ASM_REWRITE_TAC[] THEN
        DISCH_THEN(MP_TAC o SPEC `s:real^N->bool` o el 5 o CONJUNCTS) THEN
        ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `(p:real^3) IN (rr:(real^N->bool)->real^3->bool) r INTER D` THEN
        UNDISCH_TAC `(dd:(real^N->bool)->real^3->bool) s INTER D = {p}` THEN
        SET_TAC[];
        REMOVE_THEN "R0" (MP_TAC o SPEC `r:real^N->bool`) THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  REWRITE_TAC[CLOSURE_APPROACHABLE] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`R:real^3->bool`; `(rr:(real^N->bool)->real^3->bool) r0 INTER D`;
                 `E0:real^3->bool`; `p:real^3`] MOI_S4OT_ARC_END_NOT_OPEN) THEN
  ASM_SIMP_TAC[] THEN
  EXISTS_TAC `R INTER (ball(p:real^3,e) DIFF O0)` THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_IN_OPEN_INTER THEN MATCH_MP_TAC OPEN_DIFF THEN
    ASM_REWRITE_TAC[OPEN_BALL];
    ASM_REWRITE_TAC[IN_INTER; IN_DIFF; CENTRE_IN_BALL];
    GEN_REWRITE_TAC I [SUBSET] THEN X_GEN_TAC `y:real^3` THEN
    REWRITE_TAC[IN_INTER; IN_DIFF; IN_BALL] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_neg(concl th) &&
      can (find_term ((=) `e:real`)) (concl th))) THEN
    REWRITE_TAC[NOT_EXISTS_THM] THEN DISCH_THEN(MP_TAC o SPEC `y:real^3`) THEN
    ASM_REWRITE_TAC[IN_DIFF] THEN ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real^N->bool` STRIP_ASSUME_TAC) THEN
    ASM_CASES_TAC `r:real^N->bool = r0` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN
      UNDISCH_TAC `(y:real^3) IN (rr:(real^N->bool)->real^3->bool) r0 INTER D` THEN
      REWRITE_TAC[IN_INTER];
      UNDISCH_TAC `~((y:real^3) IN O0)` THEN EXPAND_TAC "O0" THEN
      REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM; NOT_EXISTS_THM] THEN
      DISCH_THEN(MP_TAC o SPEC `r:real^N->bool`) THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(y:real^3) IN (rr:(real^N->bool)->real^3->bool) r INTER D` THEN
      REWRITE_TAC[IN_INTER] THEN SIMP_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* The outer arc of a boundary edge g is a PL arc whose ends are            *)
(* the points of the two boundary faces at g (MOI_S4O_CIRCLE_ARC in R_g).   *)
(* ------------------------------------------------------------------------- *)

(* A boundary edge lies in exactly two boundary faces. *)

let MOI_S4OT_BEDGE_FACES = prove
 (`!(tt:(real^N->bool)->bool) kk g.
     moi_s34_tube tt kk /\ g IN moi_s34_simp kk (&1) /\ g SUBSET complex_boundary kk
     ==> ?s0 s1. ~(s0 = s1) /\
                 {s | s IN moi_s34_simp kk (&2) /\ g SUBSET s /\
                      s SUBSET complex_boundary kk} = {s0,s1}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `1`; `g:real^N->bool`]
    MOI_S4OT_SIMP_VERTEX) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `v:real^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(g:real^N->bool) IN kk /\ aff_dim g = &1` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(g:real^N->bool) IN moi_s34_simp kk (&1)` THEN
    REWRITE_TAC[moi_s34_simp; IN_ELIM_THM];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_S4O_CARD2 THEN CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{r | r IN moi_s34_simp kk (&2) /\ (g:real^N->bool) SUBSET r}` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MOI_S4OT_STAR_FINITE THEN EXISTS_TAC `tt:(real^N->bool)->bool` THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[MOI_S4H_SIMP_NE];
      SET_TAC[]];
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`;
                   `g:real^N->bool`] MOI_S4O_BEDGE_TWO) THEN
    ASM_REWRITE_TAC[moi_s34_simp; IN_ELIM_THM; GSYM CONJ_ASSOC]]);;

let MOI_S4OT_EDGE_CLAUSE = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car dd rr g.
     moi_s34_tube tt kk /\ moi_s34_frame tt kk h ep f1 car /\
     moi_s34_fdisk tt kk f1 car dd /\ moi_s34_resid tt kk f1 car dd rr /\
     g IN moi_s34_simp kk (&1) /\ g SUBSET complex_boundary kk
     ==> pl_cell_with_boundary 1 (moi_s34_oarc tt kk f1 rr g)
           (UNIONS {dd s INTER IMAGE f1 (moi_s34_sd tt kk g) | s |
                    s IN moi_s34_simp kk (&2) /\ g SUBSET s /\
                    s SUBSET complex_boundary kk})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                `dd:(real^N->bool)->real^3->bool`; `rr:(real^N->bool)->real^3->bool`;
                `g:real^N->bool`] MOI_S4OT_RIM_SETUP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `g:real^N->bool`]
    MOI_S4OT_BEDGE_FACES) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s0:real^N->bool` (X_CHOOSE_THEN `s1:real^N->bool`
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "BF")))) THEN
  SUBGOAL_THEN `(s0:real^N->bool) IN moi_s34_simp kk (&2) /\ g SUBSET s0 /\
                s0 SUBSET complex_boundary kk /\
                (s1:real^N->bool) IN moi_s34_simp kk (&2) /\ g SUBSET s1 /\
                s1 SUBSET complex_boundary kk` STRIP_ASSUME_TAC THENL
   [USE_THEN "BF" (MP_TAC o REWRITE_RULE[EXTENSION; IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY]) THEN
    DISCH_THEN(fun th -> MP_TAC(SPEC `s0:real^N->bool` th) THEN
                         MP_TAC(SPEC `s1:real^N->bool` th)) THEN
    REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `D = IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g)` THEN
  ABBREV_TAC `R = IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g INTER moi_s34_bd tt kk)` THEN
  ABBREV_TAC `A = UNIONS {(rr:(real^N->bool)->real^3->bool) r INTER D | r |
                          r IN moi_s34_simp kk (&3) /\ (g:real^N->bool) SUBSET r}` THEN
  (* the face points of the two boundary faces *)
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `dd:(real^N->bool)->real^3->bool`;
                 `s0:real^N->bool`] MOI_S4OT_DD_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> let cs = CONJUNCTS th in
    MP_TAC(SPEC `g:real^N->bool` (el 4 cs)) THEN MP_TAC(SPEC `s1:real^N->bool` (el 6 cs))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN DISCH_THEN(X_CHOOSE_TAC `p0:real^3`) THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `dd:(real^N->bool)->real^3->bool`;
                 `s1:real^N->bool`] MOI_S4OT_DD_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `g:real^N->bool` o el 4 o CONJUNCTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `p1:real^3`) THEN
  SUBGOAL_THEN `~(p0:real^3 = p1)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    MAP_EVERY UNDISCH_TAC
     [`(dd:(real^N->bool)->real^3->bool) s0 INTER dd s1 = {}`;
      `(dd:(real^N->bool)->real^3->bool) s0 INTER D = {p0}`;
      `(dd:(real^N->bool)->real^3->bool) s1 INTER D = {p1}`; `p0:real^3 = p1`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `UNIONS {(dd:(real^N->bool)->real^3->bool) s INTER D | s |
            s IN moi_s34_simp kk (&2) /\ (g:real^N->bool) SUBSET s /\
            s SUBSET complex_boundary kk} = {p0,p1}`
  ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN USE_THEN "BF" (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[IMAGE_CLAUSES; UNIONS_2] THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  (* the outer arc is the closure of the rim minus the rim arcs *)
  SUBGOAL_THEN `moi_s34_oarc tt kk (f1:real^N->real^3) rr g = closure(R DIFF A)` SUBST1_TAC THENL
   [REWRITE_TAC[moi_s34_oarc] THEN ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN
    EXPAND_TAC "A" THEN
    SUBGOAL_THEN `(R:real^3->bool) SUBSET D` MP_TAC THENL
     [MP_TAC(MATCH_MP MOI_S4G_CELL_FACTS
        (ASSUME `pl_cell_with_boundary 2 (D:real^3->bool) R`)) THEN SIMP_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `!r. r IN moi_s34_simp kk (&3)
                     ==> (rr:(real^N->bool)->real^3->bool) r INTER D SUBSET R` THEN
    REWRITE_TAC[EXTENSION; IN_DIFF; UNIONS_GSPEC; IN_ELIM_THM; SUBSET; IN_INTER] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  (* the facts on the union A of the rim arcs *)
  SUBGOAL_THEN `(A:real^3->bool) SUBSET R /\ closed A` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "A" THEN CONJ_TAC THENL
     [GEN_REWRITE_TAC I [SUBSET] THEN REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM] THEN
      X_GEN_TAC `y:real^3` THEN DISCH_THEN(X_CHOOSE_THEN `r:real^N->bool` STRIP_ASSUME_TAC) THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `r:real^N->bool` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `rr:(real^N->bool)->real^3->bool`)) (concl th) &&
        can (find_term ((=) `R:real^3->bool`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(y:real^3) IN (rr:(real^N->bool)->real^3->bool) r INTER D` THEN
      SET_TAC[];
      MATCH_MP_TAC CLOSED_UNIONS THEN CONJ_TAC THENL
       [ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN MATCH_MP_TAC FINITE_IMAGE THEN
        ASM_REWRITE_TAC[];
        REWRITE_TAC[FORALL_IN_GSPEC] THEN X_GEN_TAC `r:real^N->bool` THEN STRIP_TAC THEN
        MATCH_MP_TAC CLOSED_INTER THEN CONJ_TAC THEN MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
        ASM_REWRITE_TAC[] THEN
        MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                       `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                       `dd:(real^N->bool)->real^3->bool`; `rr:(real^N->bool)->real^3->bool`;
                       `r:real^N->bool`] MOI_S4OT_RR_FACTS) THEN
        ASM_REWRITE_TAC[] THEN SIMP_TAC[]]];
    ALL_TAC] THEN
  (* the face points lie on the rim arcs and are limits of the rest *)
  SUBGOAL_THEN `(p0:real^3) IN A /\ p1 IN A /\ p0 IN closure(R DIFF A) /\ p1 IN closure(R DIFF A)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `!s. s IN moi_s34_simp kk (&2) /\ (g:real^N->bool) SUBSET s /\
                      s SUBSET complex_boundary kk
                      ==> (dd:(real^N->bool)->real^3->bool) s INTER D SUBSET A /\
                          dd s INTER D SUBSET closure(R DIFF A)`
    MP_TAC THENL
     [X_GEN_TAC `s:real^N->bool` THEN STRIP_TAC THEN CONJ_TAC THENL
       [MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `s:real^N->bool`]
          MOI_S4OT_FACE_TETS) THEN
        ASM_REWRITE_TAC[] THEN
        DISCH_THEN(X_CHOOSE_THEN `r0:real^N->bool` MP_TAC o CONJUNCT2) THEN
        GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [EXTENSION] THEN
        REWRITE_TAC[IN_ELIM_THM; IN_SING] THEN
        DISCH_THEN(MP_TAC o SPEC `r0:real^N->bool`) THEN REWRITE_TAC[] THEN STRIP_TAC THEN
        MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                       `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                       `dd:(real^N->bool)->real^3->bool`; `rr:(real^N->bool)->real^3->bool`;
                       `r0:real^N->bool`] MOI_S4OT_RR_FACTS) THEN
        ASM_REWRITE_TAC[] THEN
        DISCH_THEN(MP_TAC o SPEC `s:real^N->bool` o el 6 o CONJUNCTS) THEN
        ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
        EXPAND_TAC "A" THEN GEN_REWRITE_TAC I [SUBSET] THEN
        REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
        EXISTS_TAC `r0:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
        CONJ_TAC THENL
         [MAP_EVERY UNDISCH_TAC [`(g:real^N->bool) SUBSET s`; `(s:real^N->bool) SUBSET r0`] THEN
          SET_TAC[];
          UNDISCH_TAC `(y:real^3) IN (dd:(real^N->bool)->real^3->bool) s INTER D` THEN
          UNDISCH_TAC `(dd:(real^N->bool)->real^3->bool) s SUBSET
                       (rr:(real^N->bool)->real^3->bool) r0` THEN SET_TAC[]];
        MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                      `ep:real^N->real`; `f1:real^N->real^3`;
                      `car:(real^N->bool)->real^3->bool`; `dd:(real^N->bool)->real^3->bool`;
                      `rr:(real^N->bool)->real^3->bool`; `g:real^N->bool`; `s:real^N->bool`]
          MOI_S4OT_EDGE_END) THEN
        ASM_REWRITE_TAC[]];
      DISCH_THEN(fun th -> MP_TAC(SPEC `s0:real^N->bool` th) THEN
                           MP_TAC(SPEC `s1:real^N->bool` th)) THEN
      ASM_REWRITE_TAC[SING_SUBSET] THEN SIMP_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_S4O_CIRCLE_ARC THEN
  MAP_EVERY EXISTS_TAC [`R:real^3->bool`; `A:real^3->bool`] THEN
  ASM_REWRITE_TAC[CLOSED_CLOSURE] THEN REPEAT CONJ_TAC THENL
   [(* A UNION B = R *)
    MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC[UNION_SUBSET] THEN MATCH_MP_TAC CLOSURE_MINIMAL THEN
      ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN SET_TAC[];
      MP_TAC(ISPEC `R DIFF (A:real^3->bool)` CLOSURE_SUBSET) THEN SET_TAC[]];
    (* A INTER B = {p0,p1} *)
    MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [ALL_TAC; ASM_REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET; IN_INTER]] THEN
    GEN_REWRITE_TAC I [SUBSET] THEN X_GEN_TAC `x:real^3` THEN REWRITE_TAC[IN_INTER] THEN
    STRIP_TAC THEN MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                  `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                  `dd:(real^N->bool)->real^3->bool`; `rr:(real^N->bool)->real^3->bool`;
                  `g:real^N->bool`; `x:real^3`] MOI_S4OT_EDGE_LOC) THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[OPEN_IN_OPEN] THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real^3->bool` (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `o1:real^3->bool` STRIP_ASSUME_TAC) STRIP_ASSUME_TAC)) THEN
    MP_TAC(ISPECL [`o1:real^3->bool`; `R DIFF (A:real^3->bool)`] OPEN_INTER_CLOSURE_EQ_EMPTY) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(TAUT `p /\ ~q ==> ~(q <=> p)`) THEN CONJ_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`(u:real^3->bool) = R INTER o1`; `(u:real^3->bool) SUBSET A`] THEN
      SET_TAC[];
      UNDISCH_TAC `(x:real^3) IN closure(R DIFF A)` THEN
      UNDISCH_TAC `(x:real^3) IN u` THEN UNDISCH_TAC `(u:real^3->bool) = R INTER o1` THEN
      SET_TAC[]];
    (* A is not inside {p0,p1} *)
    SUBGOAL_THEN `?r0. r0 IN moi_s34_simp kk (&3) /\ (s0:real^N->bool) SUBSET r0`
    STRIP_ASSUME_TAC THENL
     [MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `s0:real^N->bool`]
        MOI_S4OT_FACE_TETS) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `r0:real^N->bool` MP_TAC o CONJUNCT2) THEN
      GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [EXTENSION] THEN
      REWRITE_TAC[IN_ELIM_THM; IN_SING] THEN
      DISCH_THEN(MP_TAC o SPEC `r0:real^N->bool`) THEN REWRITE_TAC[] THEN
      DISCH_TAC THEN EXISTS_TAC `r0:real^N->bool` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(g:real^N->bool) SUBSET r0` ASSUME_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`(g:real^N->bool) SUBSET s0`; `(s0:real^N->bool) SUBSET r0`] THEN
      SET_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                   `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                   `dd:(real^N->bool)->real^3->bool`; `rr:(real^N->bool)->real^3->bool`;
                   `r0:real^N->bool`] MOI_S4OT_RR_FACTS) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th -> let cs = CONJUNCTS th in
      MP_TAC(SPEC `g:real^N->bool` (el 3 cs)) THEN LABEL_TAC "rdd0" (el 5 cs) THEN
      LABEL_TAC "ddr0" (el 6 cs)) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o MATCH_MP MOI_S4OT_CELL1_FACTS) THEN
    DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
    REWRITE_TAC[SUBSET; IN_INSERT; NOT_IN_EMPTY] THEN
    DISCH_THEN(MP_TAC o SPEC `z:real^3`) THEN
    ANTS_TAC THENL
     [EXPAND_TAC "A" THEN REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM] THEN
      EXISTS_TAC `r0:real^N->bool` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    STRIP_TAC THENL
     [UNDISCH_TAC `~((z:real^3) IN UNIONS {(dd:(real^N->bool)->real^3->bool) s INTER D | s |
                     s IN moi_s34_simp kk (&2) /\ (g:real^N->bool) SUBSET s /\ s SUBSET r0})` THEN
      REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM] THEN EXISTS_TAC `s0:real^N->bool` THEN
      ASM_REWRITE_TAC[IN_SING];
      ASM_CASES_TAC `(s1:real^N->bool) SUBSET r0` THENL
       [UNDISCH_TAC `~((z:real^3) IN UNIONS {(dd:(real^N->bool)->real^3->bool) s INTER D | s |
                       s IN moi_s34_simp kk (&2) /\ (g:real^N->bool) SUBSET s /\ s SUBSET r0})` THEN
        REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM] THEN EXISTS_TAC `s1:real^N->bool` THEN
        ASM_REWRITE_TAC[IN_SING];
        USE_THEN "rdd0" (MP_TAC o SPEC `s1:real^N->bool`) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        UNDISCH_TAC `(z:real^3) IN (rr:(real^N->bool)->real^3->bool) r0 INTER D` THEN
        UNDISCH_TAC `(dd:(real^N->bool)->real^3->bool) s1 INTER D = {p1}` THEN
        UNDISCH_TAC `z:real^3 = p1` THEN SET_TAC[]]];
    (* B is not inside {p0,p1} *)
    DISCH_TAC THEN
    SUBGOAL_THEN `R DIFF (A:real^3->bool) = {}` ASSUME_TAC THENL
     [MP_TAC(ISPEC `R DIFF (A:real^3->bool)` CLOSURE_SUBSET) THEN
      MAP_EVERY UNDISCH_TAC [`closure(R DIFF A) SUBSET {p0:real^3,p1}`;
                             `(p0:real^3) IN A`; `(p1:real^3) IN A`] THEN
      SET_TAC[];
      UNDISCH_TAC `(p0:real^3) IN closure(R DIFF A)` THEN ASM_REWRITE_TAC[CLOSURE_EMPTY] THEN
      REWRITE_TAC[NOT_IN_EMPTY]]]);;

(* ------------------------------------------------------------------------- *)
(* Images under an injective map; the boundary faces at a boundary          *)
(* vertex are connected through boundary edges at the vertex (the link of v *)
(* in the boundary surface is a PL circle, MOI_FSA_LK_EDGES_CONN).          *)
(* ------------------------------------------------------------------------- *)

let MOI_S4OT_IMG_INTER = prove
 (`!(f:real^N->real^M) n a b.
     (!x y. x IN n /\ y IN n /\ f x = f y ==> x = y) /\ a SUBSET n /\ b SUBSET n
     ==> IMAGE f a INTER IMAGE f b = IMAGE f (a INTER b)`,
  REPEAT STRIP_TAC THEN ASM SET_TAC[]);;

let MOI_S4OT_BFACE_CONN = prove
 (`!(tt:(real^N->bool)->bool) kk v Y.
     moi_s34_tube tt kk /\ {v} IN kk /\ v IN complex_boundary kk /\
     Y SUBSET {s | s IN moi_s34_simp kk (&2) /\ v IN s /\ s SUBSET complex_boundary kk} /\
     ~(Y = {}) /\
     (!s s' g. s IN Y /\ s' IN moi_s34_simp kk (&2) /\ v IN s' /\
               s' SUBSET complex_boundary kk /\ g IN moi_s34_simp kk (&1) /\ v IN g /\
               g SUBSET s /\ g SUBSET s' ==> s' IN Y)
     ==> Y = {s | s IN moi_s34_simp kk (&2) /\ v IN s /\ s SUBSET complex_boundary kk}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4OT_TUBE_LF) THEN
  MP_TAC(ISPEC `kk:(real^N->bool)->bool` MOI_FM3_BC_SUBCOMPLEX) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
  ABBREV_TAC `B = boundary_complex (kk:(real^N->bool)->bool)` THEN
  SUBGOAL_THEN `{v:real^N} IN B` ASSUME_TAC THENL
   [EXPAND_TAC "B" THEN REWRITE_TAC[boundary_complex; IN_ELIM_THM] THEN
    ASM_REWRITE_TAC[SING_SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s:real^N->bool. s IN B <=> s IN kk /\ s SUBSET complex_boundary kk`
  (LABEL_TAC "BIN") THENL
   [EXPAND_TAC "B" THEN REWRITE_TAC[boundary_complex; IN_ELIM_THM]; ALL_TAC] THEN
  MP_TAC(ISPEC `kk:(real^N->bool)->bool` BOUNDARY_COMPLEX_SURFACE) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `v:real^N` o CONJUNCT2 o REWRITE_RULE[combinatorial_manifold] o
    el 3 o CONJUNCTS) THEN
  ASM_REWRITE_TAC[] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_SUB_CONV) THEN
  REWRITE_TAC[pl_sphere; pl_homeomorphism] THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
    (X_CHOOSE_THEN `h:real^N->real^N` STRIP_ASSUME_TAC))) THEN
  ABBREV_TAC `L = simplicial_link (B:(real^N->bool)->bool) v` THEN
  SUBGOAL_THEN `simplicial_complex (L:(real^N->bool)->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "L" THEN MATCH_MP_TAC MOI_FM3_LINK_SC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* faces at v of B correspond to link simplices *)
  SUBGOAL_THEN
   `!e:real^N->bool. e IN L
      ==> convex hull (v INSERT e) IN B /\ v IN convex hull (v INSERT e) /\
          e SUBSET convex hull (v INSERT e) /\
          aff_dim (convex hull (v INSERT e)) = aff_dim e + &1 /\ ~(v IN e)`
  (LABEL_TAC "JOIN") THENL
   [X_GEN_TAC `e:real^N->bool` THEN DISCH_TAC THEN MATCH_MP_TAC MOI_FM3_LINK_JOIN THEN
    EXPAND_TAC "L" THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s:real^N->bool. s IN moi_s34_simp kk (&2) /\ v IN s /\ s SUBSET complex_boundary kk
      ==> ?e. e IN L /\ aff_dim e = &1 /\ s = convex hull (v INSERT e)`
  (LABEL_TAC "OPP") THENL
   [X_GEN_TAC `s:real^N->bool` THEN REWRITE_TAC[moi_s34_simp; IN_ELIM_THM] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`B:(real^N->bool)->bool`; `v:real^N`; `s:real^N->bool`] MOI_FM3_LINK_OPP) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN USE_THEN "BIN" (fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `e:real^N->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `e:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "JOIN" (fun th -> MP_TAC(MP (SPEC `e:real^N->bool` th)
      (ASSUME `(e:real^N->bool) IN L`))) THEN
    STRIP_TAC THEN
    MAP_EVERY UNDISCH_TAC [`aff_dim (convex hull ((v:real^N) INSERT e)) = aff_dim e + &1`;
                           `aff_dim (s:real^N->bool) = &2`;
                           `s = convex hull ((v:real^N) INSERT e)`] THEN
    DISCH_THEN SUBST1_TAC THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `k:real^N->bool`; `f:real^N->real^N`;
                 `h:real^N->real^N`;
                 `{e:real^N->bool | e IN L /\ aff_dim e = &1 /\ convex hull (v INSERT e) IN Y}`]
    MOI_FSA_LK_EDGES_CONN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [SET_TAC[];
      UNDISCH_TAC `~(Y:(real^N->bool)->bool = {})` THEN
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
      DISCH_THEN(X_CHOOSE_TAC `s:real^N->bool`) THEN
      USE_THEN "OPP" (MP_TAC o SPEC `s:real^N->bool`) THEN
      ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `e:real^N->bool` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `e:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
        lhs(concl th) = `s:real^N->bool`)) THEN ASM_REWRITE_TAC[];
      MAP_EVERY X_GEN_TAC [`e:real^N->bool`; `e':real^N->bool`] THEN
      REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      (* a common vertex u of the two link edges *)
      SUBGOAL_THEN `?u:real^N. {u} IN L /\ u IN e /\ u IN e'` STRIP_ASSUME_TAC THENL
       [MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `e INTER e':real^N->bool`] MOI_FM3_LF_VERTEX) THEN
        ANTS_TAC THENL
         [ASM_SIMP_TAC[MOI_FMB_SC_LF] THEN
          UNDISCH_TAC `simplicial_complex (L:(real^N->bool)->bool)` THEN
          REWRITE_TAC[simplicial_complex] THEN ASM_MESON_TAC[];
          REWRITE_TAC[IN_INTER] THEN MESON_TAC[]];
        ALL_TAC] THEN
      USE_THEN "JOIN" (fun th -> MP_TAC(MP (SPEC `e:real^N->bool` th)
                                   (ASSUME `(e:real^N->bool) IN L`)) THEN
                                 MP_TAC(MP (SPEC `e':real^N->bool` th)
                                   (ASSUME `(e':real^N->bool) IN L`)) THEN
                                 MP_TAC(MP (SPEC `{u:real^N}` th)
                                   (ASSUME `{u:real^N} IN L`))) THEN
      REWRITE_TAC[AFF_DIM_SING] THEN REPEAT STRIP_TAC THEN
      SUBGOAL_THEN `convex hull ((v:real^N) INSERT {u}) SUBSET convex hull (v INSERT e) /\
                    convex hull ((v:real^N) INSERT {u}) SUBSET convex hull (v INSERT e')`
      STRIP_ASSUME_TAC THENL
       [CONJ_TAC THENL
         [MP_TAC(ISPECL [`B:(real^N->bool)->bool`; `v:real^N`; `{u:real^N}`; `e:real^N->bool`]
            MOI_FM3_LINK_JOIN_SUBSET);
          MP_TAC(ISPECL [`B:(real^N->bool)->bool`; `v:real^N`; `{u:real^N}`; `e':real^N->bool`]
            MOI_FM3_LINK_JOIN_SUBSET)] THEN
        ANTS_TAC THEN TRY(ASM_REWRITE_TAC[] THEN NO_TAC) THEN
        DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[SING_SUBSET];
        ALL_TAC] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `Y:(real^N->bool)->bool`)) (concl th))) THEN
      EXISTS_TAC `convex hull ((v:real^N) INSERT e)` THEN
      EXISTS_TAC `convex hull ((v:real^N) INSERT {u})` THEN
      USE_THEN "BIN" (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
      ASM_REWRITE_TAC[moi_s34_simp; IN_ELIM_THM] THEN CONV_TAC INT_REDUCE_CONV];
    ALL_TAC] THEN
  DISCH_TAC THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN ASM_REWRITE_TAC[] THEN
  GEN_REWRITE_TAC I [SUBSET] THEN REWRITE_TAC[IN_ELIM_THM] THEN
  X_GEN_TAC `s:real^N->bool` THEN STRIP_TAC THEN
  USE_THEN "OPP" (MP_TAC o SPEC `s:real^N->bool`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real^N->bool` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e:real^N->bool` o REWRITE_RULE[EXTENSION; IN_ELIM_THM] o
    check (fun th -> is_eq(concl th) &&
      can (find_term ((=) `Y:(real^N->bool)->bool`)) (concl th))) THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* A finite family of PL arcs, any two meeting at most in one               *)
(* common end, each end on exactly one other arc, has line charts; with     *)
(* connected union it is a PL circle (MOI_S4L_LINE_CHART_CIRCLES).          *)
(* ------------------------------------------------------------------------- *)

let MOI_S4OT_ARCS_CHARTS = prove
 (`!(idx:A->bool) (cc:A->real^N->bool) ee.
     FINITE idx /\
     (!i. i IN idx ==> pl_cell_with_boundary 1 (cc i) (ee i)) /\
     (!i j. i IN idx /\ j IN idx /\ ~(i = j)
            ==> cc i INTER cc j SUBSET ee i INTER ee j /\
                (!x y. x IN cc i INTER cc j /\ y IN cc i INTER cc j ==> x = y)) /\
     (!i x. i IN idx /\ x IN ee i ==> ?j. j IN idx /\ ~(j = i) /\ x IN cc j) /\
     (!i j k x. i IN idx /\ j IN idx /\ k IN idx /\ ~(j = i) /\ ~(k = i) /\
                x IN ee i /\ x IN cc j /\ x IN cc k ==> j = k)
     ==> moi_s4l_line_charts (UNIONS (IMAGE cc idx))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> let cs = CONJUNCTS th in
    ASSUME_TAC (el 0 cs) THEN LABEL_TAC "CL1" (el 1 cs) THEN LABEL_TAC "MEET" (el 2 cs) THEN
    LABEL_TAC "NEXT" (el 3 cs) THEN LABEL_TAC "UNIQ" (el 4 cs)) THEN
  SUBGOAL_THEN `!i. i IN idx ==> compact((cc:A->real^N->bool) i) /\ ee i SUBSET cc i /\
                               (!x. x IN ee i ==> ?y. ~(y = x) /\ ee i = {x,y})`
  (LABEL_TAC "CF") THENL
   [X_GEN_TAC `i:A` THEN DISCH_TAC THEN
    USE_THEN "CL1" (fun th -> MP_TAC(MATCH_MP MOI_S4OT_CELL1_FACTS
      (MP (SPEC `i:A` th) (ASSUME `(i:A) IN idx`)))) THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!jj. jj SUBSET (idx:A->bool) ==> closed(UNIONS (IMAGE (cc:A->real^N->bool) jj))`
  (LABEL_TAC "CL") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC CLOSED_UNIONS THEN
    CONJ_TAC THENL [ASM_MESON_TAC[FINITE_IMAGE; FINITE_SUBSET]; ALL_TAC] THEN
    REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `k:A` THEN DISCH_TAC THEN
    MATCH_MP_TAC COMPACT_IMP_CLOSED THEN USE_THEN "CF" (MP_TAC o SPEC `k:A`) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[moi_s4l_line_charts] THEN X_GEN_TAC `x:real^N` THEN
  REWRITE_TAC[IN_UNIONS; EXISTS_IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `i:A` STRIP_ASSUME_TAC) THEN
  USE_THEN "CF" (fun th -> MP_TAC(MP (SPEC `i:A` th) (ASSUME `(i:A) IN idx`))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "PR"))) THEN
  ASM_CASES_TAC `(x:real^N) IN ee(i:A)` THENL
   [ALL_TAC;
    MP_TAC(ISPECL [`(cc:A->real^N->bool) i`; `(ee:A->real^N->bool) i`] MOI_S4L_CELL1_PL_ARC) THEN
    ANTS_TAC THENL [USE_THEN "CL1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `hh:real^1->real^N` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC MOI_S4OT_LINE_CHART_AT THEN
    MAP_EVERY EXISTS_TAC [`(cc:A->real^N->bool) i`; `pathstart(hh:real^1->real^N)`;
                          `pathfinish(hh:real^1->real^N)`;
                          `(:real^N) DIFF UNIONS (IMAGE (cc:A->real^N->bool) (idx DELETE i))`] THEN
    SUBGOAL_THEN `~((x:real^N) = pathstart(hh:real^1->real^N)) /\
                  ~((x:real^N) = pathfinish(hh:real^1->real^N))` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `~((x:real^N) IN ee(i:A))` THEN
      FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> is_eq(concl th) &&
        lhs(concl th) = `(ee:A->real^N->bool) i`)) THEN
      REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY; DE_MORGAN_THM];
      ALL_TAC] THEN
    SUBGOAL_THEN `!j. j IN idx /\ ~(j = i) ==> ~((x:real^N) IN cc(j:A))` (LABEL_TAC "OUT") THENL
     [X_GEN_TAC `j:A` THEN STRIP_TAC THEN DISCH_TAC THEN
      USE_THEN "MEET" (MP_TAC o SPECL [`i:A`; `j:A`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o CONJUNCT1) THEN
      MAP_EVERY UNDISCH_TAC [`~((x:real^N) IN ee(i:A))`; `(x:real^N) IN cc(i:A)`;
                             `(x:real^N) IN cc(j:A)`] THEN
      SET_TAC[];
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
        lhs(concl th) = `(ee:A->real^N->bool) i`)) THEN
      USE_THEN "CL1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      REWRITE_TAC[GSYM closed] THEN USE_THEN "CL" MATCH_MP_TAC THEN SET_TAC[];
      REWRITE_TAC[IN_DIFF; IN_UNIV; IN_UNIONS; EXISTS_IN_IMAGE; IN_DELETE] THEN
      REWRITE_TAC[NOT_EXISTS_THM] THEN X_GEN_TAC `j:A` THEN
      ASM_CASES_TAC `j:A = i` THEN ASM_REWRITE_TAC[] THEN
      ASM_CASES_TAC `(j:A) IN idx` THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "OUT" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `z:real^N` THEN
      REWRITE_TAC[IN_INTER; IN_DIFF; IN_UNIV; IN_UNIONS; EXISTS_IN_IMAGE; IN_DELETE] THEN
      EQ_TAC THENL
       [ALL_TAC;
        STRIP_TAC THEN ASM_REWRITE_TAC[] THEN EXISTS_TAC `i:A` THEN ASM_REWRITE_TAC[]] THEN
      DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `j:A` STRIP_ASSUME_TAC) ASSUME_TAC) THEN
      ASM_CASES_TAC `j:A = i` THENL
       [UNDISCH_TAC `(z:real^N) IN cc(j:A)` THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
        ASM_REWRITE_TAC[];
        UNDISCH_TAC `~(?x. (x IN idx /\ ~(x = i:A)) /\ (z:real^N) IN cc x)` THEN
        REWRITE_TAC[NOT_EXISTS_THM] THEN DISCH_THEN(MP_TAC o SPEC `j:A`) THEN
        ASM_REWRITE_TAC[]]]] THEN
  (* an end of the arc cc i: join with the other arc through x *)
  USE_THEN "NEXT" (MP_TAC o SPECL [`i:A`; `x:real^N`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `j:A` STRIP_ASSUME_TAC) THEN
  USE_THEN "MEET" (MP_TAC o SPECL [`i:A`; `j:A`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `(cc:A->real^N->bool) i INTER cc j = {x}` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN ASM_REWRITE_TAC[SING_SUBSET; IN_INTER] THEN
    REWRITE_TAC[SUBSET; IN_SING] THEN X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `(cc:A->real^N->bool) i INTER cc j`)) (concl th))) THEN
    ASM_REWRITE_TAC[IN_INTER];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^N) IN ee(j:A)` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`(cc:A->real^N->bool) i INTER cc j SUBSET ee i INTER ee j`;
                           `(x:real^N) IN cc(i:A)`; `(x:real^N) IN cc(j:A)`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  USE_THEN "PR" (MP_TAC o SPEC `x:real^N`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC) THEN
  USE_THEN "CF" (fun th -> MP_TAC(SPEC `x:real^N`
    (CONJUNCT2(CONJUNCT2(MP (SPEC `j:A` th) (ASSUME `(j:A) IN idx`)))))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `y':real^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `pl_cell_with_boundary 1 ((cc:A->real^N->bool) i) {y,x} /\
                pl_cell_with_boundary 1 ((cc:A->real^N->bool) j) {x,y'}` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [SUBGOAL_THEN `{y:real^N,x} = ee(i:A)` SUBST1_TAC THENL
       [UNDISCH_TAC `(ee:A->real^N->bool) i = {x,y}` THEN SET_TAC[];
        USE_THEN "CL1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      SUBGOAL_THEN `{x:real^N,y'} = ee(j:A)` SUBST1_TAC THENL
       [UNDISCH_TAC `(ee:A->real^N->bool) j = {x,y'}` THEN SET_TAC[];
        USE_THEN "CL1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(cc:A->real^N->bool) i`; `(cc:A->real^N->bool) j`; `y:real^N`; `x:real^N`;
                 `y':real^N`] MOI_S4OT_ARC_JOIN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN `!k. k IN idx /\ ~(k = i) /\ ~(k = j) ==> ~((x:real^N) IN cc(k:A))`
  (LABEL_TAC "OUT2") THENL
   [X_GEN_TAC `k:A` THEN STRIP_TAC THEN DISCH_TAC THEN
    USE_THEN "UNIQ" (MP_TAC o SPECL [`i:A`; `j:A`; `k:A`; `x:real^N`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_S4OT_LINE_CHART_AT THEN
  MAP_EVERY EXISTS_TAC [`(cc:A->real^N->bool) i UNION cc j`; `y:real^N`; `y':real^N`;
                        `(:real^N) DIFF UNIONS (IMAGE (cc:A->real^N->bool) (idx DIFF {i,j}))`] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[IN_UNION];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    REWRITE_TAC[GSYM closed] THEN USE_THEN "CL" MATCH_MP_TAC THEN SET_TAC[];
    REWRITE_TAC[IN_DIFF; IN_UNIV; IN_UNIONS; EXISTS_IN_IMAGE; IN_INSERT; NOT_IN_EMPTY] THEN
    REWRITE_TAC[NOT_EXISTS_THM; DE_MORGAN_THM] THEN X_GEN_TAC `k:A` THEN
    ASM_CASES_TAC `k:A = i` THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `k:A = j` THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `(k:A) IN idx` THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "OUT2" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `z:real^N` THEN
    REWRITE_TAC[IN_INTER; IN_DIFF; IN_UNIV; IN_UNIONS; EXISTS_IN_IMAGE; IN_INSERT;
                NOT_IN_EMPTY; IN_UNION] THEN
    EQ_TAC THENL
     [ALL_TAC;
      STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
       [EXISTS_TAC `i:A`; EXISTS_TAC `j:A`] THEN ASM_REWRITE_TAC[]] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `k:A` STRIP_ASSUME_TAC) ASSUME_TAC) THEN
    ASM_CASES_TAC `k:A = i` THENL
     [UNDISCH_TAC `(z:real^N) IN cc(k:A)` THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      ASM_REWRITE_TAC[];
      ASM_CASES_TAC `k:A = j` THENL
       [UNDISCH_TAC `(z:real^N) IN cc(k:A)` THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
        ASM_REWRITE_TAC[];
        UNDISCH_TAC `~(?x. (x IN idx /\ ~(x = i:A \/ x = j)) /\ (z:real^N) IN cc x)` THEN
        REWRITE_TAC[NOT_EXISTS_THM] THEN DISCH_THEN(MP_TAC o SPEC `k:A`) THEN
        ASM_REWRITE_TAC[]]]]);;

let MOI_S4OT_ARCS_CIRCLE = prove
 (`!(idx:A->bool) (cc:A->real^N->bool) ee.
     2 <= dimindex(:N) /\ FINITE idx /\ ~(idx = {}) /\
     (!i. i IN idx ==> pl_cell_with_boundary 1 (cc i) (ee i)) /\
     (!i j. i IN idx /\ j IN idx /\ ~(i = j)
            ==> cc i INTER cc j SUBSET ee i INTER ee j /\
                (!x y. x IN cc i INTER cc j /\ y IN cc i INTER cc j ==> x = y)) /\
     (!i x. i IN idx /\ x IN ee i ==> ?j. j IN idx /\ ~(j = i) /\ x IN cc j) /\
     (!i j k x. i IN idx /\ j IN idx /\ k IN idx /\ ~(j = i) /\ ~(k = i) /\
                x IN ee i /\ x IN cc j /\ x IN cc k ==> j = k) /\
     connected (UNIONS (IMAGE cc idx))
     ==> pl_sphere 1 (UNIONS (IMAGE cc idx))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `UNIONS (IMAGE (cc:A->real^N->bool) idx)` MOI_S4L_LINE_CHART_CIRCLES) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC MOI_S4L_PL_POLYHEDRON_UNIONS THEN
      ASM_SIMP_TAC[FINITE_IMAGE; FORALL_IN_IMAGE] THEN
      ASM_MESON_TAC[MOI_S4O_CELL_POLY];
      MATCH_MP_TAC MOI_S4OT_ARCS_CHARTS THEN EXISTS_TAC `ee:A->real^N->bool` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN
  SUBGOAL_THEN `components(UNIONS (IMAGE (cc:A->real^N->bool) idx)) =
                {UNIONS (IMAGE cc idx)}` SUBST1_TAC THENL
   [REWRITE_TAC[COMPONENTS_EQ_SING] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[EMPTY_UNIONS; FORALL_IN_IMAGE] THEN
    UNDISCH_TAC `~(idx:A->bool = {})` THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    DISCH_THEN(X_CHOOSE_TAC `i:A`) THEN DISCH_THEN(MP_TAC o SPEC `i:A`) THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP MOI_S4G_CELL_FACTS o C MATCH_MP (ASSUME `(i:A) IN idx`) o
      check (fun th -> is_forall(concl th) && is_imp(snd(strip_forall(concl th))) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "pl_cell_with_boundary"))
            (concl th))) THEN
    SIMP_TAC[];
    REWRITE_TAC[IN_SING]]);;

(* ------------------------------------------------------------------------- *)
(* At a boundary vertex v the boundary face arcs dd s INTER C_v             *)
(* and the outer arcs of the boundary edges at v form a PL circle J_v.     *)
(* ------------------------------------------------------------------------- *)

(* Point facts at v: face points, disjointness of face disks and of         *)
(* splitting disks, the face arcs and the outer arcs.                        *)

let MOI_S4OT_JV_FACTS = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car dd rr v.
     moi_s34_tube tt kk /\ moi_s34_frame tt kk h ep f1 car /\
     moi_s34_fdisk tt kk f1 car dd /\ moi_s34_resid tt kk f1 car dd rr /\ {v} IN kk
     ==> (!s g. s IN moi_s34_simp kk (&2) /\ g IN moi_s34_simp kk (&1) /\ g SUBSET s
                ==> ?p. dd s INTER IMAGE f1 (moi_s34_sd tt kk g) = {p}) /\
         (!s g. s IN moi_s34_simp kk (&2) /\ g IN moi_s34_simp kk (&1) /\ ~(g SUBSET s)
                ==> dd s INTER IMAGE f1 (moi_s34_sd tt kk g) = {}) /\
         (!s s'. s IN moi_s34_simp kk (&2) /\ s' IN moi_s34_simp kk (&2) /\ ~(s = s')
                 ==> dd s INTER dd s' = {}) /\
         (!g g'. g IN moi_s34_simp kk (&1) /\ g' IN moi_s34_simp kk (&1) /\ ~(g = g')
                 ==> IMAGE f1 (moi_s34_sd tt kk g) INTER IMAGE f1 (moi_s34_sd tt kk g') = {}) /\
         (!g. g IN moi_s34_simp kk (&1) /\ v IN g
              ==> IMAGE f1 (moi_s34_sd tt kk g) SUBSET IMAGE f1 (moi_s34_vb tt kk v)) /\
         (!s. s IN moi_s34_simp kk (&2) /\ v IN s
              ==> pl_cell_with_boundary 1 (dd s INTER IMAGE f1 (moi_s34_vb tt kk v))
                    (UNIONS {dd s INTER IMAGE f1 (moi_s34_sd tt kk g) | g |
                             g IN moi_s34_simp kk (&1) /\ v IN g /\ g SUBSET s})) /\
         (!g. g IN moi_s34_simp kk (&1) /\ g SUBSET complex_boundary kk
              ==> pl_cell_with_boundary 1 (moi_s34_oarc tt kk f1 rr g)
                    (UNIONS {dd s INTER IMAGE f1 (moi_s34_sd tt kk g) | s |
                             s IN moi_s34_simp kk (&2) /\ g SUBSET s /\
                             s SUBSET complex_boundary kk}) /\
                  moi_s34_oarc tt kk f1 rr g SUBSET IMAGE f1 (moi_s34_sd tt kk g))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `f1:real^N->real^3`;
                   `car:(real^N->bool)->real^3->bool`; `dd:(real^N->bool)->real^3->bool`;
                   `s:real^N->bool`] MOI_S4OT_DD_FACTS) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `g:real^N->bool` o el 4 o CONJUNCTS) THEN
    ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `f1:real^N->real^3`;
                   `car:(real^N->bool)->real^3->bool`; `dd:(real^N->bool)->real^3->bool`;
                   `s:real^N->bool`] MOI_S4OT_DD_FACTS) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `g:real^N->bool` o el 5 o CONJUNCTS) THEN
    ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `f1:real^N->real^3`;
                   `car:(real^N->bool)->real^3->bool`; `dd:(real^N->bool)->real^3->bool`;
                   `s:real^N->bool`] MOI_S4OT_DD_FACTS) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `s':real^N->bool` o el 6 o CONJUNCTS) THEN
    ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                   `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`]
      MOI_S4G_FRAME_FACTS) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2) THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`f1:real^N->real^3`; `moi_s34_nb tt (kk:(real^N->bool)->bool)`;
                   `moi_s34_sd tt kk (g:real^N->bool)`; `moi_s34_sd tt kk (g':real^N->bool)`]
      MOI_S4OT_IMG_INTER) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[MOI_S4G_SD_NB]; DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[IMAGE_EQ_EMPTY; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
    X_GEN_TAC `y:real^N` THEN STRIP_TAC THEN
    UNDISCH_TAC `~(g:real^N->bool = g')` THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_S4B_SD_UNIQ THEN
    MAP_EVERY EXISTS_TAC [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `y:real^N`] THEN
    ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC IMAGE_SUBSET THEN
    MATCH_MP_TAC MOI_S4G_SD_SUB_VB THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `f1:real^N->real^3`;
                   `car:(real^N->bool)->real^3->bool`; `dd:(real^N->bool)->real^3->bool`;
                   `s:real^N->bool`] MOI_S4OT_DD_FACTS) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `v:real^N` o el 3 o CONJUNCTS) THEN
    ASM_REWRITE_TAC[];
    REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC MOI_S4OT_EDGE_CLAUSE THEN
      MAP_EVERY EXISTS_TAC [`h:real^N->real^3`; `ep:real^N->real`;
                            `car:(real^N->bool)->real^3->bool`] THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC MOI_S4G_OARC_IN THEN
      MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                    `ep:real^N->real`; `f1:real^N->real^3`;
                    `car:(real^N->bool)->real^3->bool`; `dd:(real^N->bool)->real^3->bool`;
                    `rr:(real^N->bool)->real^3->bool`; `g:real^N->bool`] MOI_S4OT_RIM_SETUP) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN MATCH_MP_TAC IMAGE_SUBSET THEN SET_TAC[]]]);;

let MOI_S4OT_CELL1_CONNECTED = prove
 (`!a ba:real^N->bool. pl_cell_with_boundary 1 a ba ==> connected a`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^1->real^N` STRIP_ASSUME_TAC o
    MATCH_MP MOI_S4L_CELL1_PL_ARC) THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `path_image(h:real^1->real^N)`)) THEN
  ASM_SIMP_TAC[CONNECTED_PATH_IMAGE; ARC_IMP_PATH]);;

(* J_v is connected (BFACE_CONN). *)

let MOI_S4OT_JV_CONNECTED = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car dd rr v.
     moi_s34_tube tt kk /\ moi_s34_frame tt kk h ep f1 car /\
     moi_s34_fdisk tt kk f1 car dd /\ moi_s34_resid tt kk f1 car dd rr /\
     {v} IN kk /\ v IN complex_boundary kk
     ==> connected
          (UNIONS {dd s INTER IMAGE f1 (moi_s34_vb tt kk v) | s |
                   s IN moi_s34_simp kk (&2) /\ v IN s /\ s SUBSET complex_boundary kk} UNION
           UNIONS {moi_s34_oarc tt kk f1 rr g | g |
                   g IN moi_s34_simp kk (&1) /\ v IN g /\ g SUBSET complex_boundary kk})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                `dd:(real^N->bool)->real^3->bool`; `rr:(real^N->bool)->real^3->bool`;
                `v:real^N`] MOI_S4OT_JV_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> let cs = CONJUNCTS th in
    LABEL_TAC "PT" (el 0 cs) THEN LABEL_TAC "SDC" (el 4 cs) THEN
    LABEL_TAC "FA" (el 5 cs) THEN LABEL_TAC "OA" (el 6 cs)) THEN
  ABBREV_TAC `C = IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v)` THEN
  ABBREV_TAC `J = UNIONS {(dd:(real^N->bool)->real^3->bool) s INTER C | s |
                          s IN moi_s34_simp kk (&2) /\ v IN s /\ s SUBSET complex_boundary kk}
                  UNION
                  UNIONS {moi_s34_oarc tt kk (f1:real^N->real^3) rr g | g |
                          g IN moi_s34_simp kk (&1) /\ (v:real^N) IN g /\
                          g SUBSET complex_boundary kk}` THEN
  REWRITE_TAC[CONNECTED_CLOPEN] THEN X_GEN_TAC `t:real^3->bool` THEN STRIP_TAC THEN
  (* a connected piece of J meeting t lies in t *)
  SUBGOAL_THEN `!P:real^3->bool. connected P /\ P SUBSET J /\ ~(P INTER t = {}) ==> P SUBSET t`
  (LABEL_TAC "PIECE") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC CONNECTED_SUBSET_CLOPEN THEN
    EXISTS_TAC `J:real^3->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(!s. s IN moi_s34_simp kk (&2) /\ (v:real^N) IN s /\ s SUBSET complex_boundary kk
         ==> connected((dd:(real^N->bool)->real^3->bool) s INTER C) /\ dd s INTER C SUBSET J) /\
    (!g. g IN moi_s34_simp kk (&1) /\ (v:real^N) IN g /\ g SUBSET complex_boundary kk
         ==> connected(moi_s34_oarc tt kk (f1:real^N->real^3) rr g) /\
             moi_s34_oarc tt kk f1 rr g SUBSET J)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN X_GEN_TAC `q:real^N->bool` THEN STRIP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC MOI_S4OT_CELL1_CONNECTED THEN
      EXISTS_TAC `UNIONS {(dd:(real^N->bool)->real^3->bool) q INTER
                          IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g) | g |
                          g IN moi_s34_simp kk (&1) /\ (v:real^N) IN g /\ g SUBSET q}` THEN
      USE_THEN "FA" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      EXPAND_TAC "J" THEN MATCH_MP_TAC(SET_RULE `!a b c:real^3->bool. a SUBSET b ==> a SUBSET b UNION c`) THEN
      GEN_REWRITE_TAC I [SUBSET] THEN REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM] THEN
      X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN EXISTS_TAC `q:real^N->bool` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC MOI_S4OT_CELL1_CONNECTED THEN
      EXISTS_TAC `UNIONS {(dd:(real^N->bool)->real^3->bool) s INTER
                          IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk q) | s |
                          s IN moi_s34_simp kk (&2) /\ q SUBSET s /\
                          s SUBSET complex_boundary kk}` THEN
      USE_THEN "OA" (fun th -> MP_TAC(SPEC `q:real^N->bool` th)) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
      EXPAND_TAC "J" THEN MATCH_MP_TAC(SET_RULE `!a b c:real^3->bool. a SUBSET c ==> a SUBSET b UNION c`) THEN
      GEN_REWRITE_TAC I [SUBSET] THEN REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM] THEN
      X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN EXISTS_TAC `q:real^N->bool` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* the face point p of s at g lies on both the face arc of s and the outer arc of g *)
  SUBGOAL_THEN
   `!s g. s IN moi_s34_simp kk (&2) /\ (v:real^N) IN s /\ s SUBSET complex_boundary kk /\
          g IN moi_s34_simp kk (&1) /\ v IN g /\ g SUBSET s
          ==> ?p. p IN (dd:(real^N->bool)->real^3->bool) s INTER C /\
                  p IN moi_s34_oarc tt kk (f1:real^N->real^3) rr g`
  (LABEL_TAC "MEETP") THENL
   [REPEAT STRIP_TAC THEN
    USE_THEN "PT" (MP_TAC o SPECL [`s:real^N->bool`; `g:real^N->bool`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(X_CHOOSE_TAC `p:real^3`)] THEN
    EXISTS_TAC `p:real^3` THEN CONJ_TAC THENL
     [USE_THEN "SDC" (MP_TAC o SPEC `g:real^N->bool`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      EXPAND_TAC "C" THEN
      UNDISCH_TAC `(dd:(real^N->bool)->real^3->bool) s INTER
                   IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g) = {p}` THEN
      SET_TAC[];
      USE_THEN "OA" (MP_TAC o SPEC `g:real^N->bool`) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN
        MAP_EVERY UNDISCH_TAC [`(g:real^N->bool) SUBSET s`;
                               `(s:real^N->bool) SUBSET complex_boundary kk`] THEN SET_TAC[];
        ALL_TAC] THEN
      DISCH_THEN(MP_TAC o MATCH_MP MOI_S4G_CELL_FACTS o CONJUNCT1) THEN
      DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2) THEN
      MATCH_MP_TAC(SET_RULE `!a b x:real^3. x IN a ==> a SUBSET b ==> x IN b`) THEN
      REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM] THEN EXISTS_TAC `s:real^N->bool` THEN
      ASM_REWRITE_TAC[IN_SING] THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `Y = {s | s IN moi_s34_simp kk (&2) /\ (v:real^N) IN s /\
                       s SUBSET complex_boundary kk /\
                       (dd:(real^N->bool)->real^3->bool) s INTER C SUBSET t}` THEN
  (* every outer arc at v meets a boundary face arc *)
  SUBGOAL_THEN
   `!g. g IN moi_s34_simp kk (&1) /\ (v:real^N) IN g /\ g SUBSET complex_boundary kk
        ==> ?s. s IN moi_s34_simp kk (&2) /\ v IN s /\ s SUBSET complex_boundary kk /\
                g SUBSET s`
  (LABEL_TAC "GS") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `g:real^N->bool`]
      MOI_S4OT_BEDGE_FACES) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `s0:real^N->bool` (X_CHOOSE_THEN `s1:real^N->bool` MP_TAC)) THEN
    DISCH_THEN(MP_TAC o SPEC `s0:real^N->bool` o
      REWRITE_RULE[EXTENSION; IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY] o CONJUNCT2) THEN
    REWRITE_TAC[] THEN STRIP_TAC THEN EXISTS_TAC `s0:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC [`(v:real^N) IN g`; `(g:real^N->bool) SUBSET s0`] THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `Y:(real^N->bool)->bool = {}` THENL
   [DISJ1_TAC THEN
    SUBGOAL_THEN `!s. s IN moi_s34_simp kk (&2) /\ (v:real^N) IN s /\
                      s SUBSET complex_boundary kk
                      ==> (dd:(real^N->bool)->real^3->bool) s INTER C INTER t = {}`
    (LABEL_TAC "FE") THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
      UNDISCH_TAC `Y:(real^N->bool)->bool = {}` THEN EXPAND_TAC "Y" THEN
      REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY; NOT_FORALL_THM] THEN
      EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "PIECE" MATCH_MP_TAC THEN ASM_SIMP_TAC[] THEN
      UNDISCH_TAC `~((dd:(real^N->bool)->real^3->bool) s INTER C INTER t = {})` THEN SET_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC(SET_RULE `!t J:real^3->bool. t SUBSET J /\ J INTER t = {} ==> t = {}`) THEN
    EXISTS_TAC `J:real^3->bool` THEN
    CONJ_TAC THENL [ASM_MESON_TAC[CLOSED_IN_IMP_SUBSET]; ALL_TAC] THEN
    EXPAND_TAC "J" THEN
    REWRITE_TAC[SET_RULE `!a b t:real^3->bool.
                  (a UNION b) INTER t = {} <=> a INTER t = {} /\ b INTER t = {}`;
                INTER_UNIONS] THEN
    REWRITE_TAC[EMPTY_UNIONS; FORALL_IN_GSPEC] THEN CONJ_TAC THENL
     [X_GEN_TAC `s:real^N->bool` THEN STRIP_TAC THEN
      USE_THEN "FE" (MP_TAC o SPEC `s:real^N->bool`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; SET_TAC[]];
      X_GEN_TAC `g:real^N->bool` THEN STRIP_TAC THEN
      MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
      USE_THEN "GS" (MP_TAC o SPEC `g:real^N->bool`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
      USE_THEN "MEETP" (MP_TAC o SPECL [`s:real^N->bool`; `g:real^N->bool`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `p:real^3` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `moi_s34_oarc tt kk (f1:real^N->real^3) rr g SUBSET t` ASSUME_TAC THENL
       [USE_THEN "PIECE" MATCH_MP_TAC THEN ASM_SIMP_TAC[] THEN
        UNDISCH_TAC `~(moi_s34_oarc tt kk (f1:real^N->real^3) rr g INTER t = {})` THEN SET_TAC[];
        ALL_TAC] THEN
      USE_THEN "FE" (MP_TAC o SPEC `s:real^N->bool`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `(p:real^3) IN (dd:(real^N->bool)->real^3->bool) s INTER C` THEN
      UNDISCH_TAC `(p:real^3) IN moi_s34_oarc tt kk (f1:real^N->real^3) rr g` THEN
      UNDISCH_TAC `moi_s34_oarc tt kk (f1:real^N->real^3) rr g SUBSET t` THEN SET_TAC[]];
    DISJ2_TAC] THEN
  (* Y is nonempty, hence all boundary faces at v *)
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`;
                 `Y:(real^N->bool)->bool`] MOI_S4OT_BFACE_CONN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [EXPAND_TAC "Y" THEN SET_TAC[];
      MAP_EVERY X_GEN_TAC [`s:real^N->bool`; `s':real^N->bool`; `g:real^N->bool`] THEN
      EXPAND_TAC "Y" THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `(g:real^N->bool) SUBSET complex_boundary kk` ASSUME_TAC THENL
       [MAP_EVERY UNDISCH_TAC [`(g:real^N->bool) SUBSET s`;
                               `(s:real^N->bool) SUBSET complex_boundary kk`] THEN SET_TAC[];
        ALL_TAC] THEN
      USE_THEN "MEETP" (MP_TAC o SPECL [`s:real^N->bool`; `g:real^N->bool`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `p:real^3` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `moi_s34_oarc tt kk (f1:real^N->real^3) rr g SUBSET t` ASSUME_TAC THENL
       [USE_THEN "PIECE" MATCH_MP_TAC THEN ASM_SIMP_TAC[] THEN
        MAP_EVERY UNDISCH_TAC
         [`(p:real^3) IN (dd:(real^N->bool)->real^3->bool) s INTER C`;
          `(p:real^3) IN moi_s34_oarc tt kk (f1:real^N->real^3) rr g`;
          `(dd:(real^N->bool)->real^3->bool) s INTER C SUBSET t`] THEN
        SET_TAC[];
        ALL_TAC] THEN
      USE_THEN "MEETP" (MP_TAC o SPECL [`s':real^N->bool`; `g:real^N->bool`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `p':real^3` STRIP_ASSUME_TAC) THEN
      USE_THEN "PIECE" MATCH_MP_TAC THEN ASM_SIMP_TAC[] THEN
      MAP_EVERY UNDISCH_TAC
       [`(p':real^3) IN (dd:(real^N->bool)->real^3->bool) s' INTER C`;
        `(p':real^3) IN moi_s34_oarc tt kk (f1:real^N->real^3) rr g`;
        `moi_s34_oarc tt kk (f1:real^N->real^3) rr g SUBSET t`] THEN
      SET_TAC[]];
    DISCH_TAC] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [ASM_MESON_TAC[CLOSED_IN_IMP_SUBSET]; ALL_TAC] THEN
  EXPAND_TAC "J" THEN REWRITE_TAC[UNION_SUBSET; UNIONS_SUBSET; FORALL_IN_GSPEC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `s:real^N->bool` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(s:real^N->bool) IN Y` MP_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> is_eq(concl th) &&
        lhs(concl th) = `Y:(real^N->bool)->bool`)) THEN
      ASM_REWRITE_TAC[IN_ELIM_THM];
      EXPAND_TAC "Y" THEN REWRITE_TAC[IN_ELIM_THM] THEN SIMP_TAC[]];
    X_GEN_TAC `g:real^N->bool` THEN STRIP_TAC THEN
    USE_THEN "GS" (MP_TAC o SPEC `g:real^N->bool`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
    USE_THEN "MEETP" (MP_TAC o SPECL [`s:real^N->bool`; `g:real^N->bool`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `p:real^3` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(s:real^N->bool) IN Y` MP_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> is_eq(concl th) &&
        lhs(concl th) = `Y:(real^N->bool)->bool`)) THEN
      ASM_REWRITE_TAC[IN_ELIM_THM];
      ALL_TAC] THEN
    EXPAND_TAC "Y" THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
    USE_THEN "PIECE" MATCH_MP_TAC THEN ASM_SIMP_TAC[] THEN
    MAP_EVERY UNDISCH_TAC
     [`(p:real^3) IN (dd:(real^N->bool)->real^3->bool) s INTER C`;
      `(p:real^3) IN moi_s34_oarc tt kk (f1:real^N->real^3) rr g`;
      `(dd:(real^N->bool)->real^3->bool) s INTER C SUBSET t`] THEN
    SET_TAC[]]);;

(* A boundary vertex lies in a boundary face. *)

let MOI_S4OT_BVERTEX_FACE = prove
 (`!(kk:(real^N->bool)->bool) v.
     v IN complex_boundary kk
     ==> ?s. s IN moi_s34_simp kk (&2) /\ v IN s /\ s SUBSET complex_boundary kk`,
  REPEAT GEN_TAC THEN REWRITE_TAC[complex_boundary; IN_UNIONS; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[moi_s34_simp; IN_ELIM_THM] THEN
  GEN_REWRITE_TAC I [SUBSET] THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
  REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN EXISTS_TAC `s:real^N->bool` THEN
  ASM_REWRITE_TAC[]);;

(* J_v is a PL circle. *)

let MOI_S4OT_JV_CIRCLE = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car dd rr v.
     moi_s34_tube tt kk /\ moi_s34_frame tt kk h ep f1 car /\
     moi_s34_fdisk tt kk f1 car dd /\ moi_s34_resid tt kk f1 car dd rr /\
     {v} IN kk /\ v IN complex_boundary kk
     ==> pl_sphere 1
          (UNIONS {dd s INTER IMAGE f1 (moi_s34_vb tt kk v) | s |
                   s IN moi_s34_simp kk (&2) /\ v IN s /\ s SUBSET complex_boundary kk} UNION
           UNIONS {moi_s34_oarc tt kk f1 rr g | g |
                   g IN moi_s34_simp kk (&1) /\ v IN g /\ g SUBSET complex_boundary kk})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                `dd:(real^N->bool)->real^3->bool`; `rr:(real^N->bool)->real^3->bool`;
                `v:real^N`] MOI_S4OT_JV_CONNECTED) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                `dd:(real^N->bool)->real^3->bool`; `rr:(real^N->bool)->real^3->bool`;
                `v:real^N`] MOI_S4OT_JV_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> let cs = CONJUNCTS th in
    LABEL_TAC "PT" (el 0 cs) THEN LABEL_TAC "NPT" (el 1 cs) THEN LABEL_TAC "DDJ" (el 2 cs) THEN
    LABEL_TAC "SDJ" (el 3 cs) THEN LABEL_TAC "SDC" (el 4 cs) THEN LABEL_TAC "FA" (el 5 cs) THEN
    LABEL_TAC "OA" (el 6 cs)) THEN
  ABBREV_TAC `C = IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v)` THEN
  ABBREV_TAC `FF = {s | s IN moi_s34_simp kk (&2) /\ (v:real^N) IN s /\
                        s SUBSET complex_boundary kk}` THEN
  ABBREV_TAC `GG = {g | g IN moi_s34_simp kk (&1) /\ (v:real^N) IN g /\
                        g SUBSET complex_boundary kk}` THEN
  SUBGOAL_THEN `(!q:real^N->bool. q IN FF ==> ~(q IN GG)) /\
                (!q:real^N->bool. q IN GG ==> ~(q IN FF))` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["FF"; "GG"] THEN REWRITE_TAC[IN_ELIM_THM; moi_s34_simp] THEN
    CONJ_TAC THEN REPEAT STRIP_TAC THEN UNDISCH_TAC `aff_dim(q:real^N->bool) = &2` THEN
    ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `cc = \q:real^N->bool. if q IN FF then (dd:(real^N->bool)->real^3->bool) q INTER C
                                    else moi_s34_oarc tt kk (f1:real^N->real^3) rr q` THEN
  ABBREV_TAC `ee = \q:real^N->bool.
     if q IN FF then UNIONS {(dd:(real^N->bool)->real^3->bool) q INTER
                             IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g) | g |
                             g IN moi_s34_simp kk (&1) /\ (v:real^N) IN g /\ g SUBSET q}
     else UNIONS {dd s INTER IMAGE f1 (moi_s34_sd tt kk q) | s |
                  s IN moi_s34_simp kk (&2) /\ q SUBSET s /\ s SUBSET complex_boundary kk}` THEN
  SUBGOAL_THEN
   `(!q. q IN FF
         ==> (cc:(real^N->bool)->real^3->bool) q = dd q INTER C /\
             (ee:(real^N->bool)->real^3->bool) q =
             UNIONS {dd q INTER IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g) | g |
                     g IN moi_s34_simp kk (&1) /\ (v:real^N) IN g /\ g SUBSET q}) /\
    (!q. q IN GG
         ==> cc q = moi_s34_oarc tt kk f1 rr q /\
             ee q = UNIONS {dd s INTER IMAGE f1 (moi_s34_sd tt kk q) | s |
                            s IN moi_s34_simp kk (&2) /\ q SUBSET s /\
                            s SUBSET complex_boundary kk})`
  (CONJUNCTS_THEN2 (LABEL_TAC "CF") (LABEL_TAC "CG")) THENL
   [CONJ_TAC THEN X_GEN_TAC `q:real^N->bool` THEN DISCH_TAC THEN
    MAP_EVERY EXPAND_TAC ["cc"; "ee"] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `UNIONS {(dd:(real^N->bool)->real^3->bool) s INTER C | s |
            s IN moi_s34_simp kk (&2) /\ (v:real^N) IN s /\ s SUBSET complex_boundary kk} UNION
    UNIONS {moi_s34_oarc tt kk (f1:real^N->real^3) rr g | g |
            g IN moi_s34_simp kk (&1) /\ v IN g /\ g SUBSET complex_boundary kk} =
    UNIONS (IMAGE (cc:(real^N->bool)->real^3->bool) (FF UNION GG))`
  ASSUME_TAC THENL
   [REWRITE_TAC[IMAGE_UNION; UNIONS_UNION] THEN BINOP_TAC THEN AP_TERM_TAC THEN
    MAP_EVERY EXPAND_TAC ["FF"; "GG"] THEN
    GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
    X_GEN_TAC `y:real^3->bool` THEN EQ_TAC THEN
    DISCH_THEN(X_CHOOSE_THEN `q:real^N->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `q:real^N->bool` THEN ASM_REWRITE_TAC[] THENL
     [USE_THEN "CF" (MP_TAC o SPEC `q:real^N->bool`);
      USE_THEN "CF" (MP_TAC o SPEC `q:real^N->bool`);
      USE_THEN "CG" (MP_TAC o SPEC `q:real^N->bool`);
      USE_THEN "CG" (MP_TAC o SPEC `q:real^N->bool`)] THEN
    MAP_EVERY EXPAND_TAC ["FF"; "GG"] THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN SIMP_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MOI_S4OT_ARCS_CIRCLE THEN EXISTS_TAC `ee:(real^N->bool)->real^3->bool` THEN
  SUBGOAL_THEN
   `!s g. s IN FF /\ g IN GG /\ g SUBSET s
          ==> ?p. (dd:(real^N->bool)->real^3->bool) s INTER
                  IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g) = {p} /\
                  p IN (cc:(real^N->bool)->real^3->bool) s /\ p IN cc g /\
                  p IN (ee:(real^N->bool)->real^3->bool) s /\ p IN ee g`
  (LABEL_TAC "PP") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `(s:real^N->bool) IN moi_s34_simp kk (&2) /\ (v:real^N) IN s /\
                  s SUBSET complex_boundary kk /\ (g:real^N->bool) IN moi_s34_simp kk (&1) /\
                  v IN g /\ g SUBSET complex_boundary kk` STRIP_ASSUME_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`(s:real^N->bool) IN FF`; `(g:real^N->bool) IN GG`] THEN
      MAP_EVERY EXPAND_TAC ["FF"; "GG"] THEN REWRITE_TAC[IN_ELIM_THM] THEN SIMP_TAC[];
      ALL_TAC] THEN
    USE_THEN "PT" (MP_TAC o SPECL [`s:real^N->bool`; `g:real^N->bool`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(X_CHOOSE_TAC `p:real^3`)] THEN
    EXISTS_TAC `p:real^3` THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "CF" (fun th -> MP_TAC(MP (SPEC `s:real^N->bool` th)
      (ASSUME `(s:real^N->bool) IN FF`))) THEN
    USE_THEN "CG" (fun th -> MP_TAC(MP (SPEC `g:real^N->bool` th)
      (ASSUME `(g:real^N->bool) IN GG`))) THEN
    DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC SUBST1_TAC) THEN
    DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC SUBST1_TAC) THEN
    SUBGOAL_THEN `(p:real^3) IN UNIONS {(dd:(real^N->bool)->real^3->bool) s' INTER
                     IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g) | s' |
                     s' IN moi_s34_simp kk (&2) /\ g SUBSET s' /\
                     s' SUBSET complex_boundary kk}` ASSUME_TAC THENL
     [REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM] THEN EXISTS_TAC `s:real^N->bool` THEN
      ASM_REWRITE_TAC[IN_SING];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [USE_THEN "SDC" (MP_TAC o SPEC `g:real^N->bool`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `(dd:(real^N->bool)->real^3->bool) s INTER
                   IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g) = {p}` THEN SET_TAC[];
      USE_THEN "OA" (MP_TAC o SPEC `g:real^N->bool`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2 o MATCH_MP MOI_S4G_CELL_FACTS o CONJUNCT1) THEN
      UNDISCH_TAC `(p:real^3) IN UNIONS {(dd:(real^N->bool)->real^3->bool) s' INTER
                     IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g) | s' |
                     s' IN moi_s34_simp kk (&2) /\ g SUBSET s' /\
                     s' SUBSET complex_boundary kk}` THEN
      SET_TAC[];
      REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM] THEN EXISTS_TAC `g:real^N->bool` THEN
      ASM_REWRITE_TAC[IN_SING]];
    ALL_TAC] THEN
  (* membership in FF and GG *)
  SUBGOAL_THEN
   `(!s:real^N->bool. s IN FF <=> s IN moi_s34_simp kk (&2) /\ (v:real^N) IN s /\
                                  s SUBSET complex_boundary kk) /\
    (!g:real^N->bool. g IN GG <=> g IN moi_s34_simp kk (&1) /\ (v:real^N) IN g /\
                                  g SUBSET complex_boundary kk)`
  (CONJUNCTS_THEN2 (LABEL_TAC "INF") (LABEL_TAC "ING")) THENL
   [MAP_EVERY EXPAND_TAC ["FF"; "GG"] THEN REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  (* cc of an index lies in its face disk or splitting disk *)
  SUBGOAL_THEN
   `(!s. s IN FF ==> (cc:(real^N->bool)->real^3->bool) s SUBSET dd s) /\
    (!g. g IN GG ==> cc g SUBSET IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g))`
  (CONJUNCTS_THEN2 (LABEL_TAC "CSF") (LABEL_TAC "CSG")) THENL
   [CONJ_TAC THEN X_GEN_TAC `q:real^N->bool` THEN DISCH_TAC THENL
     [USE_THEN "CF" (fun th -> MP_TAC(MP (SPEC `q:real^N->bool` th)
      (ASSUME `(q:real^N->bool) IN FF`))) THEN
      DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN SET_TAC[];
      USE_THEN "CG" (fun th -> MP_TAC(MP (SPEC `q:real^N->bool` th)
      (ASSUME `(q:real^N->bool) IN GG`))) THEN
      DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN
      USE_THEN "OA" (MP_TAC o SPEC `q:real^N->bool`) THEN
      ANTS_TAC THENL [USE_THEN "ING" (fun th -> MP_TAC(EQ_MP (SPEC `q:real^N->bool` th)
      (ASSUME `(q:real^N->bool) IN GG`))) THEN SIMP_TAC[];
                      SIMP_TAC[]]];
    ALL_TAC] THEN
  (* ends: the face points *)
  SUBGOAL_THEN
   `(!s x. s IN FF /\ x IN (ee:(real^N->bool)->real^3->bool) s
           ==> ?g. g IN GG /\ g SUBSET s /\
                   x IN (dd:(real^N->bool)->real^3->bool) s INTER
                        IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g)) /\
    (!g x. g IN GG /\ x IN ee g
           ==> ?s. s IN FF /\ g SUBSET s /\ x IN dd s INTER IMAGE f1 (moi_s34_sd tt kk g))`
  (CONJUNCTS_THEN2 (LABEL_TAC "EF") (LABEL_TAC "EG")) THENL
   [CONJ_TAC THEN MAP_EVERY X_GEN_TAC [`q:real^N->bool`; `x:real^3`] THEN STRIP_TAC THENL
     [UNDISCH_TAC `(x:real^3) IN (ee:(real^N->bool)->real^3->bool) q` THEN
      USE_THEN "CF" (fun th -> MP_TAC(MP (SPEC `q:real^N->bool` th)
      (ASSUME `(q:real^N->bool) IN FF`))) THEN
      DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM] THEN
      DISCH_THEN(X_CHOOSE_THEN `g:real^N->bool` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `g:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "ING" (fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "INF" (fun th -> MP_TAC(EQ_MP (SPEC `q:real^N->bool` th)
      (ASSUME `(q:real^N->bool) IN FF`))) THEN
      UNDISCH_TAC `(g:real^N->bool) SUBSET q` THEN SET_TAC[];
      UNDISCH_TAC `(x:real^3) IN (ee:(real^N->bool)->real^3->bool) q` THEN
      USE_THEN "CG" (fun th -> MP_TAC(MP (SPEC `q:real^N->bool` th)
      (ASSUME `(q:real^N->bool) IN GG`))) THEN
      DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM] THEN
      DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "INF" (fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "ING" (fun th -> MP_TAC(EQ_MP (SPEC `q:real^N->bool` th)
      (ASSUME `(q:real^N->bool) IN GG`))) THEN
      UNDISCH_TAC `(q:real^N->bool) SUBSET s` THEN SET_TAC[]];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[DIMINDEX_3] THEN ARITH_TAC;
    REWRITE_TAC[FINITE_UNION] THEN MAP_EVERY EXPAND_TAC ["FF"; "GG"] THEN CONJ_TAC THEN
    MATCH_MP_TAC FINITE_SUBSET THENL
     [EXISTS_TAC `{r | r IN moi_s34_simp kk (&2) /\ {v:real^N} SUBSET r}`;
      EXISTS_TAC `{r | r IN moi_s34_simp kk (&1) /\ {v:real^N} SUBSET r}`] THEN
    (CONJ_TAC THENL
      [MATCH_MP_TAC MOI_S4OT_STAR_FINITE THEN EXISTS_TAC `tt:(real^N->bool)->bool` THEN
       ASM_REWRITE_TAC[NOT_INSERT_EMPTY];
       REWRITE_TAC[SUBSET; IN_ELIM_THM; SING_SUBSET] THEN MESON_TAC[]]);
    MP_TAC(ISPECL [`kk:(real^N->bool)->bool`; `v:real^N`] MOI_S4OT_BVERTEX_FACE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `s:real^N->bool`) THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_UNION] THEN EXISTS_TAC `s:real^N->bool` THEN
    DISJ1_TAC THEN USE_THEN "INF" (fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[];
    (* cells *)
    X_GEN_TAC `q:real^N->bool` THEN REWRITE_TAC[IN_UNION] THEN STRIP_TAC THENL
     [USE_THEN "CF" (fun th -> MP_TAC(MP (SPEC `q:real^N->bool` th)
      (ASSUME `(q:real^N->bool) IN FF`))) THEN
      DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC SUBST1_TAC) THEN
      USE_THEN "FA" MATCH_MP_TAC THEN
      USE_THEN "INF" (fun th -> MP_TAC(EQ_MP (SPEC `q:real^N->bool` th)
      (ASSUME `(q:real^N->bool) IN FF`))) THEN SIMP_TAC[];
      USE_THEN "CG" (fun th -> MP_TAC(MP (SPEC `q:real^N->bool` th)
      (ASSUME `(q:real^N->bool) IN GG`))) THEN
      DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC SUBST1_TAC) THEN
      USE_THEN "OA" (MP_TAC o SPEC `q:real^N->bool`) THEN
      ANTS_TAC THENL [USE_THEN "ING" (fun th -> MP_TAC(EQ_MP (SPEC `q:real^N->bool` th)
      (ASSUME `(q:real^N->bool) IN GG`))) THEN SIMP_TAC[];
                      SIMP_TAC[]]];
    (* pairwise meeting *)
    SUBGOAL_THEN
     `!s g. s IN FF /\ g IN GG
            ==> (cc:(real^N->bool)->real^3->bool) s INTER cc g SUBSET
                (ee:(real^N->bool)->real^3->bool) s INTER ee g /\
                (!x y. x IN cc s INTER cc g /\ y IN cc s INTER cc g ==> x = y)`
    (LABEL_TAC "FEP") THENL
     [MAP_EVERY X_GEN_TAC [`s:real^N->bool`; `g:real^N->bool`] THEN STRIP_TAC THEN
      USE_THEN "CSF" (fun th -> MP_TAC(MP (SPEC `s:real^N->bool` th)
        (ASSUME `(s:real^N->bool) IN FF`))) THEN
      USE_THEN "CSG" (fun th -> MP_TAC(MP (SPEC `g:real^N->bool` th)
        (ASSUME `(g:real^N->bool) IN GG`))) THEN
      REPEAT DISCH_TAC THEN
      ASM_CASES_TAC `(g:real^N->bool) SUBSET s` THENL
       [USE_THEN "PP" (MP_TAC o SPECL [`s:real^N->bool`; `g:real^N->bool`]) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        DISCH_THEN(X_CHOOSE_THEN `p:real^3` STRIP_ASSUME_TAC) THEN
        SUBGOAL_THEN `(cc:(real^N->bool)->real^3->bool) s INTER cc g SUBSET {p}` ASSUME_TAC THENL
         [MAP_EVERY UNDISCH_TAC
           [`(cc:(real^N->bool)->real^3->bool) s SUBSET dd s`;
            `(cc:(real^N->bool)->real^3->bool) g SUBSET
             IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g)`;
            `(dd:(real^N->bool)->real^3->bool) s INTER
             IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g) = {p}`] THEN
          SET_TAC[];
          ALL_TAC] THEN
        CONJ_TAC THENL
         [MAP_EVERY UNDISCH_TAC
           [`(cc:(real^N->bool)->real^3->bool) s INTER cc g SUBSET {p}`;
            `(p:real^3) IN (ee:(real^N->bool)->real^3->bool) s`;
            `(p:real^3) IN (ee:(real^N->bool)->real^3->bool) g`] THEN
          SET_TAC[];
          UNDISCH_TAC `(cc:(real^N->bool)->real^3->bool) s INTER cc g SUBSET {p}` THEN
          SET_TAC[]];
        SUBGOAL_THEN `(cc:(real^N->bool)->real^3->bool) s INTER cc g = {}` ASSUME_TAC THENL
         [USE_THEN "NPT" (MP_TAC o SPECL [`s:real^N->bool`; `g:real^N->bool`]) THEN
          ANTS_TAC THENL
           [ASM_REWRITE_TAC[] THEN
            USE_THEN "INF" (fun th -> MP_TAC(EQ_MP (SPEC `s:real^N->bool` th)
              (ASSUME `(s:real^N->bool) IN FF`))) THEN
            USE_THEN "ING" (fun th -> MP_TAC(EQ_MP (SPEC `g:real^N->bool` th)
              (ASSUME `(g:real^N->bool) IN GG`))) THEN
            SIMP_TAC[];
            ALL_TAC] THEN
          MAP_EVERY UNDISCH_TAC
           [`(cc:(real^N->bool)->real^3->bool) s SUBSET dd s`;
            `(cc:(real^N->bool)->real^3->bool) g SUBSET
             IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g)`] THEN
          SET_TAC[];
          ASM_REWRITE_TAC[EMPTY_SUBSET; NOT_IN_EMPTY]]];
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`i:real^N->bool`; `j:real^N->bool`] THEN
    REWRITE_TAC[IN_UNION] THEN STRIP_TAC THENL
     [USE_THEN "CSF" (fun th -> MP_TAC(MP (SPEC `i:real^N->bool` th)
        (ASSUME `(i:real^N->bool) IN FF`)) THEN
        MP_TAC(MP (SPEC `j:real^N->bool` th) (ASSUME `(j:real^N->bool) IN FF`))) THEN
      USE_THEN "DDJ" (MP_TAC o SPECL [`i:real^N->bool`; `j:real^N->bool`]) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN
        USE_THEN "INF" (fun th -> MP_TAC(EQ_MP (SPEC `i:real^N->bool` th)
          (ASSUME `(i:real^N->bool) IN FF`))) THEN
        USE_THEN "INF" (fun th -> MP_TAC(EQ_MP (SPEC `j:real^N->bool` th)
          (ASSUME `(j:real^N->bool) IN FF`))) THEN
        SIMP_TAC[];
        SET_TAC[]];
      USE_THEN "FEP" (fun th -> MP_TAC(MP (SPECL [`i:real^N->bool`; `j:real^N->bool`] th)
        (CONJ (ASSUME `(i:real^N->bool) IN FF`) (ASSUME `(j:real^N->bool) IN GG`)))) THEN
      SIMP_TAC[];
      USE_THEN "FEP" (fun th -> MP_TAC(MP (SPECL [`j:real^N->bool`; `i:real^N->bool`] th)
        (CONJ (ASSUME `(j:real^N->bool) IN FF`) (ASSUME `(i:real^N->bool) IN GG`)))) THEN
      MESON_TAC[INTER_COMM];
      USE_THEN "CSG" (fun th -> MP_TAC(MP (SPEC `i:real^N->bool` th)
        (ASSUME `(i:real^N->bool) IN GG`)) THEN
        MP_TAC(MP (SPEC `j:real^N->bool` th) (ASSUME `(j:real^N->bool) IN GG`))) THEN
      USE_THEN "SDJ" (MP_TAC o SPECL [`i:real^N->bool`; `j:real^N->bool`]) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN
        USE_THEN "ING" (fun th -> MP_TAC(EQ_MP (SPEC `i:real^N->bool` th)
          (ASSUME `(i:real^N->bool) IN GG`))) THEN
        USE_THEN "ING" (fun th -> MP_TAC(EQ_MP (SPEC `j:real^N->bool` th)
          (ASSUME `(j:real^N->bool) IN GG`))) THEN
        SIMP_TAC[];
        SET_TAC[]]];
    (* every end lies on another arc *)
    MAP_EVERY X_GEN_TAC [`i:real^N->bool`; `x:real^3`] THEN
    REWRITE_TAC[IN_UNION] THEN STRIP_TAC THENL
     [USE_THEN "EF" (MP_TAC o SPECL [`i:real^N->bool`; `x:real^3`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `g:real^N->bool` STRIP_ASSUME_TAC) THEN
      USE_THEN "PP" (MP_TAC o SPECL [`i:real^N->bool`; `g:real^N->bool`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `p:real^3` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `g:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `(x:real^3) IN (dd:(real^N->bool)->real^3->bool) i INTER
                   IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g)` THEN
      ASM_REWRITE_TAC[IN_SING] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[];
      USE_THEN "EG" (MP_TAC o SPECL [`i:real^N->bool`; `x:real^3`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
      USE_THEN "PP" (MP_TAC o SPECL [`s:real^N->bool`; `i:real^N->bool`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `p:real^3` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `(x:real^3) IN (dd:(real^N->bool)->real^3->bool) s INTER
                   IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk i)` THEN
      ASM_REWRITE_TAC[IN_SING] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]];
    (* uniqueness of the other arc through an end *)
    SUBGOAL_THEN
     `!i j x. i IN FF /\ j IN FF UNION GG /\ ~(j = i) /\
              x IN (ee:(real^N->bool)->real^3->bool) i /\
              x IN (cc:(real^N->bool)->real^3->bool) j
              ==> j IN GG /\ x IN IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk j)`
    (LABEL_TAC "WF") THENL
     [MAP_EVERY X_GEN_TAC [`i:real^N->bool`; `j:real^N->bool`; `x:real^3`] THEN
      DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
      USE_THEN "EF" (MP_TAC o SPECL [`i:real^N->bool`; `x:real^3`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `g:real^N->bool` STRIP_ASSUME_TAC) THEN
      FIRST_X_ASSUM(DISJ_CASES_TAC o REWRITE_RULE[IN_UNION] o check (fun th ->
        concl th = `(j:real^N->bool) IN FF UNION GG`)) THENL
       [USE_THEN "CSF" (fun th -> MP_TAC(MP (SPEC `j:real^N->bool` th)
          (ASSUME `(j:real^N->bool) IN FF`))) THEN
        USE_THEN "DDJ" (MP_TAC o SPECL [`i:real^N->bool`; `j:real^N->bool`]) THEN
        ANTS_TAC THENL
         [ASM_REWRITE_TAC[] THEN
          USE_THEN "INF" (fun th -> MP_TAC(EQ_MP (SPEC `i:real^N->bool` th)
            (ASSUME `(i:real^N->bool) IN FF`))) THEN
          USE_THEN "INF" (fun th -> MP_TAC(EQ_MP (SPEC `j:real^N->bool` th)
            (ASSUME `(j:real^N->bool) IN FF`))) THEN
          SIMP_TAC[];
          ALL_TAC] THEN
        MAP_EVERY UNDISCH_TAC
         [`(x:real^3) IN (cc:(real^N->bool)->real^3->bool) j`;
          `(x:real^3) IN (dd:(real^N->bool)->real^3->bool) i INTER
           IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g)`] THEN
        SET_TAC[];
        ASM_REWRITE_TAC[] THEN
        USE_THEN "CSG" (fun th -> MP_TAC(MP (SPEC `j:real^N->bool` th)
          (ASSUME `(j:real^N->bool) IN GG`))) THEN
        UNDISCH_TAC `(x:real^3) IN (cc:(real^N->bool)->real^3->bool) j` THEN SET_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `!i j x. i IN GG /\ j IN FF UNION GG /\ ~(j = i) /\
              x IN (ee:(real^N->bool)->real^3->bool) i /\
              x IN (cc:(real^N->bool)->real^3->bool) j
              ==> j IN FF /\ x IN (dd:(real^N->bool)->real^3->bool) j`
    (LABEL_TAC "WG") THENL
     [MAP_EVERY X_GEN_TAC [`i:real^N->bool`; `j:real^N->bool`; `x:real^3`] THEN
      DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
      USE_THEN "EG" (MP_TAC o SPECL [`i:real^N->bool`; `x:real^3`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
      FIRST_X_ASSUM(DISJ_CASES_TAC o REWRITE_RULE[IN_UNION] o check (fun th ->
        concl th = `(j:real^N->bool) IN FF UNION GG`)) THENL
       [ASM_REWRITE_TAC[] THEN
        USE_THEN "CSF" (fun th -> MP_TAC(MP (SPEC `j:real^N->bool` th)
          (ASSUME `(j:real^N->bool) IN FF`))) THEN
        UNDISCH_TAC `(x:real^3) IN (cc:(real^N->bool)->real^3->bool) j` THEN SET_TAC[];
        USE_THEN "CSG" (fun th -> MP_TAC(MP (SPEC `j:real^N->bool` th)
          (ASSUME `(j:real^N->bool) IN GG`))) THEN
        USE_THEN "SDJ" (MP_TAC o SPECL [`i:real^N->bool`; `j:real^N->bool`]) THEN
        ANTS_TAC THENL
         [ASM_REWRITE_TAC[] THEN
          USE_THEN "ING" (fun th -> MP_TAC(EQ_MP (SPEC `i:real^N->bool` th)
            (ASSUME `(i:real^N->bool) IN GG`))) THEN
          USE_THEN "ING" (fun th -> MP_TAC(EQ_MP (SPEC `j:real^N->bool` th)
            (ASSUME `(j:real^N->bool) IN GG`))) THEN
          SIMP_TAC[];
          ALL_TAC] THEN
        MAP_EVERY UNDISCH_TAC
         [`(x:real^3) IN (cc:(real^N->bool)->real^3->bool) j`;
          `(x:real^3) IN (dd:(real^N->bool)->real^3->bool) s INTER
           IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk i)`] THEN
        SET_TAC[]];
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`i:real^N->bool`; `j:real^N->bool`; `k:real^N->bool`; `x:real^3`] THEN
    DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
    MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    FIRST_ASSUM(DISJ_CASES_TAC o REWRITE_RULE[IN_UNION] o check (fun th ->
      concl th = `(i:real^N->bool) IN FF UNION GG`)) THENL
     [USE_THEN "WF" (MP_TAC o SPECL [`i:real^N->bool`; `j:real^N->bool`; `x:real^3`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
      USE_THEN "WF" (MP_TAC o SPECL [`i:real^N->bool`; `k:real^N->bool`; `x:real^3`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
      USE_THEN "SDJ" (MP_TAC o SPECL [`j:real^N->bool`; `k:real^N->bool`]) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN
        USE_THEN "ING" (fun th -> MP_TAC(EQ_MP (SPEC `j:real^N->bool` th)
          (ASSUME `(j:real^N->bool) IN GG`))) THEN
        USE_THEN "ING" (fun th -> MP_TAC(EQ_MP (SPEC `k:real^N->bool` th)
          (ASSUME `(k:real^N->bool) IN GG`))) THEN
        SIMP_TAC[];
        ALL_TAC] THEN
      MAP_EVERY UNDISCH_TAC
       [`(x:real^3) IN IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk j)`;
        `(x:real^3) IN IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk k)`] THEN
      SET_TAC[];
      USE_THEN "WG" (MP_TAC o SPECL [`i:real^N->bool`; `j:real^N->bool`; `x:real^3`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
      USE_THEN "WG" (MP_TAC o SPECL [`i:real^N->bool`; `k:real^N->bool`; `x:real^3`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
      USE_THEN "DDJ" (MP_TAC o SPECL [`j:real^N->bool`; `k:real^N->bool`]) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN
        USE_THEN "INF" (fun th -> MP_TAC(EQ_MP (SPEC `j:real^N->bool` th)
          (ASSUME `(j:real^N->bool) IN FF`))) THEN
        USE_THEN "INF" (fun th -> MP_TAC(EQ_MP (SPEC `k:real^N->bool` th)
          (ASSUME `(k:real^N->bool) IN FF`))) THEN
        SIMP_TAC[];
        ALL_TAC] THEN
      MAP_EVERY UNDISCH_TAC
       [`(x:real^3) IN (dd:(real^N->bool)->real^3->bool) j`;
        `(x:real^3) IN (dd:(real^N->bool)->real^3->bool) k`] THEN
      SET_TAC[]];
    (* connected *)
    UNDISCH_TAC
     `connected (UNIONS {(dd:(real^N->bool)->real^3->bool) s INTER C | s |
                         s IN moi_s34_simp kk (&2) /\ (v:real^N) IN s /\
                         s SUBSET complex_boundary kk} UNION
                 UNIONS {moi_s34_oarc tt kk (f1:real^N->real^3) rr g | g |
                         g IN moi_s34_simp kk (&1) /\ v IN g /\
                         g SUBSET complex_boundary kk})` THEN
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The patches X_r = rr r INTER C_v at a vertex v, their boundary           *)
(* arcs and how they meet each other and the splitting disks; the patches  *)
(* and the splitting disks cover a neighbourhood in Sigma_v of each of     *)
(* their points off J_v.                                                     *)
(* ------------------------------------------------------------------------- *)

let MOI_S4OT_PATCH_FACTS = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car dd rr v.
     moi_s34_tube tt kk /\ moi_s34_frame tt kk h ep f1 car /\
     moi_s34_fdisk tt kk f1 car dd /\ moi_s34_resid tt kk f1 car dd rr /\ {v} IN kk
     ==> pl_sphere 2 (frontier (IMAGE f1 (moi_s34_vb tt kk v))) /\
         frontier (IMAGE f1 (moi_s34_vb tt kk v)) =
         IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_bd tt kk) UNION
         UNIONS {IMAGE f1 (moi_s34_sd tt kk g) | g | g IN moi_s34_simp kk (&1) /\ v IN g} /\
         compact (IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_bd tt kk)) /\
         FINITE {r | r IN moi_s34_simp kk (&3) /\ v IN r} /\
         FINITE {g | g IN moi_s34_simp kk (&1) /\ v IN g} /\
         (!r. r IN moi_s34_simp kk (&3) /\ v IN r
              ==> rr r INTER IMAGE f1 (moi_s34_vb tt kk v) SUBSET
                  IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_bd tt kk) /\
                  pl_cell_with_boundary 2 (rr r INTER IMAGE f1 (moi_s34_vb tt kk v))
                    (UNIONS {dd s INTER IMAGE f1 (moi_s34_vb tt kk v) | s |
                             s IN moi_s34_simp kk (&2) /\ v IN s /\ s SUBSET r} UNION
                     UNIONS {rr r INTER IMAGE f1 (moi_s34_sd tt kk g) | g |
                             g IN moi_s34_simp kk (&1) /\ v IN g /\ g SUBSET r})) /\
         (!s. s IN moi_s34_simp kk (&2)
              ==> dd s INTER IMAGE f1 (moi_s34_vb tt kk v) SUBSET
                  IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_bd tt kk)) /\
         (!g. g IN moi_s34_simp kk (&1) /\ v IN g
              ==> IMAGE f1 (moi_s34_sd tt kk g) INTER
                  IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_bd tt kk) =
                  IMAGE f1 (moi_s34_sd tt kk g INTER moi_s34_bd tt kk))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                 `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`]
    MOI_S4G_FRAME_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> let cs = CONJUNCTS th in
    ASSUME_TAC (el 0 cs) THEN LABEL_TAC "INJ" (el 1 cs) THEN
    MP_TAC(SPEC `v:real^N` (el 2 cs))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `moi_s34_vb tt kk (v:real^N) SUBSET moi_s34_nb tt kk` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S4G_VB_NB THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                   `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                   `v:real^N`] MOI_S4L_SIGMA) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `moi_s34_nb tt (kk:(real^N->bool)->bool)` THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`]
        MOI_S4G_VB_CLOSED) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      SUBGOAL_THEN `moi_s34_vb tt kk (v:real^N) INTER moi_s34_bd tt kk =
                    moi_s34_vb tt kk v INTER (moi_s34_vb tt kk v INTER moi_s34_bd tt kk)`
      SUBST1_TAC THENL [SET_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC COMPACT_INTER_CLOSED THEN ASM_REWRITE_TAC[]];
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `3`; `{v:real^N}`]
      MOI_S4OT_STAR_FINITE) THEN
    ASM_REWRITE_TAC[NOT_INSERT_EMPTY; SING_SUBSET];
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `1`; `{v:real^N}`]
      MOI_S4OT_STAR_FINITE) THEN
    ASM_REWRITE_TAC[NOT_INSERT_EMPTY; SING_SUBSET];
    X_GEN_TAC `r:real^N->bool` THEN STRIP_TAC THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                     `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                     `dd:(real^N->bool)->real^3->bool`; `rr:(real^N->bool)->real^3->bool`;
                     `r:real^N->bool`; `moi_s34_vb tt kk (v:real^N)`] MOI_S4G_RR_SUB) THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `f1:real^N->real^3`;
                     `car:(real^N->bool)->real^3->bool`; `dd:(real^N->bool)->real^3->bool`;
                     `rr:(real^N->bool)->real^3->bool`; `r:real^N->bool`] MOI_S4OT_RR_FACTS) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `v:real^N` o el 2 o CONJUNCTS) THEN
      ASM_REWRITE_TAC[]];
    X_GEN_TAC `s:real^N->bool` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                   `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                   `dd:(real^N->bool)->real^3->bool`; `s:real^N->bool`;
                   `moi_s34_vb tt kk (v:real^N)`] MOI_S4G_DD_SUB) THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    X_GEN_TAC `g:real^N->bool` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`f1:real^N->real^3`; `moi_s34_nb tt (kk:(real^N->bool)->bool)`;
                   `moi_s34_sd tt kk (g:real^N->bool)`;
                   `moi_s34_vb tt kk (v:real^N) INTER moi_s34_bd tt kk`] MOI_S4OT_IMG_INTER) THEN
    ANTS_TAC THENL
     [USE_THEN "INJ" (fun th -> REWRITE_TAC[th]) THEN
      ASM_SIMP_TAC[MOI_S4G_SD_NB] THEN ASM SET_TAC[];
      DISCH_THEN SUBST1_TAC] THEN
    AP_TERM_TAC THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `g:real^N->bool`;
                   `v:real^N`] MOI_S4G_SD_SUB_VB) THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[]]);;

let MOI_S4OT_PATCH_MEET = prove
 (`!(tt:(real^N->bool)->bool) kk (f1:real^N->real^3) car dd rr v.
     moi_s34_tube tt kk /\ moi_s34_resid tt kk f1 car dd rr /\ {v} IN kk
     ==> (!r r'. r IN moi_s34_simp kk (&3) /\ r' IN moi_s34_simp kk (&3) /\ ~(r = r')
                 ==> (rr r INTER IMAGE f1 (moi_s34_vb tt kk v)) INTER
                     (rr r' INTER IMAGE f1 (moi_s34_vb tt kk v)) =
                     UNIONS {dd s INTER IMAGE f1 (moi_s34_vb tt kk v) | s |
                             s IN moi_s34_simp kk (&2) /\ s SUBSET r /\ s SUBSET r'}) /\
         (!r g. r IN moi_s34_simp kk (&3) /\ g IN moi_s34_simp kk (&1) /\ v IN g
                ==> (rr r INTER IMAGE f1 (moi_s34_vb tt kk v)) INTER
                    IMAGE f1 (moi_s34_sd tt kk g) =
                    rr r INTER IMAGE f1 (moi_s34_sd tt kk g))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THEN REPEAT STRIP_TAC THENL
   [MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `f1:real^N->real^3`;
                   `car:(real^N->bool)->real^3->bool`; `dd:(real^N->bool)->real^3->bool`;
                   `rr:(real^N->bool)->real^3->bool`; `r:real^N->bool`] MOI_S4OT_RR_FACTS) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `r':real^N->bool` o el 7 o CONJUNCTS) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `UNIONS {(dd:(real^N->bool)->real^3->bool) s INTER
              IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v) | s |
              s IN moi_s34_simp kk (&2) /\ s SUBSET r /\ s SUBSET r'} =
      UNIONS {dd s | s | s IN moi_s34_simp kk (&2) /\ s SUBSET r /\ s SUBSET r'} INTER
      IMAGE f1 (moi_s34_vb tt kk v)` SUBST1_TAC THENL
     [GEN_REWRITE_TAC I [EXTENSION] THEN
      REWRITE_TAC[IN_INTER; UNIONS_GSPEC; IN_ELIM_THM] THEN MESON_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `(rr:(real^N->bool)->real^3->bool) r INTER rr r'`)) THEN
    SET_TAC[];
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `g:real^N->bool`;
                   `v:real^N`] MOI_S4G_SD_SUB_VB) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o ISPEC `f1:real^N->real^3` o MATCH_MP IMAGE_SUBSET) THEN
    SET_TAC[]]);;

(* The face arc of a face s shared by two 3-simplices r, r' at v is the     *)
(* gluing arc of their patches. *)

let MOI_S4OT_TWO_PATCHES = prove
 (`!(tt:(real^N->bool)->bool) kk (f1:real^N->real^3) car dd rr v r r' s.
     moi_s34_tube tt kk /\ moi_s34_resid tt kk f1 car dd rr /\ {v} IN kk /\
     r IN moi_s34_simp kk (&3) /\ r' IN moi_s34_simp kk (&3) /\ ~(r = r') /\
     s IN moi_s34_simp kk (&2) /\ s SUBSET r /\ s SUBSET r'
     ==> (rr r INTER IMAGE f1 (moi_s34_vb tt kk v)) INTER
         (rr r' INTER IMAGE f1 (moi_s34_vb tt kk v)) =
         dd s INTER IMAGE f1 (moi_s34_vb tt kk v)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `dd:(real^N->bool)->real^3->bool`;
                 `rr:(real^N->bool)->real^3->bool`; `v:real^N`] MOI_S4OT_PATCH_MEET) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPECL [`r:real^N->bool`; `r':real^N->bool`] o
    CONJUNCT1) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM] THEN
  X_GEN_TAC `y:real^3` THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `s':real^N->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `s':real^N->bool = s` (fun th -> ASM_MESON_TAC[th]) THEN
    MATCH_MP_TAC MOI_S4OT_TETS_FACE THEN
    MAP_EVERY EXISTS_TAC [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                          `r:real^N->bool`; `r':real^N->bool`] THEN
    ASM_REWRITE_TAC[];
    DISCH_TAC THEN EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[]]);;

let MOI_S4OT_LC_FACE = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car dd rr v r r' s x.
     moi_s34_tube tt kk /\ moi_s34_frame tt kk h ep f1 car /\
     moi_s34_fdisk tt kk f1 car dd /\ moi_s34_resid tt kk f1 car dd rr /\ {v} IN kk /\
     r IN moi_s34_simp kk (&3) /\ r' IN moi_s34_simp kk (&3) /\ ~(r = r') /\
     v IN r /\ v IN r' /\ s IN moi_s34_simp kk (&2) /\ v IN s /\ s SUBSET r /\ s SUBSET r' /\
     x IN dd s INTER IMAGE f1 (moi_s34_vb tt kk v) /\
     ~(x IN UNIONS {dd s INTER IMAGE f1 (moi_s34_sd tt kk g) | g |
                    g IN moi_s34_simp kk (&1) /\ v IN g /\ g SUBSET s})
     ==> ?u. open_in (subtopology euclidean (frontier (IMAGE f1 (moi_s34_vb tt kk v)))) u /\
             x IN u /\
             u SUBSET (rr r INTER IMAGE f1 (moi_s34_vb tt kk v)) UNION
                      (rr r' INTER IMAGE f1 (moi_s34_vb tt kk v))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                `dd:(real^N->bool)->real^3->bool`; `rr:(real^N->bool)->real^3->bool`;
                `v:real^N`] MOI_S4OT_PATCH_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> let cs = CONJUNCTS th in
    ASSUME_TAC (el 0 cs) THEN
    ASSUME_TAC (MATCH_MP (SET_RULE `!f a b:real^3->bool. f = a UNION b ==> a SUBSET f`) (el 1 cs)) THEN
    LABEL_TAC "PX" (el 5 cs)) THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `dd:(real^N->bool)->real^3->bool`;
                 `rr:(real^N->bool)->real^3->bool`; `v:real^N`; `r:real^N->bool`;
                 `r':real^N->bool`; `s:real^N->bool`] MOI_S4OT_TWO_PATCHES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `dd:(real^N->bool)->real^3->bool`;
                 `s:real^N->bool`] MOI_S4OT_DD_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `v:real^N` o el 3 o CONJUNCTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  USE_THEN "PX" (fun th -> MP_TAC(MP (SPEC `r:real^N->bool` th)
    (CONJ (ASSUME `(r:real^N->bool) IN moi_s34_simp kk (&3)`) (ASSUME `(v:real^N) IN r`)))) THEN
  USE_THEN "PX" (fun th -> MP_TAC(MP (SPEC `r':real^N->bool` th)
    (CONJ (ASSUME `(r':real^N->bool) IN moi_s34_simp kk (&3)`) (ASSUME `(v:real^N) IN r'`)))) THEN
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC MOI_S4OT_GLUE_NBHD THEN
  MAP_EVERY EXISTS_TAC
   [`UNIONS {(dd:(real^N->bool)->real^3->bool) s INTER
             IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v) | s |
             s IN moi_s34_simp kk (&2) /\ (v:real^N) IN s /\ s SUBSET r} UNION
     UNIONS {(rr:(real^N->bool)->real^3->bool) r INTER IMAGE f1 (moi_s34_sd tt kk g) | g |
             g IN moi_s34_simp kk (&1) /\ v IN g /\ g SUBSET r}`;
    `UNIONS {(dd:(real^N->bool)->real^3->bool) s INTER
             IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v) | s |
             s IN moi_s34_simp kk (&2) /\ (v:real^N) IN s /\ s SUBSET r'} UNION
     UNIONS {(rr:(real^N->bool)->real^3->bool) r' INTER IMAGE f1 (moi_s34_sd tt kk g) | g |
             g IN moi_s34_simp kk (&1) /\ v IN g /\ g SUBSET r'}`;
    `(dd:(real^N->bool)->real^3->bool) s INTER IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v)`;
    `UNIONS {(dd:(real^N->bool)->real^3->bool) s INTER
             IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g) | g |
             g IN moi_s34_simp kk (&1) /\ (v:real^N) IN g /\ g SUBSET s}`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_bd tt kk)` THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_bd tt kk)` THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC(SET_RULE `!a b c:real^3->bool. a SUBSET b ==> a SUBSET b UNION c`) THEN
    GEN_REWRITE_TAC I [SUBSET] THEN REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM] THEN
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN EXISTS_TAC `s:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC(SET_RULE `!a b c:real^3->bool. a SUBSET b ==> a SUBSET b UNION c`) THEN
    GEN_REWRITE_TAC I [SUBSET] THEN REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM] THEN
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN EXISTS_TAC `s:real^N->bool` THEN
    ASM_REWRITE_TAC[]]);;

let MOI_S4OT_LC_RIM = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car dd rr v r g x.
     moi_s34_tube tt kk /\ moi_s34_frame tt kk h ep f1 car /\
     moi_s34_fdisk tt kk f1 car dd /\ moi_s34_resid tt kk f1 car dd rr /\ {v} IN kk /\
     r IN moi_s34_simp kk (&3) /\ v IN r /\ g IN moi_s34_simp kk (&1) /\ v IN g /\
     g SUBSET r /\
     x IN rr r INTER IMAGE f1 (moi_s34_sd tt kk g) /\
     ~(x IN UNIONS {dd s INTER IMAGE f1 (moi_s34_sd tt kk g) | s |
                    s IN moi_s34_simp kk (&2) /\ g SUBSET s /\ s SUBSET r})
     ==> ?u. open_in (subtopology euclidean (frontier (IMAGE f1 (moi_s34_vb tt kk v)))) u /\
             x IN u /\
             u SUBSET (rr r INTER IMAGE f1 (moi_s34_vb tt kk v)) UNION
                      IMAGE f1 (moi_s34_sd tt kk g)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                `dd:(real^N->bool)->real^3->bool`; `rr:(real^N->bool)->real^3->bool`;
                `v:real^N`] MOI_S4OT_PATCH_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> let cs = CONJUNCTS th in
    ASSUME_TAC (el 0 cs) THEN
    ASSUME_TAC (MATCH_MP (SET_RULE `!f a b:real^3->bool. f = a UNION b ==> a SUBSET f /\ b SUBSET f`)
      (el 1 cs)) THEN
    LABEL_TAC "PX" (el 5 cs)) THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                `dd:(real^N->bool)->real^3->bool`; `rr:(real^N->bool)->real^3->bool`;
                `g:real^N->bool`] MOI_S4OT_RIM_SETUP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> let cs = CONJUNCTS th in
    ASSUME_TAC (el 0 cs) THEN MP_TAC(SPEC `r:real^N->bool` (el 4 cs))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `dd:(real^N->bool)->real^3->bool`;
                 `rr:(real^N->bool)->real^3->bool`; `r:real^N->bool`] MOI_S4OT_RR_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `g:real^N->bool` o el 3 o CONJUNCTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `dd:(real^N->bool)->real^3->bool`;
                 `rr:(real^N->bool)->real^3->bool`; `v:real^N`] MOI_S4OT_PATCH_MEET) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`r:real^N->bool`; `g:real^N->bool`] o CONJUNCT2) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  USE_THEN "PX" (fun th -> MP_TAC(MP (SPEC `r:real^N->bool` th)
    (CONJ (ASSUME `(r:real^N->bool) IN moi_s34_simp kk (&3)`) (ASSUME `(v:real^N) IN r`)))) THEN
  STRIP_TAC THEN
  MATCH_MP_TAC MOI_S4OT_GLUE_NBHD THEN
  MAP_EVERY EXISTS_TAC
   [`UNIONS {(dd:(real^N->bool)->real^3->bool) s INTER
             IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v) | s |
             s IN moi_s34_simp kk (&2) /\ (v:real^N) IN s /\ s SUBSET r} UNION
     UNIONS {(rr:(real^N->bool)->real^3->bool) r INTER IMAGE f1 (moi_s34_sd tt kk g) | g |
             g IN moi_s34_simp kk (&1) /\ v IN g /\ g SUBSET r}`;
    `IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g INTER moi_s34_bd tt kk)`;
    `(rr:(real^N->bool)->real^3->bool) r INTER IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g)`;
    `UNIONS {(dd:(real^N->bool)->real^3->bool) s INTER
             IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g) | s |
             s IN moi_s34_simp kk (&2) /\ (g:real^N->bool) SUBSET s /\ s SUBSET r}`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_bd tt kk)` THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `UNIONS {IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g) | g |
                        g IN moi_s34_simp kk (&1) /\ (v:real^N) IN g}` THEN
    ASM_REWRITE_TAC[] THEN
    GEN_REWRITE_TAC I [SUBSET] THEN REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM] THEN
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN EXISTS_TAC `g:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC(SET_RULE `!a b c:real^3->bool. a SUBSET c ==> a SUBSET b UNION c`) THEN
    GEN_REWRITE_TAC I [SUBSET] THEN REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM] THEN
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN EXISTS_TAC `g:real^N->bool` THEN
    ASM_REWRITE_TAC[]]);;

let MOI_S4OT_LC_PT = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car dd rr v r r' s g x.
     moi_s34_tube tt kk /\ moi_s34_frame tt kk h ep f1 car /\
     moi_s34_fdisk tt kk f1 car dd /\ moi_s34_resid tt kk f1 car dd rr /\ {v} IN kk /\
     r IN moi_s34_simp kk (&3) /\ r' IN moi_s34_simp kk (&3) /\ ~(r = r') /\
     v IN r /\ v IN r' /\ s IN moi_s34_simp kk (&2) /\ s SUBSET r /\ s SUBSET r' /\
     g IN moi_s34_simp kk (&1) /\ v IN g /\ g SUBSET s /\
     x IN dd s INTER IMAGE f1 (moi_s34_sd tt kk g)
     ==> ?u. open_in (subtopology euclidean (frontier (IMAGE f1 (moi_s34_vb tt kk v)))) u /\
             x IN u /\
             u SUBSET ((rr r INTER IMAGE f1 (moi_s34_vb tt kk v)) UNION
                       (rr r' INTER IMAGE f1 (moi_s34_vb tt kk v))) UNION
                      IMAGE f1 (moi_s34_sd tt kk g)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(v:real^N) IN s` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                `dd:(real^N->bool)->real^3->bool`; `rr:(real^N->bool)->real^3->bool`;
                `v:real^N`] MOI_S4OT_PATCH_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> let cs = CONJUNCTS th in
    ASSUME_TAC (el 0 cs) THEN
    ASSUME_TAC (MATCH_MP (SET_RULE `!f a b:real^3->bool. f = a UNION b ==> a SUBSET f /\ b SUBSET f`)
      (el 1 cs)) THEN
    LABEL_TAC "PX" (el 5 cs)) THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                `dd:(real^N->bool)->real^3->bool`; `rr:(real^N->bool)->real^3->bool`;
                `g:real^N->bool`] MOI_S4OT_RIM_SETUP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> let cs = CONJUNCTS th in
    ASSUME_TAC (el 0 cs) THEN LABEL_TAC "RS" (el 4 cs)) THEN
  (* the two rim arcs at g and their union c *)
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `dd:(real^N->bool)->real^3->bool`;
                 `rr:(real^N->bool)->real^3->bool`; `r:real^N->bool`] MOI_S4OT_RR_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `g:real^N->bool` o el 3 o CONJUNCTS) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; DISCH_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `dd:(real^N->bool)->real^3->bool`;
                 `rr:(real^N->bool)->real^3->bool`; `r':real^N->bool`] MOI_S4OT_RR_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `g:real^N->bool` o el 3 o CONJUNCTS) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; DISCH_TAC] THEN
  ABBREV_TAC `C = IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v)` THEN
  ABBREV_TAC `D = IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g)` THEN
  ABBREV_TAC `R = IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g INTER moi_s34_bd tt kk)` THEN
  SUBGOAL_THEN `(D:real^3->bool) SUBSET C` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["C"; "D"] THEN MATCH_MP_TAC IMAGE_SUBSET THEN
    MATCH_MP_TAC MOI_S4G_SD_SUB_VB THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(D:real^3->bool) SUBSET frontier C` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `UNIONS {IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g) | g |
                        g IN moi_s34_simp kk (&1) /\ (v:real^N) IN g}` THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "D" THEN
    GEN_REWRITE_TAC I [SUBSET] THEN REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM] THEN
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN EXISTS_TAC `g:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the two patches and their union Y *)
  USE_THEN "PX" (fun th -> MP_TAC(MP (SPEC `r:real^N->bool` th)
    (CONJ (ASSUME `(r:real^N->bool) IN moi_s34_simp kk (&3)`) (ASSUME `(v:real^N) IN r`)))) THEN
  USE_THEN "PX" (fun th -> MP_TAC(MP (SPEC `r':real^N->bool` th)
    (CONJ (ASSUME `(r':real^N->bool) IN moi_s34_simp kk (&3)`) (ASSUME `(v:real^N) IN r'`)))) THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `dd:(real^N->bool)->real^3->bool`;
                 `rr:(real^N->bool)->real^3->bool`; `v:real^N`; `r:real^N->bool`;
                 `r':real^N->bool`; `s:real^N->bool`] MOI_S4OT_TWO_PATCHES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[] THEN DISCH_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `dd:(real^N->bool)->real^3->bool`;
                 `s:real^N->bool`] MOI_S4OT_DD_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> let cs = CONJUNCTS th in
    MP_TAC(SPEC `v:real^N` (el 3 cs)) THEN MP_TAC(SPEC `g:real^N->bool` (el 4 cs))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `p:real^3`) THEN DISCH_TAC THEN
  SUBGOAL_THEN `p:real^3 = x` SUBST_ALL_TAC THENL
   [UNDISCH_TAC `(x:real^3) IN (dd:(real^N->bool)->real^3->bool) s INTER D` THEN
    ASM_REWRITE_TAC[IN_SING] THEN MESON_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `ES = UNIONS {(dd:(real^N->bool)->real^3->bool) s INTER
                           IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g') | g' |
                           g' IN moi_s34_simp kk (&1) /\ (v:real^N) IN g' /\ g' SUBSET s}` THEN
  SUBGOAL_THEN `(x:real^3) IN ES` ASSUME_TAC THENL
   [EXPAND_TAC "ES" THEN REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM] THEN
    EXISTS_TAC `g:real^N->bool` THEN ASM_REWRITE_TAC[IN_SING];
    ALL_TAC] THEN
  ABBREV_TAC `JR = UNIONS {(dd:(real^N->bool)->real^3->bool) s' INTER C | s' |
                           s' IN moi_s34_simp kk (&2) /\ (v:real^N) IN s' /\ s' SUBSET r} UNION
                   UNIONS {(rr:(real^N->bool)->real^3->bool) r INTER
                           IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g') | g' |
                           g' IN moi_s34_simp kk (&1) /\ v IN g' /\ g' SUBSET r}` THEN
  ABBREV_TAC `JR' = UNIONS {(dd:(real^N->bool)->real^3->bool) s' INTER C | s' |
                            s' IN moi_s34_simp kk (&2) /\ (v:real^N) IN s' /\ s' SUBSET r'} UNION
                    UNIONS {(rr:(real^N->bool)->real^3->bool) r' INTER
                            IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g') | g' |
                            g' IN moi_s34_simp kk (&1) /\ v IN g' /\ g' SUBSET r'}` THEN
  SUBGOAL_THEN `(dd:(real^N->bool)->real^3->bool) s INTER C SUBSET JR /\
                dd s INTER C SUBSET JR' /\
                (rr:(real^N->bool)->real^3->bool) r INTER D SUBSET JR /\
                rr r' INTER D SUBSET JR'` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["JR"; "JR'"; "D"] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC(SET_RULE `!a b c:real^3->bool. a SUBSET b ==> a SUBSET b UNION c`);
      MATCH_MP_TAC(SET_RULE `!a b c:real^3->bool. a SUBSET b ==> a SUBSET b UNION c`);
      MATCH_MP_TAC(SET_RULE `!a b c:real^3->bool. a SUBSET c ==> a SUBSET b UNION c`);
      MATCH_MP_TAC(SET_RULE `!a b c:real^3->bool. a SUBSET c ==> a SUBSET b UNION c`)] THEN
    GEN_REWRITE_TAC I [SUBSET] THEN REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM] THEN
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THENL
     [EXISTS_TAC `s:real^N->bool`; EXISTS_TAC `s:real^N->bool`;
      EXISTS_TAC `g:real^N->bool`; EXISTS_TAC `g:real^N->bool`] THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  (* Y = X_r UNION X_r' is a disk *)
  MP_TAC(ISPECL [`(rr:(real^N->bool)->real^3->bool) r INTER C`; `JR:real^3->bool`;
                 `(rr:(real^N->bool)->real^3->bool) r' INTER C`; `JR':real^3->bool`;
                 `(dd:(real^N->bool)->real^3->bool) s INTER C`; `ES:real^3->bool`]
    MOI_S4OT_DISK_GLUE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  ABBREV_TAC `EB = UNIONS {(dd:(real^N->bool)->real^3->bool) s' INTER D | s' |
                           s' IN moi_s34_simp kk (&2) /\ (g:real^N->bool) SUBSET s' /\
                           s' SUBSET r}` THEN
  ABBREV_TAC `EB' = UNIONS {(dd:(real^N->bool)->real^3->bool) s' INTER D | s' |
                            s' IN moi_s34_simp kk (&2) /\ (g:real^N->bool) SUBSET s' /\
                            s' SUBSET r'}` THEN
  SUBGOAL_THEN `(x:real^3) IN EB /\ x IN EB'` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["EB"; "EB'"] THEN REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM] THEN
    CONJ_TAC THEN EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[IN_SING];
    ALL_TAC] THEN
  SUBGOAL_THEN `((rr:(real^N->bool)->real^3->bool) r INTER D) INTER (rr r' INTER D) = {x}`
  ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`((rr:(real^N->bool)->real^3->bool) r INTER C) INTER (rr r' INTER C) =
       (dd:(real^N->bool)->real^3->bool) s INTER C`;
      `(D:real^3->bool) SUBSET C`;
      `(dd:(real^N->bool)->real^3->bool) s INTER D = {x}`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(rr:(real^N->bool)->real^3->bool) r INTER D`; `EB:real^3->bool`]
    MOI_S4OT_CELL1_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `x:real^3` o last o CONJUNCTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`(rr:(real^N->bool)->real^3->bool) r' INTER D`; `EB':real^3->bool`]
    MOI_S4OT_CELL1_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `x:real^3` o last o CONJUNCTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `y':real^3` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`(rr:(real^N->bool)->real^3->bool) r INTER D`;
                 `(rr:(real^N->bool)->real^3->bool) r' INTER D`;
                 `y:real^3`; `x:real^3`; `y':real^3`] MOI_S4OT_ARC_JOIN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [SUBGOAL_THEN `{y:real^3,x} = EB` SUBST1_TAC THENL
       [UNDISCH_TAC `EB = {x:real^3,y}` THEN SET_TAC[]; FIRST_ASSUM ACCEPT_TAC];
      SUBGOAL_THEN `{x:real^3,y'} = EB'` SUBST1_TAC THENL
       [UNDISCH_TAC `EB' = {x:real^3,y'}` THEN SET_TAC[]; FIRST_ASSUM ACCEPT_TAC]];
    DISCH_TAC] THEN
  (* glue Y and D along c *)
  SUBGOAL_THEN `~((x:real^3) IN {y,y'})` ASSUME_TAC THENL
   [REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`frontier(C:real^3->bool)`;
                 `(rr:(real^N->bool)->real^3->bool) r INTER C UNION rr r' INTER C`;
                 `(JR UNION JR') DIFF ((dd:(real^N->bool)->real^3->bool) s INTER C DIFF ES)`;
                 `D:real^3->bool`; `R:real^3->bool`;
                 `(rr:(real^N->bool)->real^3->bool) r INTER D UNION rr r' INTER D`;
                 `{y:real^3,y'}`; `x:real^3`] MOI_S4OT_GLUE_NBHD) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[UNION_SUBSET] THEN CONJ_TAC THEN MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_bd tt kk)` THEN
      ASM_REWRITE_TAC[];
      MAP_EVERY UNDISCH_TAC [`(D:real^3->bool) SUBSET C`] THEN SET_TAC[];
      (* c in the boundary of Y *)
      SUBGOAL_THEN `(rr:(real^N->bool)->real^3->bool) r INTER D INTER
                    ((dd:(real^N->bool)->real^3->bool) s INTER C DIFF ES) = {} /\
                    rr r' INTER D INTER (dd s INTER C DIFF ES) = {}` MP_TAC THENL
       [MAP_EVERY UNDISCH_TAC
         [`(dd:(real^N->bool)->real^3->bool) s INTER D = {x}`; `(x:real^3) IN ES`] THEN
        SET_TAC[];
        MAP_EVERY UNDISCH_TAC
         [`(rr:(real^N->bool)->real^3->bool) r INTER D SUBSET JR`;
          `(rr:(real^N->bool)->real^3->bool) r' INTER D SUBSET JR'`] THEN
        SET_TAC[]];
      ASM_REWRITE_TAC[UNION_SUBSET] THEN
      CONJ_TAC THEN USE_THEN "RS" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ASM SET_TAC[]];
    MATCH_MP_TAC MONO_EXISTS THEN SET_TAC[]]);;

(* The local covering: every point of the patches and splitting disks at v  *)
(* off J_v has a Sigma_v-neighbourhood inside their union.                  *)

let MOI_S4OT_LOCAL_COVER = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car dd rr v x.
     moi_s34_tube tt kk /\ moi_s34_frame tt kk h ep f1 car /\
     moi_s34_fdisk tt kk f1 car dd /\ moi_s34_resid tt kk f1 car dd rr /\ {v} IN kk /\
     x IN UNIONS {rr r INTER IMAGE f1 (moi_s34_vb tt kk v) | r |
                  r IN moi_s34_simp kk (&3) /\ v IN r} UNION
          UNIONS {IMAGE f1 (moi_s34_sd tt kk g) | g | g IN moi_s34_simp kk (&1) /\ v IN g} /\
     ~(x IN UNIONS {dd s INTER IMAGE f1 (moi_s34_vb tt kk v) | s |
                    s IN moi_s34_simp kk (&2) /\ v IN s /\ s SUBSET complex_boundary kk} UNION
            UNIONS {moi_s34_oarc tt kk f1 rr g | g |
                    g IN moi_s34_simp kk (&1) /\ v IN g /\ g SUBSET complex_boundary kk})
     ==> ?u. open_in (subtopology euclidean (frontier (IMAGE f1 (moi_s34_vb tt kk v)))) u /\
             x IN u /\
             u SUBSET UNIONS {rr r INTER IMAGE f1 (moi_s34_vb tt kk v) | r |
                              r IN moi_s34_simp kk (&3) /\ v IN r} UNION
                      UNIONS {IMAGE f1 (moi_s34_sd tt kk g) | g |
                              g IN moi_s34_simp kk (&1) /\ v IN g}`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> let cs = CONJUNCTS th in
    MAP_EVERY ASSUME_TAC (butlast(butlast cs)) THEN
    LABEL_TAC "XW" (el 5 cs) THEN LABEL_TAC "XJ" (el 6 cs)) THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                `dd:(real^N->bool)->real^3->bool`; `rr:(real^N->bool)->real^3->bool`;
                `v:real^N`] MOI_S4OT_PATCH_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> let cs = CONJUNCTS th in
    ASSUME_TAC (el 0 cs) THEN
    ASSUME_TAC (MATCH_MP (SET_RULE `!f a b:real^3->bool. f = a UNION b ==> a SUBSET f /\ b SUBSET f`)
      (el 1 cs)) THEN
    LABEL_TAC "PX" (el 5 cs)) THEN
  ABBREV_TAC `W = UNIONS {(rr:(real^N->bool)->real^3->bool) r INTER
                          IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v) | r |
                          r IN moi_s34_simp kk (&3) /\ (v:real^N) IN r} UNION
                  UNIONS {IMAGE f1 (moi_s34_sd tt kk g) | g |
                          g IN moi_s34_simp kk (&1) /\ v IN g}` THEN
  SUBGOAL_THEN
   `(!r. r IN moi_s34_simp kk (&3) /\ (v:real^N) IN r
         ==> (rr:(real^N->bool)->real^3->bool) r INTER
             IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v) SUBSET W) /\
    (!g. g IN moi_s34_simp kk (&1) /\ v IN g
         ==> IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g) SUBSET W)`
  (CONJUNCTS_THEN2 (LABEL_TAC "CW") (LABEL_TAC "DW")) THENL
   [EXPAND_TAC "W" THEN CONJ_TAC THEN X_GEN_TAC `q:real^N->bool` THEN DISCH_TAC THEN
    GEN_REWRITE_TAC I [SUBSET] THEN REWRITE_TAC[IN_UNION; UNIONS_GSPEC; IN_ELIM_THM] THEN
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THENL [DISJ1_TAC; DISJ2_TAC] THEN
    EXISTS_TAC `q:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* a point of a face arc of a face s of a 3-simplex r at v *)
  SUBGOAL_THEN
   `!s r. s IN moi_s34_simp kk (&2) /\ (v:real^N) IN s /\ r IN moi_s34_simp kk (&3) /\
          s SUBSET r /\
          x IN (dd:(real^N->bool)->real^3->bool) s INTER
               IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v)
          ==> ?u. open_in (subtopology euclidean
                            (frontier (IMAGE f1 (moi_s34_vb tt kk v)))) u /\
                  x IN u /\ u SUBSET W`
  (LABEL_TAC "FH") THENL
   [MAP_EVERY X_GEN_TAC [`s:real^N->bool`; `r:real^N->bool`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `~((s:real^N->bool) SUBSET complex_boundary kk)` ASSUME_TAC THENL
     [DISCH_TAC THEN
      USE_THEN "XJ" (MP_TAC o SPEC `s:real^N->bool` o
        REWRITE_RULE[UNIONS_GSPEC; IN_ELIM_THM; NOT_EXISTS_THM] o CONJUNCT1 o
        REWRITE_RULE[IN_UNION; DE_MORGAN_THM]) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `s:real^N->bool`]
      MOI_S4OT_FACE_TETS) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `ra:real^N->bool` (X_CHOOSE_THEN `rb:real^N->bool`
      STRIP_ASSUME_TAC) o CONJUNCT2) THEN
    SUBGOAL_THEN `?r'. r' IN moi_s34_simp kk (&3) /\ (s:real^N->bool) SUBSET r' /\ ~(r' = r)`
    STRIP_ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[EXTENSION; IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY] o
        check (fun th -> is_eq(concl th) && rand(concl th) = `{ra:real^N->bool,rb}`)) THEN
      DISCH_THEN(fun th -> MP_TAC(SPEC `ra:real^N->bool` th) THEN
                           MP_TAC(SPEC `rb:real^N->bool` th)) THEN
      REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
      ASM_CASES_TAC `r:real^N->bool = ra` THENL
       [EXISTS_TAC `rb:real^N->bool` THEN ASM_REWRITE_TAC[];
        EXISTS_TAC `ra:real^N->bool` THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `(v:real^N) IN r /\ v IN r'` STRIP_ASSUME_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`(v:real^N) IN s`; `(s:real^N->bool) SUBSET r`;
                             `(s:real^N->bool) SUBSET r'`] THEN SET_TAC[];
      ALL_TAC] THEN
    ASM_CASES_TAC
     `(x:real^3) IN UNIONS {(dd:(real^N->bool)->real^3->bool) s INTER
                            IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g) | g |
                            g IN moi_s34_simp kk (&1) /\ (v:real^N) IN g /\ g SUBSET s}`
    THENL
     [FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[UNIONS_GSPEC; IN_ELIM_THM] o check (fun th ->
        can (find_term ((=) `UNIONS:((real^3->bool)->bool)->real^3->bool`)) (concl th) &&
        not (is_neg(concl th)))) THEN
      DISCH_THEN(X_CHOOSE_THEN `g:real^N->bool` STRIP_ASSUME_TAC) THEN
      MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                    `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                    `dd:(real^N->bool)->real^3->bool`; `rr:(real^N->bool)->real^3->bool`;
                    `v:real^N`; `r:real^N->bool`; `r':real^N->bool`; `s:real^N->bool`;
                    `g:real^N->bool`; `x:real^3`] MOI_S4OT_LC_PT) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `u:real^3->bool` THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "CW" (fun th -> MP_TAC(MP (SPEC `r:real^N->bool` th)
        (CONJ (ASSUME `(r:real^N->bool) IN moi_s34_simp kk (&3)`) (ASSUME `(v:real^N) IN r`))) THEN
        MP_TAC(MP (SPEC `r':real^N->bool` th)
        (CONJ (ASSUME `(r':real^N->bool) IN moi_s34_simp kk (&3)`) (ASSUME `(v:real^N) IN r'`)))) THEN
      USE_THEN "DW" (fun th -> MP_TAC(MP (SPEC `g:real^N->bool` th)
        (CONJ (ASSUME `(g:real^N->bool) IN moi_s34_simp kk (&1)`) (ASSUME `(v:real^N) IN g`)))) THEN
      UNDISCH_TAC `(u:real^3->bool) SUBSET
                   (((rr:(real^N->bool)->real^3->bool) r INTER
                     IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v)) UNION
                    (rr r' INTER IMAGE f1 (moi_s34_vb tt kk v))) UNION
                   IMAGE f1 (moi_s34_sd tt kk g)` THEN
      SET_TAC[];
      MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                    `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                    `dd:(real^N->bool)->real^3->bool`; `rr:(real^N->bool)->real^3->bool`;
                    `v:real^N`; `r:real^N->bool`; `r':real^N->bool`; `s:real^N->bool`;
                    `x:real^3`] MOI_S4OT_LC_FACE) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `u:real^3->bool` THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "CW" (fun th -> MP_TAC(MP (SPEC `r:real^N->bool` th)
        (CONJ (ASSUME `(r:real^N->bool) IN moi_s34_simp kk (&3)`) (ASSUME `(v:real^N) IN r`))) THEN
        MP_TAC(MP (SPEC `r':real^N->bool` th)
        (CONJ (ASSUME `(r':real^N->bool) IN moi_s34_simp kk (&3)`) (ASSUME `(v:real^N) IN r'`)))) THEN
      UNDISCH_TAC `(u:real^3->bool) SUBSET
                   ((rr:(real^N->bool)->real^3->bool) r INTER
                    IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v)) UNION
                   (rr r' INTER IMAGE f1 (moi_s34_vb tt kk v))` THEN
      SET_TAC[]];
    ALL_TAC] THEN
  (* a point of a rim arc *)
  SUBGOAL_THEN
   `!r g. r IN moi_s34_simp kk (&3) /\ (v:real^N) IN r /\ g IN moi_s34_simp kk (&1) /\
          v IN g /\ g SUBSET r /\
          x IN (rr:(real^N->bool)->real^3->bool) r INTER
               IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g)
          ==> ?u. open_in (subtopology euclidean
                            (frontier (IMAGE f1 (moi_s34_vb tt kk v)))) u /\
                  x IN u /\ u SUBSET W`
  (LABEL_TAC "RH") THENL
   [MAP_EVERY X_GEN_TAC [`r:real^N->bool`; `g:real^N->bool`] THEN STRIP_TAC THEN
    ASM_CASES_TAC
     `(x:real^3) IN UNIONS {(dd:(real^N->bool)->real^3->bool) s INTER
                            IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g) | s |
                            s IN moi_s34_simp kk (&2) /\ (g:real^N->bool) SUBSET s /\
                            s SUBSET r}`
    THENL
     [FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[UNIONS_GSPEC; IN_ELIM_THM] o check (fun th ->
        can (find_term ((=) `UNIONS:((real^3->bool)->bool)->real^3->bool`)) (concl th) &&
        not (is_neg(concl th)) &&
        can (find_term ((=) `(g:real^N->bool) SUBSET s`)) (concl th))) THEN
      DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
      USE_THEN "FH" MATCH_MP_TAC THEN
      MAP_EVERY EXISTS_TAC [`s:real^N->bool`; `r:real^N->bool`] THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MAP_EVERY UNDISCH_TAC [`(v:real^N) IN g`; `(g:real^N->bool) SUBSET s`] THEN SET_TAC[];
        MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `g:real^N->bool`;
                       `v:real^N`] MOI_S4G_SD_SUB_VB) THEN
        ASM_REWRITE_TAC[] THEN
        DISCH_THEN(MP_TAC o ISPEC `f1:real^N->real^3` o MATCH_MP IMAGE_SUBSET) THEN
        UNDISCH_TAC `(x:real^3) IN (dd:(real^N->bool)->real^3->bool) s INTER
                     IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g)` THEN
        SET_TAC[]];
      MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                    `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                    `dd:(real^N->bool)->real^3->bool`; `rr:(real^N->bool)->real^3->bool`;
                    `v:real^N`; `r:real^N->bool`; `g:real^N->bool`; `x:real^3`]
        MOI_S4OT_LC_RIM) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `u:real^3->bool` THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "CW" (fun th -> MP_TAC(MP (SPEC `r:real^N->bool` th)
        (CONJ (ASSUME `(r:real^N->bool) IN moi_s34_simp kk (&3)`) (ASSUME `(v:real^N) IN r`)))) THEN
      USE_THEN "DW" (fun th -> MP_TAC(MP (SPEC `g:real^N->bool` th)
        (CONJ (ASSUME `(g:real^N->bool) IN moi_s34_simp kk (&1)`) (ASSUME `(v:real^N) IN g`)))) THEN
      UNDISCH_TAC `(u:real^3->bool) SUBSET
                   ((rr:(real^N->bool)->real^3->bool) r INTER
                    IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v)) UNION
                   IMAGE f1 (moi_s34_sd tt kk g)` THEN
      SET_TAC[]];
    ALL_TAC] THEN
  (* the main case analysis *)
  SUBGOAL_THEN
   `(?r. r IN moi_s34_simp kk (&3) /\ (v:real^N) IN r /\
         (x:real^3) IN (rr:(real^N->bool)->real^3->bool) r INTER
                       IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v)) \/
    (?g. g IN moi_s34_simp kk (&1) /\ v IN g /\ x IN IMAGE f1 (moi_s34_sd tt kk g))`
  MP_TAC THENL
   [USE_THEN "XW" MP_TAC THEN EXPAND_TAC "W" THEN
    REWRITE_TAC[IN_UNION; UNIONS_GSPEC; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THENL
   [(* x in a patch X_r *)
    USE_THEN "PX" (fun th -> MP_TAC(MP (SPEC `r:real^N->bool` th)
      (CONJ (ASSUME `(r:real^N->bool) IN moi_s34_simp kk (&3)`) (ASSUME `(v:real^N) IN r`)))) THEN
    STRIP_TAC THEN
    ABBREV_TAC `JR = UNIONS {(dd:(real^N->bool)->real^3->bool) s INTER
                             IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v) | s |
                             s IN moi_s34_simp kk (&2) /\ (v:real^N) IN s /\ s SUBSET r} UNION
                     UNIONS {(rr:(real^N->bool)->real^3->bool) r INTER
                             IMAGE f1 (moi_s34_sd tt kk g) | g |
                             g IN moi_s34_simp kk (&1) /\ v IN g /\ g SUBSET r}` THEN
    ASM_CASES_TAC `(x:real^3) IN JR` THENL
     [UNDISCH_TAC `(x:real^3) IN JR` THEN EXPAND_TAC "JR" THEN
      REWRITE_TAC[IN_UNION; UNIONS_GSPEC; IN_ELIM_THM] THEN STRIP_TAC THENL
       [USE_THEN "FH" MATCH_MP_TAC THEN
      MAP_EVERY EXISTS_TAC [`s:real^N->bool`; `r:real^N->bool`] THEN ASM_REWRITE_TAC[];
        USE_THEN "RH" MATCH_MP_TAC THEN EXISTS_TAC `r:real^N->bool` THEN
        EXISTS_TAC `g:real^N->bool` THEN ASM_REWRITE_TAC[]];
      EXISTS_TAC `(rr:(real^N->bool)->real^3->bool) r INTER
                  IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v) DIFF JR` THEN
      REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC MOI_S4H_DISK_OPEN THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC SUBSET_TRANS THEN
        EXISTS_TAC `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_bd tt kk)` THEN
        ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[IN_DIFF];
        USE_THEN "CW" (fun th -> MP_TAC(MP (SPEC `r:real^N->bool` th)
          (CONJ (ASSUME `(r:real^N->bool) IN moi_s34_simp kk (&3)`)
                (ASSUME `(v:real^N) IN r`)))) THEN
        SET_TAC[]]];
    (* x in a splitting disk D_g *)
    MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                  `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                  `dd:(real^N->bool)->real^3->bool`; `rr:(real^N->bool)->real^3->bool`;
                  `g:real^N->bool`] MOI_S4OT_RIM_SETUP) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(fun th -> let cs = CONJUNCTS th in ASSUME_TAC (el 0 cs)) THEN
    ASM_CASES_TAC
     `(x:real^3) IN IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g INTER moi_s34_bd tt kk)`
    THENL
     [ALL_TAC;
      EXISTS_TAC `IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g) DIFF
                  IMAGE f1 (moi_s34_sd tt kk g INTER moi_s34_bd tt kk)` THEN
      REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC MOI_S4H_DISK_OPEN THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC SUBSET_TRANS THEN
        EXISTS_TAC `UNIONS {IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g) | g |
                            g IN moi_s34_simp kk (&1) /\ (v:real^N) IN g}` THEN
        ASM_REWRITE_TAC[] THEN
        GEN_REWRITE_TAC I [SUBSET] THEN REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM] THEN
        X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN EXISTS_TAC `g:real^N->bool` THEN
        ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[IN_DIFF];
        USE_THEN "DW" (fun th -> MP_TAC(MP (SPEC `g:real^N->bool` th)
          (CONJ (ASSUME `(g:real^N->bool) IN moi_s34_simp kk (&1)`)
                (ASSUME `(v:real^N) IN g`)))) THEN
        SET_TAC[]]] THEN
    (* x on the rim of g *)
    ASM_CASES_TAC `?r. r IN moi_s34_simp kk (&3) /\ (g:real^N->bool) SUBSET r /\
                       (x:real^3) IN (rr:(real^N->bool)->real^3->bool) r` THENL
     [FIRST_X_ASSUM(X_CHOOSE_THEN `r:real^N->bool` STRIP_ASSUME_TAC) THEN
      USE_THEN "RH" MATCH_MP_TAC THEN
      MAP_EVERY EXISTS_TAC [`r:real^N->bool`; `g:real^N->bool`] THEN
      ASM_REWRITE_TAC[IN_INTER] THEN
      MAP_EVERY UNDISCH_TAC [`(v:real^N) IN g`; `(g:real^N->bool) SUBSET r`] THEN SET_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC(TAUT `F ==> p`) THEN
    ASM_CASES_TAC `(g:real^N->bool) SUBSET complex_boundary kk` THENL
     [SUBGOAL_THEN `(x:real^3) IN moi_s34_oarc tt kk (f1:real^N->real^3) rr g` ASSUME_TAC THENL
       [REWRITE_TAC[moi_s34_oarc] THEN MATCH_MP_TAC(REWRITE_RULE[SUBSET] CLOSURE_SUBSET) THEN
        ASM_REWRITE_TAC[IN_DIFF; UNIONS_GSPEC; IN_ELIM_THM] THEN
        UNDISCH_TAC `~(?r. r IN moi_s34_simp kk (&3) /\ (g:real^N->bool) SUBSET r /\
                           (x:real^3) IN (rr:(real^N->bool)->real^3->bool) r)` THEN
        MESON_TAC[];
        ALL_TAC] THEN
      USE_THEN "XJ" (MP_TAC o SPEC `g:real^N->bool` o
        REWRITE_RULE[UNIONS_GSPEC; IN_ELIM_THM; NOT_EXISTS_THM] o CONJUNCT2 o
        REWRITE_RULE[IN_UNION; DE_MORGAN_THM]) THEN
      ASM_REWRITE_TAC[];
      UNDISCH_TAC `moi_s34_resid tt kk (f1:real^N->real^3) car dd rr` THEN
      REWRITE_TAC[moi_s34_resid] THEN
      DISCH_THEN(MP_TAC o SPEC `g:real^N->bool` o last o CONJUNCTS) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o SPEC `x:real^3` o GEN_REWRITE_RULE I [SUBSET]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM] THEN
      UNDISCH_TAC `~(?r. r IN moi_s34_simp kk (&3) /\ (g:real^N->bool) SUBSET r /\
                         (x:real^3) IN (rr:(real^N->bool)->real^3->bool) r)` THEN
      MESON_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* The vertex clause.  With W = the union of the patches X_r and            *)
(* the splitting disks D_g at v and T = A_v minus the tetra balls at v,     *)
(* Sigma_v = W UNION T, T meets W only in outer arcs, inner points of the   *)
(* boundary face arcs are limits of Sigma_v minus W, and the outer patch    *)
(* closure T is the 2-cell bounded by J_v (MOI_S4O_SPHERE_PIECE); with the  *)
(* edge clause this gives TOUTER.                                            *)
(* ------------------------------------------------------------------------- *)

(* A cell is the closure of its interior, which is nonempty. *)

let MOI_S4OT_CELL_INNER = prove
 (`!n (c:real^N->bool) b.
     pl_cell_with_boundary n c b ==> c SUBSET closure (c DIFF b) /\ ~(c DIFF b = {})`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4G_CELL_FACTS) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MOI_S4H_CELL_BD_CLOSURE) THEN
  SUBGOAL_THEN `(c:real^N->bool) SUBSET closure (c DIFF b)` ASSUME_TAC THENL
   [MP_TAC(ISPEC `(c:real^N->bool) DIFF b` CLOSURE_SUBSET) THEN
    UNDISCH_TAC `(b:real^N->bool) SUBSET closure (c DIFF b)` THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  UNDISCH_TAC `(c:real^N->bool) SUBSET closure (c DIFF b)` THEN
  ASM_REWRITE_TAC[CLOSURE_EMPTY; SUBSET_EMPTY]);;

(* A boundary point of a 2-cell in a 2-sphere that lies in no other member  *)
(* of a finite family of closed sets is a limit of points off the family.   *)

let MOI_S4OT_BD_LIMIT = prove
 (`!(sg:real^3->bool) d b cs x.
     pl_sphere 2 sg /\ pl_cell_with_boundary 2 d b /\ d SUBSET sg /\
     FINITE cs /\ (!c. c IN cs ==> closed c) /\ x IN b /\
     (!c. c IN cs /\ x IN c ==> c = d)
     ==> x IN closure (sg DIFF UNIONS cs)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4G_CELL_FACTS) THEN
  SUBGOAL_THEN `closed (UNIONS {c | c IN cs /\ ~(c = d:real^3->bool)})` ASSUME_TAC THENL
   [MATCH_MP_TAC CLOSED_UNIONS THEN CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `cs:(real^3->bool)->bool` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((x:real^3) IN UNIONS {c | c IN cs /\ ~(c = d:real^3->bool)})` ASSUME_TAC THENL
   [REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^3) IN sg` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`(x:real^3) IN b`; `(b:real^3->bool) SUBSET d`;
                           `(d:real^3->bool) SUBSET sg`] THEN SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC(SET_RULE `!x:real^3 a b. a SUBSET b /\ x IN a ==> x IN b`) THEN
  EXISTS_TAC `closure (sg DIFF (d UNION UNIONS {c | c IN cs /\ ~(c = d:real^3->bool)}))` THEN
  CONJ_TAC THENL [MATCH_MP_TAC SUBSET_CLOSURE THEN SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[CLOSURE_APPROACHABLE] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`sg:real^3->bool`; `d:real^3->bool`; `b:real^3->bool`; `x:real^3`]
    MOI_S4L_CELL_BOUNDARY_NOT_OPEN) THEN
  ASM_REWRITE_TAC[NOT_EXISTS_THM] THEN
  DISCH_THEN(MP_TAC o SPEC `sg INTER (ball(x:real^3,e) INTER
                            ((:real^3) DIFF UNIONS {c | c IN cs /\ ~(c = d:real^3->bool)}))`) THEN
  SUBGOAL_THEN `open_in (subtopology euclidean sg)
                  (sg INTER (ball(x:real^3,e) INTER
                   ((:real^3) DIFF UNIONS {c | c IN cs /\ ~(c = d:real^3->bool)})))`
  (fun th -> REWRITE_TAC[th]) THENL
   [MATCH_MP_TAC OPEN_IN_OPEN_INTER THEN MATCH_MP_TAC OPEN_INTER THEN
    REWRITE_TAC[OPEN_BALL] THEN ASM_REWRITE_TAC[GSYM closed];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[IN_INTER; CENTRE_IN_BALL; IN_DIFF; IN_UNIV] THEN
  REWRITE_TAC[SUBSET; IN_INTER; IN_BALL; IN_DIFF; IN_UNIV; IN_UNION; NOT_FORALL_THM; NOT_IMP] THEN
  MESON_TAC[DIST_SYM]);;

(* A 2-cell of a 2-sphere disjoint from t is not in the closure of t. *)

let MOI_S4OT_CELL_NOT_IN_CLOSURE = prove
 (`!(sg:real^3->bool) d b t.
     pl_sphere 2 sg /\ pl_cell_with_boundary 2 d b /\ d SUBSET sg /\ t SUBSET sg /\
     DISJOINT d t
     ==> ~(sg SUBSET closure t)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC o
    REWRITE_RULE[GSYM MEMBER_NOT_EMPTY; IN_DIFF] o CONJUNCT2 o MATCH_MP MOI_S4OT_CELL_INNER) THEN
  MP_TAC(ISPECL [`sg:real^3->bool`; `d:real^3->bool`; `b:real^3->bool`] MOI_S4H_DISK_OPEN) THEN
  ASM_REWRITE_TAC[OPEN_IN_OPEN] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^3->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`u:real^3->bool`; `t:real^3->bool`] OPEN_INTER_CLOSURE_SUBSET) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(u:real^3->bool) INTER t = {}` SUBST1_TAC THENL
   [UNDISCH_TAC `(d:real^3->bool) DIFF b = sg INTER u` THEN
    MAP_EVERY UNDISCH_TAC [`DISJOINT (d:real^3->bool) t`; `(t:real^3->bool) SUBSET sg`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[CLOSURE_EMPTY; SUBSET_EMPTY] THEN
  UNDISCH_TAC `(d:real^3->bool) DIFF b = sg INTER u` THEN
  MAP_EVERY UNDISCH_TAC [`(y:real^3) IN d`; `~((y:real^3) IN b)`;
                         `(sg:real^3->bool) SUBSET closure t`] THEN
  SET_TAC[]);;

(* W, the union of the patches and the splitting disks at v, and T, A_v     *)
(* minus the tetra balls at v: W SUBSET Sigma_v SUBSET W UNION T, T meets   *)
(* W only in the outer arcs, W is closed and contains J_v.                   *)

let MOI_S4OT_W_FACTS = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car dd rr v.
     moi_s34_tube tt kk /\ moi_s34_frame tt kk h ep f1 car /\
     moi_s34_fdisk tt kk f1 car dd /\ moi_s34_resid tt kk f1 car dd rr /\ {v} IN kk
     ==> UNIONS {rr r INTER IMAGE f1 (moi_s34_vb tt kk v) | r |
                 r IN moi_s34_simp kk (&3) /\ v IN r} UNION
         UNIONS {IMAGE f1 (moi_s34_sd tt kk g) | g | g IN moi_s34_simp kk (&1) /\ v IN g}
         SUBSET frontier (IMAGE f1 (moi_s34_vb tt kk v)) /\
         frontier (IMAGE f1 (moi_s34_vb tt kk v)) SUBSET
         (UNIONS {rr r INTER IMAGE f1 (moi_s34_vb tt kk v) | r |
                  r IN moi_s34_simp kk (&3) /\ v IN r} UNION
          UNIONS {IMAGE f1 (moi_s34_sd tt kk g) | g | g IN moi_s34_simp kk (&1) /\ v IN g}) UNION
         (IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_bd tt kk) DIFF
          UNIONS {rr r | r | r IN moi_s34_simp kk (&3) /\ v IN r}) /\
         (IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_bd tt kk) DIFF
          UNIONS {rr r | r | r IN moi_s34_simp kk (&3) /\ v IN r}) INTER
         (UNIONS {rr r INTER IMAGE f1 (moi_s34_vb tt kk v) | r |
                  r IN moi_s34_simp kk (&3) /\ v IN r} UNION
          UNIONS {IMAGE f1 (moi_s34_sd tt kk g) | g | g IN moi_s34_simp kk (&1) /\ v IN g})
         SUBSET UNIONS {moi_s34_oarc tt kk f1 rr g | g |
                        g IN moi_s34_simp kk (&1) /\ v IN g /\ g SUBSET complex_boundary kk} /\
         closed (UNIONS {rr r INTER IMAGE f1 (moi_s34_vb tt kk v) | r |
                         r IN moi_s34_simp kk (&3) /\ v IN r} UNION
                 UNIONS {IMAGE f1 (moi_s34_sd tt kk g) | g |
                         g IN moi_s34_simp kk (&1) /\ v IN g}) /\
         UNIONS {dd s INTER IMAGE f1 (moi_s34_vb tt kk v) | s |
                 s IN moi_s34_simp kk (&2) /\ v IN s /\ s SUBSET complex_boundary kk} UNION
         UNIONS {moi_s34_oarc tt kk f1 rr g | g |
                 g IN moi_s34_simp kk (&1) /\ v IN g /\ g SUBSET complex_boundary kk}
         SUBSET UNIONS {rr r INTER IMAGE f1 (moi_s34_vb tt kk v) | r |
                        r IN moi_s34_simp kk (&3) /\ v IN r} UNION
                UNIONS {IMAGE f1 (moi_s34_sd tt kk g) | g | g IN moi_s34_simp kk (&1) /\ v IN g}`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                `dd:(real^N->bool)->real^3->bool`; `rr:(real^N->bool)->real^3->bool`;
                `v:real^N`] MOI_S4OT_PATCH_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> let cs = CONJUNCTS th in
    LABEL_TAC "SIG" (el 1 cs) THEN ASSUME_TAC (el 3 cs) THEN ASSUME_TAC (el 4 cs) THEN
    LABEL_TAC "PX" (el 5 cs) THEN LABEL_TAC "RG" (el 7 cs)) THEN
  SUBGOAL_THEN `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_bd tt kk) SUBSET
                IMAGE f1 (moi_s34_vb tt kk v)` (LABEL_TAC "AC") THENL
   [MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[INTER_SUBSET]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [(* W SUBSET Sigma_v *)
    USE_THEN "SIG" SUBST1_TAC THEN
    REWRITE_TAC[UNION_SUBSET; UNIONS_SUBSET; FORALL_IN_GSPEC] THEN CONJ_TAC THENL
     [X_GEN_TAC `r:real^N->bool` THEN STRIP_TAC THEN
      USE_THEN "PX" (fun th -> MP_TAC(MP (SPEC `r:real^N->bool` th)
        (CONJ (ASSUME `(r:real^N->bool) IN moi_s34_simp kk (&3)`) (ASSUME `(v:real^N) IN r`)))) THEN
      DISCH_THEN(MP_TAC o CONJUNCT1) THEN SET_TAC[];
      X_GEN_TAC `g:real^N->bool` THEN STRIP_TAC THEN
      MATCH_MP_TAC(SET_RULE `!a b c:real^3->bool. a SUBSET c ==> a SUBSET b UNION c`) THEN
      GEN_REWRITE_TAC I [SUBSET] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
      REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM] THEN EXISTS_TAC `g:real^N->bool` THEN
      ASM_REWRITE_TAC[]];
    (* Sigma_v SUBSET W UNION T *)
    USE_THEN "SIG" SUBST1_TAC THEN
    GEN_REWRITE_TAC I [SUBSET] THEN X_GEN_TAC `y:real^3` THEN
    USE_THEN "AC" (MP_TAC o SPEC `y:real^3` o GEN_REWRITE_RULE I [SUBSET]) THEN
    REWRITE_TAC[IN_UNION; IN_DIFF; UNIONS_GSPEC; IN_ELIM_THM; IN_INTER] THEN
    MESON_TAC[];
    (* T INTER W SUBSET the outer arcs *)
    GEN_REWRITE_TAC I [SUBSET] THEN X_GEN_TAC `y:real^3` THEN
    REWRITE_TAC[IN_INTER; IN_DIFF; IN_UNION] THEN
    REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "NR")) MP_TAC) THEN
    DISCH_THEN(DISJ_CASES_THEN (X_CHOOSE_THEN `q:real^N->bool` STRIP_ASSUME_TAC)) THENL
     [REMOVE_THEN "NR" (MP_TAC o SPEC `q:real^N->bool` o REWRITE_RULE[NOT_EXISTS_THM]) THEN
      UNDISCH_TAC `(y:real^3) IN (rr:(real^N->bool)->real^3->bool) q INTER
                   IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v)` THEN
      ASM_REWRITE_TAC[IN_INTER] THEN MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `(y:real^3) IN IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk q INTER moi_s34_bd tt kk)`
    ASSUME_TAC THENL
     [USE_THEN "RG" (fun th -> MP_TAC(MP (SPEC `q:real^N->bool` th)
        (CONJ (ASSUME `(q:real^N->bool) IN moi_s34_simp kk (&1)`) (ASSUME `(v:real^N) IN q`)))) THEN
      MAP_EVERY UNDISCH_TAC
       [`(y:real^3) IN IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk q)`;
        `(y:real^3) IN IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_bd tt kk)`] THEN
      SET_TAC[];
      ALL_TAC] THEN
    ASM_CASES_TAC `(q:real^N->bool) SUBSET complex_boundary kk` THENL
     [EXISTS_TAC `q:real^N->bool` THEN ASM_REWRITE_TAC[moi_s34_oarc] THEN
      MATCH_MP_TAC(REWRITE_RULE[SUBSET] CLOSURE_SUBSET) THEN
      ASM_REWRITE_TAC[IN_DIFF; UNIONS_GSPEC; IN_ELIM_THM] THEN
      DISCH_THEN(X_CHOOSE_THEN `r:real^N->bool` STRIP_ASSUME_TAC) THEN
      REMOVE_THEN "NR" (MP_TAC o SPEC `r:real^N->bool` o REWRITE_RULE[NOT_EXISTS_THM]) THEN
      ASM_REWRITE_TAC[] THEN
      MAP_EVERY UNDISCH_TAC [`(v:real^N) IN q`; `(q:real^N->bool) SUBSET r`] THEN SET_TAC[];
      MATCH_MP_TAC(TAUT `F ==> p`) THEN
      UNDISCH_TAC `moi_s34_resid tt kk (f1:real^N->real^3) car dd rr` THEN
      REWRITE_TAC[moi_s34_resid] THEN
      DISCH_THEN(MP_TAC o SPEC `q:real^N->bool` o last o CONJUNCTS) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o SPEC `y:real^3` o GEN_REWRITE_RULE I [SUBSET]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM] THEN
      DISCH_THEN(X_CHOOSE_THEN `r:real^N->bool` STRIP_ASSUME_TAC) THEN
      REMOVE_THEN "NR" (MP_TAC o SPEC `r:real^N->bool` o REWRITE_RULE[NOT_EXISTS_THM]) THEN
      ASM_REWRITE_TAC[] THEN
      MAP_EVERY UNDISCH_TAC [`(v:real^N) IN q`; `(q:real^N->bool) SUBSET r`] THEN SET_TAC[]];
    (* W is closed *)
    MATCH_MP_TAC CLOSED_UNION THEN CONJ_TAC THEN MATCH_MP_TAC CLOSED_UNIONS THEN
    REWRITE_TAC[FORALL_IN_GSPEC] THEN CONJ_TAC THENL
     [ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN MATCH_MP_TAC FINITE_IMAGE THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `r:real^N->bool` THEN STRIP_TAC THEN MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
      USE_THEN "PX" (fun th -> MP_TAC(MP (SPEC `r:real^N->bool` th)
        (CONJ (ASSUME `(r:real^N->bool) IN moi_s34_simp kk (&3)`) (ASSUME `(v:real^N) IN r`)))) THEN
      DISCH_THEN(MP_TAC o MATCH_MP MOI_S4G_CELL_FACTS o CONJUNCT2) THEN SIMP_TAC[];
      ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN MATCH_MP_TAC FINITE_IMAGE THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `g:real^N->bool` THEN STRIP_TAC THEN MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
      MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                    `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                    `dd:(real^N->bool)->real^3->bool`; `rr:(real^N->bool)->real^3->bool`;
                    `g:real^N->bool`] MOI_S4OT_RIM_SETUP) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]]];
    (* J_v SUBSET W *)
    REWRITE_TAC[UNION_SUBSET; UNIONS_SUBSET; FORALL_IN_GSPEC] THEN CONJ_TAC THENL
     [X_GEN_TAC `s:real^N->bool` THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `s:real^N->bool`]
        MOI_S4OT_FACE_TETS) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `r:real^N->bool` (MP_TAC o SPEC `r:real^N->bool` o
        GEN_REWRITE_RULE I [EXTENSION])) THEN
      REWRITE_TAC[IN_ELIM_THM; IN_SING] THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `f1:real^N->real^3`;
                     `car:(real^N->bool)->real^3->bool`; `dd:(real^N->bool)->real^3->bool`;
                     `rr:(real^N->bool)->real^3->bool`; `r:real^N->bool`] MOI_S4OT_RR_FACTS) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o SPEC `s:real^N->bool` o el 6 o CONJUNCTS) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN DISCH_TAC THEN
      MATCH_MP_TAC(SET_RULE `!a b c:real^3->bool. a SUBSET b ==> a SUBSET b UNION c`) THEN
      GEN_REWRITE_TAC I [SUBSET] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
      REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM] THEN EXISTS_TAC `r:real^N->bool` THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MAP_EVERY UNDISCH_TAC [`(v:real^N) IN s`; `(s:real^N->bool) SUBSET r`] THEN SET_TAC[];
        MAP_EVERY UNDISCH_TAC
         [`(y:real^3) IN (dd:(real^N->bool)->real^3->bool) s INTER
                         IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v)`;
          `(dd:(real^N->bool)->real^3->bool) s SUBSET
           (rr:(real^N->bool)->real^3->bool) r`] THEN SET_TAC[]];
      X_GEN_TAC `g:real^N->bool` THEN STRIP_TAC THEN
      MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                    `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                    `dd:(real^N->bool)->real^3->bool`; `rr:(real^N->bool)->real^3->bool`;
                    `v:real^N`] MOI_S4OT_JV_FACTS) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o SPEC `g:real^N->bool` o last o CONJUNCTS) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o CONJUNCT2) THEN DISCH_TAC THEN
      MATCH_MP_TAC(SET_RULE `!a b c:real^3->bool. a SUBSET c ==> a SUBSET b UNION c`) THEN
      GEN_REWRITE_TAC I [SUBSET] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
      REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM] THEN EXISTS_TAC `g:real^N->bool` THEN
      ASM_REWRITE_TAC[] THEN
      MAP_EVERY UNDISCH_TAC
       [`(y:real^3) IN moi_s34_oarc tt kk (f1:real^N->real^3) rr g`;
        `moi_s34_oarc tt kk (f1:real^N->real^3) rr g SUBSET IMAGE f1 (moi_s34_sd tt kk g)`] THEN
      SET_TAC[]]]);;

(* An inner point of a boundary face arc at v is a limit of Sigma_v minus W *)
(* (it lies only on the patch of the unique 3-simplex at its face).          *)

let MOI_S4OT_BFACE_LIMIT = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car dd rr v s y.
     moi_s34_tube tt kk /\ moi_s34_frame tt kk h ep f1 car /\
     moi_s34_fdisk tt kk f1 car dd /\ moi_s34_resid tt kk f1 car dd rr /\ {v} IN kk /\
     s IN moi_s34_simp kk (&2) /\ v IN s /\ s SUBSET complex_boundary kk /\
     y IN dd s INTER IMAGE f1 (moi_s34_vb tt kk v) /\
     ~(y IN UNIONS {dd s INTER IMAGE f1 (moi_s34_sd tt kk g) | g |
                    g IN moi_s34_simp kk (&1) /\ v IN g /\ g SUBSET s})
     ==> y IN closure (frontier (IMAGE f1 (moi_s34_vb tt kk v)) DIFF
                       (UNIONS {rr r INTER IMAGE f1 (moi_s34_vb tt kk v) | r |
                                r IN moi_s34_simp kk (&3) /\ v IN r} UNION
                        UNIONS {IMAGE f1 (moi_s34_sd tt kk g) | g |
                                g IN moi_s34_simp kk (&1) /\ v IN g}))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> let cs = CONJUNCTS th in
    MAP_EVERY ASSUME_TAC (butlast cs) THEN LABEL_TAC "YE" (last cs)) THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `s:real^N->bool`]
    MOI_S4OT_FACE_TETS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real^N->bool` (LABEL_TAC "UR" o GEN_REWRITE_RULE I [EXTENSION])) THEN
  SUBGOAL_THEN `(r:real^N->bool) IN moi_s34_simp kk (&3) /\ s SUBSET r` STRIP_ASSUME_TAC THENL
   [USE_THEN "UR" (MP_TAC o SPEC `r:real^N->bool`) THEN REWRITE_TAC[IN_ELIM_THM; IN_SING];
    ALL_TAC] THEN
  SUBGOAL_THEN `(v:real^N) IN r` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`(v:real^N) IN s`; `(s:real^N->bool) SUBSET r`] THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                `dd:(real^N->bool)->real^3->bool`; `rr:(real^N->bool)->real^3->bool`;
                `v:real^N`] MOI_S4OT_PATCH_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> let cs = CONJUNCTS th in
    ASSUME_TAC (el 0 cs) THEN
    ASSUME_TAC (CONJUNCT1 (MATCH_MP (SET_RULE
      `!f a b:real^3->bool. f = a UNION b ==> a SUBSET f /\ b SUBSET f`) (el 1 cs))) THEN
    ASSUME_TAC (el 3 cs) THEN ASSUME_TAC (el 4 cs) THEN LABEL_TAC "PX" (el 5 cs)) THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `dd:(real^N->bool)->real^3->bool`;
                 `rr:(real^N->bool)->real^3->bool`; `r:real^N->bool`] MOI_S4OT_RR_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> let cs = CONJUNCTS th in
    LABEL_TAC "DDR" (el 6 cs) THEN LABEL_TAC "RR2" (el 7 cs)) THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                `dd:(real^N->bool)->real^3->bool`; `rr:(real^N->bool)->real^3->bool`;
                `v:real^N`] MOI_S4OT_JV_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> let cs = CONJUNCTS th in
    LABEL_TAC "DG0" (el 1 cs) THEN LABEL_TAC "DD0" (el 2 cs)) THEN
  SUBGOAL_THEN `(y:real^3) IN (rr:(real^N->bool)->real^3->bool) r` ASSUME_TAC THENL
   [USE_THEN "DDR" (fun th -> MP_TAC(MP (SPEC `s:real^N->bool` th)
      (CONJ (ASSUME `(s:real^N->bool) IN moi_s34_simp kk (&2)`)
            (ASSUME `(s:real^N->bool) SUBSET r`)))) THEN
    UNDISCH_TAC `(y:real^3) IN (dd:(real^N->bool)->real^3->bool) s INTER
                 IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v)` THEN SET_TAC[];
    ALL_TAC] THEN
  USE_THEN "PX" (fun th -> MP_TAC(MP (SPEC `r:real^N->bool` th)
    (CONJ (ASSUME `(r:real^N->bool) IN moi_s34_simp kk (&3)`) (ASSUME `(v:real^N) IN r`)))) THEN
  STRIP_TAC THEN
  REWRITE_TAC[GSYM UNIONS_UNION] THEN
  MATCH_MP_TAC MOI_S4OT_BD_LIMIT THEN
  MAP_EVERY EXISTS_TAC
   [`(rr:(real^N->bool)->real^3->bool) r INTER IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v)`;
    `UNIONS {(dd:(real^N->bool)->real^3->bool) s INTER
             IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v) | s |
             s IN moi_s34_simp kk (&2) /\ (v:real^N) IN s /\ s SUBSET r} UNION
     UNIONS {(rr:(real^N->bool)->real^3->bool) r INTER IMAGE f1 (moi_s34_sd tt kk g) | g |
             g IN moi_s34_simp kk (&1) /\ v IN g /\ g SUBSET r}`] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_bd tt kk)` THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[FINITE_UNION] THEN CONJ_TAC THEN ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
    MATCH_MP_TAC FINITE_IMAGE THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[FORALL_IN_UNION; FORALL_IN_GSPEC] THEN CONJ_TAC THENL
     [X_GEN_TAC `q:real^N->bool` THEN STRIP_TAC THEN MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
      USE_THEN "PX" (fun th -> MP_TAC(MP (SPEC `q:real^N->bool` th)
        (CONJ (ASSUME `(q:real^N->bool) IN moi_s34_simp kk (&3)`) (ASSUME `(v:real^N) IN q`)))) THEN
      DISCH_THEN(MP_TAC o MATCH_MP MOI_S4G_CELL_FACTS o CONJUNCT2) THEN SIMP_TAC[];
      X_GEN_TAC `g:real^N->bool` THEN STRIP_TAC THEN MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
      MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                    `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                    `dd:(real^N->bool)->real^3->bool`; `rr:(real^N->bool)->real^3->bool`;
                    `g:real^N->bool`] MOI_S4OT_RIM_SETUP) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]]];
    REWRITE_TAC[IN_UNION; UNIONS_GSPEC; IN_ELIM_THM] THEN DISJ1_TAC THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[IMP_CONJ; FORALL_IN_UNION; FORALL_IN_GSPEC] THEN CONJ_TAC THENL
     [X_GEN_TAC `q:real^N->bool` THEN REWRITE_TAC[IN_INTER] THEN REPEAT STRIP_TAC THEN
      ASM_CASES_TAC `q:real^N->bool = r` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(TAUT `F ==> p`) THEN
      USE_THEN "RR2" (MP_TAC o SPEC `q:real^N->bool`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o SPEC `y:real^3` o GEN_REWRITE_RULE I [EXTENSION]) THEN
      ASM_REWRITE_TAC[IN_INTER; UNIONS_GSPEC; IN_ELIM_THM] THEN
      DISCH_THEN(X_CHOOSE_THEN `s':real^N->bool` STRIP_ASSUME_TAC) THEN
      ASM_CASES_TAC `s':real^N->bool = s` THENL
       [UNDISCH_TAC `(s':real^N->bool) SUBSET q` THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
        USE_THEN "UR" (MP_TAC o SPEC `q:real^N->bool`) THEN
        REWRITE_TAC[IN_ELIM_THM; IN_SING] THEN ASM_REWRITE_TAC[];
        USE_THEN "DD0" (MP_TAC o SPECL [`s:real^N->bool`; `s':real^N->bool`]) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        MAP_EVERY UNDISCH_TAC
         [`(y:real^3) IN (dd:(real^N->bool)->real^3->bool) s'`;
          `(y:real^3) IN (dd:(real^N->bool)->real^3->bool) s INTER
                         IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v)`] THEN
        SET_TAC[]];
      X_GEN_TAC `g:real^N->bool` THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC(TAUT `F ==> p`) THEN
      ASM_CASES_TAC `(g:real^N->bool) SUBSET s` THENL
       [USE_THEN "YE" (MP_TAC o SPEC `g:real^N->bool` o
          REWRITE_RULE[UNIONS_GSPEC; IN_ELIM_THM; NOT_EXISTS_THM]) THEN
        ASM_REWRITE_TAC[IN_INTER] THEN
        UNDISCH_TAC `(y:real^3) IN (dd:(real^N->bool)->real^3->bool) s INTER
                     IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v)` THEN
        SET_TAC[];
        USE_THEN "DG0" (MP_TAC o SPECL [`s:real^N->bool`; `g:real^N->bool`]) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        MAP_EVERY UNDISCH_TAC
         [`(y:real^3) IN IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g)`;
          `(y:real^3) IN (dd:(real^N->bool)->real^3->bool) s INTER
                         IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v)`] THEN
        SET_TAC[]]]]);;

(* The vertex clause: at a boundary vertex v the outer patch is the 2-cell  *)
(* of Sigma_v bounded by J_v.                                                *)

let MOI_S4OT_VERTEX_CLAUSE = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car dd rr v.
     moi_s34_tube tt kk /\ moi_s34_frame tt kk h ep f1 car /\
     moi_s34_fdisk tt kk f1 car dd /\ moi_s34_resid tt kk f1 car dd rr /\
     {v} IN kk /\ v IN complex_boundary kk
     ==> pl_cell_with_boundary 2 (moi_s34_opatch tt kk f1 rr v)
           (UNIONS {dd s INTER IMAGE f1 (moi_s34_vb tt kk v) | s |
                    s IN moi_s34_simp kk (&2) /\ v IN s /\ s SUBSET complex_boundary kk} UNION
            UNIONS {moi_s34_oarc tt kk f1 rr g | g |
                    g IN moi_s34_simp kk (&1) /\ v IN g /\ g SUBSET complex_boundary kk})`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  (* lemma instances at v, taken before the abbreviations *)
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                `dd:(real^N->bool)->real^3->bool`; `rr:(real^N->bool)->real^3->bool`;
                `v:real^N`] MOI_S4OT_PATCH_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> let cs = CONJUNCTS th in
    ASSUME_TAC (el 0 cs) THEN
    ASSUME_TAC (CONJUNCT1 (MATCH_MP (SET_RULE
      `!f a b:real^3->bool. f = a UNION b ==> a SUBSET f /\ b SUBSET f`) (el 1 cs))) THEN
    LABEL_TAC "PX" (el 5 cs) THEN LABEL_TAC "RG" (el 7 cs)) THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                `dd:(real^N->bool)->real^3->bool`; `rr:(real^N->bool)->real^3->bool`;
                `v:real^N`] MOI_S4OT_W_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> let cs = CONJUNCTS th in
    LABEL_TAC "W0" (el 0 cs) THEN LABEL_TAC "W1" (el 1 cs) THEN LABEL_TAC "W2" (el 2 cs) THEN
    LABEL_TAC "W3" (el 3 cs) THEN LABEL_TAC "W4" (el 4 cs)) THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                `dd:(real^N->bool)->real^3->bool`; `rr:(real^N->bool)->real^3->bool`;
                `v:real^N`] MOI_S4OT_JV_CIRCLE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                `dd:(real^N->bool)->real^3->bool`; `rr:(real^N->bool)->real^3->bool`;
                `v:real^N`] MOI_S4OT_JV_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(LABEL_TAC "FA" o el 5 o CONJUNCTS) THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                `dd:(real^N->bool)->real^3->bool`; `rr:(real^N->bool)->real^3->bool`;
                `v:real^N`] MOI_S4OT_LOCAL_COVER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "LC") THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                `dd:(real^N->bool)->real^3->bool`; `rr:(real^N->bool)->real^3->bool`;
                `v:real^N`] MOI_S4OT_BFACE_LIMIT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "BF") THEN
  SUBGOAL_THEN
   `!r g. r IN moi_s34_simp kk (&3) /\ g IN moi_s34_simp kk (&1) /\ ~(g SUBSET r)
          ==> (rr:(real^N->bool)->real^3->bool) r INTER
              IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g) = {}`
  (LABEL_TAC "RRD") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `f1:real^N->real^3`;
                   `car:(real^N->bool)->real^3->bool`; `dd:(real^N->bool)->real^3->bool`;
                   `rr:(real^N->bool)->real^3->bool`; `r:real^N->bool`] MOI_S4OT_RR_FACTS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `g:real^N->bool` o last o CONJUNCTS) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the abbreviations *)
  REWRITE_TAC[moi_s34_opatch] THEN
  ABBREV_TAC `Sg = frontier (IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v))` THEN
  ABBREV_TAC
   `J = UNIONS {(dd:(real^N->bool)->real^3->bool) s INTER
                IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v) | s |
                s IN moi_s34_simp kk (&2) /\ (v:real^N) IN s /\ s SUBSET complex_boundary kk} UNION
        UNIONS {moi_s34_oarc tt kk f1 rr g | g |
                g IN moi_s34_simp kk (&1) /\ v IN g /\ g SUBSET complex_boundary kk}` THEN
  ABBREV_TAC
   `W = UNIONS {(rr:(real^N->bool)->real^3->bool) r INTER
                IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v) | r |
                r IN moi_s34_simp kk (&3) /\ (v:real^N) IN r} UNION
        UNIONS {IMAGE f1 (moi_s34_sd tt kk g) | g | g IN moi_s34_simp kk (&1) /\ v IN g}` THEN
  ABBREV_TAC
   `Tv = IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_bd tt kk) DIFF
         UNIONS {(rr:(real^N->bool)->real^3->bool) r | r |
                 r IN moi_s34_simp kk (&3) /\ (v:real^N) IN r}` THEN
  SUBGOAL_THEN `(Tv:real^3->bool) SUBSET Sg` ASSUME_TAC THENL
   [EXPAND_TAC "Tv" THEN
    UNDISCH_TAC
     `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_bd tt kk) SUBSET Sg` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z r. z IN Tv /\ r IN moi_s34_simp kk (&3) /\ (v:real^N) IN r
                      ==> ~(z IN (rr:(real^N->bool)->real^3->bool) r)` (LABEL_TAC "TR") THENL
   [EXPAND_TAC "Tv" THEN REWRITE_TAC[IN_DIFF; UNIONS_GSPEC; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `UNIONS {moi_s34_oarc tt kk (f1:real^N->real^3) rr g | g |
            g IN moi_s34_simp kk (&1) /\ (v:real^N) IN g /\ g SUBSET complex_boundary kk}
    SUBSET J` ASSUME_TAC THENL
   [EXPAND_TAC "J" THEN REWRITE_TAC[SUBSET_UNION]; ALL_TAC] THEN
  SUBGOAL_THEN `(Tv:real^3->bool) INTER W SUBSET J` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `UNIONS {moi_s34_oarc tt kk (f1:real^N->real^3) rr g | g |
                        g IN moi_s34_simp kk (&1) /\ (v:real^N) IN g /\
                        g SUBSET complex_boundary kk}` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `closed (J:real^3->bool)` ASSUME_TAC THENL
   [MP_TAC(ISPEC `J:real^3->bool` MOI_SLV_CIRCLE_CLOSED) THEN ASM_REWRITE_TAC[] THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_S4O_SPHERE_PIECE THEN EXISTS_TAC `Sg:real^3->bool` THEN
  REPEAT CONJ_TAC THENL
   [(* Sigma_v is a 2-sphere *)
    ASM_REWRITE_TAC[];
    (* J_v is a circle *)
    ASM_REWRITE_TAC[];
    (* J_v SUBSET the outer patch *)
    EXPAND_TAC "J" THEN REWRITE_TAC[UNION_SUBSET; UNIONS_SUBSET; FORALL_IN_GSPEC] THEN
    CONJ_TAC THENL
     [X_GEN_TAC `s:real^N->bool` THEN STRIP_TAC THEN
      USE_THEN "FA" (fun th -> MP_TAC(MP (SPEC `s:real^N->bool` th)
        (CONJ (ASSUME `(s:real^N->bool) IN moi_s34_simp kk (&2)`) (ASSUME `(v:real^N) IN s`)))) THEN
      DISCH_THEN(MP_TAC o CONJUNCT1 o MATCH_MP MOI_S4OT_CELL_INNER) THEN
      MATCH_MP_TAC(SET_RULE `!a b c:real^3->bool. b SUBSET c ==> a SUBSET b ==> a SUBSET c`) THEN
      MATCH_MP_TAC CLOSURE_MINIMAL THEN REWRITE_TAC[CLOSED_CLOSURE] THEN
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `closure (Sg DIFF W:real^3->bool)` THEN
      CONJ_TAC THENL
       [GEN_REWRITE_TAC I [SUBSET] THEN X_GEN_TAC `y:real^3` THEN
        REWRITE_TAC[IN_DIFF] THEN STRIP_TAC THEN
        USE_THEN "BF" MATCH_MP_TAC THEN EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC SUBSET_CLOSURE THEN USE_THEN "W1" MP_TAC THEN SET_TAC[]];
      X_GEN_TAC `g:real^N->bool` THEN STRIP_TAC THEN
      REWRITE_TAC[moi_s34_oarc] THEN MATCH_MP_TAC SUBSET_CLOSURE THEN EXPAND_TAC "Tv" THEN
      USE_THEN "RG" (fun th -> MP_TAC(MP (SPEC `g:real^N->bool` th)
        (CONJ (ASSUME `(g:real^N->bool) IN moi_s34_simp kk (&1)`) (ASSUME `(v:real^N) IN g`)))) THEN
      DISCH_TAC THEN
      GEN_REWRITE_TAC I [SUBSET] THEN X_GEN_TAC `y:real^3` THEN
      REWRITE_TAC[IN_DIFF; UNIONS_GSPEC; IN_ELIM_THM; NOT_EXISTS_THM] THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "NG")) THEN CONJ_TAC THENL
       [UNDISCH_TAC `(y:real^3) IN IMAGE (f1:real^N->real^3)
                       (moi_s34_sd tt kk g INTER moi_s34_bd tt kk)` THEN
        UNDISCH_TAC `IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g) INTER
                     IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_bd tt kk) =
                     IMAGE f1 (moi_s34_sd tt kk g INTER moi_s34_bd tt kk)` THEN
        SET_TAC[];
        X_GEN_TAC `r:real^N->bool` THEN STRIP_TAC THEN
        ASM_CASES_TAC `(g:real^N->bool) SUBSET r` THENL
         [REMOVE_THEN "NG" (MP_TAC o SPEC `r:real^N->bool`) THEN ASM_REWRITE_TAC[];
          USE_THEN "RRD" (MP_TAC o SPECL [`r:real^N->bool`; `g:real^N->bool`]) THEN
          ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
          UNDISCH_TAC `(y:real^3) IN IMAGE (f1:real^N->real^3)
                         (moi_s34_sd tt kk g INTER moi_s34_bd tt kk)` THEN
          UNDISCH_TAC `(y:real^3) IN (rr:(real^N->bool)->real^3->bool) r` THEN
          MP_TAC(ISPECL [`f1:real^N->real^3`;
                         `moi_s34_sd (tt:(real^N->bool)->bool) kk g INTER moi_s34_bd tt kk`;
                         `moi_s34_sd (tt:(real^N->bool)->bool) kk g`] IMAGE_SUBSET) THEN
          REWRITE_TAC[INTER_SUBSET] THEN SET_TAC[]]]];
    (* the outer patch is inside Sigma_v *)
    MATCH_MP_TAC CLOSURE_MINIMAL THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "Sg" THEN REWRITE_TAC[FRONTIER_CLOSED];
    (* it is closed *)
    REWRITE_TAC[CLOSED_CLOSURE];
    (* closure (Sigma_v DIFF O_v) INTER O_v SUBSET J_v *)
    GEN_REWRITE_TAC I [SUBSET] THEN X_GEN_TAC `x:real^3` THEN REWRITE_TAC[IN_INTER] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `(x:real^3) IN W` ASSUME_TAC THENL
     [SUBGOAL_THEN `closure (Sg DIFF closure Tv) SUBSET (W:real^3->bool)` MP_TAC THENL
       [MATCH_MP_TAC CLOSURE_MINIMAL THEN USE_THEN "W3" (fun th -> REWRITE_TAC[th]) THEN
        MP_TAC(ISPEC `Tv:real^3->bool` CLOSURE_SUBSET) THEN USE_THEN "W1" MP_TAC THEN SET_TAC[];
        UNDISCH_TAC `(x:real^3) IN closure (Sg DIFF closure Tv)` THEN SET_TAC[]];
      ALL_TAC] THEN
    ASM_CASES_TAC `(x:real^3) IN J` THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    USE_THEN "LC" (fun th -> MP_TAC(MP (SPEC `x:real^3` th)
      (CONJ (ASSUME `(x:real^3) IN W`) (ASSUME `~((x:real^3) IN J)`)))) THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real^3->bool` (CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC)) THEN
    REWRITE_TAC[OPEN_IN_OPEN] THEN
    DISCH_THEN(X_CHOOSE_THEN `U:real^3->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(U:real^3->bool) INTER Tv SUBSET J` ASSUME_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       [`(Tv:real^3->bool) SUBSET Sg`; `(u:real^3->bool) = Sg INTER U`;
        `(u:real^3->bool) SUBSET W`; `(Tv:real^3->bool) INTER W SUBSET J`] THEN
      SET_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`U:real^3->bool`; `Tv:real^3->bool`] OPEN_INTER_CLOSURE_SUBSET) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`(U:real^3->bool) INTER Tv`; `J:real^3->bool`] CLOSURE_MINIMAL) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `(x:real^3) IN u` THEN UNDISCH_TAC `(u:real^3->bool) = Sg INTER U` THEN
    UNDISCH_TAC `(x:real^3) IN closure Tv` THEN SET_TAC[];
    (* the outer patch is not inside J_v *)
    MP_TAC(ISPECL [`kk:(real^N->bool)->bool`; `v:real^N`] MOI_S4OT_BVERTEX_FACE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
    USE_THEN "FA" (fun th -> MP_TAC(MP (SPEC `s:real^N->bool` th)
      (CONJ (ASSUME `(s:real^N->bool) IN moi_s34_simp kk (&2)`) (ASSUME `(v:real^N) IN s`)))) THEN
    DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC o
      REWRITE_RULE[GSYM MEMBER_NOT_EMPTY; IN_DIFF] o CONJUNCT2 o MATCH_MP MOI_S4OT_CELL_INNER) THEN
    SUBGOAL_THEN `(y:real^3) IN closure (Sg DIFF W)` MP_TAC THENL
     [USE_THEN "BF" MATCH_MP_TAC THEN EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_CASES_TAC `(Sg:real^3->bool) DIFF W = {}` THENL
     [ASM_REWRITE_TAC[CLOSURE_EMPTY; NOT_IN_EMPTY]; ALL_TAC] THEN
    DISCH_THEN(K ALL_TAC) THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `z:real^3` MP_TAC o REWRITE_RULE[GSYM MEMBER_NOT_EMPTY]) THEN
    REWRITE_TAC[IN_DIFF] THEN STRIP_TAC THEN
    REWRITE_TAC[SUBSET; NOT_FORALL_THM; NOT_IMP] THEN EXISTS_TAC `z:real^3` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC(REWRITE_RULE[SUBSET] CLOSURE_SUBSET) THEN
      USE_THEN "W1" MP_TAC THEN
      MAP_EVERY UNDISCH_TAC [`(z:real^3) IN Sg`; `~((z:real^3) IN W)`] THEN SET_TAC[];
      USE_THEN "W4" MP_TAC THEN UNDISCH_TAC `~((z:real^3) IN W)` THEN SET_TAC[]];
    (* Sigma_v is not inside the outer patch *)
    MP_TAC(ISPECL [`kk:(real^N->bool)->bool`; `v:real^N`] MOI_S4OT_BVERTEX_FACE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `s:real^N->bool`]
      MOI_S4OT_FACE_TETS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real^N->bool` (MP_TAC o SPEC `r:real^N->bool` o
      GEN_REWRITE_RULE I [EXTENSION])) THEN
    REWRITE_TAC[IN_ELIM_THM; IN_SING] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(v:real^N) IN r` ASSUME_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`(v:real^N) IN s`; `(s:real^N->bool) SUBSET r`] THEN SET_TAC[];
      ALL_TAC] THEN
    USE_THEN "PX" (fun th -> MP_TAC(MP (SPEC `r:real^N->bool` th)
      (CONJ (ASSUME `(r:real^N->bool) IN moi_s34_simp kk (&3)`) (ASSUME `(v:real^N) IN r`)))) THEN
    STRIP_TAC THEN
    MATCH_MP_TAC MOI_S4OT_CELL_NOT_IN_CLOSURE THEN
    MAP_EVERY EXISTS_TAC
     [`(rr:(real^N->bool)->real^3->bool) r INTER IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v)`;
      `UNIONS {(dd:(real^N->bool)->real^3->bool) s INTER
               IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v) | s |
               s IN moi_s34_simp kk (&2) /\ (v:real^N) IN s /\ s SUBSET r} UNION
       UNIONS {(rr:(real^N->bool)->real^3->bool) r INTER IMAGE f1 (moi_s34_sd tt kk g) | g |
               g IN moi_s34_simp kk (&1) /\ v IN g /\ g SUBSET r}`] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_bd tt kk)` THEN
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
      X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
      USE_THEN "TR" (MP_TAC o SPECL [`z:real^3`; `r:real^N->bool`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]]]]);;

(* The main theorem TOUTER: the outer target cells. *)

let TOUTER = prove
 (MOI_S34_OUTER,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[moi_s34_outer] THEN CONJ_TAC THENL
   [X_GEN_TAC `v:real^N` THEN STRIP_TAC THEN MATCH_MP_TAC MOI_S4OT_VERTEX_CLAUSE THEN
    MAP_EVERY EXISTS_TAC [`h:real^N->real^3`; `ep:real^N->real`;
                          `car:(real^N->bool)->real^3->bool`] THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `g:real^N->bool` THEN STRIP_TAC THEN MATCH_MP_TAC MOI_S4OT_EDGE_CLAUSE THEN
    MAP_EVERY EXISTS_TAC [`h:real^N->real^3`; `ep:real^N->real`;
                          `car:(real^N->bool)->real^3->bool`] THEN
    ASM_REWRITE_TAC[]]);;

