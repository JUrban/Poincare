(* ========================================================================= *)
(* pc_moi_lt_tower: the tower of the loop theorem (Moise GTM 47,             *)
(* pp.187-190).  Main theorems FROZEN_TO_CELL and SPHERE_STEP (the           *)
(* statements MOI_LT_FROZEN_TO_CELL, MOI_LT_SPHERE_STEP of                   *)
(* pc_moi_loop_stmt.ml).  Route: near a boundary point only the boundary     *)
(* simplices through it matter (MOI_LTO_STAR_NBHD); for the sphere step a    *)
(* fine iterated subdivision makes the boundary simplices meeting the loop a *)
(* buffer inside b1, then LOOP_SPHERE_CASE_STATEMENT.                        *)
(* ========================================================================= *)

needs "src/pc_moi_loop_stmt.ml";;
needs "src/pc_moi_fnd_m3b.ml";;

prioritize_real();;
type_invention_error := true;;



(* ------------------------------------------------------------------------- *)
(* Boundary stars and FROZEN_TO_CELL.                                         *)
(* ------------------------------------------------------------------------- *)

let MOI_LTO_NEAR = prove
 (`!(k:(real^N->bool)->bool) y.
     FINITE k /\ (!s. s IN k ==> closed s)
     ==> ?e. &0 < e /\ !s z. s IN k /\ z IN s /\ dist(y,z) < e ==> y IN s`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `D = UNIONS {s:real^N->bool | s IN k /\ ~(y IN s)}` THEN
  SUBGOAL_THEN `closed (D:real^N->bool) /\ ~((y:real^N) IN D)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN CONJ_TAC THENL
     [MATCH_MP_TAC CLOSED_UNIONS THEN ASM_SIMP_TAC[FINITE_RESTRICT; IN_ELIM_THM];
      REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN MESON_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPEC `(:real^N) DIFF D` OPEN_CONTAINS_BALL) THEN
  ASM_REWRITE_TAC[GSYM closed] THEN DISCH_THEN(MP_TAC o SPEC `y:real^N`) THEN
  ASM_REWRITE_TAC[IN_DIFF; IN_UNIV] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `e:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`s:real^N->bool`; `z:real^N`] THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  SUBGOAL_THEN `(z:real^N) IN D` MP_TAC THENL
   [EXPAND_TAC "D" THEN REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `ball(y:real^N,e) SUBSET (:real^N) DIFF D` THEN
  REWRITE_TAC[SUBSET; IN_BALL; IN_DIFF; IN_UNIV] THEN ASM_MESON_TAC[]);;

(* Near a boundary point y only the boundary simplices through y matter.    *)

let MOI_LTO_STAR_NBHD = prove
 (`!(c:(real^N->bool)->bool) y.
     FINITE c /\ lf_simplicial_complex c /\ y IN complex_boundary c
     ==> ?e. &0 < e /\
             !z. z IN complex_boundary c /\ dist(y,z) < e
                 ==> ?s. s IN c /\ s SUBSET complex_boundary c /\ y IN s /\ z IN s`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `bt = {s:real^N->bool | s IN c /\ aff_dim s = &2 /\
                      CARD {r | r IN c /\ aff_dim r = &3 /\ s SUBSET r} = 1}` THEN
  SUBGOAL_THEN `complex_boundary (c:(real^N->bool)->bool) = UNIONS bt` ASSUME_TAC THENL
   [EXPAND_TAC "bt" THEN REWRITE_TAC[complex_boundary]; ALL_TAC] THEN
  MP_TAC(ISPECL [`bt:(real^N->bool)->bool`; `y:real^N`] MOI_LTO_NEAR) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [EXPAND_TAC "bt" THEN MATCH_MP_TAC FINITE_RESTRICT THEN ASM_REWRITE_TAC[];
      EXPAND_TAC "bt" THEN REWRITE_TAC[IN_ELIM_THM] THEN
      ASM_MESON_TAC[MOI_FM3_LF_COMPACT; COMPACT_IMP_CLOSED]];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `e:real` THEN STRIP_TAC THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `z:real^N` THEN STRIP_TAC THEN
  UNDISCH_TAC `(z:real^N) IN complex_boundary c` THEN ASM_REWRITE_TAC[IN_UNIONS] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `s:real^N->bool` THEN REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `(s:real^N->bool) IN bt` THEN EXPAND_TAC "bt" THEN SIMP_TAC[IN_ELIM_THM];
    ASM SET_TAC[];
    ASM_MESON_TAC[];
    ASM_REWRITE_TAC[]]);;

let FROZEN_TO_CELL = prove
 (MOI_LT_FROZEN_TO_CELL,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold_with_boundary]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MOI_LTD_SAN_SIMPLICIAL_CELLWISE THEN
    EXISTS_TAC `k:(real^2->bool)->bool` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC CLOSED_UNIONS THEN CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `c:(real^N->bool)->bool` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[MOI_FM3_LF_COMPACT; COMPACT_IMP_CLOSED]];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET] THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(y:real^N) IN complex_boundary c` ASSUME_TAC THENL
   [UNDISCH_TAC `(y:real^N) IN IMAGE f (relative_frontier std_triangle)` THEN
    REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `x:real^2` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `{x | x IN std_triangle /\ (f:real^2->real^N) x IN complex_boundary c} =
                 relative_frontier std_triangle` THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `x:real^2`) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `y:real^N`] MOI_LTO_STAR_NBHD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[interior_of; IN_ELIM_THM] THEN
  EXISTS_TAC `complex_boundary c INTER ball(y:real^N,e)` THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_IN_OPEN_INTER THEN REWRITE_TAC[OPEN_BALL];
    ASM_REWRITE_TAC[IN_INTER; CENTRE_IN_BALL];
    REWRITE_TAC[SUBSET; IN_INTER; IN_BALL; IN_UNIONS; IN_ELIM_THM] THEN
    X_GEN_TAC `z:real^N` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `z:real^N`) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `s:real^N->bool` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[]]);;


(* ------------------------------------------------------------------------- *)
(* SPHERE_STEP.  L = f(rel frontier) is compact inside the                   *)
(* interior U of b1 in the boundary, U = complex_boundary c INTER O with O   *)
(* open; at distance < de from L, boundary points lie in U.  In a fine      *)
(* iterated subdivision cn (simplices of diameter < de) the boundary        *)
(* simplices cb in b meeting L form a buffer inside b and b1 whose interior *)
(* in b contains L; then LOOP_SPHERE_CASE_STATEMENT for cn.                  *)
(* ------------------------------------------------------------------------- *)

let MOI_LTO_LF_SC = prove
 (`!c:(real^N->bool)->bool. FINITE c /\ lf_simplicial_complex c ==> simplicial_complex c`,
  REWRITE_TAC[simplicial_complex; lf_simplicial_complex] THEN MESON_TAC[]);;

let SPHERE_STEP = prove
 (MOI_LT_SPHERE_STEP,
  REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "sph") THEN
  MAP_EVERY X_GEN_TAC [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `b1:real^N->bool`;
                       `g:real^N->real^M`; `v:real^M->bool`; `b:real^N->bool`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold_with_boundary]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_LTD_CELLWISE_BASIC) THEN
  MP_TAC(ISPEC `f:real^2->real^N` MOI_LTD_LOOP_COMPOSE) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `relative_frontier std_triangle SUBSET std_triangle` ASSUME_TAC THENL
   [REWRITE_TAC[relative_frontier] THEN SIMP_TAC[CLOSURE_CLOSED; MOI_LTD_STD_TRIANGLE_BASIC] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `compact (IMAGE (f:real^2->real^N) (relative_frontier std_triangle))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN CONJ_TAC THENL
     [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
      SIMP_TAC[COMPACT_RELATIVE_FRONTIER_BOUNDED; COMPACT_IMP_BOUNDED;
               MOI_LTD_STD_TRIANGLE_BASIC]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?O:real^N->bool. open O /\
      (subtopology euclidean (complex_boundary c)) interior_of b1 = complex_boundary c INTER O`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM OPEN_IN_OPEN] THEN REWRITE_TAC[OPEN_IN_INTERIOR_OF]; ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (f:real^2->real^N) (relative_frontier std_triangle) SUBSET O`
  ASSUME_TAC THENL
   [UNDISCH_TAC `IMAGE (f:real^2->real^N) (relative_frontier std_triangle) SUBSET
                 (subtopology euclidean (complex_boundary (c:(real^N->bool)->bool))) interior_of
                 (b1:real^N->bool)` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (f:real^2->real^N) (relative_frontier std_triangle)`;
                 `(:real^N) DIFF O`] SEPARATE_COMPACT_CLOSED) THEN
  ASM_REWRITE_TAC[GSYM OPEN_CLOSED] THEN ANTS_TAC THENL
   [UNDISCH_TAC `IMAGE (f:real^2->real^N) (relative_frontier std_triangle) SUBSET
                 (O:real^N->bool)` THEN SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `de:real` STRIP_ASSUME_TAC) THEN
  (* the fine subdivision cn *)
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `de:real`]
    ITERATED_BARYCENTRIC_SUBDIVISION_FINE) THEN
  ASM_SIMP_TAC[MOI_LTO_LF_SC] THEN DISCH_THEN(X_CHOOSE_THEN `n:num` MP_TAC) THEN
  MP_TAC(SPECL [`n:num`; `c:(real^N->bool)->bool`]
    (MATCH_MP MOI_LTD_ITER_SD COMBINATORIAL_WB_BARYCENTRIC)) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `cn = ITER n barycentric_subdivision (c:(real^N->bool)->bool)` THEN
  STRIP_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (cn:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold_with_boundary]; ALL_TAC] THEN
  SUBGOAL_THEN `(b:real^N->bool) SUBSET complex_boundary c` ASSUME_TAC THENL
   [ASM_MESON_TAC[IN_COMPONENTS_SUBSET]; ALL_TAC] THEN
  (* the buffer cb *)
  ABBREV_TAC `cb = {s:real^N->bool | s IN cn /\ s SUBSET b /\
                      ~(s INTER IMAGE (f:real^2->real^N) (relative_frontier std_triangle) = {})}` THEN
  SUBGOAL_THEN
   `!s:real^N->bool. s IN cb <=>
       s IN cn /\ s SUBSET b /\
       ~(s INTER IMAGE (f:real^2->real^N) (relative_frontier std_triangle) = {})`
  ASSUME_TAC THENL [EXPAND_TAC "cb" THEN REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `UNIONS cb SUBSET (b1:real^N->bool)` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_UNIONS] THEN X_GEN_TAC `z:real^N` THEN
    DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC `(s:real^N->bool) IN cb` THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `?x:real^N. x IN s /\ x IN IMAGE (f:real^2->real^N) (relative_frontier std_triangle)`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `~((s:real^N->bool) INTER
                     IMAGE (f:real^2->real^N) (relative_frontier std_triangle) = {})` THEN
      SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(z:real^N) IN O` ASSUME_TAC THENL
     [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`x:real^N`; `z:real^N`] o check (fun th ->
        is_forall(concl th) && can (find_term ((=) `de:real`)) (concl th) &&
        can (find_term ((=) `O:real^N->bool`)) (concl th))) THEN
      ASM_REWRITE_TAC[IN_DIFF; IN_UNIV; REAL_NOT_LE] THEN
      MP_TAC(ISPECL [`s:real^N->bool`; `x:real^N`; `z:real^N`] DIAMETER_BOUNDED_BOUND) THEN
      ANTS_TAC THENL [ASM_MESON_TAC[MOI_FM3_LF_COMPACT; COMPACT_IMP_BOUNDED]; ALL_TAC] THEN
      SUBGOAL_THEN `diameter (s:real^N->bool) < de` MP_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[dist] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(z:real^N) IN (subtopology euclidean (complex_boundary c)) interior_of b1`
    MP_TAC THENL
     [ASM_REWRITE_TAC[IN_INTER] THEN
      MP_TAC(ASSUME `(z:real^N) IN s`) THEN MP_TAC(ASSUME `(s:real^N->bool) SUBSET b`) THEN
      MP_TAC(ASSUME `(b:real^N->bool) SUBSET complex_boundary c`) THEN SET_TAC[];
      MP_TAC(ISPECL [`subtopology euclidean (complex_boundary (c:(real^N->bool)->bool))`;
                     `b1:real^N->bool`] INTERIOR_OF_SUBSET) THEN
      SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (f:real^2->real^N) (relative_frontier std_triangle) SUBSET
    (subtopology euclidean b) interior_of (UNIONS cb)`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET] THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(y:real^N) IN b` ASSUME_TAC THENL
     [MP_TAC(ASSUME `(y:real^N) IN IMAGE (f:real^2->real^N) (relative_frontier std_triangle)`) THEN
      MP_TAC(ASSUME `IMAGE (f:real^2->real^N) (relative_frontier std_triangle) SUBSET b`) THEN
      SET_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`cn:(real^N->bool)->bool`; `y:real^N`] MOI_LTO_STAR_NBHD) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MP_TAC(ASSUME `(y:real^N) IN b`) THEN
      MP_TAC(ASSUME `(b:real^N->bool) SUBSET complex_boundary c`) THEN SET_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "star"))) THEN
    REWRITE_TAC[interior_of; IN_ELIM_THM] THEN
    EXISTS_TAC `b INTER ball(y:real^N,e)` THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_IN_OPEN_INTER THEN REWRITE_TAC[OPEN_BALL];
      ASM_REWRITE_TAC[IN_INTER; CENTRE_IN_BALL];
      REWRITE_TAC[SUBSET; IN_INTER; IN_BALL; IN_UNIONS] THEN
      X_GEN_TAC `z:real^N` THEN STRIP_TAC THEN
      REMOVE_THEN "star" (MP_TAC o SPEC `z:real^N`) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN MP_TAC(ASSUME `(z:real^N) IN b`) THEN
        MP_TAC(ASSUME `(b:real^N->bool) SUBSET complex_boundary c`) THEN SET_TAC[];
        ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC COMPONENTS_MAXIMAL THEN
        EXISTS_TAC `complex_boundary (c:(real^N->bool)->bool)` THEN
        ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
         [MATCH_MP_TAC CONVEX_CONNECTED THEN ASM_MESON_TAC[MOI_FM3_LF_CONVEX];
          ASM_MESON_TAC[];
          MP_TAC(ASSUME `(y:real^N) IN b`) THEN MP_TAC(ASSUME `(y:real^N) IN s`) THEN
          SET_TAC[]];
        MP_TAC(ASSUME `(y:real^N) IN s`) THEN
        MP_TAC(ASSUME `(y:real^N) IN IMAGE (f:real^2->real^N) (relative_frontier std_triangle)`) THEN
        SET_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `cb SUBSET (cn:(real^N->bool)->bool) /\ UNIONS cb SUBSET (b:real^N->bool) /\
    (g:real^N->real^M) continuous_on UNIONS cb /\ IMAGE g (UNIONS cb) SUBSET v`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [EXPAND_TAC "cb" THEN SET_TAC[];
      REWRITE_TAC[UNIONS_SUBSET] THEN ASM_MESON_TAC[];
      ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
      MP_TAC(ASSUME `UNIONS cb SUBSET (b1:real^N->bool)`) THEN
      MP_TAC(ASSUME `IMAGE (g:real^N->real^M) b1 SUBSET v`) THEN SET_TAC[]];
    ALL_TAC] THEN
  REMOVE_THEN "sph" (MP_TAC o SPECL
   [`cn:(real^N->bool)->bool`; `b:real^N->bool`; `cb:(real^N->bool)->bool`;
    `(f:real^2->real^N) o std_triangle_loop`; `g:real^N->real^M`; `v:real^M->bool`] o
   REWRITE_RULE[LOOP_SPHERE_CASE_STATEMENT]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

