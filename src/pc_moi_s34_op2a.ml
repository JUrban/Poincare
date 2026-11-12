needs "src/pc_moi_fnd_stmt.ml";;
needs "src/pc_moi_sch3_s2.ml";;
needs "src/pc_moi_sch3_free.ml";;
needs "src/pc_moi_sch3_push.ml";;
needs "src/pc_moi_sch3_cvx.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* pc_moi_s34_op2a: a generic bigon slide in real^3 for the                  *)
(* Moise Sec 34 unit s34_op2 (Operation 2, Lemma 7, Moise GTM 47 p.242).    *)
(* A PL 3-ball C whose frontier crosses the frontier sphere of a PL 3-ball  *)
(* U along a trace, a rim circle in that sphere, and a bigon d in the       *)
(* sphere bounded by an arc of the trace and an arc of the rim: a PL        *)
(* homeomorphism of real^3 supported near d, preserving U, removes the two  *)
(* crossings of the trace with the rim at the ends of the bigon.  Route: a   *)
(* 2D push in the plane (crosscuts of a PL disk, 2D ambient Schoenflies      *)
(* AMB2_VERTEX), an ambient chart from PL_SCHOENFLIES_3_AMBIENT, and a       *)
(* suspension of the 2D map.  Main theorem MOI_S4P_SLIDE, applied in         *)
(* pc_moi_s34_op2b.                                                          *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Local facts about PL maps.                                                *)
(* ------------------------------------------------------------------------- *)

(* A PL map is affine on every short segment from an interior point. *)

let MOI_S4P_RAD_AFF = prove
 (`!(s:real^M->bool) (f:real^M->real^N) x.
     pl_map_on s f /\ x IN interior s
     ==> ?r. &0 < r /\ ball(x,r) SUBSET s /\
             !y t. y IN ball(x,r) /\ &0 <= t /\ t <= &1
                   ==> f(x + t % (y - x)) = f x + t % (f y - f x)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(x:real^M) IN s` ASSUME_TAC THENL
   [ASM_MESON_TAC[INTERIOR_SUBSET; SUBSET]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:real^M` o GEN_REWRITE_RULE I [pl_map_on]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:(real^M->bool)->bool` (X_CHOOSE_THEN `u:real^M->bool`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`UNIONS {k:real^M->bool | k IN c /\ ~(x IN k)}`; `x:real^M`]
    SEPARATE_POINT_CLOSED) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC CLOSED_UNIONS THEN ASM_SIMP_TAC[FINITE_RESTRICT; IN_ELIM_THM] THEN
      ASM_MESON_TAC[POLYTOPE_IMP_CLOSED];
      REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN MESON_TAC[]];
    DISCH_THEN(X_CHOOSE_THEN `r1:real` STRIP_ASSUME_TAC)] THEN
  MP_TAC(ISPEC `u:real^M->bool` OPEN_CONTAINS_BALL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `x:real^M`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `r2:real` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `(x:real^M) IN interior s` THEN REWRITE_TAC[IN_INTERIOR] THEN
  DISCH_THEN(X_CHOOSE_THEN `r3:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `min r1 (min r2 r3)` THEN
  ASM_REWRITE_TAC[REAL_LT_MIN] THEN CONJ_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `ball(x:real^M,r3)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_BALL THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`y:real^M`; `t:real`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(y:real^M) IN s INTER u` MP_TAC THENL
   [REWRITE_TAC[IN_INTER] THEN CONJ_TAC THENL
     [UNDISCH_TAC `ball(x:real^M,r3) SUBSET s` THEN REWRITE_TAC[SUBSET] THEN
      DISCH_THEN MATCH_MP_TAC THEN UNDISCH_TAC `(y:real^M) IN ball(x,min r1 (min r2 r3))` THEN
      REWRITE_TAC[IN_BALL] THEN REAL_ARITH_TAC;
      UNDISCH_TAC `ball(x:real^M,r2) SUBSET u` THEN REWRITE_TAC[SUBSET] THEN
      DISCH_THEN MATCH_MP_TAC THEN UNDISCH_TAC `(y:real^M) IN ball(x,min r1 (min r2 r3))` THEN
      REWRITE_TAC[IN_BALL] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  UNDISCH_TAC `(s:real^M->bool) INTER u SUBSET UNIONS c` THEN
  REWRITE_TAC[IMP_IMP] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (SET_RULE
    `(s:real^M->bool) INTER u SUBSET t /\ (y:real^M) IN s INTER u ==> y IN t`)) THEN
  REWRITE_TAC[IN_UNIONS] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^M->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(x:real^M) IN k` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[TAUT `p <=> ~ ~p`] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:real^M` o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `r1:real`)) (concl th))) THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM; NOT_IMP] THEN CONJ_TAC THENL
     [EXISTS_TAC `k:real^M->bool` THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `(y:real^M) IN ball(x,min r1 (min r2 r3))` THEN
      REWRITE_TAC[IN_BALL] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `k:real^M->bool` o check (fun th ->
    is_forall(concl th) && can (find_term (fun t -> is_const t && fst(dest_const t) = "polytope")) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `l:real^M->real^N` (X_CHOOSE_THEN `z0:real^N` STRIP_ASSUME_TAC)))) THEN
  SUBGOAL_THEN `x + t % (y - x) IN (k:real^M->bool)` ASSUME_TAC THENL
   [REWRITE_TAC[VECTOR_ARITH `x + t % (y - x):real^M = (&1 - t) % x + t % y`] THEN
    MATCH_MP_TAC IN_CONVEX_SET THEN ASM_SIMP_TAC[POLYTOPE_IMP_CONVEX];
    ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LINEAR_ADD th; MATCH_MP LINEAR_CMUL th;
                                    MATCH_MP LINEAR_SUB th]) THEN
  VECTOR_ARITH_TAC);;

(* A PL homeomorphism between the boundaries of two PL n-cells extends to  *)
(* the cells (the proof of MOI_SPU_CELL_EXTEND of pc_moi_sch3_push, which   *)
(* is stated for 2-cells in real^3, for any n and N).                       *)

let MOI_S4P_CELL_EXTEND = prove
 (`!n d j:real^N->bool e i:real^N->bool (a:real^N->real^N) a'.
     pl_cell_with_boundary n d j /\ pl_cell_with_boundary n e i /\
     pl_homeomorphism (j,i) (a,a')
     ==> ?f g. pl_homeomorphism (d,e) (f,g) /\ (!x. x IN j ==> f x = a x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_cell_with_boundary] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `t:real^N->bool` (X_CHOOSE_THEN `p:real^N->real^N`
     (X_CHOOSE_THEN `p':real^N->real^N` (CONJUNCTS_THEN2 ASSUME_TAC
       (CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o SYM))))))
   (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `t':real^N->bool` (X_CHOOSE_THEN `q:real^N->real^N`
      (X_CHOOSE_THEN `q':real^N->real^N` (CONJUNCTS_THEN2 ASSUME_TAC
        (CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o SYM))))))
    ASSUME_TAC)) THEN
  SUBGOAL_THEN
   `relative_frontier t SUBSET (t:real^N->bool) /\
    relative_frontier t' SUBSET (t':real^N->bool) /\
    pl_polyhedron(relative_frontier t:real^N->bool) /\
    pl_polyhedron(relative_frontier t':real^N->bool)`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[RELATIVE_FRONTIER_SUBSET; POLYTOPE_IMP_CLOSED;
                  SIMPLEX_IMP_POLYTOPE; MOI_SA2_POLYTOPE_RF_POLYHEDRON];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_homeomorphism (relative_frontier t,j)
                  (p:real^N->real^N,p')`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`t:real^N->bool`; `d:real^N->bool`; `p:real^N->real^N`;
                   `p':real^N->real^N`; `relative_frontier t:real^N->bool`]
      MOI_FSA_PL_HOMEO_RESTRICT) THEN
    ASM_SIMP_TAC[LOCALLY_POLYHEDRAL_PL_POLYHEDRON];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_homeomorphism (i,relative_frontier t')
                  (q':real^N->real^N,q)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`t':real^N->bool`; `e:real^N->bool`; `q:real^N->real^N`;
                   `q':real^N->real^N`; `relative_frontier t':real^N->bool`]
      MOI_FSA_PL_HOMEO_RESTRICT) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[LOCALLY_POLYHEDRAL_PL_POLYHEDRON]; ALL_TAC] THEN
    GEN_REWRITE_TAC RAND_CONV [PL_HOMEOMORPHISM_SYM] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:real^N->bool`; `t':real^N->bool`; `n:num`;
                 `(q':real^N->real^N) o ((a:real^N->real^N) o (p:real^N->real^N))`;
                 `((p':real^N->real^N) o (a':real^N->real^N)) o (q:real^N->real^N)`]
    PL_HOMEOMORPHISM_CONE_EXTENSION) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
    EXISTS_TAC `i:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
    EXISTS_TAC `j:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `f':real^N->real^N` (X_CHOOSE_THEN
    `g':real^N->real^N` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC
   [`(q:real^N->real^N) o ((f':real^N->real^N) o (p':real^N->real^N))`;
    `((p:real^N->real^N) o (g':real^N->real^N)) o (q':real^N->real^N)`] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
    EXISTS_TAC `t':real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
    EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[PL_HOMEOMORPHISM_SYM] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN
  SUBGOAL_THEN `?y:real^N. y IN relative_frontier t /\ (x:real^N) = (p:real^N->real^N) y`
  STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[pl_homeomorphism; homeomorphism]) THEN
  SUBGOAL_THEN `(p':real^N->real^N) x = y` SUBST1_TAC THENL
   [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
  ASM_SIMP_TAC[o_THM] THEN
  SUBGOAL_THEN `(a:real^N->real^N) x IN e` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  ASM_MESON_TAC[]);;


(* ------------------------------------------------------------------------- *)
(* Crosscuts of a PL disk in the plane.  Two crosscuts with the              *)
(* same ends are carried onto each other by a PL homeomorphism of the disk  *)
(* fixing its boundary (MOI_SFR_THETA splits the disk along each crosscut). *)
(* ------------------------------------------------------------------------- *)

(* Polyhedral facts: the identity of a polyhedron, PL arcs are polyhedra. *)

let MOI_S4P_PLH_ID = prove
 (`!s:real^N->bool. pl_polyhedron s ==> pl_homeomorphism (s,s) ((\x. x),(\x. x))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[pl_homeomorphism; HOMEOMORPHISM_ID; GSYM LOCALLY_POLYHEDRAL_EQ_PL_MAP_ON_ID] THEN
  ASM_SIMP_TAC[LOCALLY_POLYHEDRAL_PL_POLYHEDRON]);;

let MOI_S4P_ARC_POLY = prove
 (`!g:real^1->real^N.
     pl_map_on (interval[vec 0,vec 1]) g ==> pl_polyhedron (path_image g)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[path_image] THEN
  MATCH_MP_TAC PL_POLYHEDRON_PL_IMAGE THEN ASM_REWRITE_TAC[pl_polyhedron] THEN
  EXISTS_TAC `{interval[vec 0:real^1,vec 1]}` THEN
  REWRITE_TAC[FINITE_SING; IN_SING; UNIONS_1] THEN MESON_TAC[POLYTOPE_INTERVAL]);;

(* Two PL arcs are PL homeomorphic by a map respecting the ends. *)

let MOI_S4P_ARC_ARC = prove
 (`!(b:real^1->real^N) (b':real^1->real^N).
     arc b /\ pl_map_on (interval[vec 0,vec 1]) b /\
     arc b' /\ pl_map_on (interval[vec 0,vec 1]) b'
     ==> ?h h'. pl_homeomorphism (path_image b,path_image b') (h,h') /\
                h (pathstart b) = pathstart b' /\ h (pathfinish b) = pathfinish b'`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `b:real^1->real^N` MOI_PL2_ARC_PL_HOMEOMORPHISM_ENDS) THEN
  MP_TAC(ISPEC `b':real^1->real^N` MOI_PL2_ARC_PL_HOMEOMORPHISM_ENDS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `k':real^N->real^1` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->real^1` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`(b':real^1->real^N) o (k:real^N->real^1)`;
                        `(b:real^1->real^N) o (k':real^N->real^1)`] THEN
  ASM_REWRITE_TAC[o_THM] THEN CONJ_TAC THENL
   [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
    EXISTS_TAC `interval[vec 0:real^1,vec 1]` THEN
    ONCE_REWRITE_TAC[PL_HOMEOMORPHISM_SYM] THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[PL_HOMEOMORPHISM_SYM] THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[pathstart; pathfinish]]);;

(* Crosscut swap: two crosscuts of a PL disk with the same ends are carried *)
(* onto each other by a PL homeomorphism of the disk fixing its boundary.   *)

let MOI_S4P_CROSSCUT_SWAP = prove
 (`!(a1:real^1->real^2) a2 b b' j.
     arc a1 /\ pl_map_on (interval[vec 0,vec 1]) a1 /\
     arc a2 /\ pl_map_on (interval[vec 0,vec 1]) a2 /\
     arc b /\ pl_map_on (interval[vec 0,vec 1]) b /\
     arc b' /\ pl_map_on (interval[vec 0,vec 1]) b' /\
     pathstart a2 = pathstart a1 /\ pathfinish a2 = pathfinish a1 /\
     pathstart b = pathstart a1 /\ pathfinish b = pathfinish a1 /\
     pathstart b' = pathstart a1 /\ pathfinish b' = pathfinish a1 /\
     path_image a1 INTER path_image a2 = {pathstart a1,pathfinish a1} /\
     path_image a1 UNION path_image a2 = j /\
     path_image b INTER j = {pathstart a1,pathfinish a1} /\
     path_image b SUBSET j UNION inside j /\
     path_image b' INTER j = {pathstart a1,pathfinish a1} /\
     path_image b' SUBSET j UNION inside j
     ==> ?f g. pl_homeomorphism (j UNION inside j,j UNION inside j) (f,g) /\
               (!x. x IN j ==> f x = x) /\
               IMAGE f (path_image b) = path_image b'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `u = (path_image a1 UNION path_image b) UNION
                  inside(path_image a1 UNION path_image (b:real^1->real^2))` THEN
  ABBREV_TAC `v = (path_image a2 UNION path_image b) UNION
                  inside(path_image a2 UNION path_image (b:real^1->real^2))` THEN
  ABBREV_TAC `u' = (path_image a1 UNION path_image b') UNION
                   inside(path_image a1 UNION path_image (b':real^1->real^2))` THEN
  ABBREV_TAC `v' = (path_image a2 UNION path_image b') UNION
                   inside(path_image a2 UNION path_image (b':real^1->real^2))` THEN
  MP_TAC(ISPECL [`a1:real^1->real^2`; `a2:real^1->real^2`; `b:real^1->real^2`;
                 `j:real^2->bool`; `u:real^2->bool`; `v:real^2->bool`] MOI_SFR_THETA) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`a1:real^1->real^2`; `a2:real^1->real^2`; `b':real^1->real^2`;
                 `j:real^2->bool`; `u':real^2->bool`; `v':real^2->bool`] MOI_SFR_THETA) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`b:real^1->real^2`; `b':real^1->real^2`] MOI_S4P_ARC_ARC) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^2->real^2` (X_CHOOSE_THEN `h':real^2->real^2`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `pl_polyhedron(path_image(a1:real^1->real^2)) /\
                pl_polyhedron(path_image(a2:real^1->real^2)) /\
                pl_polyhedron(path_image(b:real^1->real^2)) /\
                pl_polyhedron(path_image(b':real^1->real^2))` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[MOI_S4P_ARC_POLY]; ALL_TAC] THEN
  SUBGOAL_THEN `closed(path_image(a1:real^1->real^2)) /\
                closed(path_image(a2:real^1->real^2)) /\
                closed(path_image(b:real^1->real^2)) /\
                closed(path_image(b':real^1->real^2))` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[COMPACT_IMP_CLOSED; COMPACT_ARC_IMAGE]; ALL_TAC] THEN
  SUBGOAL_THEN
   `path_image a1 INTER path_image b = {pathstart(a1:real^1->real^2),pathfinish a1} /\
    path_image a2 INTER path_image b = {pathstart a1,pathfinish a1} /\
    path_image a1 INTER path_image b' = {pathstart a1,pathfinish a1} /\
    path_image a2 INTER path_image b' = {pathstart a1,pathfinish a1}`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `a1:real^1->real^2` PATHSTART_IN_PATH_IMAGE) THEN
    MP_TAC(ISPEC `a1:real^1->real^2` PATHFINISH_IN_PATH_IMAGE) THEN
    MP_TAC(ISPEC `a2:real^1->real^2` PATHSTART_IN_PATH_IMAGE) THEN
    MP_TAC(ISPEC `a2:real^1->real^2` PATHFINISH_IN_PATH_IMAGE) THEN
    MP_TAC(ISPEC `b:real^1->real^2` PATHSTART_IN_PATH_IMAGE) THEN
    MP_TAC(ISPEC `b:real^1->real^2` PATHFINISH_IN_PATH_IMAGE) THEN
    MP_TAC(ISPEC `b':real^1->real^2` PATHSTART_IN_PATH_IMAGE) THEN
    MP_TAC(ISPEC `b':real^1->real^2` PATHFINISH_IN_PATH_IMAGE) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `path_image b INTER j = {pathstart(a1:real^1->real^2),pathfinish a1}` THEN
    UNDISCH_TAC `path_image b' INTER j = {pathstart(a1:real^1->real^2),pathfinish a1}` THEN
    UNDISCH_TAC `path_image a1 UNION path_image a2 = (j:real^2->bool)` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^2. x IN path_image b /\ (x IN path_image a1 \/ x IN path_image a2)
                           ==> h x = x` ASSUME_TAC THENL
   [X_GEN_TAC `x:real^2` THEN STRIP_TAC THEN
    (SUBGOAL_THEN `x = pathstart(a1:real^1->real^2) \/ x = pathfinish a1` MP_TAC THENL
      [UNDISCH_TAC `path_image b INTER j = {pathstart(a1:real^1->real^2),pathfinish a1}` THEN
       UNDISCH_TAC `path_image a1 UNION path_image a2 = (j:real^2->bool)` THEN
       ASM SET_TAC[];
       ASM_MESON_TAC[]]);
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!c:real^1->real^2 w w'.
      (c = a1 \/ c = a2) /\
      pl_cell_with_boundary 2 w (path_image c UNION path_image b) /\
      pl_cell_with_boundary 2 w' (path_image c UNION path_image b')
      ==> ?ff gg. pl_homeomorphism (w,w') (ff,gg) /\
                (!x. x IN path_image c ==> ff x = x) /\
                (!x. x IN path_image b ==> ff x = h x)`
  (LABEL_TAC "half") THENL
   [REPEAT GEN_TAC THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "cc") STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`path_image(c:real^1->real^2)`; `path_image(b:real^1->real^2)`;
                   `path_image(c:real^1->real^2)`; `path_image(b':real^1->real^2)`;
                   `\x:real^2. x`; `\x:real^2. x`; `h:real^2->real^2`; `h':real^2->real^2`]
      MOI_PL2_PL_HOMEOMORPHISM_UNION) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[IMAGE_ID] THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "cc" (DISJ_CASES_THEN SUBST_ALL_TAC) THEN
      ASM_SIMP_TAC[MOI_S4P_PLH_ID] THEN REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
      GEN_TAC THEN DISCH_THEN(DISJ_CASES_THEN SUBST1_TAC) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(ASSUME_TAC o BETA_RULE) THEN
    MP_TAC(ISPECL [`2`; `w:real^2->bool`; `path_image c UNION path_image (b:real^1->real^2)`;
                   `w':real^2->bool`; `path_image c UNION path_image (b':real^1->real^2)`;
                   `\x:real^2. if x IN path_image c then x else h x`;
                   `\y:real^2. if y IN path_image c then y else h' y`]
      MOI_S4P_CELL_EXTEND) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `ff:real^2->real^2` THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `gg:real^2->real^2` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THEN X_GEN_TAC `x:real^2` THEN
    DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `x:real^2`) THEN
    ASM_REWRITE_TAC[IN_UNION] THEN DISCH_THEN SUBST1_TAC THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  USE_THEN "half" (MP_TAC o SPECL [`a1:real^1->real^2`; `u:real^2->bool`; `u':real^2->bool`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `fu:real^2->real^2` (X_CHOOSE_THEN `gu:real^2->real^2`
    STRIP_ASSUME_TAC)) THEN
  USE_THEN "half" (MP_TAC o SPECL [`a2:real^1->real^2`; `v:real^2->bool`; `v':real^2->bool`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `fv:real^2->real^2` (X_CHOOSE_THEN `gv:real^2->real^2`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `IMAGE (h:real^2->real^2) (path_image b) = path_image (b':real^1->real^2)`
  ASSUME_TAC THENL [ASM_MESON_TAC[MOI_PL2_PL_HOMEO_IMAGE]; ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (fu:real^2->real^2) (path_image b) = path_image (b':real^1->real^2)`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `IMAGE (h:real^2->real^2) (path_image b)`)) THEN
    MATCH_MP_TAC(SET_RULE `(!x:real^2. x IN s ==> f x = g x) ==> IMAGE f s = IMAGE (g:real^2->real^2) s`) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`u:real^2->bool`; `v:real^2->bool`; `u':real^2->bool`; `v':real^2->bool`;
                 `fu:real^2->real^2`; `gu:real^2->real^2`; `fv:real^2->real^2`;
                 `gv:real^2->real^2`] MOI_PL2_PL_HOMEOMORPHISM_UNION) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[COMPACT_IMP_CLOSED];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MAP_EVERY EXISTS_TAC [`\x:real^2. if x IN u then (fu:real^2->real^2) x else fv x`;
                        `\y:real^2. if y IN u' then (gu:real^2->real^2) y else gv y`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN COND_CASES_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `fu:real^2->real^2`)) (concl th) &&
        can (find_term ((=) `path_image (a1:real^1->real^2)`)) (concl th))) THEN
      UNDISCH_TAC `(x:real^2) IN j` THEN UNDISCH_TAC `(x:real^2) IN u` THEN
      UNDISCH_TAC `u INTER path_image a2 = {pathstart(a1:real^1->real^2),pathfinish a1}` THEN
      UNDISCH_TAC `path_image a1 UNION path_image a2 = (j:real^2->bool)` THEN
      MP_TAC(ISPEC `a1:real^1->real^2` PATHSTART_IN_PATH_IMAGE) THEN
      MP_TAC(ISPEC `a1:real^1->real^2` PATHFINISH_IN_PATH_IMAGE) THEN
      SET_TAC[];
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `fv:real^2->real^2`)) (concl th) &&
        can (find_term ((=) `path_image (a2:real^1->real^2)`)) (concl th))) THEN
      UNDISCH_TAC `(x:real^2) IN j` THEN UNDISCH_TAC `~((x:real^2) IN u)` THEN
      UNDISCH_TAC `(path_image a1 UNION path_image b) UNION
                   inside(path_image a1 UNION path_image (b:real^1->real^2)) = u` THEN
      UNDISCH_TAC `path_image a1 UNION path_image a2 = (j:real^2->bool)` THEN
      SET_TAC[]];
    SUBGOAL_THEN `path_image (b:real^1->real^2) SUBSET u` ASSUME_TAC THENL
     [UNDISCH_TAC `(path_image a1 UNION path_image b) UNION
                   inside(path_image a1 UNION path_image (b:real^1->real^2)) = u` THEN
      SET_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `IMAGE (fu:real^2->real^2) (path_image b)`)) THEN
    MATCH_MP_TAC(SET_RULE `(!x:real^2. x IN s ==> f x = g x) ==> IMAGE f s = IMAGE (g:real^2->real^2) s`) THEN
    UNDISCH_TAC `path_image (b:real^1->real^2) SUBSET u` THEN SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The conical picture of a curve crossing in the plane.                     *)
(* ------------------------------------------------------------------------- *)

(* A PL homeomorphism of the plane carries curve-crossing charts. *)

let MOI_S4P_PLH_OPEN = prove
 (`!(c:real^N->real^N) c' u.
     pl_homeomorphism ((:real^N),(:real^N)) (c,c') /\ open u
     ==> open (IMAGE c u) /\ pl_homeomorphism (u,IMAGE c u) (c,c')`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `open (IMAGE (c:real^N->real^N) u)` ASSUME_TAC THENL
   [SUBGOAL_THEN `IMAGE (c:real^N->real^N) u = {y | (c':real^N->real^N) y IN u}`
    SUBST1_TAC THENL
     [UNDISCH_TAC `pl_homeomorphism ((:real^N),(:real^N)) (c:real^N->real^N,c')` THEN
      REWRITE_TAC[pl_homeomorphism; homeomorphism; IN_UNIV; EXTENSION; IN_IMAGE;
                  IN_ELIM_THM] THEN MESON_TAC[];
      MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE_UNIV THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[pl_homeomorphism; homeomorphism; CONTINUOUS_ON_EQ_CONTINUOUS_AT;
                    OPEN_UNIV; IN_UNIV]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_SCD_PLH_SUBSET THEN
  MAP_EVERY EXISTS_TAC [`(:real^N)`; `(:real^N)`] THEN
  ASM_SIMP_TAC[SUBSET_UNIV; LOCALLY_POLYHEDRAL_OPEN]);;

let MOI_S4P_CROSS2_TRANSPORT = prove
 (`!(c:real^2->real^2) c' j k x.
     pl_homeomorphism ((:real^2),(:real^2)) (c,c') /\
     pl_curve_crossing_at (:real^2) j k x
     ==> pl_curve_crossing_at (:real^2) (IMAGE c j) (IMAGE c k) (c x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_curve_crossing_at; SUBTOPOLOGY_UNIV; GSYM OPEN_IN] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `u:real^2->bool`
    (X_CHOOSE_THEN `f:real^2->real^2` (X_CHOOSE_THEN `g:real^2->real^2`
      STRIP_ASSUME_TAC)))) THEN
  MP_TAC(ISPECL [`c:real^2->real^2`; `c':real^2->real^2`; `u:real^2->bool`]
    MOI_S4P_PLH_OPEN) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!y:real^2. c'((c:real^2->real^2) y) = y` ASSUME_TAC THENL
   [ASM_MESON_TAC[pl_homeomorphism; homeomorphism; IN_UNIV]; ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE ((f:real^2->real^2) o (c':real^2->real^2)) (IMAGE c u) = IMAGE f u`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM IMAGE_o; o_DEF] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`IMAGE (c:real^2->real^2) u`; `(f:real^2->real^2) o (c':real^2->real^2)`;
                        `(c:real^2->real^2) o (g:real^2->real^2)`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM SET_TAC[];
    MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `u:real^2->bool` THEN
    ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[PL_HOMEOMORPHISM_SYM] THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[o_THM];
    ONCE_REWRITE_TAC[GSYM IMAGE_o] THEN
    REWRITE_TAC[o_ASSOC] THEN
    SUBGOAL_THEN `IMAGE (f o (c':real^2->real^2)) (IMAGE c j INTER IMAGE c u) =
                  IMAGE (f:real^2->real^2) (j INTER u)` SUBST1_TAC THENL
     [REWRITE_TAC[GSYM IMAGE_o; o_DEF; EXTENSION; IN_IMAGE; IN_INTER] THEN ASM_MESON_TAC[];
      ASM_REWRITE_TAC[]];
    SUBGOAL_THEN `IMAGE (f o (c':real^2->real^2)) (IMAGE c k INTER IMAGE c u) =
                  IMAGE (f:real^2->real^2) (k INTER u)` SUBST1_TAC THENL
     [REWRITE_TAC[GSYM IMAGE_o; o_DEF; EXTENSION; IN_IMAGE; IN_INTER] THEN ASM_MESON_TAC[];
      ASM_REWRITE_TAC[]]]);;

(* Points of a ray from x of length at most r lie on the radial segment. *)

let MOI_S4P_RAY_SEG = prove
 (`!(x:real^N) a y r mu.
     ~(a = x) /\ &0 <= mu /\ y = x + mu % (a - x) /\ norm(y - x) <= r
     ==> y IN segment[x,x + r % inv(norm(a - x)) % (a - x)]`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < norm(a - x:real^N)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT; VECTOR_SUB_EQ]; ALL_TAC] THEN
  SUBGOAL_THEN `norm(y - x:real^N) = mu * norm(a - x)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[VECTOR_ARITH `(x + m % v) - x:real^N = m % v`; NORM_MUL] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 <= m ==> abs m = m`];
    ALL_TAC] THEN
  ASM_CASES_TAC `r = &0` THENL
   [SUBGOAL_THEN `y:real^N = x` SUBST1_TAC THENL
     [ASM_MESON_TAC[NORM_LE_0; VECTOR_SUB_EQ]; REWRITE_TAC[ENDS_IN_SEGMENT]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < r` ASSUME_TAC THENL
   [MP_TAC(ISPEC `y - x:real^N` NORM_POS_LE) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[IN_SEGMENT] THEN EXISTS_TAC `(mu * norm(a - x:real^N)) / r` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_DIV THEN ASM_SIMP_TAC[REAL_LE_MUL; NORM_POS_LE; REAL_LT_IMP_LE];
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_MUL_LID] THEN ASM_MESON_TAC[];
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[VECTOR_ARITH `(&1 - t) % x + t % (x + v):real^N = x + t % v`] THEN
    AP_TERM_TAC THEN REWRITE_TAC[VECTOR_MUL_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    UNDISCH_TAC `&0 < r` THEN UNDISCH_TAC `&0 < norm(a - x:real^N)` THEN
    CONV_TAC REAL_FIELD]);;

(* Small facts used by the conical picture. *)

let MOI_S4P_HOMEO_OPEN_IMAGE = prove
 (`!(f:real^N->real^N) g u v w.
     homeomorphism (u,v) (f,g) /\ open u /\ open v /\ w SUBSET v /\ open w
     ==> open (IMAGE g w)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`g:real^N->real^N`; `f:real^N->real^N`; `v:real^N->bool`; `u:real^N->bool`;
                 `w:real^N->bool`] HOMEOMORPHISM_IMP_OPEN_MAP) THEN
  ANTS_TAC THENL
   [ONCE_REWRITE_TAC[HOMEOMORPHISM_SYM] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC OPEN_SUBSET THEN ASM_REWRITE_TAC[];
    DISCH_TAC THEN MATCH_MP_TAC OPEN_IN_OPEN_TRANS THEN
    EXISTS_TAC `u:real^N->bool` THEN ASM_REWRITE_TAC[]]);;

let MOI_S4P_AXIS2 = prove
 (`(!z:real^2. z$1 = &0 ==> z = (z$2) % basis 2) /\
   (!z:real^2. z$2 = &0 ==> z = (z$1) % basis 1) /\
   (!t. (t % basis 2:real^2)$1 = &0) /\ (!t. (t % basis 2:real^2)$2 = t) /\
   (!t. (t % basis 1:real^2)$1 = t) /\ (!t. (t % basis 1:real^2)$2 = &0) /\
   (!t. norm(t % basis 2:real^2) = abs t) /\ (!t. norm(t % basis 1:real^2) = abs t)`,
  SIMP_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_MUL_COMPONENT; BASIS_COMPONENT;
           ARITH; NORM_MUL; NORM_BASIS] THEN REAL_ARITH_TAC);;

(* A radially affine injective map on a ball sends an axis through 0 onto   *)
(* two radial segments near the image of 0.                                 *)

let MOI_S4P_RADIAL_POINT = prove
 (`!(g:real^2->real^2) x s (b:real^2) t.
     &0 < s /\ norm b = &1 /\
     (!y t. y IN ball(vec 0,s) /\ &0 <= t /\ t <= &1 ==> g(t % y) = x + t % (g y - x)) /\
     &0 <= t /\ t < s
     ==> g(t % b) = x + (&2 * t / s) % (g((s / &2) % b) - x)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!w. abs w < s ==> (w % b:real^2) IN ball(vec 0,s)` ASSUME_TAC THENL
   [REWRITE_TAC[IN_BALL_0; NORM_MUL] THEN ASM_REWRITE_TAC[REAL_MUL_RID]; ALL_TAC] THEN
  ASM_CASES_TAC `&2 * t / s <= &1` THENL
   [SUBGOAL_THEN `t % (b:real^2) = (&2 * t / s) % ((s / &2) % b)` SUBST1_TAC THENL
     [REWRITE_TAC[VECTOR_MUL_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      UNDISCH_TAC `&0 < s` THEN CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `x:real^2`)) (concl th))) THEN
    REPEAT CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
       [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC];
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `s < &2 * t` ASSUME_TAC THENL
   [UNDISCH_TAC `~(&2 * t / s <= &1)` THEN
    REWRITE_TAC[REAL_ARITH `&2 * t / s = (&2 * t) / s`] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < t` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPECL [`t % b:real^2`; `s / (&2 * t)`] o check (fun th ->
    is_forall(concl th) && can (find_term ((=) `x:real^2`)) (concl th))) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `&0 < t ==> &0 < &2 * t`] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(s / (&2 * t)) % t % (b:real^2) = (s / &2) % b` SUBST1_TAC THENL
   [REWRITE_TAC[VECTOR_MUL_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    UNDISCH_TAC `&0 < t` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[VECTOR_ARITH `(x + u % (y - x)) - x:real^2 = u % (y - x)`] THEN
  REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
  SUBGOAL_THEN `(&2 * t / s) * s / (&2 * t) = &1` SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < t` THEN UNDISCH_TAC `&0 < s` THEN CONV_TAC REAL_FIELD;
    VECTOR_ARITH_TAC]);;

let MOI_S4P_RADIAL_AXIS = prove
 (`!(g:real^2->real^2) x s (b:real^2) c r.
     &0 < s /\ norm b = &1 /\
     (!y t. y IN ball(vec 0,s) /\ &0 <= t /\ t <= &1 ==> g(t % y) = x + t % (g y - x)) /\
     (!y. y IN ball(vec 0,s) ==> (g y IN c <=> ?t. y = t % b)) /\
     cball(x,r) SUBSET IMAGE g (ball(vec 0,s)) /\ &0 < r /\
     ~(g((s / &2) % b) = x) /\ ~(g((--(s / &2)) % b) = x) /\
     r < norm(g((s / &2) % b) - x) /\ r < norm(g((--(s / &2)) % b) - x)
     ==> c INTER cball(x,r) =
         segment[x,x + r % inv(norm(g((s / &2) % b) - x)) % (g((s / &2) % b) - x)] UNION
         segment[x,x + r % inv(norm(g((--(s / &2)) % b) - x)) % (g((--(s / &2)) % b) - x)]`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!w. abs w < s ==> (w % b:real^2) IN ball(vec 0,s)` ASSUME_TAC THENL
   [REWRITE_TAC[IN_BALL_0; NORM_MUL] THEN ASM_REWRITE_TAC[REAL_MUL_RID]; ALL_TAC] THEN
  SUBGOAL_THEN `norm(--b:real^2) = &1` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_NEG]; ALL_TAC] THEN
  SUBGOAL_THEN `(--(s / &2)) % (b:real^2) = (s / &2) % --b` ASSUME_TAC THENL
   [VECTOR_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!(bb:real^2) w. norm bb = &1 /\ ~((g:real^2->real^2)((s / &2) % bb) = (x:real^2)) /\
                    r < norm(g((s / &2) % bb) - x) /\ &0 <= w /\ w < s /\
                    norm(g(w % bb) - x) <= r
                    ==> g(w % bb) IN segment[x,x + r % inv(norm(g((s / &2) % bb) - x)) %
                                                   (g((s / &2) % bb) - x)]`
  (LABEL_TAC "sub") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_S4P_RAY_SEG THEN
    EXISTS_TAC `&2 * w / s` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
       [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC];
      MATCH_MP_TAC MOI_S4P_RADIAL_POINT THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!(bb:real^2) y. norm bb = &1 /\
                    (!t. (t % bb) IN ball(vec 0,s) ==> (g:real^2->real^2)(t % bb) IN c) /\
                    r < norm(g((s / &2) % bb) - x) /\
                    y IN segment[x,x + r % inv(norm(g((s / &2) % bb) - x)) %
                                   (g((s / &2) % bb) - x)]
                    ==> y IN c INTER cball(x,r)`
  (LABEL_TAC "sup") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    UNDISCH_TAC `(y:real^2) IN segment[x,x + r % inv(norm((g:real^2->real^2)((s / &2) % bb) - x)) %
                                       (g((s / &2) % bb) - x)]` THEN
    REWRITE_TAC[IN_SEGMENT] THEN
    DISCH_THEN(X_CHOOSE_THEN `lam:real` STRIP_ASSUME_TAC) THEN
    ABBREV_TAC `P = (g:real^2->real^2)((s / &2) % bb)` THEN
    SUBGOAL_THEN `&0 < norm(P - x:real^2)` ASSUME_TAC THENL
     [MP_TAC(ISPEC `P - x:real^2` NORM_POS_LE) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ABBREV_TAC `mu = lam * r * inv(norm(P - x:real^2))` THEN
    SUBGOAL_THEN `&0 <= mu /\ mu <= &1` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "mu" THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC REAL_LE_MUL THEN
        ASM_SIMP_TAC[REAL_LE_INV_EQ; NORM_POS_LE] THEN
        MP_TAC(ISPEC `P - x:real^2` NORM_POS_LE) THEN ASM_REAL_ARITH_TAC;
        REWRITE_TAC[GSYM real_div; REAL_MUL_ASSOC] THEN
        ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_MUL_LID] THEN
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1 * r` THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]];
      ALL_TAC] THEN
    SUBGOAL_THEN `y = (g:real^2->real^2)(mu % (s / &2) % bb)` SUBST1_TAC THENL
     [MP_TAC(ISPECL [`(s / &2) % bb:real^2`; `mu:real`] (ASSUME
       `!y t. y IN ball(vec 0,s) /\ &0 <= t /\ t <= &1
              ==> (g:real^2->real^2)(t % y) = x + t % (g y - x)`)) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[IN_BALL_0; NORM_MUL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "mu" THEN
      REWRITE_TAC[VECTOR_ARITH `(&1 - l) % x + l % (x + v):real^2 = x + l % v`] THEN
      REWRITE_TAC[VECTOR_MUL_ASSOC; REAL_MUL_ASSOC];
      ALL_TAC] THEN
    REWRITE_TAC[IN_INTER; VECTOR_MUL_ASSOC] THEN CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_BALL_0; NORM_MUL; REAL_ABS_MUL] THEN
      ASM_REWRITE_TAC[REAL_MUL_RID] THEN
      SUBGOAL_THEN `abs mu * abs(s / &2) <= &1 * s / &2` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    REWRITE_TAC[GSYM VECTOR_MUL_ASSOC] THEN
    MP_TAC(ISPECL [`(s / &2) % bb:real^2`; `mu:real`] (ASSUME
       `!y t. y IN ball(vec 0,s) /\ &0 <= t /\ t <= &1
              ==> (g:real^2->real^2)(t % y) = x + t % (g y - x)`)) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[IN_BALL_0; NORM_MUL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[IN_CBALL; dist] THEN
    REWRITE_TAC[VECTOR_ARITH `x - (x + v):real^2 = --v`; NORM_NEG; NORM_MUL] THEN
    EXPAND_TAC "mu" THEN
    ASM_SIMP_TAC[REAL_ABS_MUL; REAL_ABS_INV; REAL_ABS_NORM;
                 REAL_ARITH `&0 <= m ==> abs m = m`] THEN
    REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
    ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ; REAL_MUL_RID] THEN
    SUBGOAL_THEN `&0 <= r` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 <= m ==> abs m = m`] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1 * r` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  UNDISCH_TAC `--(s / &2) % (b:real^2) = s / &2 % --b` THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th] THEN RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN
                       ASSUME_TAC th) THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `y:real^2` THEN EQ_TAC THENL
   [REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN
    SUBGOAL_THEN `?z:real^2. z IN ball(vec 0,s) /\ y = (g:real^2->real^2) z` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `cball(x:real^2,r) SUBSET IMAGE (g:real^2->real^2) (ball(vec 0,s))` THEN
      UNDISCH_TAC `(y:real^2) IN cball(x,r)` THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `?t. z = t % (b:real^2)` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `(z:real^2) IN ball(vec 0,s)` THEN
    ASM_REWRITE_TAC[IN_BALL_0; NORM_MUL; REAL_MUL_RID] THEN DISCH_TAC THEN
    REWRITE_TAC[IN_UNION] THEN DISJ_CASES_TAC(REAL_ARITH `&0 <= t \/ t < &0`) THENL
     [DISJ1_TAC THEN USE_THEN "sub" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(y:real^2) IN cball(x,r)` THEN ASM_REWRITE_TAC[IN_CBALL; dist] THEN
      DISCH_TAC THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; ONCE_REWRITE_TAC[NORM_SUB] THEN ASM_REWRITE_TAC[]];
      DISJ2_TAC THEN
      SUBGOAL_THEN `t % (b:real^2) = (--t) % --b` SUBST1_TAC THENL
       [VECTOR_ARITH_TAC; ALL_TAC] THEN
      USE_THEN "sub" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(y:real^2) IN cball(x,r)` THEN ASM_REWRITE_TAC[IN_CBALL; dist] THEN
      REWRITE_TAC[VECTOR_ARITH `(--t) % --b:real^2 = t % b`] THEN
      DISCH_TAC THEN REPEAT CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
        ONCE_REWRITE_TAC[NORM_SUB] THEN ASM_REWRITE_TAC[]]];
    REWRITE_TAC[IN_UNION] THEN STRIP_TAC THENL
     [USE_THEN "sup" MATCH_MP_TAC THEN EXISTS_TAC `b:real^2` THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `t:real` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(g:real^2->real^2)(t % b) IN c <=> ?t'. t % b = t' % (b:real^2)`
      SUBST1_TAC THENL [ASM_MESON_TAC[]; MESON_TAC[]];
      USE_THEN "sup" MATCH_MP_TAC THEN EXISTS_TAC `--b:real^2` THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `t:real` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(g:real^2->real^2)(t % --b) IN c <=> ?t'. t % --b = t' % (b:real^2)`
      SUBST1_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      EXISTS_TAC `--t` THEN VECTOR_ARITH_TAC]]);;

(* Points of the radial segment are images of points of the axis. *)

let MOI_S4P_SEG_PT = prove
 (`!(g:real^2->real^2) x s (b:real^2) r y.
     &0 < s /\ norm b = &1 /\
     (!y t. y IN ball(vec 0,s) /\ &0 <= t /\ t <= &1 ==> g(t % y) = x + t % (g y - x)) /\
     &0 < r /\ r < norm(g((s / &2) % b) - x) /\
     y IN segment[x,x + r % inv(norm(g((s / &2) % b) - x)) % (g((s / &2) % b) - x)]
     ==> ?m. &0 <= m /\ m < s / &2 /\ y = g(m % b) /\ (~(y = x) ==> &0 < m)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `(y:real^2) IN segment[x,x + r % inv(norm((g:real^2->real^2)((s / &2) % b) - x)) %
                                       (g((s / &2) % b) - x)]` THEN
  REWRITE_TAC[IN_SEGMENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `lam:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `P = (g:real^2->real^2)((s / &2) % b)` THEN
  SUBGOAL_THEN `&0 < norm(P - x:real^2)` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `mu = lam * r * inv(norm(P - x:real^2))` THEN
  SUBGOAL_THEN `&0 <= mu /\ mu < &1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "mu" THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN
      ASM_SIMP_TAC[REAL_LE_INV_EQ; NORM_POS_LE] THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[GSYM real_div; REAL_MUL_ASSOC] THEN
      ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_MUL_LID] THEN
      MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `&1 * r` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  EXISTS_TAC `mu * s / &2` THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC(REAL_ARITH `m * a < &1 * a ==> m * a < a`) THEN
    MATCH_MP_TAC REAL_LT_RMUL THEN ASM_REAL_ARITH_TAC;
    MP_TAC(ISPECL [`(s / &2) % b:real^2`; `mu:real`] (ASSUME
       `!y t. y IN ball(vec 0,s) /\ &0 <= t /\ t <= &1
              ==> (g:real^2->real^2)(t % y) = x + t % (g y - x)`)) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[IN_BALL_0; NORM_MUL; REAL_MUL_RID] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[VECTOR_MUL_ASSOC] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "mu" THEN
    REWRITE_TAC[VECTOR_ARITH `(&1 - l) % x + l % (x + v):real^2 = x + l % v`] THEN
    REWRITE_TAC[VECTOR_MUL_ASSOC; REAL_MUL_ASSOC];
    DISCH_TAC THEN MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
     [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    ASM_REWRITE_TAC[REAL_LT_LE] THEN DISCH_THEN(ASSUME_TAC o SYM) THEN
    UNDISCH_TAC `~(y:real^2 = x)` THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `lam = &0` SUBST_ALL_TAC THENL
     [UNDISCH_TAC `lam * r * inv(norm(P - x:real^2)) = mu` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[REAL_ENTIRE; REAL_INV_EQ_0] THEN ASM_REAL_ARITH_TAC;
      ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC]]);;

(* The conical picture of a curve crossing in the plane: near x the two     *)
(* curves are two radial segments each, and the complement of k near x has  *)
(* two sides, the two segments of j lying on different sides.               *)

(* A curve-crossing chart can be taken inside any open neighbourhood. *)

let MOI_S4P_CROSS_RESTRICT = prove
 (`!(j:real^2->bool) k x ww.
     pl_curve_crossing_at (:real^2) j k x /\ open ww /\ x IN ww
     ==> ?u f g. open u /\ u SUBSET ww /\ x IN u /\
                 pl_homeomorphism (u,IMAGE f u) (f,g) /\ open (IMAGE f u) /\
                 f x = vec 0 /\
                 IMAGE f (j INTER u) = IMAGE f u INTER {y:real^2 | y$1 = &0} /\
                 IMAGE f (k INTER u) = IMAGE f u INTER {y:real^2 | y$2 = &0}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_curve_crossing_at; SUBTOPOLOGY_UNIV; GSYM OPEN_IN] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `u:real^2->bool` (X_CHOOSE_THEN `f:real^2->real^2`
     (X_CHOOSE_THEN `g:real^2->real^2` STRIP_ASSUME_TAC))) STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [pl_homeomorphism]) THEN
  SUBGOAL_THEN `!y z. y IN u /\ z IN u /\ (f:real^2->real^2) y = f z ==> y = z` ASSUME_TAC THENL
   [UNDISCH_TAC `homeomorphism (u,IMAGE f u) (f:real^2->real^2,g)` THEN
    REWRITE_TAC[homeomorphism] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `open (IMAGE (f:real^2->real^2) (u INTER ww))` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S4P_HOMEO_OPEN_IMAGE THEN
    MAP_EVERY EXISTS_TAC [`g:real^2->real^2`; `IMAGE (f:real^2->real^2) u`; `u:real^2->bool`] THEN
    ASM_SIMP_TAC[OPEN_INTER; INTER_SUBSET] THEN
    ONCE_REWRITE_TAC[HOMEOMORPHISM_SYM] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`u INTER ww:real^2->bool`; `f:real^2->real^2`; `g:real^2->real^2`] THEN
  ASM_SIMP_TAC[OPEN_INTER; INTER_SUBSET; IN_INTER] THEN REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `pl_homeomorphism (u,IMAGE f u) (f:real^2->real^2,g)` THEN
    REWRITE_TAC[pl_homeomorphism] THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC HOMEOMORPHISM_OF_SUBSETS THEN
      MAP_EVERY EXISTS_TAC [`u:real^2->bool`; `IMAGE (f:real^2->real^2) u`] THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      MATCH_MP_TAC PL_MAP_ON_SUBSET THEN EXISTS_TAC `u:real^2->bool` THEN
      ASM_SIMP_TAC[INTER_SUBSET; LOCALLY_POLYHEDRAL_OPEN; OPEN_INTER];
      MATCH_MP_TAC PL_MAP_ON_SUBSET THEN EXISTS_TAC `IMAGE (f:real^2->real^2) u` THEN
      ASM_SIMP_TAC[LOCALLY_POLYHEDRAL_OPEN] THEN SET_TAC[]];
    UNDISCH_TAC `IMAGE (f:real^2->real^2) (j INTER u) = IMAGE f u INTER {y:real^2 | y$1 = &0}` THEN
    UNDISCH_TAC `!y z. y IN u /\ z IN u /\ (f:real^2->real^2) y = f z ==> y = z` THEN
    SET_TAC[];
    UNDISCH_TAC `IMAGE (f:real^2->real^2) (k INTER u) = IMAGE f u INTER {y:real^2 | y$2 = &0}` THEN
    UNDISCH_TAC `!y z. y IN u /\ z IN u /\ (f:real^2->real^2) y = f z ==> y = z` THEN
    SET_TAC[]]);;

(* A map that is radially affine and injective near 0 sends opposite      *)
(* radii to different radial segments.                                     *)

let MOI_S4P_RAD_DISTINCT = prove
 (`!(g:real^N->real^M) x V r0 b s rr.
     (!y t. y IN ball(vec 0,r0) /\ &0 <= t /\ t <= &1 ==> g(t % y) = x + t % (g y - x)) /\
     (!y z. y IN V /\ z IN V /\ g y = g z ==> y = z) /\ ball(vec 0,r0) SUBSET V /\
     ~(b = vec 0) /\ &0 < s /\ s * norm b < r0 /\ &0 < rr /\
     ~(g(s % b) = x) /\ ~(g((--s) % b) = x)
     ==> ~(x + rr % inv(norm(g(s % b) - x)) % (g(s % b) - x) =
           x + rr % inv(norm(g((--s) % b) - x)) % (g((--s) % b) - x))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `P = (g:real^N->real^M)(s % b) - x` THEN
  ABBREV_TAC `Q = (g:real^N->real^M)((--s) % b) - x` THEN
  SUBGOAL_THEN `&0 < norm(P:real^M) /\ &0 < norm(Q:real^M)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "P" THEN EXPAND_TAC "Q" THEN ASM_REWRITE_TAC[NORM_POS_LT; VECTOR_SUB_EQ];
    ALL_TAC] THEN
  REWRITE_TAC[VECTOR_ARITH `x + a:real^M = x + b <=> a = b`; VECTOR_MUL_ASSOC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `Q:real^M = (norm Q / norm(P:real^M)) % P` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o AP_TERM `((%) (norm(Q:real^M) / rr)):real^M->real^M`) THEN
    REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
    SUBGOAL_THEN `norm(Q:real^M) / rr * rr * inv(norm Q) = &1 /\
                  norm(Q:real^M) / rr * rr * inv(norm(P:real^M)) = norm Q / norm P`
    (fun th -> REWRITE_TAC[th; VECTOR_MUL_LID]) THENL
     [UNDISCH_TAC `&0 < rr` THEN UNDISCH_TAC `&0 < norm(P:real^M)` THEN
      UNDISCH_TAC `&0 < norm(Q:real^M)` THEN CONV_TAC REAL_FIELD;
      MESON_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `lam = norm(Q:real^M) / norm(P:real^M)` THEN
  SUBGOAL_THEN `&0 < lam` ASSUME_TAC THENL
   [EXPAND_TAC "lam" THEN MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `t = min (&1) (inv lam)` THEN
  SUBGOAL_THEN `&0 < t /\ t <= &1 /\ &0 < t * lam /\ t * lam <= &1` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < inv lam /\ inv lam * lam = &1` STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_INV_EQ; REAL_MUL_LINV; REAL_LT_IMP_NZ]; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < t /\ t <= &1 /\ t <= inv lam` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "t" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_MUL] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv lam * lam` THEN
    CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!c. abs c <= s ==> (c % b:real^N) IN ball(vec 0,r0)` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[IN_BALL_0; NORM_MUL] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `s * norm(b:real^N)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[NORM_POS_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `(s % b:real^N) IN ball(vec 0,r0) /\ ((--s) % b:real^N) IN ball(vec 0,r0) /\
                ((t * lam) % (s % b):real^N) IN ball(vec 0,r0) /\
                (t % ((--s) % b):real^N) IN ball(vec 0,r0)` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[VECTOR_MUL_ASSOC] THEN REPEAT CONJ_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_NEG] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`] THEN
    TRY REAL_ARITH_TAC THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(g:real^N->real^M)((t * lam) % (s % b)) = x + (t * lam) % P /\
                g(t % ((--s) % b)) = x + t % Q` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "P" THEN EXPAND_TAC "Q" THEN CONJ_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `ball:real^N#real->real^N->bool`)) (concl th) &&
      can (find_term ((=) `g:real^N->real^M`)) (concl th))) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `(t * lam) % (s % b):real^N = t % ((--s) % b)` MP_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `V:real^N->bool`)) (concl th))) THEN
    REPEAT CONJ_TAC THENL
     [ASM SET_TAC[]; ASM SET_TAC[];
      ASM_REWRITE_TAC[VECTOR_MUL_ASSOC]];
    ALL_TAC] THEN
  REWRITE_TAC[VECTOR_MUL_ASSOC; VECTOR_MUL_RCANCEL] THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 < a /\ b < &0 ==> ~(a = b)`) THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_MUL];
    REWRITE_TAC[REAL_MUL_RNEG; REAL_NEG_LT0] THEN ASM_SIMP_TAC[REAL_LT_MUL]]);;

let MOI_S4P_CROSS_CONE = prove
 (`!(j:real^2->bool) k x ww.
     pl_curve_crossing_at (:real^2) j k x /\ open ww /\ x IN ww
     ==> ?r d1 d2 e1 e2 n g1 g2.
           &0 < r /\
           ~(d1 = vec 0) /\ ~(d2 = vec 0) /\ ~(e1 = vec 0) /\ ~(e2 = vec 0) /\
           j INTER cball(x,r) =
           segment[x,x + r % inv(norm d1) % d1] UNION segment[x,x + r % inv(norm d2) % d2] /\
           k INTER cball(x,r) =
           segment[x,x + r % inv(norm e1) % e1] UNION segment[x,x + r % inv(norm e2) % e2] /\
           j INTER k INTER cball(x,r) = {x} /\
           open n /\ cball(x,r) SUBSET n /\
           n DIFF k = g1 UNION g2 /\ DISJOINT g1 g2 /\ open g1 /\ open g2 /\
           connected g1 /\ connected g2 /\
           x IN closure g1 /\ x IN closure g2 /\
           segment[x,x + r % inv(norm d1) % d1] DELETE x SUBSET g1 /\
           segment[x,x + r % inv(norm d2) % d2] DELETE x SUBSET g2 /\
           n SUBSET ww /\
           ~(x + r % inv(norm d1) % d1 = x + r % inv(norm d2) % d2) /\
           ~(x + r % inv(norm e1) % e1 = x + r % inv(norm e2) % e2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`j:real^2->bool`; `k:real^2->bool`; `x:real^2`; `ww:real^2->bool`]
    MOI_S4P_CROSS_RESTRICT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^2->bool` (X_CHOOSE_THEN `f:real^2->real^2`
    (X_CHOOSE_THEN `g:real^2->real^2` STRIP_ASSUME_TAC))) THEN
  ABBREV_TAC `V = IMAGE (f:real^2->real^2) u` THEN
  SUBGOAL_THEN `(g:real^2->real^2) (vec 0) = x` ASSUME_TAC THENL
   [UNDISCH_TAC `pl_homeomorphism (u,V) (f:real^2->real^2,g)` THEN
    REWRITE_TAC[pl_homeomorphism; homeomorphism] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:real^2->bool`; `g:real^2->real^2`; `vec 0:real^2`] MOI_S4P_RAD_AFF) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_MESON_TAC[pl_homeomorphism]; ALL_TAC] THEN
    ASM_SIMP_TAC[INTERIOR_OPEN] THEN UNDISCH_TAC `(f:real^2->real^2) x = vec 0` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN EXPAND_TAC "V" THEN ASM SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[VECTOR_ADD_LID; VECTOR_SUB_RZERO] THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r0:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!y z. y IN V /\ z IN V /\ (g:real^2->real^2) y = g z ==> y = z`
  ASSUME_TAC THENL
   [UNDISCH_TAC `pl_homeomorphism (u,V) (f:real^2->real^2,g)` THEN
    REWRITE_TAC[pl_homeomorphism; homeomorphism] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y. y IN V ==> (g:real^2->real^2) y IN u /\ f (g y) = y`
  ASSUME_TAC THENL
   [UNDISCH_TAC `pl_homeomorphism (u,V) (f:real^2->real^2,g)` THEN
    REWRITE_TAC[pl_homeomorphism; homeomorphism] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!w. w IN u ==> (g:real^2->real^2) (f w) = w` ASSUME_TAC THENL
   [UNDISCH_TAC `pl_homeomorphism (u,V) (f:real^2->real^2,g)` THEN
    REWRITE_TAC[pl_homeomorphism; homeomorphism] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!(c:real^2->bool) i y.
       IMAGE (f:real^2->real^2) (c INTER u) = V INTER {y:real^2 | y$i = &0} /\ y IN V
       ==> ((g:real^2->real^2) y IN c <=> y$i = &0)`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    EQ_TAC THEN DISCH_TAC THENL
     [SUBGOAL_THEN `(y:real^2) IN IMAGE (f:real^2->real^2) (c INTER u)` MP_TAC THENL
       [REWRITE_TAC[IN_IMAGE; IN_INTER] THEN EXISTS_TAC `(g:real^2->real^2) y` THEN
        ASM_SIMP_TAC[];
        ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN SIMP_TAC[]];
      SUBGOAL_THEN `(y:real^2) IN IMAGE (f:real^2->real^2) (c INTER u)` MP_TAC THENL
       [ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM]; ALL_TAC] THEN
      REWRITE_TAC[IN_IMAGE; IN_INTER] THEN
      DISCH_THEN(X_CHOOSE_THEN `w:real^2` STRIP_ASSUME_TAC) THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y. y IN V ==> ((g:real^2->real^2) y IN j <=> y$1 = &0) /\
                               (g y IN k <=> y$2 = &0)` ASSUME_TAC THENL
   [X_GEN_TAC `y:real^2` THEN DISCH_TAC THEN CONJ_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `i:num`)) (concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `ball(vec 0:real^2,r0 / &2) SUBSET ball(vec 0,r0)` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_BALL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `n = IMAGE (g:real^2->real^2) (ball(vec 0,r0 / &2))` THEN
  SUBGOAL_THEN `!w:real^2->bool. w SUBSET ball(vec 0,r0) /\ open w
                                 ==> open (IMAGE (g:real^2->real^2) w)` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_S4P_HOMEO_OPEN_IMAGE THEN
    MAP_EVERY EXISTS_TAC [`f:real^2->real^2`; `u:real^2->bool`; `V:real^2->bool`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[pl_homeomorphism]; ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `open (n:real^2->bool) /\ (x:real^2) IN n` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "n" THEN CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[OPEN_BALL];
      REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `vec 0:real^2` THEN
      ASM_REWRITE_TAC[CENTRE_IN_BALL] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!w. abs w < r0 ==> (w % basis 1:real^2) IN V /\ (w % basis 2:real^2) IN V`
  ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN
    UNDISCH_TAC `ball(vec 0:real^2,r0) SUBSET V` THEN REWRITE_TAC[SUBSET] THEN
    DISCH_THEN(fun th -> CONJ_TAC THEN MATCH_MP_TAC th) THEN
    ASM_REWRITE_TAC[IN_BALL_0; MOI_S4P_AXIS2];
    ALL_TAC] THEN
  SUBGOAL_THEN `(vec 0:real^2) IN V` ASSUME_TAC THENL
   [UNDISCH_TAC `ball(vec 0:real^2,r0) SUBSET V` THEN REWRITE_TAC[SUBSET] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[CENTRE_IN_BALL];
    ALL_TAC] THEN
  SUBGOAL_THEN `!w. ~(w = &0) /\ abs w < r0
                    ==> ~((g:real^2->real^2)(w % basis 1) = x) /\ ~(g(w % basis 2) = x)`
  ASSUME_TAC THENL
   [GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THEN DISCH_TAC THENL
     [SUBGOAL_THEN `w % basis 1:real^2 = vec 0` MP_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
          can (find_term ((=) `y = z:real^2`)) (concl th))) THEN
        ASM_SIMP_TAC[];
        ASM_SIMP_TAC[VECTOR_MUL_EQ_0; BASIS_NONZERO; DIMINDEX_2; ARITH]];
      SUBGOAL_THEN `w % basis 2:real^2 = vec 0` MP_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
          can (find_term ((=) `y = z:real^2`)) (concl th))) THEN
        ASM_SIMP_TAC[];
        ASM_SIMP_TAC[VECTOR_MUL_EQ_0; BASIS_NONZERO; DIMINDEX_2; ARITH]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y. y IN ball(vec 0,r0)
                    ==> ((g:real^2->real^2) y IN j <=> ?t. y = t % basis 2) /\
                        (g y IN k <=> ?t. y = t % basis 1)` ASSUME_TAC THENL
   [X_GEN_TAC `y:real^2` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(y:real^2) IN V` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN CONJ_TAC THEN EQ_TAC THEN STRIP_TAC THEN
    ASM_MESON_TAC[MOI_S4P_AXIS2];
    ALL_TAC] THEN
  SUBGOAL_THEN `norm(basis 1:real^2) = &1 /\ norm(basis 2:real^2) = &1 /\
                norm(--basis 1:real^2) = &1 /\ norm(--basis 2:real^2) = &1`
  STRIP_ASSUME_TAC THENL
   [SIMP_TAC[NORM_NEG; NORM_BASIS; DIMINDEX_2; ARITH]; ALL_TAC] THEN
  SUBGOAL_THEN
   `~((g:real^2->real^2)((r0 / &2) % basis 2) = x) /\ ~(g((--(r0 / &2)) % basis 2) = x) /\
    ~(g((r0 / &2) % basis 1) = x) /\ ~(g((--(r0 / &2)) % basis 1) = x)`
  STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM((fun th -> MP_TAC(SPEC `r0 / &2` th) THEN MP_TAC(SPEC `--(r0 / &2)` th)) o
      check (fun th -> is_forall(concl th) && can (find_term ((=) `basis 1:real^2`)) (concl th) &&
                       can (find_term ((=) `w:real`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `n:real^2->bool` OPEN_CONTAINS_CBALL) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `x:real^2`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `r = min e (min (norm((g:real^2->real^2)((r0 / &2) % basis 2) - x))
                       (min (norm(g((--(r0 / &2)) % basis 2) - x))
                       (min (norm(g((r0 / &2) % basis 1) - x))
                            (norm(g((--(r0 / &2)) % basis 1) - x))))) / &2` THEN
  SUBGOAL_THEN
   `&0 < r /\ r < norm((g:real^2->real^2)((r0 / &2) % basis 2) - x) /\
    r < norm(g((--(r0 / &2)) % basis 2) - x) /\ r < norm(g((r0 / &2) % basis 1) - x) /\
    r < norm(g((--(r0 / &2)) % basis 1) - x) /\ cball(x,r) SUBSET n`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN
     `&0 < norm((g:real^2->real^2)((r0 / &2) % basis 2) - x) /\
      &0 < norm(g((--(r0 / &2)) % basis 2) - x) /\ &0 < norm(g((r0 / &2) % basis 1) - x) /\
      &0 < norm(g((--(r0 / &2)) % basis 1) - x)` MP_TAC THENL
     [ASM_REWRITE_TAC[NORM_POS_LT; VECTOR_SUB_EQ]; ALL_TAC] THEN
    EXPAND_TAC "r" THEN STRIP_TAC THEN REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `cball(x:real^2,e)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_CBALL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `cball(x:real^2,r) SUBSET IMAGE (g:real^2->real^2) (ball(vec 0,r0))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `n:real^2->bool` THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "n" THEN
    MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`g:real^2->real^2`; `x:real^2`; `r0:real`; `basis 2:real^2`;
                 `j:real^2->bool`; `r:real`] MOI_S4P_RADIAL_AXIS) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; DISCH_TAC] THEN
  MP_TAC(ISPECL [`g:real^2->real^2`; `x:real^2`; `r0:real`; `basis 1:real^2`;
                 `k:real^2->bool`; `r:real`] MOI_S4P_RADIAL_AXIS) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; DISCH_TAC] THEN
  ABBREV_TAC `g1 = IMAGE (g:real^2->real^2) (ball(vec 0,r0 / &2) INTER {y:real^2 | y$2 > &0})` THEN
  ABBREV_TAC `g2 = IMAGE (g:real^2->real^2) (ball(vec 0,r0 / &2) INTER {y:real^2 | y$2 < &0})` THEN
  SUBGOAL_THEN
   `segment[x,x + r % inv(norm((g:real^2->real^2)((r0 / &2) % basis 2) - x)) %
                        (g((r0 / &2) % basis 2) - x)] DELETE x SUBSET g1 /\
    segment[x,x + r % inv(norm(g((--(r0 / &2)) % basis 2) - x)) %
                        (g((--(r0 / &2)) % basis 2) - x)] DELETE x SUBSET g2`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN GEN_REWRITE_TAC I [SUBSET] THEN
    REWRITE_TAC[IN_DELETE] THEN X_GEN_TAC `y:real^2` THEN STRIP_TAC THENL
     [MP_TAC(ISPECL [`g:real^2->real^2`; `x:real^2`; `r0:real`; `basis 2:real^2`;
                     `r:real`; `y:real^2`] MOI_S4P_SEG_PT) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `m:real` STRIP_ASSUME_TAC) THEN
      EXPAND_TAC "g1" THEN REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `m % basis 2:real^2` THEN
      ASM_REWRITE_TAC[IN_INTER; IN_BALL_0; IN_ELIM_THM; MOI_S4P_AXIS2; real_gt] THEN
      ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC;
      MP_TAC(REWRITE_RULE[VECTOR_ARITH `(r0 / &2) % --b:real^2 = (--(r0 / &2)) % b`]
        (ISPECL [`g:real^2->real^2`; `x:real^2`; `r0:real`; `--basis 2:real^2`;
                 `r:real`; `y:real^2`] MOI_S4P_SEG_PT)) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `m:real` STRIP_ASSUME_TAC) THEN
      EXPAND_TAC "g2" THEN REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `(--m) % basis 2:real^2` THEN
      ASM_REWRITE_TAC[IN_INTER; IN_BALL_0; IN_ELIM_THM; MOI_S4P_AXIS2;
                      VECTOR_ARITH `(--m) % b:real^2 = m % --b`] THEN
      ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z:real^2. z IN ball(vec 0,r0 / &2) ==> z IN V` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    UNDISCH_TAC `ball(vec 0:real^2,r0) SUBSET V` THEN
    UNDISCH_TAC `ball(vec 0:real^2,r0 / &2) SUBSET ball(vec 0,r0)` THEN
    UNDISCH_TAC `(z:real^2) IN ball(vec 0,r0 / &2)` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^2. y IN n ==> ?z. z IN ball(vec 0,r0 / &2) /\ y = (g:real^2->real^2) z`
  ASSUME_TAC THENL
   [EXPAND_TAC "n" THEN REWRITE_TAC[IN_IMAGE] THEN MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `j INTER k INTER cball(x:real^2,r) = {x}` ASSUME_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `y:real^2` THEN
    REWRITE_TAC[IN_INTER; IN_SING] THEN EQ_TAC THENL
     [STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `y:real^2` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `n:real^2->bool`)) (concl th))) THEN
      ANTS_TAC THENL
       [MAP_EVERY UNDISCH_TAC [`(y:real^2) IN cball(x,r)`; `cball(x:real^2,r) SUBSET n`] THEN
        SET_TAC[];
        ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `z:real^2` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `z:real^2 = vec 0` (fun th -> ASM_REWRITE_TAC[th]) THEN
      SUBGOAL_THEN `(z:real^2) IN V` ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `(z:real^2)$1 = &0 /\ z$2 = &0` MP_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VEC_COMPONENT];
      DISCH_THEN SUBST1_TAC THEN
      SUBGOAL_THEN `(vec 0:real^2) IN V` ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[CENTRE_IN_CBALL] THEN
      CONJ_TAC THENL [ALL_TAC; CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC]] THEN
      UNDISCH_TAC `(g:real^2->real^2) (vec 0) = x` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      ASM_SIMP_TAC[VEC_COMPONENT]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(n:real^2->bool) DIFF k = g1 UNION g2` ASSUME_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `y:real^2` THEN
    REWRITE_TAC[IN_DIFF; IN_UNION] THEN EXPAND_TAC "g1" THEN EXPAND_TAC "g2" THEN
    EXPAND_TAC "n" THEN REWRITE_TAC[IN_IMAGE; IN_INTER; IN_ELIM_THM; real_gt] THEN
    EQ_TAC THENL
     [DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `z:real^2` STRIP_ASSUME_TAC) ASSUME_TAC) THEN
      SUBGOAL_THEN `(z:real^2) IN V` ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `~((z:real^2)$2 = &0)` MP_TAC THENL
       [UNDISCH_TAC `~((y:real^2) IN k)` THEN ASM_SIMP_TAC[];
        ALL_TAC] THEN
      DISCH_THEN(DISJ_CASES_TAC o MATCH_MP (REAL_ARITH `~(a = &0) ==> &0 < a \/ a < &0`)) THENL
       [DISJ1_TAC; DISJ2_TAC] THEN EXISTS_TAC `z:real^2` THEN ASM_REWRITE_TAC[];
      STRIP_TAC THEN
      (CONJ_TAC THENL [EXISTS_TAC `x':real^2` THEN ASM_REWRITE_TAC[]; ALL_TAC]) THEN
      ASM_REWRITE_TAC[] THEN
      (SUBGOAL_THEN `(x':real^2) IN V` ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC]) THEN
      ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `DISJOINT (g1:real^2->bool) g2` ASSUME_TAC THENL
   [EXPAND_TAC "g1" THEN EXPAND_TAC "g2" THEN
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_IMAGE; NOT_IN_EMPTY; IN_ELIM_THM; real_gt] THEN
    X_GEN_TAC `y:real^2` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `z1:real^2` STRIP_ASSUME_TAC)
                               (X_CHOOSE_THEN `z2:real^2` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `z1:real^2 = z2` MP_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (find_term ((=) `y = z:real^2`)) (concl th))) THEN
      ASM_SIMP_TAC[] THEN
      MAP_EVERY UNDISCH_TAC [`y = (g:real^2->real^2) z1`; `y = (g:real^2->real^2) z2`] THEN
      MESON_TAC[];
      DISCH_THEN SUBST_ALL_TAC THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `open (g1:real^2->bool) /\ open (g2:real^2->bool)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "g1" THEN EXPAND_TAC "g2" THEN CONJ_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "open")) (concl th))) THEN
    SIMP_TAC[OPEN_INTER; OPEN_BALL; OPEN_HALFSPACE_COMPONENT_GT; OPEN_HALFSPACE_COMPONENT_LT] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `ball(vec 0:real^2,r0 / &2)` THEN
    ASM_REWRITE_TAC[INTER_SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN `connected (g1:real^2->bool) /\ connected (g2:real^2->bool)` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `(g:real^2->real^2) continuous_on ball(vec 0,r0 / &2)` ASSUME_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `V:real^2->bool` THEN
      CONJ_TAC THENL
       [UNDISCH_TAC `pl_homeomorphism (u,V) (f:real^2->real^2,g)` THEN
        SIMP_TAC[pl_homeomorphism; homeomorphism];
        REWRITE_TAC[SUBSET] THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    EXPAND_TAC "g1" THEN EXPAND_TAC "g2" THEN CONJ_TAC THEN
    MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN
    (CONJ_TAC THENL
      [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `ball(vec 0:real^2,r0 / &2)` THEN
       ASM_REWRITE_TAC[INTER_SUBSET];
       MATCH_MP_TAC CONVEX_CONNECTED THEN
       SIMP_TAC[CONVEX_INTER; CONVEX_BALL; CONVEX_HALFSPACE_COMPONENT_GT;
                CONVEX_HALFSPACE_COMPONENT_LT]]);
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^2) IN closure g1 /\ x IN closure g2` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[CLOSURE_APPROACHABLE] THEN CONJ_TAC THEN X_GEN_TAC `e':real` THEN
    DISCH_TAC THENL
     [EXISTS_TAC `x + min (e' / &2) r % inv(norm((g:real^2->real^2)((r0 / &2) % basis 2) - x)) %
                    (g((r0 / &2) % basis 2) - x)`;
      EXISTS_TAC `x + min (e' / &2) r % inv(norm((g:real^2->real^2)((--(r0 / &2)) % basis 2) - x)) %
                    (g((--(r0 / &2)) % basis 2) - x)`] THEN
    (CONJ_TAC THENL
      [FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
         can (find_term (fun t -> is_const t && fst(dest_const t) = "DELETE")) (concl th))) THEN
       REWRITE_TAC[IN_DELETE; IN_SEGMENT] THEN CONJ_TAC THENL
        [EXISTS_TAC `min (e' / &2) r / r` THEN REPEAT CONJ_TAC THENL
          [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
           ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
           REWRITE_TAC[VECTOR_ARITH `(&1 - t) % x + t % (x + v):real^2 = x + t % v`] THEN
           AP_TERM_TAC THEN REWRITE_TAC[VECTOR_MUL_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
           UNDISCH_TAC `&0 < r` THEN CONV_TAC REAL_FIELD];
         REWRITE_TAC[VECTOR_ARITH `x + v:real^2 = x <=> v = vec 0`; VECTOR_MUL_EQ_0] THEN
         ASM_REWRITE_TAC[VECTOR_SUB_EQ; REAL_INV_EQ_0; NORM_EQ_0] THEN ASM_REAL_ARITH_TAC];
       REWRITE_TAC[dist; VECTOR_ARITH `(x + v) - x:real^2 = v`; NORM_MUL] THEN
       REWRITE_TAC[REAL_ABS_INV; REAL_ABS_NORM] THEN
       SUBGOAL_THEN `&0 < norm((g:real^2->real^2)((r0 / &2) % basis 2) - x) /\
                     &0 < norm(g((--(r0 / &2)) % basis 2) - x)` STRIP_ASSUME_TAC THENL
        [ASM_REWRITE_TAC[NORM_POS_LT; VECTOR_SUB_EQ]; ALL_TAC] THEN
       ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ; REAL_MUL_RID; GSYM REAL_MUL_ASSOC] THEN
       ASM_REAL_ARITH_TAC]);
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!b. b = basis 1 \/ b = basis 2
        ==> ~(x + r % inv(norm((g:real^2->real^2)((r0 / &2) % b) - x)) %
                       (g((r0 / &2) % b) - x) =
              x + r % inv(norm(g((--(r0 / &2)) % b) - x)) % (g((--(r0 / &2)) % b) - x))`
  ASSUME_TAC THENL
   [X_GEN_TAC `b:real^2` THEN DISCH_TAC THEN MATCH_MP_TAC MOI_S4P_RAD_DISTINCT THEN
    MAP_EVERY EXISTS_TAC [`V:real^2->bool`; `r0:real`] THEN
    FIRST_X_ASSUM(DISJ_CASES_THEN SUBST1_TAC) THEN
    ASM_SIMP_TAC[BASIS_NONZERO; DIMINDEX_2; ARITH; NORM_BASIS] THEN
    (CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ASM_REAL_ARITH_TAC]);
    ALL_TAC] THEN
  SUBGOAL_THEN `(n:real^2->bool) SUBSET ww` ASSUME_TAC THENL
   [EXPAND_TAC "n" THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
    X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN
    MATCH_MP_TAC(SET_RULE `!u. (y:real^2) IN u /\ u SUBSET ww ==> y IN ww`) THEN
    EXISTS_TAC `u:real^2->bool` THEN
    UNDISCH_TAC `!y:real^2. y IN V ==> (g:real^2->real^2) y IN u /\ (f:real^2->real^2) (g y) = y` THEN
    UNDISCH_TAC `!z:real^2. z IN ball(vec 0,r0 / &2) ==> z IN V` THEN
    UNDISCH_TAC `(z:real^2) IN ball(vec 0,r0 / &2)` THEN
    UNDISCH_TAC `(u:real^2->bool) SUBSET ww` THEN MESON_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`r:real`; `(g:real^2->real^2)((r0 / &2) % basis 2) - x`;
    `(g:real^2->real^2)((--(r0 / &2)) % basis 2) - x`;
    `(g:real^2->real^2)((r0 / &2) % basis 1) - x`;
    `(g:real^2->real^2)((--(r0 / &2)) % basis 1) - x`;
    `n:real^2->bool`; `g1:real^2->bool`; `g2:real^2->bool`] THEN
  ASM_REWRITE_TAC[VECTOR_SUB_EQ] THEN ASM_SIMP_TAC[VECTOR_SUB_EQ]);;

(* ------------------------------------------------------------------------- *)
(* Local structure of segments and triangle boundaries near a              *)
(* point (radial segments), used for the corner analysis of the 2D push.   *)
(* ------------------------------------------------------------------------- *)


let MOI_S4P_SEG_LOCAL_END = prove
 (`!(a:real^N) b r.
     ~(a = b) /\ &0 < r /\ r <= norm(b - a)
     ==> segment[a,b] INTER cball(a,r) = segment[a,a + r % inv(norm(b - a)) % (b - a)]`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < norm(b - a:real^N)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT; VECTOR_SUB_EQ]; ALL_TAC] THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `y:real^N` THEN
  REWRITE_TAC[IN_INTER; IN_CBALL; IN_SEGMENT; dist] THEN EQ_TAC THENL
   [DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC) ASSUME_TAC) THEN
    EXISTS_TAC `t * norm(b - a:real^N) / r` THEN
    UNDISCH_TAC `norm(a - y:real^N) <= r` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[VECTOR_ARITH `a - ((&1 - t) % a + t % b):real^N = --(t % (b - a))`;
                NORM_NEG; NORM_MUL] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 <= t ==> abs t = t`] THEN DISCH_TAC THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LE_DIV; NORM_POS_LE; REAL_LT_IMP_LE];
      REWRITE_TAC[REAL_ARITH `t * n / r = (t * n) / r`] THEN
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_MUL_LID];
      REWRITE_TAC[VECTOR_ARITH `(&1 - s) % a + s % (a + v):real^N = a + s % v`;
                  VECTOR_ARITH `(&1 - t) % a + t % b:real^N = a + t % (b - a)`] THEN
      AP_TERM_TAC THEN REWRITE_TAC[VECTOR_MUL_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      UNDISCH_TAC `&0 < r` THEN UNDISCH_TAC `&0 < norm(b - a:real^N)` THEN
      CONV_TAC REAL_FIELD];
    DISCH_THEN(X_CHOOSE_THEN `s:real` STRIP_ASSUME_TAC) THEN CONJ_TAC THENL
     [EXISTS_TAC `s * r / norm(b - a:real^N)` THEN ASM_REWRITE_TAC[] THEN
      REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LE_DIV; NORM_POS_LE; REAL_LT_IMP_LE];
        REWRITE_TAC[REAL_ARITH `t * n / r = (t * n) / r`] THEN
        ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_MUL_LID] THEN
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1 * r` THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
        REWRITE_TAC[VECTOR_ARITH `(&1 - s) % a + s % (a + v):real^N = a + s % v`;
                    VECTOR_ARITH `(&1 - t) % a + t % b:real^N = a + t % (b - a)`] THEN
        AP_TERM_TAC THEN REWRITE_TAC[VECTOR_MUL_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
        UNDISCH_TAC `&0 < norm(b - a:real^N)` THEN CONV_TAC REAL_FIELD];
      ASM_REWRITE_TAC[VECTOR_ARITH `a - ((&1 - s) % a + s % (a + v)):real^N = --(s % v)`] THEN
      REWRITE_TAC[NORM_NEG; NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM] THEN
      ASM_SIMP_TAC[REAL_ARITH `&0 <= t ==> abs t = t`; REAL_ARITH `&0 < r ==> abs r = r`] THEN
      ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ; GSYM REAL_MUL_ASSOC; REAL_MUL_RID] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1 * r` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]]]);;

let MOI_S4P_SEG_LOCAL_MID = prove
 (`!(a:real^N) b x r.
     x IN segment[a,b] /\ ~(x = a) /\ ~(x = b) /\ &0 < r /\
     r <= norm(a - x) /\ r <= norm(b - x)
     ==> segment[a,b] INTER cball(x,r) =
         segment[x,x + r % inv(norm(b - x)) % (b - x)] UNION
         segment[x,x + r % inv(norm(a - x)) % (a - x)]`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o LAND_CONV)
    [SYM(MATCH_MP UNION_SEGMENT th)]) THEN
  REWRITE_TAC[SET_RULE `((s:real^N->bool) UNION t) INTER u = (s INTER u) UNION (t INTER u)`] THEN
  GEN_REWRITE_TAC RAND_CONV [UNION_COMM] THEN
  BINOP_TAC THENL
   [GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [SEGMENT_SYM] THEN
    MATCH_MP_TAC MOI_S4P_SEG_LOCAL_END THEN
    ASM_MESON_TAC[];
    MATCH_MP_TAC MOI_S4P_SEG_LOCAL_END THEN ASM_MESON_TAC[]]);;

let MOI_S4P_FAR_CLOSED = prove
 (`!(s:real^N->bool) x. closed s /\ ~(x IN s) ==> ?r. &0 < r /\ s INTER cball(x,r) = {}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `x:real^N`] SEPARATE_POINT_CLOSED) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `d / &2` THEN ASM_REWRITE_TAC[REAL_HALF] THEN
  REWRITE_TAC[EXTENSION; IN_INTER; IN_CBALL; NOT_IN_EMPTY] THEN
  X_GEN_TAC `y:real^N` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `y:real^N`) THEN ASM_REWRITE_TAC[] THEN
  ASM_REAL_ARITH_TAC);;

(* Two segments from x of the same positive length meet only in x unless  *)
(* they coincide; a radial segment inside two radial segments is one of    *)
(* them; shrinking a radial segment.                                       *)

let MOI_S4P_RAD_MEET = prove
 (`!(x:real^N) b1 b2 r.
     &0 < r /\ norm(b1 - x) = r /\ norm(b2 - x) = r /\ ~(b1 = b2)
     ==> segment[x,b1] INTER segment[x,b2] = {x}`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `z:real^N` THEN
  REWRITE_TAC[IN_INTER; IN_SING] THEN EQ_TAC THENL
   [ALL_TAC; DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[ENDS_IN_SEGMENT]] THEN
  REWRITE_TAC[IN_SEGMENT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `s:real` STRIP_ASSUME_TAC)
                             (X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `(&1 - s) % x + s % b1 = (&1 - t) % x + t % (b2:real^N)` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `norm(((&1 - s) % x + s % b1) - x:real^N) = s * r /\
                norm(((&1 - t) % x + t % b2) - x:real^N) = t * r` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[VECTOR_ARITH `((&1 - s) % x + s % b) - x:real^N = s % (b - x)`; NORM_MUL] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 <= s ==> abs s = s`];
    ALL_TAC] THEN
  SUBGOAL_THEN `s:real = t` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC REAL_EQ_RCANCEL_IMP THEN EXISTS_TAC `r:real` THEN
    ASM_MESON_TAC[REAL_LT_IMP_NZ];
    ALL_TAC] THEN
  ASM_CASES_TAC `t = &0` THENL
   [ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `t % (b1 - x) = t % (b2 - x:real^N)` MP_TAC THENL
   [UNDISCH_TAC `(&1 - t) % x + t % b1 = (&1 - t) % x + t % (b2:real^N)` THEN
    VECTOR_ARITH_TAC;
    ASM_REWRITE_TAC[VECTOR_MUL_LCANCEL; VECTOR_ARITH `b1 - x = b2 - x <=> b1:real^N = b2`]]);;

let MOI_S4P_RAD_ID = prove
 (`!(x:real^N) b b1 b2 r.
     &0 < r /\ norm(b - x) = r /\ norm(b1 - x) = r /\ norm(b2 - x) = r /\
     segment[x,b] SUBSET segment[x,b1] UNION segment[x,b2]
     ==> b = b1 \/ b = b2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!c:real^N. norm(c - x) = r /\ b IN segment[x,c] ==> b = c` ASSUME_TAC THENL
   [X_GEN_TAC `c:real^N` THEN REWRITE_TAC[IN_SEGMENT] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `s:real` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `norm(((&1 - s) % x + s % c) - x:real^N) = s * r` MP_TAC THENL
     [REWRITE_TAC[VECTOR_ARITH `((&1 - s) % x + s % b) - x:real^N = s % (b - x)`;
                  NORM_MUL] THEN
      ASM_SIMP_TAC[REAL_ARITH `&0 <= s ==> abs s = s`];
      ALL_TAC] THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> lhs(concl th) = `b:real^N`)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `s = &1` SUBST1_TAC THENL
     [MATCH_MP_TAC REAL_EQ_RCANCEL_IMP THEN EXISTS_TAC `r:real` THEN
      ASM_MESON_TAC[REAL_LT_IMP_NZ; REAL_MUL_LID];
      VECTOR_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(b:real^N) IN segment[x,b1] UNION segment[x,b2]` MP_TAC THENL
   [ASM_MESON_TAC[SUBSET; ENDS_IN_SEGMENT]; ALL_TAC] THEN
  REWRITE_TAC[IN_UNION] THEN ASM_MESON_TAC[]);;

let MOI_S4P_RAD_SHRINK = prove
 (`!(x:real^N) b r r'.
     norm(b - x) = r /\ &0 < r' /\ r' <= r
     ==> segment[x,b] INTER cball(x,r') = segment[x,x + (r' / r) % (b - x)] /\
         norm((x + (r' / r) % (b - x)) - x) = r'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < r /\ ~(x:real^N = b)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `norm(b - b:real^N) = r` THEN REWRITE_TAC[VECTOR_SUB_REFL; NORM_0] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`x:real^N`; `b:real^N`; `r':real`] MOI_S4P_SEG_LOCAL_END) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[VECTOR_MUL_ASSOC; real_div];
    REWRITE_TAC[VECTOR_ARITH `(x + v) - x:real^N = v`; NORM_MUL] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&0 <= r' / r` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 <= a ==> abs a = a`] THEN
    UNDISCH_TAC `&0 < r` THEN CONV_TAC REAL_FIELD]);;

(* The boundary of a triangle near a vertex and near an edge point. *)

let MOI_S4P_UNIT_NORM = prove
 (`!(x:real^N) v r.
     ~(v = vec 0) /\ &0 <= r ==> norm((x + r % inv(norm v) % v) - x) = r`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[VECTOR_ARITH `(x + v) - x:real^N = v`; NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 <= r ==> abs r = r`; GSYM REAL_MUL_ASSOC] THEN
  ASM_SIMP_TAC[REAL_MUL_LINV; NORM_EQ_0; REAL_MUL_RID]);;

let MOI_S4P_TRI_VERTEX = prove
 (`!a b c:real^2.
     ~collinear{a,b,c}
     ==> ?r b1 b2. &0 < r /\ norm(b1 - a) = r /\ norm(b2 - a) = r /\ ~(b1 = b2) /\
                   relative_frontier(convex hull {a,b,c}) INTER cball(a,r) =
                   segment[a,b1] UNION segment[a,b2]`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_PL2_NONCOLLINEAR_DISTINCT) THEN
  SUBGOAL_THEN `~((a:real^2) IN segment[b,c])` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM BETWEEN_IN_SEGMENT] THEN DISCH_THEN(MP_TAC o MATCH_MP BETWEEN_IMP_COLLINEAR) THEN
    UNDISCH_TAC `~collinear{a:real^2,b,c}` THEN REWRITE_TAC[INSERT_AC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`segment[b:real^2,c]`; `a:real^2`] MOI_S4P_FAR_CLOSED) THEN
  ASM_REWRITE_TAC[CLOSED_SEGMENT] THEN DISCH_THEN(X_CHOOSE_THEN `r0:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `&0 < norm(b - a:real^2) /\ &0 < norm(c - a:real^2)` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[NORM_POS_LT; VECTOR_SUB_EQ] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `r = min r0 (min (norm(b - a:real^2)) (norm(c - a)))` THEN
  SUBGOAL_THEN `&0 < r /\ r <= r0 /\ r <= norm(b - a:real^2) /\ r <= norm(c - a:real^2)`
  STRIP_ASSUME_TAC THENL [EXPAND_TAC "r" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`r:real`; `a + r % inv(norm(b - a)) % (b - a):real^2`;
                        `a + r % inv(norm(c - a)) % (c - a):real^2`] THEN
  ASM_SIMP_TAC[MOI_S4P_UNIT_NORM; VECTOR_SUB_EQ; REAL_LT_IMP_LE] THEN CONJ_TAC THENL
   [REWRITE_TAC[VECTOR_ARITH `a + x:real^N = a + y <=> x = y`; VECTOR_MUL_ASSOC] THEN
    DISCH_TAC THEN UNDISCH_TAC `~collinear{a:real^2,b,c}` THEN REWRITE_TAC[] THEN
    REWRITE_TAC[COLLINEAR_3_EXPAND] THEN DISJ2_TAC THEN
    EXISTS_TAC `&1 - norm(b - a:real^2) / norm(c - a)` THEN
    MATCH_MP_TAC(VECTOR_ARITH
     `!k. b - a = k % (c - a) ==> b:real^N = (&1 - k) % a + (&1 - (&1 - k)) % c`) THEN
    FIRST_X_ASSUM(MP_TAC o AP_TERM `((%) (norm(b - a:real^2) / r)):real^2->real^2`) THEN
    REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
    SUBGOAL_THEN `norm(b - a:real^2) / r * r * inv(norm(b - a)) = &1 /\
                  norm(b - a:real^2) / r * r * inv(norm(c - a)) = norm(b - a) / norm(c - a)`
    (fun th -> REWRITE_TAC[th; VECTOR_MUL_LID]) THEN
    UNDISCH_TAC `&0 < r` THEN UNDISCH_TAC `&0 < norm(b - a:real^2)` THEN
    UNDISCH_TAC `&0 < norm(c - a:real^2)` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  ASM_SIMP_TAC[RELATIVE_FRONTIER_OF_TRIANGLE] THEN
  REWRITE_TAC[SET_RULE `((s:real^2->bool) UNION t UNION u) INTER v =
                        (s INTER v) UNION (t INTER v) UNION (u INTER v)`] THEN
  SUBGOAL_THEN `segment[b:real^2,c] INTER cball(a,r) = {}` SUBST1_TAC THENL
   [MATCH_MP_TAC(SET_RULE `!t. s INTER t = {} /\ u SUBSET t ==> (s:real^2->bool) INTER u = {}`) THEN
    EXISTS_TAC `cball(a:real^2,r0)` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SUBSET_CBALL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[SEGMENT_SYM] THEN
  REWRITE_TAC[UNION_EMPTY] THEN
  ONCE_REWRITE_TAC[SEGMENT_SYM] THEN
  MP_TAC(ISPECL [`a:real^2`; `b:real^2`; `r:real`] MOI_S4P_SEG_LOCAL_END) THEN
  MP_TAC(ISPECL [`a:real^2`; `c:real^2`; `r:real`] MOI_S4P_SEG_LOCAL_END) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN(SUBST1_TAC o SYM)) THEN
  REWRITE_TAC[SEGMENT_SYM] THEN SET_TAC[]);;

let MOI_S4P_TRI_EDGE = prove
 (`!a b c x:real^2.
     ~collinear{a,b,c} /\ x IN segment(a,b)
     ==> ?r b1 b2. &0 < r /\ norm(b1 - x) = r /\ norm(b2 - x) = r /\ ~(b1 = b2) /\
                   relative_frontier(convex hull {a,b,c}) INTER cball(x,r) =
                   segment[x,b1] UNION segment[x,b2]`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_PL2_NONCOLLINEAR_DISTINCT) THEN
  MP_TAC(ASSUME `(x:real^2) IN segment(a,b)`) THEN
  REWRITE_TAC[open_segment; IN_DIFF; IN_INSERT; NOT_IN_EMPTY; DE_MORGAN_THM] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `collinear{a:real^2,b,x}` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[SET_RULE `{a:real^2,b,x} = {a,x,b}`] THEN
    MATCH_MP_TAC BETWEEN_IMP_COLLINEAR THEN ASM_REWRITE_TAC[BETWEEN_IN_SEGMENT];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((x:real^2) IN segment[b,c]) /\ ~(x IN segment[c,a])` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN REWRITE_TAC[GSYM BETWEEN_IN_SEGMENT] THEN
    DISCH_THEN(MP_TAC o MATCH_MP BETWEEN_IMP_COLLINEAR) THEN DISCH_TAC THEN
    UNDISCH_TAC `~collinear{a:real^2,b,c}` THEN REWRITE_TAC[] THENL
     [MATCH_MP_TAC COLLINEAR_3_TRANS THEN EXISTS_TAC `x:real^2` THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `collinear{b:real^2,x,c}` THEN REWRITE_TAC[INSERT_AC];
      ONCE_REWRITE_TAC[SET_RULE `{a:real^2,b,c} = {b,a,c}`] THEN
      MATCH_MP_TAC COLLINEAR_3_TRANS THEN EXISTS_TAC `x:real^2` THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [UNDISCH_TAC `collinear{a:real^2,b,x}` THEN REWRITE_TAC[INSERT_AC];
        UNDISCH_TAC `collinear{c:real^2,x,a}` THEN REWRITE_TAC[INSERT_AC]]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`segment[b:real^2,c] UNION segment[c,a]`; `x:real^2`] MOI_S4P_FAR_CLOSED) THEN
  ASM_SIMP_TAC[CLOSED_UNION; CLOSED_SEGMENT; IN_UNION] THEN
  DISCH_THEN(X_CHOOSE_THEN `r0:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `&0 < norm(a - x:real^2) /\ &0 < norm(b - x:real^2)` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[NORM_POS_LT; VECTOR_SUB_EQ] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `r = min r0 (min (norm(a - x:real^2)) (norm(b - x)))` THEN
  SUBGOAL_THEN `&0 < r /\ r <= r0 /\ r <= norm(a - x:real^2) /\ r <= norm(b - x:real^2)`
  STRIP_ASSUME_TAC THENL [EXPAND_TAC "r" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`r:real`; `x + r % inv(norm(b - x)) % (b - x):real^2`;
                        `x + r % inv(norm(a - x)) % (a - x):real^2`] THEN
  ASM_SIMP_TAC[MOI_S4P_UNIT_NORM; VECTOR_SUB_EQ; REAL_LT_IMP_LE] THEN CONJ_TAC THENL
   [REWRITE_TAC[VECTOR_ARITH `a + x:real^N = a + y <=> x = y`; VECTOR_MUL_ASSOC] THEN
    DISCH_TAC THEN
    UNDISCH_TAC `(x:real^2) IN segment(a,b)` THEN
    REWRITE_TAC[CONJUNCT2(SPEC_ALL IN_SEGMENT)] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `u:real` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `((r * inv(norm(b - x:real^2))) * (&1 - u) + (r * inv(norm(a - x))) * u) %
                  (b - a:real^2) = vec 0` MP_TAC THENL
     [MP_TAC(ASSUME `(r * inv(norm(b - x:real^2))) % (b - x) =
                     (r * inv(norm(a - x))) % (a - x:real^2)`) THEN
      SPEC_TAC(`r * inv(norm(b - x:real^2))`,`k1:real`) THEN
      SPEC_TAC(`r * inv(norm(a - x:real^2))`,`k2:real`) THEN
      UNDISCH_TAC `x:real^2 = (&1 - u) % a + u % b` THEN DISCH_THEN SUBST1_TAC THEN
      REPEAT GEN_TAC THEN VECTOR_ARITH_TAC;
      ALL_TAC] THEN
    UNDISCH_THEN `x:real^2 = (&1 - u) % a + u % b` (K ALL_TAC) THEN
    REWRITE_TAC[VECTOR_MUL_EQ_0; VECTOR_SUB_EQ] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 < x ==> ~(x = &0)`) THEN MATCH_MP_TAC REAL_LT_ADD THEN
    CONJ_TAC THEN REPEAT(MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC) THEN
    ASM_REWRITE_TAC[REAL_LT_INV_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[RELATIVE_FRONTIER_OF_TRIANGLE] THEN
  REWRITE_TAC[SET_RULE `((s:real^2->bool) UNION t UNION u) INTER v =
                        (s INTER v) UNION ((t UNION u) INTER v)`] THEN
  SUBGOAL_THEN `(segment[b:real^2,c] UNION segment[c,a]) INTER cball(x,r) = {}` SUBST1_TAC THENL
   [MATCH_MP_TAC(SET_RULE `!t. s INTER t = {} /\ u SUBSET t ==> (s:real^2->bool) INTER u = {}`) THEN
    EXISTS_TAC `cball(x:real^2,r0)` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SUBSET_CBALL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[UNION_EMPTY] THEN MATCH_MP_TAC MOI_S4P_SEG_LOCAL_MID THEN
  ASM_REWRITE_TAC[]);;

let MOI_S4P_TRI_LOCAL = prove
 (`!(t:real^2->bool) x.
     &2 simplex t /\ x IN relative_frontier t
     ==> ?r b1 b2. &0 < r /\ norm(b1 - x) = r /\ norm(b2 - x) = r /\ ~(b1 = b2) /\
                   relative_frontier t INTER cball(x,r) = segment[x,b1] UNION segment[x,b2]`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MOI_PL2_SIMPLEX_2] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `a:real^2` (X_CHOOSE_THEN `b:real^2` (X_CHOOSE_THEN `c:real^2`
     STRIP_ASSUME_TAC))) MP_TAC) THEN
  FIRST_X_ASSUM SUBST1_TAC THEN ASM_SIMP_TAC[RELATIVE_FRONTIER_OF_TRIANGLE] THEN
  SUBGOAL_THEN `~collinear{b:real^2,c,a} /\ ~collinear{c:real^2,a,b}` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `~collinear{a:real^2,b,c}` THEN REWRITE_TAC[INSERT_AC]; ALL_TAC] THEN
  SUBGOAL_THEN `segment[a,b] UNION segment[b,c] UNION segment[c,a] =
                relative_frontier(convex hull {a:real^2,b,c}) /\
                segment[a,b] UNION segment[b,c] UNION segment[c,a] =
                relative_frontier(convex hull {b:real^2,c,a}) /\
                segment[a,b] UNION segment[b,c] UNION segment[c,a] =
                relative_frontier(convex hull {c:real^2,a,b})` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[RELATIVE_FRONTIER_OF_TRIANGLE] THEN SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[SEGMENT_CLOSED_OPEN; IN_UNION; IN_INSERT; NOT_IN_EMPTY] THEN
  REWRITE_TAC[GSYM SEGMENT_CLOSED_OPEN] THEN
  STRIP_TAC THENL
   [REWRITE_TAC[ASSUME `segment[a,b] UNION segment[b,c] UNION segment[c,a] =
                 relative_frontier(convex hull {a:real^2,b,c})`] THEN
    MATCH_MP_TAC MOI_S4P_TRI_EDGE THEN ASM_REWRITE_TAC[];
    FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> concl th = `x:real^2 = a`)) THEN
    REWRITE_TAC[ASSUME `segment[a,b] UNION segment[b,c] UNION segment[c,a] =
                 relative_frontier(convex hull {a:real^2,b,c})`] THEN
    MATCH_MP_TAC MOI_S4P_TRI_VERTEX THEN ASM_REWRITE_TAC[];
    FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> concl th = `x:real^2 = b`)) THEN
    REWRITE_TAC[ASSUME `segment[a,b] UNION segment[b,c] UNION segment[c,a] =
                 relative_frontier(convex hull {b:real^2,c,a})`] THEN
    MATCH_MP_TAC MOI_S4P_TRI_VERTEX THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[ASSUME `segment[a,b] UNION segment[b,c] UNION segment[c,a] =
                 relative_frontier(convex hull {b:real^2,c,a})`] THEN
    MATCH_MP_TAC MOI_S4P_TRI_EDGE THEN ASM_REWRITE_TAC[];
    FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> concl th = `x:real^2 = b`)) THEN
    REWRITE_TAC[ASSUME `segment[a,b] UNION segment[b,c] UNION segment[c,a] =
                 relative_frontier(convex hull {b:real^2,c,a})`] THEN
    MATCH_MP_TAC MOI_S4P_TRI_VERTEX THEN ASM_REWRITE_TAC[];
    FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> concl th = `x:real^2 = c`)) THEN
    REWRITE_TAC[ASSUME `segment[a,b] UNION segment[b,c] UNION segment[c,a] =
                 relative_frontier(convex hull {c:real^2,a,b})`] THEN
    MATCH_MP_TAC MOI_S4P_TRI_VERTEX THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[ASSUME `segment[a,b] UNION segment[b,c] UNION segment[c,a] =
                 relative_frontier(convex hull {c:real^2,a,b})`] THEN
    MATCH_MP_TAC MOI_S4P_TRI_EDGE THEN ASM_REWRITE_TAC[];
    FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> concl th = `x:real^2 = c`)) THEN
    REWRITE_TAC[ASSUME `segment[a,b] UNION segment[b,c] UNION segment[c,a] =
                 relative_frontier(convex hull {c:real^2,a,b})`] THEN
    MATCH_MP_TAC MOI_S4P_TRI_VERTEX THEN ASM_REWRITE_TAC[];
    FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> concl th = `x:real^2 = a`)) THEN
    REWRITE_TAC[ASSUME `segment[a,b] UNION segment[b,c] UNION segment[c,a] =
                 relative_frontier(convex hull {a:real^2,b,c})`] THEN
    MATCH_MP_TAC MOI_S4P_TRI_VERTEX THEN ASM_REWRITE_TAC[]]);;

let SPDR9_BRANCH_SET = prove
 (`!(A:real^N->bool) A' J C S1 S2 x y b1 b2.
     x IN S2 /\ b2 IN S2 ==> x IN S1 /\ b1 IN S1 ==> x IN A' ==> x IN A ==>
     S2 SUBSET C ==> S1 SUBSET C ==> J INTER C = S1 UNION S2 ==> A UNION A' = J ==>
     A INTER A' = {x,y} ==> ~(y IN C) ==>
     ~(A INTER C SUBSET {x}) /\ ~(A' INTER C SUBSET {x}) ==>
     (S2 DELETE x SUBSET A \/ S2 DELETE x SUBSET A') ==>
     (S1 DELETE x SUBSET A \/ S1 DELETE x SUBSET A') ==>
     (A INTER C = S1 /\ A' INTER C = S2) \/ (A INTER C = S2 /\ A' INTER C = S1)`,
  REPEAT GEN_TAC THEN REPLICATE_TAC 8 DISCH_TAC THEN
  DISCH_THEN(fun th1 -> DISCH_THEN(fun th2 ->
    ASSUME_TAC(MATCH_MP (SET_RULE
     `!A A' C (x:real^N) y. A INTER A' = {x,y} /\ ~(y IN C) ==> A INTER A' INTER C SUBSET {x}`)
     (CONJ th1 th2)))) THEN
  DISCH_THEN STRIP_ASSUME_TAC THEN
  DISCH_THEN DISJ_CASES_TAC THEN DISCH_THEN DISJ_CASES_TAC THENL
   [UNDISCH_TAC `~((A':real^N->bool) INTER C SUBSET {x})` THEN
    MAP_EVERY UNDISCH_TAC
     [`(J:real^N->bool) INTER C = S1 UNION S2`; `(A:real^N->bool) UNION A' = J`;
      `(A:real^N->bool) INTER A' INTER C SUBSET {x}`;
      `(S1:real^N->bool) DELETE x SUBSET A`; `(S2:real^N->bool) DELETE x SUBSET A`] THEN
    SET_TAC[];
    DISJ2_TAC THEN
    MAP_EVERY UNDISCH_TAC
     [`(x:real^N) IN S1 /\ b1 IN S1`; `(x:real^N) IN S2 /\ b2 IN S2`;
      `(x:real^N) IN A`; `(x:real^N) IN A'`;
      `(S1:real^N->bool) SUBSET C`; `(S2:real^N->bool) SUBSET C`;
      `(J:real^N->bool) INTER C = S1 UNION S2`; `(A:real^N->bool) UNION A' = J`;
      `(A:real^N->bool) INTER A' INTER C SUBSET {x}`;
      `(S1:real^N->bool) DELETE x SUBSET A'`; `(S2:real^N->bool) DELETE x SUBSET A`] THEN
    SET_TAC[];
    DISJ1_TAC THEN
    MAP_EVERY UNDISCH_TAC
     [`(x:real^N) IN S1 /\ b1 IN S1`; `(x:real^N) IN S2 /\ b2 IN S2`;
      `(x:real^N) IN A`; `(x:real^N) IN A'`;
      `(S1:real^N->bool) SUBSET C`; `(S2:real^N->bool) SUBSET C`;
      `(J:real^N->bool) INTER C = S1 UNION S2`; `(A:real^N->bool) UNION A' = J`;
      `(A:real^N->bool) INTER A' INTER C SUBSET {x}`;
      `(S1:real^N->bool) DELETE x SUBSET A`; `(S2:real^N->bool) DELETE x SUBSET A'`] THEN
    SET_TAC[];
    UNDISCH_TAC `~((A:real^N->bool) INTER C SUBSET {x})` THEN
    MAP_EVERY UNDISCH_TAC
     [`(J:real^N->bool) INTER C = S1 UNION S2`; `(A:real^N->bool) UNION A' = J`;
      `(A:real^N->bool) INTER A' INTER C SUBSET {x}`;
      `(S1:real^N->bool) DELETE x SUBSET A'`; `(S2:real^N->bool) DELETE x SUBSET A'`] THEN
    SET_TAC[]]);;

(* A circle J split into two arcs A, A' at x and y: near x each arc is one *)
(* of the two radial segments of J.                                         *)

let MOI_S4P_BRANCH = prove
 (`!(J:real^N->bool) A A' x y r b1 b2.
     A UNION A' = J /\ A INTER A' = {x,y} /\ closed A /\ closed A' /\
     x IN closure(A DELETE x) /\ x IN closure(A' DELETE x) /\
     &0 < r /\ ~(y IN cball(x,r)) /\ norm(b1 - x) = r /\ norm(b2 - x) = r /\
     J INTER cball(x,r) = segment[x,b1] UNION segment[x,b2]
     ==> (A INTER cball(x,r) = segment[x,b1] /\ A' INTER cball(x,r) = segment[x,b2]) \/
         (A INTER cball(x,r) = segment[x,b2] /\ A' INTER cball(x,r) = segment[x,b1])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `segment[x:real^N,b1] SUBSET cball(x,r) /\ segment[x,b2] SUBSET cball(x,r)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SEGMENT_SUBSET_CONVEX THEN
    ASM_REWRITE_TAC[CONVEX_CBALL; IN_CBALL; dist; VECTOR_SUB_REFL; NORM_0] THEN
    ONCE_REWRITE_TAC[NORM_SUB] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!b:real^N. segment[x,b] SUBSET cball(x,r) /\
                           segment[x,b] SUBSET J
                           ==> (segment[x,b] DELETE x) SUBSET A \/
                               (segment[x,b] DELETE x) SUBSET A'` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_SFR_CONNECTED_SIDE THEN
    EXISTS_TAC `{x:real^N,y}` THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONVEX_CONNECTED THEN REWRITE_TAC[CONVEX_SEMIOPEN_SEGMENT];
      ASM SET_TAC[];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `segment[x:real^N,b1] SUBSET J /\ segment[x,b2] SUBSET J` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^N) IN A /\ x IN A'` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!B:real^N->bool. x IN closure(B DELETE x) ==> ~(B INTER cball(x,r) SUBSET {x})`
  ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[CLOSURE_APPROACHABLE] THEN
    DISCH_THEN(MP_TAC o SPEC `r:real`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `z:real^N` STRIP_ASSUME_TAC) THEN
    REWRITE_TAC[SUBSET; IN_INTER; IN_SING; IN_CBALL] THEN
    DISCH_THEN(MP_TAC o SPEC `z:real^N`) THEN
    UNDISCH_TAC `(z:real^N) IN B DELETE x` THEN REWRITE_TAC[IN_DELETE] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `dist(z:real^N,x) < r` THEN
    MP_TAC(ISPECL [`x:real^N`; `z:real^N`] DIST_SYM) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `b1:real^N`) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `b2:real^N`) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~((A:real^N->bool) INTER cball(x,r) SUBSET {x}) /\
                ~((A':real^N->bool) INTER cball(x,r) SUBSET {x})` MP_TAC THENL
   [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `~((y:real^N) IN cball(x,r))` THEN
  UNDISCH_TAC `A INTER A' = {x:real^N,y}` THEN
  UNDISCH_TAC `(A:real^N->bool) UNION A' = J` THEN
  UNDISCH_TAC `(J:real^N->bool) INTER cball(x,r) = segment[x,b1] UNION segment[x,b2]` THEN
  UNDISCH_TAC `segment[x:real^N,b1] SUBSET cball(x,r)` THEN
  UNDISCH_TAC `segment[x:real^N,b2] SUBSET cball(x,r)` THEN
  UNDISCH_TAC `(x:real^N) IN A` THEN UNDISCH_TAC `(x:real^N) IN A'` THEN
  MP_TAC(ISPECL [`x:real^N`; `b1:real^N`] ENDS_IN_SEGMENT) THEN
  MP_TAC(ISPECL [`x:real^N`; `b2:real^N`] ENDS_IN_SEGMENT) THEN
  MATCH_ACCEPT_TAC SPDR9_BRANCH_SET);;

(* ------------------------------------------------------------------------- *)
(* The corner analysis of the 2D push.  At a crossing point x of            *)
(* the bigon boundary (a triangle t in the chart), tau is the arc a plus   *)
(* one radial whisker leaving t, rho is a prime plus one whisker, and small *)
(* neighbourhoods are split by rho into two connected sides.               *)
(* ------------------------------------------------------------------------- *)

(* Shrinking a pair of radial segments; picking the other radial segment. *)

let MOI_S4P_RAD2_SHRINK = prove
 (`!(s:real^N->bool) x b1 b2 r r'.
     s INTER cball(x,r) = segment[x,b1] UNION segment[x,b2] /\
     norm(b1 - x) = r /\ norm(b2 - x) = r /\ ~(b1 = b2) /\ &0 < r' /\ r' <= r
     ==> ?c1 c2. s INTER cball(x,r') = segment[x,c1] UNION segment[x,c2] /\
                 norm(c1 - x) = r' /\ norm(c2 - x) = r' /\ ~(c1 = c2) /\
                 segment[x,c1] SUBSET segment[x,b1] /\ segment[x,c2] SUBSET segment[x,b2]`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`x:real^N`; `b1:real^N`; `r:real`; `r':real`] MOI_S4P_RAD_SHRINK) THEN
  MP_TAC(ISPECL [`x:real^N`; `b2:real^N`; `r:real`; `r':real`] MOI_S4P_RAD_SHRINK) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`x + (r' / r) % (b1 - x):real^N`; `x + (r' / r) % (b2 - x):real^N`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN `cball(x:real^N,r') SUBSET cball(x,r)` ASSUME_TAC THENL
     [MATCH_MP_TAC SUBSET_CBALL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `(s INTER cball(x:real^N,r)) INTER cball(x,r')` THEN CONJ_TAC THENL
     [MATCH_MP_TAC(SET_RULE `c' SUBSET c ==> (s:real^N->bool) INTER c' = (s INTER c) INTER c'`) THEN
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[]] THEN
    ASM_REWRITE_TAC[SET_RULE `((s:real^N->bool) UNION t) INTER u = (s INTER u) UNION (t INTER u)`];
    REWRITE_TAC[VECTOR_ARITH `x + a:real^N = x + b <=> a = b`] THEN
    SUBGOAL_THEN `&0 < r' / r` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[VECTOR_MUL_LCANCEL; REAL_LT_IMP_NZ] THEN
    ASM_REWRITE_TAC[VECTOR_ARITH `b1 - x = b2 - x <=> b1:real^N = b2`];
    ASM_MESON_TAC[INTER_SUBSET];
    ASM_MESON_TAC[INTER_SUBSET]]);;

let MOI_S4P_RAD_PICK = prove
 (`!(s:real^N->bool) x d1 d2 c r.
     s INTER cball(x,r) = segment[x,d1] UNION segment[x,d2] /\
     norm(d1 - x) = r /\ norm(d2 - x) = r /\ ~(d1 = d2) /\ &0 < r /\
     norm(c - x) = r /\ segment[x,c] SUBSET s
     ==> ?u. s INTER cball(x,r) = segment[x,c] UNION segment[x,u] /\
             norm(u - x) = r /\ ~(u = c)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `segment[x:real^N,c] SUBSET cball(x,r)` ASSUME_TAC THENL
   [MATCH_MP_TAC SEGMENT_SUBSET_CONVEX THEN
    ASM_REWRITE_TAC[CONVEX_CBALL; IN_CBALL; dist; VECTOR_SUB_REFL; NORM_0] THEN
    ONCE_REWRITE_TAC[NORM_SUB] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`x:real^N`; `c:real^N`; `d1:real^N`; `d2:real^N`; `r:real`] MOI_S4P_RAD_ID) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
  STRIP_TAC THENL
   [EXISTS_TAC `d2:real^N` THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    EXISTS_TAC `d1:real^N` THEN ASM_REWRITE_TAC[UNION_COMM]]);;

(* At a crossing point, small neighbourhoods are split by rho into two     *)
(* connected sides, each containing points of one branch of tau.           *)

let MOI_S4P_SIDES_LOCAL = prove
 (`!(tau:real^2->bool) rho x r ca ut ww.
     pl_curve_crossing_at (:real^2) tau rho x /\ &0 < r /\
     norm(ca - x) = r /\ norm(ut - x) = r /\ ~(ca = ut) /\
     tau INTER cball(x,r) = segment[x,ca] UNION segment[x,ut] /\ open ww /\ x IN ww
     ==> ?n g1 g2. open n /\ x IN n /\ n SUBSET ww /\ n DIFF rho = g1 UNION g2 /\
                   DISJOINT g1 g2 /\ open g1 /\ open g2 /\ connected g1 /\ connected g2 /\
                   ~(g1 INTER (segment[x,ca] DELETE x) = {}) /\
                   ~(g2 INTER (segment[x,ut] DELETE x) = {})`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`tau:real^2->bool`; `rho:real^2->bool`; `x:real^2`;
                 `ww INTER ball(x:real^2,r)`] MOI_S4P_CROSS_CONE) THEN
  ASM_SIMP_TAC[OPEN_INTER; OPEN_BALL; IN_INTER; CENTRE_IN_BALL] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`r3:real`; `d1:real^2`; `d2:real^2`; `e1:real^2`; `e2:real^2`;
                       `n:real^2->bool`; `h1:real^2->bool`; `h2:real^2->bool`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `?F1 F2:real^2. tau INTER cball(x,r3) = segment[x,F1] UNION segment[x,F2] /\
                              norm(F1 - x) = r3 /\ norm(F2 - x) = r3 /\ ~(F1 = F2) /\
                              segment[x,F1] DELETE x SUBSET h1 /\
                              segment[x,F2] DELETE x SUBSET h2`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXISTS_TAC [`x + r3 % inv(norm d1) % d1:real^2`;
                          `x + r3 % inv(norm d2) % d2:real^2`] THEN
    ASM_SIMP_TAC[MOI_S4P_UNIT_NORM; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `r3 <= r` ASSUME_TAC THENL
   [SUBGOAL_THEN `(F1:real^2) IN ball(x,r)` MP_TAC THENL
     [SUBGOAL_THEN `(F1:real^2) IN cball(x,r3)` MP_TAC THENL
       [REWRITE_TAC[IN_CBALL; dist] THEN ONCE_REWRITE_TAC[NORM_SUB] THEN ASM_REAL_ARITH_TAC;
        ASM SET_TAC[]];
      REWRITE_TAC[IN_BALL; dist] THEN ONCE_REWRITE_TAC[NORM_SUB] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`tau:real^2->bool`; `x:real^2`; `ca:real^2`; `ut:real^2`; `r:real`; `r3:real`]
    MOI_S4P_RAD2_SHRINK) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c1:real^2` (X_CHOOSE_THEN `c2:real^2` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `(F1 = c1 \/ F1 = c2) /\ (F2 = c1 \/ F2 = (c2:real^2))` MP_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC MOI_S4P_RAD_ID THEN
    MAP_EVERY EXISTS_TAC [`x:real^2`; `r3:real`] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `tau INTER cball(x:real^2,r3) = segment[x,c1] UNION segment[x,c2]` THEN
    UNDISCH_TAC `tau INTER cball(x:real^2,r3) = segment[x,F1] UNION segment[x,F2]` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(F1:real^2 = x) /\ ~(F2:real^2 = x) /\ ~(c1:real^2 = x) /\ ~(c2:real^2 = x)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[VECTOR_SUB_REFL; NORM_0]) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(c1:real^2) IN segment[x,ca] /\ c2 IN segment[x,ut]` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC(SET_RULE `!s. (c:real^2) IN s /\ s SUBSET t ==> c IN t`) THENL
     [EXISTS_TAC `segment[x:real^2,c1]`; EXISTS_TAC `segment[x:real^2,c2]`] THEN
    ASM_REWRITE_TAC[ENDS_IN_SEGMENT];
    ALL_TAC] THEN
  SUBGOAL_THEN `(F1:real^2) IN h1 /\ (F2:real^2) IN h2` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `segment[x,F1] DELETE x SUBSET (h1:real^2->bool)`;
      UNDISCH_TAC `segment[x,F2] DELETE x SUBSET (h2:real^2->bool)`] THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[IN_DELETE; ENDS_IN_SEGMENT];
    ALL_TAC] THEN
  SUBGOAL_THEN `x IN (n:real^2->bool) /\ n SUBSET ww` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `cball(x:real^2,r3) SUBSET n` THEN REWRITE_TAC[SUBSET] THEN
      DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[CENTRE_IN_CBALL] THEN ASM_REAL_ARITH_TAC;
      ASM SET_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (DISJ_CASES_THEN SUBST_ALL_TAC)
                             (DISJ_CASES_THEN SUBST_ALL_TAC)) THENL
   [UNDISCH_TAC `~(c1:real^2 = c1)` THEN REWRITE_TAC[];
    MAP_EVERY EXISTS_TAC [`n:real^2->bool`; `h1:real^2->bool`; `h2:real^2->bool`] THEN
    ASM_REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN CONJ_TAC THENL
     [EXISTS_TAC `c1:real^2`; EXISTS_TAC `c2:real^2`] THEN
    ASM_REWRITE_TAC[IN_INTER; IN_DELETE];
    MAP_EVERY EXISTS_TAC [`n:real^2->bool`; `h2:real^2->bool`; `h1:real^2->bool`] THEN
    ONCE_REWRITE_TAC[UNION_COMM; DISJOINT_SYM] THEN
    ASM_REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN CONJ_TAC THENL
     [EXISTS_TAC `c1:real^2`; EXISTS_TAC `c2:real^2`] THEN
    ASM_REWRITE_TAC[IN_INTER; IN_DELETE];
    UNDISCH_TAC `~(c2:real^2 = c2)` THEN REWRITE_TAC[]]);;

(* The corner analysis at a crossing point x of the bigon boundary: tau    *)
(* is the arc a plus one whisker leaving t, rho is a' plus one whisker,    *)
(* and small neighbourhoods are split by rho into a side meeting t DIFF a' *)
(* and a side meeting the tau whisker.                                     *)

let MOI_S4P_CORNER = prove
 (`!(t:real^2->bool) a a' tau rho x y r0.
     &2 simplex t /\ x IN relative_frontier t /\ ~(x = y) /\ &0 < r0 /\
     a UNION a' = relative_frontier t /\ a INTER a' = {x,y} /\
     closed a /\ closed a' /\ x IN closure(a DELETE x) /\ x IN closure(a' DELETE x) /\
     tau INTER t = a /\ rho INTER t = a' /\
     pl_curve_crossing_at (:real^2) tau rho x
     ==> ?r ut ur. &0 < r /\ r <= r0 /\ ~(y IN cball(x,r)) /\
                   norm(ut - x) = r /\ norm(ur - x) = r /\
                   tau INTER cball(x,r) = (a INTER cball(x,r)) UNION segment[x,ut] /\
                   rho INTER cball(x,r) = (a' INTER cball(x,r)) UNION segment[x,ur] /\
                   segment[x,ut] INTER t = {x} /\ segment[x,ur] INTER t = {x} /\
                   tau INTER rho INTER cball(x,r) = {x} /\
                   (!ww. open ww /\ x IN ww
                         ==> ?n g1 g2. open n /\ x IN n /\ n SUBSET ww /\
                                       n DIFF rho = g1 UNION g2 /\ DISJOINT g1 g2 /\
                                       open g1 /\ open g2 /\ connected g1 /\ connected g2 /\
                                       ~(g1 INTER (t DIFF a') = {}) /\
                                       ~(g2 INTER (segment[x,ut] DELETE x) = {}))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(x:real^2) IN a /\ x IN a' /\ (y:real^2) IN a /\ y IN a'` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`t:real^2->bool`; `x:real^2`] MOI_S4P_TRI_LOCAL) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r1:real` (X_CHOOSE_THEN `b1:real^2` (X_CHOOSE_THEN `b2:real^2`
    STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `?r2 D1 D2 E1 E2:real^2.
                  &0 < r2 /\
                  tau INTER cball(x,r2) = segment[x,D1] UNION segment[x,D2] /\
                  rho INTER cball(x,r2) = segment[x,E1] UNION segment[x,E2] /\
                  norm(D1 - x) = r2 /\ norm(D2 - x) = r2 /\ ~(D1 = D2) /\
                  norm(E1 - x) = r2 /\ norm(E2 - x) = r2 /\ ~(E1 = E2) /\
                  tau INTER rho INTER cball(x,r2) = {x}`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`tau:real^2->bool`; `rho:real^2->bool`; `x:real^2`; `(:real^2)`]
      MOI_S4P_CROSS_CONE) THEN
    ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`r2:real`; `d1:real^2`; `d2:real^2`; `e1:real^2`; `e2:real^2`;
                         `n0:real^2->bool`; `h1:real^2->bool`; `h2:real^2->bool`] THEN
    STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`r2:real`; `x + r2 % inv(norm d1) % d1:real^2`;
                          `x + r2 % inv(norm d2) % d2:real^2`;
                          `x + r2 % inv(norm e1) % e1:real^2`; `x + r2 % inv(norm e2) % e2:real^2`] THEN
    ASM_SIMP_TAC[MOI_S4P_UNIT_NORM; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  ABBREV_TAC `r = min r1 (min r2 (min r0 (norm(y - x:real^2) / &2)))` THEN
  SUBGOAL_THEN `&0 < norm(y - x:real^2)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT; VECTOR_SUB_EQ] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < r /\ r <= r1 /\ r <= r2 /\ r <= r0 /\ r < norm(y - x:real^2)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "r" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~((y:real^2) IN cball(x,r))` ASSUME_TAC THENL
   [REWRITE_TAC[IN_CBALL; dist] THEN ONCE_REWRITE_TAC[NORM_SUB] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `?ca ca':real^2. a INTER cball(x,r) = segment[x,ca] /\
                                a' INTER cball(x,r) = segment[x,ca'] /\
                                norm(ca - x) = r /\ norm(ca' - x) = r /\ ~(ca = ca')`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`relative_frontier t:real^2->bool`; `x:real^2`; `b1:real^2`; `b2:real^2`;
                   `r1:real`; `r:real`] MOI_S4P_RAD2_SHRINK) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `c1:real^2` (X_CHOOSE_THEN `c2:real^2` STRIP_ASSUME_TAC)) THEN
    MP_TAC(ISPECL [`relative_frontier t:real^2->bool`; `a:real^2->bool`; `a':real^2->bool`;
                   `x:real^2`; `y:real^2`; `r:real`; `c1:real^2`; `c2:real^2`]
      MOI_S4P_BRANCH) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN STRIP_TAC THENL
     [MAP_EVERY EXISTS_TAC [`c1:real^2`; `c2:real^2`] THEN ASM_REWRITE_TAC[];
      MAP_EVERY EXISTS_TAC [`c2:real^2`; `c1:real^2`] THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `segment[x:real^2,ca] SUBSET tau /\ segment[x:real^2,ca'] SUBSET rho /\
                segment[x:real^2,ca] SUBSET t /\ segment[x:real^2,ca'] SUBSET t /\
                segment[x:real^2,ca] SUBSET cball(x,r) /\ segment[x:real^2,ca'] SUBSET cball(x,r)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `a INTER cball(x:real^2,r) = segment[x,ca]` THEN
    UNDISCH_TAC `a' INTER cball(x:real^2,r) = segment[x,ca']` THEN
    UNDISCH_TAC `(tau:real^2->bool) INTER t = a` THEN
    UNDISCH_TAC `(rho:real^2->bool) INTER t = a'` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?ut:real^2. tau INTER cball(x,r) = segment[x,ca] UNION segment[x,ut] /\
                            norm(ut - x) = r /\ ~(ut = ca)` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`tau:real^2->bool`; `x:real^2`; `D1:real^2`; `D2:real^2`;
                   `r2:real`; `r:real`] MOI_S4P_RAD2_SHRINK) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `D1':real^2` (X_CHOOSE_THEN `D2':real^2` STRIP_ASSUME_TAC)) THEN
    MATCH_MP_TAC MOI_S4P_RAD_PICK THEN
    MAP_EVERY EXISTS_TAC [`D1':real^2`; `D2':real^2`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?ur:real^2. rho INTER cball(x,r) = segment[x,ca'] UNION segment[x,ur] /\
                            norm(ur - x) = r /\ ~(ur = ca')` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`rho:real^2->bool`; `x:real^2`; `E1:real^2`; `E2:real^2`;
                   `r2:real`; `r:real`] MOI_S4P_RAD2_SHRINK) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `E1':real^2` (X_CHOOSE_THEN `E2':real^2` STRIP_ASSUME_TAC)) THEN
    MATCH_MP_TAC MOI_S4P_RAD_PICK THEN
    MAP_EVERY EXISTS_TAC [`E1':real^2`; `E2':real^2`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`x:real^2`; `ut:real^2`; `ca:real^2`; `r:real`] MOI_S4P_RAD_MEET) THEN
  MP_TAC(ISPECL [`x:real^2`; `ur:real^2`; `ca':real^2`; `r:real`] MOI_S4P_RAD_MEET) THEN
  MP_TAC(ISPECL [`x:real^2`; `ca:real^2`; `ca':real^2`; `r:real`] MOI_S4P_RAD_MEET) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `(x:real^2) IN t` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `cball(x:real^2,r) SUBSET cball(x,r2)` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_CBALL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `tau INTER cball(x:real^2,r) = (a INTER cball(x,r)) UNION segment[x,ut] /\
                rho INTER cball(x:real^2,r) = (a' INTER cball(x,r)) UNION segment[x,ur]`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `tau INTER cball(x:real^2,r) = segment[x,ca] UNION segment[x,ut]` THEN
      UNDISCH_TAC `a INTER cball(x:real^2,r) = segment[x,ca]` THEN
      DISCH_THEN SUBST1_TAC THEN DISCH_THEN ACCEPT_TAC;
      UNDISCH_TAC `rho INTER cball(x:real^2,r) = segment[x,ca'] UNION segment[x,ur]` THEN
      UNDISCH_TAC `a' INTER cball(x:real^2,r) = segment[x,ca']` THEN
      DISCH_THEN SUBST1_TAC THEN DISCH_THEN ACCEPT_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `segment[x:real^2,ut] INTER t = {x}` ASSUME_TAC THENL
   [UNDISCH_TAC `segment[x:real^2,ut] INTER segment[x,ca] = {x}` THEN
    UNDISCH_TAC `tau INTER cball(x:real^2,r) = segment[x,ca] UNION segment[x,ut]` THEN
    UNDISCH_TAC `(tau:real^2->bool) INTER t = a` THEN
    UNDISCH_TAC `a INTER cball(x:real^2,r) = segment[x,ca]` THEN
    UNDISCH_TAC `(x:real^2) IN t` THEN
    MP_TAC(ISPECL [`x:real^2`; `ut:real^2`] ENDS_IN_SEGMENT) THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `segment[x:real^2,ur] INTER t = {x}` ASSUME_TAC THENL
   [UNDISCH_TAC `segment[x:real^2,ur] INTER segment[x,ca'] = {x}` THEN
    UNDISCH_TAC `rho INTER cball(x:real^2,r) = segment[x,ca'] UNION segment[x,ur]` THEN
    UNDISCH_TAC `(rho:real^2->bool) INTER t = a'` THEN
    UNDISCH_TAC `a' INTER cball(x:real^2,r) = segment[x,ca']` THEN
    UNDISCH_TAC `(x:real^2) IN t` THEN
    MP_TAC(ISPECL [`x:real^2`; `ur:real^2`] ENDS_IN_SEGMENT) THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `tau INTER rho INTER cball(x:real^2,r) = {x}` ASSUME_TAC THENL
   [SUBGOAL_THEN `(x:real^2) IN tau /\ x IN rho /\ x IN cball(x,r)` MP_TAC THENL
     [REWRITE_TAC[CENTRE_IN_CBALL] THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `tau INTER rho INTER cball(x:real^2,r2) = {x}` THEN
    UNDISCH_TAC `cball(x:real^2,r) SUBSET cball(x,r2)` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!ww. open ww /\ x IN ww
         ==> ?n g1 g2. open n /\ x IN n /\ n SUBSET ww /\
                       n DIFF rho = g1 UNION g2 /\ DISJOINT g1 g2 /\
                       open g1 /\ open g2 /\ connected g1 /\ connected g2 /\
                       ~(g1 INTER (t DIFF a') = {}) /\
                       ~(g2 INTER (segment[x:real^2,ut] DELETE x) = {})`
  ASSUME_TAC THENL
   [X_GEN_TAC `ww:real^2->bool` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`tau:real^2->bool`; `rho:real^2->bool`; `x:real^2`; `r:real`; `ca:real^2`;
                   `ut:real^2`; `ww:real^2->bool`] MOI_S4P_SIDES_LOCAL) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `n:real^2->bool` THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `g1:real^2->bool` THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `g2:real^2->bool` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `~((g1:real^2->bool) INTER (segment[x,ca] DELETE x) = {})` THEN
    UNDISCH_TAC `segment[x:real^2,ca] INTER segment[x,ca'] = {x}` THEN
    UNDISCH_TAC `a' INTER cball(x:real^2,r) = segment[x,ca']` THEN
    UNDISCH_TAC `segment[x:real^2,ca] SUBSET t` THEN
    UNDISCH_TAC `segment[x:real^2,ca] SUBSET cball(x,r)` THEN
    SET_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`r:real`; `ut:real^2`; `ur:real^2`] THEN
  REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC);;

(* ------------------------------------------------------------------------- *)
(* Tools for the 2D push in standard position: an enlarged                  *)
(* triangle inside a given open set, PL arcs of 1-cells with given ends,    *)
(* and the exit point of a segment leaving a convex set.                    *)
(* ------------------------------------------------------------------------- *)

(* A triangle inside an open set has a slightly enlarged homothetic copy  *)
(* containing it in its interior, still inside the open set.               *)

let MOI_S4P_ENLARGE = prove
 (`!(t:real^2->bool) u.
     &2 simplex t /\ open u /\ t SUBSET u
     ==> ?k. &2 simplex k /\ t SUBSET interior k /\ k SUBSET u`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [MOI_PL2_SIMPLEX_2]) THEN
  DISCH_THEN(X_CHOOSE_THEN `v0:real^2` (X_CHOOSE_THEN `v1:real^2` (X_CHOOSE_THEN `v2:real^2`
    STRIP_ASSUME_TAC))) THEN
  ABBREV_TAC `c:real^2 = inv(&3) % v0 + inv(&3) % v1 + inv(&3) % v2` THEN
  SUBGOAL_THEN `(c:real^2) IN interior t` ASSUME_TAC THENL
   [UNDISCH_TAC `t = convex hull {v0:real^2,v1,v2}` THEN DISCH_THEN SUBST1_TAC THEN
    ASM_SIMP_TAC[INTERIOR_CONVEX_HULL_3_MINIMAL; IN_ELIM_THM] THEN
    MAP_EVERY EXISTS_TAC [`inv(&3)`; `inv(&3)`; `inv(&3)`] THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_THEN `t = convex hull {v0:real^2,v1,v2}` (K ALL_TAC) THEN
  SUBGOAL_THEN `compact(t:real^2->bool) /\ convex t /\ (c:real^2) IN t` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[SIMPLEX_IMP_COMPACT; SIMPLEX_IMP_CONVEX; INTERIOR_SUBSET; SUBSET];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:real^2->bool`; `(:real^2) DIFF u`] SEPARATE_COMPACT_CLOSED) THEN
  ASM_REWRITE_TAC[GSYM OPEN_CLOSED] THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[IN_DIFF; IN_UNIV] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `D = diameter(t:real^2->bool)` THEN
  SUBGOAL_THEN `!x:real^2. x IN t ==> norm(x - c) <= D` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "D" THEN MATCH_MP_TAC DIAMETER_BOUNDED_BOUND THEN
    ASM_SIMP_TAC[COMPACT_IMP_BOUNDED];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= D` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `norm(c - c:real^2)` THEN
    ASM_SIMP_TAC[NORM_POS_LE];
    ALL_TAC] THEN
  ABBREV_TAC `lam = &1 + d / (&2 * (D + &1))` THEN
  SUBGOAL_THEN `&1 < lam /\ (lam - &1) * D < d` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "lam" THEN
    SUBGOAL_THEN `&0 < d / (&2 * (D + &1))` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_ARITH `(&1 + x) - &1 = x`] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `d / (&2 * (D + &1)) * (D + &1)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
      SUBGOAL_THEN `d / (&2 * (D + &1)) * (D + &1) = d / &2` SUBST1_TAC THENL
       [UNDISCH_TAC `&0 <= D` THEN CONV_TAC REAL_FIELD; ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(lam = &0)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  EXISTS_TAC `IMAGE (\x:real^2. lam % x + (&1 - lam) % c) t` THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[AFFINITY_SCALING_TRANSLATION; IMAGE_o; SIMPLEX_TRANSLATION_EQ] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) SIMPLEX_LINEAR_IMAGE_EQ o snd) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[LINEAR_SCALING; VECTOR_MUL_LCANCEL];
      DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]];
    ASM_REWRITE_TAC[INTERIOR_AFFINITY] THEN
    REWRITE_TAC[SUBSET; IN_IMAGE] THEN X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    EXISTS_TAC `c + inv lam % (x - c):real^2` THEN CONJ_TAC THENL
     [REWRITE_TAC[VECTOR_ADD_LDISTRIB; VECTOR_SUB_LDISTRIB; VECTOR_MUL_ASSOC] THEN
      ASM_SIMP_TAC[REAL_MUL_RINV] THEN VECTOR_ARITH_TAC;
      ALL_TAC] THEN
    ASM_CASES_TAC `x:real^2 = c` THENL
     [ASM_REWRITE_TAC[VECTOR_SUB_REFL; VECTOR_MUL_RZERO; VECTOR_ADD_RID]; ALL_TAC] THEN
    MP_TAC(ISPECL [`t:real^2->bool`; `c:real^2`; `x:real^2`]
      IN_INTERIOR_CLOSURE_CONVEX_SEGMENT) THEN
    ASM_SIMP_TAC[CLOSURE_CLOSED; COMPACT_IMP_CLOSED; SUBSET] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[IN_SEGMENT] THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `inv lam` THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_INV_LT_1 THEN ASM_REAL_ARITH_TAC;
      VECTOR_ARITH_TAC];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`x:real^2`; `lam % x + (&1 - lam) % c:real^2`]) THEN
    ASM_REWRITE_TAC[REAL_NOT_LE; dist] THEN
    REWRITE_TAC[VECTOR_ARITH `x - (lam % x + (&1 - lam) % c):real^2 = --((lam - &1) % (x - c))`;
                NORM_NEG; NORM_MUL] THEN
    ASM_SIMP_TAC[REAL_ARITH `&1 < lam ==> abs(lam - &1) = lam - &1`] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `(lam - &1) * D` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC]);;

(* A PL 1-cell with ends p, q is the image of a PL arc from p to q. *)

let MOI_S4P_CELL1_ARC = prove
 (`!(a:real^N->bool) p q.
     pl_cell_with_boundary 1 a {p,q} /\ ~(p = q)
     ==> ?g. arc g /\ pl_map_on (interval[vec 0,vec 1]) g /\ path_image g = a /\
             pathstart g = p /\ pathfinish g = q`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_cell_with_boundary; pl_homeomorphism] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
    (X_CHOOSE_THEN `f':real^N->real^N` STRIP_ASSUME_TAC))) ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [MOI_PL2_SIMPLEX_1]) THEN
  DISCH_THEN(X_CHOOSE_THEN `x0:real^N` (X_CHOOSE_THEN `x1:real^N` STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  SUBGOAL_THEN `relative_frontier(segment[x0:real^N,x1]) = {x0,x1}` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[relative_frontier; RELATIVE_INTERIOR_SEGMENT; CLOSURE_SEGMENT] THEN
    REWRITE_TAC[SEGMENT_CLOSED_OPEN] THEN
    MP_TAC(ISPECL [`x0:real^N`; `x1:real^N`] ENDS_NOT_IN_SEGMENT) THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?h:real^1->real^N. arc h /\ pl_map_on (interval[vec 0,vec 1]) h /\
                                   path_image h = a /\ {p,q} = {pathstart h,pathfinish h}`
  STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `(f:real^N->real^N) o linepath(x0,x1)` THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC ARC_CONTINUOUS_IMAGE THEN
      ASM_SIMP_TAC[ARC_LINEPATH; PATH_IMAGE_LINEPATH] THEN ASM_MESON_TAC[];
      MATCH_MP_TAC PL_MAP_ON_COMPOSE THEN EXISTS_TAC `segment[x0:real^N,x1]` THEN
      ASM_SIMP_TAC[MOI_PL2_PL_LINEPATH; MOI_PL2_LOCALLY_POLYHEDRAL_INTERVAL] THEN
      REWRITE_TAC[GSYM path_image; PATH_IMAGE_LINEPATH; SUBSET_REFL];
      ASM_REWRITE_TAC[PATH_IMAGE_COMPOSE; PATH_IMAGE_LINEPATH];
      ASM_REWRITE_TAC[PATHSTART_COMPOSE; PATHFINISH_COMPOSE;
                      PATHSTART_LINEPATH; PATHFINISH_LINEPATH; IMAGE_CLAUSES]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(pathstart h = p /\ pathfinish h = q) \/
                (pathstart h = q /\ pathfinish (h:real^1->real^N) = p)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `{p:real^N,q} = {pathstart h,pathfinish h}` THEN
    UNDISCH_TAC `~(p:real^N = q)` THEN SET_TAC[];
    EXISTS_TAC `h:real^1->real^N` THEN ASM_REWRITE_TAC[];
    EXISTS_TAC `reversepath h:real^1->real^N` THEN
    ASM_SIMP_TAC[ARC_REVERSEPATH; MOI_PL2_PL_REVERSEPATH; PATH_IMAGE_REVERSEPATH;
                 PATHSTART_REVERSEPATH; PATHFINISH_REVERSEPATH]]);;

(* A segment from an interior point of a convex compact set to an outside *)
(* point meets it in a segment ending on the frontier.                     *)

let MOI_S4P_EXIT = prove
 (`!(s:real^N->bool) x y.
     convex s /\ closed s /\ x IN interior s /\ ~(y IN s)
     ==> ?z. z IN frontier s /\ z IN segment[x,y] /\ ~(z = x) /\
             segment[x,y] INTER s = segment[x,z] /\
             segment[x,z] DELETE z SUBSET interior s`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `x:real^N`; `y:real^N`] SEGMENT_TO_FRONTIER) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[INTERIOR_SUBSET; SUBSET]; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `z:real^N` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(z:real^N) IN s` ASSUME_TAC THENL
   [ASM_MESON_TAC[frontier; IN_DIFF; CLOSURE_CLOSED]; ALL_TAC] THEN
  SUBGOAL_THEN `~((z:real^N) IN interior s)` ASSUME_TAC THENL
   [ASM_MESON_TAC[frontier; IN_DIFF]; ALL_TAC] THEN
  CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[SEGMENT_CLOSED_OPEN] THEN
    MP_TAC(ISPECL [`x:real^N`; `z:real^N`] ENDS_NOT_IN_SEGMENT) THEN
    UNDISCH_TAC `segment(x:real^N,z) SUBSET interior s` THEN
    UNDISCH_TAC `(x:real^N) IN interior s` THEN
    UNDISCH_TAC `~((z:real^N) IN interior s)` THEN SET_TAC[]] THEN
  SUBGOAL_THEN `(x:real^N) IN s` ASSUME_TAC THENL
   [ASM_MESON_TAC[INTERIOR_SUBSET; SUBSET]; ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[SUBSET_INTER] THEN CONJ_TAC THEN MATCH_MP_TAC SEGMENT_SUBSET_CONVEX THEN
    ASM_REWRITE_TAC[CONVEX_SEGMENT; ENDS_IN_SEGMENT]] THEN
  REWRITE_TAC[SUBSET; IN_INTER] THEN X_GEN_TAC `w:real^N` THEN STRIP_TAC THEN
  UNDISCH_TAC `(w:real^N) IN segment[x,y]` THEN REWRITE_TAC[IN_SEGMENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `mu:real` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `(z:real^N) IN segment[x,y]` THEN REWRITE_TAC[IN_SEGMENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `nu:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `&0 < nu` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 <= nu /\ ~(nu = &0) ==> &0 < nu`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    UNDISCH_TAC `~(z:real^N = x)` THEN ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `mu <= nu` THENL
   [EXISTS_TAC `mu / nu` THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[VECTOR_ARITH
       `(&1 - u) % x + u % ((&1 - nu) % x + nu % y):real^N = (&1 - u * nu) % x + (u * nu) % y`] THEN
      ASM_SIMP_TAC[REAL_DIV_RMUL; REAL_LT_IMP_NZ]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(z:real^N) IN interior s` (fun th -> ASM_MESON_TAC[th]) THEN
  SUBGOAL_THEN `segment(x:real^N,w) SUBSET interior s` MP_TAC THENL
   [MATCH_MP_TAC IN_INTERIOR_CLOSURE_CONVEX_SEGMENT THEN ASM_MESON_TAC[CLOSURE_CLOSED];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[IN_SEGMENT] THEN CONJ_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `mu % (y - x:real^N) = vec 0` MP_TAC THENL
     [UNDISCH_TAC `x:real^N = w` THEN ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[VECTOR_MUL_EQ_0; VECTOR_SUB_EQ; DE_MORGAN_THM] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM_MESON_TAC[]];
    ALL_TAC] THEN
  EXISTS_TAC `nu / mu` THEN
  SUBGOAL_THEN `&0 < mu` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
    ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[VECTOR_ARITH
     `(&1 - u) % x + u % ((&1 - mu) % x + mu % y):real^N = (&1 - u * mu) % x + (u * mu) % y`] THEN
    ASM_SIMP_TAC[REAL_DIV_RMUL; REAL_LT_IMP_NZ]]);;

(* ------------------------------------------------------------------------- *)
(* The topological core of the 2D push: swapping crosscuts of a             *)
(* triangle with an extension by the identity, three-point arcs, a chord    *)
(* of the standard triangle, and a crosscut of a PL disk between two of its *)
(* frontier points.                                                         *)
(* ------------------------------------------------------------------------- *)

(* Two crosscuts of a triangle with the same ends are carried onto each    *)
(* other by a PL homeomorphism of the plane that is the identity off the   *)
(* interior of the triangle.                                               *)

let MOI_S4P_SWAP_EXTEND = prove
 (`!(k:real^2->bool) (b:real^1->real^2) b'.
     &2 simplex k /\
     arc b /\ pl_map_on (interval[vec 0,vec 1]) b /\
     arc b' /\ pl_map_on (interval[vec 0,vec 1]) b' /\
     pathstart b' = pathstart b /\ pathfinish b' = pathfinish b /\
     path_image b SUBSET k /\ path_image b' SUBSET k /\
     path_image b INTER relative_frontier k = {pathstart b,pathfinish b} /\
     path_image b' INTER relative_frontier k = {pathstart b,pathfinish b}
     ==> ?w w'. pl_homeomorphism ((:real^2),(:real^2)) (w,w') /\
                (!x. ~(x IN interior k) ==> w x = x) /\ IMAGE w k = k /\
                IMAGE w (path_image b) = path_image b'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `?gam:real^1->real^2.
                  simple_path gam /\ pathfinish gam = pathstart gam /\
                  pl_map_on (interval[vec 0,vec 1]) gam /\
                  path_image gam = relative_frontier k /\
                  relative_frontier k UNION inside(relative_frontier k) = k /\
                  k DIFF interior k = relative_frontier k`
  STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [MOI_PL2_SIMPLEX_2]) THEN
    DISCH_THEN(X_CHOOSE_THEN `k0:real^2` (X_CHOOSE_THEN `k1:real^2` (X_CHOOSE_THEN `k2:real^2`
      STRIP_ASSUME_TAC))) THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    EXISTS_TAC `polygonal_path[k0;k1;k2;k0:real^2]` THEN
    MP_TAC(ISPECL [`k0:real^2`; `k1:real^2`; `k2:real^2`] MOI_PL2_TRIANGLE_POLYGON) THEN
    ASM_SIMP_TAC[MOI_PL2_PL_POLYGONAL_PATH; RELATIVE_FRONTIER_OF_TRIANGLE] THEN
    STRIP_TAC THEN
    REWRITE_TAC[MOI_PL2_TRIANGLE_CLOSED_INSIDE; INTERIOR_OF_TRIANGLE] THEN
    SUBGOAL_THEN `segment[k0:real^2,k1] UNION segment[k1,k2] UNION segment[k2,k0] SUBSET
                  convex hull {k0,k1,k2}` MP_TAC THENL
     [REWRITE_TAC[UNION_SUBSET] THEN REPEAT CONJ_TAC THEN
      MATCH_MP_TAC SEGMENT_SUBSET_CONVEX THEN REWRITE_TAC[CONVEX_CONVEX_HULL] THEN
      CONJ_TAC THEN MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_INSERT];
      SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(pathstart b:real^2 = pathfinish b) /\ pathstart b IN relative_frontier k /\
                pathfinish b IN relative_frontier k`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_MESON_TAC[ARC_DISTINCT_ENDS]; ASM SET_TAC[]]; ALL_TAC] THEN
  MP_TAC(ISPECL [`gam:real^1->real^2`; `pathstart b:real^2`; `pathfinish b:real^2`]
    MOI_SFR_LOOP_SPLIT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `a1:real^1->real^2` (X_CHOOSE_THEN `a2:real^1->real^2`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`a1:real^1->real^2`; `a2:real^1->real^2`; `b:real^1->real^2`;
                 `b':real^1->real^2`; `relative_frontier k:real^2->bool`] MOI_S4P_CROSSCUT_SWAP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^2->real^2` (X_CHOOSE_THEN `g:real^2->real^2`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`k:real^2->bool`; `f:real^2->real^2`; `g:real^2->real^2`]
    MOI_SA2_PLH_EXTEND_ID) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[SIMPLEX_IMP_POLYTOPE];
      X_GEN_TAC `x:real^2` THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  DISCH_TAC THEN
  MAP_EVERY EXISTS_TAC [`\x:real^2. if x IN k then f x else x`;
                        `\x:real^2. if x IN k then g x else x`] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `IMAGE (f:real^2->real^2) k = k` ASSUME_TAC THENL
   [ASM_MESON_TAC[pl_homeomorphism; homeomorphism]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
    MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `IMAGE (f:real^2->real^2) k` THEN
    CONJ_TAC THENL [MATCH_MP_TAC(SET_RULE
      `(!x. x IN k ==> g x = f x) ==> IMAGE (g:real^2->real^2) k = IMAGE f k`) THEN
      SIMP_TAC[]; ASM_REWRITE_TAC[]];
    MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `IMAGE (f:real^2->real^2) (path_image b)` THEN
    CONJ_TAC THENL [MATCH_MP_TAC(SET_RULE
      `(!x. x IN s ==> g x = f x) ==> IMAGE (g:real^2->real^2) s = IMAGE f s`) THEN
      ASM SET_TAC[]; ASM_REWRITE_TAC[]]]);;

(* A polygonal path through three non-collinear points is an arc. *)

let MOI_S4P_ARC3 = prove
 (`!a b c:real^N.
     ~collinear{a,b,c}
     ==> arc(polygonal_path[a;b;c]) /\
         path_image(polygonal_path[a;b;c]) = segment[a,b] UNION segment[b,c] /\
         pathstart(polygonal_path[a;b;c]) = a /\ pathfinish(polygonal_path[a;b;c]) = c`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_PL2_NONCOLLINEAR_DISTINCT) THEN
  REWRITE_TAC[polygonal_path] THEN
  SIMP_TAC[PATH_IMAGE_JOIN; PATHSTART_JOIN; PATHFINISH_JOIN; PATHSTART_LINEPATH;
           PATHFINISH_LINEPATH; PATH_IMAGE_LINEPATH] THEN
  MATCH_MP_TAC ARC_JOIN THEN
  ASM_REWRITE_TAC[ARC_LINEPATH_EQ; PATHSTART_LINEPATH; PATHFINISH_LINEPATH;
                  PATH_IMAGE_LINEPATH] THEN
  REWRITE_TAC[SUBSET; IN_INTER; IN_SING] THEN X_GEN_TAC `z:real^N` THEN STRIP_TAC THEN
  ASM_CASES_TAC `z:real^N = b` THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `~collinear{a:real^N,b,c}` THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC COLLINEAR_3_TRANS THEN EXISTS_TAC `z:real^N` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ONCE_REWRITE_TAC[SET_RULE `{a:real^N,b,z} = {a,z,b}`] THEN
    MATCH_MP_TAC BETWEEN_IMP_COLLINEAR THEN ASM_REWRITE_TAC[BETWEEN_IN_SEGMENT];
    MATCH_MP_TAC BETWEEN_IMP_COLLINEAR THEN ASM_REWRITE_TAC[BETWEEN_IN_SEGMENT]]);;

(* A chord of the standard triangle from vec 0 to basis 1 through its     *)
(* interior.                                                                *)

let MOI_S4P_STD_CHORD = prove
 (`~collinear{vec 0:real^2,inv(&4) % (basis 1 + basis 2),basis 1} /\
   segment[vec 0:real^2,inv(&4) % (basis 1 + basis 2)] UNION
   segment[inv(&4) % (basis 1 + basis 2),basis 1] SUBSET
   convex hull {vec 0,basis 1,basis 2} /\
   (segment[vec 0:real^2,inv(&4) % (basis 1 + basis 2)] UNION
    segment[inv(&4) % (basis 1 + basis 2),basis 1]) INTER
   relative_frontier(convex hull {vec 0,basis 1,basis 2}) = {vec 0,basis 1}`,
  ABBREV_TAC `m:real^2 = inv(&4) % (basis 1 + basis 2)` THEN
  SUBGOAL_THEN `~collinear{vec 0:real^2,basis 1,basis 2}` ASSUME_TAC THENL
   [REWRITE_TAC[MOI_PL2_STD_TRIANGLES]; ALL_TAC] THEN
  SUBGOAL_THEN `(m:real^2)$1 = inv(&4) /\ m$2 = inv(&4) /\
                (basis 1:real^2)$1 = &1 /\ (basis 1:real^2)$2 = &0 /\
                (basis 2:real^2)$1 = &0 /\ (basis 2:real^2)$2 = &1`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "m" THEN
    SIMP_TAC[VECTOR_MUL_COMPONENT; VECTOR_ADD_COMPONENT; BASIS_COMPONENT; DIMINDEX_2; ARITH] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!x y z. &0 < x /\ &0 < y /\ &0 < z /\ x + y + z = &1
                        ==> (x % vec 0 + y % basis 1 + z % basis 2:real^2) IN
                            interior(convex hull {vec 0,basis 1,basis 2})` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN ASM_SIMP_TAC[INTERIOR_CONVEX_HULL_3_MINIMAL; IN_ELIM_THM] THEN
    MAP_EVERY EXISTS_TAC [`x:real`; `y:real`; `z:real`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `interior(convex hull {vec 0:real^2,basis 1,basis 2}) INTER
                relative_frontier(convex hull {vec 0,basis 1,basis 2}) = {}` ASSUME_TAC THENL
   [ASM_SIMP_TAC[INTERIOR_OF_TRIANGLE; RELATIVE_FRONTIER_OF_TRIANGLE] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(m:real^2) IN convex hull {vec 0,basis 1,basis 2}` ASSUME_TAC THENL
   [REWRITE_TAC[CONVEX_HULL_3; IN_ELIM_THM] THEN
    MAP_EVERY EXISTS_TAC [`&1 / &2`; `inv(&4)`; `inv(&4)`] THEN
    EXPAND_TAC "m" THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[COLLINEAR_LEMMA; CART_EQ; DIMINDEX_2; FORALL_2; VEC_COMPONENT;
                VECTOR_MUL_COMPONENT] THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC[NOT_EXISTS_THM] THEN REAL_ARITH_TAC;
    REWRITE_TAC[UNION_SUBSET] THEN CONJ_TAC THEN MATCH_MP_TAC SEGMENT_SUBSET_CONVEX THEN
    ASM_REWRITE_TAC[CONVEX_CONVEX_HULL] THEN MATCH_MP_TAC HULL_INC THEN
    REWRITE_TAC[IN_INSERT];
    ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [ALL_TAC;
    ASM_SIMP_TAC[RELATIVE_FRONTIER_OF_TRIANGLE] THEN
    REWRITE_TAC[SUBSET; IN_INSERT; NOT_IN_EMPTY; IN_INTER; IN_UNION] THEN
    MESON_TAC[ENDS_IN_SEGMENT]] THEN
  REWRITE_TAC[SUBSET; IN_INTER; IN_UNION; IN_INSERT; NOT_IN_EMPTY] THEN
  X_GEN_TAC `w:real^2` THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  REWRITE_TAC[IN_SEGMENT] THEN
  DISCH_THEN(DISJ_CASES_THEN (X_CHOOSE_THEN `s:real` STRIP_ASSUME_TAC)) THENL
   [ASM_CASES_TAC `s = &0` THENL
     [DISJ1_TAC THEN ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(w:real^2) IN interior(convex hull {vec 0,basis 1,basis 2})` MP_TAC THENL
     [SUBGOAL_THEN `w = (&1 - s / &2) % vec 0 + (s * inv(&4)) % basis 1 +
                        (s * inv(&4)) % basis 2:real^2` SUBST1_TAC THENL
       [ASM_REWRITE_TAC[] THEN EXPAND_TAC "m" THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      ASM SET_TAC[]];
    ASM_CASES_TAC `s = &1` THENL
     [DISJ2_TAC THEN ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(w:real^2) IN interior(convex hull {vec 0,basis 1,basis 2})` MP_TAC THENL
     [SUBGOAL_THEN `w = ((&1 - s) / &2) % vec 0 + ((&1 - s) * inv(&4) + s) % basis 1 +
                        ((&1 - s) * inv(&4)) % basis 2:real^2` SUBST1_TAC THENL
       [ASM_REWRITE_TAC[] THEN EXPAND_TAC "m" THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      ASM SET_TAC[]]]);;

(* A PL disk has a PL crosscut between any two distinct frontier points. *)

let MOI_S4P_FAR_CUT = prove
 (`!(v:real^2->bool) C t0 t1.
     pl_cell_with_boundary 2 v C /\ t0 IN C /\ t1 IN C /\ ~(t0 = t1)
     ==> ?g. arc g /\ pl_map_on (interval[vec 0,vec 1]) g /\
             pathstart g = t0 /\ pathfinish g = t1 /\
             path_image g SUBSET v /\ path_image g INTER C = {t0,t1}`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_SFR_CELL_FACTS) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `gam:real^1->real^2` STRIP_ASSUME_TAC)
    STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`gam:real^1->real^2`; `t0:real^2`; `t1:real^2`] MOI_SFR_LOOP_SPLIT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^1->real^2` (X_CHOOSE_THEN `h':real^1->real^2`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`v:real^2->bool`; `h:real^1->real^2`; `vec 0:real^2`; `basis 1:real^2`;
                 `basis 2:real^2`] MOI_PL2_BALL_BOUNDARY_ARC) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[MOI_PL2_STD_TRIANGLES] THEN ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^2->real^2` (X_CHOOSE_THEN `f':real^2->real^2`
    STRIP_ASSUME_TAC)) THEN
  ABBREV_TAC `m:real^2 = inv(&4) % (basis 1 + basis 2)` THEN
  ABBREV_TAC `tri = convex hull {vec 0:real^2,basis 1,basis 2}` THEN
  MP_TAC MOI_S4P_STD_CHORD THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&2 simplex (tri:real^2->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "tri" THEN REWRITE_TAC[MOI_PL2_SIMPLEX_2] THEN
    MAP_EVERY EXISTS_TAC [`vec 0:real^2`; `basis 1:real^2`; `basis 2:real^2`] THEN
    REWRITE_TAC[MOI_PL2_STD_TRIANGLES];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`vec 0:real^2`; `m:real^2`; `basis 1:real^2`] MOI_S4P_ARC3) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `homeomorphism (tri,v) (f:real^2->real^2,f') /\ pl_map_on tri f`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `pl_homeomorphism (tri,v) (f:real^2->real^2,f')` THEN
    SIMP_TAC[pl_homeomorphism];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  SUBGOAL_THEN `(f:real^2->real^2) (vec 0) = t0 /\ f (basis 1) = t1` STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM((fun th -> MP_TAC(SPEC `vec 0:real^1` th) THEN MP_TAC(SPEC `vec 1:real^1` th)) o
      check (fun th -> can (find_term (fun t -> is_const t && fst(dest_const t) = "linepath"))
                           (concl th))) THEN
    REWRITE_TAC[ENDS_IN_UNIT_INTERVAL; linepath; DROP_VEC] THEN
    REWRITE_TAC[REAL_SUB_RZERO; REAL_SUB_REFL; VECTOR_MUL_LZERO; VECTOR_MUL_LID;
                VECTOR_MUL_RZERO; VECTOR_ADD_LID; VECTOR_ADD_RID] THEN
    UNDISCH_TAC `pathstart (h:real^1->real^2) = t0` THEN
    UNDISCH_TAC `pathfinish (h:real^1->real^2) = t1` THEN
    REWRITE_TAC[pathstart; pathfinish] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `frontier v = IMAGE (f:real^2->real^2) (relative_frontier tri)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_PL2_FRONTIER_PL_BALL_2 THEN EXISTS_TAC `f':real^2->real^2` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `(f:real^2->real^2) o polygonal_path[vec 0;m;basis 1]` THEN
  ASM_REWRITE_TAC[PATHSTART_COMPOSE; PATHFINISH_COMPOSE; PATH_IMAGE_COMPOSE] THEN
  SUBGOAL_THEN `!x y. x IN tri /\ y IN tri /\ (f:real^2->real^2) x = f y ==> x = y`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `x:real^2 = f'(f x) /\ y = (f':real^2->real^2)(f y)`
      (fun th -> ONCE_REWRITE_TAC[th]) THENL
     [CONJ_TAC THEN CONV_TAC SYM_CONV THEN
      FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `f':real^2->real^2`)) (concl th) &&
        can (find_term ((=) `tri:real^2->bool`)) (concl th))) THEN
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC ARC_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `tri:real^2->bool` THEN
      ASM_REWRITE_TAC[];
      MAP_EVERY X_GEN_TAC [`x:real^2`; `y:real^2`] THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `tri:real^2->bool`)) (concl th) &&
        not (can (find_term ((=) `f':real^2->real^2`)) (concl th)))) THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `segment[vec 0:real^2,m] UNION segment[m,basis 1] SUBSET tri` THEN
      UNDISCH_TAC `(x:real^2) IN segment[vec 0,m] UNION segment[m,basis 1]` THEN
      UNDISCH_TAC `(y:real^2) IN segment[vec 0,m] UNION segment[m,basis 1]` THEN SET_TAC[]];
    MATCH_MP_TAC PL_MAP_ON_COMPOSE THEN EXISTS_TAC `tri:real^2->bool` THEN
    ASM_REWRITE_TAC[MOI_PL2_PL_POLYGONAL_PATH] THEN
    REWRITE_TAC[GSYM path_image] THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `IMAGE (f:real^2->real^2) tri` THEN
    CONJ_TAC THENL [MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[];
                    ASM_REWRITE_TAC[SUBSET_REFL]];
    SUBGOAL_THEN `C = IMAGE (f:real^2->real^2) (relative_frontier tri)` SUBST1_TAC THENL
     [UNDISCH_TAC `frontier v = IMAGE (f:real^2->real^2) (relative_frontier tri)` THEN
      UNDISCH_TAC `frontier v = (C:real^2->bool)` THEN
      DISCH_THEN SUBST1_TAC THEN DISCH_THEN ACCEPT_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `relative_frontier tri SUBSET (tri:real^2->bool)` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`tri:real^2->bool`; `&2:int`] SIMPLEX_IMP_CLOSED) THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[relative_frontier; CLOSURE_CLOSED] THEN SET_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `IMAGE (f:real^2->real^2)
                 ((segment[vec 0,m] UNION segment[m,basis 1]) INTER relative_frontier tri)` THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `!x y. x IN tri /\ y IN tri /\ (f:real^2->real^2) x = f y ==> x = y` THEN
      UNDISCH_TAC `segment[vec 0:real^2,m] UNION segment[m,basis 1] SUBSET tri` THEN
      UNDISCH_TAC `relative_frontier tri SUBSET (tri:real^2->bool)` THEN SET_TAC[];
      ASM_REWRITE_TAC[IMAGE_CLAUSES]]]);;

(* ------------------------------------------------------------------------- *)
(* The side argument and the topological core of the 2D push                *)
(* (MOI_S4P_PUSH_TRI): in a triangle k, the crosscut tau INTER k is moved   *)
(* to the far side of the crosscut rho INTER k by a PL homeomorphism of the *)
(* plane that is the identity off the interior of k.                       *)
(* ------------------------------------------------------------------------- *)

(* The side argument: in a disk k split by the crosscut R = rho INTER k   *)
(* into closed pieces u and v, a connected set W reached from a crossing   *)
(* point x of R through the side of rho opposite to a set S inside u lies  *)
(* in v.                                                                    *)

let MOI_S4P_SIDE_ARG = prove
 (`!(u:real^2->bool) v k R rho n g1 g2 S W x.
     closed u /\ closed v /\ u UNION v = k /\ u INTER v = R /\ rho INTER k = R /\
     closure(interior v) = v /\ interior v INTER R = {} /\
     (!s. connected s /\ s SUBSET k /\ s INTER R = {} ==> s SUBSET u \/ s SUBSET v) /\
     S SUBSET u /\ S INTER rho = {} /\
     open n /\ x IN n /\ n SUBSET k /\ x IN rho /\
     n DIFF rho = g1 UNION g2 /\ connected g1 /\ connected g2 /\
     ~(g1 INTER S = {}) /\ ~(g2 INTER W = {}) /\
     connected W /\ W SUBSET k /\ W INTER rho = {}
     ==> W SUBSET v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(g1:real^2->bool) SUBSET k /\ g1 INTER R = {} /\
                (g2:real^2->bool) SUBSET k /\ g2 INTER R = {} /\ W INTER R = {}`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(n:real^2->bool) DIFF rho = g1 UNION g2` THEN
    UNDISCH_TAC `(n:real^2->bool) SUBSET k` THEN UNDISCH_TAC `(rho:real^2->bool) INTER k = R` THEN
    UNDISCH_TAC `(W:real^2->bool) INTER rho = {}` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(g1:real^2->bool) SUBSET u` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `g1:real^2->bool` o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `connected:(real^2->bool)->bool`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `~((g1:real^2->bool) INTER S = {})` THEN
    UNDISCH_TAC `(S:real^2->bool) SUBSET u` THEN UNDISCH_TAC `(S:real^2->bool) INTER rho = {}` THEN
    UNDISCH_TAC `(u:real^2->bool) INTER v = R` THEN UNDISCH_TAC `(rho:real^2->bool) INTER k = R` THEN
    UNDISCH_TAC `(g1:real^2->bool) INTER R = {}` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(g2:real^2->bool) SUBSET v` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `g2:real^2->bool` o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `connected:(real^2->bool)->bool`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(TAUT `~p ==> p \/ q ==> q`) THEN DISCH_TAC THEN
    SUBGOAL_THEN `(n:real^2->bool) SUBSET u` ASSUME_TAC THENL
     [UNDISCH_TAC `(n:real^2->bool) DIFF rho = g1 UNION g2` THEN
      UNDISCH_TAC `(g1:real^2->bool) SUBSET u` THEN UNDISCH_TAC `(g2:real^2->bool) SUBSET u` THEN
      UNDISCH_TAC `(n:real^2->bool) SUBSET k` THEN UNDISCH_TAC `(rho:real^2->bool) INTER k = R` THEN
      UNDISCH_TAC `(u:real^2->bool) INTER v = R` THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `~((n:real^2->bool) INTER interior v = {})` MP_TAC THENL
     [MP_TAC(ISPECL [`n:real^2->bool`; `interior v:real^2->bool`] OPEN_INTER_CLOSURE_EQ_EMPTY) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      UNDISCH_TAC `(x:real^2) IN n` THEN UNDISCH_TAC `(x:real^2) IN rho` THEN
      UNDISCH_TAC `(n:real^2->bool) SUBSET k` THEN UNDISCH_TAC `(rho:real^2->bool) INTER k = R` THEN
      UNDISCH_TAC `(u:real^2->bool) INTER v = R` THEN SET_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPEC `v:real^2->bool` INTERIOR_SUBSET) THEN
    UNDISCH_TAC `(n:real^2->bool) SUBSET u` THEN UNDISCH_TAC `(u:real^2->bool) INTER v = R` THEN
    UNDISCH_TAC `interior(v:real^2->bool) INTER R = {}` THEN SET_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `W:real^2->bool` o check (fun th ->
    is_forall(concl th) && can (find_term ((=) `connected:(real^2->bool)->bool`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `~p ==> p \/ q ==> q`) THEN DISCH_TAC THEN
  UNDISCH_TAC `~((g2:real^2->bool) INTER W = {})` THEN
  UNDISCH_TAC `(W:real^2->bool) SUBSET u` THEN UNDISCH_TAC `(g2:real^2->bool) SUBSET v` THEN
  UNDISCH_TAC `(u:real^2->bool) INTER v = R` THEN UNDISCH_TAC `(W:real^2->bool) INTER R = {}` THEN
  SET_TAC[]);;

(* The topological core of the 2D push.  In a triangle k, the crosscut     *)
(* b = tau INTER k is replaced by a crosscut on the far side of the        *)
(* crosscut c = rho INTER k; the far side is found from the local sides of *)
(* rho at the two crossing points p and q.                                 *)

let MOI_S4P_PUSH_TRI = prove
 (`!(k:real^2->bool) (b:real^1->real^2) c tau rho S Wp Wq p q.
     &2 simplex k /\
     arc b /\ pl_map_on (interval[vec 0,vec 1]) b /\ path_image b = tau INTER k /\
     path_image b INTER relative_frontier k = {pathstart b,pathfinish b} /\
     arc c /\ pl_map_on (interval[vec 0,vec 1]) c /\ path_image c = rho INTER k /\
     path_image c INTER relative_frontier k = {pathstart c,pathfinish c} /\
     ~(pathstart b IN rho) /\ ~(pathfinish b IN rho) /\
     connected S /\ S SUBSET k /\ S INTER rho = {} /\
     connected Wp /\ Wp SUBSET k /\ Wp INTER rho = {} /\ pathstart b IN closure Wp /\
     connected Wq /\ Wq SUBSET k /\ Wq INTER rho = {} /\ pathfinish b IN closure Wq /\
     p IN rho /\ q IN rho /\
     (?n g1 g2. open n /\ p IN n /\ n SUBSET k /\ n DIFF rho = g1 UNION g2 /\
                connected g1 /\ connected g2 /\ ~(g1 INTER S = {}) /\ ~(g2 INTER Wp = {})) /\
     (?n g1 g2. open n /\ q IN n /\ n SUBSET k /\ n DIFF rho = g1 UNION g2 /\
                connected g1 /\ connected g2 /\ ~(g1 INTER S = {}) /\ ~(g2 INTER Wq = {}))
     ==> ?w w'. pl_homeomorphism ((:real^2),(:real^2)) (w,w') /\
                (!x. ~(x IN interior k) ==> w x = x) /\ IMAGE w k = k /\
                IMAGE w (tau INTER k) INTER rho = {}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `?gam:real^1->real^2.
                  simple_path gam /\ pathfinish gam = pathstart gam /\
                  pl_map_on (interval[vec 0,vec 1]) gam /\
                  path_image gam = relative_frontier k /\
                  relative_frontier k UNION inside(relative_frontier k) = k /\
                  inside(relative_frontier k) INTER relative_frontier k = {} /\
                  interior k = inside(relative_frontier k)`
  STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [MOI_PL2_SIMPLEX_2]) THEN
    DISCH_THEN(X_CHOOSE_THEN `k0:real^2` (X_CHOOSE_THEN `k1:real^2` (X_CHOOSE_THEN `k2:real^2`
      STRIP_ASSUME_TAC))) THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    EXISTS_TAC `polygonal_path[k0;k1;k2;k0:real^2]` THEN
    MP_TAC(ISPECL [`k0:real^2`; `k1:real^2`; `k2:real^2`] MOI_PL2_TRIANGLE_POLYGON) THEN
    ASM_SIMP_TAC[MOI_PL2_PL_POLYGONAL_PATH; RELATIVE_FRONTIER_OF_TRIANGLE] THEN
    STRIP_TAC THEN
    REWRITE_TAC[MOI_PL2_TRIANGLE_CLOSED_INSIDE; INTERIOR_OF_TRIANGLE; INSIDE_NO_OVERLAP] THEN
    REWRITE_TAC[INSIDE_OF_TRIANGLE; INTERIOR_OF_TRIANGLE];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(pathstart c:real^2 = pathfinish c) /\ pathstart c IN relative_frontier k /\
                pathfinish c IN relative_frontier k /\
                ~(pathstart b:real^2 = pathfinish b) /\ pathstart b IN relative_frontier k /\
                pathfinish b IN relative_frontier k`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN MATCH_MP_TAC ARC_DISTINCT_ENDS THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `path_image c INTER relative_frontier k = {pathstart c,pathfinish (c:real^1->real^2)}` THEN
      SET_TAC[];
      UNDISCH_TAC `path_image c INTER relative_frontier k = {pathstart c,pathfinish (c:real^1->real^2)}` THEN
      SET_TAC[];
      ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN MATCH_MP_TAC ARC_DISTINCT_ENDS THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `path_image b INTER relative_frontier k = {pathstart b,pathfinish (b:real^1->real^2)}` THEN
      SET_TAC[];
      UNDISCH_TAC `path_image b INTER relative_frontier k = {pathstart b,pathfinish (b:real^1->real^2)}` THEN
      SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`gam:real^1->real^2`; `pathstart c:real^2`; `pathfinish c:real^2`]
    MOI_SFR_LOOP_SPLIT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `a1:real^1->real^2` (X_CHOOSE_THEN `a2:real^1->real^2`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN
   `?u v C2. closed u /\ closed v /\ u UNION v = k /\ u INTER v = path_image c /\
             closure(interior v) = v /\ interior v INTER path_image c = {} /\
             (!s. connected s /\ s SUBSET k /\ s INTER path_image c = {}
                  ==> s SUBSET u \/ s SUBSET v) /\
             pl_cell_with_boundary 2 v C2 /\ v INTER relative_frontier k SUBSET C2 /\
             path_image c SUBSET C2 /\ (S:real^2->bool) SUBSET u`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`a1:real^1->real^2`; `a2:real^1->real^2`; `c:real^1->real^2`;
                   `relative_frontier k:real^2->bool`;
                   `(path_image a1 UNION path_image c) UNION
                    inside(path_image a1 UNION path_image (c:real^1->real^2))`;
                   `(path_image a2 UNION path_image c) UNION
                    inside(path_image a2 UNION path_image (c:real^1->real^2))`]
      MOI_SFR_THETA) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN SET_TAC[]; ALL_TAC] THEN
    ABBREV_TAC `u = (path_image a1 UNION path_image c) UNION
                    inside(path_image a1 UNION path_image (c:real^1->real^2))` THEN
    ABBREV_TAC `v = (path_image a2 UNION path_image c) UNION
                    inside(path_image a2 UNION path_image (c:real^1->real^2))` THEN
    REWRITE_TAC[ASSUME `relative_frontier k UNION inside(relative_frontier k) = (k:real^2->bool)`] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `(u:real^2->bool) SUBSET k /\ (v:real^2->bool) SUBSET k` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(u:real^2->bool) UNION v = k` THEN SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `interior(u:real^2->bool) SUBSET inside(relative_frontier k) /\
                  interior(v:real^2->bool) SUBSET inside(relative_frontier k)` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `interior(k:real^2->bool) = inside(relative_frontier k)` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN CONJ_TAC THEN MATCH_MP_TAC SUBSET_INTERIOR THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPEC `path_image a1 UNION path_image (c:real^1->real^2)` INSIDE_NO_OVERLAP) THEN
    MP_TAC(ISPEC `path_image a2 UNION path_image (c:real^1->real^2)` INSIDE_NO_OVERLAP) THEN
    REPEAT DISCH_TAC THEN
    SUBGOAL_THEN
     `closed(u:real^2->bool) /\ closed(v:real^2->bool) /\ v UNION u = k /\
      v INTER u = path_image c /\
      interior u INTER path_image c = {} /\ interior v INTER path_image c = {} /\
      u INTER relative_frontier k SUBSET path_image a1 UNION path_image c /\
      v INTER relative_frontier k SUBSET path_image a2 UNION path_image c /\
      path_image c SUBSET path_image a1 UNION path_image c /\
      path_image c SUBSET path_image a2 UNION path_image (c:real^1->real^2) /\
      (!s. connected s /\ s SUBSET k /\ s INTER path_image c = {}
           ==> s SUBSET v \/ s SUBSET u)`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC COMPACT_IMP_CLOSED THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC COMPACT_IMP_CLOSED THEN ASM_REWRITE_TAC[];
        UNDISCH_TAC `(u:real^2->bool) UNION v = k` THEN SET_TAC[];
        UNDISCH_TAC `(u:real^2->bool) INTER v = path_image c` THEN SET_TAC[];
        UNDISCH_TAC `interior(u:real^2->bool) = inside(path_image a1 UNION path_image c)` THEN
        DISCH_THEN SUBST1_TAC THEN
        UNDISCH_TAC `inside(path_image a1 UNION path_image (c:real^1->real^2)) INTER
                     (path_image a1 UNION path_image c) = {}` THEN SET_TAC[];
        UNDISCH_TAC `interior(v:real^2->bool) = inside(path_image a2 UNION path_image c)` THEN
        DISCH_THEN SUBST1_TAC THEN
        UNDISCH_TAC `inside(path_image a2 UNION path_image (c:real^1->real^2)) INTER
                     (path_image a2 UNION path_image c) = {}` THEN SET_TAC[];
        UNDISCH_TAC `interior(u:real^2->bool) SUBSET inside(relative_frontier k)` THEN
        UNDISCH_TAC `inside(relative_frontier k) INTER relative_frontier (k:real^2->bool) = {}` THEN
        UNDISCH_TAC `interior(u:real^2->bool) = inside(path_image a1 UNION path_image c)` THEN
        UNDISCH_TAC `(path_image a1 UNION path_image c) UNION
                     inside(path_image a1 UNION path_image (c:real^1->real^2)) = u` THEN
        SET_TAC[];
        UNDISCH_TAC `interior(v:real^2->bool) SUBSET inside(relative_frontier k)` THEN
        UNDISCH_TAC `inside(relative_frontier k) INTER relative_frontier (k:real^2->bool) = {}` THEN
        UNDISCH_TAC `interior(v:real^2->bool) = inside(path_image a2 UNION path_image c)` THEN
        UNDISCH_TAC `(path_image a2 UNION path_image c) UNION
                     inside(path_image a2 UNION path_image (c:real^1->real^2)) = v` THEN
        SET_TAC[];
        SET_TAC[];
        SET_TAC[];
        X_GEN_TAC `s:real^2->bool` THEN STRIP_TAC THEN ONCE_REWRITE_TAC[DISJ_SYM] THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
          can (find_term ((=) `connected:(real^2->bool)->bool`)) (concl th))) THEN
        ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    MP_TAC(SPEC `S:real^2->bool` (ASSUME
     `!s. connected s /\ s SUBSET k /\ s INTER path_image c = {}
          ==> s SUBSET u \/ s SUBSET (v:real^2->bool)`)) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(S:real^2->bool) INTER rho = {}` THEN
      UNDISCH_TAC `path_image c = (rho:real^2->bool) INTER k` THEN SET_TAC[];
      ALL_TAC] THEN
    STRIP_TAC THENL
     [MAP_EVERY EXISTS_TAC [`u:real^2->bool`; `v:real^2->bool`;
                            `path_image a2 UNION path_image (c:real^1->real^2)`] THEN
      REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      MAP_EVERY EXISTS_TAC [`v:real^2->bool`; `u:real^2->bool`;
                            `path_image a1 UNION path_image (c:real^1->real^2)`] THEN
      REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  UNDISCH_THEN `path_image c = (rho:real^2->bool) INTER k` (ASSUME_TAC o SYM) THEN
  SUBGOAL_THEN `(Wp:real^2->bool) SUBSET v /\ (Wq:real^2->bool) SUBSET v` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC MOI_S4P_SIDE_ARG THENL
     [MAP_EVERY EXISTS_TAC [`u:real^2->bool`; `k:real^2->bool`; `path_image(c:real^1->real^2)`;
                            `rho:real^2->bool`; `n:real^2->bool`; `g1:real^2->bool`;
                            `g2:real^2->bool`; `S:real^2->bool`; `p:real^2`];
      MAP_EVERY EXISTS_TAC [`u:real^2->bool`; `k:real^2->bool`; `path_image(c:real^1->real^2)`;
                            `rho:real^2->bool`; `n':real^2->bool`; `g1':real^2->bool`;
                            `g2':real^2->bool`; `S:real^2->bool`; `q:real^2`]] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `pathstart b IN (v:real^2->bool) /\ pathfinish b IN v` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC(SET_RULE `!s. (x:real^2) IN s /\ s SUBSET t ==> x IN t`) THENL
     [EXISTS_TAC `closure(Wp:real^2->bool)`; EXISTS_TAC `closure(Wq:real^2->bool)`] THEN
    ASM_SIMP_TAC[CLOSURE_MINIMAL];
    ALL_TAC] THEN
  SUBGOAL_THEN `pathstart b IN (C2:real^2->bool) /\ pathfinish b IN C2` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(v:real^2->bool) INTER relative_frontier k SUBSET C2` THEN
    UNDISCH_TAC `pathstart b IN (v:real^2->bool)` THEN UNDISCH_TAC `pathfinish b IN (v:real^2->bool)` THEN
    UNDISCH_TAC `pathstart b IN relative_frontier (k:real^2->bool)` THEN
    UNDISCH_TAC `pathfinish b IN relative_frontier (k:real^2->bool)` THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`v:real^2->bool`; `C2:real^2->bool`; `pathstart b:real^2`; `pathfinish b:real^2`]
    MOI_S4P_FAR_CUT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^1->real^2` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(v:real^2->bool) SUBSET k` ASSUME_TAC THENL
   [UNDISCH_TAC `(u:real^2->bool) UNION v = k` THEN SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`k:real^2->bool`; `b:real^1->real^2`; `g:real^1->real^2`] MOI_S4P_SWAP_EXTEND) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `path_image b = (tau:real^2->bool) INTER k` THEN SET_TAC[];
      UNDISCH_TAC `path_image g SUBSET (v:real^2->bool)` THEN
      UNDISCH_TAC `(v:real^2->bool) SUBSET k` THEN SET_TAC[];
      UNDISCH_TAC `path_image g SUBSET (v:real^2->bool)` THEN
      UNDISCH_TAC `(v:real^2->bool) INTER relative_frontier k SUBSET C2` THEN
      UNDISCH_TAC `path_image g INTER C2 = {pathstart b,pathfinish (b:real^1->real^2)}` THEN
      UNDISCH_TAC `pathstart b IN relative_frontier (k:real^2->bool)` THEN
      UNDISCH_TAC `pathfinish b IN relative_frontier (k:real^2->bool)` THEN
      SUBGOAL_THEN `pathstart g IN path_image g /\ pathfinish g IN path_image (g:real^1->real^2)`
      MP_TAC THENL [REWRITE_TAC[PATHSTART_IN_PATH_IMAGE; PATHFINISH_IN_PATH_IMAGE]; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `w:real^2->real^2` THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `w':real^2->real^2` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `tau INTER k = path_image(b:real^1->real^2)` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `path_image g SUBSET (v:real^2->bool)` THEN
  UNDISCH_TAC `(v:real^2->bool) SUBSET k` THEN
  UNDISCH_TAC `rho INTER k = path_image(c:real^1->real^2)` THEN
  UNDISCH_TAC `path_image c SUBSET (C2:real^2->bool)` THEN
  UNDISCH_TAC `path_image g INTER C2 = {pathstart b,pathfinish (b:real^1->real^2)}` THEN
  UNDISCH_TAC `~(pathstart b IN (rho:real^2->bool))` THEN
  UNDISCH_TAC `~(pathfinish b IN (rho:real^2->bool))` THEN
  SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The 2D push in standard position (the bigon d is a triangle t):           *)
(* helper lemmas and MOI_S4P_PUSH2_STD.                                      *)
(* ------------------------------------------------------------------------- *)

(* An arc extended at both ends by segments meeting it only at its ends. *)

let MOI_S4P_ARC_WHISKERS = prove
 (`!(g:real^1->real^N) x0 x1.
     arc g /\ pl_map_on (interval[vec 0,vec 1]) g /\
     ~(x0 = pathstart g) /\ ~(x1 = pathfinish g) /\
     segment[x0,pathstart g] INTER path_image g = {pathstart g} /\
     segment[pathfinish g,x1] INTER path_image g = {pathfinish g} /\
     segment[x0,pathstart g] INTER segment[pathfinish g,x1] = {}
     ==> arc(linepath(x0,pathstart g) ++ (g ++ linepath(pathfinish g,x1))) /\
         pl_map_on (interval[vec 0,vec 1])
           (linepath(x0,pathstart g) ++ (g ++ linepath(pathfinish g,x1))) /\
         pathstart(linepath(x0,pathstart g) ++ (g ++ linepath(pathfinish g,x1))) = x0 /\
         pathfinish(linepath(x0,pathstart g) ++ (g ++ linepath(pathfinish g,x1))) = x1 /\
         path_image(linepath(x0,pathstart g) ++ (g ++ linepath(pathfinish g,x1))) =
           segment[x0,pathstart g] UNION path_image g UNION segment[pathfinish g,x1]`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `arc(g ++ linepath(pathfinish g,x1:real^N)) /\
                path_image(g ++ linepath(pathfinish g,x1:real^N)) =
                path_image g UNION segment[pathfinish g,x1]`
  STRIP_ASSUME_TAC THENL
   [SIMP_TAC[PATH_IMAGE_JOIN; PATHSTART_LINEPATH; PATH_IMAGE_LINEPATH] THEN
    MATCH_MP_TAC ARC_JOIN THEN
    ASM_REWRITE_TAC[ARC_LINEPATH_EQ; PATHSTART_LINEPATH; PATH_IMAGE_LINEPATH] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[PATHSTART_JOIN; PATHFINISH_JOIN; PATHSTART_LINEPATH; PATHFINISH_LINEPATH] THEN
  SIMP_TAC[PATH_IMAGE_JOIN; PATHSTART_JOIN; PATHFINISH_LINEPATH; PATHSTART_LINEPATH] THEN
  ASM_REWRITE_TAC[PATH_IMAGE_LINEPATH] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC ARC_JOIN THEN
    ASM_REWRITE_TAC[ARC_LINEPATH_EQ; PATHSTART_LINEPATH; PATHFINISH_LINEPATH;
                    PATHSTART_JOIN; PATH_IMAGE_LINEPATH] THEN
    ASM SET_TAC[];
    MATCH_MP_TAC MOI_PL2_PL_JOINPATHS THEN
    SIMP_TAC[MOI_PL2_PL_LINEPATH; MOI_PL2_LOCALLY_POLYHEDRAL_INTERVAL;
             PATHFINISH_LINEPATH; PATHSTART_JOIN] THEN
    MATCH_MP_TAC MOI_PL2_PL_JOINPATHS THEN
    ASM_SIMP_TAC[MOI_PL2_PL_LINEPATH; MOI_PL2_LOCALLY_POLYHEDRAL_INTERVAL; PATHSTART_LINEPATH]]);;

(* Small facts for the 2D push in standard position. *)

let MOI_S4P_ARC_ENDS_LIMIT = prove
 (`!g:real^1->real^N.
     arc g
     ==> closed(path_image g) /\
         pathstart g IN closure(path_image g DELETE pathstart g) /\
         pathfinish g IN closure(path_image g DELETE pathfinish g)`,
  REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC COMPACT_IMP_CLOSED THEN MATCH_MP_TAC COMPACT_PATH_IMAGE THEN
    ASM_SIMP_TAC[ARC_IMP_PATH];
    MP_TAC(ISPECL [`g:real^1->real^N`; `{pathstart g:real^N}`] MOI_SFR_ARC_DENSE);
    MP_TAC(ISPECL [`g:real^1->real^N`; `{pathfinish g:real^N}`] MOI_SFR_ARC_DENSE)] THEN
  ASM_REWRITE_TAC[FINITE_SING; SET_RULE `(s:real^N->bool) DIFF {x} = s DELETE x`] THEN
  REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[PATHSTART_IN_PATH_IMAGE; PATHFINISH_IN_PATH_IMAGE]);;

let MOI_S4P_CBALL_DISJ = prove
 (`!(p:real^N) q rp rq. rp + rq < norm(q - p) ==> cball(p,rp) INTER cball(q,rq) = {}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[EXTENSION; IN_INTER; IN_CBALL; NOT_IN_EMPTY] THEN
  X_GEN_TAC `z:real^N` THEN POP_ASSUM MP_TAC THEN NORM_ARITH_TAC);;

let MOI_S4P_SEG_CBALL = prove
 (`!(x:real^N) u r. norm(u - x) = r ==> segment[x,u] SUBSET cball(x,r)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SEGMENT_SUBSET_CONVEX THEN
  REWRITE_TAC[CONVEX_CBALL; IN_CBALL; DIST_REFL] THEN
  POP_ASSUM MP_TAC THEN NORM_ARITH_TAC);;

(* tau INTER k from the corner descriptions and a bad set avoided by k. *)

let MOI_S4P_DESC = prove
 (`!(tau:real^2->bool) a k Cp Cq Bp Bq Ep Eq Wp Wq.
     tau INTER Cp = (a INTER Cp) UNION Ep /\ tau INTER Cq = (a INTER Cq) UNION Eq /\
     Bp SUBSET Cp /\ Bq SUBSET Cq /\ a SUBSET tau /\ a SUBSET k /\
     k INTER (closure(tau DIFF a) DIFF (Bp UNION Bq)) = {} /\
     Ep INTER k = Wp /\ Eq INTER k = Wq /\ Ep SUBSET tau /\ Eq SUBSET tau
     ==> tau INTER k = a UNION Wp UNION Wq`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `tau DIFF a:real^2->bool` CLOSURE_SUBSET) THEN
  UNDISCH_TAC `tau INTER Cp = (a INTER Cp) UNION (Ep:real^2->bool)` THEN
  UNDISCH_TAC `tau INTER Cq = (a INTER Cq) UNION (Eq:real^2->bool)` THEN
  UNDISCH_TAC `(Bp:real^2->bool) SUBSET Cp` THEN UNDISCH_TAC `(Bq:real^2->bool) SUBSET Cq` THEN
  UNDISCH_TAC `(a:real^2->bool) SUBSET tau` THEN UNDISCH_TAC `(a:real^2->bool) SUBSET k` THEN
  UNDISCH_TAC `k INTER (closure(tau DIFF a) DIFF (Bp UNION Bq)) = {}:real^2->bool` THEN
  UNDISCH_TAC `(Ep:real^2->bool) INTER k = Wp` THEN UNDISCH_TAC `(Eq:real^2->bool) INTER k = Wq` THEN
  UNDISCH_TAC `(Ep:real^2->bool) SUBSET tau` THEN UNDISCH_TAC `(Eq:real^2->bool) SUBSET tau` THEN
  SET_TAC[]);;

let MOI_S4P_WHISKER_OUT = prove
 (`!(x:real^N) u r s. &0 < r /\ norm(u - x) = r /\ segment[x,u] INTER s = {x} ==> ~(u IN s)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `u:real^N = x` SUBST_ALL_TAC THENL
   [UNDISCH_TAC `segment[x:real^N,u] INTER s = {x}` THEN UNDISCH_TAC `(u:real^N) IN s` THEN
    MP_TAC(ISPECL [`x:real^N`; `u:real^N`] ENDS_IN_SEGMENT) THEN SET_TAC[];
    UNDISCH_TAC `norm(x - x:real^N) = r` THEN REWRITE_TAC[VECTOR_SUB_REFL; NORM_0] THEN
    ASM_REAL_ARITH_TAC]);;

(* A triangle in the plane minus one of its two boundary arcs is connected *)
(* and misses that arc's complement curve; and the triangle has interior.  *)

let MOI_S4P_SIMPLEX2_INTERIOR = prove
 (`!t:real^2->bool. &2 simplex t ==> ~(interior t = {})`,
  GEN_TAC THEN REWRITE_TAC[MOI_PL2_SIMPLEX_2] THEN
  DISCH_THEN(X_CHOOSE_THEN `v0:real^2` (X_CHOOSE_THEN `v1:real^2` (X_CHOOSE_THEN `v2:real^2`
    STRIP_ASSUME_TAC))) THEN
  ASM_SIMP_TAC[INTERIOR_CONVEX_HULL_3_MINIMAL; GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
  EXISTS_TAC `inv(&3) % v0 + inv(&3) % v1 + inv(&3) % v2:real^2` THEN
  MAP_EVERY EXISTS_TAC [`inv(&3)`; `inv(&3)`; `inv(&3)`] THEN REWRITE_TAC[] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV);;

let MOI_S4P_TRI_MINUS_ARC = prove
 (`!(t:real^2->bool) a'.
     &2 simplex t /\ a' SUBSET relative_frontier t
     ==> connected(t DIFF a') /\ t DIFF a' SUBSET closure(interior t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `convex(t:real^2->bool) /\ closed t /\ ~(interior t = {})` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[SIMPLEX_IMP_CONVEX; SIMPLEX_IMP_CLOSED; MOI_S4P_SIMPLEX2_INTERIOR]; ALL_TAC] THEN
  SUBGOAL_THEN `closure(interior t) = (t:real^2->bool)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[CONVEX_CLOSURE_INTERIOR; CLOSURE_CLOSED]; ALL_TAC] THEN
  SUBGOAL_THEN `interior(t:real^2->bool) SUBSET t DIFF a'` ASSUME_TAC THENL
   [MP_TAC(ISPEC `t:real^2->bool` INTERIOR_SUBSET) THEN
    UNDISCH_TAC `(a':real^2->bool) SUBSET relative_frontier t` THEN
    ASM_SIMP_TAC[relative_frontier; RELATIVE_INTERIOR_NONEMPTY_INTERIOR; CLOSURE_CLOSED] THEN
    SET_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CONNECTED_INTERMEDIATE_CLOSURE THEN
    EXISTS_TAC `interior(t:real^2->bool)` THEN
    ASM_SIMP_TAC[CONVEX_CONNECTED; CONVEX_INTERIOR] THEN SET_TAC[];
    ASM_REWRITE_TAC[] THEN SET_TAC[]]);;

(* The 2D push in standard position: the bigon is a triangle t bounded by  *)
(* the arcs a (in tau) and a' (in rho) with ends p and q, where tau and    *)
(* rho cross.                                                               *)

let MOI_S4P_PUSH2_STD = prove
 (`!(t:real^2->bool) a a' tau rho p q oo.
     &2 simplex t /\ p IN relative_frontier t /\ q IN relative_frontier t /\ ~(p = q) /\
     a UNION a' = relative_frontier t /\ a INTER a' = {p,q} /\
     pl_cell_with_boundary 1 a {p,q} /\ pl_cell_with_boundary 1 a' {p,q} /\
     tau INTER t = a /\ rho INTER t = a' /\
     closure(tau DIFF a) INTER t SUBSET {p,q} /\ closure(rho DIFF a') INTER t SUBSET {p,q} /\
     pl_curve_crossing_at (:real^2) tau rho p /\ pl_curve_crossing_at (:real^2) tau rho q /\
     open oo /\ t SUBSET oo
     ==> ?w w' K. pl_homeomorphism ((:real^2),(:real^2)) (w,w') /\
                  &2 simplex K /\ compact K /\ t SUBSET interior K /\ K SUBSET oo /\
                  (!x. ~(x IN interior K) ==> w x = x) /\ IMAGE w K = K /\
                  tau INTER rho INTER K = {p,q} /\
                  IMAGE w tau INTER rho INTER K = {}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`a:real^2->bool`; `p:real^2`; `q:real^2`] MOI_S4P_CELL1_ARC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `ga:real^1->real^2` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`a':real^2->bool`; `p:real^2`; `q:real^2`] MOI_S4P_CELL1_ARC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `ga':real^1->real^2` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPEC `ga:real^1->real^2` MOI_S4P_ARC_ENDS_LIMIT) THEN
  MP_TAC(ISPEC `ga':real^1->real^2` MOI_S4P_ARC_ENDS_LIMIT) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(a:real^2->bool) SUBSET t /\ (a':real^2->bool) SUBSET t /\
                a SUBSET tau /\ a' SUBSET rho /\
                (p:real^2) IN a /\ q IN a /\ p IN a' /\ q IN a' /\ p IN t /\ q IN t`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(tau:real^2->bool) INTER t = a` THEN
    UNDISCH_TAC `(rho:real^2->bool) INTER t = a'` THEN
    UNDISCH_TAC `(a:real^2->bool) INTER a' = {p,q}` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < norm(q - p:real^2)` ASSUME_TAC THENL
   [REWRITE_TAC[NORM_POS_LT; VECTOR_SUB_EQ] THEN
    MP_TAC(ASSUME `~(p:real^2 = q)`) THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:real^2->bool`; `a:real^2->bool`; `a':real^2->bool`; `tau:real^2->bool`;
                 `rho:real^2->bool`; `p:real^2`; `q:real^2`; `norm(q - p:real^2) / &3`]
    MOI_S4P_CORNER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `rp:real` (X_CHOOSE_THEN `utp:real^2` (X_CHOOSE_THEN `urp:real^2`
    STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`t:real^2->bool`; `a:real^2->bool`; `a':real^2->bool`; `tau:real^2->bool`;
                 `rho:real^2->bool`; `q:real^2`; `p:real^2`; `norm(q - p:real^2) / &3`]
    MOI_S4P_CORNER) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; SET_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `rq:real` (X_CHOOSE_THEN `utq:real^2` (X_CHOOSE_THEN `urq:real^2`
    STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `~((utp:real^2) IN t) /\ ~((urp:real^2) IN t) /\ ~((utq:real^2) IN t) /\
                ~((urq:real^2) IN t)` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC MOI_S4P_WHISKER_OUT THENL
     [MAP_EVERY EXISTS_TAC [`p:real^2`; `rp:real`];
      MAP_EVERY EXISTS_TAC [`p:real^2`; `rp:real`];
      MAP_EVERY EXISTS_TAC [`q:real^2`; `rq:real`];
      MAP_EVERY EXISTS_TAC [`q:real^2`; `rq:real`]] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `U0 = (oo:real^2->bool) DIFF
                   ((closure(tau DIFF a) DIFF (ball(p,rp) UNION ball(q,rq))) UNION
                    (closure(rho DIFF a') DIFF (ball(p,rp) UNION ball(q,rq))) UNION
                    {utp,urp,utq,urq})` THEN
  SUBGOAL_THEN `open(U0:real^2->bool) /\ t SUBSET U0` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "U0" THEN CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_DIFF THEN ASM_REWRITE_TAC[] THEN
      REPEAT(MATCH_MP_TAC CLOSED_UNION THEN CONJ_TAC) THEN
      TRY(MATCH_MP_TAC CLOSED_DIFF THEN SIMP_TAC[CLOSED_CLOSURE; OPEN_UNION; OPEN_BALL]) THEN
      MATCH_MP_TAC FINITE_IMP_CLOSED THEN REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY];
      MP_TAC(ISPECL [`p:real^2`; `rp:real`] CENTRE_IN_BALL) THEN
      MP_TAC(ISPECL [`q:real^2`; `rq:real`] CENTRE_IN_BALL) THEN
      REWRITE_TAC[ASSUME `&0 < rp`; ASSUME `&0 < rq`] THEN
      UNDISCH_TAC `closure(tau DIFF a) INTER t SUBSET {p:real^2,q}` THEN
      UNDISCH_TAC `closure(rho DIFF a') INTER t SUBSET {p:real^2,q}` THEN
      UNDISCH_TAC `(t:real^2->bool) SUBSET oo` THEN
      UNDISCH_TAC `~((utp:real^2) IN t)` THEN UNDISCH_TAC `~((urp:real^2) IN t)` THEN
      UNDISCH_TAC `~((utq:real^2) IN t)` THEN UNDISCH_TAC `~((urq:real^2) IN t)` THEN
      SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:real^2->bool`; `U0:real^2->bool`] MOI_S4P_ENLARGE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^2->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `convex(k:real^2->bool) /\ closed k /\ compact k /\
                relative_frontier k = k DIFF interior k /\
                (p:real^2) IN interior k /\ q IN interior k /\
                ~(utp IN k) /\ ~(urp IN k) /\ ~(utq IN k) /\ ~(urq IN k) /\
                k SUBSET oo /\
                k INTER (closure(tau DIFF a) DIFF (ball(p,rp) UNION ball(q,rq))) = {} /\
                k INTER (closure(rho DIFF a') DIFF (ball(p,rp) UNION ball(q,rq))) = {}`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `convex(k:real^2->bool) /\ compact k` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[SIMPLEX_IMP_CONVEX; SIMPLEX_IMP_COMPACT]; ALL_TAC] THEN
    ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN
    SUBGOAL_THEN `~(interior(k:real^2->bool) = {})` ASSUME_TAC THENL
     [UNDISCH_TAC `(t:real^2->bool) SUBSET interior k` THEN UNDISCH_TAC `(p:real^2) IN t` THEN
      SET_TAC[];
      ALL_TAC] THEN
    ASM_SIMP_TAC[RELATIVE_FRONTIER_NONEMPTY_INTERIOR; frontier; CLOSURE_CLOSED;
                 COMPACT_IMP_CLOSED] THEN
    UNDISCH_TAC `(t:real^2->bool) SUBSET interior k` THEN
    UNDISCH_TAC `(k:real^2->bool) SUBSET U0` THEN
    UNDISCH_TAC `oo DIFF
                 ((closure(tau DIFF a) DIFF (ball(p,rp) UNION ball(q,rq))) UNION
                  (closure(rho DIFF a') DIFF (ball(p,rp) UNION ball(q,rq))) UNION
                  {utp,urp,utq,urq}) = (U0:real^2->bool)` THEN
    UNDISCH_TAC `(p:real^2) IN t` THEN UNDISCH_TAC `(q:real^2) IN t` THEN
    SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:real^2->bool`; `p:real^2`; `utp:real^2`] MOI_S4P_EXIT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t0:real^2` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`k:real^2->bool`; `p:real^2`; `urp:real^2`] MOI_S4P_EXIT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r0:real^2` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`k:real^2->bool`; `q:real^2`; `utq:real^2`] MOI_S4P_EXIT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t1:real^2` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`k:real^2->bool`; `q:real^2`; `urq:real^2`] MOI_S4P_EXIT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r1:real^2` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(a:real^2->bool) SUBSET k /\ (a':real^2->bool) SUBSET k /\
                segment[p:real^2,utp] SUBSET tau /\ segment[q:real^2,utq] SUBSET tau /\
                segment[p:real^2,urp] SUBSET rho /\ segment[q:real^2,urq] SUBSET rho /\
                segment[p:real^2,utp] SUBSET cball(p,rp) /\ segment[p:real^2,urp] SUBSET cball(p,rp) /\
                segment[q:real^2,utq] SUBSET cball(q,rq) /\ segment[q:real^2,urq] SUBSET cball(q,rq) /\
                cball(p:real^2,rp) INTER cball(q,rq) = {}`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[MOI_S4P_SEG_CBALL] THEN REPEAT CONJ_TAC THENL
     [MP_TAC(ISPEC `k:real^2->bool` INTERIOR_SUBSET) THEN
      UNDISCH_TAC `(t:real^2->bool) SUBSET interior k` THEN
      UNDISCH_TAC `(a:real^2->bool) SUBSET t` THEN SET_TAC[];
      MP_TAC(ISPEC `k:real^2->bool` INTERIOR_SUBSET) THEN
      UNDISCH_TAC `(t:real^2->bool) SUBSET interior k` THEN
      UNDISCH_TAC `(a':real^2->bool) SUBSET t` THEN SET_TAC[];
      UNDISCH_TAC `tau INTER cball(p:real^2,rp) = a INTER cball(p,rp) UNION segment[p,utp]` THEN
      SET_TAC[];
      UNDISCH_TAC `tau INTER cball(q:real^2,rq) = a INTER cball(q,rq) UNION segment[q,utq]` THEN
      SET_TAC[];
      UNDISCH_TAC `rho INTER cball(p:real^2,rp) = a' INTER cball(p,rp) UNION segment[p,urp]` THEN
      SET_TAC[];
      UNDISCH_TAC `rho INTER cball(q:real^2,rq) = a' INTER cball(q,rq) UNION segment[q,urq]` THEN
      SET_TAC[];
      MATCH_MP_TAC MOI_S4P_CBALL_DISJ THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `tau INTER k = a UNION segment[p:real^2,t0] UNION segment[q,t1] /\
                rho INTER k = a' UNION segment[p:real^2,r0] UNION segment[q,r1]`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC MOI_S4P_DESC THENL
     [MAP_EVERY EXISTS_TAC [`cball(p:real^2,rp)`; `cball(q:real^2,rq)`; `ball(p:real^2,rp)`;
                            `ball(q:real^2,rq)`; `segment[p:real^2,utp]`; `segment[q:real^2,utq]`];
      MAP_EVERY EXISTS_TAC [`cball(p:real^2,rp)`; `cball(q:real^2,rq)`; `ball(p:real^2,rp)`;
                            `ball(q:real^2,rq)`; `segment[p:real^2,urp]`; `segment[q:real^2,urq]`]] THEN
    ASM_REWRITE_TAC[BALL_SUBSET_CBALL];
    ALL_TAC] THEN
  SUBGOAL_THEN `frontier(k:real^2->bool) = k DIFF interior k` ASSUME_TAC THENL
   [ASM_SIMP_TAC[frontier; CLOSURE_CLOSED]; ALL_TAC] THEN
  SUBGOAL_THEN `segment[p:real^2,t0] SUBSET segment[p,utp] /\ segment[p:real^2,r0] SUBSET segment[p,urp] /\
                segment[q:real^2,t1] SUBSET segment[q,utq] /\ segment[q:real^2,r1] SUBSET segment[q,urq]`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `segment[p:real^2,utp] INTER k = segment[p,t0]` THEN SET_TAC[];
      UNDISCH_TAC `segment[p:real^2,urp] INTER k = segment[p,r0]` THEN SET_TAC[];
      UNDISCH_TAC `segment[q:real^2,utq] INTER k = segment[q,t1]` THEN SET_TAC[];
      UNDISCH_TAC `segment[q:real^2,urq] INTER k = segment[q,r1]` THEN SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`ga:real^1->real^2`; `t0:real^2`; `t1:real^2`] MOI_S4P_ARC_WHISKERS) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [REWRITE_TAC[ISPECL [`t0:real^2`; `p:real^2`] (CONJUNCT1 SEGMENT_SYM)] THEN
    REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `segment[p:real^2,t0] SUBSET segment[p,utp]` THEN
      UNDISCH_TAC `segment[p:real^2,utp] INTER t = {p}` THEN
      UNDISCH_TAC `(a:real^2->bool) SUBSET t` THEN UNDISCH_TAC `(p:real^2) IN a` THEN
      MP_TAC(ISPECL [`p:real^2`; `t0:real^2`] ENDS_IN_SEGMENT) THEN SET_TAC[];
      UNDISCH_TAC `segment[q:real^2,t1] SUBSET segment[q,utq]` THEN
      UNDISCH_TAC `segment[q:real^2,utq] INTER t = {q}` THEN
      UNDISCH_TAC `(a:real^2->bool) SUBSET t` THEN UNDISCH_TAC `(q:real^2) IN a` THEN
      MP_TAC(ISPECL [`q:real^2`; `t1:real^2`] ENDS_IN_SEGMENT) THEN SET_TAC[];
      UNDISCH_TAC `segment[p:real^2,t0] SUBSET segment[p,utp]` THEN
      UNDISCH_TAC `segment[q:real^2,t1] SUBSET segment[q,utq]` THEN
      UNDISCH_TAC `segment[p:real^2,utp] SUBSET cball(p,rp)` THEN
      UNDISCH_TAC `segment[q:real^2,utq] SUBSET cball(q,rq)` THEN
      UNDISCH_TAC `cball(p:real^2,rp) INTER cball(q,rq) = {}` THEN SET_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `b = linepath(t0:real^2,p) ++ (ga ++ linepath(q,t1))` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`ga':real^1->real^2`; `r0:real^2`; `r1:real^2`] MOI_S4P_ARC_WHISKERS) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [REWRITE_TAC[ISPECL [`r0:real^2`; `p:real^2`] (CONJUNCT1 SEGMENT_SYM)] THEN
    REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `segment[p:real^2,r0] SUBSET segment[p,urp]` THEN
      UNDISCH_TAC `segment[p:real^2,urp] INTER t = {p}` THEN
      UNDISCH_TAC `(a':real^2->bool) SUBSET t` THEN UNDISCH_TAC `(p:real^2) IN a'` THEN
      MP_TAC(ISPECL [`p:real^2`; `r0:real^2`] ENDS_IN_SEGMENT) THEN SET_TAC[];
      UNDISCH_TAC `segment[q:real^2,r1] SUBSET segment[q,urq]` THEN
      UNDISCH_TAC `segment[q:real^2,urq] INTER t = {q}` THEN
      UNDISCH_TAC `(a':real^2->bool) SUBSET t` THEN UNDISCH_TAC `(q:real^2) IN a'` THEN
      MP_TAC(ISPECL [`q:real^2`; `r1:real^2`] ENDS_IN_SEGMENT) THEN SET_TAC[];
      UNDISCH_TAC `segment[p:real^2,r0] SUBSET segment[p,urp]` THEN
      UNDISCH_TAC `segment[q:real^2,r1] SUBSET segment[q,urq]` THEN
      UNDISCH_TAC `segment[p:real^2,urp] SUBSET cball(p,rp)` THEN
      UNDISCH_TAC `segment[q:real^2,urq] SUBSET cball(q,rq)` THEN
      UNDISCH_TAC `cball(p:real^2,rp) INTER cball(q,rq) = {}` THEN SET_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `c = linepath(r0:real^2,p) ++ (ga' ++ linepath(q,r1))` THEN STRIP_TAC THEN
  SUBGOAL_THEN `path_image b = tau INTER (k:real^2->bool) /\ path_image c = rho INTER k`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ISPECL [`t0:real^2`; `p:real^2`] (CONJUNCT1 SEGMENT_SYM);
                ISPECL [`r0:real^2`; `p:real^2`] (CONJUNCT1 SEGMENT_SYM)] THEN
    SET_TAC[];
    ALL_TAC] THEN
  UNDISCH_THEN `path_image b = segment[t0,p] UNION a UNION segment[q:real^2,t1]` (K ALL_TAC) THEN
  UNDISCH_THEN `path_image c = segment[r0,p] UNION a' UNION segment[q:real^2,r1]` (K ALL_TAC) THEN
  SUBGOAL_THEN `(a:real^2->bool) SUBSET interior k /\ (a':real^2->bool) SUBSET interior k`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(t:real^2->bool) SUBSET interior k` THEN
    UNDISCH_TAC `(a:real^2->bool) SUBSET t` THEN UNDISCH_TAC `(a':real^2->bool) SUBSET t` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `path_image b INTER relative_frontier k = {pathstart b,pathfinish (b:real^1->real^2)} /\
                path_image c INTER relative_frontier k = {pathstart c,pathfinish (c:real^1->real^2)}`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ISPECL [`t0:real^2`; `p:real^2`] (CONJUNCT1 SEGMENT_SYM);
                ISPECL [`r0:real^2`; `p:real^2`] (CONJUNCT1 SEGMENT_SYM)] THEN
    MP_TAC(ISPECL [`p:real^2`; `t0:real^2`] ENDS_IN_SEGMENT) THEN
    MP_TAC(ISPECL [`q:real^2`; `t1:real^2`] ENDS_IN_SEGMENT) THEN
    MP_TAC(ISPECL [`p:real^2`; `r0:real^2`] ENDS_IN_SEGMENT) THEN
    MP_TAC(ISPECL [`q:real^2`; `r1:real^2`] ENDS_IN_SEGMENT) THEN
    UNDISCH_TAC `segment[p:real^2,t0] DELETE t0 SUBSET interior k` THEN
    UNDISCH_TAC `segment[q:real^2,t1] DELETE t1 SUBSET interior k` THEN
    UNDISCH_TAC `segment[p:real^2,r0] DELETE r0 SUBSET interior k` THEN
    UNDISCH_TAC `segment[q:real^2,r1] DELETE r1 SUBSET interior k` THEN
    UNDISCH_TAC `(t0:real^2) IN frontier k` THEN UNDISCH_TAC `(t1:real^2) IN frontier k` THEN
    UNDISCH_TAC `(r0:real^2) IN frontier k` THEN UNDISCH_TAC `(r1:real^2) IN frontier k` THEN
    UNDISCH_TAC `(a:real^2->bool) SUBSET interior k` THEN
    UNDISCH_TAC `(a':real^2->bool) SUBSET interior k` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `tau INTER rho INTER k = {p:real^2,q}` ASSUME_TAC THENL
   [SUBGOAL_THEN `segment[p:real^2,t0] SUBSET cball(p,rp) /\ segment[p:real^2,r0] SUBSET cball(p,rp) /\
                  segment[q:real^2,t1] SUBSET cball(q,rq) /\ segment[q:real^2,r1] SUBSET cball(q,rq)`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THEN MATCH_MP_TAC SUBSET_TRANS THENL
       [EXISTS_TAC `segment[p:real^2,utp]`; EXISTS_TAC `segment[p:real^2,urp]`;
        EXISTS_TAC `segment[q:real^2,utq]`; EXISTS_TAC `segment[q:real^2,urq]`] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(p:real^2) IN k /\ q IN k /\ p IN cball(p,rp) /\ q IN cball(q,rq)`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[CENTRE_IN_CBALL] THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
      CONJ_TAC THEN MATCH_MP_TAC(REWRITE_RULE[SUBSET] INTERIOR_SUBSET) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `tau INTER rho INTER cball(p:real^2,rp) = {p}` THEN
    UNDISCH_TAC `tau INTER rho INTER cball(q:real^2,rq) = {q}` THEN
    UNDISCH_TAC `tau INTER k = a UNION segment[p:real^2,t0] UNION segment[q,t1]` THEN
    UNDISCH_TAC `rho INTER k = a' UNION segment[p:real^2,r0] UNION segment[q,r1]` THEN
    UNDISCH_TAC `segment[p:real^2,t0] SUBSET cball(p,rp)` THEN
    UNDISCH_TAC `segment[p:real^2,r0] SUBSET cball(p,rp)` THEN
    UNDISCH_TAC `segment[q:real^2,t1] SUBSET cball(q,rq)` THEN
    UNDISCH_TAC `segment[q:real^2,r1] SUBSET cball(q,rq)` THEN
    UNDISCH_TAC `(a:real^2->bool) INTER a' = {p,q}` THEN
    UNDISCH_TAC `(p:real^2) IN k` THEN UNDISCH_TAC `(q:real^2) IN k` THEN
    UNDISCH_TAC `(p:real^2) IN cball(p,rp)` THEN UNDISCH_TAC `(q:real^2) IN cball(q,rq)` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((t0:real^2) IN rho) /\ ~((t1:real^2) IN rho)` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`p:real^2`; `t0:real^2`] ENDS_IN_SEGMENT) THEN
    MP_TAC(ISPECL [`q:real^2`; `t1:real^2`] ENDS_IN_SEGMENT) THEN
    UNDISCH_TAC `tau INTER rho INTER k = {p:real^2,q}` THEN
    UNDISCH_TAC `tau INTER k = a UNION segment[p:real^2,t0] UNION segment[q,t1]` THEN
    UNDISCH_TAC `(t0:real^2) IN frontier k` THEN UNDISCH_TAC `(t1:real^2) IN frontier k` THEN
    UNDISCH_TAC `frontier(k:real^2->bool) = k DIFF interior k` THEN
    UNDISCH_TAC `(p:real^2) IN interior k` THEN UNDISCH_TAC `(q:real^2) IN interior k` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `connected(t DIFF a':real^2->bool) /\ t DIFF a' SUBSET k /\
                (t DIFF a') INTER rho = {}` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`t:real^2->bool`; `a':real^2->bool`] MOI_S4P_TRI_MINUS_ARC) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(a:real^2->bool) UNION a' = relative_frontier t` THEN
      SET_TAC[];
      ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MP_TAC(ISPEC `k:real^2->bool` INTERIOR_SUBSET) THEN
      UNDISCH_TAC `(t:real^2->bool) SUBSET interior k` THEN SET_TAC[];
      UNDISCH_TAC `(rho:real^2->bool) INTER t = a'` THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `connected(segment[p:real^2,t0] DELETE p) /\ segment[p,t0] DELETE p SUBSET k /\
    (segment[p,t0] DELETE p) INTER rho = {} /\ t0 IN closure(segment[p,t0] DELETE p) /\
    connected(segment[q:real^2,t1] DELETE q) /\ segment[q,t1] DELETE q SUBSET k /\
    (segment[q,t1] DELETE q) INTER rho = {} /\ t1 IN closure(segment[q,t1] DELETE q)`
  STRIP_ASSUME_TAC THENL
   [SIMP_TAC[CONVEX_CONNECTED; CONVEX_SEMIOPEN_SEGMENT] THEN REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `segment[p:real^2,utp] INTER k = segment[p,t0]` THEN SET_TAC[];
      UNDISCH_TAC `segment[p:real^2,t0] SUBSET segment[p,utp]` THEN
      UNDISCH_TAC `segment[p:real^2,utp] SUBSET tau` THEN
      UNDISCH_TAC `segment[p:real^2,utp] SUBSET cball(p,rp)` THEN
      UNDISCH_TAC `tau INTER rho INTER cball(p:real^2,rp) = {p}` THEN SET_TAC[];
      MATCH_MP_TAC(SET_RULE `!s. (x:real^2) IN s /\ s SUBSET t ==> x IN t`) THEN
      EXISTS_TAC `segment[p:real^2,t0] DELETE p` THEN REWRITE_TAC[CLOSURE_SUBSET] THEN
      ASM_REWRITE_TAC[IN_DELETE; ENDS_IN_SEGMENT];
      UNDISCH_TAC `segment[q:real^2,utq] INTER k = segment[q,t1]` THEN SET_TAC[];
      UNDISCH_TAC `segment[q:real^2,t1] SUBSET segment[q,utq]` THEN
      UNDISCH_TAC `segment[q:real^2,utq] SUBSET tau` THEN
      UNDISCH_TAC `segment[q:real^2,utq] SUBSET cball(q,rq)` THEN
      UNDISCH_TAC `tau INTER rho INTER cball(q:real^2,rq) = {q}` THEN SET_TAC[];
      MATCH_MP_TAC(SET_RULE `!s. (x:real^2) IN s /\ s SUBSET t ==> x IN t`) THEN
      EXISTS_TAC `segment[q:real^2,t1] DELETE q` THEN REWRITE_TAC[CLOSURE_SUBSET] THEN
      ASM_REWRITE_TAC[IN_DELETE; ENDS_IN_SEGMENT]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(?n g1 g2. open n /\ p IN n /\ n SUBSET k /\ n DIFF rho = g1 UNION g2 /\
               connected g1 /\ connected g2 /\ ~(g1 INTER (t DIFF a') = {}) /\
               ~(g2 INTER (segment[p:real^2,t0] DELETE p) = {})) /\
    (?n g1 g2. open n /\ q IN n /\ n SUBSET k /\ n DIFF rho = g1 UNION g2 /\
               connected g1 /\ connected g2 /\ ~(g1 INTER (t DIFF a') = {}) /\
               ~(g2 INTER (segment[q:real^2,t1] DELETE q) = {}))`
  (CONJUNCTS_THEN ASSUME_TAC) THENL
   [CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `interior k:real^2->bool` o check (fun th ->
        is_forall(concl th) && can (find_term ((=) `utp:real^2`)) (concl th)));
      FIRST_X_ASSUM(MP_TAC o SPEC `interior k:real^2->bool` o check (fun th ->
        is_forall(concl th) && can (find_term ((=) `utq:real^2`)) (concl th)))] THEN
    ASM_REWRITE_TAC[OPEN_INTERIOR] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `n:real^2->bool` THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `g1:real^2->bool` THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `g2:real^2->bool` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `k:real^2->bool` INTERIOR_SUBSET) THENL
     [UNDISCH_TAC `~((g2:real^2->bool) INTER (segment[p,utp] DELETE p) = {})` THEN
      UNDISCH_TAC `segment[p:real^2,utp] INTER k = segment[p,t0]`;
      UNDISCH_TAC `~((g2:real^2->bool) INTER (segment[q,utq] DELETE q) = {})` THEN
      UNDISCH_TAC `segment[q:real^2,utq] INTER k = segment[q,t1]`] THEN
    UNDISCH_TAC `n SUBSET interior(k:real^2->bool)` THEN
    UNDISCH_TAC `(n:real^2->bool) DIFF rho = g1 UNION g2` THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:real^2->bool`; `b:real^1->real^2`; `c:real^1->real^2`; `tau:real^2->bool`;
                 `rho:real^2->bool`; `t DIFF a':real^2->bool`;
                 `segment[p:real^2,t0] DELETE p`; `segment[q:real^2,t1] DELETE q`;
                 `p:real^2`; `q:real^2`] MOI_S4P_PUSH_TRI) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(a':real^2->bool) SUBSET rho` THEN UNDISCH_TAC `(p:real^2) IN a'` THEN
    UNDISCH_TAC `(q:real^2) IN a'` THEN SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^2->real^2` (X_CHOOSE_THEN `w':real^2->real^2`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `IMAGE (w:real^2->real^2) tau INTER rho INTER k = {}` ASSUME_TAC THENL
   [SUBGOAL_THEN `IMAGE (w:real^2->real^2) tau INTER k = IMAGE w (tau INTER k)` MP_TAC THENL
     [MP_TAC(ISPEC `k:real^2->bool` INTERIOR_SUBSET) THEN
      UNDISCH_TAC `!x. ~(x IN interior k) ==> (w:real^2->real^2) x = x` THEN
      UNDISCH_TAC `IMAGE (w:real^2->real^2) k = k` THEN SET_TAC[];
      UNDISCH_TAC `IMAGE (w:real^2->real^2) (tau INTER k) INTER rho = {}` THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `compact(k:real^2->bool) /\ k SUBSET oo` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`w:real^2->real^2`; `w':real^2->real^2`; `k:real^2->bool`] THEN
  REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC);;

(* ------------------------------------------------------------------------- *)
(* The 2D push MOI_S4P_PUSH2 (general bigon in the                           *)
(* plane, by the triangle chart AMB2_VERTEX and MOI_S4P_PUSH2_STD).          *)
(* ------------------------------------------------------------------------- *)

(* Transport facts for PL homeomorphisms of the plane. *)

let MOI_S4P_PLH2_FACTS = prove
 (`!(f:real^2->real^2) g.
     pl_homeomorphism ((:real^2),(:real^2)) (f,g)
     ==> (!x. g(f x) = x) /\ (!y. f(g y) = y) /\
         (!s. closure(IMAGE f s) = IMAGE f (closure s)) /\
         (!s. interior(IMAGE f s) = IMAGE f (interior s)) /\
         (!s. compact s ==> compact(IMAGE f s)) /\
         (!n d j. pl_cell_with_boundary n d j
                  ==> pl_cell_with_boundary n (IMAGE f d) (IMAGE f j))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SA2_PLH_UNIV) THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`f:real^2->real^2`; `g:real^2->real^2`; `(:real^2)`; `(:real^2)`;
                   `s:real^2->bool`] HOMEOMORPHISM_CLOSURE) THEN
    ASM_REWRITE_TAC[SUBSET_UNIV; INTER_UNIV];
    GEN_TAC THEN
    MP_TAC(ISPECL [`f:real^2->real^2`; `g:real^2->real^2`; `(:real^2)`; `(:real^2)`;
                   `s:real^2->bool`] HOMEOMORPHISM_INTERIOR_OF) THEN
    ASM_REWRITE_TAC[SUBSET_UNIV; SUBTOPOLOGY_UNIV; EUCLIDEAN_INTERIOR_OF] THEN
    MESON_TAC[];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
    ASM_MESON_TAC[homeomorphism; CONTINUOUS_ON_SUBSET; SUBSET_UNIV];
    REPEAT GEN_TAC THEN REWRITE_TAC[pl_cell_with_boundary] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real^2->bool`
      (X_CHOOSE_THEN `p:real^2->real^2` (X_CHOOSE_THEN `q:real^2->real^2`
        STRIP_ASSUME_TAC))) THEN
    MAP_EVERY EXISTS_TAC [`t:real^2->bool`; `(f:real^2->real^2) o (p:real^2->real^2)`;
                          `(q:real^2->real^2) o (g:real^2->real^2)`] THEN
    ASM_REWRITE_TAC[IMAGE_o] THEN
    MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `d:real^2->bool` THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `pl_polyhedron(d:real^2->bool)` ASSUME_TAC THENL
     [SUBGOAL_THEN `d = IMAGE (p:real^2->real^2) t` SUBST1_TAC THENL
       [ASM_MESON_TAC[pl_homeomorphism; homeomorphism]; ALL_TAC] THEN
      MATCH_MP_TAC PL_POLYHEDRON_PL_IMAGE THEN
      CONJ_TAC THENL [ASM_MESON_TAC[POLYTOPE_IMP_PL_POLYHEDRON; SIMPLEX_IMP_POLYTOPE];
                      ASM_MESON_TAC[pl_homeomorphism]];
      ALL_TAC] THEN
    UNDISCH_TAC `pl_homeomorphism ((:real^2),(:real^2)) (f:real^2->real^2,g)` THEN
    REWRITE_TAC[pl_homeomorphism] THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC HOMEOMORPHISM_OF_SUBSETS THEN
      MAP_EVERY EXISTS_TAC [`(:real^2)`; `(:real^2)`] THEN
      ASM_REWRITE_TAC[SUBSET_UNIV];
      MATCH_MP_TAC PL_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
      ASM_SIMP_TAC[SUBSET_UNIV; LOCALLY_POLYHEDRAL_PL_POLYHEDRON];
      MATCH_MP_TAC PL_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
      ASM_REWRITE_TAC[SUBSET_UNIV] THEN MATCH_MP_TAC LOCALLY_POLYHEDRAL_PL_POLYHEDRON THEN
      MATCH_MP_TAC PL_POLYHEDRON_PL_IMAGE THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC PL_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
      ASM_SIMP_TAC[SUBSET_UNIV; LOCALLY_POLYHEDRAL_PL_POLYHEDRON]]]);;

let MOI_S4P_BIJ_IMAGE = prove
 (`!(f:real^N->real^N) g.
     (!x. g(f x) = x) /\ (!y. f(g y) = y)
     ==> (!s. IMAGE g (IMAGE f s) = s) /\ (!s. IMAGE f (IMAGE g s) = s) /\
         (!A t u. IMAGE g (A INTER IMAGE f t INTER u) = IMAGE g A INTER t INTER IMAGE g u)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_INTER] THEN ASM_MESON_TAC[]);;

let MOI_S4P_SIMPLEX2_CLOSED_INSIDE = prove
 (`!t:real^2->bool. &2 simplex t ==> relative_frontier t UNION inside(relative_frontier t) = t`,
  GEN_TAC THEN REWRITE_TAC[MOI_PL2_SIMPLEX_2] THEN
  DISCH_THEN(X_CHOOSE_THEN `v0:real^2` (X_CHOOSE_THEN `v1:real^2` (X_CHOOSE_THEN `v2:real^2`
    STRIP_ASSUME_TAC))) THEN
  ASM_SIMP_TAC[RELATIVE_FRONTIER_OF_TRIANGLE; MOI_PL2_TRIANGLE_CLOSED_INSIDE]);;

(* The 2D push: a PL bigon d bounded by an arc a of tau and                  *)
(* an arc a' of rho, where tau and rho cross at the corners p and q, can   *)
(* be pushed off: a PL homeomorphism of the plane supported in a compact   *)
(* neighbourhood K of d inside oo removes the two crossings in K.          *)

let MOI_S4P_PUSH2 = prove
 (`!(d:real^2->bool) a a' tau rho p q oo.
     pl_cell_with_boundary 2 d (a UNION a') /\ ~(p = q) /\ a INTER a' = {p,q} /\
     pl_cell_with_boundary 1 a {p,q} /\ pl_cell_with_boundary 1 a' {p,q} /\
     tau INTER d = a /\ rho INTER d = a' /\
     closure(tau DIFF a) INTER d SUBSET {p,q} /\ closure(rho DIFF a') INTER d SUBSET {p,q} /\
     pl_curve_crossing_at (:real^2) tau rho p /\ pl_curve_crossing_at (:real^2) tau rho q /\
     open oo /\ d SUBSET oo
     ==> ?w w' K. pl_homeomorphism ((:real^2),(:real^2)) (w,w') /\
                  compact K /\ d SUBSET interior K /\ K SUBSET oo /\
                  (!x. ~(x IN interior K) ==> w x = x) /\ IMAGE w K = K /\
                  tau INTER rho INTER K = {p,q} /\
                  IMAGE w tau INTER rho INTER K = {}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`a:real^2->bool`; `p:real^2`; `q:real^2`] MOI_S4P_CELL1_ARC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `ga:real^1->real^2` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`a':real^2->bool`; `p:real^2`; `q:real^2`] MOI_S4P_CELL1_ARC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `ga':real^1->real^2` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `pl_sphere 1 (a UNION a':real^2->bool)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`ga:real^1->real^2`; `ga':real^1->real^2`] MOI_SFR_ARCS_SPHERE) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `d = (a UNION a') UNION inside(a UNION a':real^2->bool)` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP MOI_SFR_CELL_FACTS o check (fun th ->
      can (find_term ((=) `2`)) (concl th))) THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`a UNION a':real^2->bool`; `oo:real^2->bool`; `p:real^2`] AMB2_VERTEX) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [UNDISCH_TAC `(d:real^2->bool) SUBSET oo` THEN
      UNDISCH_TAC `d = (a UNION a') UNION inside(a UNION a':real^2->bool)` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN SIMP_TAC[];
      UNDISCH_TAC `(a:real^2->bool) INTER a' = {p,q}` THEN SET_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^2->bool` (X_CHOOSE_THEN `f:real^2->real^2`
    (X_CHOOSE_THEN `g:real^2->real^2` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `pl_homeomorphism ((:real^2),(:real^2)) (g:real^2->real^2,f)` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[PL_HOMEOMORPHISM_SYM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`f:real^2->real^2`; `g:real^2->real^2`] MOI_S4P_PLH2_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`g:real^2->real^2`; `f:real^2->real^2`] MOI_S4P_PLH2_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^2->real^2`; `g:real^2->real^2`; `oo:real^2->bool`; `d:real^2->bool`]
    MOI_SA2_FIX_OFF) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `IMAGE (f:real^2->real^2) d = t` ASSUME_TAC THENL
   [UNDISCH_TAC `d = (a UNION a') UNION inside(a UNION a':real^2->bool)` THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[IMAGE_UNION] THEN
    MP_TAC(ISPECL [`f:real^2->real^2`; `g:real^2->real^2`; `a UNION a':real^2->bool`]
      MOI_SCD_INSIDE_HOMEOMORPHISM) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[pl_homeomorphism]; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN
    UNDISCH_TAC `IMAGE (f:real^2->real^2) (a UNION a') = relative_frontier t` THEN
    REWRITE_TAC[IMAGE_UNION] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC MOI_S4P_SIMPLEX2_CLOSED_INSIDE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:real^2->bool`; `IMAGE (f:real^2->real^2) a`; `IMAGE (f:real^2->real^2) a'`;
                 `IMAGE (f:real^2->real^2) tau`; `IMAGE (f:real^2->real^2) rho`;
                 `(f:real^2->real^2) p`; `(f:real^2->real^2) q`; `oo:real^2->bool`]
    MOI_S4P_PUSH2_STD) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `IMAGE (f:real^2->real^2) (a UNION a') = relative_frontier t` THEN
      UNDISCH_TAC `(a:real^2->bool) INTER a' = {p,q}` THEN SET_TAC[];
      UNDISCH_TAC `IMAGE (f:real^2->real^2) (a UNION a') = relative_frontier t` THEN
      UNDISCH_TAC `(a:real^2->bool) INTER a' = {p,q}` THEN SET_TAC[];
      UNDISCH_TAC `~(p:real^2 = q)` THEN UNDISCH_TAC `!x:real^2. g((f:real^2->real^2) x) = x` THEN
      MESON_TAC[];
      UNDISCH_TAC `IMAGE (f:real^2->real^2) (a UNION a') = relative_frontier t` THEN
      REWRITE_TAC[IMAGE_UNION];
      UNDISCH_TAC `(a:real^2->bool) INTER a' = {p,q}` THEN
      UNDISCH_TAC `!x:real^2. g((f:real^2->real^2) x) = x` THEN SET_TAC[];
      SUBGOAL_THEN `{(f:real^2->real^2) p,f q} = IMAGE f {p,q}` SUBST1_TAC THENL
       [REWRITE_TAC[IMAGE_CLAUSES]; ALL_TAC] THEN
      FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      SUBGOAL_THEN `{(f:real^2->real^2) p,f q} = IMAGE f {p,q}` SUBST1_TAC THENL
       [REWRITE_TAC[IMAGE_CLAUSES]; ALL_TAC] THEN
      FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `IMAGE (f:real^2->real^2) d = t` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      UNDISCH_TAC `(tau:real^2->bool) INTER d = a` THEN
      UNDISCH_TAC `!x:real^2. g((f:real^2->real^2) x) = x` THEN SET_TAC[];
      UNDISCH_TAC `IMAGE (f:real^2->real^2) d = t` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      UNDISCH_TAC `(rho:real^2->bool) INTER d = a'` THEN
      UNDISCH_TAC `!x:real^2. g((f:real^2->real^2) x) = x` THEN SET_TAC[];
      SUBGOAL_THEN `IMAGE (f:real^2->real^2) tau DIFF IMAGE f a = IMAGE f (tau DIFF a)`
      SUBST1_TAC THENL
       [UNDISCH_TAC `!x:real^2. g((f:real^2->real^2) x) = x` THEN SET_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `IMAGE (f:real^2->real^2) d = t` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      UNDISCH_TAC `closure(tau DIFF a) INTER d SUBSET {p:real^2,q}` THEN
      UNDISCH_TAC `!x:real^2. g((f:real^2->real^2) x) = x` THEN SET_TAC[];
      SUBGOAL_THEN `IMAGE (f:real^2->real^2) rho DIFF IMAGE f a' = IMAGE f (rho DIFF a')`
      SUBST1_TAC THENL
       [UNDISCH_TAC `!x:real^2. g((f:real^2->real^2) x) = x` THEN SET_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `IMAGE (f:real^2->real^2) d = t` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      UNDISCH_TAC `closure(rho DIFF a') INTER d SUBSET {p:real^2,q}` THEN
      UNDISCH_TAC `!x:real^2. g((f:real^2->real^2) x) = x` THEN SET_TAC[];
      MATCH_MP_TAC MOI_S4P_CROSS2_TRANSPORT THEN EXISTS_TAC `g:real^2->real^2` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC MOI_S4P_CROSS2_TRANSPORT THEN EXISTS_TAC `g:real^2->real^2` THEN
      ASM_REWRITE_TAC[];
      UNDISCH_TAC `IMAGE (f:real^2->real^2) d = t` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `w0:real^2->real^2` (X_CHOOSE_THEN `w0':real^2->real^2`
    (X_CHOOSE_THEN `K0:real^2->bool` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `pl_homeomorphism ((:real^2),(:real^2))
                  ((g:real^2->real^2) o (w0:real^2->real^2) o (f:real^2->real^2),
                   ((g:real^2->real^2) o (w0':real^2->real^2)) o (f:real^2->real^2))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `(:real^2)` THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `(:real^2)` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `interior(IMAGE (g:real^2->real^2) K0) = IMAGE g (interior K0) /\
                compact(IMAGE (g:real^2->real^2) K0)` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^2. ~(x IN oo) ==> (g:real^2->real^2) x = x` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`f:real^2->real^2`; `g:real^2->real^2`] MOI_S4P_BIJ_IMAGE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`(g:real^2->real^2) o (w0:real^2->real^2) o (f:real^2->real^2)`;
    `((g:real^2->real^2) o (w0':real^2->real^2)) o (f:real^2->real^2)`;
    `IMAGE (g:real^2->real^2) K0`] THEN
  ASM_REWRITE_TAC[] THEN
  SUBST1_TAC(SYM(ASSUME `d = (a UNION a') UNION inside(a UNION a':real^2->bool)`)) THEN
  REWRITE_TAC[o_THM] THEN REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `(t:real^2->bool) SUBSET interior K0` THEN
    UNDISCH_TAC `IMAGE (f:real^2->real^2) d = t` THEN
    UNDISCH_TAC `!x:real^2. g((f:real^2->real^2) x) = x` THEN SET_TAC[];
    UNDISCH_TAC `(K0:real^2->bool) SUBSET oo` THEN
    UNDISCH_TAC `!x:real^2. ~(x IN oo) ==> (f:real^2->real^2) x = x` THEN
    UNDISCH_TAC `!y:real^2. (f:real^2->real^2)(g y) = y` THEN SET_TAC[];
    X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    SUBGOAL_THEN `~((f:real^2->real^2) x IN interior K0)` ASSUME_TAC THENL
     [UNDISCH_TAC `~((x:real^2) IN IMAGE (g:real^2->real^2) (interior K0))` THEN
      UNDISCH_TAC `!x:real^2. g((f:real^2->real^2) x) = x` THEN SET_TAC[];
      ASM_SIMP_TAC[]];
    REWRITE_TAC[IMAGE_o] THEN ASM_REWRITE_TAC[];
    SUBGOAL_THEN `tau INTER rho INTER IMAGE (g:real^2->real^2) K0 =
                  IMAGE g (IMAGE (f:real^2->real^2) tau INTER IMAGE f rho INTER K0)`
    SUBST1_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[ASSUME `IMAGE (f:real^2->real^2) tau INTER IMAGE f rho INTER K0 =
                        {f p,f (q:real^2)}`; IMAGE_CLAUSES] THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[IMAGE_o] THEN
    SUBGOAL_THEN `IMAGE (g:real^2->real^2) (IMAGE (w0:real^2->real^2) (IMAGE (f:real^2->real^2) tau))
                  INTER rho INTER IMAGE g K0 =
                  IMAGE g (IMAGE w0 (IMAGE f tau) INTER IMAGE f rho INTER K0)`
    SUBST1_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[ASSUME `IMAGE (w0:real^2->real^2) (IMAGE (f:real^2->real^2) tau) INTER
                        IMAGE f rho INTER K0 = {}`; IMAGE_CLAUSES]]);;

(* The 2D push in chart form: the triangle chart f and the triangle k in   *)
(* which the push w of MOI_S4P_PUSH2_STD lives (used by the suspension).    *)

let MOI_S4P_PUSH2C = prove
 (`!(d:real^2->bool) a a' tau rho p q oo.
     pl_cell_with_boundary 2 d (a UNION a') /\ ~(p = q) /\ a INTER a' = {p,q} /\
     pl_cell_with_boundary 1 a {p,q} /\ pl_cell_with_boundary 1 a' {p,q} /\
     tau INTER d = a /\ rho INTER d = a' /\
     closure(tau DIFF a) INTER d SUBSET {p,q} /\ closure(rho DIFF a') INTER d SUBSET {p,q} /\
     pl_curve_crossing_at (:real^2) tau rho p /\ pl_curve_crossing_at (:real^2) tau rho q /\
     open oo /\ d SUBSET oo
     ==> ?f g w w' k.
           pl_homeomorphism ((:real^2),(:real^2)) (f,g) /\
           (!x. ~(x IN oo) ==> f x = x) /\
           &2 simplex k /\ IMAGE f d SUBSET interior k /\ IMAGE g k SUBSET oo /\
           pl_homeomorphism ((:real^2),(:real^2)) (w,w') /\
           (!x. ~(x IN interior k) ==> w x = x) /\ IMAGE w k = k /\
           IMAGE f tau INTER IMAGE f rho INTER k = {f p,f q} /\
           IMAGE w (IMAGE f tau) INTER IMAGE f rho INTER k = {}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`a:real^2->bool`; `p:real^2`; `q:real^2`] MOI_S4P_CELL1_ARC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `ga:real^1->real^2` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`a':real^2->bool`; `p:real^2`; `q:real^2`] MOI_S4P_CELL1_ARC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `ga':real^1->real^2` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `pl_sphere 1 (a UNION a':real^2->bool)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`ga:real^1->real^2`; `ga':real^1->real^2`] MOI_SFR_ARCS_SPHERE) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `d = (a UNION a') UNION inside(a UNION a':real^2->bool)` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP MOI_SFR_CELL_FACTS o check (fun th ->
      can (find_term ((=) `2`)) (concl th))) THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`a UNION a':real^2->bool`; `oo:real^2->bool`; `p:real^2`] AMB2_VERTEX) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [UNDISCH_TAC `(d:real^2->bool) SUBSET oo` THEN
      UNDISCH_TAC `d = (a UNION a') UNION inside(a UNION a':real^2->bool)` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN SIMP_TAC[];
      UNDISCH_TAC `(a:real^2->bool) INTER a' = {p,q}` THEN SET_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^2->bool` (X_CHOOSE_THEN `f:real^2->real^2`
    (X_CHOOSE_THEN `g:real^2->real^2` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `pl_homeomorphism ((:real^2),(:real^2)) (g:real^2->real^2,f)` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[PL_HOMEOMORPHISM_SYM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`f:real^2->real^2`; `g:real^2->real^2`] MOI_S4P_PLH2_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`g:real^2->real^2`; `f:real^2->real^2`] MOI_S4P_PLH2_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^2->real^2`; `g:real^2->real^2`; `oo:real^2->bool`; `d:real^2->bool`]
    MOI_SA2_FIX_OFF) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `IMAGE (f:real^2->real^2) d = t` ASSUME_TAC THENL
   [UNDISCH_TAC `d = (a UNION a') UNION inside(a UNION a':real^2->bool)` THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[IMAGE_UNION] THEN
    MP_TAC(ISPECL [`f:real^2->real^2`; `g:real^2->real^2`; `a UNION a':real^2->bool`]
      MOI_SCD_INSIDE_HOMEOMORPHISM) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[pl_homeomorphism]; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN
    UNDISCH_TAC `IMAGE (f:real^2->real^2) (a UNION a') = relative_frontier t` THEN
    REWRITE_TAC[IMAGE_UNION] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC MOI_S4P_SIMPLEX2_CLOSED_INSIDE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:real^2->bool`; `IMAGE (f:real^2->real^2) a`; `IMAGE (f:real^2->real^2) a'`;
                 `IMAGE (f:real^2->real^2) tau`; `IMAGE (f:real^2->real^2) rho`;
                 `(f:real^2->real^2) p`; `(f:real^2->real^2) q`; `oo:real^2->bool`]
    MOI_S4P_PUSH2_STD) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `IMAGE (f:real^2->real^2) (a UNION a') = relative_frontier t` THEN
      UNDISCH_TAC `(a:real^2->bool) INTER a' = {p,q}` THEN SET_TAC[];
      UNDISCH_TAC `IMAGE (f:real^2->real^2) (a UNION a') = relative_frontier t` THEN
      UNDISCH_TAC `(a:real^2->bool) INTER a' = {p,q}` THEN SET_TAC[];
      UNDISCH_TAC `~(p:real^2 = q)` THEN UNDISCH_TAC `!x:real^2. g((f:real^2->real^2) x) = x` THEN
      MESON_TAC[];
      UNDISCH_TAC `IMAGE (f:real^2->real^2) (a UNION a') = relative_frontier t` THEN
      REWRITE_TAC[IMAGE_UNION];
      UNDISCH_TAC `(a:real^2->bool) INTER a' = {p,q}` THEN
      UNDISCH_TAC `!x:real^2. g((f:real^2->real^2) x) = x` THEN SET_TAC[];
      SUBGOAL_THEN `{(f:real^2->real^2) p,f q} = IMAGE f {p,q}` SUBST1_TAC THENL
       [REWRITE_TAC[IMAGE_CLAUSES]; ALL_TAC] THEN
      FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      SUBGOAL_THEN `{(f:real^2->real^2) p,f q} = IMAGE f {p,q}` SUBST1_TAC THENL
       [REWRITE_TAC[IMAGE_CLAUSES]; ALL_TAC] THEN
      FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `IMAGE (f:real^2->real^2) d = t` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      UNDISCH_TAC `(tau:real^2->bool) INTER d = a` THEN
      UNDISCH_TAC `!x:real^2. g((f:real^2->real^2) x) = x` THEN SET_TAC[];
      UNDISCH_TAC `IMAGE (f:real^2->real^2) d = t` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      UNDISCH_TAC `(rho:real^2->bool) INTER d = a'` THEN
      UNDISCH_TAC `!x:real^2. g((f:real^2->real^2) x) = x` THEN SET_TAC[];
      SUBGOAL_THEN `IMAGE (f:real^2->real^2) tau DIFF IMAGE f a = IMAGE f (tau DIFF a)`
      SUBST1_TAC THENL
       [UNDISCH_TAC `!x:real^2. g((f:real^2->real^2) x) = x` THEN SET_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `IMAGE (f:real^2->real^2) d = t` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      UNDISCH_TAC `closure(tau DIFF a) INTER d SUBSET {p:real^2,q}` THEN
      UNDISCH_TAC `!x:real^2. g((f:real^2->real^2) x) = x` THEN SET_TAC[];
      SUBGOAL_THEN `IMAGE (f:real^2->real^2) rho DIFF IMAGE f a' = IMAGE f (rho DIFF a')`
      SUBST1_TAC THENL
       [UNDISCH_TAC `!x:real^2. g((f:real^2->real^2) x) = x` THEN SET_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `IMAGE (f:real^2->real^2) d = t` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      UNDISCH_TAC `closure(rho DIFF a') INTER d SUBSET {p:real^2,q}` THEN
      UNDISCH_TAC `!x:real^2. g((f:real^2->real^2) x) = x` THEN SET_TAC[];
      MATCH_MP_TAC MOI_S4P_CROSS2_TRANSPORT THEN EXISTS_TAC `g:real^2->real^2` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC MOI_S4P_CROSS2_TRANSPORT THEN EXISTS_TAC `g:real^2->real^2` THEN
      ASM_REWRITE_TAC[];
      UNDISCH_TAC `IMAGE (f:real^2->real^2) d = t` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `w0:real^2->real^2` (X_CHOOSE_THEN `w0':real^2->real^2`
    (X_CHOOSE_THEN `K0:real^2->bool` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `IMAGE (f:real^2->real^2) d SUBSET interior K0 /\ IMAGE (g:real^2->real^2) K0 SUBSET oo`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `IMAGE (f:real^2->real^2) d = t` THEN DISCH_THEN SUBST1_TAC THEN
      ASM_REWRITE_TAC[];
      UNDISCH_TAC `(K0:real^2->bool) SUBSET oo` THEN
      UNDISCH_TAC `!x:real^2. ~(x IN oo) ==> (f:real^2->real^2) x = x` THEN
      UNDISCH_TAC `!y:real^2. (f:real^2->real^2)(g y) = y` THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBST1_TAC(SYM(ASSUME `d = (a UNION a') UNION inside(a UNION a':real^2->bool)`)) THEN
  MAP_EVERY EXISTS_TAC [`f:real^2->real^2`; `g:real^2->real^2`; `w0:real^2->real^2`;
                        `w0':real^2->real^2`; `K0:real^2->bool`] THEN
  REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC);;

(* ------------------------------------------------------------------------- *)
(* The suspension of a 2D push, from the                                     *)
(* conewise extension MOI_SCX_DCONE of pc_moi_sch3_cvx: a PL push w of the   *)
(* plane supported in a polytope k gives a PL homeomorphism of real^3 that   *)
(* preserves the third coordinate, restricts to w on the plane x3 = 0 and   *)
(* is supported in a compact bipyramid B over k of height h.                *)
(* ------------------------------------------------------------------------- *)

let MOI_S4P_SUSPEND = prove
 (`!(k:real^2->bool) w w' h.
     polytope k /\ ~(interior k = {}) /\
     pl_homeomorphism ((:real^2),(:real^2)) (w,w') /\
     (!y. ~(y IN interior k) ==> w y = y) /\ &0 < h
     ==> ?sg sg' B.
           pl_homeomorphism ((:real^3),(:real^3)) (sg,sg') /\
           compact B /\ IMAGE sg B = B /\
           (!x. ~(x IN B) ==> sg x = x) /\
           (!x. x IN B ==> moi_scx_pr x IN k /\ abs(x$3) <= h) /\
           (!x. (sg x)$3 = x$3) /\
           (!y. sg(moi_scx_e y) = moi_scx_e(w y)) /\
           IMAGE moi_scx_e k SUBSET B`,
  REPEAT STRIP_TAC THEN
  UNDISCH_TAC `~(interior (k:real^2->bool) = {})` THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN DISCH_THEN(X_CHOOSE_TAC `b0:real^2`) THEN
  MP_TAC(ISPECL [`k:real^2->bool`; `b0:real^2`; `w:real^2->real^2`; `w':real^2->real^2`;
                 `h:real`] MOI_SCX_DCONE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `sg:real^3->real^3` (X_CHOOSE_THEN `sg':real^3->real^3`
    STRIP_ASSUME_TAC)) THEN
  ABBREV_TAC `B = convex hull ((moi_scx_e b0 + h % basis 3) INSERT
                               (moi_scx_e b0 + --h % basis 3) INSERT
                               IMAGE moi_scx_e (k:real^2->bool))` THEN
  MAP_EVERY EXISTS_TAC [`sg:real^3->real^3`; `sg':real^3->real^3`; `B:real^3->bool`] THEN
  SUBGOAL_THEN `(b0:real^2) IN k /\ convex (k:real^2->bool)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[INTERIOR_SUBSET; SUBSET; POLYTOPE_IMP_CONVEX]; ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^3. x IN B ==> moi_scx_pr x IN k /\ abs(x$3) <= h`
  ASSUME_TAC THENL
   [EXPAND_TAC "B" THEN
    MP_TAC(ISPECL [`IMAGE moi_scx_e (k:real^2->bool)`; `moi_scx_e b0`;
                   `h % basis 3:real^3`] MOI_SCX_BIPYR) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC CONVEX_LINEAR_IMAGE THEN ASM_REWRITE_TAC[MOI_SCX_EP];
        MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    REWRITE_TAC[VECTOR_ARITH `!m b:real^3 h. m - h % b = m + --h % b`] THEN
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[IN_UNION; MOI_SCX_CONE_PT; IN_IMAGE] THEN X_GEN_TAC `x:real^3` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[MOI_SCX_CONE_COORDS] THEN
    (CONJ_TAC THENL
      [REWRITE_TAC[VECTOR_ARITH `b0 + r % (y - b0):real^2 = (&1 - r) % b0 + r % y`] THEN
       UNDISCH_TAC `convex(k:real^2->bool)` THEN REWRITE_TAC[CONVEX_ALT] THEN
       DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
       REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_NEG] THEN
       ASM_SIMP_TAC[REAL_ARITH `&0 < h ==> abs h = h`;
                    REAL_ARITH `r <= &1 ==> abs(&1 - r) = &1 - r`] THEN
       MATCH_MP_TAC(REAL_ARITH `&0 <= r * h ==> (&1 - r) * h <= h`) THEN
       MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC]);
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE moi_scx_e (k:real^2->bool) SUBSET B` ASSUME_TAC THENL
   [EXPAND_TAC "B" THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `(moi_scx_e b0 + h % basis 3) INSERT (moi_scx_e b0 + --h % basis 3) INSERT
                IMAGE moi_scx_e (k:real^2->bool)` THEN
    REWRITE_TAC[HULL_SUBSET] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `compact(B:real^3->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "B" THEN MATCH_MP_TAC POLYTOPE_IMP_COMPACT THEN
    MATCH_MP_TAC MOI_SCX_CONE_POLYTOPE THEN
    MATCH_MP_TAC POLYTOPE_LINEAR_IMAGE THEN ASM_REWRITE_TAC[MOI_SCX_EP];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SCD_PL_HOMEO_UNIV o
    check (fun th -> can (find_term ((=) `sg:real^3->real^3`)) (concl th) &&
                     can (find_term ((=) `pl_homeomorphism:(real^3->bool)#(real^3->bool)->(real^3->real^3)#(real^3->real^3)->bool`)) (concl th))) THEN
  SUBGOAL_THEN `IMAGE (sg:real^3->real^3) B SUBSET B /\ IMAGE (sg':real^3->real^3) B SUBSET B`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`sg:real^3->real^3`; `sg':real^3->real^3`; `B:real^3->bool`;
                   `B:real^3->bool`] MOI_SCD_FIX_OFF) THEN
    ASM_REWRITE_TAC[SUBSET_REFL] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`sg':real^3->real^3`; `sg:real^3->real^3`; `B:real^3->bool`;
                   `B:real^3->bool`] MOI_SCD_FIX_OFF) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[PL_HOMEOMORPHISM_SYM]; SIMP_TAC[SUBSET_REFL]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; IN_IMAGE] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    EXISTS_TAC `(sg':real^3->real^3) y` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `IMAGE (sg':real^3->real^3) B SUBSET B` THEN REWRITE_TAC[SUBSET; IN_IMAGE] THEN
    DISCH_THEN MATCH_MP_TAC THEN EXISTS_TAC `y:real^3` THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `y:real^2` THEN ASM_CASES_TAC `(y:real^2) IN k` THEN ASM_SIMP_TAC[] THEN
    SUBGOAL_THEN `~(moi_scx_e y IN B) /\ ~((y:real^2) IN interior k)` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [DISCH_TAC THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `moi_scx_e y` o check (fun th ->
          can (find_term ((=) `moi_scx_pr`)) (concl th) && is_forall(concl th))) THEN
        ASM_REWRITE_TAC[MOI_SCX_EP];
        ASM_MESON_TAC[INTERIOR_SUBSET; SUBSET]];
      ASM_SIMP_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* Transport of the bigon data from a surface chart in real^3 to            *)
(* the plane: PL arcs and cells, closures and curve crossings under a PL    *)
(* homeomorphism of an open piece of the surface onto an open set of        *)
(* real^2.                                                                   *)
(* ------------------------------------------------------------------------- *)

(* A PL arc is a PL 1-cell with its two ends (any dimension). *)

let MOI_S4P_ARC_CELL = prove
 (`!g:real^1->real^N.
     arc g /\ pl_map_on (interval[vec 0,vec 1]) g
     ==> pl_cell_with_boundary 1 (path_image g) {pathstart g,pathfinish g}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `g:real^1->real^N` MOI_PL2_ARC_PL_HOMEOMORPHISM_ENDS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `h:real^N->real^1` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `~(vec 0:real^N = basis 1)` ASSUME_TAC THENL
   [CONV_TAC(RAND_CONV SYM_CONV) THEN MATCH_MP_TAC BASIS_NONZERO THEN
    REWRITE_TAC[LE_REFL; DIMINDEX_GE_1];
    ALL_TAC] THEN
  MP_TAC(ISPEC `linepath(vec 0:real^N,basis 1)` MOI_PL2_ARC_PL_HOMEOMORPHISM_ENDS) THEN
  ASM_SIMP_TAC[ARC_LINEPATH; MOI_PL2_PL_LINEPATH; PATH_IMAGE_LINEPATH;
               PATHSTART_LINEPATH; PATHFINISH_LINEPATH;
               MOI_PL2_LOCALLY_POLYHEDRAL_INTERVAL] THEN
  DISCH_THEN(X_CHOOSE_THEN `h0:real^N->real^1` STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[pl_cell_with_boundary] THEN
  MAP_EVERY EXISTS_TAC [`segment[vec 0:real^N,basis 1]`;
                        `(g:real^1->real^N) o (h0:real^N->real^1)`;
                        `linepath(vec 0:real^N,basis 1) o (h:real^N->real^1)`] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[MOI_PL2_SIMPLEX_1] THEN
    MAP_EVERY EXISTS_TAC [`vec 0:real^N`; `basis 1:real^N`] THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
    EXISTS_TAC `interval[vec 0:real^1,vec 1]` THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[PL_HOMEOMORPHISM_SYM] THEN ASM_REWRITE_TAC[];
    SUBGOAL_THEN `relative_frontier(segment[vec 0:real^N,basis 1]) = {vec 0,basis 1}`
    SUBST1_TAC THENL
     [REWRITE_TAC[relative_frontier; RELATIVE_INTERIOR_SEGMENT; CLOSURE_SEGMENT] THEN
      ASM_REWRITE_TAC[SEGMENT_CLOSED_OPEN] THEN
      MP_TAC(ISPECL [`vec 0:real^N`; `basis 1:real^N`] ENDS_NOT_IN_SEGMENT) THEN SET_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[IMAGE_CLAUSES; o_THM; pathstart; pathfinish]]);;

(* PL 1-cells and 2-cells under PL homeomorphisms between any dimensions. *)

let MOI_S4P_CELL1_TRANS = prove
 (`!(f:real^M->real^N) f' s t a p q.
     pl_homeomorphism (s,t) (f,f') /\ pl_cell_with_boundary 1 a {p,q} /\ ~(p = q) /\
     a SUBSET s
     ==> pl_cell_with_boundary 1 (IMAGE f a) {f p,f q}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`a:real^M->bool`; `p:real^M`; `q:real^M`] MOI_S4P_CELL1_ARC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `g:real^1->real^M` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [pl_homeomorphism]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  MP_TAC(ISPEC `(f:real^M->real^N) o (g:real^1->real^M)` MOI_S4P_ARC_CELL) THEN
  REWRITE_TAC[PATH_IMAGE_COMPOSE; PATHSTART_COMPOSE; PATHFINISH_COMPOSE] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC ARC_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
      ASM_MESON_TAC[SUBSET]];
    MATCH_MP_TAC PL_MAP_ON_COMPOSE THEN EXISTS_TAC `s:real^M->bool` THEN
    ASM_REWRITE_TAC[GSYM path_image]]);;

let MOI_S4P_CELL2_TRANS = prove
 (`!(f:real^M->real^N) f' s t d j.
     2 <= dimindex(:N) /\ pl_homeomorphism (s,t) (f,f') /\ pl_cell_with_boundary 2 d j /\
     d SUBSET s
     ==> pl_cell_with_boundary 2 (IMAGE f d) (IMAGE f j)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_SS2_CELL_OF_FSA THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MOI_SS2_FSA_IMAGE THEN
  MAP_EVERY EXISTS_TAC [`s:real^M->bool`; `t:real^N->bool`; `f':real^N->real^M`] THEN
  ASM_SIMP_TAC[MOI_SS2_FSA_OF_CELL]);;

(* Closures under a homeomorphism of subsets (no openness needed). *)

let MOI_S4P_CLOSURE_TRANS = prove
 (`!(f:real^M->real^N) f' s t x d.
     homeomorphism (s,t) (f,f') /\ x SUBSET s /\ d SUBSET s
     ==> closure(IMAGE f x) INTER IMAGE f d SUBSET IMAGE f (closure x INTER d)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[homeomorphism] THEN STRIP_TAC THEN
  REWRITE_TAC[SUBSET; IN_INTER; IN_IMAGE] THEN X_GEN_TAC `y:real^N` THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (X_CHOOSE_THEN `z:real^M` STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN EXISTS_TAC `z:real^M` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(z:real^M) IN s` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `(f:real^M->real^N) z IN closure (IMAGE f x)` THEN
  REWRITE_TAC[CLOSURE_SEQUENTIAL; IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `yy:num->real^N` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `(f':real^N->real^M) o (yy:num->real^N)` THEN CONJ_TAC THENL
   [X_GEN_TAC `n:num` THEN REWRITE_TAC[o_THM] THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `w:real^M` STRIP_ASSUME_TAC o SPEC `n:num`) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(w:real^M) IN s` (fun th -> ASM_SIMP_TAC[th]) THEN ASM SET_TAC[];
    SUBGOAL_THEN `z:real^M = f'((f:real^M->real^N) z)` SUBST1_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `(f':real^N->real^M) continuous_on t` THEN
    REWRITE_TAC[CONTINUOUS_ON_SEQUENTIALLY] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    X_GEN_TAC `n:num` THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `w:real^M` STRIP_ASSUME_TAC o SPEC `n:num`) THEN
    ASM SET_TAC[]]);;
(* Curve crossings under a PL chart of an open piece S INTER V of S. *)

let MOI_S4P_CHART_CAP = prove
 (`!(s:real^M->real^2) s' (f:real^M->real^2) g S V u w.
     (!y. y IN S INTER V ==> s'(s y) = y) /\ (!y. y IN u ==> g(f y) = y) /\
     u SUBSET S
     ==> IMAGE (f o s') (IMAGE s (w INTER S INTER V) INTER IMAGE s (u INTER V)) =
         IMAGE f (w INTER u) INTER IMAGE f (u INTER V)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^M->real^2`; `s':real^2->real^M`; `S INTER V:real^M->bool`;
                 `w INTER S INTER V:real^M->bool`; `u INTER V:real^M->bool`]
                MOI_SS2_INJ_IMAGE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN
  MP_TAC(ISPECL [`f:real^M->real^2`; `g:real^2->real^M`; `u:real^M->bool`;
                 `w INTER u:real^M->bool`; `u INTER V:real^M->bool`] MOI_SS2_INJ_IMAGE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN
  REWRITE_TAC[GSYM IMAGE_o] THEN
  SUBGOAL_THEN `(w INTER S INTER V) INTER u INTER V =
                (w INTER u) INTER (u INTER V:real^M->bool)` SUBST1_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC MOI_SCX_IMAGE_CONG THEN REWRITE_TAC[o_THM; IN_INTER] THEN
  X_GEN_TAC `y:real^M` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(s':real^2->real^M) (s y) = y` (fun th -> REWRITE_TAC[th]) THEN
  FIRST_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]);;

let MOI_S4P_CROSS_TRANS = prove
 (`!(S:real^M->bool) V (s:real^M->real^2) s' oo tau rho x.
     pl_curve_crossing_at S tau rho x /\ open V /\ x IN V /\ open oo /\
     pl_homeomorphism (S INTER V,oo) (s,s')
     ==> pl_curve_crossing_at (:real^2) (IMAGE s (tau INTER S INTER V))
                                        (IMAGE s (rho INTER S INTER V)) (s x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_curve_crossing_at] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `u:real^M->bool` (X_CHOOSE_THEN
    `f:real^M->real^2` (X_CHOOSE_THEN `g:real^2->real^M` STRIP_ASSUME_TAC)))
    STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(u:real^M->bool) SUBSET S` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_IMP_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `(!y:real^M. y IN S INTER V ==> (s':real^2->real^M) (s y) = y) /\
                IMAGE (s:real^M->real^2) (S INTER V) = oo /\
                (!y:real^M. y IN u ==> (g:real^2->real^M) (f y) = y) /\
                homeomorphism (S INTER V,oo) (s,s') /\
                homeomorphism (u,IMAGE f u) (f,g) /\ pl_map_on u f`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`pl_homeomorphism (S INTER V,oo) (s:real^M->real^2,s')`;
                           `pl_homeomorphism (u,IMAGE f u) (f:real^M->real^2,g)`] THEN
    SIMP_TAC[pl_homeomorphism; homeomorphism]; ALL_TAC] THEN
  SUBGOAL_THEN `locally_polyhedral (u INTER V:real^M->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC LOCALLY_POLYHEDRAL_INTER_OPEN THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(ISPECL [`u:real^M->bool`; `f:real^M->real^2`]
                        PL_MAP_ON_IMP_LOCALLY_POLYHEDRAL) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `open (IMAGE (f:real^M->real^2) (u INTER V))` ASSUME_TAC THENL
   [MATCH_MP_TAC OPEN_IN_OPEN_TRANS THEN EXISTS_TAC `IMAGE (f:real^M->real^2) u` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HOMEOMORPHISM_IMP_OPEN_MAP THEN
    MAP_EVERY EXISTS_TAC [`g:real^2->real^M`; `u:real^M->bool`] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC OPEN_IN_OPEN_INTER THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `open (IMAGE (s:real^M->real^2) (u INTER V))` ASSUME_TAC THENL
   [MATCH_MP_TAC OPEN_IN_OPEN_TRANS THEN EXISTS_TAC `oo:real^2->bool` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HOMEOMORPHISM_IMP_OPEN_MAP THEN
    MAP_EVERY EXISTS_TAC [`s':real^2->real^M`; `S INTER V:real^M->bool`] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `open_in (subtopology euclidean S) (u:real^M->bool)` THEN
    REWRITE_TAC[OPEN_IN_OPEN] THEN
    DISCH_THEN(X_CHOOSE_THEN `U0:real^M->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `U0 INTER V:real^M->bool` THEN ASM_SIMP_TAC[OPEN_INTER] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (s':real^2->real^M) (IMAGE s (u INTER V)) = u INTER V`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM IMAGE_o] THEN
    MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `IMAGE (\x:real^M. x) (u INTER V)` THEN
    CONJ_TAC THENL [ALL_TAC; REWRITE_TAC[IMAGE_ID]] THEN
    MATCH_MP_TAC MOI_SCX_IMAGE_CONG THEN
    REWRITE_TAC[o_THM] THEN X_GEN_TAC `y:real^M` THEN DISCH_TAC THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE ((f:real^M->real^2) o (s':real^2->real^M)) (IMAGE s (u INTER V)) =
                IMAGE f (u INTER V)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[IMAGE_o]; ALL_TAC] THEN
  EXISTS_TAC `IMAGE (s:real^M->real^2) (u INTER V)` THEN
  EXISTS_TAC `(f:real^M->real^2) o (s':real^2->real^M)` THEN
  EXISTS_TAC `(s:real^M->real^2) o (g:real^2->real^M)` THEN
  REWRITE_TAC[SUBTOPOLOGY_UNIV; GSYM OPEN_IN] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM SET_TAC[];
    MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `u INTER V:real^M->bool` THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`s':real^2->real^M`; `s:real^M->real^2`; `oo:real^2->bool`;
                     `S INTER V:real^M->bool`; `IMAGE (s:real^M->real^2) (u INTER V)`]
                    MOI_SCD_PLH_SUBSET) THEN
      ASM_SIMP_TAC[LOCALLY_POLYHEDRAL_OPEN] THEN DISCH_THEN MATCH_MP_TAC THEN
      CONJ_TAC THENL [ASM_MESON_TAC[PL_HOMEOMORPHISM_SYM]; ASM SET_TAC[]];
      MP_TAC(ISPECL [`f:real^M->real^2`; `g:real^2->real^M`; `u:real^M->bool`;
                     `IMAGE (f:real^M->real^2) u`; `u INTER V:real^M->bool`]
                    MOI_SCD_PLH_SUBSET) THEN
      ASM_SIMP_TAC[LOCALLY_POLYHEDRAL_OPEN; INTER_SUBSET]];
    REWRITE_TAC[o_THM] THEN
    SUBGOAL_THEN `(s':real^2->real^M) (s x) = x` (fun th -> ASM_REWRITE_TAC[th]) THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
    MP_TAC(ISPECL [`s:real^M->real^2`; `s':real^2->real^M`; `f:real^M->real^2`;
                   `g:real^2->real^M`; `S:real^M->bool`; `V:real^M->bool`;
                   `u:real^M->bool`; `tau:real^M->bool`] MOI_S4P_CHART_CAP) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`f:real^M->real^2`; `u INTER V:real^M->bool`; `u:real^M->bool`]
                  IMAGE_SUBSET) THEN
    REWRITE_TAC[INTER_SUBSET] THEN SET_TAC[];
    MP_TAC(ISPECL [`s:real^M->real^2`; `s':real^2->real^M`; `f:real^M->real^2`;
                   `g:real^2->real^M`; `S:real^M->bool`; `V:real^M->bool`;
                   `u:real^M->bool`; `rho:real^M->bool`] MOI_S4P_CHART_CAP) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`f:real^M->real^2`; `u INTER V:real^M->bool`; `u:real^M->bool`]
                  IMAGE_SUBSET) THEN
    REWRITE_TAC[INTER_SUBSET] THEN SET_TAC[]]);;
(* The bigon data of a surface S in real^3, inside a PL chart s of the     *)
(* open piece S INTER V onto an open set oo of the plane, satisfy the       *)
(* hypotheses of the 2D push MOI_S4P_PUSH2C.                                *)

let MOI_S4P_PLANE_DATA = prove
 (`!(S:real^3->bool) V (s:real^3->real^2) s' oo d a a' tau rho p q.
     open V /\ open oo /\ pl_homeomorphism (S INTER V,oo) (s,s') /\
     pl_cell_with_boundary 2 d (a UNION a') /\ d SUBSET S INTER V /\
     ~(p = q) /\ a INTER a' = {p,q} /\
     pl_cell_with_boundary 1 a {p,q} /\ pl_cell_with_boundary 1 a' {p,q} /\
     tau INTER d = a /\ rho INTER d = a' /\
     closure(tau DIFF a) INTER d SUBSET {p,q} /\
     closure(rho DIFF a') INTER d SUBSET {p,q} /\
     pl_curve_crossing_at S tau rho p /\ pl_curve_crossing_at S tau rho q
     ==> pl_cell_with_boundary 2 (IMAGE s d) (IMAGE s a UNION IMAGE s a') /\
         ~(s p = s q) /\ IMAGE s a INTER IMAGE s a' = {s p,s q} /\
         pl_cell_with_boundary 1 (IMAGE s a) {s p,s q} /\
         pl_cell_with_boundary 1 (IMAGE s a') {s p,s q} /\
         IMAGE s (tau INTER S INTER V) INTER IMAGE s d = IMAGE s a /\
         IMAGE s (rho INTER S INTER V) INTER IMAGE s d = IMAGE s a' /\
         closure(IMAGE s (tau INTER S INTER V) DIFF IMAGE s a) INTER IMAGE s d
           SUBSET {s p,s q} /\
         closure(IMAGE s (rho INTER S INTER V) DIFF IMAGE s a') INTER IMAGE s d
           SUBSET {s p,s q} /\
         pl_curve_crossing_at (:real^2) (IMAGE s (tau INTER S INTER V))
                                        (IMAGE s (rho INTER S INTER V)) (s p) /\
         pl_curve_crossing_at (:real^2) (IMAGE s (tau INTER S INTER V))
                                        (IMAGE s (rho INTER S INTER V)) (s q) /\
         IMAGE s d SUBSET oo`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(a:real^3->bool) SUBSET d /\ (a':real^3->bool) SUBSET d /\
                (p:real^3) IN d /\ (q:real^3) IN d /\ p IN V /\ q IN V`
  STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(!y:real^3. y IN S INTER V ==> (s':real^2->real^3) (s y) = y) /\
                IMAGE (s:real^3->real^2) (S INTER V) = oo /\
                homeomorphism (S INTER V,oo) (s,s')`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `pl_homeomorphism (S INTER V,oo) (s:real^3->real^2,s')` THEN
    SIMP_TAC[pl_homeomorphism; homeomorphism]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!X Y:real^3->bool. X SUBSET S INTER V /\ Y SUBSET S INTER V
                       ==> IMAGE (s:real^3->real^2) X INTER IMAGE s Y = IMAGE s (X INTER Y) /\
                           IMAGE s X DIFF IMAGE s Y = IMAGE s (X DIFF Y)`
  (LABEL_TAC "inj") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC MOI_SS2_INJ_IMAGE THEN
    EXISTS_TAC `s':real^2->real^3` THEN EXISTS_TAC `S INTER V:real^3->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!w:real^3->bool.
                  IMAGE (s:real^3->real^2) (w INTER S INTER V) INTER IMAGE s d =
                  IMAGE s (w INTER d)`
  (LABEL_TAC "capd") THENL
   [GEN_TAC THEN USE_THEN "inj" (MP_TAC o SPECL
      [`w INTER S INTER V:real^3->bool`; `d:real^3->bool`]) THEN
    ANTS_TAC THENL [UNDISCH_TAC `(d:real^3->bool) SUBSET S INTER V` THEN SET_TAC[]; ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN AP_TERM_TAC THEN
    UNDISCH_TAC `(d:real^3->bool) SUBSET S INTER V` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!w b:real^3->bool.
      w INTER d = b /\ closure(w DIFF b) INTER d SUBSET {p,q}
      ==> closure(IMAGE (s:real^3->real^2) (w INTER S INTER V) DIFF IMAGE s b) INTER
          IMAGE s d SUBSET {s p,s q}`
  (LABEL_TAC "cl") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    USE_THEN "inj" (MP_TAC o SPECL [`w INTER S INTER V:real^3->bool`; `b:real^3->bool`]) THEN
    ANTS_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`(w:real^3->bool) INTER d = b`; `(d:real^3->bool) SUBSET S INTER V`] THEN
      SET_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN
    MP_TAC(ISPECL [`s:real^3->real^2`; `s':real^2->real^3`; `S INTER V:real^3->bool`;
                   `oo:real^2->bool`; `(w INTER S INTER V) DIFF b:real^3->bool`;
                   `d:real^3->bool`] MOI_S4P_CLOSURE_TRANS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC(SET_RULE `(t:real^2->bool) SUBSET u ==> s SUBSET t ==> s SUBSET u`) THEN
    MATCH_MP_TAC(SET_RULE `x SUBSET {p,q} ==> IMAGE (f:real^3->real^2) x SUBSET {f p,f q}`) THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `closure(w DIFF b) INTER (d:real^3->bool)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(SET_RULE `(s:real^3->bool) SUBSET t ==> s INTER d SUBSET t INTER d`) THEN
    MATCH_MP_TAC SUBSET_CLOSURE THEN SET_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[GSYM IMAGE_UNION] THEN MATCH_MP_TAC MOI_S4P_CELL2_TRANS THEN
    MAP_EVERY EXISTS_TAC [`s':real^2->real^3`; `S INTER V:real^3->bool`; `oo:real^2->bool`] THEN
    ASM_REWRITE_TAC[DIMINDEX_2; LE_REFL];
    DISCH_TAC THEN UNDISCH_TAC `~(p:real^3 = q)` THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `(s':real^2->real^3) (s (p:real^3))` THEN
    CONJ_TAC THENL
     [CONV_TAC SYM_CONV THEN FIRST_ASSUM MATCH_MP_TAC THEN
       MAP_EVERY UNDISCH_TAC [`(d:real^3->bool) SUBSET S INTER V`; `(p:real^3) IN d`; `(q:real^3) IN d`] THEN
       SET_TAC[];
      ASM_REWRITE_TAC[] THEN FIRST_ASSUM MATCH_MP_TAC THEN
       MAP_EVERY UNDISCH_TAC [`(d:real^3->bool) SUBSET S INTER V`; `(p:real^3) IN d`; `(q:real^3) IN d`] THEN
       SET_TAC[]];
    USE_THEN "inj" (MP_TAC o SPECL [`a:real^3->bool`; `a':real^3->bool`]) THEN
    ANTS_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`(d:real^3->bool) SUBSET S INTER V`; `(a:real^3->bool) SUBSET d`;
                           `(a':real^3->bool) SUBSET d`] THEN SET_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN ASM_REWRITE_TAC[IMAGE_CLAUSES];
    MATCH_MP_TAC MOI_S4P_CELL1_TRANS THEN
    MAP_EVERY EXISTS_TAC [`s':real^2->real^3`; `S INTER V:real^3->bool`; `oo:real^2->bool`] THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC [`(d:real^3->bool) SUBSET S INTER V`; `(a:real^3->bool) SUBSET d`;
                           `(a':real^3->bool) SUBSET d`] THEN SET_TAC[];
    MATCH_MP_TAC MOI_S4P_CELL1_TRANS THEN
    MAP_EVERY EXISTS_TAC [`s':real^2->real^3`; `S INTER V:real^3->bool`; `oo:real^2->bool`] THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC [`(d:real^3->bool) SUBSET S INTER V`; `(a:real^3->bool) SUBSET d`;
                           `(a':real^3->bool) SUBSET d`] THEN SET_TAC[];
    USE_THEN "capd" (fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[];
    USE_THEN "capd" (fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[];
    USE_THEN "cl" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    USE_THEN "cl" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOI_S4P_CROSS_TRANS THEN EXISTS_TAC `s':real^2->real^3` THEN
    EXISTS_TAC `oo:real^2->bool` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOI_S4P_CROSS_TRANS THEN EXISTS_TAC `s':real^2->real^3` THEN
    EXISTS_TAC `oo:real^2->bool` THEN ASM_REWRITE_TAC[];
    UNDISCH_TAC `IMAGE (s:real^3->real^2) (S INTER V) = oo` THEN
    UNDISCH_TAC `(d:real^3->bool) SUBSET S INTER V` THEN SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The sphere chart.  A PL 2-cell is not a PL 2-sphere (as in               *)
(* MOI_S5F_CELL_NOT_SPHERE of pc_moi_s35_fina, which is outside this load    *)
(* closure); room for a small triangle on the boundary of a 3-simplex off a  *)
(* closed set; a facet chart carrying a 2-cell of the boundary sphere into   *)
(* the open base triangle of the standard simplex.                           *)
(* ------------------------------------------------------------------------- *)

let MOI_S4P_CELL_NOT_SPHERE = prove
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

let MOI_S4P_ROOM = prove
 (`!(k:real^3->bool) c.
     &3 simplex k /\ closed c /\ ~(relative_frontier k SUBSET c)
     ==> ?t. &2 simplex t /\ t SUBSET relative_frontier k /\ DISJOINT t c`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [simplex]) THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real^3->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`v:real^3->bool`; `relative_frontier k DIFF (c:real^3->bool)`]
                MOI_SS2_DENSE_FACET) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ONCE_REWRITE_TAC[SET_RULE `s DIFF c = s INTER ((:real^3) DIFF c)`] THEN
      MATCH_MP_TAC OPEN_IN_OPEN_INTER THEN ASM_REWRITE_TAC[GSYM closed];
      UNDISCH_TAC `~(relative_frontier k SUBSET (c:real^3->bool))` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^3` (X_CHOOSE_THEN `q:real^3` STRIP_ASSUME_TAC)) THEN
  ABBREV_TAC `ff = convex hull (v DELETE (w:real^3))` THEN
  SUBGOAL_THEN `&2 simplex (ff:real^3->bool) /\ ff SUBSET relative_frontier k`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_SPU_FACE_SIMPLEX THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [EXPAND_TAC "ff" THEN ASM_SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
      EXISTS_TAC `v DELETE (w:real^3)` THEN ASM_REWRITE_TAC[DELETE_SUBSET];
      EXPAND_TAC "ff" THEN REWRITE_TAC[AFF_DIM_CONVEX_HULL] THEN
      SUBGOAL_THEN `~affine_dependent(v DELETE (w:real^3))` ASSUME_TAC THENL
       [MATCH_MP_TAC AFFINE_INDEPENDENT_SUBSET THEN EXISTS_TAC `v:real^3->bool` THEN
        ASM_REWRITE_TAC[DELETE_SUBSET];
        ALL_TAC] THEN
      ASM_SIMP_TAC[AFF_DIM_AFFINE_INDEPENDENT; CARD_DELETE;
                   AFFINE_INDEPENDENT_IMP_FINITE] THEN
      UNDISCH_TAC `&(CARD(v:real^3->bool)):int = &3 + &1` THEN
      REWRITE_TAC[INT_OF_NUM_ADD; INT_OF_NUM_EQ] THEN CONV_TAC NUM_REDUCE_CONV THEN
      DISCH_THEN SUBST1_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN INT_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(q:real^3) IN ff /\ ~(q IN c)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [EXPAND_TAC "ff" THEN ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `?e. &0 < e /\ !y:real^3. norm(y - q) < e ==> ~(y IN c)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `closed(c:real^3->bool)` THEN REWRITE_TAC[closed; OPEN_CONTAINS_BALL] THEN
    DISCH_THEN(MP_TAC o SPEC `q:real^3`) THEN ASM_REWRITE_TAC[IN_DIFF; IN_UNIV] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `e:real` THEN
    REWRITE_TAC[SUBSET; IN_BALL; IN_DIFF; IN_UNIV] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[dist] THEN
    ONCE_REWRITE_TAC[NORM_SUB] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?B. &0 < B /\ !x:real^3. x IN ff ==> norm(x - q) <= B`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `bounded(ff:real^3->bool)` MP_TAC THENL
     [MATCH_MP_TAC POLYTOPE_IMP_BOUNDED THEN MATCH_MP_TAC SIMPLEX_IMP_POLYTOPE THEN
      EXISTS_TAC `&2:int` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[BOUNDED_POS] THEN DISCH_THEN(X_CHOOSE_THEN `b:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `&2 * b` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `norm(x:real^3) + norm(q:real^3)` THEN
    REWRITE_TAC[NORM_ARITH `norm(x - y:real^3) <= norm x + norm y`] THEN
    MATCH_MP_TAC(REAL_ARITH `x <= b /\ y <= b ==> x + y <= &2 * b`) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `del = min (&1) (e / (&4 * B))` THEN
  SUBGOAL_THEN `&0 < del /\ del <= &1 /\ del * B <= e / &2` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "del" THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[REAL_LT_MIN] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(e / (&4 * B)) * B` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
         [REAL_ARITH_TAC; ASM_SIMP_TAC[REAL_LT_IMP_LE]];
        SUBGOAL_THEN `e / (&4 * B) * B = e / &4` SUBST1_TAC THENL
         [UNDISCH_TAC `&0 < B` THEN CONV_TAC REAL_FIELD; ASM_REAL_ARITH_TAC]]];
    ALL_TAC] THEN
  EXISTS_TAC `IMAGE (\x:real^3. q + del % (x - q)) ff` THEN REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN `IMAGE (\x:real^3. q + del % (x - q)) ff =
                  IMAGE (\x. (q - del % q) + x) (IMAGE (\x. del % x) ff)` SUBST1_TAC THENL
     [REWRITE_TAC[GSYM IMAGE_o; o_DEF] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[FUN_EQ_THM] THEN VECTOR_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[SIMPLEX_TRANSLATION_EQ] THEN
    MP_TAC(ISPECL [`\x:real^3. del % x`; `ff:real^3->bool`; `&2:int`]
                  SIMPLEX_LINEAR_IMAGE_EQ) THEN
    ASM_REWRITE_TAC[LINEAR_SCALING] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[VECTOR_MUL_LCANCEL] THEN ASM_MESON_TAC[REAL_LT_IMP_NZ];
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `ff:real^3->bool` THEN
    ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    REWRITE_TAC[VECTOR_ARITH `q + d % (x - q):real^3 = (&1 - d) % q + d % x`] THEN
    MATCH_MP_TAC IN_CONVEX_SET THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[SIMPLEX_IMP_CONVEX]; ASM_REAL_ARITH_TAC];
    REWRITE_TAC[SET_RULE `!(f:real^3->real^3) s c. DISJOINT (IMAGE f s) c <=> !x. x IN s ==> ~(f x IN c)`] THEN
    X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[VECTOR_ARITH `(q + d % (x - q)) - q:real^3 = d % (x - q)`; NORM_MUL] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < d ==> abs d = d`] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `del * B` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      ASM_REAL_ARITH_TAC]]);;
(* A 2-cell d in the boundary sphere of a 3-simplex k: an extension fh of a *)
(* PL self-homeomorphism of that sphere to a polytope k2 around k, and an   *)
(* affine identification of the standard 3-simplex with k, after which fh   *)
(* carries d into the open base triangle conv{0,e1,e2} (plane x3 = 0).      *)

let MOI_S4P_FACET_CHART = prove
 (`!(k:real^3->bool) d j.
     &3 simplex k /\ pl_cell_with_boundary 2 d j /\ d SUBSET relative_frontier k
     ==> ?k2 fh gh (l:real^3->real^3) l' a0.
           polytope k2 /\ k SUBSET interior k2 /\ pl_homeomorphism (k2,k2) (fh,gh) /\
           IMAGE fh k = k /\ IMAGE fh (relative_frontier k) = relative_frontier k /\
           (!x. x IN k2 /\ ~(x IN interior k2) ==> ~(fh x IN interior k2)) /\
           linear l /\ linear l' /\ (!x. l'(l x) = x) /\ (!y. l(l' y) = y) /\
           IMAGE (\x. a0 + l x) (convex hull {vec 0,basis 1,basis 2,basis 3}) = k /\
           (!x. x IN d
                ==> l'(fh x - a0) IN
                    relative_interior(convex hull {vec 0,basis 1,basis 2}))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `pl_sphere 2 (relative_frontier k:real^3->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC PL_SPHERE_RELATIVE_FRONTIER_SIMPLEX THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(relative_frontier k SUBSET (d:real^3->bool))` ASSUME_TAC THENL
   [DISCH_TAC THEN
    MP_TAC(ISPECL [`d:real^3->bool`; `j:real^3->bool`] MOI_S4P_CELL_NOT_SPHERE) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `d = relative_frontier k:real^3->bool` (fun th -> ASM_REWRITE_TAC[th]) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:real^3->bool`; `d:real^3->bool`] MOI_S4P_ROOM) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
    ASM_MESON_TAC[MOI_SS2_CELL_FACTS];
    DISCH_THEN(X_CHOOSE_THEN `t0:real^3->bool` STRIP_ASSUME_TAC)] THEN
  SUBGOAL_THEN `pl_cell_with_boundary 2 (t0:real^3->bool) (relative_frontier t0)`
  ASSUME_TAC THENL
   [REWRITE_TAC[pl_cell_with_boundary] THEN
    MAP_EVERY EXISTS_TAC [`t0:real^3->bool`; `\x:real^3. x`; `\x:real^3. x`] THEN
    ASM_REWRITE_TAC[pl_homeomorphism; HOMEOMORPHISM_ID; IMAGE_ID] THEN
    REWRITE_TAC[GSYM LOCALLY_POLYHEDRAL_EQ_PL_MAP_ON_ID] THEN
    ASM_MESON_TAC[LOCALLY_POLYHEDRAL_POLYTOPE; SIMPLEX_IMP_POLYTOPE];
    ALL_TAC] THEN
  SUBGOAL_THEN `relative_frontier t0 SUBSET (t0:real^3->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC RELATIVE_FRONTIER_SUBSET THEN ASM_MESON_TAC[SIMPLEX_IMP_CLOSED];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`relative_frontier k:real^3->bool`; `t0:real^3->bool`;
                 `relative_frontier t0:real^3->bool`] DISK_COMPLEMENT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `dd = (relative_frontier k DIFF t0) UNION relative_frontier (t0:real^3->bool)` THEN
  MP_TAC(ISPEC `k:real^3->bool` MOI_SPU_SIMPLEX_HAS_FACE) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `f0:real^3->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`k:real^3->bool`; `dd:real^3->bool`; `relative_frontier t0:real^3->bool`;
                 `f0:real^3->bool`] MOI_SPU_SPHERE_DISK_PLH) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN EXPAND_TAC "dd" THEN ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `ph:real^3->real^3` (X_CHOOSE_THEN `ps:real^3->real^3`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `(!x:real^3. x IN relative_frontier k ==> ps(ph x) = x) /\
                IMAGE (ph:real^3->real^3) (relative_frontier k) = relative_frontier k`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[pl_homeomorphism; homeomorphism]; ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (ph:real^3->real^3) d SUBSET relative_interior f0` ASSUME_TAC THENL
   [SUBGOAL_THEN `IMAGE (ph:real^3->real^3) (dd DIFF relative_frontier t0) =
                  f0 DIFF relative_frontier f0` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`ph:real^3->real^3`; `ps:real^3->real^3`;
                     `relative_frontier k:real^3->bool`; `dd:real^3->bool`;
                     `relative_frontier t0:real^3->bool`] MOI_SS2_INJ_IMAGE) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN EXPAND_TAC "dd" THEN ASM SET_TAC[]; ALL_TAC] THEN
      DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT2) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `f0 DIFF relative_frontier (f0:real^3->bool)` THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN MATCH_MP_TAC IMAGE_SUBSET THEN
      EXPAND_TAC "dd" THEN ASM SET_TAC[];
      REWRITE_TAC[relative_frontier] THEN
      MP_TAC(ISPEC `f0:real^3->bool` CLOSURE_SUBSET) THEN SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:real^3->bool`; `ph:real^3->real^3`; `ps:real^3->real^3`]
                MOI_SPU_EXTEND_SPHERE_PLH) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `k2:real^3->bool` (X_CHOOSE_THEN `fh:real^3->real^3`
    (X_CHOOSE_THEN `gh:real^3->real^3` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`k:real^3->bool`; `f0:real^3->bool`] MOI_SPU_SIMPLEX_FACE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^3` (X_CHOOSE_THEN `a:real^3` (X_CHOOSE_THEN `b:real^3`
    (X_CHOOSE_THEN `c:real^3` (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC))))) THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `k:real^3->bool`)) THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `f0:real^3->bool`)) THEN
  MP_TAC(ISPECL [`a:real^3`; `b:real^3`; `c:real^3`; `w:real^3`] MOI_SS2_AFFINE_ISO) THEN
  ANTS_TAC THENL
   [SUBGOAL_THEN `{a,b,c,w} = {w,a,b,c:real^3}` SUBST1_TAC THENL [SET_TAC[]; ALL_TAC] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `l:real^3->real^3` (X_CHOOSE_THEN `l':real^3->real^3`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `!x y:real^3. (l:real^3->real^3) x = l y ==> x = y` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (\x. a + (l:real^3->real^3) x) {vec 0,basis 1,basis 2,basis 3} = {a,b,c,w} /\
    IMAGE (\x. a + (l:real^3->real^3) x) {vec 0,basis 1,basis 2} = {a,b,c}`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `(l:real^3->real^3) (vec 0) = vec 0` ASSUME_TAC THENL
     [MP_TAC(ISPEC `l:real^3->real^3` LINEAR_0) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[IMAGE_CLAUSES] THEN
    REWRITE_TAC[VECTOR_ADD_RID; VECTOR_ARITH `a + (b - a):real^3 = b`];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`k2:real^3->bool`; `fh:real^3->real^3`; `gh:real^3->real^3`;
                        `l:real^3->real^3`; `l':real^3->real^3`; `a:real^3`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `IMAGE (ph:real^3->real^3) (relative_frontier k)` THEN
    CONJ_TAC THENL [MATCH_MP_TAC MOI_SCX_IMAGE_CONG THEN ASM_SIMP_TAC[]; ASM_REWRITE_TAC[]];
    MP_TAC(ISPECL [`l:real^3->real^3`; `a:real^3`;
                   `{vec 0,basis 1,basis 2,basis 3}:real^3->bool`] MOI_SS2_AFFINE_IMAGES) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN
    UNDISCH_TAC `convex hull {w,a,b,c:real^3} = k` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    AP_TERM_TAC THEN SET_TAC[];
    X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(fh:real^3->real^3) x IN
                  IMAGE (\x. a + (l:real^3->real^3) x)
                        (relative_interior(convex hull {vec 0:real^3,basis 1,basis 2}))`
    MP_TAC THENL
     [MP_TAC(ISPECL [`l:real^3->real^3`; `a:real^3`;
                     `convex hull {vec 0,basis 1,basis 2}:real^3->bool`]
                    MOI_SS2_AFFINE_IMAGES) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM o last o CONJUNCTS) THEN
      MP_TAC(ISPECL [`l:real^3->real^3`; `a:real^3`;
                     `{vec 0,basis 1,basis 2}:real^3->bool`] MOI_SS2_AFFINE_IMAGES) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN
      UNDISCH_TAC `convex hull {a,b,c:real^3} = f0` THEN DISCH_THEN SUBST1_TAC THEN
      SUBGOAL_THEN `(fh:real^3->real^3) x = ph x` SUBST1_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o SPEC `x:real^3` o check (fun th ->
          can (find_term ((=) `gh:real^3->real^3`)) (concl th) && is_forall(concl th) &&
          can (find_term ((=) `ps:real^3->real^3`)) (concl th))) THEN
        ANTS_TAC THENL [ASM SET_TAC[]; SIMP_TAC[]];
        ALL_TAC] THEN
      ASM SET_TAC[];
      REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) THEN
      ASM_REWRITE_TAC[VECTOR_ARITH `(a + y) - a:real^3 = y`]]]);;

(* ------------------------------------------------------------------------- *)
(* The 3D push in the normalized chart: the suspension of a 2D              *)
(* push conjugated by a planar chart f x id, level-preserving, with compact  *)
(* support over g(k) in the slab |x3| <= h.                                  *)
(* ------------------------------------------------------------------------- *)

let MOI_S4P_EP3 = prove
 (`(!x:real^3. moi_scx_e(moi_scx_pr x) + x$3 % basis 3 = x) /\
   moi_scx_pr(basis 3) = vec 0 /\
   (!x:real^3 c. moi_scx_pr(x + c % basis 3) = moi_scx_pr x) /\
   (!u c. (moi_scx_e u + c % basis 3)$3 = c)`,
  REWRITE_TAC[moi_scx_e; moi_scx_pr; CART_EQ; DIMINDEX_2; DIMINDEX_3; FORALL_2;
              FORALL_3; VECTOR_2; VECTOR_3; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
              VEC_COMPONENT; MOI_SCX_B3] THEN
  REAL_ARITH_TAC);;

let MOI_S4P_PLH_UNIV_INV = prove
 (`!(f:real^N->real^N) g.
     pl_map_on (:real^N) f /\ pl_map_on (:real^N) g /\
     (!x. g(f x) = x) /\ (!y. f(g y) = y)
     ==> pl_homeomorphism ((:real^N),(:real^N)) (f,g)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HOMEOMORPHISM_IMP_PL_HOMEOMORPHISM THEN
  ASM_REWRITE_TAC[homeomorphism; IN_UNIV] THEN
  ASM_SIMP_TAC[PL_MAP_ON_IMP_CONTINUOUS_ON] THEN ASM SET_TAC[]);;

(* The product of a PL homeomorphism of the plane with the identity of the  *)
(* third coordinate.                                                         *)

let MOI_S4P_PROD_PLH = prove
 (`!(f:real^2->real^2) g.
     pl_homeomorphism ((:real^2),(:real^2)) (f,g)
     ==> pl_homeomorphism ((:real^3),(:real^3))
           ((\x. moi_scx_e(f(moi_scx_pr x)) + x$3 % basis 3),
            (\x. moi_scx_e(g(moi_scx_pr x)) + x$3 % basis 3))`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SA2_PLH_UNIV) THEN
  SUBGOAL_THEN
   `!v:real^2->real^2. pl_map_on (:real^2) v
       ==> pl_map_on (:real^3) (\x. moi_scx_e(v(moi_scx_pr x)) + x$3 % basis 3)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`(:real^3)`; `\x:real^3. moi_scx_e((v:real^2->real^2)(moi_scx_pr x))`;
                   `\x:real^3. x$3 % (basis 3:real^3)`] PL_MAP_ON_ADD) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
     [SUBGOAL_THEN `(\x:real^3. moi_scx_e((v:real^2->real^2)(moi_scx_pr x))) =
                    moi_scx_e o v o moi_scx_pr` SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC PL_MAP_ON_COMPOSE THEN EXISTS_TAC `(:real^2)` THEN
      REWRITE_TAC[SUBSET_UNIV] THEN CONJ_TAC THENL
       [MATCH_MP_TAC PL_MAP_ON_COMPOSE THEN EXISTS_TAC `(:real^2)` THEN
        ASM_REWRITE_TAC[SUBSET_UNIV] THEN MATCH_MP_TAC MOI_SCX_PL_LINEAR THEN
        SIMP_TAC[LOCALLY_POLYHEDRAL_OPEN; OPEN_UNIV; MOI_SCX_EP];
        MATCH_MP_TAC MOI_SCX_PL_LINEAR THEN
        SIMP_TAC[LOCALLY_POLYHEDRAL_OPEN; OPEN_UNIV; MOI_SCX_EP]];
      MATCH_MP_TAC MOI_SCX_PL_LINEAR THEN
      SIMP_TAC[LOCALLY_POLYHEDRAL_OPEN; OPEN_UNIV] THEN
      REWRITE_TAC[linear; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
      VECTOR_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_S4P_PLH_UNIV_INV THEN
  CONJ_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[pl_homeomorphism]; ALL_TAC] THEN
  CONJ_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[pl_homeomorphism]; ALL_TAC] THEN
  ASM_REWRITE_TAC[MOI_S4P_EP3; MOI_SCX_EP]);;

let MOI_S4P_CONJ_SUSPEND = prove
 (`!(f:real^2->real^2) g w w' k h.
     pl_homeomorphism ((:real^2),(:real^2)) (f,g) /\ &2 simplex k /\
     pl_homeomorphism ((:real^2),(:real^2)) (w,w') /\
     (!y. ~(y IN interior k) ==> w y = y) /\ &0 < h
     ==> ?G G' KG.
           pl_homeomorphism ((:real^3),(:real^3)) (G,G') /\
           compact KG /\ IMAGE G KG = KG /\ (!x. ~(x IN KG) ==> G x = x) /\
           (!x. (G x)$3 = x$3) /\
           (!x. x IN KG ==> moi_scx_pr x IN IMAGE g k /\ abs(x$3) <= h) /\
           (!y. G(moi_scx_e y) = moi_scx_e(g(w(f y)))) /\
           IMAGE moi_scx_e (IMAGE g k) SUBSET KG`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:real^2->bool`; `w:real^2->real^2`; `w':real^2->real^2`; `h:real`]
                MOI_S4P_SUSPEND) THEN
  ASM_SIMP_TAC[MOI_S4P_SIMPLEX2_INTERIOR] THEN
  ANTS_TAC THENL [ASM_MESON_TAC[SIMPLEX_IMP_POLYTOPE]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `sg:real^3->real^3` (X_CHOOSE_THEN `sg':real^3->real^3`
    (X_CHOOSE_THEN `B:real^3->bool` STRIP_ASSUME_TAC))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SA2_PLH_UNIV o
    check (fun th -> can (find_term ((=) `f:real^2->real^2`)) (concl th))) THEN
  ABBREV_TAC `F2 = \x:real^3. moi_scx_e((f:real^2->real^2)(moi_scx_pr x)) + x$3 % basis 3` THEN
  ABBREV_TAC `F2' = \x:real^3. moi_scx_e((g:real^2->real^2)(moi_scx_pr x)) + x$3 % basis 3` THEN
  SUBGOAL_THEN `pl_homeomorphism ((:real^3),(:real^3)) (F2,F2')` ASSUME_TAC THENL
   [EXPAND_TAC "F2" THEN EXPAND_TAC "F2'" THEN MATCH_MP_TAC MOI_S4P_PROD_PLH THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(!x:real^3. F2'(F2 x) = x) /\ (!x:real^3. F2(F2' x) = x) /\
    (!x:real^3. (F2 x)$3 = x$3) /\ (!x:real^3. (F2' x)$3 = x$3) /\
    (!x:real^3. moi_scx_pr(F2' x) = g(moi_scx_pr x)) /\
    (!y. F2(moi_scx_e y) = moi_scx_e(f y)) /\ (!y. F2'(moi_scx_e y) = moi_scx_e(g y))`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "F2" THEN EXPAND_TAC "F2'" THEN
    ASM_REWRITE_TAC[MOI_S4P_EP3; MOI_SCX_EP; VECTOR_MUL_LZERO; VECTOR_ADD_RID];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`(F2':real^3->real^3) o (sg:real^3->real^3) o (F2:real^3->real^3)`;
    `((F2':real^3->real^3) o (sg':real^3->real^3)) o (F2:real^3->real^3)`;
    `IMAGE (F2':real^3->real^3) B`] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `(:real^3)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `(:real^3)` THEN
      ASM_REWRITE_TAC[];
      ASM_MESON_TAC[PL_HOMEOMORPHISM_SYM]];
    MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[pl_homeomorphism; homeomorphism; CONTINUOUS_ON_SUBSET; SUBSET_UNIV];
    REWRITE_TAC[IMAGE_o] THEN
    SUBGOAL_THEN `IMAGE (F2:real^3->real^3) (IMAGE F2' B) = B` SUBST1_TAC THENL
     [REWRITE_TAC[GSYM IMAGE_o] THEN MATCH_MP_TAC EQ_TRANS THEN
      EXISTS_TAC `IMAGE (\x:real^3. x) B` THEN CONJ_TAC THENL
       [MATCH_MP_TAC MOI_SCX_IMAGE_CONG THEN ASM_REWRITE_TAC[o_THM];
        REWRITE_TAC[IMAGE_ID]];
      ASM_REWRITE_TAC[]];
    X_GEN_TAC `x:real^3` THEN REWRITE_TAC[o_THM] THEN DISCH_TAC THEN
    SUBGOAL_THEN `~((F2:real^3->real^3) x IN B)` (fun th -> ASM_SIMP_TAC[th]) THEN
    DISCH_TAC THEN UNDISCH_TAC `~((x:real^3) IN IMAGE (F2':real^3->real^3) B)` THEN REWRITE_TAC[IN_IMAGE] THEN
    EXISTS_TAC `(F2:real^3->real^3) x` THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[o_THM];
    REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_SIMP_TAC[]; ASM_SIMP_TAC[]];
    ASM_REWRITE_TAC[o_THM];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `y:real^2` THEN DISCH_TAC THEN
    REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `moi_scx_e y` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `IMAGE moi_scx_e k SUBSET (B:real^3->bool)` THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[]]);;
(* Near the open base triangle the standard 3-simplex is the half-space     *)
(* x3 >= 0 and its boundary is the plane x3 = 0.                             *)

let MOI_S4P_K0_SLAB = prove
 (`!x:real^3.
     &0 < x$1 /\ &0 < x$2 /\ x$1 + x$2 + abs(x$3) < &1
     ==> (x IN convex hull {vec 0,basis 1,basis 2,basis 3} <=> &0 <= x$3) /\
         (x IN relative_frontier(convex hull {vec 0,basis 1,basis 2,basis 3}) <=>
          x$3 = &0)`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `relative_frontier(convex hull {vec 0:real^3,basis 1,basis 2,basis 3}) =
                frontier(convex hull {vec 0,basis 1,basis 2,basis 3})` SUBST1_TAC THENL
   [MATCH_MP_TAC RELATIVE_FRONTIER_NONEMPTY_INTERIOR THEN
    REWRITE_TAC[MOI_SPU_INT_K0; GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
    EXISTS_TAC `vector[&1 / &4; &1 / &4; &1 / &4]:real^3` THEN
    REWRITE_TAC[VECTOR_3] THEN CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  REWRITE_TAC[MOI_SPU_K0; MOI_SPU_FRONTIER_K0; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC);;

(* A level-preserving map, the identity off KG and with IMAGE KG = KG, keeps *)
(* every set X that is a level condition on a set Q containing KG.          *)

let MOI_S4P_LEVEL_INV = prove
 (`!(G:real^3->real^3) KG Q X (P:real->bool).
     (!x. ~(x IN KG) ==> G x = x) /\ IMAGE G KG = KG /\ KG SUBSET Q /\
     (!x. (G x)$3 = x$3) /\ (!x. x IN Q ==> (x IN X <=> P(x$3)))
     ==> IMAGE G X = X`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    ASM_CASES_TAC `(x:real^3) IN KG` THENL [ALL_TAC; ASM_SIMP_TAC[]] THEN
    SUBGOAL_THEN `(x:real^3) IN Q /\ (G:real^3->real^3) x IN Q /\ G x IN KG`
    STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN UNDISCH_TAC `(x:real^3) IN X` THEN ASM_SIMP_TAC[];
    REWRITE_TAC[SUBSET; IN_IMAGE] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    ASM_CASES_TAC `(y:real^3) IN KG` THENL
     [ALL_TAC; EXISTS_TAC `y:real^3` THEN ASM_SIMP_TAC[]] THEN
    SUBGOAL_THEN `?x:real^3. x IN KG /\ (G:real^3->real^3) x = y` STRIP_ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    EXISTS_TAC `x:real^3` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(x:real^3) IN Q /\ y IN Q` STRIP_ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN UNDISCH_TAC `(y:real^3) IN X` THEN ASM_SIMP_TAC[] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `(G:real^3->real^3) x = y`)) THEN
    ASM_REWRITE_TAC[]]);;
(* Conjugating a PL homeomorphism G of real^3, supported in a compact set   *)
(* KG inside the interior of a polytope k2, by a PL self-homeomorphism fh   *)
(* of k2 that keeps the boundary of k2 on the boundary, and extending by    *)
(* the identity.                                                             *)

let MOI_S4P_CONJ_POLY = prove
 (`!(k2:real^3->bool) fh gh (G:real^3->real^3) G' KG.
     polytope k2 /\ pl_homeomorphism (k2,k2) (fh,gh) /\
     (!x. x IN k2 /\ ~(x IN interior k2) ==> ~(fh x IN interior k2)) /\
     pl_homeomorphism ((:real^3),(:real^3)) (G,G') /\
     KG SUBSET interior k2 /\ (!x. ~(x IN KG) ==> G x = x) /\ IMAGE G KG = KG
     ==> ?H H'. pl_homeomorphism ((:real^3),(:real^3)) (H,H') /\
                (!x. x IN k2 ==> H x = gh(G(fh x))) /\
                (!x. ~(x IN IMAGE gh KG) ==> H x = x) /\
                IMAGE H (IMAGE gh KG) = IMAGE gh KG`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(KG:real^3->bool) SUBSET k2` ASSUME_TAC THENL
   [MP_TAC(ISPEC `k2:real^3->bool` INTERIOR_SUBSET) THEN ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(!x:real^3. x IN k2 ==> gh(fh x) = x) /\ (!y:real^3. y IN k2 ==> fh(gh y) = y) /\
                IMAGE (fh:real^3->real^3) k2 = k2 /\ IMAGE (gh:real^3->real^3) k2 = k2`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[pl_homeomorphism; homeomorphism]; ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (G:real^3->real^3) k2 = k2` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
      ASM_CASES_TAC `(x:real^3) IN KG` THENL [ASM SET_TAC[]; ASM_SIMP_TAC[]];
      REWRITE_TAC[SUBSET; IN_IMAGE] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
      ASM_CASES_TAC `(y:real^3) IN KG` THENL
       [ASM SET_TAC[]; EXISTS_TAC `y:real^3` THEN ASM_SIMP_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_homeomorphism (k2,k2) ((G:real^3->real^3),G')` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`G:real^3->real^3`; `G':real^3->real^3`; `k2:real^3->bool`]
                  MOI_SCD_PLH_RESTRICT) THEN
    ASM_SIMP_TAC[POLYTOPE_IMP_PL_POLYHEDRON];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_homeomorphism (k2,k2)
                  (((gh:real^3->real^3) o (G:real^3->real^3)) o (fh:real^3->real^3),
                   gh o ((G':real^3->real^3) o (fh:real^3->real^3)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `k2:real^3->bool` THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `k2:real^3->bool` THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[PL_HOMEOMORPHISM_SYM];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k2:real^3->bool`;
                 `((gh:real^3->real^3) o (G:real^3->real^3)) o (fh:real^3->real^3)`;
                 `(gh:real^3->real^3) o ((G':real^3->real^3) o (fh:real^3->real^3))`]
                MOI_SA2_PLH_EXTEND_ID) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[o_THM] THEN X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
    SUBGOAL_THEN `~((fh:real^3->real^3) x IN KG)` (fun th -> ASM_SIMP_TAC[th]) THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `~((fh:real^3->real^3) x IN interior k2)` MP_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ASM SET_TAC[]];
    ALL_TAC] THEN
  DISCH_TAC THEN
  MAP_EVERY EXISTS_TAC
   [`\x:real^3. if x IN k2 then (((gh:real^3->real^3) o (G:real^3->real^3)) o (fh:real^3->real^3)) x else x`;
    `\x:real^3. if x IN k2 then ((gh:real^3->real^3) o ((G':real^3->real^3) o (fh:real^3->real^3))) x else x`] THEN
  ASM_REWRITE_TAC[o_THM] THEN REPEAT CONJ_TAC THENL
   [SIMP_TAC[];
    X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~((fh:real^3->real^3) x IN KG)` (fun th -> ASM_SIMP_TAC[th]) THEN
    DISCH_TAC THEN UNDISCH_TAC `~((x:real^3) IN IMAGE (gh:real^3->real^3) KG)` THEN REWRITE_TAC[IN_IMAGE] THEN
    EXISTS_TAC `(fh:real^3->real^3) x` THEN ASM_SIMP_TAC[];
    MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_IMAGE] THEN X_GEN_TAC `z:real^3` THEN
    DISCH_TAC THEN
    (SUBGOAL_THEN `(z:real^3) IN k2 /\ (gh:real^3->real^3) z IN k2` STRIP_ASSUME_TAC THENL
      [ASM SET_TAC[]; ALL_TAC]) THEN
    ASM_SIMP_TAC[] THENL
     [EXISTS_TAC `(G:real^3->real^3) z` THEN REWRITE_TAC[] THEN ASM SET_TAC[];
      SUBGOAL_THEN `?u:real^3. u IN KG /\ (G:real^3->real^3) u = z` STRIP_ASSUME_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      EXISTS_TAC `(gh:real^3->real^3) u` THEN
      SUBGOAL_THEN `(u:real^3) IN k2 /\ (gh:real^3->real^3) u IN k2` STRIP_ASSUME_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      ASM_SIMP_TAC[] THEN EXISTS_TAC `u:real^3` THEN ASM_REWRITE_TAC[]]]);;

(* The open base triangle of the standard simplex in the plane x3 = 0. *)

let MOI_S4P_RELINT_F0S = prove
 (`!x:real^3.
     x IN relative_interior(convex hull {vec 0,basis 1,basis 2})
     ==> x$3 = &0 /\ &0 < x$1 /\ &0 < x$2 /\ x$1 + x$2 < &1`,
  GEN_TAC THEN REWRITE_TAC[IN_RELATIVE_INTERIOR] THEN
  ABBREV_TAC `f0s = convex hull {vec 0:real^3,basis 1,basis 2}` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `!y:real^3. y IN f0s ==> y$3 = &0 /\ &0 <= y$1 /\ &0 <= y$2 /\ y$1 + y$2 <= &1`
  (LABEL_TAC "comp") THENL
   [EXPAND_TAC "f0s" THEN
    SUBGOAL_THEN `convex hull {vec 0:real^3,basis 1,basis 2} SUBSET
                  {y | y$3 = &0} INTER convex hull {vec 0,basis 1,basis 2,basis 3}`
    MP_TAC THENL
     [REWRITE_TAC[SUBSET_INTER] THEN CONJ_TAC THENL
       [MATCH_MP_TAC HULL_MINIMAL THEN CONJ_TAC THENL
         [REWRITE_TAC[SUBSET; IN_INSERT; NOT_IN_EMPTY; IN_ELIM_THM] THEN
          REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[VEC_COMPONENT] THEN
          SIMP_TAC[BASIS_COMPONENT; DIMINDEX_3; ARITH];
          SUBGOAL_THEN `{y:real^3 | y$3 = &0} = {y | basis 3 dot y = &0}` SUBST1_TAC THENL
           [SIMP_TAC[DOT_BASIS; DIMINDEX_3; ARITH]; REWRITE_TAC[CONVEX_HYPERPLANE]]];
        MATCH_MP_TAC HULL_MONO THEN SET_TAC[]];
      REWRITE_TAC[MOI_SPU_K0; SUBSET; IN_INTER; IN_ELIM_THM] THEN DISCH_TAC THEN
      X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `y:real^3`) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(vec 0:real^3) IN f0s /\ basis 1 IN f0s /\ basis 2 IN f0s /\
                affine(affine hull f0s) /\ (f0s:real^3->bool) SUBSET affine hull f0s`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "f0s" THEN SIMP_TAC[HULL_INC; IN_INSERT; AFFINE_AFFINE_HULL; HULL_SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN `!v:real^3. v IN affine hull f0s /\ norm(v - x) < e ==> v IN f0s`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    UNDISCH_TAC `ball(x:real^3,e) INTER affine hull f0s SUBSET f0s` THEN
    REWRITE_TAC[SUBSET; IN_INTER; IN_BALL; dist] THEN DISCH_THEN MATCH_MP_TAC THEN
    ONCE_REWRITE_TAC[NORM_SUB] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^3) IN affine hull f0s` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!c. abs c < e
                    ==> x + c % basis 1 IN (f0s:real^3->bool) /\ x + c % basis 2 IN f0s`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[VECTOR_ARITH `(x + c % b) - x:real^3 = c % b`; NORM_MUL] THEN
    SIMP_TAC[NORM_BASIS; DIMINDEX_3; ARITH; REAL_MUL_RID] THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[VECTOR_ARITH `x + c % b:real^3 = x + c % (b - vec 0)`] THEN
    MATCH_MP_TAC IN_AFFINE_ADD_MUL_DIFF THEN ASM SET_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `--(e / &2)`) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e / &2`) THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < e ==> abs(e / &2) < e /\ abs(--(e / &2)) < e`] THEN
  DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN
  MAP_EVERY (fun t -> USE_THEN "comp" (fun th -> MP_TAC(MATCH_MP th (ASSUME t))))
   [`x IN (f0s:real^3->bool)`; `x + e / &2 % basis 1 IN (f0s:real^3->bool)`;
    `x + --(e / &2) % basis 1 IN (f0s:real^3->bool)`;
    `x + --(e / &2) % basis 2 IN (f0s:real^3->bool)`] THEN
  REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
  SIMP_TAC[BASIS_COMPONENT; DIMINDEX_3; ARITH] THEN ASM_REAL_ARITH_TAC);;
(* ------------------------------------------------------------------------- *)
(* The bigon slide in real^3 (main theorem MOI_S4P_SLIDE).                   *)
(* ------------------------------------------------------------------------- *)

let MOI_S4P_Q_OPEN = prove
 (`open {x:real^3 | &0 < x$1 /\ &0 < x$2 /\ x$1 + x$2 + abs(x$3) < &1}`,
  SUBGOAL_THEN
   `{x:real^3 | &0 < x$1 /\ &0 < x$2 /\ x$1 + x$2 + abs(x$3) < &1} =
    {x | basis 1 dot x > &0} INTER {x | basis 2 dot x > &0} INTER
    {x | vector[&1; &1; &1] dot x < &1} INTER {x | vector[&1; &1; -- &1] dot x < &1}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM] THEN
    SIMP_TAC[DOT_BASIS; DIMINDEX_3; ARITH; DOT_3; VECTOR_3] THEN REAL_ARITH_TAC;
    SIMP_TAC[OPEN_INTER; OPEN_HALFSPACE_GT; OPEN_HALFSPACE_LT]]);;

let MOI_S4P_SLIDE = prove
 (`PL_SCHOENFLIES_3_AMBIENT_STATEMENT
   ==> !(S:real^3->bool) d a a' tau rho p q W0.
         pl_sphere 2 S /\ pl_cell_with_boundary 2 d (a UNION a') /\ d SUBSET S /\
         ~(p = q) /\ a INTER a' = {p,q} /\
         pl_cell_with_boundary 1 a {p,q} /\ pl_cell_with_boundary 1 a' {p,q} /\
         tau SUBSET S /\ rho SUBSET S /\ tau INTER d = a /\ rho INTER d = a' /\
         closure(tau DIFF a) INTER d SUBSET {p,q} /\
         closure(rho DIFF a') INTER d SUBSET {p,q} /\
         pl_curve_crossing_at S tau rho p /\ pl_curve_crossing_at S tau rho q /\
         open W0 /\ d SUBSET W0
         ==> ?phi phi' K.
               pl_homeomorphism ((:real^3),(:real^3)) (phi,phi') /\
               compact K /\ K SUBSET W0 /\
               (!x. ~(x IN K) ==> phi x = x) /\ IMAGE phi K = K /\
               IMAGE phi S = S /\ IMAGE phi (inside S) = inside S /\
               tau INTER rho INTER K = {p,q} /\
               IMAGE phi tau INTER rho INTER K = {}`,
  DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  (* the ambient Schoenflies chart f1 *)
  FIRST_ASSUM(MP_TAC o SPECL [`S:real^3->bool`; `(:real^3)`] o
    MATCH_MP MOI_SCD_COR_AMBIENT_BALL) THEN
  ASM_REWRITE_TAC[CONVEX_UNIV; OPEN_UNIV; SUBSET_UNIV; IN_UNIV] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^3->bool` (X_CHOOSE_THEN `f1:real^3->real^3`
    (X_CHOOSE_THEN `g1:real^3->real^3` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`f1:real^3->real^3`; `g1:real^3->real^3`] MOI_SCD_PL_HOMEO_UNIV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  (* the facet chart *)
  MP_TAC(ISPECL [`k:real^3->bool`; `IMAGE (f1:real^3->real^3) d`;
                 `IMAGE (f1:real^3->real^3) (a UNION a')`] MOI_S4P_FACET_CHART) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC MOI_SCD_CELL_IMAGE THEN EXISTS_TAC `g1:real^3->real^3` THEN
      ASM_REWRITE_TAC[];
      UNDISCH_TAC `IMAGE (f1:real^3->real^3) S = relative_frontier k` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k2:real^3->bool` (X_CHOOSE_THEN `fh:real^3->real^3`
    (X_CHOOSE_THEN `gh:real^3->real^3` (X_CHOOSE_THEN `l:real^3->real^3`
    (X_CHOOSE_THEN `l':real^3->real^3` (X_CHOOSE_THEN `a0:real^3` STRIP_ASSUME_TAC)))))) THEN
  SUBGOAL_THEN
   `(!x:real^3. x IN k2 ==> gh(fh x) = x) /\ (!y:real^3. y IN k2 ==> fh(gh y) = y) /\
    IMAGE (fh:real^3->real^3) k2 = k2 /\ IMAGE (gh:real^3->real^3) k2 = k2 /\
    fh continuous_on k2 /\ gh continuous_on k2 /\ pl_map_on k2 fh`
  STRIP_ASSUME_TAC THENL [UNDISCH_TAC `pl_homeomorphism (k2,k2) (fh:real^3->real^3,gh)` THEN
    SIMP_TAC[pl_homeomorphism; homeomorphism]; ALL_TAC] THEN
  SUBGOAL_THEN `(k:real^3->bool) SUBSET k2 /\ relative_frontier k SUBSET k`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [ASM_MESON_TAC[INTERIOR_SUBSET; SUBSET_TRANS];
      MATCH_MP_TAC RELATIVE_FRONTIER_SUBSET THEN ASM_MESON_TAC[SIMPLEX_IMP_CLOSED]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s:real^3->bool. s SUBSET k2 /\ IMAGE fh s = s ==> IMAGE gh s = s`
  (LABEL_TAC "ghinv") THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [SYM th]) THEN
    REWRITE_TAC[GSYM IMAGE_o] THEN MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `IMAGE (\x:real^3. x) s` THEN
    CONJ_TAC THENL [ALL_TAC; REWRITE_TAC[IMAGE_ID]] THEN
    MATCH_MP_TAC MOI_SCX_IMAGE_CONG THEN REWRITE_TAC[o_THM] THEN
    REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (gh:real^3->real^3) k = k /\
                IMAGE (gh:real^3->real^3) (relative_frontier k) = relative_frontier k`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[SUBSET_TRANS];
    ALL_TAC] THEN
  (* the standard simplex, the slab Q, the open set OO, the charts Psi, Psii *)
  ABBREV_TAC `k0 = convex hull {vec 0:real^3,basis 1,basis 2,basis 3}` THEN
  SUBGOAL_THEN `IMAGE (\x. a0 + (l:real^3->real^3) x) (relative_frontier k0) =
                relative_frontier k` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`l:real^3->real^3`; `a0:real^3`; `k0:real^3->bool`]
                  MOI_SS2_AFFINE_IMAGES) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(ACCEPT_TAC o SYM);
    ALL_TAC] THEN
  ABBREV_TAC `Q = {x:real^3 | &0 < x$1 /\ &0 < x$2 /\ x$1 + x$2 + abs(x$3) < &1}` THEN
  ABBREV_TAC `OO = {x:real^3 | x IN Q /\ a0 + (l:real^3->real^3) x IN interior k2 /\
                               (g1:real^3->real^3)((gh:real^3->real^3)(a0 + l x)) IN W0}` THEN
  SUBGOAL_THEN `open (OO:real^3->bool)` ASSUME_TAC THENL
   [SUBGOAL_THEN
     `OO = (Q:real^3->bool) INTER
           {x | x IN (:real^3) /\ (\x. a0 + (l:real^3->real^3) x) x IN
                {y | y IN interior k2 /\
                     ((g1:real^3->real^3) o (gh:real^3->real^3)) y IN W0}}`
    SUBST1_TAC THENL
     [EXPAND_TAC "OO" THEN REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM; IN_UNIV; o_THM] THEN
      MESON_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC OPEN_INTER THEN CONJ_TAC THENL
     [EXPAND_TAC "Q" THEN REWRITE_TAC[MOI_S4P_Q_OPEN]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN REWRITE_TAC[OPEN_UNIV] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_ADD THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
      ASM_SIMP_TAC[LINEAR_CONTINUOUS_ON; ETA_AX];
      ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN ASM_REWRITE_TAC[OPEN_INTERIOR; ETA_AX] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `k2:real^3->bool` THEN
      ASM_REWRITE_TAC[INTERIOR_SUBSET];
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^3)` THEN
      ASM_REWRITE_TAC[SUBSET_UNIV]];
    ALL_TAC] THEN
  ABBREV_TAC `Psi = \x:real^3. (l':real^3->real^3)((fh:real^3->real^3)((f1:real^3->real^3) x) - a0)` THEN
  ABBREV_TAC `Psii = \y:real^3. (g1:real^3->real^3)((gh:real^3->real^3)(a0 + (l:real^3->real^3) y))` THEN
  SUBGOAL_THEN `!x:real^3. (f1:real^3->real^3) x IN k2 ==> (Psii:real^3->real^3)(Psi x) = x`
  (LABEL_TAC "p1") THENL
   [EXPAND_TAC "Psi" THEN EXPAND_TAC "Psii" THEN REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[VECTOR_ARITH `a0 + (z - a0):real^3 = z`] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^3. a0 + (l:real^3->real^3) y IN k2 ==> (Psi:real^3->real^3)(Psii y) = y`
  (LABEL_TAC "p2") THENL
   [EXPAND_TAC "Psi" THEN EXPAND_TAC "Psii" THEN REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[VECTOR_ARITH `(a0 + z) - a0:real^3 = z`];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^3. x IN S
                  ==> (Psi:real^3->real^3) x IN relative_frontier k0 /\
                      (f1:real^3->real^3) x IN interior k2 /\ f1 x IN relative_frontier k`
  (LABEL_TAC "p3") THENL
   [X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(f1:real^3->real^3) x IN relative_frontier k` ASSUME_TAC THENL
     [UNDISCH_TAC `IMAGE (f1:real^3->real^3) S = relative_frontier k` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ALL_TAC;
      MAP_EVERY UNDISCH_TAC [`(f1:real^3->real^3) x IN relative_frontier k`;
        `relative_frontier k SUBSET (k:real^3->bool)`; `(k:real^3->bool) SUBSET interior k2`] THEN
      SET_TAC[]] THEN
    SUBGOAL_THEN `(fh:real^3->real^3)((f1:real^3->real^3) x) IN
                  IMAGE (\x. a0 + (l:real^3->real^3) x) (relative_frontier k0)` MP_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `IMAGE (fh:real^3->real^3) (relative_frontier k) = relative_frontier k` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) THEN
    EXPAND_TAC "Psi" THEN ASM_REWRITE_TAC[VECTOR_ARITH `(a0 + z) - a0:real^3 = z`];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^3. y IN relative_frontier k0 ==> (Psii:real^3->real^3) y IN S`
  (LABEL_TAC "p4") THENL
   [X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `a0 + (l:real^3->real^3) y IN relative_frontier k` MP_TAC THENL
     [SUBST1_TAC(SYM(ASSUME `IMAGE (\x. a0 + (l:real^3->real^3) x) (relative_frontier k0) =
                              relative_frontier k`)) THEN
      REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `y:real^3` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `(gh:real^3->real^3)(a0 + (l:real^3->real^3) y) IN relative_frontier k`
    MP_TAC THENL
     [UNDISCH_TAC `IMAGE (gh:real^3->real^3) (relative_frontier k) = relative_frontier k` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `IMAGE (f1:real^3->real^3) S = relative_frontier k` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `s0:real^3` STRIP_ASSUME_TAC) THEN
    EXPAND_TAC "Psii" THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^3. x IN d ==> (Psi:real^3->real^3) x IN OO /\ (Psi x)$3 = &0`
  (LABEL_TAC "p6") THENL
   [X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(Psi:real^3->real^3) x IN
                  relative_interior(convex hull {vec 0,basis 1,basis 2})` MP_TAC THENL
     [EXPAND_TAC "Psi" THEN REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP MOI_S4P_RELINT_F0S) THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(f1:real^3->real^3) x IN k` ASSUME_TAC THENL

     [MAP_EVERY UNDISCH_TAC [`(x:real^3) IN d`; `(d:real^3->bool) SUBSET S`;
        `IMAGE (f1:real^3->real^3) S = relative_frontier k`;
        `relative_frontier k SUBSET (k:real^3->bool)`] THEN
      SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `a0 + (l:real^3->real^3)(Psi x) = (fh:real^3->real^3)((f1:real^3->real^3) x)`
    ASSUME_TAC THENL
     [EXPAND_TAC "Psi" THEN ASM_REWRITE_TAC[VECTOR_ARITH `a0 + (z - a0):real^3 = z`];
      ALL_TAC] THEN
    EXPAND_TAC "OO" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [EXPAND_TAC "Q" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
      SUBGOAL_THEN `(fh:real^3->real^3)((f1:real^3->real^3) x) IN k` MP_TAC THENL
       [UNDISCH_TAC `IMAGE (fh:real^3->real^3) k = k` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
        MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
        UNDISCH_TAC `(k:real^3->bool) SUBSET interior k2` THEN SET_TAC[]];
      SUBGOAL_THEN `(f1:real^3->real^3) x IN k2` ASSUME_TAC THENL
       [MAP_EVERY UNDISCH_TAC [`(f1:real^3->real^3) x IN k`; `(k:real^3->bool) SUBSET k2`] THEN
        SET_TAC[];
        ALL_TAC] THEN
      ASM_SIMP_TAC[] THEN
      MAP_EVERY UNDISCH_TAC [`(x:real^3) IN d`; `(d:real^3->bool) SUBSET W0`] THEN SET_TAC[]];
    ALL_TAC] THEN
  (* continuity of the charts; the open sets V and oo *)
  SUBGOAL_THEN `(Psi:real^3->real^3) continuous_on {z | (f1:real^3->real^3) z IN k2}`
  ASSUME_TAC THENL
   [EXPAND_TAC "Psi" THEN
    MATCH_MP_TAC LINEAR_CONTINUOUS_ON_COMPOSE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUB THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
    SUBGOAL_THEN `(\x:real^3. (fh:real^3->real^3)((f1:real^3->real^3) x)) = fh o f1`
    SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^3)` THEN
      ASM_REWRITE_TAC[SUBSET_UNIV];
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `k2:real^3->bool` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(Psii:real^3->real^3) continuous_on OO` ASSUME_TAC THENL
   [EXPAND_TAC "Psii" THEN
    SUBGOAL_THEN `(\y:real^3. (g1:real^3->real^3)((gh:real^3->real^3)(a0 + (l:real^3->real^3) y))) =
                  g1 o gh o (\y. a0 + l y)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_ADD THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
        ASM_SIMP_TAC[LINEAR_CONTINUOUS_ON; ETA_AX];
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `k2:real^3->bool` THEN
        ASM_REWRITE_TAC[] THEN EXPAND_TAC "OO" THEN
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
        MESON_TAC[INTERIOR_SUBSET; SUBSET]];
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^3)` THEN
      ASM_REWRITE_TAC[SUBSET_UNIV]];
    ALL_TAC] THEN
  ABBREV_TAC `V = {x:real^3 | x IN {z | z IN (:real^3) /\ (f1:real^3->real^3) z IN interior k2} /\
                              (Psi:real^3->real^3) x IN OO}` THEN
  SUBGOAL_THEN `open (V:real^3->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "V" THEN MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `{z | (f1:real^3->real^3) z IN k2}` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_UNIV] THEN MESON_TAC[INTERIOR_SUBSET; SUBSET];
      MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN ASM_REWRITE_TAC[OPEN_UNIV; OPEN_INTERIOR]];
    ALL_TAC] THEN
  ABBREV_TAC `oo = {y:real^2 | y IN (:real^2) /\ moi_scx_e y IN OO}` THEN
  SUBGOAL_THEN `open (oo:real^2->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "oo" THEN MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN
    ASM_SIMP_TAC[OPEN_UNIV; LINEAR_CONTINUOUS_ON; MOI_SCX_EP];
    ALL_TAC] THEN
  (* the plane chart of S INTER V onto oo *)
  SUBGOAL_THEN `!x:real^3. x IN S INTER V
                  ==> (Psi:real^3->real^3) x IN OO /\ (Psi x)$3 = &0 /\
                      moi_scx_e(moi_scx_pr(Psi x)) = Psi x /\ (f1:real^3->real^3) x IN k2`
  (LABEL_TAC "c1") THENL
   [X_GEN_TAC `x:real^3` THEN EXPAND_TAC "V" THEN
    REWRITE_TAC[IN_INTER; IN_ELIM_THM; IN_UNIV] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(Psi:real^3->real^3) x IN Q` ASSUME_TAC THENL
     [UNDISCH_TAC `(Psi:real^3->real^3) x IN OO` THEN EXPAND_TAC "OO" THEN
      SIMP_TAC[IN_ELIM_THM];
      ALL_TAC] THEN
    SUBGOAL_THEN `((Psi:real^3->real^3) x)$3 = &0` ASSUME_TAC THENL
     [MP_TAC(ISPEC `(Psi:real^3->real^3) x` MOI_S4P_K0_SLAB) THEN ANTS_TAC THENL
       [UNDISCH_TAC `(Psi:real^3->real^3) x IN Q` THEN EXPAND_TAC "Q" THEN
        SIMP_TAC[IN_ELIM_THM];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[GSYM(CONJUNCT2 th)]) THEN
      USE_THEN "p3" (MP_TAC o SPEC `x:real^3`) THEN UNDISCH_TAC `(x:real^3) IN S` THEN
      MESON_TAC[];
      ALL_TAC] THEN
    ASM_SIMP_TAC[MOI_SCX_EP_INV] THEN
    MATCH_MP_TAC(REWRITE_RULE[SUBSET] INTERIOR_SUBSET) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^2. y IN oo
                  ==> (Psii:real^3->real^3)(moi_scx_e y) IN S INTER V /\
                      (Psi:real^3->real^3)(Psii(moi_scx_e y)) = moi_scx_e y`
  (LABEL_TAC "c2") THENL
   [X_GEN_TAC `y:real^2` THEN EXPAND_TAC "oo" THEN REWRITE_TAC[IN_ELIM_THM; IN_UNIV] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `moi_scx_e y IN Q /\ a0 + (l:real^3->real^3)(moi_scx_e y) IN interior k2`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `moi_scx_e y IN OO` THEN EXPAND_TAC "OO" THEN SIMP_TAC[IN_ELIM_THM];
      ALL_TAC] THEN
    SUBGOAL_THEN `moi_scx_e y IN relative_frontier k0` ASSUME_TAC THENL
     [MP_TAC(ISPEC `moi_scx_e y` MOI_S4P_K0_SLAB) THEN ANTS_TAC THENL
       [UNDISCH_TAC `moi_scx_e y IN Q` THEN EXPAND_TAC "Q" THEN SIMP_TAC[IN_ELIM_THM];
        ASM_REWRITE_TAC[MOI_SCX_EP] THEN MESON_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `(Psi:real^3->real^3)(Psii(moi_scx_e y)) = moi_scx_e y` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `Psii:real^3->real^3`)) (concl th) &&
        can (find_term ((=) `k2:real^3->bool`)) (concl th) &&
        not(can (find_term ((=) `f1:real^3->real^3`)) (concl th)))) THEN
      MATCH_MP_TAC(REWRITE_RULE[SUBSET] INTERIOR_SUBSET) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[IN_INTER] THEN
    SUBGOAL_THEN `(Psii:real^3->real^3)(moi_scx_e y) IN S` ASSUME_TAC THENL
     [USE_THEN "p4" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "V" THEN REWRITE_TAC[IN_ELIM_THM; IN_UNIV] THEN
    CONJ_TAC THENL
     [USE_THEN "p3" (fun th -> MP_TAC(MATCH_MP th
        (ASSUME `(Psii:real^3->real^3)(moi_scx_e (y:real^2)) IN S`))) THEN SIMP_TAC[];
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `sg = \x:real^3. moi_scx_pr((Psi:real^3->real^3) x)` THEN
  ABBREV_TAC `sg' = \y:real^2. (Psii:real^3->real^3)(moi_scx_e y)` THEN
  SUBGOAL_THEN `(!x:real^3. x IN S INTER V ==> (sg':real^2->real^3)(sg x) = x) /\
                (!y:real^2. y IN oo ==> (sg:real^3->real^2)(sg' y) = y) /\
                (!x:real^3. x IN S INTER V ==> (sg:real^3->real^2) x IN oo) /\
                (!y:real^2. y IN oo ==> (sg':real^2->real^3) y IN S INTER V)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "sg" THEN EXPAND_TAC "sg'" THEN REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
      USE_THEN "c1" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(x:real^3) IN S INTER V`))) THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN USE_THEN "p1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `y:real^2` THEN DISCH_TAC THEN
      USE_THEN "c2" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(y:real^2) IN oo`))) THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[MOI_SCX_EP];
      X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
      USE_THEN "c1" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(x:real^3) IN S INTER V`))) THEN
      STRIP_TAC THEN EXPAND_TAC "oo" THEN ASM_REWRITE_TAC[IN_ELIM_THM; IN_UNIV];
      X_GEN_TAC `y:real^2` THEN DISCH_TAC THEN
      USE_THEN "c2" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(y:real^2) IN oo`))) THEN
      SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `locally_polyhedral (S INTER V:real^3->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC LOCALLY_POLYHEDRAL_INTER_OPEN THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC LOCALLY_POLYHEDRAL_PL_POLYHEDRON THEN
    FIRST_ASSUM(MATCH_ACCEPT_TAC o MATCH_MP MOI_SCD_PL_SPHERE_POLYHEDRON);
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_homeomorphism (S INTER V,oo) (sg:real^3->real^2,sg')` ASSUME_TAC THENL
   [MATCH_MP_TAC HOMEOMORPHISM_IMP_PL_HOMEOMORPHISM THEN CONJ_TAC THENL
     [REWRITE_TAC[homeomorphism] THEN ASM_SIMP_TAC[] THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
         [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM_SIMP_TAC[];
          REWRITE_TAC[SUBSET; IN_IMAGE] THEN X_GEN_TAC `y:real^2` THEN DISCH_TAC THEN
          EXISTS_TAC `(sg':real^2->real^3) y` THEN ASM_SIMP_TAC[]];
        EXPAND_TAC "sg" THEN MATCH_MP_TAC LINEAR_CONTINUOUS_ON_COMPOSE THEN
        REWRITE_TAC[MOI_SCX_EP] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
        EXISTS_TAC `{z | (f1:real^3->real^3) z IN k2}` THEN ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
        USE_THEN "c1" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(x:real^3) IN S INTER V`))) THEN
        SIMP_TAC[];
        MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
         [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM_SIMP_TAC[];
          REWRITE_TAC[SUBSET; IN_IMAGE] THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
          EXISTS_TAC `(sg:real^3->real^2) x` THEN ASM_SIMP_TAC[]];
        EXPAND_TAC "sg'" THEN
        SUBGOAL_THEN `(\y:real^2. (Psii:real^3->real^3)(moi_scx_e y)) = Psii o moi_scx_e`
        SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
        MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
        SIMP_TAC[LINEAR_CONTINUOUS_ON; MOI_SCX_EP] THEN
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `OO:real^3->bool` THEN
        ASM_REWRITE_TAC[] THEN EXPAND_TAC "oo" THEN
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; IN_UNIV] THEN SIMP_TAC[]];
      EXPAND_TAC "sg" THEN EXPAND_TAC "Psi" THEN
      SUBGOAL_THEN
       `(\x:real^3. moi_scx_pr((l':real^3->real^3)((fh:real^3->real^3)
                                     ((f1:real^3->real^3) x) - a0))) =
        moi_scx_pr o (\z. l' z + --(l' a0)) o fh o f1`
      SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; o_THM] THEN ASM_SIMP_TAC[LINEAR_SUB] THEN
        REWRITE_TAC[VECTOR_SUB];
        ALL_TAC] THEN
      MATCH_MP_TAC PL_MAP_ON_COMPOSE THEN EXISTS_TAC `(:real^3)` THEN
      REWRITE_TAC[SUBSET_UNIV] THEN CONJ_TAC THENL
       [ALL_TAC;
        MATCH_MP_TAC MOI_SCX_PL_LINEAR THEN
        SIMP_TAC[LOCALLY_POLYHEDRAL_OPEN; OPEN_UNIV; MOI_SCX_EP]] THEN
      MATCH_MP_TAC PL_MAP_ON_COMPOSE THEN EXISTS_TAC `(:real^3)` THEN
      REWRITE_TAC[SUBSET_UNIV] THEN CONJ_TAC THENL
       [ALL_TAC;
        MATCH_MP_TAC PL_MAP_ON_AFFINE THEN
        ASM_SIMP_TAC[LOCALLY_POLYHEDRAL_OPEN; OPEN_UNIV]] THEN
      MATCH_MP_TAC PL_MAP_ON_COMPOSE THEN EXISTS_TAC `k2:real^3->bool` THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC PL_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^3)` THEN
        ASM_REWRITE_TAC[SUBSET_UNIV];
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
        USE_THEN "c1" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(x:real^3) IN S INTER V`))) THEN
        SIMP_TAC[]]];
    ALL_TAC] THEN
  (* the 2D push in the chart *)
  SUBGOAL_THEN `(d:real^3->bool) SUBSET S INTER V` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_INTER] THEN X_GEN_TAC `x:real^3` THEN
    DISCH_TAC THEN CONJ_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`(x:real^3) IN d`; `(d:real^3->bool) SUBSET S`] THEN SET_TAC[]; ALL_TAC] THEN
    EXPAND_TAC "V" THEN REWRITE_TAC[IN_ELIM_THM; IN_UNIV] THEN CONJ_TAC THENL
     [USE_THEN "p3" (MP_TAC o SPEC `x:real^3`) THEN ANTS_TAC THENL
       [MAP_EVERY UNDISCH_TAC [`(x:real^3) IN d`; `(d:real^3->bool) SUBSET S`] THEN SET_TAC[]; SIMP_TAC[]];
      USE_THEN "p6" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(x:real^3) IN d`))) THEN SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^3->bool`; `V:real^3->bool`; `sg:real^3->real^2`; `sg':real^2->real^3`;
                 `oo:real^2->bool`; `d:real^3->bool`; `a:real^3->bool`; `a':real^3->bool`;
                 `tau:real^3->bool`; `rho:real^3->bool`; `p:real^3`; `q:real^3`]
                MOI_S4P_PLANE_DATA) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`IMAGE (sg:real^3->real^2) d`; `IMAGE (sg:real^3->real^2) a`;
                 `IMAGE (sg:real^3->real^2) a'`;
                 `IMAGE (sg:real^3->real^2) (tau INTER S INTER V)`;
                 `IMAGE (sg:real^3->real^2) (rho INTER S INTER V)`;
                 `(sg:real^3->real^2) p`; `(sg:real^3->real^2) q`; `oo:real^2->bool`]
                MOI_S4P_PUSH2C) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `f2:real^2->real^2` (X_CHOOSE_THEN `g2:real^2->real^2`
    (X_CHOOSE_THEN `w:real^2->real^2` (X_CHOOSE_THEN `w':real^2->real^2`
    (X_CHOOSE_THEN `kq:real^2->bool` STRIP_ASSUME_TAC))))) THEN
  SUBGOAL_THEN `(!x:real^2. (g2:real^2->real^2)(f2 x) = x) /\ (!y:real^2. (f2:real^2->real^2)(g2 y) = y)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`f2:real^2->real^2`; `g2:real^2->real^2`] MOI_SA2_PLH_UNIV) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  (* the height of the slab *)
  SUBGOAL_THEN `?h. &0 < h /\
                    !x:real^3. moi_scx_pr x IN IMAGE (g2:real^2->real^2) kq /\ abs(x$3) <= h
                               ==> x IN OO`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`IMAGE moi_scx_e (IMAGE (g2:real^2->real^2) kq)`; `(:real^3) DIFF OO`]
                  SEPARATE_COMPACT_CLOSED) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
        SIMP_TAC[LINEAR_CONTINUOUS_ON; MOI_SCX_EP] THEN
        MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN CONJ_TAC THENL
         [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
          REWRITE_TAC[SUBSET_UNIV] THEN
          UNDISCH_TAC `pl_homeomorphism ((:real^2),(:real^2)) (f2:real^2->real^2,g2)` THEN
          SIMP_TAC[pl_homeomorphism; homeomorphism];
          FIRST_ASSUM(MATCH_ACCEPT_TAC o MATCH_MP SIMPLEX_IMP_COMPACT)];
        REWRITE_TAC[GSYM OPEN_CLOSED] THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[SET_RULE `!s t:real^3->bool. s INTER (UNIV DIFF t) = {} <=> s SUBSET t`] THEN
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN
        SUBGOAL_THEN `(g2:real^2->real^2) z IN oo` MP_TAC THENL
         [UNDISCH_TAC `IMAGE (g2:real^2->real^2) kq SUBSET oo` THEN
          REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN DISCH_THEN MATCH_MP_TAC THEN
          ASM_REWRITE_TAC[];
          ALL_TAC] THEN
        EXPAND_TAC "oo" THEN SIMP_TAC[IN_ELIM_THM]];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `del:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `del / &2` THEN ASM_REWRITE_TAC[REAL_HALF] THEN
    X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
    ONCE_REWRITE_TAC[TAUT `p <=> ~ ~p`] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`moi_scx_e(moi_scx_pr x)`; `x:real^3`]) THEN
    ASM_REWRITE_TAC[IN_DIFF; IN_UNIV] THEN
    SUBGOAL_THEN `moi_scx_e(moi_scx_pr x) IN IMAGE moi_scx_e (IMAGE (g2:real^2->real^2) kq)`
    (fun th -> REWRITE_TAC[th]) THENL [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[dist] THEN
    SUBGOAL_THEN `moi_scx_e(moi_scx_pr x) - x = --((x:real^3)$3 % basis 3)` SUBST1_TAC THENL
     [MP_TAC(CONJUNCT1 MOI_S4P_EP3) THEN DISCH_THEN(MP_TAC o SPEC `x:real^3`) THEN
      VECTOR_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[NORM_NEG; NORM_MUL] THEN SIMP_TAC[NORM_BASIS; DIMINDEX_3; ARITH] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the suspension, level preserving, supported in OO *)
  MP_TAC(ISPECL [`f2:real^2->real^2`; `g2:real^2->real^2`; `w:real^2->real^2`;
                 `w':real^2->real^2`; `kq:real^2->bool`; `h:real`] MOI_S4P_CONJ_SUSPEND) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `G:real^3->real^3` (X_CHOOSE_THEN `G':real^3->real^3`
    (X_CHOOSE_THEN `KG:real^3->bool` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `(KG:real^3->bool) SUBSET OO /\ (OO:real^3->bool) SUBSET Q` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[SUBSET] THEN
       UNDISCH_TAC `!x:real^3. x IN KG ==> moi_scx_pr x IN IMAGE (g2:real^2->real^2) kq /\ abs(x$3) <= h` THEN
       UNDISCH_TAC `!x:real^3. moi_scx_pr x IN IMAGE (g2:real^2->real^2) kq /\ abs(x$3) <= h ==> x IN OO` THEN
       MESON_TAC[];
      EXPAND_TAC "OO" THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (G:real^3->real^3) k0 = k0 /\
                IMAGE G (relative_frontier k0) = relative_frontier k0`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC MOI_S4P_LEVEL_INV THEN
    MAP_EVERY EXISTS_TAC [`KG:real^3->bool`; `Q:real^3->bool`] THENL
     [EXISTS_TAC `\t:real. &0 <= t`; EXISTS_TAC `\t:real. t = &0`] THEN
    ASM_REWRITE_TAC[] THEN
    (CONJ_TAC THENL
      [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `OO:real^3->bool` THEN ASM_REWRITE_TAC[];
       ALL_TAC]) THEN
    X_GEN_TAC `x:real^3` THEN EXPAND_TAC "Q" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    DISCH_THEN(MP_TAC o MATCH_MP MOI_S4P_K0_SLAB) THEN ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  (* conjugation by the affine map A, then by fh on k2 *)
  ABBREV_TAC `GA = \y:real^3. a0 + (l:real^3->real^3)((G:real^3->real^3)((l':real^3->real^3)(y - a0)))` THEN
  ABBREV_TAC `GA' = \y:real^3. a0 + (l:real^3->real^3)((G':real^3->real^3)((l':real^3->real^3)(y - a0)))` THEN
  SUBGOAL_THEN `pl_homeomorphism ((:real^3),(:real^3)) (GA:real^3->real^3,GA')` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`l:real^3->real^3`; `l':real^3->real^3`; `a0:real^3`] MOI_SS2_AFFINE_PLH) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `GA = ((\x. a0 + (l:real^3->real^3) x) o (G:real^3->real^3)) o
           (\y. (l':real^3->real^3)(y - a0)) /\
      GA' = (\x. a0 + (l:real^3->real^3) x) o ((G':real^3->real^3) o
            (\y. (l':real^3->real^3)(y - a0)))`
    (CONJUNCTS_THEN SUBST1_TAC) THENL
     [EXPAND_TAC "GA" THEN EXPAND_TAC "GA'" THEN REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `(:real^3)` THEN CONJ_TAC THENL
     [ONCE_REWRITE_TAC[PL_HOMEOMORPHISM_SYM] THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `(:real^3)` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z:real^3. (GA:real^3->real^3)(a0 + l z) = a0 + (l:real^3->real^3)((G:real^3->real^3) z)`
  (LABEL_TAC "ga") THENL
   [EXPAND_TAC "GA" THEN ASM_REWRITE_TAC[VECTOR_ARITH `(a0 + z) - a0:real^3 = z`]; ALL_TAC] THEN
  SUBGOAL_THEN `!X:real^3->bool. IMAGE (GA:real^3->real^3) (IMAGE (\x. a0 + (l:real^3->real^3) x) X) =
                                 IMAGE (\x. a0 + l x) (IMAGE (G:real^3->real^3) X)`
  (LABEL_TAC "gaim") THENL
   [GEN_TAC THEN REWRITE_TAC[GSYM IMAGE_o] THEN MATCH_MP_TAC MOI_SCX_IMAGE_CONG THEN
    REWRITE_TAC[o_THM] THEN USE_THEN "ga" (fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  ABBREV_TAC `KA = IMAGE (\x. a0 + (l:real^3->real^3) x) KG` THEN
  SUBGOAL_THEN
   `(!y:real^3. ~(y IN KA) ==> (GA:real^3->real^3) y = y) /\ IMAGE GA KA = KA /\
    KA SUBSET interior k2 /\ compact KA /\
    IMAGE GA k = k /\ IMAGE GA (relative_frontier k) = relative_frontier k`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
      SUBGOAL_THEN `y = a0 + (l:real^3->real^3)((l':real^3->real^3)(y - a0))` SUBST1_TAC THENL
       [ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
      USE_THEN "ga" (fun th -> REWRITE_TAC[th]) THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN DISCH_TAC THEN
      UNDISCH_TAC `~((y:real^3) IN KA)` THEN EXPAND_TAC "KA" THEN REWRITE_TAC[IN_IMAGE] THEN
      EXISTS_TAC `(l':real^3->real^3)(y - a0)` THEN ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC;
      EXPAND_TAC "KA" THEN USE_THEN "gaim" (fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[];
      EXPAND_TAC "KA" THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
      X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(z:real^3) IN OO` MP_TAC THENL
       [UNDISCH_TAC `(KG:real^3->bool) SUBSET OO` THEN UNDISCH_TAC `(z:real^3) IN KG` THEN SET_TAC[];
        ALL_TAC] THEN
      EXPAND_TAC "OO" THEN SIMP_TAC[IN_ELIM_THM];
      EXPAND_TAC "KA" THEN MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CONTINUOUS_ON_ADD THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
      ASM_SIMP_TAC[LINEAR_CONTINUOUS_ON; ETA_AX];
      SUBST1_TAC(SYM(ASSUME `IMAGE (\x. a0 + (l:real^3->real^3) x) k0 = k`)) THEN
      USE_THEN "gaim" (fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[];
      SUBST1_TAC(SYM(ASSUME `IMAGE (\x. a0 + (l:real^3->real^3) x) (relative_frontier k0) =
                              relative_frontier k`)) THEN
      USE_THEN "gaim" (fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k2:real^3->bool`; `fh:real^3->real^3`; `gh:real^3->real^3`;
                 `GA:real^3->real^3`; `GA':real^3->real^3`; `KA:real^3->bool`]
                MOI_S4P_CONJ_POLY) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `H:real^3->real^3` (X_CHOOSE_THEN `H':real^3->real^3`
    STRIP_ASSUME_TAC)) THEN
  (* the slide phi = g1 o H o f1 and its support K = Psii(KG) *)
  ABBREV_TAC `K = IMAGE (Psii:real^3->real^3) KG` THEN
  ABBREV_TAC `phi = (g1:real^3->real^3) o (H:real^3->real^3) o (f1:real^3->real^3)` THEN
  ABBREV_TAC `phi' = ((g1:real^3->real^3) o (H':real^3->real^3)) o (f1:real^3->real^3)` THEN
  SUBGOAL_THEN `pl_homeomorphism ((:real^3),(:real^3)) (phi:real^3->real^3,phi')`
  ASSUME_TAC THENL
   [EXPAND_TAC "phi" THEN EXPAND_TAC "phi'" THEN
    MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `(:real^3)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `(:real^3)` THEN
      ASM_REWRITE_TAC[];
      ONCE_REWRITE_TAC[PL_HOMEOMORPHISM_SYM] THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^3. (phi':real^3->real^3)(phi x) = x` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`phi:real^3->real^3`; `phi':real^3->real^3`] MOI_SCD_PL_HOMEO_UNIV) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN

  SUBGOAL_THEN `(!Y:real^3->bool. IMAGE (g1:real^3->real^3) (IMAGE f1 Y) = Y) /\
                (!Y:real^3->bool. IMAGE (f1:real^3->real^3) (IMAGE g1 Y) = Y)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN GEN_TAC THEN REWRITE_TAC[GSYM IMAGE_o] THEN MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `IMAGE (\x:real^3. x) Y` THEN
    (CONJ_TAC THENL [ALL_TAC; REWRITE_TAC[IMAGE_ID]]) THEN
    MATCH_MP_TAC MOI_SCX_IMAGE_CONG THEN ASM_REWRITE_TAC[o_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (f1:real^3->real^3) K = IMAGE (gh:real^3->real^3) KA` ASSUME_TAC THENL
   [EXPAND_TAC "K" THEN
    SUBST1_TAC(SYM(ASSUME `IMAGE (\x. a0 + (l:real^3->real^3) x) KG = KA`)) THEN
    EXPAND_TAC "Psii" THEN
    REWRITE_TAC[GSYM IMAGE_o] THEN MATCH_MP_TAC MOI_SCX_IMAGE_CONG THEN
    ASM_REWRITE_TAC[o_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (g1:real^3->real^3) (IMAGE (gh:real^3->real^3) KA) = K` ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!X:real^3->bool. X SUBSET k2 /\ IMAGE fh X = X /\ IMAGE GA X = X
                                 ==> IMAGE H X = X`
  (LABEL_TAC "hinv") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `IMAGE (\x. (gh:real^3->real^3)((GA:real^3->real^3)((fh:real^3->real^3) x))) X` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MOI_SCX_IMAGE_CONG THEN REWRITE_TAC[] THEN UNDISCH_TAC `(X:real^3->bool) SUBSET k2` THEN
      UNDISCH_TAC `!x:real^3. x IN k2 ==> (H:real^3->real^3) x = (gh:real^3->real^3) ((GA:real^3->real^3) ((fh:real^3->real^3) x))` THEN
      MESON_TAC[SUBSET];
      ALL_TAC] THEN
    SUBGOAL_THEN `IMAGE (\x. (gh:real^3->real^3)((GA:real^3->real^3)((fh:real^3->real^3) x))) X =
                  IMAGE gh (IMAGE GA (IMAGE fh X))` SUBST1_TAC THENL
     [REWRITE_TAC[GSYM IMAGE_o; o_DEF]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "ghinv" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (H:real^3->real^3) k = k /\
                IMAGE (H:real^3->real^3) (relative_frontier k) = relative_frontier k`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN USE_THEN "hinv" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `k:real^3->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^3. x IN S ==> (x IN K <=> (Psi:real^3->real^3) x IN KG)`
  (LABEL_TAC "kmem") THENL
   [X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN EQ_TAC THENL
     [SUBST1_TAC(SYM(ASSUME `IMAGE (Psii:real^3->real^3) KG = K`)) THEN REWRITE_TAC[IN_IMAGE] THEN
      DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `(z:real^3) IN OO` MP_TAC THENL
       [UNDISCH_TAC `(KG:real^3->bool) SUBSET OO` THEN REWRITE_TAC[SUBSET] THEN
        DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      EXPAND_TAC "OO" THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
      SUBGOAL_THEN `(Psi:real^3->real^3)(Psii z) = z` (fun th -> ASM_REWRITE_TAC[th]) THEN
      USE_THEN "p2" MATCH_MP_TAC THEN
      MATCH_MP_TAC(REWRITE_RULE[SUBSET] INTERIOR_SUBSET) THEN ASM_REWRITE_TAC[];
      DISCH_TAC THEN SUBST1_TAC(SYM(ASSUME `IMAGE (Psii:real^3->real^3) KG = K`)) THEN REWRITE_TAC[IN_IMAGE] THEN
      EXISTS_TAC `(Psi:real^3->real^3) x` THEN ASM_REWRITE_TAC[] THEN
      CONV_TAC SYM_CONV THEN USE_THEN "p1" MATCH_MP_TAC THEN
      USE_THEN "p3" (MP_TAC o C MATCH_MP (ASSUME `(x:real^3) IN S`)) THEN
      MESON_TAC[INTERIOR_SUBSET; SUBSET]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^3. x IN S /\ x IN K ==> x IN S INTER V /\ (Psi:real^3->real^3) x IN KG`
  (LABEL_TAC "ks") THENL
   [X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(Psi:real^3->real^3) x IN KG` ASSUME_TAC THENL
     [USE_THEN "kmem" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(x:real^3) IN S`))) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[IN_INTER] THEN EXPAND_TAC "V" THEN REWRITE_TAC[IN_ELIM_THM; IN_UNIV] THEN
    CONJ_TAC THENL
     [USE_THEN "p3" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(x:real^3) IN S`))) THEN
      SIMP_TAC[];
      UNDISCH_TAC `(KG:real^3->bool) SUBSET OO` THEN REWRITE_TAC[SUBSET] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^3. x IN S INTER V
                  ==> (phi:real^3->real^3) x =
                      (Psii:real^3->real^3)((G:real^3->real^3)((Psi:real^3->real^3) x))`
  (LABEL_TAC "phis") THENL
   [X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    USE_THEN "c1" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(x:real^3) IN S INTER V`))) THEN
    STRIP_TAC THEN EXPAND_TAC "phi" THEN REWRITE_TAC[o_THM] THEN ASM_SIMP_TAC[] THEN
    SUBGOAL_THEN `(fh:real^3->real^3)((f1:real^3->real^3) x) = a0 + l((Psi:real^3->real^3) x)`
    SUBST1_TAC THENL
     [EXPAND_TAC "Psi" THEN ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "ga" (fun th -> REWRITE_TAC[th]) THEN EXPAND_TAC "Psii" THEN REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^3. ~(x IN K) ==> (phi:real^3->real^3) x = x` (LABEL_TAC "phioff") THENL
   [X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN EXPAND_TAC "phi" THEN REWRITE_TAC[o_THM] THEN
    SUBGOAL_THEN `(H:real^3->real^3)((f1:real^3->real^3) x) = f1 x` (fun th -> ASM_REWRITE_TAC[th]) THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `H:real^3->real^3`)) (concl th) &&
      can (find_term ((=) `KA:real^3->bool`)) (concl th))) THEN
    DISCH_TAC THEN UNDISCH_TAC `~((x:real^3) IN K)` THEN REWRITE_TAC[] THEN
    SUBST1_TAC(SYM(ASSUME `IMAGE (g1:real^3->real^3) (IMAGE (gh:real^3->real^3) KA) = K`)) THEN
    MATCH_MP_TAC(SET_RULE `!(g:real^3->real^3) f s x. g(f x) = x /\ f x IN s ==> x IN IMAGE g s`) THEN
    EXISTS_TAC `f1:real^3->real^3` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (phi:real^3->real^3) S = S /\
                IMAGE (phi:real^3->real^3) (S UNION inside S) = S UNION inside S`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "phi" THEN REWRITE_TAC[IMAGE_o] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [SUBST1_TAC(SYM(ASSUME `IMAGE (f1:real^3->real^3) S = relative_frontier k`)) THEN
      ASM_REWRITE_TAC[];
      SUBST1_TAC(SYM(ASSUME `IMAGE (f1:real^3->real^3) (S UNION inside S) = k`)) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`phi:real^3->real^3`; `phi':real^3->real^3`; `K:real^3->bool`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [(* compact K *)
    SUBST1_TAC(SYM(ASSUME `IMAGE (Psii:real^3->real^3) KG = K`)) THEN
    MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `OO:real^3->bool` THEN
    ASM_REWRITE_TAC[];
    (* K SUBSET W0 *)
    SUBST1_TAC(SYM(ASSUME `IMAGE (Psii:real^3->real^3) KG = K`)) THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(z:real^3) IN OO` MP_TAC THENL
     [UNDISCH_TAC `(KG:real^3->bool) SUBSET OO` THEN REWRITE_TAC[SUBSET] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    EXPAND_TAC "OO" THEN EXPAND_TAC "Psii" THEN SIMP_TAC[IN_ELIM_THM];
    (* IMAGE phi K = K *)
    EXPAND_TAC "phi" THEN REWRITE_TAC[IMAGE_o] THEN ASM_REWRITE_TAC[];
    (* inside S *)
    MP_TAC(ISPECL [`phi:real^3->real^3`; `phi':real^3->real^3`; `(:real^3)`;
                   `S UNION inside S:real^3->bool`; `S:real^3->bool`] MOI_SS2_INJ_IMAGE) THEN
    ASM_REWRITE_TAC[SUBSET_UNIV; IN_UNIV] THEN
    DISCH_THEN(MP_TAC o CONJUNCT2) THEN
    MP_TAC(ISPEC `S:real^3->bool` INSIDE_NO_OVERLAP) THEN
    SUBGOAL_THEN `(S UNION inside S) DIFF S = inside S:real^3->bool` SUBST1_TAC THENL
     [MP_TAC(ISPEC `S:real^3->bool` INSIDE_NO_OVERLAP) THEN SET_TAC[]; ALL_TAC] THEN
    MESON_TAC[];
    (* tau INTER rho INTER K = {p,q} *)
    MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_INTER] THEN X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
      SUBGOAL_THEN `(x:real^3) IN S` ASSUME_TAC THENL
       [UNDISCH_TAC `(tau:real^3->bool) SUBSET S` THEN REWRITE_TAC[SUBSET] THEN
        DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      USE_THEN "ks" (fun th -> MP_TAC(MATCH_MP th
        (CONJ (ASSUME `(x:real^3) IN S`) (ASSUME `(x:real^3) IN K`)))) THEN STRIP_TAC THEN
      USE_THEN "c1" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(x:real^3) IN S INTER V`))) THEN
      STRIP_TAC THEN
      SUBGOAL_THEN `(sg:real^3->real^2) x IN IMAGE (g2:real^2->real^2) kq` ASSUME_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o SPEC `(Psi:real^3->real^3) x` o check (fun th ->
          is_forall(concl th) && can (find_term ((=) `h:real`)) (concl th) &&
          can (find_term ((=) `KG:real^3->bool`)) (concl th))) THEN
        ASM_REWRITE_TAC[] THEN EXPAND_TAC "sg" THEN SIMP_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `(f2:real^2->real^2)((sg:real^3->real^2) x) IN {f2(sg p),f2(sg q)}`
      MP_TAC THENL
       [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
          rand(concl th) = `{(f2:real^2->real^2)(sg(p:real^3)),f2(sg(q:real^3))}`)) THEN
        REWRITE_TAC[IN_INTER] THEN REPEAT CONJ_TAC THENL
         [MATCH_MP_TAC FUN_IN_IMAGE THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
           MAP_EVERY UNDISCH_TAC [`(x:real^3) IN tau`; `(x:real^3) IN S INTER V`] THEN SET_TAC[];
          MATCH_MP_TAC FUN_IN_IMAGE THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
           MAP_EVERY UNDISCH_TAC [`(x:real^3) IN rho`; `(x:real^3) IN S INTER V`] THEN SET_TAC[];
          UNDISCH_TAC `(sg:real^3->real^2) x IN IMAGE (g2:real^2->real^2) kq` THEN
          REWRITE_TAC[IN_IMAGE] THEN STRIP_TAC THEN ASM_REWRITE_TAC[]];
        ALL_TAC] THEN
      SUBGOAL_THEN `(p:real^3) IN S INTER V /\ (q:real^3) IN S INTER V` STRIP_ASSUME_TAC THENL
       [MAP_EVERY UNDISCH_TAC [`(d:real^3->bool) SUBSET S INTER V`; `a INTER a' = {p:real^3,q}`;
                               `tau INTER d = (a:real^3->bool)`] THEN SET_TAC[];
        ALL_TAC] THEN
      REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
      DISCH_THEN(DISJ_CASES_THEN (MP_TAC o AP_TERM `g2:real^2->real^2`)) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o AP_TERM `sg':real^2->real^3`) THEN
      ASM_SIMP_TAC[];
      REWRITE_TAC[SUBSET; IN_INSERT; NOT_IN_EMPTY; IN_INTER] THEN X_GEN_TAC `x:real^3` THEN
      SUBGOAL_THEN `!u:real^3. u IN d ==> u IN K` (LABEL_TAC "dk") THENL
       [X_GEN_TAC `u:real^3` THEN DISCH_TAC THEN
        SUBGOAL_THEN `(u:real^3) IN S INTER V /\ (u:real^3) IN S` STRIP_ASSUME_TAC THENL
         [UNDISCH_TAC `(d:real^3->bool) SUBSET S INTER V` THEN UNDISCH_TAC `(u:real^3) IN d` THEN
          SET_TAC[];
          ALL_TAC] THEN
        USE_THEN "kmem" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `(u:real^3) IN S`)]) THEN
        USE_THEN "c1" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(u:real^3) IN S INTER V`))) THEN
        STRIP_TAC THEN
        SUBGOAL_THEN `moi_scx_e((sg:real^3->real^2) u) IN KG` MP_TAC THENL
         [UNDISCH_TAC `IMAGE moi_scx_e (IMAGE (g2:real^2->real^2) kq) SUBSET KG` THEN
          REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
          MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[IN_IMAGE] THEN
          EXISTS_TAC `(f2:real^2->real^2)((sg:real^3->real^2) u)` THEN ASM_REWRITE_TAC[] THEN
          MP_TAC(ISPEC `kq:real^2->bool` INTERIOR_SUBSET) THEN
          UNDISCH_TAC `IMAGE (f2:real^2->real^2) (IMAGE (sg:real^3->real^2) d) SUBSET interior kq` THEN
          REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN DISCH_THEN(fun th1 -> DISCH_THEN(fun th2 ->
            MATCH_MP_TAC th2 THEN MATCH_MP_TAC th1 THEN ASM_REWRITE_TAC[]));
          EXPAND_TAC "sg" THEN ASM_REWRITE_TAC[]];
        ALL_TAC] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      (CONJ_TAC THENL
        [MAP_EVERY UNDISCH_TAC [`a INTER a' = {p:real^3,q}`; `tau INTER d = (a:real^3->bool)`;
                             `rho INTER d = (a':real^3->bool)`] THEN SET_TAC[];
         ALL_TAC]) THEN
      (CONJ_TAC THENL
        [MAP_EVERY UNDISCH_TAC [`a INTER a' = {p:real^3,q}`; `tau INTER d = (a:real^3->bool)`;
                             `rho INTER d = (a':real^3->bool)`] THEN SET_TAC[];
         ALL_TAC]) THEN
      USE_THEN "dk" MATCH_MP_TAC THEN
      MAP_EVERY UNDISCH_TAC [`a INTER a' = {p:real^3,q}`; `tau INTER d = (a:real^3->bool)`;
                             `rho INTER d = (a':real^3->bool)`] THEN SET_TAC[]];
    (* IMAGE phi tau INTER rho INTER K = {} *)
    REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN X_GEN_TAC `z:real^3` THEN
    REWRITE_TAC[IN_IMAGE] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(x:real^3) IN K` ASSUME_TAC THENL
     [ONCE_REWRITE_TAC[TAUT `p <=> ~ ~p`] THEN DISCH_TAC THEN
      UNDISCH_TAC `(z:real^3) IN K` THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "phioff" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `~((x:real^3) IN K)`)]) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(x:real^3) IN S` ASSUME_TAC THENL
     [UNDISCH_TAC `(tau:real^3->bool) SUBSET S` THEN REWRITE_TAC[SUBSET] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    USE_THEN "ks" (fun th -> MP_TAC(MATCH_MP th
      (CONJ (ASSUME `(x:real^3) IN S`) (ASSUME `(x:real^3) IN K`)))) THEN STRIP_TAC THEN
    USE_THEN "c1" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(x:real^3) IN S INTER V`))) THEN
    STRIP_TAC THEN
    ABBREV_TAC `y = (sg:real^3->real^2) x` THEN
    SUBGOAL_THEN `(Psi:real^3->real^3) x = moi_scx_e y` ASSUME_TAC THENL
     [EXPAND_TAC "y" THEN EXPAND_TAC "sg" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ABBREV_TAC `y' = (g2:real^2->real^2)((w:real^2->real^2)((f2:real^2->real^2) y))` THEN
    SUBGOAL_THEN `(G:real^3->real^3)((Psi:real^3->real^3) x) = moi_scx_e y'` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `moi_scx_e y' IN KG` ASSUME_TAC THENL
     [SUBST1_TAC(SYM(ASSUME `(G:real^3->real^3)((Psi:real^3->real^3) x) = moi_scx_e y'`)) THEN
      SUBST1_TAC(SYM(ASSUME `IMAGE (G:real^3->real^3) KG = KG`)) THEN
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(y':real^2) IN oo` ASSUME_TAC THENL
     [EXPAND_TAC "oo" THEN REWRITE_TAC[IN_ELIM_THM; IN_UNIV] THEN
      UNDISCH_TAC `(KG:real^3->bool) SUBSET OO` THEN REWRITE_TAC[SUBSET] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(phi:real^3->real^3) x = (sg':real^2->real^3) y'` ASSUME_TAC THENL
     [USE_THEN "phis" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `(x:real^3) IN S INTER V`)]) THEN
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "sg'" THEN REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(z:real^3) IN S INTER V /\ (sg:real^3->real^2) z = y'` STRIP_ASSUME_TAC THENL
     [ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(y':real^2) IN IMAGE (sg:real^3->real^2) (rho INTER S INTER V)` ASSUME_TAC THENL
     [SUBST1_TAC(SYM(ASSUME `(sg:real^3->real^2) z = y'`)) THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
      MP_TAC(ASSUME `(z:real^3) IN S INTER V`) THEN UNDISCH_TAC `(z:real^3) IN rho` THEN
      REWRITE_TAC[IN_INTER] THEN SIMP_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(y':real^2) IN IMAGE (g2:real^2->real^2) kq` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `moi_scx_e y'` o check (fun th ->
        is_forall(concl th) && can (find_term ((=) `h:real`)) (concl th) &&
        can (find_term ((=) `KG:real^3->bool`)) (concl th))) THEN
      ASM_REWRITE_TAC[MOI_SCX_EP] THEN SIMP_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(w:real^2->real^2)((f2:real^2->real^2) y) = f2 y'` ASSUME_TAC THENL
     [SUBST1_TAC(SYM(ASSUME `(g2:real^2->real^2)((w:real^2->real^2)((f2:real^2->real^2) y)) = y'`)) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(w:real^2->real^2)((f2:real^2->real^2) y) IN
                  IMAGE w (IMAGE f2 (IMAGE (sg:real^3->real^2) (tau INTER S INTER V))) INTER
                  IMAGE f2 (IMAGE sg (rho INTER S INTER V)) INTER kq` MP_TAC THENL
     [REWRITE_TAC[IN_INTER] THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC FUN_IN_IMAGE THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
        SUBST1_TAC(SYM(ASSUME `(sg:real^3->real^2) x = y`)) THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
        MP_TAC(ASSUME `(x:real^3) IN S INTER V`) THEN UNDISCH_TAC `(x:real^3) IN tau` THEN
        REWRITE_TAC[IN_INTER] THEN SIMP_TAC[];
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `(y':real^2) IN IMAGE (g2:real^2->real^2) kq` THEN
        REWRITE_TAC[IN_IMAGE] THEN STRIP_TAC THEN ASM_REWRITE_TAC[]];
      ASM_REWRITE_TAC[NOT_IN_EMPTY]]]);;

