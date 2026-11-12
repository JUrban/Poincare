(* ========================================================================= *)
(* pc_moi_s33_conn: Moise GTM 47, Sec 33, Lemmas 5-6 (p.232): connected X   *)
(* and Bd X, connected handle pieces.  Main theorems S33_L5 |- MOI_S33_L5   *)
(* and S33_L6 |- MOI_S33_L6 (pc_moi_s33_stmt.ml).  Route: L5 as in the      *)
(* book: 30.2 on Bd X gives a separating component B, and 26.6 in           *)
(* triangulated form (MOI_S30_BOUNDS) fills it; the traces are untouched.   *)
(* L6: a refinement of x carrying the trace polygons, two sides at each     *)
(* trace from the crossing condition, and connectivity of each piece by     *)
(* 30.2 on Fr(X INTER c v) (the book's last step, which it leaves           *)
(* implicit).                                                               *)
(* ========================================================================= *)

needs "src/pc_moi_s33_stmt.ml";;
needs "src/pc_moi_fnd_m3a.ml";;
needs "src/pc_moi_fnd_m3b.ml";;
needs "src/pc_moi_fnd_euler.ml";;
needs "src/pc_moi_fnd_rn.ml";;
needs "src/pc_moi_s26_nbhd.ml";;
needs "src/pc_moi_sch3_s2.ml";;
needs "src/pc_moi_s30_bound.ml";;
needs "src/pc_moi_s26_cut.ml";;
needs "src/pc_moi_s3032_stmt6.ml";;   (* MOI_S3S6_FINITE_COMPONENTS *)
needs "src/pc_moi_s28_cut.ml";;       (* MOI_S8CU_HALF_FROM_LOCAL *)

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Part 1: tools.  pl_crossing_at is local in its second set                *)
(* (MOI_S3CN_CROSSING_LOCAL); a pseudo-cell minus a closed topological disk *)
(* away from its rim is connected (MOI_S3CN_CELL_MINUS_DISK, via the open   *)
(* unit disk minus a compact set with connected complement,                 *)
(* MOI_S3CN_BALL_MINUS_COMPACT, and a closest-point retraction).            *)
(* ------------------------------------------------------------------------- *)

let MOI_S3CN_CROSSING_LOCAL = prove
 (`!(s:real^3->bool) t t' y w.
     pl_crossing_at s t y /\ open w /\ y IN w /\ t INTER w = t' INTER w
     ==> pl_crossing_at s t' y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_crossing_at] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `u:real^3->bool` (X_CHOOSE_THEN `f:real^3->real^3`
      (X_CHOOSE_THEN `g:real^3->real^3` STRIP_ASSUME_TAC))) STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`u INTER w:real^3->bool`; `f:real^3->real^3`; `g:real^3->real^3`] THEN
  UNDISCH_TAC `pl_homeomorphism (u,IMAGE (f:real^3->real^3) u) (f,g)` THEN
  REWRITE_TAC[pl_homeomorphism] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!a b:real^3->bool. a SUBSET u /\ b SUBSET u
                ==> IMAGE (f:real^3->real^3) (a INTER b) = IMAGE f a INTER IMAGE f b`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN UNDISCH_TAC `homeomorphism (u,IMAGE (f:real^3->real^3) u) (f,g)` THEN
    REWRITE_TAC[homeomorphism] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `open (IMAGE (f:real^3->real^3) (u INTER w))` ASSUME_TAC THENL
   [MATCH_MP_TAC OPEN_IN_OPEN_TRANS THEN
    EXISTS_TAC `IMAGE (f:real^3->real^3) u` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC HOMEOMORPHISM_IMP_OPEN_MAP THEN
    MAP_EVERY EXISTS_TAC [`g:real^3->real^3`; `u:real^3->bool`] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC OPEN_OPEN_IN_TRANS THEN
    ASM_SIMP_TAC[OPEN_INTER; INTER_SUBSET];
    ALL_TAC] THEN
  ASM_SIMP_TAC[OPEN_INTER; IN_INTER] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC HOMEOMORPHISM_OF_SUBSETS THEN
    MAP_EVERY EXISTS_TAC [`u:real^3->bool`; `IMAGE (f:real^3->real^3) u`] THEN
    ASM_REWRITE_TAC[INTER_SUBSET] THEN MATCH_MP_TAC IMAGE_SUBSET THEN SET_TAC[];
    MATCH_MP_TAC PL_MAP_ON_SUBSET THEN EXISTS_TAC `u:real^3->bool` THEN
    ASM_SIMP_TAC[INTER_SUBSET; LOCALLY_POLYHEDRAL_OPEN; OPEN_INTER];
    MATCH_MP_TAC PL_MAP_ON_SUBSET THEN EXISTS_TAC `IMAGE (f:real^3->real^3) u` THEN
    ASM_SIMP_TAC[LOCALLY_POLYHEDRAL_OPEN] THEN MATCH_MP_TAC IMAGE_SUBSET THEN SET_TAC[];
    SUBGOAL_THEN `s INTER u INTER w:real^3->bool = (s INTER u) INTER (u INTER w)`
    SUBST1_TAC THENL [SET_TAC[]; ALL_TAC] THEN
    W(MP_TAC o PART_MATCH (lhs o rand) (ASSUME
      `!a b:real^3->bool. a SUBSET u /\ b SUBSET u
                ==> IMAGE (f:real^3->real^3) (a INTER b) = IMAGE f a INTER IMAGE f b`) o
      lhand o snd) THEN
    ANTS_TAC THENL [SET_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `IMAGE (f:real^3->real^3) (u INTER w) SUBSET IMAGE f u` MP_TAC THENL
     [MATCH_MP_TAC IMAGE_SUBSET THEN SET_TAC[]; SET_TAC[]];
    SUBGOAL_THEN `t' INTER u INTER w:real^3->bool = (t INTER u) INTER (u INTER w)`
    SUBST1_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    W(MP_TAC o PART_MATCH (lhs o rand) (ASSUME
      `!a b:real^3->bool. a SUBSET u /\ b SUBSET u
                ==> IMAGE (f:real^3->real^3) (a INTER b) = IMAGE f a INTER IMAGE f b`) o
      lhand o snd) THEN
    ANTS_TAC THENL [SET_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `IMAGE (f:real^3->real^3) (u INTER w) SUBSET IMAGE f u` MP_TAC THENL
     [MATCH_MP_TAC IMAGE_SUBSET THEN SET_TAC[]; SET_TAC[]]]);;

let MOI_S3CN_BALL_MINUS_COMPACT = prove
 (`!c:real^2->bool.
     compact c /\ c SUBSET ball(vec 0,&1) /\ connected ((:real^2) DIFF c)
     ==> connected (ball(vec 0,&1) DIFF c)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `c:real^2->bool = {}` THEN
  ASM_REWRITE_TAC[DIFF_EMPTY; CONNECTED_BALL] THEN
  SUBGOAL_THEN `?r. r < &1 /\ !z:real^2. z IN c ==> norm z <= r` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `IMAGE (norm:real^2->real) c` COMPACT_ATTAINS_SUP) THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[IMAGE_EQ_EMPTY; GSYM IMAGE_o] THEN
      MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
      ASM_REWRITE_TAC[CONTINUOUS_ON_LIFT_NORM];
      ALL_TAC] THEN
    REWRITE_TAC[FORALL_IN_IMAGE; EXISTS_IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `z0:real^2` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `norm(z0:real^2)` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(c:real^2->bool) SUBSET ball(vec 0,&1)` THEN
    REWRITE_TAC[SUBSET; IN_BALL_0] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `r' = (r + &1) / &2` THEN
  SUBGOAL_THEN `r < r' /\ r' < &1 /\ &0 < r'` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "r'" THEN
    SUBGOAL_THEN `?z:real^2. z IN c` (X_CHOOSE_TAC `z1:real^2`) THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= r` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `norm(z1:real^2)` THEN
      ASM_SIMP_TAC[NORM_POS_LE];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `rho = closest_point (cball(vec 0:real^2,r'))` THEN
  SUBGOAL_THEN `!z:real^2. ~(z IN c) ==> ~(rho z IN c) /\ rho z IN ball(vec 0,&1)`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN
    ASM_CASES_TAC `(z:real^2) IN cball(vec 0,r')` THENL
     [EXPAND_TAC "rho" THEN ASM_SIMP_TAC[CLOSEST_POINT_SELF] THEN
      UNDISCH_TAC `(z:real^2) IN cball(vec 0,r')` THEN
      REWRITE_TAC[IN_CBALL_0; IN_BALL_0] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`cball(vec 0:real^2,r')`; `z:real^2`] CLOSEST_POINT_IN_FRONTIER) THEN
    ASM_REWRITE_TAC[CLOSED_CBALL; CBALL_EQ_EMPTY; INTERIOR_CBALL; FRONTIER_CBALL] THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      UNDISCH_TAC `~((z:real^2) IN cball(vec 0,r'))` THEN
      REWRITE_TAC[IN_CBALL_0; IN_BALL_0] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[IN_SPHERE_0; IN_BALL_0] THEN DISCH_TAC THEN
    CONJ_TAC THENL [DISCH_TAC; ASM_REAL_ARITH_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `(rho:real^2->real^2) z` o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `r:real`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `ball(vec 0:real^2,&1) DIFF c =
                IMAGE rho ((:real^2) DIFF c) UNION
                {x | r' <= norm(x - vec 0) /\ norm(x - vec 0) < &1}`
  SUBST1_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_DIFF; IN_UNION; IN_ELIM_THM; IN_IMAGE; IN_UNIV;
                  VECTOR_SUB_RZERO; IN_BALL_0] THEN
      X_GEN_TAC `z:real^2` THEN STRIP_TAC THEN
      ASM_CASES_TAC `r' <= norm(z:real^2)` THEN ASM_REWRITE_TAC[] THEN
      EXISTS_TAC `z:real^2` THEN ASM_REWRITE_TAC[] THEN
      EXPAND_TAC "rho" THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC CLOSEST_POINT_SELF THEN
      REWRITE_TAC[IN_CBALL_0] THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[UNION_SUBSET; SUBSET; FORALL_IN_IMAGE; IN_DIFF; IN_UNIV; IN_ELIM_THM;
                  VECTOR_SUB_RZERO] THEN
      CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      X_GEN_TAC `z:real^2` THEN STRIP_TAC THEN REWRITE_TAC[IN_BALL_0] THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `z:real^2` o check (fun th ->
        is_forall(concl th) && can (find_term ((=) `r:real`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC CONNECTED_UNION THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "rho" THEN MATCH_MP_TAC CONTINUOUS_ON_CLOSEST_POINT THEN
    REWRITE_TAC[CONVEX_CBALL; CLOSED_CBALL; CBALL_EQ_EMPTY] THEN ASM_REAL_ARITH_TAC;
    MP_TAC(ISPECL [`vec 0:real^2`; `r':real`; `&1`]
      (CONJUNCT1(CONJUNCT2(CONJUNCT2 CONNECTED_ANNULUS)))) THEN
    REWRITE_TAC[DIMINDEX_2; LE_REFL];
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_IMAGE; IN_ELIM_THM; IN_DIFF; IN_UNIV;
                VECTOR_SUB_RZERO] THEN
    EXISTS_TAC `r' % basis 1:real^2` THEN
    SUBGOAL_THEN `norm(r' % basis 1:real^2) = r'` ASSUME_TAC THENL
     [SIMP_TAC[NORM_MUL; NORM_BASIS; DIMINDEX_2; ARITH] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    EXISTS_TAC `r' % basis 1:real^2` THEN CONJ_TAC THENL
     [EXPAND_TAC "rho" THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC CLOSEST_POINT_SELF THEN
      ASM_REWRITE_TAC[IN_CBALL_0; REAL_LE_REFL];
      DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `r' % basis 1:real^2` o check (fun th ->
        is_forall(concl th) && can (find_term ((=) `r:real`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]]);;

let MOI_S3CN_HOMEO_IMAGE_DIFF = prove
 (`!(f:real^M->real^N) g s t d.
     homeomorphism (s,t) (f,g) /\ d SUBSET s
     ==> IMAGE g (t DIFF IMAGE f d) = s DIFF d`,
  REPEAT GEN_TAC THEN REWRITE_TAC[homeomorphism] THEN STRIP_TAC THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:real^M` THEN
  REWRITE_TAC[IN_IMAGE; IN_DIFF] THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    DISCH_TAC THEN UNDISCH_TAC `~(?x:real^M. y = (f:real^M->real^N) x /\ x IN d)` THEN
    REWRITE_TAC[] THEN EXISTS_TAC `(g:real^N->real^M) y` THEN ASM_SIMP_TAC[] THEN
    ASM SET_TAC[];
    STRIP_TAC THEN EXISTS_TAC `(f:real^M->real^N) x` THEN ASM_SIMP_TAC[] THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `z:real^M` STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC `~((x:real^M) IN d)` THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `x = (g:real^N->real^M) ((f:real^M->real^N) x) /\ z = g (f z)`
    (fun th -> ONCE_REWRITE_TAC[th]) THENL [ASM SET_TAC[]; ASM_REWRITE_TAC[]] THEN
    ASM SET_TAC[]]);;

let MOI_S3CN_CELL_MINUS_DISK = prove
 (`!(e:real^N->bool) j p d jd.
     pseudo_cell e j p /\ disk_with_boundary d jd /\ d SUBSET e DIFF j
     ==> connected (e DIFF d)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pseudo_cell; disk_with_boundary] THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `f1:real^2->real^N` (X_CHOOSE_THEN `g1:real^N->real^2`
      STRIP_ASSUME_TAC)) ASSUME_TAC)) THEN
  UNDISCH_TAC `(e DIFF j:real^N->bool) homeomorphic ball(vec 0:real^2,&1)` THEN
  REWRITE_TAC[homeomorphic] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^N->real^2` (X_CHOOSE_THEN `g:real^2->real^N`
    ASSUME_TAC)) THEN
  SUBGOAL_THEN `compact (d:real^N->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `homeomorphism (cball(vec 0:real^2,&1),d:real^N->bool) (f1,g1)` THEN
    REWRITE_TAC[homeomorphism] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> rhs(concl th) = `d:real^N->bool`)) THEN
    MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[COMPACT_CBALL];
    ALL_TAC] THEN
  SUBGOAL_THEN `homeomorphism (d:real^N->bool,IMAGE (f:real^N->real^2) d) (f,g)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HOMEOMORPHISM_OF_SUBSETS THEN
    MAP_EVERY EXISTS_TAC [`e DIFF j:real^N->bool`; `ball(vec 0:real^2,&1)`] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `homeomorphism (e DIFF j:real^N->bool,ball(vec 0:real^2,&1)) (f,g)` THEN
    REWRITE_TAC[homeomorphism] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `compact (IMAGE (f:real^N->real^2) d) /\
                IMAGE f d SUBSET ball(vec 0:real^2,&1)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[homeomorphism];
      UNDISCH_TAC `homeomorphism (e DIFF j:real^N->bool,ball(vec 0:real^2,&1)) (f,g)` THEN
      REWRITE_TAC[homeomorphism] THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `connected ((:real^2) DIFF IMAGE (f:real^N->real^2) d)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`IMAGE (f:real^N->real^2) d`; `cball(vec 0:real^2,&1)`]
      CONNECTED_COMPLEMENT_HOMEOMORPHIC_CONVEX_COMPACT) THEN
    REWRITE_TAC[DIMINDEX_2; LE_REFL; CONVEX_CBALL; COMPACT_CBALL] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    MATCH_MP_TAC HOMEOMORPHIC_TRANS THEN EXISTS_TAC `d:real^N->bool` THEN CONJ_TAC THENL
     [ONCE_REWRITE_TAC[HOMEOMORPHIC_SYM] THEN REWRITE_TAC[homeomorphic] THEN
      ASM_MESON_TAC[];
      ONCE_REWRITE_TAC[HOMEOMORPHIC_SYM] THEN REWRITE_TAC[homeomorphic] THEN
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPEC `IMAGE (f:real^N->real^2) d` MOI_S3CN_BALL_MINUS_COMPACT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `connected ((e DIFF j) DIFF d:real^N->bool)` ASSUME_TAC THENL
   [SUBGOAL_THEN `(e DIFF j) DIFF d =
                  IMAGE (g:real^2->real^N) (ball(vec 0,&1) DIFF IMAGE f d)` SUBST1_TAC THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOI_S3CN_HOMEO_IMAGE_DIFF THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `ball(vec 0:real^2,&1)` THEN
    CONJ_TAC THENL [ASM_MESON_TAC[homeomorphism]; SET_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC CONNECTED_INTERMEDIATE_CLOSURE THEN
  EXISTS_TAC `(e DIFF j) DIFF d:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_TRANS THEN
  EXISTS_TAC `((:real^N) DIFF d) INTER closure (e DIFF j:real^N->bool)` THEN
  CONJ_TAC THENL
   [ASM_REWRITE_TAC[] THEN SET_TAC[];
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `closure (((:real^N) DIFF d) INTER (e DIFF j:real^N->bool))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_INTER_CLOSURE_SUBSET THEN
      ASM_SIMP_TAC[GSYM closed; COMPACT_IMP_CLOSED];
      MATCH_MP_TAC SUBSET_CLOSURE THEN SET_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* Part 2: Lemma 5 tools.  MOI_S30_BOUNDS with its inputs discharged         *)
(* (MOI_S3CN_BOUNDS); separation by a compact set puts the bounded side     *)
(* inside and the unbounded side outside (MOI_S3CN_SEP_INSIDE); a pseudo-   *)
(* cell whose centre is inside the separating component B and whose rim is  *)
(* outside keeps its trace and its disk (MOI_S3CN_TRACE_KEEP).              *)
(* ------------------------------------------------------------------------- *)

let MOI_S3CN_BOUNDS = prove
 (`MOISE_266_STATEMENT
   ==> !m:(real^3->bool)->bool.
         FINITE m /\ combinatorial_manifold 2 m /\ connected (UNIONS m) /\
         ~(UNIONS m = {})
         ==> ?x:(real^3->bool)->bool.
               FINITE x /\ combinatorial_manifold_with_boundary 3 x /\
               UNIONS x = UNIONS m UNION inside (UNIONS m) /\
               frontier (UNIONS x) = UNIONS m /\ complex_boundary x = UNIONS m /\
               complex_euler (boundary_complex x) = complex_euler m`,
  DISCH_TAC THEN MP_TAC BOUNDS THEN ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ACCEPT_TAC(MATCH_MP COMPACT_NBHD (INST_TYPE [`:3`,`:N`] DERIVED_NBHD_COMBINATORIAL));
    ACCEPT_TAC(MATCH_MP CUT (CONJ (ASSUME `MOISE_266_STATEMENT`) SPHERE_SPLIT));
    MATCH_ACCEPT_TAC COMPLEX_EULER_PL_INVARIANT]);;

let MOI_S3CN_SEP_INSIDE = prove
 (`!(b:real^3->bool) k1 k2.
     compact b /\ separates_in (:real^3) b k1 k2 /\
     connected k1 /\ ~(k1 = {}) /\ DISJOINT b k1 /\
     connected k2 /\ ~bounded k2 /\ DISJOINT b k2
     ==> k1 SUBSET inside b /\ k2 SUBSET outside b`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(k2:real^3->bool) SUBSET outside b` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; outside; IN_ELIM_THM] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    DISCH_TAC THEN UNDISCH_TAC `~bounded(k2:real^3->bool)` THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC BOUNDED_SUBSET THEN
    EXISTS_TAC `connected_component ((:real^3) DIFF b) y` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONNECTED_COMPONENT_MAXIMAL THEN ASM SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[INSIDE_OUTSIDE] THEN
  SUBGOAL_THEN `DISJOINT (k1:real^3->bool) (outside b)` MP_TAC THENL
   [ALL_TAC; ASM SET_TAC[]] THEN
  REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
  X_GEN_TAC `x1:real^3` THEN STRIP_TAC THEN
  UNDISCH_TAC `separates_in (:real^3) b k1 (k2:real^3->bool)` THEN
  REWRITE_TAC[separates_in; SUBTOPOLOGY_UNIV; GSYM OPEN_IN] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^3->bool` (X_CHOOSE_THEN `v:real^3->bool`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPEC `b:real^3->bool` CONNECTED_OUTSIDE) THEN
  ASM_SIMP_TAC[DIMINDEX_3; ARITH; COMPACT_IMP_BOUNDED] THEN
  REWRITE_TAC[connected] THEN
  MAP_EVERY EXISTS_TAC [`u:real^3->bool`; `v:real^3->bool`] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `b:real^3->bool` OUTSIDE_NO_OVERLAP) THEN
  SUBGOAL_THEN `?y:real^3. y IN k2` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[BOUNDED_EMPTY; MEMBER_NOT_EMPTY]; ALL_TAC] THEN
  ASM SET_TAC[]);;

let MOI_S3CN_CONNECTED_SIDE = prove
 (`!(b:real^N->bool) s.
     closed b /\ connected s /\ DISJOINT s b
     ==> s SUBSET inside b \/ s SUBSET outside b`,
  REPEAT STRIP_TAC THEN
  UNDISCH_TAC `connected (s:real^N->bool)` THEN REWRITE_TAC[connected] THEN
  REWRITE_TAC[NOT_EXISTS_THM] THEN
  DISCH_THEN(MP_TAC o SPECL [`inside b:real^N->bool`; `outside b:real^N->bool`]) THEN
  ASM_SIMP_TAC[OPEN_INSIDE; OPEN_OUTSIDE] THEN
  MP_TAC(ISPEC `b:real^N->bool` INSIDE_UNION_OUTSIDE) THEN
  MP_TAC(ISPEC `b:real^N->bool` INSIDE_INTER_OUTSIDE) THEN
  ASM SET_TAC[]);;

let MOI_S3CN_PL_SPHERE1_CONNECTED = prove
 (`!s:real^N->bool. pl_sphere 1 s ==> connected s /\ ~(s = {})`,
  GEN_TAC THEN REWRITE_TAC[pl_sphere; pl_homeomorphism] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
    (X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `convex (k:real^N->bool) /\ bounded k /\ aff_dim k = &2`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[SIMPLEX_IMP_CONVEX; SIMPLEX_IMP_POLYTOPE; POLYTOPE_IMP_BOUNDED;
                  AFF_DIM_SIMPLEX];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> rhs(concl th) = `s:real^N->bool`)) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONNECTED_SPHERE_GEN THEN ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
    REWRITE_TAC[IMAGE_EQ_EMPTY; RELATIVE_FRONTIER_EQ_EMPTY] THEN DISCH_TAC THEN
    MP_TAC(ISPEC `k:real^N->bool` AFFINE_BOUNDED_EQ_TRIVIAL) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    UNDISCH_TAC `aff_dim (k:real^N->bool) = &2` THEN
    ASM_REWRITE_TAC[AFF_DIM_EMPTY; AFF_DIM_SING] THEN INT_ARITH_TAC]);;

let MOI_S3CN_TRACE_KEEP = prove
 (`!(e:real^3->bool) j p d jd bdx b.
     pseudo_cell e j p /\ disk_with_boundary d jd /\ pl_sphere 1 jd /\
     jd SUBSET e /\ jd SUBSET bdx /\ e INTER bdx SUBSET jd /\ d SUBSET e DIFF j /\
     closed bdx /\ b IN components bdx /\ p IN d DIFF jd /\ p IN inside b /\
     j SUBSET outside b
     ==> jd SUBSET b /\ e INTER b = jd /\ e INTER (b UNION inside b) = d`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(b:real^3->bool) SUBSET bdx /\ closed b` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[IN_COMPONENTS_SUBSET; CLOSED_COMPONENTS]; ALL_TAC] THEN
  UNDISCH_TAC `pseudo_cell (e:real^3->bool) j p` THEN REWRITE_TAC[pseudo_cell] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `connected (e:real^3->bool)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> rhs(concl th) = `e:real^3->bool`)) THEN
    MATCH_MP_TAC CONNECTED_CLOSURE THEN
    FIRST_X_ASSUM((fun th -> REWRITE_TAC[MATCH_MP HOMEOMORPHIC_CONNECTEDNESS th]) o
      check (fun th -> can (find_term ((=) `ball(vec 0:real^2,&1)`)) (concl th))) THEN
    REWRITE_TAC[CONNECTED_BALL];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(j:real^3->bool = {})` ASSUME_TAC THENL
   [DISCH_TAC THEN
    UNDISCH_TAC `(j:real^3->bool) homeomorphic sphere(vec 0:real^2,&1)` THEN
    ASM_REWRITE_TAC[HOMEOMORPHIC_EMPTY; SPHERE_EQ_EMPTY] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(e INTER b:real^3->bool = {})` ASSUME_TAC THENL
   [DISCH_TAC THEN
    MP_TAC(ISPECL [`b:real^3->bool`; `e:real^3->bool`] MOI_S3CN_CONNECTED_SIDE) THEN
    ASM_REWRITE_TAC[DISJOINT] THEN ONCE_REWRITE_TAC[INTER_COMM] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `b:real^3->bool` INSIDE_INTER_OUTSIDE) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(jd:real^3->bool) SUBSET b` ASSUME_TAC THENL
   [MATCH_MP_TAC COMPONENTS_MAXIMAL THEN EXISTS_TAC `bdx:real^3->bool` THEN
    ASM_SIMP_TAC[MOI_S3CN_PL_SPHERE1_CONNECTED] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `e INTER b:real^3->bool = jd` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(jd:real^3->bool) SUBSET d` ASSUME_TAC THENL
   [UNDISCH_TAC `disk_with_boundary (d:real^3->bool) jd` THEN
    REWRITE_TAC[disk_with_boundary; homeomorphism] THEN
    MP_TAC(ISPECL [`vec 0:real^2`; `&1`] SPHERE_SUBSET_CBALL) THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `d DIFF jd SUBSET inside(b:real^3->bool)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`b:real^3->bool`; `d DIFF jd:real^3->bool`] MOI_S3CN_CONNECTED_SIDE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
      UNDISCH_TAC `disk_with_boundary (d:real^3->bool) jd` THEN
      REWRITE_TAC[disk_with_boundary] THEN
      DISCH_THEN(X_CHOOSE_THEN `f:real^2->real^3` (X_CHOOSE_THEN `g:real^3->real^2`
        STRIP_ASSUME_TAC)) THEN
      SUBGOAL_THEN `d DIFF jd = IMAGE (f:real^2->real^3) (ball(vec 0,&1))` SUBST1_TAC THENL
       [UNDISCH_TAC `homeomorphism (cball(vec 0:real^2,&1),d:real^3->bool) (f,g)` THEN
        ASM_REWRITE_TAC[homeomorphism] THEN
        REWRITE_TAC[GSYM CBALL_DIFF_SPHERE] THEN
        MP_TAC(ISPECL [`vec 0:real^2`; `&1`] SPHERE_SUBSET_CBALL) THEN SET_TAC[];
        ALL_TAC] THEN
      MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN REWRITE_TAC[CONNECTED_BALL] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `cball(vec 0:real^2,&1)` THEN
      REWRITE_TAC[BALL_SUBSET_CBALL] THEN ASM_MESON_TAC[homeomorphism];
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPEC `b:real^3->bool` INSIDE_INTER_OUTSIDE) THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `e DIFF d SUBSET outside(b:real^3->bool)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`b:real^3->bool`; `e DIFF d:real^3->bool`] MOI_S3CN_CONNECTED_SIDE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
      MATCH_MP_TAC MOI_S3CN_CELL_MINUS_DISK THEN
      MAP_EVERY EXISTS_TAC [`j:real^3->bool`; `p:real^3`; `jd:real^3->bool`] THEN
      ASM_REWRITE_TAC[pseudo_cell];
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPEC `b:real^3->bool` INSIDE_INTER_OUTSIDE) THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPEC `b:real^3->bool` INSIDE_INTER_OUTSIDE) THEN ASM SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Part 3: Lemma 5 (p.232).  The filled separating surface is               *)
(* connected (MOI_S3CN_INSIDE_UNION_CONNECTED, from 26.6 and the bounded    *)
(* complementary component).  S33_L5: 30.2 in R^3 on Bd X (finitely many    *)
(* components) separating K' from the complement of Int N' gives one       *)
(* component B; B lies between them (MOI_S3CN_SEP_INSIDE), is a closed     *)
(* combinatorial surface (BOUNDARY_COMPLEX_SURFACE), and MOI_S3CN_BOUNDS    *)
(* gives X' with |X'| = B UNION inside B and Bd X' = B.  The crossing        *)
(* condition is local (MOI_S3CN_CROSSING_LOCAL, B isolated among the        *)
(* components) and every trace and disk is kept (MOI_S3CN_TRACE_KEEP).      *)
(* ------------------------------------------------------------------------- *)

let MOI_S3CN_INSIDE_UNION_CONNECTED = prove
 (`!m:(real^3->bool)->bool.
     MOISE_266_STATEMENT /\ FINITE m /\ combinatorial_manifold 2 m /\
     connected (UNIONS m) /\ ~(UNIONS m = {})
     ==> connected (UNIONS m UNION inside (UNIONS m))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MOISE_266_STATEMENT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o SPEC `m:(real^3->bool)->bool`) ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `b:real^3->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`UNIONS m:real^3->bool`; `b:real^3->bool`] MOI_S3BD_INSIDE_COMPONENT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `UNIONS m UNION b:real^3->bool = closure b` SUBST1_TAC THENL
   [REWRITE_TAC[CLOSURE_UNION_FRONTIER] THEN ASM SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC CONNECTED_CLOSURE THEN MATCH_MP_TAC IN_COMPONENTS_CONNECTED THEN
  EXISTS_TAC `(:real^3) DIFF UNIONS m` THEN ASM_REWRITE_TAC[IN_INSERT]);;

let S33_L5 = prove
 (MOI_S33_L5,
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "302") (CONJUNCTS_THEN2 (LABEL_TAC "266")
    (LABEL_TAC "tf"))) THEN
  MAP_EVERY X_GEN_TAC [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
                       `h:real^3->real^3`; `e:(real^3->bool)->real^3->bool`;
                       `c:real^3->real^3->bool`; `x:(real^3->bool)->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "hd") (CONJUNCTS_THEN2 (LABEL_TAC "x2")
    (LABEL_TAC "tr"))) THEN
  SUBGOAL_THEN `moi_s33_tube t l (h:real^3->real^3)` (LABEL_TAC "tube") THENL
   [USE_THEN "hd" (MP_TAC o REWRITE_RULE[moi_s33_hd]) THEN SIMP_TAC[]; ALL_TAC] THEN
  USE_THEN "tf" (MP_TAC o SPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
                                 `h:real^3->real^3`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> MAP_EVERY (fun i -> ASSUME_TAC (el i (CONJUNCTS th))) [2;3;5;8;11]) THEN
  REMOVE_THEN "tf" (K ALL_TAC) THEN
  USE_THEN "x2" (STRIP_ASSUME_TAC o REWRITE_RULE[moi_s33_x2]) THEN
  SUBGOAL_THEN `UNIONS l SUBSET UNIONS (t:(real^3->bool)->bool) /\
                (h:real^3->real^3) continuous_on UNIONS t /\
                connected (UNIONS (l:(real^3->bool)->bool)) /\ ~(UNIONS l = {})`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "tube" (MP_TAC o REWRITE_RULE[moi_s33_tube; graph_in_complex;
                                          simplicial_subcomplex]) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUBSET_UNIONS THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[EMPTY_UNIONS] THEN DISCH_THEN(MP_TAC o SPEC `s:real^3->bool`) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      UNDISCH_TAC `aff_dim (s:real^3->bool) = &1` THEN
      ASM_REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `compact (IMAGE (h:real^3->real^3) (derived_nbhd t l))` ASSUME_TAC THENL
     [MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `UNIONS (t:(real^3->bool)->bool)` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
  SUBGOAL_THEN `~bounded ((:real^3) DIFF interior (IMAGE (h:real^3->real^3)
                                                  (derived_nbhd t l)))` ASSUME_TAC THENL
   [DISCH_TAC THEN MP_TAC(INST_TYPE [`:3`,`:N`] NOT_BOUNDED_UNIV) THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC BOUNDED_SUBSET THEN
    EXISTS_TAC `((:real^3) DIFF interior (IMAGE (h:real^3->real^3) (derived_nbhd t l)))
                UNION IMAGE h (derived_nbhd t l)` THEN
    ASM_SIMP_TAC[BOUNDED_UNION; COMPACT_IMP_BOUNDED] THEN
    MP_TAC(ISPEC `IMAGE (h:real^3->real^3) (derived_nbhd t l)` INTERIOR_SUBSET) THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `closed ((:real^3) DIFF interior (IMAGE (h:real^3->real^3) (derived_nbhd t l))) /\
                connected ((:real^3) DIFF interior (IMAGE (h:real^3->real^3) (derived_nbhd t l))) /\
                ~((:real^3) DIFF interior (IMAGE (h:real^3->real^3) (derived_nbhd t l)) = {})`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CLOSED_DIFF THEN REWRITE_TAC[CLOSED_UNIV; OPEN_INTERIOR];
      REWRITE_TAC[GSYM CLOSURE_COMPLEMENT] THEN MATCH_MP_TAC CONNECTED_CLOSURE THEN
      ASM_REWRITE_TAC[];
      DISCH_TAC THEN UNDISCH_TAC `~bounded ((:real^3) DIFF interior (IMAGE (h:real^3->real^3)
                                                  (derived_nbhd t l)))` THEN
      ASM_REWRITE_TAC[BOUNDED_EMPTY]];
    ALL_TAC] THEN
  SUBGOAL_THEN `connected (IMAGE (h:real^3->real^3) (UNIONS l)) /\
                ~(IMAGE (h:real^3->real^3) (UNIONS l) = {})` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[IMAGE_EQ_EMPTY] THEN
    MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `UNIONS (t:(real^3->bool)->bool)` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s:real^3->bool. s IN x ==> compact s /\ convex s` ASSUME_TAC THENL
   [UNDISCH_TAC `combinatorial_manifold_with_boundary 3 (x:(real^3->bool)->bool)` THEN
    REWRITE_TAC[combinatorial_manifold_with_boundary; lf_simplicial_complex] THEN
    MESON_TAC[SIMPLEX_IMP_COMPACT; SIMPLEX_IMP_CONVEX];
    ALL_TAC] THEN
  SUBGOAL_THEN `compact (UNIONS (x:(real^3->bool)->bool)) /\
                FINITE (components (frontier (UNIONS (x:(real^3->bool)->bool))))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_UNIONS THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    MP_TAC(CONJUNCT2(MATCH_MP COMPLEX_BOUNDARY_FRONTIER_3
      (ASSUME `combinatorial_manifold_with_boundary 3 (x:(real^3->bool)->bool)`))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[complex_boundary] THEN MATCH_MP_TAC MOI_FBC_FINITE_COMPONENTS THEN
    ASM_SIMP_TAC[FINITE_RESTRICT; IN_ELIM_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN `closed (UNIONS (x:(real^3->bool)->bool)) /\
                frontier (UNIONS (x:(real^3->bool)->bool)) SUBSET UNIONS x /\
                interior (UNIONS (x:(real^3->bool)->bool)) SUBSET UNIONS x` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[COMPACT_IMP_CLOSED; FRONTIER_SUBSET_CLOSED; INTERIOR_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `DISJOINT (IMAGE (h:real^3->real^3) (UNIONS l))
                  ((:real^3) DIFF interior (IMAGE (h:real^3->real^3) (derived_nbhd t l))) /\
                DISJOINT (frontier (UNIONS (x:(real^3->bool)->bool)))
                  (IMAGE (h:real^3->real^3) (UNIONS l)) /\
                DISJOINT (frontier (UNIONS (x:(real^3->bool)->bool)))
                  ((:real^3) DIFF interior (IMAGE (h:real^3->real^3) (derived_nbhd t l)))`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY (fun t -> MP_TAC(ASSUME t))
     [`IMAGE (h:real^3->real^3) (UNIONS l) SUBSET interior (IMAGE h (derived_nbhd t l))`;
      `IMAGE (h:real^3->real^3) (UNIONS l) SUBSET interior (UNIONS x)`;
      `UNIONS x SUBSET interior (IMAGE (h:real^3->real^3) (derived_nbhd t l))`;
      `frontier (UNIONS (x:(real^3->bool)->bool)) SUBSET UNIONS x`] THEN
    REWRITE_TAC[frontier] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `separates_in (:real^3) (frontier (UNIONS (x:(real^3->bool)->bool)))
                  (IMAGE (h:real^3->real^3) (UNIONS l))
                  ((:real^3) DIFF interior (IMAGE (h:real^3->real^3) (derived_nbhd t l)))`
  ASSUME_TAC THENL
   [REWRITE_TAC[separates_in; SUBTOPOLOGY_UNIV; GSYM OPEN_IN] THEN
    MAP_EVERY EXISTS_TAC [`interior (UNIONS (x:(real^3->bool)->bool))`;
                          `(:real^3) DIFF UNIONS x`] THEN
    ASM_SIMP_TAC[OPEN_INTERIOR; OPEN_DIFF; OPEN_UNIV; frontier; CLOSURE_CLOSED] THEN
    MAP_EVERY (fun t -> MP_TAC(ASSUME t))
     [`UNIONS x SUBSET interior (IMAGE (h:real^3->real^3) (derived_nbhd t l))`;
      `interior (UNIONS (x:(real^3->bool)->bool)) SUBSET UNIONS x`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  USE_THEN "302" (MP_TAC o SPECL [`(:real^3)`; `frontier (UNIONS (x:(real^3->bool)->bool))`;
     `IMAGE (h:real^3->real^3) (UNIONS l)`;
     `(:real^3) DIFF interior (IMAGE (h:real^3->real^3) (derived_nbhd t l))`] o
   REWRITE_RULE[MOISE_302_STATEMENT]) THEN
  ASM_SIMP_TAC[SUBTOPOLOGY_UNIV; GSYM CLOSED_IN; OPEN_UNIV; CONVEX_IMP_SIMPLY_CONNECTED;
               CONVEX_UNIV; FRONTIER_CLOSED; COMPACT_IMP_CLOSED] THEN
  DISCH_THEN(X_CHOOSE_THEN `b:real^3->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(b:real^3->bool) SUBSET frontier (UNIONS (x:(real^3->bool)->bool)) /\
                compact b /\ connected b /\ ~(b = {})` STRIP_ASSUME_TAC THENL
   [MP_TAC(ASSUME `(b:real^3->bool) IN components (frontier (UNIONS (x:(real^3->bool)->bool)))`) THEN
    MP_TAC(ASSUME `compact (UNIONS (x:(real^3->bool)->bool))`) THEN
    MESON_TAC[IN_COMPONENTS_SUBSET; COMPACT_COMPONENTS; IN_COMPONENTS_CONNECTED;
              IN_COMPONENTS_NONEMPTY; COMPACT_FRONTIER];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`b:real^3->bool`; `IMAGE (h:real^3->real^3) (UNIONS l)`;
                 `(:real^3) DIFF interior (IMAGE (h:real^3->real^3) (derived_nbhd t l))`]
                MOI_S3CN_SEP_INSIDE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
    MATCH_MP_TAC(SET_RULE `!b f k:real^3->bool. b SUBSET f /\ DISJOINT f k ==> DISJOINT b k`) THEN
    EXISTS_TAC `frontier (UNIONS (x:(real^3->bool)->bool))` THEN ASM_REWRITE_TAC[];
    STRIP_TAC] THEN
  MP_TAC(CONJUNCT2(CONJUNCT2(CONJUNCT2(CONJUNCT2(MATCH_MP BOUNDARY_COMPLEX_SURFACE
      (ASSUME `combinatorial_manifold_with_boundary 3 (x:(real^3->bool)->bool)`)))))) THEN
  DISCH_THEN(MP_TAC o SPEC `b:real^3->bool`) THEN
  ANTS_TAC THENL
   [MP_TAC(CONJUNCT2(MATCH_MP COMPLEX_BOUNDARY_FRONTIER_3
      (ASSUME `combinatorial_manifold_with_boundary 3 (x:(real^3->bool)->bool)`))) THEN
    ASM_SIMP_TAC[];
    STRIP_TAC] THEN
  MP_TAC(SPEC `{s | s IN x /\ s SUBSET (b:real^3->bool)}`
     (MATCH_MP MOI_S3CN_BOUNDS (ASSUME `MOISE_266_STATEMENT`))) THEN
  ASM_SIMP_TAC[FINITE_RESTRICT] THEN
  DISCH_THEN(X_CHOOSE_THEN `x':(real^3->bool)->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPEC `{s | s IN x /\ s SUBSET (b:real^3->bool)}` MOI_S3CN_INSIDE_UNION_CONNECTED) THEN
  ASM_SIMP_TAC[FINITE_RESTRICT] THEN DISCH_TAC THEN
  SUBGOAL_THEN `IMAGE (h:real^3->real^3) (UNIONS l) SUBSET interior (b UNION inside b) /\
                b UNION inside b SUBSET interior (IMAGE (h:real^3->real^3) (derived_nbhd t l))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `inside (b:real^3->bool)` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC INTERIOR_MAXIMAL THEN
      ASM_SIMP_TAC[OPEN_INSIDE; COMPACT_IMP_CLOSED] THEN SET_TAC[];
      MP_TAC(ISPEC `b:real^3->bool` INSIDE_INTER_OUTSIDE) THEN
      MAP_EVERY (fun t -> MP_TAC(ASSUME t))
       [`(:real^3) DIFF interior (IMAGE (h:real^3->real^3) (derived_nbhd t l)) SUBSET outside b`;
        `(b:real^3->bool) SUBSET frontier (UNIONS (x:(real^3->bool)->bool))`;
        `frontier (UNIONS (x:(real^3->bool)->bool)) SUBSET UNIONS x`;
        `UNIONS x SUBSET interior (IMAGE (h:real^3->real^3) (derived_nbhd t l))`] THEN
      SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `?w:real^3->bool. open w /\ b SUBSET w /\
                  frontier (UNIONS (x:(real^3->bool)->bool)) INTER w = b INTER w`
  STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `(:real^3) DIFF UNIONS (components (frontier (UNIONS (x:(real^3->bool)->bool)))
                                       DELETE (b:real^3->bool))` THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[GSYM closed] THEN MATCH_MP_TAC CLOSED_UNIONS THEN
      ASM_SIMP_TAC[FINITE_DELETE; IN_DELETE] THEN MESON_TAC[CLOSED_COMPONENTS; FRONTIER_CLOSED];
      REWRITE_TAC[SUBSET; IN_DIFF; IN_UNIV; IN_UNIONS; IN_DELETE] THEN
      X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
      DISCH_THEN(X_CHOOSE_THEN `c':real^3->bool` STRIP_ASSUME_TAC) THEN
      MP_TAC(ISPECL [`frontier (UNIONS (x:(real^3->bool)->bool))`; `b:real^3->bool`;
                     `c':real^3->bool`] COMPONENTS_NONOVERLAP) THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(ASSUME `~(c' = (b:real^3->bool))`) THEN MP_TAC(ASSUME `(z:real^3) IN b`) THEN
      MP_TAC(ASSUME `(z:real^3) IN c'`) THEN SET_TAC[];
      MATCH_MP_TAC(SET_RULE
       `!t j k:real^3->bool. t SUBSET j UNION k /\ j SUBSET t
                             ==> t INTER ((:real^3) DIFF k) = j INTER ((:real^3) DIFF k)`) THEN
      CONJ_TAC THENL
       [MP_TAC(ISPEC `frontier (UNIONS (x:(real^3->bool)->bool))` UNIONS_COMPONENTS) THEN
        SET_TAC[];
        ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!u v y. ~(u = v) /\ segment[u,v] IN l /\
                       y IN e(segment[u,v]) INTER (b:real^3->bool)
                       ==> pl_crossing_at (e(segment[u,v]) DIFF moi_s33_rim t l h u v) b y`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`u:real^3`; `v:real^3`; `y:real^3`] THEN
    REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN
    MATCH_MP_TAC MOI_S3CN_CROSSING_LOCAL THEN
    MAP_EVERY EXISTS_TAC [`frontier (UNIONS (x:(real^3->bool)->bool))`; `w:real^3->bool`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [USE_THEN "x2" (MATCH_MP_TAC o last o CONJUNCTS o REWRITE_RULE[moi_s33_x2]) THEN
      ASM_REWRITE_TAC[IN_INTER] THEN
      MP_TAC(ASSUME `(b:real^3->bool) SUBSET frontier (UNIONS (x:(real^3->bool)->bool))`) THEN
      REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MP_TAC(ASSUME `(b:real^3->bool) SUBSET w`) THEN
      REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!u v:real^3. ~(u = v) /\ segment[u,v] IN l
                     ==> pl_sphere 1 ((e:(real^3->bool)->real^3->bool)(segment[u,v]) INTER
                                      (b:real^3->bool)) /\
                         disk_with_boundary (e(segment[u,v]) INTER (b UNION inside b))
                                            (e(segment[u,v]) INTER b)`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`u:real^3`; `v:real^3`] THEN STRIP_TAC THEN
    USE_THEN "hd" (MP_TAC o SPECL [`u:real^3`; `v:real^3`] o CONJUNCT1 o CONJUNCT2 o
                   REWRITE_RULE[moi_s33_hd]) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    USE_THEN "tr" (MP_TAC o SPECL [`u:real^3`; `v:real^3`] o REWRITE_RULE[moi_s33_traces]) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `(e:(real^3->bool)->real^3->bool)(segment[u,v]) INTER UNIONS x SUBSET
        e(segment[u,v]) DIFF moi_s33_rim t l h u v /\
      moi_s33_rim t l h u v SUBSET outside b`
    STRIP_ASSUME_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq (concl th) &&
        rhs (concl th) = `moi_s33_rim (t:(real^3->bool)->bool) l (h:real^3->real^3)
                                      (u:real^3) (v:real^3)`)) THEN
      MAP_EVERY (fun t -> MP_TAC(ASSUME t))
       [`UNIONS x SUBSET interior (IMAGE (h:real^3->real^3) (derived_nbhd t l))`;
        `(:real^3) DIFF interior (IMAGE (h:real^3->real^3) (derived_nbhd t l)) SUBSET
         outside b`] THEN
      REWRITE_TAC[frontier] THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `(h:real^3->real^3)(midpoint(u,v)) IN
        ((e:(real^3->bool)->real^3->bool)(segment[u,v]) INTER UNIONS x) DIFF
        (e(segment[u,v]) INTER frontier (UNIONS x)) /\
      (h:real^3->real^3)(midpoint(u,v)) IN inside b`
    STRIP_ASSUME_TAC THENL
     [MP_TAC(ASSUME `(e:(real^3->bool)->real^3->bool)(segment[u,v]) INTER
                     IMAGE (h:real^3->real^3) (UNIONS l) = {h(midpoint(u,v))}`) THEN
      MAP_EVERY (fun t -> MP_TAC(ASSUME t))
       [`IMAGE (h:real^3->real^3) (UNIONS l) SUBSET interior (UNIONS x)`;
        `interior (UNIONS (x:(real^3->bool)->bool)) SUBSET UNIONS x`;
        `IMAGE (h:real^3->real^3) (UNIONS l) SUBSET inside b`] THEN
      REWRITE_TAC[frontier] THEN SET_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`(e:(real^3->bool)->real^3->bool)(segment[u,v])`;
                   `moi_s33_rim t l h u v`; `(h:real^3->real^3)(midpoint(u,v))`;
                   `(e:(real^3->bool)->real^3->bool)(segment[u,v]) INTER UNIONS x`;
                   `(e:(real^3->bool)->real^3->bool)(segment[u,v]) INTER frontier (UNIONS x)`;
                   `frontier (UNIONS (x:(real^3->bool)->bool))`; `b:real^3->bool`]
                  MOI_S3CN_TRACE_KEEP) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[INTER_SUBSET; SUBSET_REFL; FRONTIER_CLOSED]; ALL_TAC] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT2 th]) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `x':(real^3->bool)->bool` THEN
  REWRITE_TAC[moi_s33_inv; moi_s33_x2; moi_s33_traces] THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Part 4: Lemma 6 tools (generic).  The pieces of a set cut by a           *)
(* closed set EE, given as closures of components (MOI_S3CN_PIECES); a half *)
(* plane chart from a PL chart in which a set is a closed half disk         *)
(* (MOI_S3CN_HALF_CHART, via MOI_S8CU_HALF_FROM_LOCAL); plane charts pass   *)
(* to a set agreeing with the first near the point (MOI_S3CN_R2_TRANSFER,   *)
(* the plane case of MOI_S3TM_CHART_TRANSFER of pc_moi_s30_tame, whose      *)
(* closure is much larger); triangles of a complex miss a union of edges    *)
(* and vertices in their interiors (MOI_S3CN_TRI_MISS) and lie in one piece *)
(* (MOI_S3CN_TRI_PIECE); in a chart where a pseudo-cell is the plane z1 = 0 *)
(* the two half balls lie in the two adjacent pieces (MOI_S3CN_TWO_SIDES), *)
(* and a piece meets the plane z2 = 0 of the surface in a half disk         *)
(* (MOI_S3CN_CHART_PULL, MOI_S3CN_SIDE_TRACE); a triangulation of Bd X in  *)
(* which finitely many PL curves with line charts are unions of edges and   *)
(* vertices (MOI_S3CN_TRIANG: SIMPLICIAL_COMPLEX_REFINE_POLYTOPES on the    *)
(* boundary complex, cm 2 by SURF_LOCAL).                                   *)
(* ------------------------------------------------------------------------- *)

let MOI_S3CN_PIECES = prove
 (`!(V:A->bool) (N:real^N->bool) EE (c:A->real^N->bool) (p:A->real^N).
     FINITE V /\ closed EE /\
     (!v. v IN V ==> c v = closure (connected_component (N DIFF EE) (p v))) /\
     UNIONS {c v | v IN V} = N /\
     (!v w. v IN V /\ w IN V /\ ~(v = w) ==> c v INTER c w SUBSET EE)
     ==> (!v w. v IN V /\ w IN V /\ ~(v = w)
                ==> connected_component (N DIFF EE) (p v) INTER c w = {}) /\
         (!z. z IN N DIFF EE
              ==> ?v. v IN V /\ z IN connected_component (N DIFF EE) (p v)) /\
         (!v z. v IN V /\ z IN N DIFF EE /\ z IN c v
                ==> z IN connected_component (N DIFF EE) (p v)) /\
         (!v. v IN V ==> open (connected_component (N DIFF EE) (p v) INTER interior N))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "cdef") (CONJUNCTS_THEN2 (LABEL_TAC "cov")
      (LABEL_TAC "int"))))) THEN
  SUBGOAL_THEN `!v z. v IN V /\ z IN N DIFF EE /\ z IN (c:A->real^N->bool) v
                      ==> z IN connected_component (N DIFF EE) ((p:A->real^N) v)`
  (LABEL_TAC "in") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`N DIFF EE:real^N->bool`; `(p:A->real^N) v`]
                  CLOSED_IN_CONNECTED_COMPONENT) THEN
    REWRITE_TAC[CLOSED_IN_INTER_CLOSURE] THEN
    DISCH_THEN(fun th -> GEN_REWRITE_TAC RAND_CONV [GSYM th]) THEN
    REWRITE_TAC[IN_INTER] THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "cdef" (fun th -> REWRITE_TAC[GSYM(MATCH_MP th (ASSUME `(v:A) IN V`))]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!v w. v IN V /\ w IN V /\ ~(v = w)
                      ==> connected_component (N DIFF EE) ((p:A->real^N) v) INTER
                          (c:A->real^N->bool) w = {}`
  (LABEL_TAC "dis") THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `connected_component (N DIFF EE) ((p:A->real^N) v) SUBSET
                  (c:A->real^N->bool) v`
    MP_TAC THENL
     [USE_THEN "cdef" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `(v:A) IN V`)]) THEN
      REWRITE_TAC[CLOSURE_SUBSET];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`N DIFF EE:real^N->bool`; `(p:A->real^N) v`]
                  CONNECTED_COMPONENT_SUBSET) THEN
    USE_THEN "int" (MP_TAC o SPECL [`v:A`; `w:A`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z. z IN N DIFF EE
                    ==> ?v. v IN V /\ z IN connected_component (N DIFF EE) ((p:A->real^N) v)`
  (LABEL_TAC "ex") THENL
   [X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(z:real^N) IN UNIONS {(c:A->real^N->bool) v | v IN V}` MP_TAC THENL
     [USE_THEN "cov" SUBST1_TAC THEN UNDISCH_TAC `(z:real^N) IN N DIFF EE` THEN SET_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool`
      (CONJUNCTS_THEN2 (X_CHOOSE_THEN `v:A` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
    EXISTS_TAC `v:A` THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "in" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(z:real^N) IN s` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [USE_THEN "dis" ACCEPT_TAC; USE_THEN "ex" ACCEPT_TAC; USE_THEN "in" ACCEPT_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `v:A` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `connected_component (N DIFF EE) ((p:A->real^N) v) INTER interior N =
    (interior N DIFF EE) DIFF UNIONS {(c:A->real^N->bool) w | w IN V /\ ~(w = v)}`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `z:real^N` THEN
    REWRITE_TAC[IN_INTER; IN_DIFF; IN_UNIONS; IN_ELIM_THM] THEN EQ_TAC THENL
     [STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MP_TAC(ISPECL [`N DIFF EE:real^N->bool`; `(p:A->real^N) v`]
                      CONNECTED_COMPONENT_SUBSET) THEN
        UNDISCH_TAC `(z:real^N) IN connected_component (N DIFF EE) ((p:A->real^N) v)` THEN
        SET_TAC[];
        REWRITE_TAC[NOT_EXISTS_THM] THEN X_GEN_TAC `s:real^N->bool` THEN
        DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `w:A` STRIP_ASSUME_TAC) ASSUME_TAC) THEN
        USE_THEN "dis" (MP_TAC o SPECL [`v:A`; `w:A`]) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        UNDISCH_TAC `(z:real^N) IN connected_component (N DIFF EE) ((p:A->real^N) v)` THEN
        UNDISCH_TAC `(z:real^N) IN s` THEN ASM_REWRITE_TAC[] THEN SET_TAC[]];
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `(z:real^N) IN N DIFF EE` ASSUME_TAC THENL
       [MP_TAC(ISPEC `N:real^N->bool` INTERIOR_SUBSET) THEN
        UNDISCH_TAC `(z:real^N) IN interior N` THEN UNDISCH_TAC `~((z:real^N) IN EE)` THEN
        SET_TAC[];
        ALL_TAC] THEN
      USE_THEN "ex" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(z:real^N) IN N DIFF EE`))) THEN
      DISCH_THEN(X_CHOOSE_THEN `u:A` STRIP_ASSUME_TAC) THEN
      ASM_CASES_TAC `u:A = v` THENL
       [FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o check (fun th -> is_neg (concl th) &&
        is_exists (dest_neg (concl th)))) THEN
      MATCH_MP_TAC(TAUT `p ==> ~p ==> q`) THEN
      EXISTS_TAC `(c:A->real^N->bool) u` THEN CONJ_TAC THENL
       [EXISTS_TAC `u:A` THEN ASM_REWRITE_TAC[];
        USE_THEN "cdef" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `(u:A) IN V`)]) THEN
        MATCH_MP_TAC(SET_RULE `!s t. s SUBSET t /\ (z:real^N) IN s ==> z IN t`) THEN
        EXISTS_TAC `connected_component (N DIFF EE) ((p:A->real^N) u)` THEN
        ASM_REWRITE_TAC[CLOSURE_SUBSET]]];
    ALL_TAC] THEN
  MATCH_MP_TAC OPEN_DIFF THEN CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_DIFF THEN ASM_REWRITE_TAC[OPEN_INTERIOR]; ALL_TAC] THEN
  MATCH_MP_TAC CLOSED_UNIONS THEN CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `IMAGE (c:A->real^N->bool) V` THEN
    ASM_SIMP_TAC[FINITE_IMAGE] THEN SET_TAC[];
    REWRITE_TAC[FORALL_IN_GSPEC] THEN X_GEN_TAC `w:A` THEN STRIP_TAC THEN
    USE_THEN "cdef" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `(w:A) IN V`)]) THEN
    REWRITE_TAC[CLOSED_CLOSURE]]);;

let MOI_S3CN_HALF_CHART = prove
 (`!(A:real^3->bool) u (f:real^3->real^3) g y r sg.
     open u /\ homeomorphism (u,IMAGE f u) (f,g) /\ y IN u /\ f y = vec 0 /\
     &0 < r /\ ball(vec 0,r) SUBSET IMAGE f u /\ sg * sg = &1 /\
     A INTER IMAGE g (ball(vec 0,r)) =
       IMAGE g {z | z IN ball(vec 0,r) /\ z$2 = &0 /\ &0 <= sg * z$1}
     ==> moi_s28_locally_half A y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  ABBREV_TAC `D = {z:real^3 | z IN ball(vec 0,r) /\ z$2 = &0 /\ &0 <= sg * z$1}` THEN
  SUBGOAL_THEN `(D:real^3->bool) SUBSET IMAGE (f:real^3->real^3) u` ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN UNDISCH_TAC `ball(vec 0:real^3,r) SUBSET IMAGE (f:real^3->real^3) u` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `open (IMAGE (g:real^3->real^3) (ball(vec 0,r)))` ASSUME_TAC THENL
   [MATCH_MP_TAC OPEN_IN_OPEN_TRANS THEN EXISTS_TAC `u:real^3->bool` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HOMEOMORPHISM_IMP_OPEN_MAP THEN
    MAP_EVERY EXISTS_TAC [`f:real^3->real^3`; `IMAGE (f:real^3->real^3) u`] THEN
    CONJ_TAC THENL [ONCE_REWRITE_TAC[HOMEOMORPHISM_SYM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC OPEN_SUBSET THEN ASM_REWRITE_TAC[OPEN_BALL];
    ALL_TAC] THEN
  ABBREV_TAC `pr = \z:real^3. vector[z$3; sg * z$1]:real^2` THEN
  ABBREV_TAC `pr' = \w:real^2. vector[sg * w$2; &0; w$1]:real^3` THEN
  SUBGOAL_THEN `(!z:real^3. z$2 = &0 ==> norm((pr:real^3->real^2) z) = norm z) /\
                (!w:real^2. norm((pr':real^2->real^3) w) = norm w) /\
                (!z:real^3. z$2 = &0 ==> pr' ((pr:real^3->real^2) z) = z) /\
                (!w:real^2. pr ((pr':real^2->real^3) w) = w) /\
                (!z:real^3. ((pr:real^3->real^2) z)$2 = sg * z$1) /\
                (!w:real^2. ((pr':real^2->real^3) w)$2 = &0 /\
                            sg * (pr' w)$1 = w$2)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["pr"; "pr'"] THEN
    REWRITE_TAC[NORM_EQ; DOT_2; DOT_3; VECTOR_2; VECTOR_3; CART_EQ; DIMINDEX_2;
                DIMINDEX_3; FORALL_2; FORALL_3] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `sg * sg = &1` THEN CONV_TAC REAL_RING;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `homeomorphism ((D:real^3->bool),{z:real^2 | &0 <= z$2} INTER ball(vec 0,r))
                  ((pr:real^3->real^2),(pr':real^2->real^3))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S8TA_HOMEO_INV THEN
    SUBGOAL_THEN `linear (pr:real^3->real^2) /\ linear (pr':real^2->real^3)`
    STRIP_ASSUME_TAC THENL
     [MAP_EVERY EXPAND_TAC ["pr"; "pr'"] THEN
      REWRITE_TAC[linear; CART_EQ; DIMINDEX_2; DIMINDEX_3; FORALL_2; FORALL_3; VECTOR_2;
                  VECTOR_3; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[LINEAR_CONTINUOUS_ON] THEN EXPAND_TAC "D" THEN
    REWRITE_TAC[IN_ELIM_THM; IN_INTER; IN_BALL_0] THEN
    CONJ_TAC THEN GEN_TAC THEN STRIP_TAC THEN ASM_SIMP_TAC[] THEN
    ASM_REWRITE_TAC[REAL_MUL_ASSOC; REAL_MUL_LID];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (g:real^3->real^3) D SUBSET u /\
                IMAGE (f:real^3->real^3) (IMAGE g D) = D`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `(D:real^3->bool) SUBSET IMAGE (f:real^3->real^3) u` THEN
      UNDISCH_TAC `IMAGE (g:real^3->real^3) (IMAGE (f:real^3->real^3) u) = u` THEN SET_TAC[];
      REWRITE_TAC[GSYM IMAGE_o] THEN MATCH_MP_TAC EQ_TRANS THEN
      EXISTS_TAC `IMAGE (\x:real^3. x) D` THEN CONJ_TAC THENL
       [MATCH_MP_TAC IMAGE_EQ THEN REWRITE_TAC[o_THM] THEN
        UNDISCH_TAC `(D:real^3->bool) SUBSET IMAGE (f:real^3->real^3) u` THEN ASM SET_TAC[];
        REWRITE_TAC[IMAGE_ID]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `homeomorphism (IMAGE (g:real^3->real^3) D,
                               {z:real^2 | &0 <= z$2} INTER ball(vec 0,r))
                              ((pr:real^3->real^2) o (f:real^3->real^3),
                               (g:real^3->real^3) o (pr':real^2->real^3))`
  (LABEL_TAC "hc") THENL
   [MATCH_MP_TAC HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `D:real^3->bool` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HOMEOMORPHISM_OF_SUBSETS THEN
    MAP_EVERY EXISTS_TAC [`u:real^3->bool`; `IMAGE (f:real^3->real^3) u`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_S8CU_HALF_FROM_LOCAL THEN
  MAP_EVERY EXISTS_TAC [`IMAGE (g:real^3->real^3) D`;
                        `(pr:real^3->real^2) o (f:real^3->real^3)`;
                        `(g:real^3->real^3) o (pr':real^2->real^3)`] THEN
  USE_THEN "hc" (fun th -> REWRITE_TAC[th; CONJUNCT1(CONJUNCT2(GEN_REWRITE_RULE I
    [homeomorphism] th))]) THEN
  REPEAT CONJ_TAC THENL
   [FIRST_X_ASSUM((fun th -> REWRITE_TAC[GSYM th]) o check (fun th -> is_eq(concl th) &&
      rand(concl th) = `IMAGE (g:real^3->real^3) D`)) THEN
    MATCH_MP_TAC OPEN_IN_OPEN_INTER THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `vec 0:real^3` THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `(f:real^3->real^3) y = vec 0`)) THEN
      CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `{z:real^3 | z IN ball(vec 0,r) /\ z$2 = &0 /\ &0 <= sg * z$1} = D` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      REWRITE_TAC[IN_ELIM_THM; CENTRE_IN_BALL; VEC_COMPONENT; REAL_MUL_RZERO; REAL_LE_REFL] THEN
      ASM_REWRITE_TAC[]];
    MATCH_MP_TAC OPEN_IN_OPEN_INTER THEN REWRITE_TAC[OPEN_BALL];
    REWRITE_TAC[o_THM] THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "pr" THEN
    REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2; VEC_COMPONENT] THEN
    REAL_ARITH_TAC]);;

let MOI_S3CN_R2_TRANSFER = prove
 (`!(X:real^N->bool) Y W y.
     open_in (subtopology euclidean X) W /\ open_in (subtopology euclidean Y) W /\
     y IN W /\ moi_s28_locally_r2 X y
     ==> moi_s28_locally_r2 Y y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s28_locally_r2] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `u:real^N->bool` STRIP_ASSUME_TAC)))) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `h:real^N->real^2` (X_CHOOSE_THEN `k:real^2->real^N`
    ASSUME_TAC) o REWRITE_RULE[homeomorphic]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  SUBGOAL_THEN `(u:real^N->bool) SUBSET X /\ (W:real^N->bool) SUBSET X`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[OPEN_IN_SUBSET; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY]; ALL_TAC] THEN
  SUBGOAL_THEN `open (IMAGE (h:real^N->real^2) (u INTER W))` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`h:real^N->real^2`; `k:real^2->real^N`; `u:real^N->bool`; `(:real^2)`;
                   `u INTER W:real^N->bool`] HOMEOMORPHISM_IMP_OPEN_MAP) THEN
    ASM_REWRITE_TAC[SUBTOPOLOGY_UNIV; GSYM OPEN_IN] THEN DISCH_THEN MATCH_MP_TAC THEN
    MATCH_MP_TAC OPEN_IN_SUBSET_TRANS THEN EXISTS_TAC `X:real^N->bool` THEN
    ASM_SIMP_TAC[OPEN_IN_INTER; INTER_SUBSET];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(h:real^N->real^2) y` o GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL]) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `IMAGE (k:real^2->real^N) (ball((h:real^N->real^2) y,e))` THEN
  SUBGOAL_THEN `homeomorphism ((:real^2),u) ((k:real^2->real^N),(h:real^N->real^2))`
  ASSUME_TAC THENL [ONCE_REWRITE_TAC[HOMEOMORPHISM_SYM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (k:real^2->real^N) (ball((h:real^N->real^2) y,e)) SUBSET u INTER (W:real^N->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `IMAGE (k:real^2->real^N) (IMAGE (h:real^N->real^2) (u INTER W))` THEN
    CONJ_TAC THENL [ASM_SIMP_TAC[IMAGE_SUBSET]; ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `open_in (subtopology euclidean u) (IMAGE (k:real^2->real^N) (ball((h:real^N->real^2) y,e)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HOMEOMORPHISM_IMP_OPEN_MAP THEN
    MAP_EVERY EXISTS_TAC [`h:real^N->real^2`; `(:real^2)`] THEN
    ASM_REWRITE_TAC[SUBTOPOLOGY_UNIV; GSYM OPEN_IN; OPEN_BALL];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_IN_TRANS THEN EXISTS_TAC `W:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC OPEN_IN_SUBSET_TRANS THEN EXISTS_TAC `X:real^N->bool` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_IN_TRANS THEN EXISTS_TAC `u:real^N->bool` THEN ASM_REWRITE_TAC[];
      ASM SET_TAC[]];
    REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `(h:real^N->real^2) y` THEN
    ASM_SIMP_TAC[CENTRE_IN_BALL] THEN ASM SET_TAC[];
    MATCH_MP_TAC(ISPECL [`IMAGE (k:real^2->real^N) (ball((h:real^N->real^2) y,e))`;
                         `ball((h:real^N->real^2) y,e)`; `(:real^2)`] HOMEOMORPHIC_TRANS) THEN
    ASM_SIMP_TAC[HOMEOMORPHIC_BALL_UNIV] THEN ONCE_REWRITE_TAC[HOMEOMORPHIC_SYM] THEN
    REWRITE_TAC[homeomorphic] THEN
    MAP_EVERY EXISTS_TAC [`k:real^2->real^N`; `h:real^N->real^2`] THEN
    MATCH_MP_TAC HOMEOMORPHISM_OF_SUBSETS THEN
    MAP_EVERY EXISTS_TAC [`(:real^2)`; `u:real^N->bool`] THEN
    ASM_REWRITE_TAC[SUBSET_UNIV] THEN ASM SET_TAC[]]);;

let MOI_S3CN_TRI_MISS = prove
 (`!(bx:(real^N->bool)->bool) J r.
     simplicial_complex bx /\ UNIONS {s | s IN bx /\ s SUBSET J} = J /\
     (!s. s IN bx /\ s SUBSET J ==> aff_dim s <= &1) /\ r IN bx /\ aff_dim r = &2
     ==> DISJOINT (relative_interior r) J`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN X_GEN_TAC `z:real^N` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `?s:real^N->bool. s IN bx /\ s SUBSET J /\ z IN s` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(z:real^N) IN J` THEN
    FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM th]) THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `((r:real^N->bool) INTER s) face_of r` ASSUME_TAC THENL
   [UNDISCH_TAC `simplicial_complex (bx:(real^N->bool)->bool)` THEN
    REWRITE_TAC[simplicial_complex] THEN
    DISCH_THEN(MP_TAC o SPECL [`r:real^N->bool`; `s:real^N->bool`] o last o CONJUNCTS) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `(r:real^N->bool) INTER s = r` THENL
   [SUBGOAL_THEN `aff_dim (r:real^N->bool) <= aff_dim (s:real^N->bool)` MP_TAC THENL
     [MATCH_MP_TAC AFF_DIM_SUBSET THEN
      UNDISCH_TAC `(r:real^N->bool) INTER s = r` THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `aff_dim (s:real^N->bool) <= &1` MP_TAC THENL
     [ASM_SIMP_TAC[]; ASM_REWRITE_TAC[] THEN INT_ARITH_TAC];
    MP_TAC(ISPECL [`(r:real^N->bool) INTER s`; `r:real^N->bool`]
                  FACE_OF_DISJOINT_RELATIVE_INTERIOR) THEN
    ASM_REWRITE_TAC[] THEN MP_TAC(ISPEC `r:real^N->bool` RELATIVE_INTERIOR_SUBSET) THEN
    UNDISCH_TAC `(z:real^N) IN relative_interior r` THEN UNDISCH_TAC `(z:real^N) IN s` THEN
    SET_TAC[]]);;

let MOI_S3CN_TRI_PIECE = prove
 (`!(V:A->bool) (oo:real^N->bool) (p:A->real^N) (c:A->real^N->bool) r.
     (!z. z IN oo ==> ?v. v IN V /\ z IN connected_component oo (p v)) /\
     (!v. v IN V ==> c v = closure (connected_component oo (p v))) /\
     convex r /\ closed r /\ ~(relative_interior r = {}) /\ relative_interior r SUBSET oo
     ==> ?v. v IN V /\ relative_interior r SUBSET connected_component oo (p v) /\
             r SUBSET c v`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ex") (CONJUNCTS_THEN2 (LABEL_TAC "cdef")
    STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `z:real^N` o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  USE_THEN "ex" (MP_TAC o SPEC `z:real^N`) THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `(z:real^N) IN relative_interior r` THEN
    UNDISCH_TAC `relative_interior r SUBSET (oo:real^N->bool)` THEN SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `v:A` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `relative_interior r SUBSET connected_component oo ((p:A->real^N) v)`
  ASSUME_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP CONNECTED_COMPONENT_EQ) THEN
    MATCH_MP_TAC CONNECTED_COMPONENT_MAXIMAL THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[CONVEX_CONNECTED; CONVEX_RELATIVE_INTERIOR];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  USE_THEN "cdef" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `(v:A) IN V`)]) THEN
  SUBGOAL_THEN `r = closure (relative_interior r:real^N->bool)` SUBST1_TAC THENL
   [ASM_SIMP_TAC[CONVEX_CLOSURE_RELATIVE_INTERIOR; CLOSURE_CLOSED]; ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_CLOSURE THEN ASM_REWRITE_TAC[]);;

let MOI_S3CN_TWO_SIDES = prove
 (`!(u:real^3->bool) (f:real^3->real^3) g y r Es oo C1 C2.
     open u /\ homeomorphism (u,IMAGE f u) (f,g) /\ y IN u /\ f y = vec 0 /\
     &0 < r /\ ball(vec 0,r) SUBSET IMAGE f u /\
     IMAGE f (Es INTER u) = IMAGE f u INTER {z:real^3 | z$1 = &0} /\
     IMAGE g (ball(vec 0,r)) DIFF Es SUBSET oo /\ DISJOINT oo Es /\
     C1 IN components oo /\ C2 IN components oo /\ ~(C1 = C2) /\
     y IN closure C1 /\ y IN closure C2
     ==> ?sg. sg * sg = &1 /\
              IMAGE g {z | z IN ball(vec 0,r) /\ &0 < sg * z$1} SUBSET C1 /\
              IMAGE g {z | z IN ball(vec 0,r) /\ sg * z$1 < &0} SUBSET C2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  SUBGOAL_THEN `open (IMAGE (g:real^3->real^3) (ball(vec 0,r)))` ASSUME_TAC THENL
   [MATCH_MP_TAC OPEN_IN_OPEN_TRANS THEN EXISTS_TAC `u:real^3->bool` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HOMEOMORPHISM_IMP_OPEN_MAP THEN
    MAP_EVERY EXISTS_TAC [`f:real^3->real^3`; `IMAGE (f:real^3->real^3) u`] THEN
    CONJ_TAC THENL [ONCE_REWRITE_TAC[HOMEOMORPHISM_SYM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC OPEN_SUBSET THEN ASM_REWRITE_TAC[OPEN_BALL];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z. z IN ball(vec 0,r) ==> ((g:real^3->real^3) z IN Es <=> z$1 = &0)`
  (LABEL_TAC "es") THENL
   [X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(z:real^3) IN IMAGE (f:real^3->real^3) u` ASSUME_TAC THENL
     [UNDISCH_TAC `ball(vec 0:real^3,r) SUBSET IMAGE (f:real^3->real^3) u` THEN
      UNDISCH_TAC `(z:real^3) IN ball(vec 0,r)` THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(g:real^3->real^3) z IN u /\ (f:real^3->real^3) (g z) = z`
    STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[] THEN
      UNDISCH_TAC `IMAGE (g:real^3->real^3) (IMAGE (f:real^3->real^3) u) = u` THEN
      UNDISCH_TAC `(z:real^3) IN IMAGE (f:real^3->real^3) u` THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(z:real^3) IN IMAGE (f:real^3->real^3) (Es INTER u) <=> (g:real^3->real^3) z IN Es`
    MP_TAC THENL
     [REWRITE_TAC[IN_IMAGE; IN_INTER] THEN EQ_TAC THENL
       [DISCH_THEN(X_CHOOSE_THEN `q:real^3` STRIP_ASSUME_TAC) THEN
        UNDISCH_TAC `(q:real^3) IN Es` THEN ASM_SIMP_TAC[];
        DISCH_TAC THEN EXISTS_TAC `(g:real^3->real^3) z` THEN ASM_REWRITE_TAC[]];
      ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN SIMP_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `Q1 = IMAGE (g:real^3->real^3) (ball(vec 0,r) INTER {z:real^3 | z$1 > &0})` THEN
  ABBREV_TAC `Q2 = IMAGE (g:real^3->real^3) (ball(vec 0,r) INTER {z:real^3 | z$1 < &0})` THEN
  SUBGOAL_THEN `!Q. (Q = Q1 \/ Q = Q2)
                    ==> connected Q /\ ~(Q = {}) /\ (Q:real^3->bool) SUBSET oo`
  (LABEL_TAC "qf") THENL
   [X_GEN_TAC `Q:real^3->bool` THEN
    DISCH_THEN(DISJ_CASES_THEN SUBST1_TAC) THEN MAP_EVERY EXPAND_TAC ["Q1"; "Q2"] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
        EXISTS_TAC `IMAGE (f:real^3->real^3) u` THEN ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `ball(vec 0:real^3,r) SUBSET IMAGE (f:real^3->real^3) u` THEN SET_TAC[];
        MATCH_MP_TAC CONVEX_CONNECTED THEN
        SIMP_TAC[CONVEX_INTER; CONVEX_BALL; CONVEX_HALFSPACE_COMPONENT_GT]];
      REWRITE_TAC[IMAGE_EQ_EMPTY] THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
      EXISTS_TAC `(r / &2) % basis 1:real^3` THEN
      REWRITE_TAC[IN_INTER; IN_ELIM_THM; IN_BALL_0; NORM_MUL; VECTOR_MUL_COMPONENT;
                  real_gt] THEN
      SIMP_TAC[NORM_BASIS; BASIS_COMPONENT; DIMINDEX_3; ARITH] THEN
      ASM_REAL_ARITH_TAC;
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTER; IN_ELIM_THM; real_gt] THEN
      X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
      UNDISCH_TAC `IMAGE (g:real^3->real^3) (ball(vec 0,r)) DIFF Es SUBSET oo` THEN
      REWRITE_TAC[SUBSET; IN_DIFF] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_SIMP_TAC[FUN_IN_IMAGE] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
        EXISTS_TAC `IMAGE (f:real^3->real^3) u` THEN ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `ball(vec 0:real^3,r) SUBSET IMAGE (f:real^3->real^3) u` THEN SET_TAC[];
        MATCH_MP_TAC CONVEX_CONNECTED THEN
        SIMP_TAC[CONVEX_INTER; CONVEX_BALL; CONVEX_HALFSPACE_COMPONENT_LT]];
      REWRITE_TAC[IMAGE_EQ_EMPTY] THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
      EXISTS_TAC `--(r / &2) % basis 1:real^3` THEN
      REWRITE_TAC[IN_INTER; IN_ELIM_THM; IN_BALL_0; NORM_MUL; VECTOR_MUL_COMPONENT;
                  REAL_ABS_NEG] THEN
      SIMP_TAC[NORM_BASIS; BASIS_COMPONENT; DIMINDEX_3; ARITH] THEN
      ASM_REAL_ARITH_TAC;
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTER; IN_ELIM_THM] THEN
      X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
      UNDISCH_TAC `IMAGE (g:real^3->real^3) (ball(vec 0,r)) DIFF Es SUBSET oo` THEN
      REWRITE_TAC[SUBSET; IN_DIFF] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_SIMP_TAC[FUN_IN_IMAGE] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!Q C. (Q = Q1 \/ Q = Q2) /\ C IN components oo /\ ~(C INTER Q = {})
                      ==> (Q:real^3->bool) SUBSET C`
  (LABEL_TAC "qm") THENL
   [REPEAT GEN_TAC THEN
    DISCH_THEN(CONJUNCTS_THEN2 (fun th -> USE_THEN "qf" (STRIP_ASSUME_TAC o C MATCH_MP th))
      STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC COMPONENTS_MAXIMAL THEN EXISTS_TAC `oo:real^3->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^3) IN IMAGE (g:real^3->real^3) (ball(vec 0,r))` ASSUME_TAC THENL
   [REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `vec 0:real^3` THEN
    ASM_REWRITE_TAC[CENTRE_IN_BALL] THEN
    FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `(f:real^3->real^3) y = vec 0`)) THEN
    CONV_TAC SYM_CONV THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!C. C IN components oo /\ (y:real^3) IN closure C
                    ==> ~(C INTER Q1 = {}) \/ ~(C INTER Q2 = {})`
  (LABEL_TAC "meet") THENL
   [X_GEN_TAC `C:real^3->bool` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`IMAGE (g:real^3->real^3) (ball(vec 0,r))`; `C:real^3->bool`]
                  OPEN_INTER_CLOSURE_EQ_EMPTY) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(TAUT `~p /\ (~q ==> r) ==> (p <=> q) ==> r`) THEN CONJ_TAC THENL
     [UNDISCH_TAC `(y:real^3) IN IMAGE (g:real^3->real^3) (ball(vec 0,r))` THEN
      UNDISCH_TAC `(y:real^3) IN closure C` THEN SET_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `q:real^3` (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
    SUBGOAL_THEN `~((z:real^3)$1 = &0)` ASSUME_TAC THENL
     [USE_THEN "es" (fun th -> REWRITE_TAC[GSYM(MATCH_MP th
        (ASSUME `(z:real^3) IN ball(vec 0,r)`))]) THEN
      FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `q = (g:real^3->real^3) z`)) THEN
      SUBGOAL_THEN `(C:real^3->bool) SUBSET oo` MP_TAC THENL
       [MATCH_MP_TAC IN_COMPONENTS_SUBSET THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `DISJOINT (oo:real^3->bool) Es` THEN
      UNDISCH_TAC `(g:real^3->real^3) z IN C` THEN SET_TAC[];
      ALL_TAC] THEN
    MAP_EVERY EXPAND_TAC ["Q1"; "Q2"] THEN
    REWRITE_TAC[IN_IMAGE; IN_INTER; IN_ELIM_THM; real_gt] THEN
    ASM_CASES_TAC `&0 < (z:real^3)$1` THENL [DISJ1_TAC; DISJ2_TAC] THEN
    EXISTS_TAC `q:real^3` THEN ASM_REWRITE_TAC[] THEN EXISTS_TAC `z:real^3` THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `C1 INTER C2:real^3->bool = {}` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`oo:real^3->bool`; `C1:real^3->bool`; `C2:real^3->bool`]
                  COMPONENTS_NONOVERLAP) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(Q1:real^3->bool = {}) /\ ~(Q2:real^3->bool = {})` STRIP_ASSUME_TAC THENL
   [USE_THEN "qf" (MP_TAC o SPEC `Q1:real^3->bool`) THEN
    USE_THEN "qf" (MP_TAC o SPEC `Q2:real^3->bool`) THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((Q1:real^3->bool) SUBSET C1 /\ Q1 SUBSET C2) /\
                ~((Q2:real^3->bool) SUBSET C1 /\ Q2 SUBSET C2)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `C1 INTER C2:real^3->bool = {}` THEN
    UNDISCH_TAC `~(Q1:real^3->bool = {})` THEN UNDISCH_TAC `~(Q2:real^3->bool = {})` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `((Q1:real^3->bool) SUBSET C1 \/ Q2 SUBSET C1) /\
                ((Q1:real^3->bool) SUBSET C2 \/ Q2 SUBSET C2)`
  (CONJUNCTS_THEN ASSUME_TAC) THENL
   [CONJ_TAC THENL
     [USE_THEN "meet" (MP_TAC o SPEC `C1:real^3->bool`);
      USE_THEN "meet" (MP_TAC o SPEC `C2:real^3->bool`)] THEN
    (ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
     MATCH_MP_TAC MONO_OR THEN CONJ_TAC THEN DISCH_TAC THEN
     USE_THEN "qm" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);
    ALL_TAC] THEN
  SUBGOAL_THEN `((Q1:real^3->bool) SUBSET C1 /\ Q2 SUBSET C2) \/
                ((Q2:real^3->bool) SUBSET C1 /\ Q1 SUBSET C2)`
  MP_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`(Q1:real^3->bool) SUBSET C1 \/ Q2 SUBSET C1`;
      `(Q1:real^3->bool) SUBSET C2 \/ Q2 SUBSET C2`;
      `~((Q1:real^3->bool) SUBSET C1 /\ Q1 SUBSET C2)`;
      `~((Q2:real^3->bool) SUBSET C1 /\ Q2 SUBSET C2)`] THEN
    CONV_TAC TAUT;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(!sg. sg = &1 ==> {z:real^3 | z IN ball(vec 0,r) /\ &0 < sg * z$1} =
                     ball(vec 0,r) INTER {z | z$1 > &0} /\
                     {z:real^3 | z IN ball(vec 0,r) /\ sg * z$1 < &0} =
                     ball(vec 0,r) INTER {z | z$1 < &0}) /\
    (!sg. sg = -- &1 ==> {z:real^3 | z IN ball(vec 0,r) /\ &0 < sg * z$1} =
                         ball(vec 0,r) INTER {z | z$1 < &0} /\
                         {z:real^3 | z IN ball(vec 0,r) /\ sg * z$1 < &0} =
                         ball(vec 0,r) INTER {z | z$1 > &0})`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM; real_gt;
                REAL_ARITH `!x. &0 < &1 * x <=> &0 < x`; REAL_ARITH `!x. &1 * x < &0 <=> x < &0`;
                REAL_ARITH `!x. &0 < -- &1 * x <=> x < &0`;
                REAL_ARITH `!x. -- &1 * x < &0 <=> &0 < x`];
    ALL_TAC] THEN
  STRIP_TAC THENL
   [EXISTS_TAC `&1` THEN ASM_SIMP_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV;
    EXISTS_TAC `-- &1` THEN ASM_SIMP_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV]);;

let MOI_S3CN_CHART_PULL = prove
 (`!(u:real^3->bool) (f:real^3->real^3) g r t k.
     homeomorphism (u,IMAGE f u) (f,g) /\ ball(vec 0,r) SUBSET IMAGE f u /\
     IMAGE f (t INTER u) = IMAGE f u INTER {z:real^3 | z$k = &0}
     ==> !z. z IN ball(vec 0,r) ==> (g z IN t <=> z$k = &0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(z:real^3) IN IMAGE (f:real^3->real^3) u` ASSUME_TAC THENL
   [UNDISCH_TAC `ball(vec 0:real^3,r) SUBSET IMAGE (f:real^3->real^3) u` THEN
    UNDISCH_TAC `(z:real^3) IN ball(vec 0,r)` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(g:real^3->real^3) z IN u /\ (f:real^3->real^3) (g z) = z`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[] THEN
    UNDISCH_TAC `IMAGE (g:real^3->real^3) (IMAGE (f:real^3->real^3) u) = u` THEN
    UNDISCH_TAC `(z:real^3) IN IMAGE (f:real^3->real^3) u` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(z:real^3) IN IMAGE (f:real^3->real^3) (t INTER u) <=> (g:real^3->real^3) z IN t`
  MP_TAC THENL
   [REWRITE_TAC[IN_IMAGE; IN_INTER] THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `q:real^3` STRIP_ASSUME_TAC) THEN
      UNDISCH_TAC `(q:real^3) IN t` THEN ASM_SIMP_TAC[];
      DISCH_TAC THEN EXISTS_TAC `(g:real^3->real^3) z` THEN ASM_REWRITE_TAC[]];
    ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN SIMP_TAC[]]);;

let MOI_S3CN_SIDE_TRACE = prove
 (`!(u:real^3->bool) (f:real^3->real^3) g r Es S P sg.
     homeomorphism (u,IMAGE f u) (f,g) /\ ball(vec 0,r) SUBSET IMAGE f u /\
     IMAGE f (Es INTER u) = IMAGE f u INTER {z:real^3 | z$1 = &0} /\
     IMAGE f (S INTER u) = IMAGE f u INTER {z:real^3 | z$2 = &0} /\ sg * sg = &1 /\
     IMAGE g {z | z IN ball(vec 0,r) /\ &0 < sg * z$1} SUBSET P /\
     DISJOINT (IMAGE g {z | z IN ball(vec 0,r) /\ sg * z$1 < &0}) P /\
     Es INTER IMAGE g (ball(vec 0,r)) SUBSET P
     ==> (P INTER S) INTER IMAGE g (ball(vec 0,r)) =
         IMAGE g {z | z IN ball(vec 0,r) /\ z$2 = &0 /\ &0 <= sg * z$1}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`u:real^3->bool`; `f:real^3->real^3`; `g:real^3->real^3`; `r:real`;
                 `Es:real^3->bool`; `1`] MOI_S3CN_CHART_PULL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(ISPECL [`u:real^3->bool`; `f:real^3->real^3`; `g:real^3->real^3`; `r:real`;
                 `S:real^3->bool`; `2`] MOI_S3CN_CHART_PULL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `p:real^3` THEN
  REWRITE_TAC[IN_INTER; IN_IMAGE; IN_ELIM_THM] THEN EQ_TAC THENL
   [DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)
      (X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC)) THEN
    EXISTS_TAC `z:real^3` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(z:real^3)$2 = &0` ASSUME_TAC THENL
     [FIRST_ASSUM((fun th -> REWRITE_TAC[GSYM(MATCH_MP th
        (ASSUME `(z:real^3) IN ball(vec 0,r)`))]) o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `S:real^3->bool`)) (concl th))) THEN
      UNDISCH_TAC `(p:real^3) IN S` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    UNDISCH_TAC `DISJOINT (IMAGE (g:real^3->real^3)
                   {z | z IN ball(vec 0,r) /\ sg * z$1 < &0}) P` THEN
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_IMAGE; IN_ELIM_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `p:real^3`) THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `z:real^3` THEN ASM_REWRITE_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) THEN
    REPEAT CONJ_TAC THENL
     [ALL_TAC;
      ASM_SIMP_TAC[];
      EXISTS_TAC `z:real^3` THEN ASM_REWRITE_TAC[]] THEN
    ASM_CASES_TAC `&0 < sg * (z:real^3)$1` THENL
     [UNDISCH_TAC `IMAGE (g:real^3->real^3) {z | z IN ball(vec 0,r) /\ &0 < sg * z$1}
                   SUBSET P` THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
      DISCH_THEN(MP_TAC o SPEC `z:real^3`) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(z:real^3)$1 = &0` ASSUME_TAC THENL
     [SUBGOAL_THEN `sg * (z:real^3)$1 = &0` MP_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      UNDISCH_TAC `sg * sg = &1` THEN CONV_TAC REAL_RING;
      ALL_TAC] THEN
    UNDISCH_TAC `Es INTER IMAGE (g:real^3->real^3) (ball(vec 0,r)) SUBSET P` THEN
    REWRITE_TAC[SUBSET; IN_INTER; IN_IMAGE] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_SIMP_TAC[] THEN EXISTS_TAC `z:real^3` THEN ASM_REWRITE_TAC[]]);;

let MOI_S3CN_TRIANG = prove
 (`!(x:(real^3->bool)->bool) (J:A->real^3->bool) ix.
     FINITE x /\ combinatorial_manifold_with_boundary 3 x /\ FINITE ix /\
     (!i. i IN ix ==> pl_polyhedron (J i) /\ J i SUBSET frontier (UNIONS x) /\
                     moi_s4l_line_charts (J i))
     ==> ?bx. FINITE bx /\ simplicial_complex bx /\ combinatorial_manifold 2 bx /\
              UNIONS bx = frontier (UNIONS x) /\
              (!i. i IN ix ==> UNIONS {s | s IN bx /\ s SUBSET J i} = J i) /\
              (!i s. i IN ix /\ s IN bx /\ s SUBSET J i ==> aff_dim s <= &1)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "J")))) THEN
  MP_TAC(ISPEC `x:(real^3->bool)->bool` BOUNDARY_COMPLEX_SURFACE) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  ABBREV_TAC `K0 = boundary_complex (x:(real^3->bool)->bool)` THEN
  SUBGOAL_THEN `complex_boundary (x:(real^3->bool)->bool) = frontier (UNIONS x)` ASSUME_TAC THENL
   [MP_TAC(CONJUNCT2(MATCH_MP COMPLEX_BOUNDARY_FRONTIER_3
      (ASSUME `combinatorial_manifold_with_boundary 3 (x:(real^3->bool)->bool)`))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE (K0:(real^3->bool)->bool) /\ simplicial_complex K0` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `FINITE (K0:(real^3->bool)->bool)` ASSUME_TAC THENL
     [EXPAND_TAC "K0" THEN REWRITE_TAC[boundary_complex] THEN
      MATCH_MP_TAC FINITE_RESTRICT THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[MOI_SIMPLICIAL_COMPLEX_LF] THEN
    UNDISCH_TAC `combinatorial_manifold 2 (K0:(real^3->bool)->bool)` THEN
    SIMP_TAC[combinatorial_manifold];
    ALL_TAC] THEN
  SUBGOAL_THEN `!i. ?c. i IN ix ==> FINITE c /\ (!k. k IN c ==> polytope k) /\
                                 (J:A->real^3->bool) i = UNIONS c`
  MP_TAC THENL
   [X_GEN_TAC `i:A` THEN ASM_CASES_TAC `(i:A) IN ix` THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "J" (MP_TAC o CONJUNCT1 o C MATCH_MP (ASSUME `(i:A) IN ix`)) THEN
    REWRITE_TAC[pl_polyhedron] THEN MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `P:A->(real^3->bool)->bool` (LABEL_TAC "P")) THEN
  MP_TAC(ISPECL [`K0:(real^3->bool)->bool`;
                 `UNIONS (IMAGE (P:A->(real^3->bool)->bool) ix)`]
                SIMPLICIAL_COMPLEX_REFINE_POLYTOPES) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[FINITE_UNIONS; FORALL_IN_IMAGE; FINITE_IMAGE];
      REWRITE_TAC[IN_UNIONS; IN_IMAGE] THEN
      X_GEN_TAC `k:real^3->bool` THEN
      DISCH_THEN(X_CHOOSE_THEN `c:(real^3->bool)->bool` (CONJUNCTS_THEN2
        (X_CHOOSE_THEN `i:A` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
      FIRST_X_ASSUM SUBST_ALL_TAC THEN
      USE_THEN "P" (STRIP_ASSUME_TAC o C MATCH_MP (ASSUME `(i:A) IN ix`)) THEN
      CONJ_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `(J:A->real^3->bool) i` THEN CONJ_TAC THENL
       [ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `(k:real^3->bool) IN (P:A->(real^3->bool)->bool) i` THEN SET_TAC[];
        USE_THEN "J" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `(i:A) IN ix`)])]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `bx:(real^3->bool)->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `bx:(real^3->bool)->bool` THEN
  SUBGOAL_THEN `FINITE (bx:(real^3->bool)->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `simplicial_complex (bx:(real^3->bool)->bool)` THEN SIMP_TAC[simplicial_complex];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^3. y IN UNIONS bx ==> moi_s28_locally_r2 (UNIONS bx) y`
  (LABEL_TAC "r2") THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`K0:(real^3->bool)->bool`; `y:real^3`] MOI_S8TA_CM_ALL_R2) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!i. i IN ix ==> UNIONS {s | s IN bx /\ s SUBSET (J:A->real^3->bool) i} = J i`
  (LABEL_TAC "ju") THENL
   [X_GEN_TAC `i:A` THEN DISCH_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN
    CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
    GEN_REWRITE_TAC I [SUBSET] THEN X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    USE_THEN "P" (STRIP_ASSUME_TAC o C MATCH_MP (ASSUME `(i:A) IN ix`)) THEN
    SUBGOAL_THEN `?k. k IN (P:A->(real^3->bool)->bool) i /\ (z:real^3) IN k`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(z:real^3) IN (J:A->real^3->bool) i` THEN ASM_REWRITE_TAC[IN_UNIONS];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `k:real^3->bool` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `P:A->(real^3->bool)->bool`)) (concl th) &&
      can (find_term ((=) `bx:(real^3->bool)->bool`)) (concl th))) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[IN_UNIONS; IN_IMAGE] THEN
      EXISTS_TAC `(P:A->(real^3->bool)->bool) i` THEN ASM_REWRITE_TAC[] THEN
      EXISTS_TAC `i:A` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `f:(real^3->bool)->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `?s:real^3->bool. s IN f /\ z IN s` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(z:real^3) IN k` THEN ASM_REWRITE_TAC[IN_UNIONS]; ALL_TAC] THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN EXISTS_TAC `s:real^3->bool` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [UNDISCH_TAC `(f:(real^3->bool)->bool) SUBSET bx` THEN
      UNDISCH_TAC `(s:real^3->bool) IN f` THEN SET_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `k:real^3->bool` THEN CONJ_TAC THENL
     [UNDISCH_TAC `k = UNIONS (f:(real^3->bool)->bool)` THEN
      UNDISCH_TAC `(s:real^3->bool) IN f` THEN SET_TAC[];
      UNDISCH_TAC `(k:real^3->bool) IN (P:A->(real^3->bool)->bool) i` THEN
      UNDISCH_TAC `(J:A->real^3->bool) i = UNIONS (P i)` THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!i s. i IN ix /\ s IN bx /\ s SUBSET (J:A->real^3->bool) i
                      ==> aff_dim s <= &1`
  (LABEL_TAC "dim") THENL
   [MAP_EVERY X_GEN_TAC [`i:A`; `s:real^3->bool`] THEN STRIP_TAC THEN
    MATCH_MP_TAC MOI_S4L_LC_DIM_LE1 THEN
    EXISTS_TAC `{s | s IN bx /\ s SUBSET (J:A->real^3->bool) i}` THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN CONJ_TAC THENL
     [MATCH_MP_TAC MOI_LFO_SUBCOMPLEX THEN EXISTS_TAC `bx:(real^3->bool)->bool` THEN
      ASM_REWRITE_TAC[IN_ELIM_THM] THEN CONJ_TAC THENL
       [GEN_REWRITE_TAC I [SUBSET] THEN SIMP_TAC[IN_ELIM_THM]; ALL_TAC] THEN
      MAP_EVERY X_GEN_TAC [`f:real^3->bool`; `t:real^3->bool`] THEN STRIP_TAC THEN
      CONJ_TAC THENL
       [UNDISCH_TAC `simplicial_complex (bx:(real^3->bool)->bool)` THEN
        REWRITE_TAC[simplicial_complex] THEN
        DISCH_THEN(MATCH_MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
        EXISTS_TAC `t:real^3->bool` THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `t:real^3->bool` THEN
        ASM_SIMP_TAC[FACE_OF_IMP_SUBSET]];
      USE_THEN "ju" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `(i:A) IN ix`)]) THEN
      USE_THEN "J" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `(i:A) IN ix`)])];
    ALL_TAC] THEN
  MP_TAC(ISPEC `bx:(real^3->bool)->bool` SURF_LOCAL) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]; USE_THEN "r2" (fun th -> MESON_TAC[th])];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "sb") (LABEL_TAC "cm"))) THEN
  SUBGOAL_THEN `surface_boundary (bx:(real^3->bool)->bool) = {}` ASSUME_TAC THENL
   [USE_THEN "sb" SUBST1_TAC THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN
    USE_THEN "r2" (fun th -> MESON_TAC[th]);
    ALL_TAC] THEN
  SUBGOAL_THEN `combinatorial_manifold 2 (bx:(real^3->bool)->bool)` ASSUME_TAC THENL
   [USE_THEN "cm" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Part 5: Lemma 6, the pieces as surfaces.  At a point of a trace the      *)
(* piece meets Bd X in a closed half disk of a crossing chart, so it is a   *)
(* half-plane point (MOI_S3CN_HALF_AT, from MOI_S3CN_TWO_SIDES,             *)
(* MOI_S3CN_SIDE_TRACE and MOI_S3CN_HALF_CHART).  For a triangulation of Bd *)
(* X whose triangles avoid the pseudo-cells inside, the subcomplex of a     *)
(* piece covers c v INTER Bd X, all its points are plane or half-plane      *)
(* points, so by SURF_LOCAL it is a combinatorial surface with boundary     *)
(* the trace points (MOI_S3CN_PIECE_V).                                     *)
(* ------------------------------------------------------------------------- *)

let MOI_S3CN_HALF_AT = prove
 (`!(S:real^3->bool) E rim Eo N C1 C2 P y.
     pl_crossing_at (E DIFF rim) S y /\
     closed rim /\ ~(y IN rim) /\ closed Eo /\ ~(y IN Eo) /\ y IN interior N /\
     C1 IN components (N DIFF (E UNION Eo)) /\ C2 IN components (N DIFF (E UNION Eo)) /\
     ~(C1 = C2) /\ y IN closure C1 /\ y IN closure C2 /\
     C1 SUBSET P /\ E SUBSET P /\ DISJOINT C2 P
     ==> moi_s28_locally_half (P INTER S) y`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[pl_crossing_at; pl_homeomorphism] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^3->bool` (X_CHOOSE_THEN `f:real^3->real^3`
    (X_CHOOSE_THEN `g:real^3->real^3` STRIP_ASSUME_TAC))) THEN
  ABBREV_TAC `G0 = u INTER interior N INTER ((:real^3) DIFF rim) INTER
                   ((:real^3) DIFF Eo)` THEN
  SUBGOAL_THEN `open (G0:real^3->bool) /\ (y:real^3) IN G0 /\ G0 SUBSET u`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "G0" THEN REPEAT CONJ_TAC THENL
     [REPEAT(MATCH_MP_TAC OPEN_INTER THEN CONJ_TAC) THEN
      ASM_REWRITE_TAC[OPEN_INTERIOR; GSYM closed];
      ASM_REWRITE_TAC[IN_INTER; IN_DIFF; IN_UNIV];
      SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `open (IMAGE (f:real^3->real^3) G0)` ASSUME_TAC THENL
   [MATCH_MP_TAC OPEN_IN_OPEN_TRANS THEN EXISTS_TAC `IMAGE (f:real^3->real^3) u` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HOMEOMORPHISM_IMP_OPEN_MAP THEN
    MAP_EVERY EXISTS_TAC [`g:real^3->real^3`; `u:real^3->bool`] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC OPEN_SUBSET THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `vec 0:real^3` o GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL]) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `y:real^3` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  SUBGOAL_THEN `ball(vec 0:real^3,r) SUBSET IMAGE (f:real^3->real^3) u /\
                IMAGE (g:real^3->real^3) (ball(vec 0,r)) SUBSET G0`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `IMAGE (f:real^3->real^3) G0` THEN
      ASM_SIMP_TAC[IMAGE_SUBSET];
      MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `IMAGE (g:real^3->real^3) (IMAGE (f:real^3->real^3) G0)` THEN
      ASM_SIMP_TAC[IMAGE_SUBSET] THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
      X_GEN_TAC `q:real^3` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(g:real^3->real^3) (f q) = q` SUBST1_TAC THENL
       [FIRST_ASSUM MATCH_MP_TAC THEN
        UNDISCH_TAC `(G0:real^3->bool) SUBSET u` THEN UNDISCH_TAC `(q:real^3) IN G0` THEN
        SET_TAC[];
        ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`u:real^3->bool`; `f:real^3->real^3`; `g:real^3->real^3`; `y:real^3`;
                 `r:real`; `E DIFF rim:real^3->bool`; `N DIFF (E UNION Eo):real^3->bool`;
                 `C1:real^3->bool`; `C2:real^3->bool`] MOI_S3CN_TWO_SIDES) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [UNDISCH_TAC `IMAGE (g:real^3->real^3) (ball(vec 0,r)) SUBSET G0` THEN
      EXPAND_TAC "G0" THEN MP_TAC(ISPEC `N:real^3->bool` INTERIOR_SUBSET) THEN SET_TAC[];
      SET_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `sg:real` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC MOI_S3CN_HALF_CHART THEN
  MAP_EVERY EXISTS_TAC [`u:real^3->bool`; `f:real^3->real^3`; `g:real^3->real^3`;
                        `r:real`; `sg:real`] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_S3CN_SIDE_TRACE THEN
  MAP_EVERY EXISTS_TAC [`u:real^3->bool`; `f:real^3->real^3`; `E DIFF rim:real^3->bool`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM SET_TAC[];
    UNDISCH_TAC `DISJOINT (C2:real^3->bool) P` THEN
    UNDISCH_TAC `IMAGE (g:real^3->real^3) {z | z IN ball(vec 0,r) /\ sg * z$1 < &0}
                 SUBSET C2` THEN SET_TAC[];
    UNDISCH_TAC `(E:real^3->bool) SUBSET P` THEN SET_TAC[]]);;

let MOI_S3CN_PIECE_V = prove
 (`!(bx:(real^3->bool)->bool) S (V:A->bool) N EE (c:A->real^3->bool) (p:A->real^3) v.
     FINITE bx /\ simplicial_complex bx /\ UNIONS bx = S /\ S SUBSET interior N /\
     (!z. z IN S ==> moi_s28_locally_r2 S z) /\
     FINITE V /\ closed EE /\
     (!w. w IN V ==> c w = closure (connected_component (N DIFF EE) (p w))) /\
     UNIONS {c w | w IN V} = N /\
     (!w w'. w IN V /\ w' IN V /\ ~(w = w') ==> c w INTER c w' SUBSET EE) /\
     (!r. r IN bx /\ aff_dim r = &2 ==> DISJOINT (relative_interior r) EE) /\
     v IN V /\
     (!z. z IN S INTER EE INTER c v ==> ?s. s IN bx /\ z IN s /\ s SUBSET c v) /\
     (!z. z IN S INTER EE INTER c v ==> moi_s28_locally_half (c v INTER S) z)
     ==> FINITE {s | s IN bx /\ s SUBSET c v} /\
         combinatorial_manifold_with_boundary 2 {s | s IN bx /\ s SUBSET c v} /\
         UNIONS {s | s IN bx /\ s SUBSET c v} = c v INTER S /\
         surface_boundary {s | s IN bx /\ s SUBSET c v} = S INTER EE INTER c v`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "r2") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "cdef")
    (CONJUNCTS_THEN2 (LABEL_TAC "cov") (CONJUNCTS_THEN2 (LABEL_TAC "int")
    (CONJUNCTS_THEN2 (LABEL_TAC "tri") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "tr") (LABEL_TAC "half")))))))))))))) THEN
  MP_TAC(ISPECL [`V:A->bool`; `N:real^3->bool`; `EE:real^3->bool`; `c:A->real^3->bool`;
                 `p:A->real^3`] MOI_S3CN_PIECES) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [USE_THEN "cdef" ACCEPT_TAC; USE_THEN "cov" ACCEPT_TAC; USE_THEN "int" ACCEPT_TAC];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "dis") (CONJUNCTS_THEN2 (LABEL_TAC "ex")
    (CONJUNCTS_THEN2 (LABEL_TAC "in") (LABEL_TAC "op")))) THEN
  ABBREV_TAC `A = {s | s IN bx /\ s SUBSET (c:A->real^3->bool) v}` THEN
  SUBGOAL_THEN `FINITE (A:(real^3->bool)->bool) /\ simplicial_complex A` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [EXPAND_TAC "A" THEN MATCH_MP_TAC FINITE_RESTRICT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC MOI_LFO_SUBCOMPLEX THEN EXISTS_TAC `bx:(real^3->bool)->bool` THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "A" THEN REWRITE_TAC[IN_ELIM_THM] THEN CONJ_TAC THENL
     [GEN_REWRITE_TAC I [SUBSET] THEN SIMP_TAC[IN_ELIM_THM]; ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`f:real^3->bool`; `t:real^3->bool`] THEN STRIP_TAC THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `simplicial_complex (bx:(real^3->bool)->bool)` THEN
      REWRITE_TAC[simplicial_complex] THEN
      DISCH_THEN(MATCH_MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
      EXISTS_TAC `t:real^3->bool` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `t:real^3->bool` THEN
      ASM_SIMP_TAC[FACE_OF_IMP_SUBSET]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z. z IN (c:A->real^3->bool) v INTER S /\ ~(z IN EE)
                    ==> z IN connected_component (N DIFF EE) ((p:A->real^3) v)`
  (LABEL_TAC "off") THENL
   [X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN USE_THEN "in" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[IN_DIFF] THEN
    UNDISCH_TAC `(S:real^3->bool) SUBSET interior N` THEN
    MP_TAC(ISPEC `N:real^3->bool` INTERIOR_SUBSET) THEN
    UNDISCH_TAC `(z:real^3) IN (c:A->real^3->bool) v INTER S` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `UNIONS (A:(real^3->bool)->bool) = (c:A->real^3->bool) v INTER S`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [EXPAND_TAC "A" THEN REWRITE_TAC[UNIONS_SUBSET; IN_ELIM_THM] THEN
      X_GEN_TAC `s:real^3->bool` THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[SUBSET_INTER] THEN
      FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th =
        `UNIONS bx = (S:real^3->bool)`)) THEN
      UNDISCH_TAC `(s:real^3->bool) IN bx` THEN SET_TAC[];
      ALL_TAC] THEN
    GEN_REWRITE_TAC I [SUBSET] THEN X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    EXPAND_TAC "A" THEN REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
    ASM_CASES_TAC `(z:real^3) IN EE` THENL
     [USE_THEN "tr" (MP_TAC o SPEC `z:real^3`) THEN
      ANTS_TAC THENL
       [UNDISCH_TAC `(z:real^3) IN EE` THEN
        UNDISCH_TAC `(z:real^3) IN (c:A->real^3->bool) v INTER S` THEN SET_TAC[];
        MESON_TAC[]];
      ALL_TAC] THEN
    USE_THEN "off" (MP_TAC o SPEC `z:real^3`) THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    SUBGOAL_THEN `?q:real^3->bool. q IN bx /\ z IN q` STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN `(z:real^3) IN UNIONS bx` MP_TAC THENL
       [ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `(z:real^3) IN (c:A->real^3->bool) v INTER S` THEN SET_TAC[];
        REWRITE_TAC[IN_UNIONS]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`bx:(real^3->bool)->bool`; `q:real^3->bool`] MOI_S8TB_PURE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [USE_THEN "r2" (fun th -> MESON_TAC[th]);
        UNDISCH_TAC `(z:real^3) IN q` THEN SET_TAC[]];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real^3->bool` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`bx:(real^3->bool)->bool`; `r:real^3->bool`] MOI_LFO_SIMPLEX_COMPACT) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `~(relative_interior r:real^3->bool = {})` ASSUME_TAC THENL
     [ASM_SIMP_TAC[RELATIVE_INTERIOR_EQ_EMPTY] THEN DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `aff_dim ({}:real^3->bool) = &2` THEN
      REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `relative_interior r SUBSET (N DIFF EE:real^3->bool)` ASSUME_TAC THENL
     [USE_THEN "tri" (MP_TAC o SPEC `r:real^3->bool`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      MP_TAC(ISPEC `r:real^3->bool` RELATIVE_INTERIOR_SUBSET) THEN
      SUBGOAL_THEN `(r:real^3->bool) SUBSET N` MP_TAC THENL
       [MP_TAC(ISPEC `N:real^3->bool` INTERIOR_SUBSET) THEN
        UNDISCH_TAC `(S:real^3->bool) SUBSET interior N` THEN
        FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th =
          `UNIONS bx = (S:real^3->bool)`)) THEN
        UNDISCH_TAC `(r:real^3->bool) IN bx` THEN SET_TAC[];
        SET_TAC[]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`V:A->bool`; `N DIFF EE:real^3->bool`; `p:A->real^3`;
                   `c:A->real^3->bool`; `r:real^3->bool`] MOI_S3CN_TRI_PIECE) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[COMPACT_IMP_CLOSED]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `u:A` STRIP_ASSUME_TAC) THEN
    ASM_CASES_TAC `u:A = v` THENL
     [EXISTS_TAC `r:real^3->bool` THEN
      UNDISCH_TAC `(r:real^3->bool) SUBSET (c:A->real^3->bool) u` THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(q:real^3->bool) SUBSET r` THEN UNDISCH_TAC `(z:real^3) IN q` THEN
      SET_TAC[];
      ALL_TAC] THEN
    USE_THEN "dis" (MP_TAC o SPECL [`v:A`; `u:A`]) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `(r:real^3->bool) SUBSET (c:A->real^3->bool) u` THEN
    UNDISCH_TAC `(q:real^3->bool) SUBSET r` THEN UNDISCH_TAC `(z:real^3) IN q` THEN
    UNDISCH_TAC `(z:real^3) IN connected_component (N DIFF EE) ((p:A->real^3) v)` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z. z IN (c:A->real^3->bool) v INTER S /\ ~(z IN EE)
                    ==> moi_s28_locally_r2 (c v INTER S) z`
  (LABEL_TAC "r2off") THENL
   [X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN MATCH_MP_TAC MOI_S3CN_R2_TRANSFER THEN
    MAP_EVERY EXISTS_TAC
     [`S:real^3->bool`;
      `S INTER (connected_component (N DIFF EE) ((p:A->real^3) v) INTER interior N)`] THEN
    SUBGOAL_THEN `(z:real^3) IN connected_component (N DIFF EE) ((p:A->real^3) v)`
    ASSUME_TAC THENL
     [USE_THEN "off" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `open (connected_component (N DIFF EE) ((p:A->real^3) v) INTER interior N)`
    ASSUME_TAC THENL [USE_THEN "op" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_IN_OPEN_INTER THEN ASM_REWRITE_TAC[];
      SUBGOAL_THEN
       `S INTER (connected_component (N DIFF EE) ((p:A->real^3) v) INTER interior N) =
        ((c:A->real^3->bool) v INTER S) INTER
        (connected_component (N DIFF EE) (p v) INTER interior N)`
      SUBST1_TAC THENL
       [SUBGOAL_THEN `connected_component (N DIFF EE) ((p:A->real^3) v) SUBSET
                      (c:A->real^3->bool) v` MP_TAC THENL
         [USE_THEN "cdef" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `(v:A) IN V`)]) THEN
          REWRITE_TAC[CLOSURE_SUBSET];
          SET_TAC[]];
        MATCH_MP_TAC OPEN_IN_OPEN_INTER THEN ASM_REWRITE_TAC[]];
      ASM_REWRITE_TAC[IN_INTER] THEN
      UNDISCH_TAC `(S:real^3->bool) SUBSET interior N` THEN
      UNDISCH_TAC `(z:real^3) IN (c:A->real^3->bool) v INTER S` THEN SET_TAC[];
      USE_THEN "r2" MATCH_MP_TAC THEN
      UNDISCH_TAC `(z:real^3) IN (c:A->real^3->bool) v INTER S` THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z. z IN UNIONS A ==> moi_s28_locally_r2 (UNIONS A) z \/
                                      moi_s28_locally_half (UNIONS (A:(real^3->bool)->bool)) z`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    ASM_CASES_TAC `(z:real^3) IN EE` THENL
     [DISJ2_TAC THEN USE_THEN "half" MATCH_MP_TAC THEN
      UNDISCH_TAC `(z:real^3) IN EE` THEN
      UNDISCH_TAC `(z:real^3) IN (c:A->real^3->bool) v INTER S` THEN SET_TAC[];
      DISJ1_TAC THEN USE_THEN "r2off" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPEC `A:(real^3->bool)->bool` SURF_LOCAL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 SUBST1_TAC (K ALL_TAC))) THEN
  ASM_REWRITE_TAC[] THEN GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `z:real^3` THEN
  REWRITE_TAC[IN_ELIM_THM; IN_INTER] THEN
  ASM_CASES_TAC `(z:real^3) IN EE` THEN ASM_REWRITE_TAC[] THENL
   [EQ_TAC THENL [SIMP_TAC[]; ALL_TAC] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_S8TA_HALF_NOT_R2 THEN USE_THEN "half" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[IN_INTER];
    ALL_TAC] THEN
  REWRITE_TAC[TAUT `~(a /\ b /\ ~c)  <=> (a /\ b ==> c)`] THEN STRIP_TAC THEN
  UNDISCH_TAC `~moi_s28_locally_r2 ((c:A->real^3->bool) v INTER S) z` THEN
  REWRITE_TAC[] THEN USE_THEN "r2off" MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_INTER]);;

(* ------------------------------------------------------------------------- *)
(* Part 6: Lemma 6, connectivity of the pieces (the step the book leaves    *)
(* implicit).  Attaching disjoint closed sets along connected nonempty      *)
(* traces cannot connect a disconnected set (MOI_S3CN_CONN_ATTACH); a       *)
(* component of a closed subset of a connected surface which is open in the *)
(* surface is all of it (MOI_S3CN_CONN_CLOPEN).  MOI_S3CN_CONN: F = A UNION *)
(* (the disks at v) separates the vertex image from the complement of Int   *)
(* N', so 30.2 gives a separating component B; every disk lies in B (else   *)
(* the edge image, the pseudo-cell and its rim reach the complement without *)
(* meeting B); every component of A meets a trace (else it is open and      *)
(* closed in the connected Bd X, and then A is all of Bd X), so F = B is    *)
(* connected and so is A.                                                   *)
(* ------------------------------------------------------------------------- *)

let MOI_S3CN_CONN_ATTACH = prove
 (`!(A:real^N->bool) (W:B->bool) (D:B->real^N->bool).
     closed A /\ FINITE W /\
     (!w. w IN W ==> closed (D w) /\ connected (A INTER D w) /\ ~(A INTER D w = {})) /\
     (!w w'. w IN W /\ w' IN W /\ ~(w = w') ==> DISJOINT (D w) (D w')) /\
     connected (A UNION UNIONS (IMAGE D W))
     ==> connected A`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "D") (CONJUNCTS_THEN2 (LABEL_TAC "dis") MP_TAC)))) THEN
  ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [CONNECTED_CLOSED] THEN
  REWRITE_TAC[NOT_CLAUSES] THEN
  DISCH_THEN(X_CHOOSE_THEN `e1:real^N->bool` (X_CHOOSE_THEN `e2:real^N->bool`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `!w. w IN W ==> A INTER (D:B->real^N->bool) w SUBSET e1 \/
                               A INTER D w SUBSET e2`
  (LABEL_TAC "side") THENL
   [X_GEN_TAC `w:B` THEN DISCH_TAC THEN
    USE_THEN "D" (MP_TAC o CONJUNCT1 o CONJUNCT2 o C MATCH_MP (ASSUME `(w:B) IN W`)) THEN
    REWRITE_TAC[CONNECTED_CLOSED; NOT_EXISTS_THM] THEN
    DISCH_THEN(MP_TAC o SPECL [`e1:real^N->bool`; `e2:real^N->bool`]) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(A:real^N->bool) SUBSET e1 UNION e2` THEN
    UNDISCH_TAC `e1 INTER e2 INTER (A:real^N->bool) = {}` THEN SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[CONNECTED_CLOSED] THEN
  EXISTS_TAC `(e1 INTER A) UNION
              UNIONS {(D:B->real^N->bool) w | w | w IN W /\ A INTER D w SUBSET e1}` THEN
  EXISTS_TAC `(e2 INTER A) UNION
              UNIONS {(D:B->real^N->bool) w | w | w IN W /\ ~(A INTER D w SUBSET e1)}` THEN
  SUBGOAL_THEN `!P. FINITE {(D:B->real^N->bool) w | w | w IN W /\ P w} /\
                    (!t. t IN {D w | w | w IN W /\ P w} ==> closed t)`
  ASSUME_TAC THENL
   [GEN_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `IMAGE (D:B->real^N->bool) W` THEN
      ASM_SIMP_TAC[FINITE_IMAGE] THEN SET_TAC[];
      REWRITE_TAC[FORALL_IN_GSPEC] THEN X_GEN_TAC `w:B` THEN STRIP_TAC THEN
      USE_THEN "D" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `(w:B) IN W`)])];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CLOSED_UNION THEN ASM_SIMP_TAC[CLOSED_INTER] THEN
    MATCH_MP_TAC CLOSED_UNIONS THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC CLOSED_UNION THEN ASM_SIMP_TAC[CLOSED_INTER] THEN
    MATCH_MP_TAC CLOSED_UNIONS THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[UNION_SUBSET; UNIONS_SUBSET; FORALL_IN_IMAGE] THEN CONJ_TAC THENL
     [UNDISCH_TAC `(A:real^N->bool) SUBSET e1 UNION e2` THEN SET_TAC[]; ALL_TAC] THEN
    X_GEN_TAC `w:B` THEN DISCH_TAC THEN
    ASM_CASES_TAC `A INTER (D:B->real^N->bool) w SUBSET e1` THENL
     [MATCH_MP_TAC(SET_RULE `!s t u v:real^N->bool. s SUBSET t ==> s SUBSET (u UNION t) UNION v`) THEN
      MATCH_MP_TAC(SET_RULE `!s u:(real^N->bool)->bool. s IN u ==> s SUBSET UNIONS u`) THEN
      REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `w:B` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC(SET_RULE `!s t u v:real^N->bool. s SUBSET t ==> s SUBSET v UNION (u UNION t)`) THEN
      MATCH_MP_TAC(SET_RULE `!s u:(real^N->bool)->bool. s IN u ==> s SUBSET UNIONS u`) THEN
      REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `w:B` THEN ASM_REWRITE_TAC[]];
    ALL_TAC;
    UNDISCH_TAC `~(e1 INTER (A:real^N->bool) = {})` THEN SET_TAC[];
    UNDISCH_TAC `~(e2 INTER (A:real^N->bool) = {})` THEN SET_TAC[]] THEN
  SUBGOAL_THEN
   `UNIONS {(D:B->real^N->bool) w | w | w IN W /\ A INTER D w SUBSET e1} INTER A
    SUBSET e1 /\
    UNIONS {(D:B->real^N->bool) w | w | w IN W /\ ~(A INTER D w SUBSET e1)} INTER A
    SUBSET e2 /\
    UNIONS {(D:B->real^N->bool) w | w | w IN W /\ A INTER D w SUBSET e1} INTER
    UNIONS {(D:B->real^N->bool) w | w | w IN W /\ ~(A INTER D w SUBSET e1)} = {}`
  MP_TAC THENL
   [REPEAT CONJ_TAC THENL
     [GEN_REWRITE_TAC I [SUBSET] THEN REWRITE_TAC[IN_INTER; IN_UNIONS; IN_ELIM_THM] THEN
      X_GEN_TAC `z:real^N` THEN
      DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `t:real^N->bool` (CONJUNCTS_THEN2
        (X_CHOOSE_THEN `w:B` STRIP_ASSUME_TAC) ASSUME_TAC)) ASSUME_TAC) THEN
      UNDISCH_TAC `A INTER (D:B->real^N->bool) w SUBSET e1` THEN
      REWRITE_TAC[SUBSET; IN_INTER] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(z:real^N) IN t` THEN ASM_REWRITE_TAC[];
      GEN_REWRITE_TAC I [SUBSET] THEN REWRITE_TAC[IN_INTER; IN_UNIONS; IN_ELIM_THM] THEN
      X_GEN_TAC `z:real^N` THEN
      DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `t:real^N->bool` (CONJUNCTS_THEN2
        (X_CHOOSE_THEN `w:B` STRIP_ASSUME_TAC) ASSUME_TAC)) ASSUME_TAC) THEN
      USE_THEN "side" (MP_TAC o C MATCH_MP (ASSUME `(w:B) IN W`)) THEN
      ASM_REWRITE_TAC[SUBSET; IN_INTER] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(z:real^N) IN t` THEN ASM_REWRITE_TAC[];
      GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `z:real^N` THEN
      REWRITE_TAC[IN_INTER; NOT_IN_EMPTY; IN_UNIONS; IN_ELIM_THM] THEN
      DISCH_THEN(CONJUNCTS_THEN2
        (X_CHOOSE_THEN `t:real^N->bool` (CONJUNCTS_THEN2
          (X_CHOOSE_THEN `w:B` STRIP_ASSUME_TAC) ASSUME_TAC))
        (X_CHOOSE_THEN `t':real^N->bool` (CONJUNCTS_THEN2
          (X_CHOOSE_THEN `w':B` STRIP_ASSUME_TAC) ASSUME_TAC))) THEN
      SUBGOAL_THEN `~(w:B = w')` ASSUME_TAC THENL
       [DISCH_THEN SUBST_ALL_TAC THEN ASM_MESON_TAC[]; ALL_TAC] THEN
      USE_THEN "dis" (MP_TAC o SPECL [`w:B`; `w':B`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `(z:real^N) IN t` THEN UNDISCH_TAC `(z:real^N) IN t'` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[]];
    ALL_TAC] THEN
  UNDISCH_TAC `e1 INTER e2 INTER (A:real^N->bool) = {}` THEN SET_TAC[]);;

let MOI_S3CN_CONN_CLOPEN = prove
 (`!(A:real^N->bool) S A'.
     closed A /\ A SUBSET S /\ connected S /\ FINITE (components A) /\ A' IN components A /\
     (!z. z IN A' ==> ?O. open O /\ z IN O /\ S INTER O SUBSET A)
     ==> A' = S`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(A':real^N->bool = {}) /\ A' SUBSET A /\ closed A'` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[IN_COMPONENTS_NONEMPTY; IN_COMPONENTS_SUBSET; CLOSED_COMPONENTS];
    ALL_TAC] THEN
  ABBREV_TAC `G = (:real^N) DIFF UNIONS (components A DELETE (A':real^N->bool))` THEN
  SUBGOAL_THEN `open (G:real^N->bool) /\ A' = A INTER G`
  (CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o SYM)) THENL
   [EXPAND_TAC "G" THEN CONJ_TAC THENL
     [REWRITE_TAC[GSYM closed] THEN MATCH_MP_TAC CLOSED_UNIONS THEN
      ASM_SIMP_TAC[FINITE_DELETE; IN_DELETE] THEN
      X_GEN_TAC `c:real^N->bool` THEN STRIP_TAC THEN
      MATCH_MP_TAC CLOSED_COMPONENTS THEN EXISTS_TAC `A:real^N->bool` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `z:real^N` THEN
    REWRITE_TAC[IN_INTER; IN_DIFF; IN_UNIV; IN_UNIONS; IN_DELETE] THEN EQ_TAC THENL
     [DISCH_TAC THEN CONJ_TAC THENL
       [UNDISCH_TAC `(A':real^N->bool) SUBSET A` THEN UNDISCH_TAC `(z:real^N) IN A'` THEN
        SET_TAC[];
        ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `c:real^N->bool` STRIP_ASSUME_TAC) THEN
      MP_TAC(ISPECL [`A:real^N->bool`; `A':real^N->bool`; `c:real^N->bool`]
                    COMPONENTS_NONOVERLAP) THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(ASSUME `~(c:real^N->bool = A')`) THEN MP_TAC(ASSUME `(z:real^N) IN A'`) THEN
      MP_TAC(ASSUME `(z:real^N) IN c`) THEN SET_TAC[];
      STRIP_TAC THEN
      MP_TAC(ISPEC `A:real^N->bool` UNIONS_COMPONENTS) THEN
      REWRITE_TAC[EXTENSION; IN_UNIONS] THEN DISCH_THEN(MP_TAC o SPEC `z:real^N`) THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPEC `S:real^N->bool` CONNECTED_CLOPEN) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `A':real^N->bool`) THEN ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [ONCE_REWRITE_TAC[OPEN_IN_SUBOPEN] THEN X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `z:real^N` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `S:real^N->bool`)) (concl th))) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `O:real^N->bool` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `S INTER (O INTER G:real^N->bool)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC OPEN_IN_OPEN_INTER THEN ASM_SIMP_TAC[OPEN_INTER]; ALL_TAC] THEN
      CONJ_TAC THENL
       [UNDISCH_TAC `(z:real^N) IN A'` THEN UNDISCH_TAC `(z:real^N) IN O` THEN
        UNDISCH_TAC `(A':real^N->bool) SUBSET A` THEN UNDISCH_TAC `(A:real^N->bool) SUBSET S` THEN
        UNDISCH_TAC `A INTER G = (A':real^N->bool)` THEN SET_TAC[];
        UNDISCH_TAC `S INTER O SUBSET (A:real^N->bool)` THEN
        UNDISCH_TAC `A INTER G = (A':real^N->bool)` THEN SET_TAC[]];
      MATCH_MP_TAC CLOSED_SUBSET THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(A':real^N->bool) SUBSET A` THEN UNDISCH_TAC `(A:real^N->bool) SUBSET S` THEN
      SET_TAC[]];
    ASM_REWRITE_TAC[]]);;

let MOI_S3CN_CONN = prove
 (`!(X:real^3->bool) P (W:B->bool) (E:B->real^3->bool) (Y:B->real^3->bool) pv k.
     MOISE_302_STATEMENT /\
     compact X /\ connected (frontier X) /\ closed P /\ FINITE W /\
     closed k /\ connected k /\ ~(k = {}) /\ DISJOINT k X /\
     FINITE (components (P INTER frontier X)) /\
     pv IN X /\ pv IN P /\ ~(pv IN frontier X) /\ (!w. w IN W ==> ~(pv IN E w)) /\
     (!w. w IN W ==> closed (E w) /\ connected (E w) /\ E w SUBSET P /\
                     connected (E w INTER X) /\ ~(E w INTER frontier X = {}) /\
                     connected (E w INTER frontier X) /\ ~(E w INTER k = {}) /\
                     connected (Y w) /\ pv IN Y w /\ ~(Y w INTER E w = {}) /\
                     DISJOINT (Y w) (frontier X) /\
                     (!w'. w' IN W /\ ~(w' = w) ==> DISJOINT (Y w) (E w'))) /\
     (!w w'. w IN W /\ w' IN W /\ ~(w = w') ==> DISJOINT (E w) (E w')) /\
     (!z. z IN X INTER P /\ ~(z IN frontier X) /\ (!w. w IN W ==> ~(z IN E w))
          ==> z IN interior (X INTER P)) /\
     (!z. z IN P INTER frontier X /\ (!w. w IN W ==> ~(z IN E w))
          ==> ?O. open O /\ z IN O /\ frontier X INTER O SUBSET P)
     ==> connected (P INTER frontier X)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> MAP_EVERY (fun (s,t) -> LABEL_TAC s t)
    (zip ["302";"cX";"cS";"cP";"fW";"ck";"conk";"nk";"dkX";"fc";"pvX";"pvP";"pvS";
          "pvE";"Ew";"dis";"int";"loc"] (CONJUNCTS th))) THEN
  ABBREV_TAC `S = frontier (X:real^3->bool)` THEN
  SUBGOAL_THEN `closed (X:real^3->bool) /\ closed (S:real^3->bool) /\ S SUBSET X`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED; FRONTIER_CLOSED;
                                     FRONTIER_SUBSET_CLOSED];
    ALL_TAC] THEN
  ABBREV_TAC `A = (P:real^3->bool) INTER S` THEN
  SUBGOAL_THEN `closed (A:real^3->bool) /\ A SUBSET S /\ A SUBSET P` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "A" THEN ASM_SIMP_TAC[CLOSED_INTER; INTER_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `!w. w IN W ==> A INTER ((E:B->real^3->bool) w INTER X) = E w INTER S`
  (LABEL_TAC "trace") THENL
   [X_GEN_TAC `w:B` THEN DISCH_TAC THEN
    USE_THEN "Ew" (MP_TAC o C MATCH_MP (ASSUME `(w:B) IN W`)) THEN STRIP_TAC THEN
    EXPAND_TAC "A" THEN UNDISCH_TAC `(E:B->real^3->bool) w SUBSET P` THEN
    UNDISCH_TAC `(S:real^3->bool) SUBSET X` THEN SET_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `FF = A UNION UNIONS (IMAGE (\w. (E:B->real^3->bool) w INTER X) W)` THEN
  SUBGOAL_THEN `closed (FF:real^3->bool) /\ FF SUBSET X INTER P /\ A SUBSET FF /\
                (!w. w IN W ==> (E:B->real^3->bool) w INTER X SUBSET FF)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "FF" THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CLOSED_UNION THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CLOSED_UNIONS THEN ASM_SIMP_TAC[FINITE_IMAGE; FORALL_IN_IMAGE] THEN
      X_GEN_TAC `w:B` THEN DISCH_TAC THEN MATCH_MP_TAC CLOSED_INTER THEN
      USE_THEN "Ew" (fun th -> ASM_SIMP_TAC[MATCH_MP th (ASSUME `(w:B) IN W`)]);
      REWRITE_TAC[UNION_SUBSET; UNIONS_SUBSET; FORALL_IN_IMAGE] THEN CONJ_TAC THENL
       [UNDISCH_TAC `(A:real^3->bool) SUBSET S` THEN UNDISCH_TAC `(A:real^3->bool) SUBSET P` THEN
        UNDISCH_TAC `(S:real^3->bool) SUBSET X` THEN SET_TAC[];
        X_GEN_TAC `w:B` THEN DISCH_TAC THEN
        USE_THEN "Ew" (MP_TAC o C MATCH_MP (ASSUME `(w:B) IN W`)) THEN SET_TAC[]];
      SET_TAC[];
      X_GEN_TAC `w:B` THEN DISCH_TAC THEN
      MATCH_MP_TAC(SET_RULE `!a s:real^3->bool u. s IN u ==> s SUBSET a UNION UNIONS u`) THEN
      REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `w:B` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE (components (FF:real^3->bool))` ASSUME_TAC THENL
   [SUBGOAL_THEN `FF = UNIONS (components A UNION
                               IMAGE (\w. (E:B->real^3->bool) w INTER X) W)`
    SUBST1_TAC THENL
     [EXPAND_TAC "FF" THEN REWRITE_TAC[UNIONS_UNION; GSYM UNIONS_COMPONENTS]; ALL_TAC] THEN
    MATCH_MP_TAC MOI_S3S6_FINITE_COMPONENTS THEN
    ASM_SIMP_TAC[FINITE_UNION; FINITE_IMAGE; IN_UNION; FORALL_IN_IMAGE] THEN
    X_GEN_TAC `s:real^3->bool` THEN STRIP_TAC THENL
     [MATCH_MP_TAC IN_COMPONENTS_CONNECTED THEN EXISTS_TAC `A:real^3->bool` THEN
      ASM_REWRITE_TAC[];
      UNDISCH_TAC `(s:real^3->bool) IN IMAGE (\w. (E:B->real^3->bool) w INTER X) W` THEN
      REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `w:B` STRIP_ASSUME_TAC) THEN
      ASM_REWRITE_TAC[] THEN
      USE_THEN "Ew" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `(w:B) IN W`)])];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((pv:real^3) IN FF)` ASSUME_TAC THENL
   [EXPAND_TAC "FF" THEN REWRITE_TAC[IN_UNION; IN_UNIONS; IN_IMAGE] THEN
    GEN_REWRITE_TAC I [DE_MORGAN_THM] THEN CONJ_TAC THENL
     [UNDISCH_TAC `(A:real^3->bool) SUBSET S` THEN UNDISCH_TAC `~((pv:real^3) IN S)` THEN
      SET_TAC[];
      STRIP_TAC THEN
      UNDISCH_TAC `(pv:real^3) IN t` THEN ASM_REWRITE_TAC[IN_INTER] THEN
      USE_THEN "pvE" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `(x:B) IN W`)])];
    ALL_TAC] THEN
  SUBGOAL_THEN `separates_in (:real^3) FF {pv:real^3} k` ASSUME_TAC THENL
   [REWRITE_TAC[separates_in; SUBTOPOLOGY_UNIV; GSYM OPEN_IN] THEN
    MAP_EVERY EXISTS_TAC [`interior (X INTER P) DIFF (FF:real^3->bool)`;
                          `(:real^3) DIFF (X INTER P)`] THEN
    SUBGOAL_THEN `interior (X INTER P) SUBSET (X INTER P:real^3->bool)` ASSUME_TAC THENL
     [REWRITE_TAC[INTERIOR_SUBSET]; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_DIFF THEN ASM_REWRITE_TAC[OPEN_INTERIOR];
      REWRITE_TAC[GSYM closed] THEN ASM_SIMP_TAC[CLOSED_INTER];
      UNDISCH_TAC `interior (X INTER P) SUBSET (X INTER P:real^3->bool)` THEN SET_TAC[];
      GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `z:real^3` THEN
      REWRITE_TAC[IN_UNION; IN_DIFF; IN_UNIV] THEN EQ_TAC THENL
       [UNDISCH_TAC `interior (X INTER P) SUBSET (X INTER P:real^3->bool)` THEN
        UNDISCH_TAC `(FF:real^3->bool) SUBSET X INTER P` THEN SET_TAC[];
        DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
        ASM_CASES_TAC `(z:real^3) IN X INTER P` THEN ASM_REWRITE_TAC[] THEN
        USE_THEN "int" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
         [DISCH_TAC THEN UNDISCH_TAC `~((z:real^3) IN FF)` THEN REWRITE_TAC[] THEN
          UNDISCH_TAC `(A:real^3->bool) SUBSET FF` THEN EXPAND_TAC "A" THEN
          UNDISCH_TAC `(z:real^3) IN X INTER P` THEN UNDISCH_TAC `(z:real^3) IN S` THEN
          SET_TAC[];
          X_GEN_TAC `w:B` THEN DISCH_TAC THEN DISCH_TAC THEN
          UNDISCH_TAC `~((z:real^3) IN FF)` THEN REWRITE_TAC[] THEN
          FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(w:B) IN W`) o check (fun th ->
            is_forall(concl th) && can (find_term ((=) `FF:real^3->bool`)) (concl th))) THEN
          UNDISCH_TAC `(z:real^3) IN X INTER P` THEN
          UNDISCH_TAC `(z:real^3) IN (E:B->real^3->bool) w` THEN SET_TAC[]]];
      REWRITE_TAC[SING_SUBSET; IN_DIFF] THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "int" MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_INTER];
      UNDISCH_TAC `DISJOINT (k:real^3->bool) X` THEN SET_TAC[]];
    ALL_TAC] THEN
  USE_THEN "302" (MP_TAC o SPECL [`(:real^3)`; `FF:real^3->bool`; `{pv:real^3}`;
                                   `k:real^3->bool`] o REWRITE_RULE[MOISE_302_STATEMENT]) THEN
  REWRITE_TAC[SUBTOPOLOGY_UNIV; GSYM CLOSED_IN; OPEN_UNIV; CONNECTED_SING; CLOSED_SING;
              NOT_INSERT_EMPTY] THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[CONVEX_IMP_SIMPLY_CONNECTED; CONVEX_UNIV] THEN
    REWRITE_TAC[DISJOINT; INTER; IN_SING; IN_ELIM_THM; EXTENSION; NOT_IN_EMPTY] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `DISJOINT (k:real^3->bool) X` THEN UNDISCH_TAC `(pv:real^3) IN X` THEN
      REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN MESON_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `DISJOINT (k:real^3->bool) X` THEN
    UNDISCH_TAC `(FF:real^3->bool) SUBSET X INTER P` THEN
    REWRITE_TAC[DISJOINT; SUBSET; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN MESON_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real^3->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(B:real^3->bool) SUBSET FF` ASSUME_TAC THENL
   [MATCH_MP_TAC IN_COMPONENTS_SUBSET THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!w. w IN W ==> (E:B->real^3->bool) w INTER X SUBSET B` (LABEL_TAC "inB") THENL
   [X_GEN_TAC `w:B` THEN DISCH_TAC THEN
    USE_THEN "Ew" (STRIP_ASSUME_TAC o C MATCH_MP (ASSUME `(w:B) IN W`)) THEN
    MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    SUBGOAL_THEN `(E:B->real^3->bool) w INTER X INTER B = {}` ASSUME_TAC THENL
     [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
      UNDISCH_TAC `~((E:B->real^3->bool) w INTER X SUBSET B)` THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC COMPONENTS_MAXIMAL THEN EXISTS_TAC `FF:real^3->bool` THEN
      ASM_SIMP_TAC[] THEN
      UNDISCH_TAC `~((E:B->real^3->bool) w INTER X INTER B = {})` THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `!z. z IN FF /\ z IN (Y:B->real^3->bool) w UNION E w UNION k
                      ==> z IN (E:B->real^3->bool) w INTER X`
    ASSUME_TAC THENL
     [X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
      SUBGOAL_THEN `(z:real^3) IN A \/ ?x:B. x IN W /\ z IN (E:B->real^3->bool) x INTER X`
      MP_TAC THENL
       [UNDISCH_TAC `(z:real^3) IN FF` THEN EXPAND_TAC "FF" THEN
        REWRITE_TAC[IN_UNION; IN_UNIONS; IN_IMAGE] THEN MESON_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `!x:B. x IN W /\ ~(x = w)
                          ==> DISJOINT ((Y:B->real^3->bool) w) (E x) /\
                              DISJOINT ((E:B->real^3->bool) w) (E x)`
      MP_TAC THENL
       [X_GEN_TAC `x:B` THEN STRIP_TAC THEN CONJ_TAC THENL
         [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
            can (find_term ((=) `(Y:B->real^3->bool) w`)) (concl th))) THEN
          ASM_REWRITE_TAC[];
          USE_THEN "dis" MATCH_MP_TAC THEN ASM_MESON_TAC[]];
        ALL_TAC] THEN
      MAP_EVERY (fun t -> MP_TAC(ASSUME t))
       [`(A:real^3->bool) SUBSET S`; `(S:real^3->bool) SUBSET X`;
        `DISJOINT ((Y:B->real^3->bool) w) S`; `DISJOINT (k:real^3->bool) X`;
        `(z:real^3) IN (Y:B->real^3->bool) w UNION E w UNION k`] THEN
      POP_ASSUM_LIST(K ALL_TAC) THEN SET_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `separates_in (:real^3) B {pv:real^3} k` THEN
    REWRITE_TAC[separates_in; SUBTOPOLOGY_UNIV; GSYM OPEN_IN; NOT_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`U:real^3->bool`; `V:real^3->bool`] THEN STRIP_TAC THEN
    MP_TAC(ISPEC `(Y:B->real^3->bool) w UNION E w UNION k` connected) THEN
    SUBGOAL_THEN `connected ((Y:B->real^3->bool) w UNION E w UNION k)` (fun th -> REWRITE_TAC[th]) THENL
     [MATCH_MP_TAC CONNECTED_UNION THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONNECTED_UNION THEN ASM_REWRITE_TAC[];
        UNDISCH_TAC `~((Y:B->real^3->bool) w INTER E w = {})` THEN SET_TAC[]];
      ALL_TAC] THEN
    REWRITE_TAC[] THEN
    MAP_EVERY EXISTS_TAC [`U:real^3->bool`; `V:real^3->bool`] THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `(B:real^3->bool) SUBSET FF` THEN
      UNDISCH_TAC `(E:B->real^3->bool) w INTER X INTER B = {}` THEN
      UNDISCH_TAC `!z. z IN FF /\ z IN (Y:B->real^3->bool) w UNION E w UNION k
                       ==> z IN (E:B->real^3->bool) w INTER X` THEN
      POP_ASSUM_LIST(K ALL_TAC) THEN SET_TAC[];
      UNDISCH_TAC `DISJOINT (U:real^3->bool) V` THEN SET_TAC[];
      UNDISCH_TAC `{pv:real^3} SUBSET U` THEN
      UNDISCH_TAC `(pv:real^3) IN (Y:B->real^3->bool) w` THEN SET_TAC[];
      UNDISCH_TAC `(k:real^3->bool) SUBSET V` THEN UNDISCH_TAC `~(k:real^3->bool = {})` THEN
      SET_TAC[]];
    ALL_TAC] THEN
  ASM_CASES_TAC `?A'. A' IN components A /\
                      (!w. w IN W ==> DISJOINT A' ((E:B->real^3->bool) w))` THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `A':real^3->bool` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`A:real^3->bool`; `S:real^3->bool`; `A':real^3->bool`]
                  MOI_S3CN_CONN_CLOPEN) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(A':real^3->bool) SUBSET A` ASSUME_TAC THENL
       [MATCH_MP_TAC IN_COMPONENTS_SUBSET THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      USE_THEN "loc" (MP_TAC o SPEC `z:real^3`) THEN ANTS_TAC THENL
       [CONJ_TAC THENL
         [UNDISCH_TAC `(A':real^3->bool) SUBSET A` THEN UNDISCH_TAC `(z:real^3) IN A'` THEN
          SET_TAC[];
          X_GEN_TAC `w:B` THEN DISCH_TAC THEN
          FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(w:B) IN W`) o check (fun th ->
            is_forall(concl th) &&
            can (find_term ((=) `A':real^3->bool`)) (concl th))) THEN
          UNDISCH_TAC `(z:real^3) IN A'` THEN SET_TAC[]];
        ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `O:real^3->bool` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `O:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
      EXPAND_TAC "A" THEN UNDISCH_TAC `S INTER O SUBSET (P:real^3->bool)` THEN SET_TAC[];
      DISCH_TAC THEN
      SUBGOAL_THEN `A:real^3->bool = S` (fun th -> ASM_REWRITE_TAC[th]) THEN
      SUBGOAL_THEN `(A':real^3->bool) SUBSET A` MP_TAC THENL
       [MATCH_MP_TAC IN_COMPONENTS_SUBSET THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `A':real^3->bool = S` THEN UNDISCH_TAC `(A:real^3->bool) SUBSET S` THEN
      SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(A:real^3->bool) SUBSET B` ASSUME_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [UNIONS_COMPONENTS] THEN
    REWRITE_TAC[UNIONS_SUBSET] THEN X_GEN_TAC `c:real^3->bool` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `c:real^3->bool` o REWRITE_RULE[NOT_EXISTS_THM]) THEN
    ASM_REWRITE_TAC[NOT_FORALL_THM; NOT_IMP] THEN
    DISCH_THEN(X_CHOOSE_THEN `w:B` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(c:real^3->bool) SUBSET A` ASSUME_TAC THENL
     [MATCH_MP_TAC IN_COMPONENTS_SUBSET THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC COMPONENTS_MAXIMAL THEN EXISTS_TAC `FF:real^3->bool` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC IN_COMPONENTS_CONNECTED THEN EXISTS_TAC `A:real^3->bool` THEN
      ASM_REWRITE_TAC[];
      UNDISCH_TAC `(c:real^3->bool) SUBSET A` THEN UNDISCH_TAC `(A:real^3->bool) SUBSET FF` THEN
      SET_TAC[];
      USE_THEN "inB" (MP_TAC o C MATCH_MP (ASSUME `(w:B) IN W`)) THEN
      UNDISCH_TAC `~DISJOINT (c:real^3->bool) ((E:B->real^3->bool) w)` THEN
      UNDISCH_TAC `(c:real^3->bool) SUBSET A` THEN UNDISCH_TAC `(A:real^3->bool) SUBSET S` THEN
      UNDISCH_TAC `(S:real^3->bool) SUBSET X` THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `connected (FF:real^3->bool)` ASSUME_TAC THENL
   [SUBGOAL_THEN `FF:real^3->bool = B` SUBST1_TAC THENL
     [MATCH_MP_TAC SUBSET_ANTISYM THEN ASM_REWRITE_TAC[] THEN
      EXPAND_TAC "FF" THEN REWRITE_TAC[UNION_SUBSET; UNIONS_SUBSET; FORALL_IN_IMAGE] THEN
      ASM_REWRITE_TAC[] THEN X_GEN_TAC `w:B` THEN DISCH_TAC THEN
      USE_THEN "inB" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `(w:B) IN W`)]);
      MATCH_MP_TAC IN_COMPONENTS_CONNECTED THEN EXISTS_TAC `FF:real^3->bool` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_S3CN_CONN_ATTACH THEN
  MAP_EVERY EXISTS_TAC [`W:B->bool`; `\w. (E:B->real^3->bool) w INTER X`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `w:B` THEN DISCH_TAC THEN
    USE_THEN "trace" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `(w:B) IN W`)]) THEN
    USE_THEN "Ew" (STRIP_ASSUME_TAC o C MATCH_MP (ASSUME `(w:B) IN W`)) THEN
    ASM_SIMP_TAC[CLOSED_INTER];
    MAP_EVERY X_GEN_TAC [`w:B`; `w':B`] THEN STRIP_TAC THEN
    USE_THEN "dis" (MP_TAC o SPECL [`w:B`; `w':B`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SET_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* Part 7: facts of the handle decomposition used by S33_L6.  The           *)
(* midpoint of one edge at v is not on another (MOI_S3CN_MID_OTHER); a       *)
(* pseudo-cell meeting a piece c v belongs to an edge at v                   *)
(* (MOI_S3CN_EDGE_AT); basic facts of pseudo-cells (MOI_S3CN_PSEUDO_FACTS);  *)
(* the graph and handle facts packaged from moi_s33_hd (MOI_S3CN_HD_FACTS).  *)
(* ------------------------------------------------------------------------- *)

let MOI_S3CN_MID_OTHER = prove
 (`!(l:(real^N->bool)->bool) v w w'.
     simplicial_complex l /\ segment[v,w] IN l /\ segment[v,w'] IN l /\
     ~(v = w) /\ ~(v = w') /\ ~(w = w')
     ==> ~(midpoint(v,w') IN segment[v,w])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `(segment[v,w] INTER segment[v,w']) face_of segment[v:real^N,w] /\
                (segment[v,w] INTER segment[v,w']) face_of segment[v:real^N,w']`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `simplicial_complex (l:(real^N->bool)->bool)` THEN
    REWRITE_TAC[simplicial_complex] THEN
    DISCH_THEN(MP_TAC o SPECL [`segment[v:real^N,w]`; `segment[v:real^N,w']`] o
               last o CONJUNCTS) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `segment[v,w] INTER segment[v,w'] = segment[v:real^N,w']` ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`segment[v,w] INTER segment[v:real^N,w']`; `segment[v:real^N,w']`]
                  FACE_OF_DISJOINT_RELATIVE_INTERIOR) THEN
    ASM_REWRITE_TAC[RELATIVE_INTERIOR_SEGMENT] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `midpoint(v:real^N,w')` THEN
    ASM_REWRITE_TAC[IN_INTER; MIDPOINT_IN_SEGMENT];
    ALL_TAC] THEN
  SUBGOAL_THEN `segment[v:real^N,w'] = segment[v,w]` MP_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`segment[v:real^N,w']`; `segment[v:real^N,w]`] FACE_OF_AFF_DIM_LT) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[CONVEX_SEGMENT] THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(segment[v,w] INTER segment[v,w']) face_of segment[v:real^N,w]` THEN
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[AFF_DIM_SEGMENT] THEN INT_ARITH_TAC];
    REWRITE_TAC[SEGMENT_EQ] THEN
    REWRITE_TAC[EXTENSION; IN_INSERT; NOT_IN_EMPTY] THEN
    DISCH_THEN(MP_TAC o SPEC `w':real^N`) THEN ASM_MESON_TAC[]]);;

let MOI_S3CN_EDGE_AT = prove
 (`!(l:(real^N->bool)->bool) (e:(real^N->bool)->real^N->bool) (c:real^N->real^N->bool) v s.
     simplicial_complex l /\ (!s. s IN l ==> aff_dim s <= &1) /\
     (!s s'. s IN l /\ s' IN l /\ aff_dim s = &1 /\ aff_dim s' = &1 /\ ~(s = s')
             ==> DISJOINT (e s) (e s')) /\
     (!v w. {v} IN l /\ {w} IN l /\ ~(v = w)
            ==> c v INTER c w = (if segment[v,w] IN l then e(segment[v,w]) else {})) /\
     {v} IN l /\ s IN l /\ aff_dim s = &1 /\ ~(c v INTER e s = {})
     ==> ?w. ~(w = v) /\ s = segment[v,w] /\ {w} IN l`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "dis") (CONJUNCTS_THEN2 (LABEL_TAC "cc")
    STRIP_ASSUME_TAC)))) THEN
  MP_TAC(ISPECL [`l:(real^N->bool)->bool`; `s:real^N->bool`] MOI_S4L_K1_CASES) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC (DISJ_CASES_THEN2
     (X_CHOOSE_THEN `a:real^N` (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC))
     (X_CHOOSE_THEN `a:real^N` (X_CHOOSE_THEN `b:real^N` STRIP_ASSUME_TAC)))) THENL
   [UNDISCH_TAC `aff_dim ({}:real^N->bool) = &1` THEN REWRITE_TAC[AFF_DIM_EMPTY] THEN
    INT_ARITH_TAC;
    UNDISCH_TAC `aff_dim {a:real^N} = &1` THEN REWRITE_TAC[AFF_DIM_SING] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  ASM_CASES_TAC `v:real^N = a` THENL
   [EXISTS_TAC `b:real^N` THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `v:real^N = b` THENL
   [EXISTS_TAC `a:real^N` THEN ASM_REWRITE_TAC[SEGMENT_SYM]; ALL_TAC] THEN
  SUBGOAL_THEN `(c:real^N->real^N->bool) a INTER c b =
                (e:(real^N->bool)->real^N->bool)(segment[a,b])` ASSUME_TAC THENL
   [USE_THEN "cc" (MP_TAC o SPECL [`a:real^N`; `b:real^N`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(c:real^N->real^N->bool) v INTER (e:(real^N->bool)->real^N->bool)
                (segment[a,b]) = {}` MP_TAC THENL
   [ALL_TAC; ASM_REWRITE_TAC[]] THEN
  USE_THEN "cc" (MP_TAC o SPECL [`v:real^N`; `a:real^N`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  COND_CASES_TAC THENL
   [DISCH_TAC;
    UNDISCH_TAC `(c:real^N->real^N->bool) a INTER c b =
                 (e:(real^N->bool)->real^N->bool)(segment[a,b])` THEN SET_TAC[]] THEN
  USE_THEN "dis" (MP_TAC o SPECL [`segment[v:real^N,a]`; `segment[a:real^N,b]`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[AFF_DIM_SEGMENT; SEGMENT_EQ] THEN
    REWRITE_TAC[EXTENSION; IN_INSERT; NOT_IN_EMPTY] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `(c:real^N->real^N->bool) a INTER c b =
               (e:(real^N->bool)->real^N->bool)(segment[a,b])` THEN
  UNDISCH_TAC `(c:real^N->real^N->bool) v INTER c a =
               (e:(real^N->bool)->real^N->bool)(segment[v:real^N,a])` THEN
  SET_TAC[]);;

let MOI_S3CN_PSEUDO_FACTS = prove
 (`!(e:real^N->bool) j p.
     pseudo_cell e j p
     ==> closed e /\ connected e /\ compact j /\ ~(j = {}) /\ j SUBSET e /\
         p IN e /\ ~(p IN j)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pseudo_cell] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> rhs(concl th) = `e:real^N->bool`)) THEN
    REWRITE_TAC[CLOSED_CLOSURE];
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> rhs(concl th) = `e:real^N->bool`)) THEN
    MATCH_MP_TAC CONNECTED_CLOSURE THEN
    FIRST_X_ASSUM((fun th -> REWRITE_TAC[MATCH_MP HOMEOMORPHIC_CONNECTEDNESS th]) o
      check (fun th -> can (find_term ((=) `ball(vec 0:real^2,&1)`)) (concl th))) THEN
    REWRITE_TAC[CONNECTED_BALL];
    FIRST_X_ASSUM((fun th -> REWRITE_TAC[MATCH_MP HOMEOMORPHIC_COMPACTNESS th]) o
      check (fun th -> can (find_term ((=) `sphere(vec 0:real^2,&1)`)) (concl th))) THEN
    REWRITE_TAC[COMPACT_SPHERE];
    DISCH_THEN SUBST_ALL_TAC THEN
    FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[HOMEOMORPHIC_EMPTY] o check (fun th ->
      can (find_term ((=) `sphere(vec 0:real^2,&1)`)) (concl th))) THEN
    REWRITE_TAC[SPHERE_EQ_EMPTY] THEN REAL_ARITH_TAC;
    ASM SET_TAC[];
    ASM SET_TAC[]]);;

let MOI_S3CN_HD_FACTS = prove
 (`!(t:(real^3->bool)->bool) l (h:real^3->real^3) e c.
     moi_s33_hd t l h e c /\ FINITE l
     ==> simplicial_complex l /\ (!s. s IN l ==> aff_dim s <= &1) /\
         FINITE {v:real^3 | {v} IN l} /\
         (!x y. x IN UNIONS t /\ y IN UNIONS t /\ h x = h y ==> x = y) /\
         h continuous_on UNIONS t /\ UNIONS l SUBSET UNIONS t /\
         (!s. s IN l /\ aff_dim s = &1
              ==> ?a b. ~(a = b) /\ s = segment[a,b] /\ {a} IN l /\ {b} IN l) /\
         (!v w. ~(v = w) /\ segment[v,w] IN l
                ==> {v} IN l /\ {w} IN l /\ aff_dim (segment[v,w]) = &1 /\
                    e(segment[v,w]) = c v INTER c w) /\
         (!s. s IN l /\ aff_dim s = &1 ==> closed (e s) /\ connected (e s)) /\
         closed (UNIONS {e s | s IN l /\ aff_dim s = &1}) /\
         (!v s. {v} IN l /\ s IN l /\ aff_dim s = &1 /\ ~(c v INTER e s = {})
                ==> ?w. ~(w = v) /\ s = segment[v,w] /\ {w} IN l) /\
         (!v w w'. segment[v,w] IN l /\ segment[v,w'] IN l /\
                   ~(v = w) /\ ~(v = w') /\ ~(w = w')
                   ==> ~(midpoint(v,w') IN segment[v,w]))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN REWRITE_TAC[moi_s33_hd] THEN
  DISCH_THEN(fun th -> MAP_EVERY (fun (s,t) -> LABEL_TAC s t)
    (zip ["tube";"pc";"edis";"cdef";"ccov";"cc"] (CONJUNCTS th))) THEN
  USE_THEN "tube" (MP_TAC o REWRITE_RULE[moi_s33_tube; graph_in_complex;
                                        simplicial_subcomplex]) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `simplicial_complex (l:(real^3->bool)->bool)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[MOI_SIMPLICIAL_COMPLEX_LF] THEN MATCH_MP_TAC MOI_FDN_LF_SUBCOMPLEX THEN
    EXISTS_TAC `t:(real^3->bool)->bool` THEN ASM_REWRITE_TAC[simplicial_subcomplex];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s. s IN l /\ aff_dim s = &1
                    ==> ?a b. ~(a = b) /\ s = segment[a:real^3,b] /\ {a} IN l /\ {b} IN l`
  (LABEL_TAC "edge") THENL
   [X_GEN_TAC `q:real^3->bool` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`l:(real^3->bool)->bool`; `q:real^3->bool`] MOI_S4L_K1_CASES) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC (DISJ_CASES_THEN2
       (X_CHOOSE_THEN `a:real^3` (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)) ACCEPT_TAC)) THENL
     [UNDISCH_TAC `aff_dim ({}:real^3->bool) = &1` THEN REWRITE_TAC[AFF_DIM_EMPTY] THEN
      INT_ARITH_TAC;
      UNDISCH_TAC `aff_dim {a:real^3} = &1` THEN REWRITE_TAC[AFF_DIM_SING] THEN INT_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!v w. ~(v = w) /\ segment[v,w] IN l
                      ==> {v} IN l /\ {w} IN l /\ aff_dim (segment[v,w]) = &1 /\
                          (e:(real^3->bool)->real^3->bool)(segment[v,w]) =
                          (c:real^3->real^3->bool) v INTER c w`
  (LABEL_TAC "vw") THENL
   [MAP_EVERY X_GEN_TAC [`v:real^3`; `w:real^3`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `{v:real^3} IN l /\ {w:real^3} IN l` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN
      UNDISCH_TAC `simplicial_complex (l:(real^3->bool)->bool)` THEN
      REWRITE_TAC[simplicial_complex] THEN
      DISCH_THEN(MATCH_MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
      EXISTS_TAC `segment[v:real^3,w]` THEN
      ASM_REWRITE_TAC[FACE_OF_SING; EXTREME_POINT_OF_SEGMENT];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[AFF_DIM_SEGMENT] THEN
    USE_THEN "cc" (MP_TAC o SPECL [`v:real^3`; `w:real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(ACCEPT_TAC o SYM);
    ALL_TAC] THEN
  SUBGOAL_THEN `!s. s IN l /\ aff_dim s = &1
                    ==> closed ((e:(real^3->bool)->real^3->bool) s) /\ connected (e s)`
  (LABEL_TAC "ec") THENL
   [X_GEN_TAC `q:real^3->bool` THEN DISCH_TAC THEN
    USE_THEN "edge" (MP_TAC o C MATCH_MP (ASSUME `(q:real^3->bool) IN l /\ aff_dim q = &1`)) THEN
    DISCH_THEN(X_CHOOSE_THEN `a:real^3` (X_CHOOSE_THEN `b:real^3` STRIP_ASSUME_TAC)) THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    USE_THEN "pc" (MP_TAC o SPECL [`a:real^3`; `b:real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o MATCH_MP MOI_S3CN_PSEUDO_FACTS o CONJUNCT1) THEN SIMP_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`\v:real^3. {v}`; `l:(real^3->bool)->bool`] FINITE_IMAGE_INJ) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN SET_TAC[];
    UNDISCH_TAC `(l:(real^3->bool)->bool) SUBSET t` THEN SET_TAC[];
    MATCH_MP_TAC CLOSED_UNIONS THEN CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `IMAGE (e:(real^3->bool)->real^3->bool) l` THEN
      ASM_SIMP_TAC[FINITE_IMAGE] THEN SET_TAC[];
      REWRITE_TAC[FORALL_IN_GSPEC] THEN USE_THEN "ec" (fun th -> MESON_TAC[th])];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_S3CN_EDGE_AT THEN
    MAP_EVERY EXISTS_TAC [`e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [USE_THEN "edis" (fun th -> MESON_TAC[th; DISJOINT]); USE_THEN "cc" ACCEPT_TAC];
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`l:(real^3->bool)->bool`; `v:real^3`; `w:real^3`; `w':real^3`]
                  MOI_S3CN_MID_OTHER) THEN
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Part 8: Lemma 6 (p.232), S33_L6 |- MOI_S33_L6.  bx is the                *)
(* triangulation of Bd X of MOI_S3CN_TRIANG for the traces E INTER Bd X     *)
(* (PL curves with line charts by the crossing condition, pc_moi_pl1m).     *)
(* For each vertex v the piece complex is a combinatorial surface covering  *)
(* c v INTER Bd X with boundary the traces at v (MOI_S3CN_PIECE_V: off the  *)
(* pseudo-cells the piece is open in Bd X, at a trace point it is a half    *)
(* plane, MOI_S3CN_HALF_AT), and c v INTER Bd X is connected (MOI_S3CN_CONN *)
(* with the edge images h[v,w] as arms to the pseudo-cells).                *)
(* ------------------------------------------------------------------------- *)

let MOI_S3CN_DISK_CONNECTED = prove
 (`!(d:real^N->bool) j. disk_with_boundary d j ==> connected d /\ compact d`,
  REPEAT GEN_TAC THEN REWRITE_TAC[disk_with_boundary] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^2->real^N` (X_CHOOSE_THEN `g:real^N->real^2`
    (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC)))) THEN
  SUBGOAL_THEN `cball(vec 0:real^2,&1) homeomorphic (d:real^N->bool)` MP_TAC THENL
   [REWRITE_TAC[homeomorphic] THEN
    MAP_EVERY EXISTS_TAC [`f:real^2->real^N`; `g:real^N->real^2`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM(MATCH_MP HOMEOMORPHIC_CONNECTEDNESS th);
                                   GSYM(MATCH_MP HOMEOMORPHIC_COMPACTNESS th)]) THEN
  REWRITE_TAC[CONNECTED_CBALL; COMPACT_CBALL]);;

let S33_L6 = prove
 (MOI_S33_L6,
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "302") (LABEL_TAC "tf")) THEN
  MAP_EVERY X_GEN_TAC [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
                       `h:real^3->real^3`; `e:(real^3->bool)->real^3->bool`;
                       `c:real^3->real^3->bool`; `x:(real^3->bool)->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "hd") (LABEL_TAC "inv")) THEN
  SUBGOAL_THEN `moi_s33_tube t l (h:real^3->real^3)` (LABEL_TAC "tube") THENL
   [USE_THEN "hd" (MP_TAC o REWRITE_RULE[moi_s33_hd]) THEN SIMP_TAC[]; ALL_TAC] THEN
  USE_THEN "tf" (MP_TAC o SPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
                                 `h:real^3->real^3`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> MAP_EVERY (fun i -> ASSUME_TAC (el i (CONJUNCTS th))) [0;2;3;5;8;11]) THEN
  REMOVE_THEN "tf" (K ALL_TAC) THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                 `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`]
                MOI_S3CN_HD_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> MAP_EVERY (fun (s,t) -> LABEL_TAC s t)
    (zip ["scl";"dl";"fV";"hinj";"hcont";"lt";"edge";"vw";"ec";"cEE";"eat";"mid"]
         (CONJUNCTS th))) THEN
  USE_THEN "hd" (MP_TAC o REWRITE_RULE[moi_s33_hd]) THEN
  DISCH_THEN(fun th -> MAP_EVERY (fun (s,t) -> LABEL_TAC s t)
    (zip ["tube2";"pc";"edis";"cdef";"ccov";"cc"] (CONJUNCTS th))) THEN
  REMOVE_THEN "tube2" (K ALL_TAC) THEN REMOVE_THEN "ccov" (LABEL_TAC "ccov" o SYM) THEN
  USE_THEN "inv" (MP_TAC o REWRITE_RULE[moi_s33_inv; moi_s33_x2; moi_s33_traces]) THEN
  DISCH_THEN(fun th -> MAP_EVERY (fun (s,t) -> LABEL_TAC s t)
    (zip ["fx";"cmx";"KX";"XN";"cross";"traces";"cX";"cS"] (CONJUNCTS th))) THEN
  SUBGOAL_THEN `compact (IMAGE (h:real^3->real^3) (derived_nbhd t l))` ASSUME_TAC THENL
   [MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `UNIONS (t:(real^3->bool)->bool)` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `compact (UNIONS (x:(real^3->bool)->bool))` ASSUME_TAC THENL
   [MATCH_MP_TAC COMPACT_UNIONS THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `s:real^3->bool` THEN DISCH_TAC THEN MATCH_MP_TAC MOI_FM3_LF_COMPACT THEN
    EXISTS_TAC `x:(real^3->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `combinatorial_manifold_with_boundary 3 (x:(real^3->bool)->bool)` THEN
    SIMP_TAC[combinatorial_manifold_with_boundary];
    ALL_TAC] THEN
  ABBREV_TAC `N' = IMAGE (h:real^3->real^3) (derived_nbhd t l)` THEN
  ABBREV_TAC `X = UNIONS (x:(real^3->bool)->bool)` THEN
  ABBREV_TAC `S = frontier (X:real^3->bool)` THEN
  ABBREV_TAC `EE = UNIONS {(e:(real^3->bool)->real^3->bool) s | s IN l /\ aff_dim s = &1}` THEN
  SUBGOAL_THEN `closed (X:real^3->bool) /\ closed (N':real^3->bool)` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[COMPACT_IMP_CLOSED]; ALL_TAC] THEN
  SUBGOAL_THEN `closed (S:real^3->bool) /\ S SUBSET X` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN REWRITE_TAC[FRONTIER_CLOSED] THEN
    MATCH_MP_TAC FRONTIER_SUBSET_CLOSED THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(S:real^3->bool) SUBSET interior N'` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `X:real^3->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!v w. {v} IN l /\ {w} IN l /\ ~(v = w)
                      ==> (c:real^3->real^3->bool) v INTER c w SUBSET EE`
  (LABEL_TAC "cint") THENL
   [MAP_EVERY X_GEN_TAC [`v:real^3`; `w:real^3`] THEN STRIP_TAC THEN
    USE_THEN "cc" (MP_TAC o SPECL [`v:real^3`; `w:real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    COND_CASES_TAC THEN REWRITE_TAC[EMPTY_SUBSET] THEN EXPAND_TAC "EE" THEN
    MATCH_MP_TAC(SET_RULE `!s:real^3->bool uu. s IN uu ==> s SUBSET UNIONS uu`) THEN
    REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `segment[v:real^3,w]` THEN
    ASM_REWRITE_TAC[AFF_DIM_SEGMENT];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`{v:real^3 | {v} IN l}`; `N':real^3->bool`; `EE:real^3->bool`;
                 `c:real^3->real^3->bool`; `h:real^3->real^3`] MOI_S3CN_PIECES) THEN
  REWRITE_TAC[IN_ELIM_THM] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `v:real^3` THEN DISCH_TAC THEN
    USE_THEN "cdef" (fun th -> REWRITE_TAC[CONJUNCT1(MATCH_MP th (ASSUME `{v:real^3} IN l`))]);
    ALL_TAC] THEN
  DISCH_THEN(fun th -> MAP_EVERY (fun (s,t) -> LABEL_TAC s t)
    (zip ["pdis";"pex";"pin";"pop"] (CONJUNCTS th))) THEN
  SUBGOAL_THEN `closed ((:real^3) DIFF interior N') /\ connected ((:real^3) DIFF interior N') /\
                ~((:real^3) DIFF interior N' = {}) /\ DISJOINT ((:real^3) DIFF interior N') X`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `~bounded ((:real^3) DIFF interior N')` ASSUME_TAC THENL
     [DISCH_TAC THEN MP_TAC(INST_TYPE [`:3`,`:N`] NOT_BOUNDED_UNIV) THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC BOUNDED_SUBSET THEN
      EXISTS_TAC `((:real^3) DIFF interior N') UNION N'` THEN
      ASM_SIMP_TAC[BOUNDED_UNION; COMPACT_IMP_BOUNDED] THEN
      MP_TAC(ISPEC `N':real^3->bool` INTERIOR_SUBSET) THEN SET_TAC[];
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CLOSED_DIFF THEN REWRITE_TAC[CLOSED_UNIV; OPEN_INTERIOR];
      REWRITE_TAC[GSYM CLOSURE_COMPLEMENT] THEN MATCH_MP_TAC CONNECTED_CLOSURE THEN
      ASM_REWRITE_TAC[];
      DISCH_TAC THEN UNDISCH_TAC `~bounded ((:real^3) DIFF interior N')` THEN
      ASM_REWRITE_TAC[BOUNDED_EMPTY];
      UNDISCH_TAC `(X:real^3->bool) SUBSET interior N'` THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!u v. ~(u = v) /\ segment[u,v] IN l
          ==> closed ((e:(real^3->bool)->real^3->bool)(segment[u,v])) /\
              connected (e(segment[u,v])) /\ compact (e(segment[u,v])) /\
              e(segment[u,v]) = (c:real^3->real^3->bool) u INTER c v /\
              compact (moi_s33_rim t l (h:real^3->real^3) u v) /\
              ~(moi_s33_rim t l h u v = {}) /\
              moi_s33_rim t l h u v SUBSET (:real^3) DIFF interior N' /\
              moi_s33_rim t l h u v SUBSET e(segment[u,v]) /\
              h(midpoint(u,v)) IN e(segment[u,v]) /\
              e(segment[u,v]) INTER IMAGE h (UNIONS l) = {h(midpoint(u,v))} /\
              (e(segment[u,v]) DIFF moi_s33_rim t l h u v) INTER S = e(segment[u,v]) INTER S /\
              (!y. y IN (e(segment[u,v]) DIFF moi_s33_rim t l h u v) INTER S
                   ==> pl_crossing_at (e(segment[u,v]) DIFF moi_s33_rim t l h u v) S y) /\
              pl_sphere 1 (e(segment[u,v]) INTER S) /\
              disk_with_boundary (e(segment[u,v]) INTER X) (e(segment[u,v]) INTER S)`
  (LABEL_TAC "ef") THENL
   [MAP_EVERY X_GEN_TAC [`u:real^3`; `v:real^3`] THEN STRIP_TAC THEN
    USE_THEN "pc" (MP_TAC o SPECL [`u:real^3`; `v:real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (STRIP_ASSUME_TAC o MATCH_MP MOI_S3CN_PSEUDO_FACTS)
      (CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o SYM))) THEN
    USE_THEN "vw" (MP_TAC o SPECL [`u:real^3`; `v:real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o SYM)))) THEN
    USE_THEN "traces" (MP_TAC o SPECL [`u:real^3`; `v:real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    SUBGOAL_THEN `moi_s33_rim t l (h:real^3->real^3) u v SUBSET (:real^3) DIFF interior N' /\
                  moi_s33_rim t l h u v INTER S = {}`
    STRIP_ASSUME_TAC THENL
     [FIRST_ASSUM(SUBST1_TAC o check (fun th -> is_eq(concl th) &&
        lhs(concl th) = `moi_s33_rim t l (h:real^3->real^3) u v`)) THEN
      UNDISCH_TAC `(S:real^3->bool) SUBSET interior N'` THEN
      REWRITE_TAC[frontier] THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(c:real^3->real^3->bool) u SUBSET N'` ASSUME_TAC THENL
     [USE_THEN "ccov" (SUBST1_TAC o SYM) THEN
      MATCH_MP_TAC(SET_RULE `!s:real^3->bool uu. s IN uu ==> s SUBSET UNIONS uu`) THEN
      REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `u:real^3` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
     [REWRITE_TAC[COMPACT_EQ_BOUNDED_CLOSED] THEN
      CONJ_TAC THENL [ALL_TAC; FIRST_ASSUM ACCEPT_TAC] THEN
      MATCH_MP_TAC BOUNDED_SUBSET THEN EXISTS_TAC `N':real^3->bool` THEN CONJ_TAC THENL
       [MATCH_MP_TAC COMPACT_IMP_BOUNDED THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      UNDISCH_TAC `(c:real^3->real^3->bool) u SUBSET N'` THEN
      UNDISCH_TAC `(c:real^3->real^3->bool) u INTER c v =
                   (e:(real^3->bool)->real^3->bool) (segment[u,v])` THEN SET_TAC[];
      FIRST_ASSUM(ACCEPT_TAC o SYM o check (fun th -> is_eq(concl th) &&
        rhs(concl th) = `(e:(real^3->bool)->real^3->bool) (segment[u,v])`));
      UNDISCH_TAC `moi_s33_rim t l (h:real^3->real^3) u v INTER S = {}` THEN SET_TAC[];
      X_GEN_TAC `y:real^3` THEN REWRITE_TAC[IN_INTER; IN_DIFF] THEN STRIP_TAC THEN
      USE_THEN "cross" MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_INTER]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`x:(real^3->bool)->bool`;
                 `\s:real^3->bool. (e:(real^3->bool)->real^3->bool) s INTER S`;
                 `{s:real^3->bool | s IN l /\ aff_dim s = &1}`] MOI_S3CN_TRIANG) THEN
  BETA_TAC THEN REWRITE_TAC[IN_ELIM_THM] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_RESTRICT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    X_GEN_TAC `s:real^3->bool` THEN STRIP_TAC THEN
    USE_THEN "edge" (MP_TAC o C MATCH_MP (CONJ (ASSUME `(s:real^3->bool) IN l`)
                                               (ASSUME `aff_dim (s:real^3->bool) = &1`))) THEN
    DISCH_THEN(X_CHOOSE_THEN `a:real^3` (X_CHOOSE_THEN `b:real^3` STRIP_ASSUME_TAC)) THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    USE_THEN "ef" (MP_TAC o SPECL [`a:real^3`; `b:real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    REPEAT CONJ_TAC THENL
     [FIRST_ASSUM((fun th -> GEN_REWRITE_TAC RAND_CONV [GSYM th]) o check (fun th ->
        is_eq(concl th) && is_binary "INTER" (lhs(concl th)) &&
        can (find_term ((=) `moi_s33_rim t l (h:real^3->real^3) a b`)) (lhs(concl th)))) THEN
      MATCH_MP_TAC MOI_S4L_CROSSING_POLYHEDRON THEN CONJ_TAC THENL
       [FIRST_ASSUM((fun th -> REWRITE_TAC[th]) o check (fun th ->
          is_eq(concl th) && is_binary "INTER" (lhs(concl th)) &&
          can (find_term ((=) `moi_s33_rim t l (h:real^3->real^3) a b`)) (lhs(concl th)))) THEN
        MATCH_MP_TAC COMPACT_INTER_CLOSED THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
        FIRST_ASSUM ACCEPT_TAC];
      REWRITE_TAC[INTER_SUBSET];
      FIRST_ASSUM((fun th -> GEN_REWRITE_TAC RAND_CONV [GSYM th]) o check (fun th ->
        is_eq(concl th) && is_binary "INTER" (lhs(concl th)) &&
        can (find_term ((=) `moi_s33_rim t l (h:real^3->real^3) a b`)) (lhs(concl th)))) THEN
      MATCH_MP_TAC MOI_S4L_CROSSING_CHARTS THEN FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `bx:(real^3->bool)->bool` (fun th -> MAP_EVERY
    (fun (s,t) -> LABEL_TAC s t)
    (zip ["bfin";"bsc";"bcm";"bun";"bju";"bdim"] (CONJUNCTS th)))) THEN
  REMOVE_THEN "bun" (LABEL_TAC "bun" o REWRITE_RULE[ASSUME `UNIONS (x:(real^3->bool)->bool) = X`;
                                                   ASSUME `frontier (X:real^3->bool) = S`]) THEN
  SUBGOAL_THEN `!r. r IN bx /\ aff_dim r = &2
                    ==> DISJOINT (relative_interior r) (EE:real^3->bool)`
  (LABEL_TAC "tri") THENL
   [X_GEN_TAC `r:real^3->bool` THEN STRIP_TAC THEN
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
    X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
    UNDISCH_TAC `(z:real^3) IN EE` THEN EXPAND_TAC "EE" THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `q:real^3->bool` (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `s:real^3->bool` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
    MP_TAC(ISPECL [`bx:(real^3->bool)->bool`;
                   `(e:(real^3->bool)->real^3->bool) s INTER S`; `r:real^3->bool`]
                  MOI_S3CN_TRI_MISS) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [USE_THEN "bju" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        REPEAT STRIP_TAC THEN USE_THEN "bdim" MATCH_MP_TAC THEN
        EXISTS_TAC `s:real^3->bool` THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `(z:real^3) IN S` MP_TAC THENL
     [MP_TAC(ISPEC `r:real^3->bool` RELATIVE_INTERIOR_SUBSET) THEN
      USE_THEN "bun" (SUBST1_TAC o SYM) THEN
      UNDISCH_TAC `(r:real^3->bool) IN bx` THEN
      UNDISCH_TAC `(z:real^3) IN relative_interior r` THEN SET_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `(z:real^3) IN q` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(z:real^3) IN relative_interior r` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!v. {v} IN l ==> (h:real^3->real^3) v IN N' DIFF EE /\ h v IN c v /\
                                 connected_component (N' DIFF EE) (h v) SUBSET c v`
  (LABEL_TAC "vtx") THENL
   [X_GEN_TAC `v:real^3` THEN DISCH_TAC THEN
    USE_THEN "cdef" (MP_TAC o C MATCH_MP (ASSUME `{v:real^3} IN l`)) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    DISCH_THEN(MP_TAC o AP_TERM `\s:real^3->bool. (h:real^3->real^3) v IN s`) THEN
    REWRITE_TAC[IN_SING; IN_INTER] THEN DISCH_TAC THEN
    SUBGOAL_THEN `(h:real^3->real^3) v IN c v` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
      SUBGOAL_THEN `connected_component (N' DIFF EE) ((h:real^3->real^3) v) = {}`
      MP_TAC THENL [ASM_REWRITE_TAC[CONNECTED_COMPONENT_EQ_EMPTY]; ALL_TAC] THEN
      MP_TAC(ASSUME `(c:real^3->real^3->bool) v =
                     closure (connected_component (N' DIFF EE) ((h:real^3->real^3) v))`) THEN
      MP_TAC(ASSUME `(h:real^3->real^3) v IN c v`) THEN
      POP_ASSUM_LIST(K ALL_TAC) THEN
      DISCH_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `(h:real^3->real^3) v IN closure {}` THEN
      REWRITE_TAC[CLOSURE_EMPTY; NOT_IN_EMPTY];
      FIRST_ASSUM(SUBST1_TAC o check (fun th -> is_eq(concl th) &&
        lhs(concl th) = `(c:real^3->real^3->bool) v`)) THEN
      REWRITE_TAC[CLOSURE_SUBSET]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!v w z. ~(v = w) /\ segment[v,w] IN l /\
                        z IN (e:(real^3->bool)->real^3->bool)(segment[v,w]) INTER S
                        ==> moi_s28_locally_half ((c:real^3->real^3->bool) v INTER S) z`
  (LABEL_TAC "half") THENL
   [MAP_EVERY X_GEN_TAC [`v:real^3`; `w:real^3`; `z:real^3`] THEN STRIP_TAC THEN
    USE_THEN "ef" (MP_TAC o SPECL [`v:real^3`; `w:real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(fun th -> MAP_EVERY (fun (s,t) -> LABEL_TAC s t)
      (zip ["E1";"E2";"E3";"E4";"E5";"E6";"E7";"E8";"E9";"E10";"E11";"E12";"E13";"E14"]
           (CONJUNCTS th))) THEN
    REMOVE_THEN "E4" (K ALL_TAC) THEN
    USE_THEN "vw" (MP_TAC o SPECL [`v:real^3`; `w:real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o SYM)))) THEN
    USE_THEN "vtx" (STRIP_ASSUME_TAC o C MATCH_MP (ASSUME `{v:real^3} IN l`)) THEN
    USE_THEN "vtx" (STRIP_ASSUME_TAC o C MATCH_MP (ASSUME `{w:real^3} IN l`)) THEN
    ABBREV_TAC `Eo = UNIONS {(e:(real^3->bool)->real^3->bool) s |
                             s IN l /\ aff_dim s = &1 /\ ~(s = segment[v,w])}` THEN
    SUBGOAL_THEN `(e:(real^3->bool)->real^3->bool)(segment[v,w]) UNION Eo = EE`
    ASSUME_TAC THENL
     [MAP_EVERY EXPAND_TAC ["Eo"; "EE"] THEN
      GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `y:real^3` THEN
      REWRITE_TAC[IN_UNION; IN_UNIONS; IN_ELIM_THM] THEN
      EQ_TAC THENL
       [DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC (X_CHOOSE_THEN `q:real^3->bool`
          (CONJUNCTS_THEN2 (X_CHOOSE_THEN `s:real^3->bool` STRIP_ASSUME_TAC) ASSUME_TAC))) THENL
         [EXISTS_TAC `(e:(real^3->bool)->real^3->bool)(segment[v,w])` THEN
          ASM_REWRITE_TAC[] THEN EXISTS_TAC `segment[v:real^3,w]` THEN ASM_REWRITE_TAC[];
          EXISTS_TAC `q:real^3->bool` THEN CONJ_TAC THENL
           [EXISTS_TAC `s:real^3->bool` THEN ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]]];
        DISCH_THEN(X_CHOOSE_THEN `q:real^3->bool` (CONJUNCTS_THEN2
          (X_CHOOSE_THEN `s:real^3->bool` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
        ASM_CASES_TAC `s = segment[v:real^3,w]` THENL
         [DISJ1_TAC THEN UNDISCH_TAC `(y:real^3) IN q` THEN ASM_REWRITE_TAC[];
          DISJ2_TAC THEN EXISTS_TAC `q:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
          EXISTS_TAC `s:real^3->bool` THEN ASM_REWRITE_TAC[]]];
      ALL_TAC] THEN
    SUBGOAL_THEN `closed (Eo:real^3->bool) /\ ~((z:real^3) IN Eo)` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "Eo" THEN CONJ_TAC THENL
       [MATCH_MP_TAC CLOSED_UNIONS THEN CONJ_TAC THENL
         [MATCH_MP_TAC FINITE_SUBSET THEN
          EXISTS_TAC `IMAGE (e:(real^3->bool)->real^3->bool) l` THEN
          ASM_SIMP_TAC[FINITE_IMAGE] THEN SET_TAC[];
          REWRITE_TAC[FORALL_IN_GSPEC] THEN X_GEN_TAC `s:real^3->bool` THEN STRIP_TAC THEN
          USE_THEN "ec" (MP_TAC o SPEC `s:real^3->bool`) THEN ASM_SIMP_TAC[]];
        REWRITE_TAC[IN_UNIONS; IN_ELIM_THM; NOT_EXISTS_THM] THEN
        X_GEN_TAC `q:real^3->bool` THEN
        DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `s:real^3->bool` STRIP_ASSUME_TAC)
          ASSUME_TAC) THEN
        USE_THEN "edis" (MP_TAC o SPECL [`segment[v:real^3,w]`; `s:real^3->bool`]) THEN
        ANTS_TAC THENL
         [ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
          UNDISCH_TAC `~(s = segment[v:real^3,w])` THEN ASM_REWRITE_TAC[];
          ALL_TAC] THEN
        UNDISCH_TAC `(z:real^3) IN q` THEN ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `(z:real^3) IN (e:(real^3->bool)->real^3->bool)(segment[v,w]) INTER S` THEN
        SET_TAC[]];
      ALL_TAC] THEN
    MATCH_MP_TAC MOI_S3CN_HALF_AT THEN
    MAP_EVERY EXISTS_TAC
     [`(e:(real^3->bool)->real^3->bool)(segment[v,w])`; `moi_s33_rim t l (h:real^3->real^3) v w`;
      `Eo:real^3->bool`; `N':real^3->bool`;
      `connected_component (N' DIFF EE) ((h:real^3->real^3) v)`;
      `connected_component (N' DIFF EE) ((h:real^3->real^3) w)`] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(z:real^3) IN (c:real^3->real^3->bool) v /\ (z:real^3) IN c w`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(z:real^3) IN (e:(real^3->bool)->real^3->bool)(segment[v,w]) INTER S` THEN
      UNDISCH_TAC `(c:real^3->real^3->bool) v INTER c w =
                   (e:(real^3->bool)->real^3->bool)(segment[v,w])` THEN SET_TAC[];
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [USE_THEN "E12" MATCH_MP_TAC THEN USE_THEN "E11" SUBST1_TAC THEN ASM_REWRITE_TAC[];
      USE_THEN "E5" (ACCEPT_TAC o MATCH_MP COMPACT_IMP_CLOSED);
      USE_THEN "E7" MP_TAC THEN UNDISCH_TAC `(S:real^3->bool) SUBSET interior N'` THEN
      UNDISCH_TAC `(z:real^3) IN (e:(real^3->bool)->real^3->bool)(segment[v,w]) INTER S` THEN
      SET_TAC[];
      UNDISCH_TAC `(S:real^3->bool) SUBSET interior N'` THEN
      UNDISCH_TAC `(z:real^3) IN (e:(real^3->bool)->real^3->bool)(segment[v,w]) INTER S` THEN
      SET_TAC[];
      REWRITE_TAC[IN_COMPONENTS] THEN EXISTS_TAC `(h:real^3->real^3) v` THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[IN_COMPONENTS] THEN EXISTS_TAC `(h:real^3->real^3) w` THEN ASM_REWRITE_TAC[];
      DISCH_TAC THEN
      USE_THEN "pdis" (MP_TAC o SPECL [`v:real^3`; `w:real^3`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
      EXISTS_TAC `(h:real^3->real^3) w` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[IN; CONNECTED_COMPONENT_REFL_EQ] THEN ASM_REWRITE_TAC[GSYM IN];
      USE_THEN "cdef" (fun th -> REWRITE_TAC[GSYM(CONJUNCT1(MATCH_MP th
        (ASSUME `{v:real^3} IN l`)))]) THEN ASM_REWRITE_TAC[];
      USE_THEN "cdef" (fun th -> REWRITE_TAC[GSYM(CONJUNCT1(MATCH_MP th
        (ASSUME `{w:real^3} IN l`)))]) THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `(c:real^3->real^3->bool) v INTER c w =
                   (e:(real^3->bool)->real^3->bool)(segment[v,w])` THEN SET_TAC[];
      USE_THEN "pdis" (MP_TAC o SPECL [`w:real^3`; `v:real^3`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN SET_TAC[]];
    ALL_TAC] THEN
  EXISTS_TAC `bx:(real^3->bool)->bool` THEN REWRITE_TAC[moi_s33_pieces] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `v:real^3` THEN DISCH_TAC THEN
  SUBGOAL_THEN `!z. z IN S INTER EE INTER (c:real^3->real^3->bool) v
                    ==> ?w. ~(w = v) /\ segment[v,w] IN l /\
                            z IN (e:(real^3->bool)->real^3->bool)(segment[v,w]) INTER S`
  (LABEL_TAC "at") THENL
   [X_GEN_TAC `z:real^3` THEN REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN
    UNDISCH_TAC `(z:real^3) IN EE` THEN EXPAND_TAC "EE" THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `q:real^3->bool` (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `s:real^3->bool` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
    USE_THEN "eat" (MP_TAC o SPECL [`v:real^3`; `s:real^3->bool`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
      EXISTS_TAC `z:real^3` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(z:real^3) IN q` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `w:real^3` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `w:real^3` THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `(z:real^3) IN q` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`bx:(real^3->bool)->bool`; `S:real^3->bool`; `{v:real^3 | {v} IN l}`;
                 `N':real^3->bool`; `EE:real^3->bool`; `c:real^3->real^3->bool`;
                 `h:real^3->real^3`; `v:real^3`] MOI_S3CN_PIECE_V) THEN
  REWRITE_TAC[IN_ELIM_THM] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`bx:(real^3->bool)->bool`; `z:real^3`] MOI_S8TA_CM_ALL_R2) THEN
      ASM_REWRITE_TAC[];
      X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
      USE_THEN "cdef" (fun th -> REWRITE_TAC[CONJUNCT1(MATCH_MP th (ASSUME `{w:real^3} IN l`))]);
      X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
      USE_THEN "at" (MP_TAC o C MATCH_MP
        (ASSUME `(z:real^3) IN S INTER EE INTER (c:real^3->real^3->bool) v`)) THEN
      DISCH_THEN(X_CHOOSE_THEN `w:real^3` STRIP_ASSUME_TAC) THEN
      USE_THEN "vw" (MP_TAC o SPECL [`v:real^3`; `w:real^3`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
        (CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o SYM)))) THEN
      USE_THEN "bju" (MP_TAC o SPEC `segment[v:real^3,w]`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(fun th -> MP_TAC(ASSUME
        `(z:real^3) IN (e:(real^3->bool)->real^3->bool)(segment[v,w]) INTER S`) THEN
        GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM th]) THEN
      REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN MATCH_MP_TAC MONO_EXISTS THEN
      X_GEN_TAC `s:real^3->bool` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(s:real^3->bool) SUBSET (e:(real^3->bool)->real^3->bool)(segment[v,w]) INTER S` THEN
      UNDISCH_TAC `(c:real^3->real^3->bool) v INTER c w =
                   (e:(real^3->bool)->real^3->bool)(segment[v,w])` THEN SET_TAC[];
      X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
      USE_THEN "at" (MP_TAC o C MATCH_MP
        (ASSUME `(z:real^3) IN S INTER EE INTER (c:real^3->real^3->bool) v`)) THEN
      DISCH_THEN(X_CHOOSE_THEN `w:real^3` STRIP_ASSUME_TAC) THEN
      USE_THEN "half" MATCH_MP_TAC THEN EXISTS_TAC `w:real^3` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(fun th -> MAP_EVERY (fun (s,t) -> LABEL_TAC s t)
    (zip ["Af";"Acm";"Au";"Asb"] (CONJUNCTS th))) THEN
  SUBGOAL_THEN `S INTER EE INTER (c:real^3->real^3->bool) v =
                UNIONS {(e:(real^3->bool)->real^3->bool)(segment[v,w]) INTER S | w |
                        ~(w = v) /\ segment[v,w] IN l}`
  ASSUME_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `z:real^3` THEN EQ_TAC THENL
     [DISCH_TAC THEN
      USE_THEN "at" (MP_TAC o C MATCH_MP
        (ASSUME `(z:real^3) IN S INTER EE INTER (c:real^3->real^3->bool) v`)) THEN
      DISCH_THEN(X_CHOOSE_THEN `w:real^3` STRIP_ASSUME_TAC) THEN
      REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
      EXISTS_TAC `(e:(real^3->bool)->real^3->bool)(segment[v,w]) INTER S` THEN
      ASM_REWRITE_TAC[] THEN EXISTS_TAC `w:real^3` THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
      DISCH_THEN(X_CHOOSE_THEN `q:real^3->bool` (CONJUNCTS_THEN2
        (X_CHOOSE_THEN `w:real^3` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
      UNDISCH_TAC `(z:real^3) IN q` THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      USE_THEN "vw" (MP_TAC o SPECL [`v:real^3`; `w:real^3`]) THEN
      ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
        (CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o SYM)))) THEN
      REWRITE_TAC[IN_INTER] THEN REPEAT CONJ_TAC THENL
       [UNDISCH_TAC `(z:real^3) IN (e:(real^3->bool)->real^3->bool)(segment[v,w]) INTER S` THEN
        SET_TAC[];
        EXPAND_TAC "EE" THEN REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
        EXISTS_TAC `(e:(real^3->bool)->real^3->bool)(segment[v,w])` THEN CONJ_TAC THENL
         [EXISTS_TAC `segment[v:real^3,w]` THEN ASM_REWRITE_TAC[];
          UNDISCH_TAC `(z:real^3) IN (e:(real^3->bool)->real^3->bool)(segment[v,w]) INTER S` THEN
          SET_TAC[]];
        UNDISCH_TAC `(z:real^3) IN (e:(real^3->bool)->real^3->bool)(segment[v,w]) INTER S` THEN
        UNDISCH_TAC `(c:real^3->real^3->bool) v INTER c w =
                     (e:(real^3->bool)->real^3->bool)(segment[v,w])` THEN SET_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z. z IN (c:real^3->real^3->bool) v /\ z IN N' /\
                    (!w. ~(w = v) /\ segment[v,w] IN l
                         ==> ~(z IN (e:(real^3->bool)->real^3->bool)(segment[v,w])))
                    ==> z IN connected_component (N' DIFF EE) ((h:real^3->real^3) v)`
  (LABEL_TAC "off") THENL
   [X_GEN_TAC `z:real^3` THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "nw"))) THEN
    USE_THEN "pin" MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_DIFF] THEN
    EXPAND_TAC "EE" THEN REWRITE_TAC[IN_UNIONS; IN_ELIM_THM; NOT_EXISTS_THM] THEN
    X_GEN_TAC `q:real^3->bool` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `s:real^3->bool` STRIP_ASSUME_TAC) ASSUME_TAC) THEN
    USE_THEN "eat" (MP_TAC o SPECL [`v:real^3`; `s:real^3->bool`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
      EXISTS_TAC `z:real^3` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(z:real^3) IN q` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `w:real^3` STRIP_ASSUME_TAC) THEN
    USE_THEN "nw" (MP_TAC o SPEC `w:real^3`) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(s:real^3->bool) IN l` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `(z:real^3) IN q` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(h:real^3->real^3) v IN interior X /\ interior X INTER S = {} /\
                interior X SUBSET X`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `IMAGE (h:real^3->real^3) (UNIONS l) SUBSET interior X` THEN
      MATCH_MP_TAC(SET_RULE `!y:real^3 s t. y IN s ==> s SUBSET t ==> y IN t`) THEN
      MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[IN_UNIONS] THEN
      EXISTS_TAC `{v:real^3}` THEN ASM_REWRITE_TAC[IN_SING];
      SUBST1_TAC(SYM(ASSUME `frontier (X:real^3->bool) = S`)) THEN
      REWRITE_TAC[frontier] THEN SET_TAC[];
      REWRITE_TAC[INTERIOR_SUBSET]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`X:real^3->bool`; `(c:real^3->real^3->bool) v`;
                 `{w:real^3 | ~(w = v) /\ segment[v,w] IN l}`;
                 `\w:real^3. (e:(real^3->bool)->real^3->bool)(segment[v,w])`;
                 `\w:real^3. IMAGE (h:real^3->real^3) (segment[v,w])`;
                 `(h:real^3->real^3) v`; `(:real^3) DIFF interior N'`] MOI_S3CN_CONN) THEN
  BETA_TAC THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [USE_THEN "cdef" (fun th -> REWRITE_TAC[CONJUNCT1(MATCH_MP th (ASSUME `{v:real^3} IN l`))]) THEN
      REWRITE_TAC[CLOSED_CLOSURE];
      MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{w:real^3 | {w} IN l}` THEN
      ASM_REWRITE_TAC[] THEN GEN_REWRITE_TAC I [SUBSET] THEN REWRITE_TAC[IN_ELIM_THM] THEN
      X_GEN_TAC `w:real^3` THEN STRIP_TAC THEN
      USE_THEN "vw" (MP_TAC o SPECL [`v:real^3`; `w:real^3`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
      USE_THEN "Au" (SUBST1_TAC o SYM) THEN MATCH_MP_TAC MOI_FBC_FINITE_COMPONENTS THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN_ELIM_THM] THEN
      X_GEN_TAC `s:real^3->bool` THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`bx:(real^3->bool)->bool`; `s:real^3->bool`] MOI_LFO_SIMPLEX_COMPACT) THEN
      ASM_SIMP_TAC[];
      UNDISCH_TAC `(h:real^3->real^3) v IN interior X` THEN
      UNDISCH_TAC `interior X SUBSET (X:real^3->bool)` THEN SET_TAC[];
      USE_THEN "vtx" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `{v:real^3} IN l`)]);
      UNDISCH_TAC `(h:real^3->real^3) v IN interior X` THEN
      UNDISCH_TAC `interior X INTER (S:real^3->bool) = {}` THEN SET_TAC[];
      (X_GEN_TAC `w:real^3` THEN STRIP_TAC THEN DISCH_TAC THEN
  USE_THEN "ef" (MP_TAC o SPECL [`v:real^3`; `w:real^3`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o el 9 o CONJUNCTS) THEN DISCH_TAC THEN
  SUBGOAL_THEN `(v:real^3) IN UNIONS l /\ midpoint(v,w) IN UNIONS l` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[IN_UNIONS] THEN CONJ_TAC THENL
     [EXISTS_TAC `{v:real^3}` THEN ASM_REWRITE_TAC[IN_SING];
      EXISTS_TAC `segment[v:real^3,w]` THEN ASM_REWRITE_TAC[MIDPOINT_IN_SEGMENT]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(h:real^3->real^3) v = h(midpoint(v,w))` ASSUME_TAC THENL
   [SUBGOAL_THEN `(h:real^3->real^3) v IN IMAGE h (UNIONS l)` MP_TAC THENL
     [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `(h:real^3->real^3) v IN (e:(real^3->bool)->real^3->bool)(segment[v,w])` THEN
    UNDISCH_TAC `(e:(real^3->bool)->real^3->bool)(segment[v,w]) INTER
                 IMAGE (h:real^3->real^3) (UNIONS l) = {h(midpoint(v,w))}` THEN
    SET_TAC[];
    ALL_TAC] THEN
  USE_THEN "hinj" (MP_TAC o SPECL [`v:real^3`; `midpoint(v:real^3,w)`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `UNIONS l SUBSET UNIONS (t:(real^3->bool)->bool)` THEN
    UNDISCH_TAC `(v:real^3) IN UNIONS l` THEN UNDISCH_TAC `midpoint(v:real^3,w) IN UNIONS l` THEN
    SET_TAC[];
    REWRITE_TAC[MIDPOINT_EQ_ENDPOINT] THEN ASM_REWRITE_TAC[]]);
      (X_GEN_TAC `w:real^3` THEN STRIP_TAC THEN
  USE_THEN "ef" (MP_TAC o SPECL [`v:real^3`; `w:real^3`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> MAP_EVERY (fun (s,t) -> LABEL_TAC s t)
    (zip ["F1";"F2";"F3";"F4";"F5";"F6";"F7";"F8";"F9";"F10";"F11";"F12";"F13";"F14"]
         (CONJUNCTS th))) THEN
  REMOVE_THEN "F4" (ASSUME_TAC o SYM) THEN
  SUBGOAL_THEN `segment[v:real^3,w] SUBSET UNIONS l /\
                IMAGE (h:real^3->real^3) (segment[v,w]) SUBSET IMAGE h (UNIONS l)`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
     [MATCH_MP_TAC(SET_RULE `!s:real^3->bool uu. s IN uu ==> s SUBSET UNIONS uu`) THEN
      ASM_REWRITE_TAC[];
      SIMP_TAC[IMAGE_SUBSET]];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [USE_THEN "F1" ACCEPT_TAC;
    USE_THEN "F2" ACCEPT_TAC;
    UNDISCH_TAC `(c:real^3->real^3->bool) v INTER c w =
                 (e:(real^3->bool)->real^3->bool)(segment[v,w])` THEN SET_TAC[];
    USE_THEN "F14" (fun th -> REWRITE_TAC[MATCH_MP MOI_S3CN_DISK_CONNECTED th]);
    USE_THEN "F13" (fun th -> REWRITE_TAC[MATCH_MP MOI_S3CN_PL_SPHERE1_CONNECTED th]);
    USE_THEN "F13" (fun th -> REWRITE_TAC[MATCH_MP MOI_S3CN_PL_SPHERE1_CONNECTED th]);
    USE_THEN "F6" MP_TAC THEN USE_THEN "F7" MP_TAC THEN USE_THEN "F8" MP_TAC THEN SET_TAC[];
    MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN REWRITE_TAC[CONNECTED_SEGMENT] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `UNIONS (t:(real^3->bool)->bool)` THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `UNIONS l SUBSET UNIONS (t:(real^3->bool)->bool)` THEN
    UNDISCH_TAC `segment[v:real^3,w] SUBSET UNIONS l` THEN SET_TAC[];
    MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[ENDS_IN_SEGMENT];
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
    EXISTS_TAC `(h:real^3->real^3)(midpoint(v,w))` THEN
    USE_THEN "F9" (fun th -> REWRITE_TAC[th]) THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[MIDPOINT_IN_SEGMENT];
    UNDISCH_TAC `IMAGE (h:real^3->real^3) (segment[v,w]) SUBSET IMAGE h (UNIONS l)` THEN
    UNDISCH_TAC `IMAGE (h:real^3->real^3) (UNIONS l) SUBSET interior X` THEN
    UNDISCH_TAC `interior X INTER (S:real^3->bool) = {}` THEN SET_TAC[];
    (X_GEN_TAC `w':real^3` THEN STRIP_TAC THEN
  USE_THEN "ef" (MP_TAC o SPECL [`v:real^3`; `w':real^3`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o el 9 o CONJUNCTS) THEN DISCH_TAC THEN
  REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN X_GEN_TAC `y:real^3` THEN
  REWRITE_TAC[IN_IMAGE] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `q:real^3` STRIP_ASSUME_TAC) ASSUME_TAC) THEN
  SUBGOAL_THEN `(q:real^3) IN UNIONS l /\ midpoint(v:real^3,w') IN UNIONS l`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `segment[v:real^3,w] SUBSET UNIONS l` THEN
      UNDISCH_TAC `(q:real^3) IN segment[v,w]` THEN SET_TAC[];
      REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `segment[v:real^3,w']` THEN
      ASM_REWRITE_TAC[MIDPOINT_IN_SEGMENT]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(h:real^3->real^3) q = h(midpoint(v,w'))` ASSUME_TAC THENL
   [SUBGOAL_THEN `(h:real^3->real^3) q IN IMAGE h (UNIONS l)` MP_TAC THENL
     [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `(y:real^3) IN (e:(real^3->bool)->real^3->bool)(segment[v,w'])` THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(e:(real^3->bool)->real^3->bool)(segment[v,w']) INTER
                 IMAGE (h:real^3->real^3) (UNIONS l) = {h(midpoint(v,w'))}` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `q = midpoint(v:real^3,w')` SUBST_ALL_TAC THENL
   [USE_THEN "hinj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `UNIONS l SUBSET UNIONS (t:(real^3->bool)->bool)` THEN
    UNDISCH_TAC `(q:real^3) IN UNIONS l` THEN UNDISCH_TAC `midpoint(v:real^3,w') IN UNIONS l` THEN
    SET_TAC[];
    ALL_TAC] THEN
  USE_THEN "mid" (MP_TAC o SPECL [`v:real^3`; `w:real^3`; `w':real^3`]) THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[])]);
      (MAP_EVERY X_GEN_TAC [`w:real^3`; `w':real^3`] THEN STRIP_TAC THEN
  USE_THEN "edis" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  USE_THEN "vw" (MP_TAC o SPECL [`v:real^3`; `w:real^3`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  USE_THEN "vw" (MP_TAC o SPECL [`v:real^3`; `w':real^3`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  ASM_REWRITE_TAC[SEGMENT_EQ] THEN
  REWRITE_TAC[EXTENSION; IN_INSERT; NOT_IN_EMPTY] THEN
  DISCH_THEN(MP_TAC o SPEC `w:real^3`) THEN ASM_REWRITE_TAC[]);
      (X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(z:real^3) IN connected_component (N' DIFF EE) ((h:real^3->real^3) v)`
  ASSUME_TAC THENL
   [USE_THEN "off" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(z:real^3) IN X INTER (c:real^3->real^3->bool) v` THEN
    UNDISCH_TAC `(X:real^3->bool) SUBSET interior N'` THEN
    MP_TAC(ISPEC `N':real^3->bool` INTERIOR_SUBSET) THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(z:real^3) IN interior X` ASSUME_TAC THENL
   [UNDISCH_TAC `~((z:real^3) IN S)` THEN
    SUBST1_TAC(SYM(ASSUME `frontier (X:real^3->bool) = S`)) THEN
    SIMP_TAC[frontier; CLOSURE_CLOSED; ASSUME `closed (X:real^3->bool)`] THEN
    UNDISCH_TAC `(z:real^3) IN X INTER (c:real^3->real^3->bool) v` THEN SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC(SET_RULE `!z:real^3 O s. z IN O /\ O SUBSET interior s ==> z IN interior s`) THEN
  EXISTS_TAC `interior X INTER
              (connected_component (N' DIFF EE) ((h:real^3->real^3) v) INTER interior N')` THEN
  CONJ_TAC THENL
   [ASM_REWRITE_TAC[IN_INTER] THEN
    UNDISCH_TAC `(z:real^3) IN X INTER (c:real^3->real^3->bool) v` THEN
    UNDISCH_TAC `(X:real^3->bool) SUBSET interior N'` THEN SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC INTERIOR_MAXIMAL THEN CONJ_TAC THENL
   [USE_THEN "vtx" (MP_TAC o C MATCH_MP (ASSUME `{v:real^3} IN l`)) THEN
    UNDISCH_TAC `interior X SUBSET (X:real^3->bool)` THEN SET_TAC[];
    MATCH_MP_TAC OPEN_INTER THEN REWRITE_TAC[OPEN_INTERIOR] THEN
    USE_THEN "pop" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);
      (X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
  EXISTS_TAC `connected_component (N' DIFF EE) ((h:real^3->real^3) v) INTER interior N'` THEN
  REPEAT CONJ_TAC THENL
   [USE_THEN "pop" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[IN_INTER] THEN CONJ_TAC THENL
     [USE_THEN "off" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(z:real^3) IN (c:real^3->real^3->bool) v INTER S` THEN
      UNDISCH_TAC `(S:real^3->bool) SUBSET interior N'` THEN
      MP_TAC(ISPEC `N':real^3->bool` INTERIOR_SUBSET) THEN SET_TAC[];
      UNDISCH_TAC `(z:real^3) IN (c:real^3->real^3->bool) v INTER S` THEN
      UNDISCH_TAC `(S:real^3->bool) SUBSET interior N'` THEN SET_TAC[]];
    USE_THEN "vtx" (MP_TAC o C MATCH_MP (ASSUME `{v:real^3} IN l`)) THEN SET_TAC[]])];
    ALL_TAC] THEN
  SIMP_TAC[]);;

