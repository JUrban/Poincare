(* ========================================================================= *)
(* pc_moi_s32_steps: Steps 2-4 of the proof of Moise 32.1 and the final     *)
(* deletion of one annulus of each even torus (GTM 47, pp.226-227).  Main   *)
(* theorem STEPS24 : |- MOI_S32_STEPS24 (pc_moi_s3032_stmt.ml;              *)
(* antecedents MOISE_301, MOISE_267 (unused), MOISE_286 and LIMIT).  The    *)
(* book does not justify the deletion of the interior of an annulus lying   *)
(* on the barrier (Step 4, final step): Parts 1-4 give the merge lemma, the *)
(* local sides of a combinatorial surface in real^3, single deletions       *)
(* against a closed surface (26.6) and the torus pieces (28.6), stated      *)
(* without tower data.                                                      *)
(* ========================================================================= *)

needs "src/pc_moi_s3032_stmt.ml";;
needs "src/pc_moi_s32_gfacts.ml";;
needs "src/pc_moi_s32_iter.ml";;
needs "src/pc_moi_s32_init.ml";;
needs "src/pc_moi_s32_cell.ml";;
needs "src/pc_moi_s31_rev.ml";;
needs "src/pc_moi_fnd_plst.ml";;
needs "src/pc_moi_s30sep.ml";;
needs "src/pc_moi_s26_cross.ml";;
needs "src/pc_moi_s26_local.ml";;
needs "src/pc_moi_s26_sep.ml";;
needs "src/pc_moi_s26_surf.ml";;
needs "src/pc_moi_s28_tria.ml";;
needs "src/pc_moi_s28_trib.ml";;
needs "src/pc_moi_s28_plane.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Part 1: the merge lemma MOI_S3ST_MERGE.  A closed set x separating a     *)
(* from b in an open m stays separating when a piece z is removed, if one   *)
(* local side of z lies in an open region oo bounded by x and avoiding a    *)
(* and b, and the other local side is connected near every point of z       *)
(* outside a finite set vv with z DIFF vv connected: the outer side of z    *)
(* meets only one side of the separation, and z joins that side together    *)
(* with oo.                                                                 *)
(* ------------------------------------------------------------------------- *)

let MOI_S3ST_SEP_OPEN = prove
 (`!(m:real^3->bool) x a b.
     open m /\ separates_in m x {a} {b}
     ==> ?u v. open u /\ open v /\ u SUBSET m /\ v SUBSET m /\ DISJOINT u v /\
               u UNION v = m DIFF x /\ a IN u /\ b IN v`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  REWRITE_TAC[separates_in] THEN ASM_SIMP_TAC[OPEN_IN_OPEN_EQ] THEN
  REWRITE_TAC[SING_SUBSET] THEN MESON_TAC[]);;

let MOI_S3ST_SEP_INTRO = prove
 (`!(m:real^3->bool) x a b u v.
     open m /\ open u /\ open v /\ u SUBSET m /\ v SUBSET m /\ DISJOINT u v /\
     u UNION v = m DIFF x /\ a IN u /\ b IN v
     ==> separates_in m x {a} {b}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[separates_in] THEN
  MAP_EVERY EXISTS_TAC [`u:real^3->bool`; `v:real^3->bool`] THEN
  ASM_SIMP_TAC[OPEN_IN_OPEN_EQ; SING_SUBSET]);;

(* A component of a small ball minus x and closure oo reaches the finite-  *)
(* set-free part of z: its frontier in the ball lies in x INTER ball, which *)
(* lies in z, and a ball minus a finite set is connected.                  *)

let MOI_S3ST_ESCAPE = prove
 (`!(x:real^3->bool) z oo vv q r p.
     open oo /\ frontier oo SUBSET x /\ open (ball(q,r) DIFF x) /\
     ball(q,r) INTER x SUBSET z /\ z SUBSET x /\ FINITE vv /\ vv SUBSET z /\
     ~(ball(q,r) INTER (z DIFF vv) = {}) /\
     p IN ball(q,r) DIFF (x UNION closure oo)
     ==> ?y. y IN z DIFF vv /\ y IN ball(q,r) /\
             y IN closure (connected_component (ball(q,r) DIFF (x UNION closure oo)) p)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `gg = ball(q:real^3,r) DIFF (x UNION closure oo)` THEN
  SUBGOAL_THEN `open (gg:real^3->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "gg" THEN
    REWRITE_TAC[SET_RULE `b DIFF (x UNION c) = (b DIFF x) DIFF (c:real^3->bool)`] THEN
    MATCH_MP_TAC OPEN_DIFF THEN ASM_REWRITE_TAC[CLOSED_CLOSURE];
    ALL_TAC] THEN
  SUBGOAL_THEN `open (connected_component gg (p:real^3)) /\
                connected (connected_component gg p) /\
                p IN connected_component gg p /\ connected_component gg p SUBSET gg`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[OPEN_CONNECTED_COMPONENT; CONNECTED_CONNECTED_COMPONENT;
      CONNECTED_COMPONENT_SUBSET] THEN
    GEN_REWRITE_TAC I [IN] THEN REWRITE_TAC[CONNECTED_COMPONENT_REFL_EQ] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `w = connected_component (gg:real^3->bool) p` THEN
  SUBGOAL_THEN `(w:real^3->bool) SUBSET ball(q,r) /\ DISJOINT w x /\ DISJOINT w (closure oo)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(w:real^3->bool) SUBSET gg` THEN EXPAND_TAC "gg" THEN SET_TAC[];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[TAUT `p <=> ~ ~p`] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(ball(q:real^3,r) DIFF vv) INTER closure w SUBSET w` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_INTER; IN_DIFF] THEN X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
    ASM_CASES_TAC `(y:real^3) IN gg` THENL
     [MP_TAC(ISPECL [`gg:real^3->bool`; `p:real^3`] CLOSED_IN_CONNECTED_COMPONENT) THEN
      ASM_REWRITE_TAC[CLOSED_IN_INTER_CLOSURE] THEN
      DISCH_THEN(fun th -> ONCE_REWRITE_TAC[GSYM th]) THEN ASM_REWRITE_TAC[IN_INTER];
      ALL_TAC] THEN
    ASM_CASES_TAC `(y:real^3) IN oo` THENL
     [SUBGOAL_THEN `~((oo:real^3->bool) INTER w = {})` MP_TAC THENL
       [MP_TAC(ISPECL [`oo:real^3->bool`; `w:real^3->bool`] OPEN_INTER_CLOSURE_EQ_EMPTY) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
        REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN EXISTS_TAC `y:real^3` THEN
        ASM_REWRITE_TAC[];
        MP_TAC(ISPEC `oo:real^3->bool` CLOSURE_SUBSET) THEN
        UNDISCH_TAC `DISJOINT (w:real^3->bool) (closure oo)` THEN SET_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `(y:real^3) IN x` ASSUME_TAC THENL
     [UNDISCH_TAC `~((y:real^3) IN gg)` THEN EXPAND_TAC "gg" THEN
      REWRITE_TAC[IN_DIFF; IN_UNION] THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `frontier oo SUBSET (x:real^3->bool)` THEN
      ASM_SIMP_TAC[frontier; INTERIOR_OPEN] THEN
      UNDISCH_TAC `~((y:real^3) IN oo)` THEN SET_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:real^3` o REWRITE_RULE[NOT_EXISTS_THM]) THEN
    ASM_REWRITE_TAC[IN_DIFF] THEN
    UNDISCH_TAC `ball(q:real^3,r) INTER x SUBSET z` THEN
    UNDISCH_TAC `(y:real^3) IN ball(q,r)` THEN UNDISCH_TAC `(y:real^3) IN x` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `connected (ball(q:real^3,r) DIFF vv)` ASSUME_TAC THENL
   [MATCH_MP_TAC CONNECTED_OPEN_DIFF_COUNTABLE THEN
    ASM_SIMP_TAC[FINITE_IMP_COUNTABLE; OPEN_BALL; CONNECTED_BALL; DIMINDEX_3; ARITH];
    ALL_TAC] THEN
  SUBGOAL_THEN `DISJOINT (w:real^3->bool) vv` ASSUME_TAC THENL
   [UNDISCH_TAC `DISJOINT (w:real^3->bool) x` THEN UNDISCH_TAC `vv SUBSET (z:real^3->bool)` THEN
    UNDISCH_TAC `(z:real^3->bool) SUBSET x` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(w:real^3->bool) = ball(q,r) DIFF vv` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [CONNECTED_CLOPEN] o check
      (fun th -> concl th = `connected (ball(q:real^3,r) DIFF vv)`)) THEN
    DISCH_THEN(MP_TAC o SPEC `w:real^3->bool`) THEN ANTS_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC OPEN_SUBSET THEN ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `(w:real^3->bool) SUBSET ball(q,r)` THEN
        UNDISCH_TAC `DISJOINT (w:real^3->bool) vv` THEN SET_TAC[];
        REWRITE_TAC[CLOSED_IN_INTER_CLOSURE] THEN
        MP_TAC(ISPEC `w:real^3->bool` CLOSURE_SUBSET) THEN
        UNDISCH_TAC `(ball(q:real^3,r) DIFF vv) INTER closure w SUBSET w` THEN
        UNDISCH_TAC `(w:real^3->bool) SUBSET ball(q,r)` THEN
        UNDISCH_TAC `DISJOINT (w:real^3->bool) vv` THEN SET_TAC[]];
      UNDISCH_TAC `(p:real^3) IN w` THEN SET_TAC[]];
    ALL_TAC] THEN
  UNDISCH_TAC `~(ball(q:real^3,r) INTER (z DIFF vv) = {})` THEN
  UNDISCH_TAC `(w:real^3->bool) = ball(q,r) DIFF vv` THEN
  UNDISCH_TAC `DISJOINT (w:real^3->bool) x` THEN
  UNDISCH_TAC `(z:real^3->bool) SUBSET x` THEN SET_TAC[]);;

let MOI_S3ST_CONN_SIDE = prove
 (`!s u v:real^3->bool.
     connected s /\ open u /\ open v /\ DISJOINT u v /\ s SUBSET u UNION v /\
     ~(s INTER v = {})
     ==> s SUBSET v`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [CONNECTED]) THEN
  REWRITE_TAC[NOT_EXISTS_THM] THEN
  DISCH_THEN(MP_TAC o SPECL [`u:real^3->bool`; `v:real^3->bool`]) THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `DISJOINT (u:real^3->bool) v` THEN UNDISCH_TAC `(s:real^3->bool) SUBSET u UNION v` THEN
  UNDISCH_TAC `~((s:real^3->bool) INTER v = {})` THEN SET_TAC[]);;

let MOI_S3ST_OPEN_DIFF_CLOSED_IN = prove
 (`!(m:real^3->bool) x. open m /\ closed_in (subtopology euclidean m) x ==> open (m DIFF x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CLOSED_IN_CLOSED] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[SET_RULE `m DIFF (m INTER f) = m DIFF (f:real^3->bool)`] THEN
  MATCH_MP_TAC OPEN_DIFF THEN ASM_REWRITE_TAC[]);;

(* Half of the merge lemma: the side of v does not touch the free part of  *)
(* z from outside closure oo; then z goes with u and oo.                   *)

let MOI_S3ST_MERGE_HALF = prove
 (`!(m:real^3->bool) x z oo vv a b u v.
     open m /\ closed_in (subtopology euclidean m) x /\ z SUBSET x /\
     closed_in (subtopology euclidean m) (x DIFF z) /\
     open u /\ open v /\ u SUBSET m /\ v SUBSET m /\ DISJOINT u v /\
     u UNION v = m DIFF x /\ a IN u /\ b IN v /\
     open oo /\ frontier oo SUBSET x /\ ~(b IN closure oo) /\
     FINITE vv /\ vv SUBSET z /\ z SUBSET closure (z DIFF vv) /\
     (z DIFF vv) INTER closure ((m DIFF (x UNION closure oo)) INTER v) = {}
     ==> separates_in m (x DIFF z) {a} {b}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `gg = m DIFF (x UNION closure oo:real^3->bool)` THEN
  SUBGOAL_THEN `(x:real^3->bool) SUBSET m` ASSUME_TAC THENL
   [FIRST_ASSUM(MATCH_ACCEPT_TAC o MATCH_MP CLOSED_IN_IMP_SUBSET); ALL_TAC] THEN
  SUBGOAL_THEN `open (m DIFF x:real^3->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S3ST_OPEN_DIFF_CLOSED_IN THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `closure oo DIFF x SUBSET (oo:real^3->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `frontier oo SUBSET (x:real^3->bool)` THEN
    ASM_SIMP_TAC[frontier; INTERIOR_OPEN] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!q:real^3. q IN z ==> ?r. &0 < r /\ ball(q,r) SUBSET m /\
                                          ball(q,r) INTER (x DIFF z) = {}`
  (LABEL_TAC "nb") THENL
   [X_GEN_TAC `q:real^3` THEN DISCH_TAC THEN
    UNDISCH_TAC `closed_in (subtopology euclidean m) (x DIFF z:real^3->bool)` THEN
    REWRITE_TAC[CLOSED_IN_CLOSED] THEN
    DISCH_THEN(X_CHOOSE_THEN `f:real^3->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(q:real^3) IN m DIFF f` MP_TAC THENL
     [UNDISCH_TAC `(x:real^3->bool) DIFF z = m INTER f` THEN
      UNDISCH_TAC `(q:real^3) IN z` THEN UNDISCH_TAC `(z:real^3->bool) SUBSET x` THEN
      UNDISCH_TAC `(x:real^3->bool) SUBSET m` THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `open (m DIFF f:real^3->bool)` MP_TAC THENL
     [MATCH_MP_TAC OPEN_DIFF THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[OPEN_CONTAINS_BALL] THEN DISCH_THEN(MP_TAC o SPEC `q:real^3`) THEN
    MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC `r:real` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `ball(q:real^3,r) SUBSET m DIFF f` THEN
    UNDISCH_TAC `(x:real^3->bool) DIFF z = m INTER f` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!q:real^3. q IN z ==> ~(q IN closure (gg INTER v))` (LABEL_TAC "nv") THENL
   [X_GEN_TAC `q:real^3` THEN DISCH_TAC THEN
    ASM_CASES_TAC `(q:real^3) IN vv` THENL
     [ALL_TAC;
      UNDISCH_TAC `(z DIFF vv) INTER closure (gg INTER v:real^3->bool) = {}` THEN
      UNDISCH_TAC `~((q:real^3) IN vv)` THEN UNDISCH_TAC `(q:real^3) IN z` THEN SET_TAC[]] THEN
    DISCH_TAC THEN
    USE_THEN "nb" (MP_TAC o C MATCH_MP (ASSUME `(q:real^3) IN z`)) THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `?p:real^3. p IN ball(q,r) /\ p IN gg INTER v` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(q:real^3) IN closure (gg INTER v)` THEN
      REWRITE_TAC[CLOSURE_APPROACHABLE; IN_BALL] THEN
      DISCH_THEN(MP_TAC o SPEC `r:real`) THEN ASM_REWRITE_TAC[] THEN MESON_TAC[DIST_SYM];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`x:real^3->bool`; `z:real^3->bool`; `oo:real^3->bool`; `vv:real^3->bool`;
                   `q:real^3`; `r:real`; `p:real^3`] MOI_S3ST_ESCAPE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [SUBGOAL_THEN `ball(q:real^3,r) DIFF x = ball(q,r) INTER (m DIFF x)` SUBST1_TAC THENL
         [UNDISCH_TAC `ball(q:real^3,r) SUBSET m` THEN SET_TAC[]; ALL_TAC] THEN
        MATCH_MP_TAC OPEN_INTER THEN ASM_REWRITE_TAC[OPEN_BALL];
        UNDISCH_TAC `ball(q:real^3,r) INTER (x DIFF z) = {}` THEN SET_TAC[];
        MP_TAC(SET_RULE `(q:real^3) IN z /\ z SUBSET closure (z DIFF vv)
                         ==> q IN closure (z DIFF vv)`) THEN
        ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[CLOSURE_APPROACHABLE; GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_BALL] THEN
        DISCH_THEN(MP_TAC o SPEC `r:real`) THEN ASM_REWRITE_TAC[] THEN MESON_TAC[DIST_SYM];
        UNDISCH_TAC `(p:real^3) IN gg INTER v` THEN EXPAND_TAC "gg" THEN
        UNDISCH_TAC `(p:real^3) IN ball(q,r)` THEN SET_TAC[]];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
    ABBREV_TAC `w = connected_component (ball(q:real^3,r) DIFF (x UNION closure oo)) p` THEN
    SUBGOAL_THEN `(w:real^3->bool) SUBSET gg` ASSUME_TAC THENL
     [EXPAND_TAC "w" THEN MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `ball(q:real^3,r) DIFF (x UNION closure oo)` THEN
      REWRITE_TAC[CONNECTED_COMPONENT_SUBSET] THEN EXPAND_TAC "gg" THEN
      UNDISCH_TAC `ball(q:real^3,r) SUBSET m` THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(w:real^3->bool) SUBSET v` ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_S3ST_CONN_SIDE THEN EXISTS_TAC `u:real^3->bool` THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [EXPAND_TAC "w" THEN REWRITE_TAC[CONNECTED_CONNECTED_COMPONENT];
        UNDISCH_TAC `(w:real^3->bool) SUBSET gg` THEN EXPAND_TAC "gg" THEN
        UNDISCH_TAC `(u:real^3->bool) UNION v = m DIFF x` THEN SET_TAC[];
        REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN EXISTS_TAC `p:real^3` THEN
        CONJ_TAC THENL
         [EXPAND_TAC "w" THEN GEN_REWRITE_TAC I [IN] THEN
          REWRITE_TAC[CONNECTED_COMPONENT_REFL_EQ] THEN
          UNDISCH_TAC `(p:real^3) IN gg INTER v` THEN EXPAND_TAC "gg" THEN
          UNDISCH_TAC `(p:real^3) IN ball(q,r)` THEN SET_TAC[];
          UNDISCH_TAC `(p:real^3) IN gg INTER v` THEN SET_TAC[]]];
      ALL_TAC] THEN
    UNDISCH_TAC `(z DIFF vv) INTER closure (gg INTER v:real^3->bool) = {}` THEN
    MP_TAC(ISPECL [`w:real^3->bool`; `gg INTER v:real^3->bool`] SUBSET_CLOSURE) THEN
    ANTS_TAC THENL
     [UNDISCH_TAC `(w:real^3->bool) SUBSET gg` THEN UNDISCH_TAC `(w:real^3->bool) SUBSET v` THEN
      SET_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `(y:real^3) IN z DIFF vv` THEN UNDISCH_TAC `(y:real^3) IN closure w` THEN
    SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_S3ST_SEP_INTRO THEN
  MAP_EVERY EXISTS_TAC [`u UNION z UNION (oo INTER (m DIFF x)):real^3->bool`;
                        `v DIFF closure oo:real^3->bool`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[OPEN_CONTAINS_BALL] THEN X_GEN_TAC `w:real^3` THEN
    REWRITE_TAC[IN_UNION] THEN STRIP_TAC THENL
     [UNDISCH_TAC `open (u:real^3->bool)` THEN REWRITE_TAC[OPEN_CONTAINS_BALL] THEN
      DISCH_THEN(MP_TAC o SPEC `w:real^3`) THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC MONO_EXISTS THEN SET_TAC[];
      USE_THEN "nb" (MP_TAC o C MATCH_MP (ASSUME `(w:real^3) IN z`)) THEN
      DISCH_THEN(X_CHOOSE_THEN `r1:real` STRIP_ASSUME_TAC) THEN
      USE_THEN "nv" (MP_TAC o C MATCH_MP (ASSUME `(w:real^3) IN z`)) THEN
      REWRITE_TAC[CLOSURE_APPROACHABLE; NOT_FORALL_THM; NOT_IMP; NOT_EXISTS_THM] THEN
      DISCH_THEN(X_CHOOSE_THEN `r2:real` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `min r1 r2` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
      REWRITE_TAC[SUBSET; IN_BALL; REAL_LT_MIN; IN_UNION] THEN
      X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
      SUBGOAL_THEN `(y:real^3) IN ball(w,r1)` ASSUME_TAC THENL
       [ASM_REWRITE_TAC[IN_BALL]; ALL_TAC] THEN
      ASM_CASES_TAC `(y:real^3) IN x` THENL
       [DISJ2_TAC THEN DISJ1_TAC THEN
        UNDISCH_TAC `ball(w:real^3,r1) INTER (x DIFF z) = {}` THEN
        UNDISCH_TAC `(y:real^3) IN ball(w,r1)` THEN UNDISCH_TAC `(y:real^3) IN x` THEN SET_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `(y:real^3) IN u \/ (y:real^3) IN v` MP_TAC THENL
       [UNDISCH_TAC `(u:real^3->bool) UNION v = m DIFF x` THEN
        UNDISCH_TAC `ball(w:real^3,r1) SUBSET m` THEN UNDISCH_TAC `(y:real^3) IN ball(w,r1)` THEN
        UNDISCH_TAC `~((y:real^3) IN x)` THEN SET_TAC[];
        ALL_TAC] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN DISJ2_TAC THEN DISJ2_TAC THEN
      SUBGOAL_THEN `~((y:real^3) IN gg)` MP_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o SPEC `y:real^3` o check (fun th -> is_forall (concl th) &&
          can (find_term ((=) `r2:real`)) (concl th))) THEN
        REWRITE_TAC[IN_INTER] THEN ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      EXPAND_TAC "gg" THEN
      UNDISCH_TAC `closure oo DIFF x SUBSET (oo:real^3->bool)` THEN
      UNDISCH_TAC `(y:real^3) IN v` THEN UNDISCH_TAC `(v:real^3->bool) SUBSET m` THEN
      UNDISCH_TAC `~((y:real^3) IN x)` THEN SET_TAC[];
      SUBGOAL_THEN `open (oo INTER (m DIFF x):real^3->bool)` MP_TAC THENL
       [MATCH_MP_TAC OPEN_INTER THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[OPEN_CONTAINS_BALL] THEN DISCH_THEN(MP_TAC o SPEC `w:real^3`) THEN
      ASM_REWRITE_TAC[IN_INTER] THEN MATCH_MP_TAC MONO_EXISTS THEN SET_TAC[]];
    MATCH_MP_TAC OPEN_DIFF THEN ASM_REWRITE_TAC[CLOSED_CLOSURE];
    UNDISCH_TAC `(u:real^3->bool) SUBSET m` THEN UNDISCH_TAC `(z:real^3->bool) SUBSET x` THEN
    UNDISCH_TAC `(x:real^3->bool) SUBSET m` THEN SET_TAC[];
    UNDISCH_TAC `(v:real^3->bool) SUBSET m` THEN SET_TAC[];
    UNDISCH_TAC `DISJOINT (u:real^3->bool) v` THEN UNDISCH_TAC `(z:real^3->bool) SUBSET x` THEN
    UNDISCH_TAC `(u:real^3->bool) UNION v = m DIFF x` THEN
    MP_TAC(ISPEC `oo:real^3->bool` CLOSURE_SUBSET) THEN SET_TAC[];
    UNDISCH_TAC `(u:real^3->bool) UNION v = m DIFF x` THEN UNDISCH_TAC `(z:real^3->bool) SUBSET x` THEN
    UNDISCH_TAC `(x:real^3->bool) SUBSET m` THEN
    UNDISCH_TAC `closure oo DIFF x SUBSET (oo:real^3->bool)` THEN
    MP_TAC(ISPEC `oo:real^3->bool` CLOSURE_SUBSET) THEN SET_TAC[];
    ASM_REWRITE_TAC[IN_UNION];
    ASM_REWRITE_TAC[IN_DIFF]]);;

let MOI_S3ST_SEP_SWAP = prove
 (`!(m:real^3->bool) c s t. separates_in m c t s ==> separates_in m c s t`,
  REWRITE_TAC[separates_in] THEN MESON_TAC[DISJOINT_SYM; UNION_COMM]);;

(* The merge lemma.  Deleting from a closed separating set x of the open  *)
(* set m a piece z, one of whose local sides lies in an open region oo     *)
(* bounded by x and avoiding the two points, keeps the separation: the     *)
(* outer local side of z (outside x and closure oo) meets only one side of *)
(* the separation, since z minus the finite set vv is connected.           *)

let MOI_S3ST_MERGE = prove
 (`!(m:real^3->bool) x z oo vv a b.
     open m /\ closed_in (subtopology euclidean m) x /\ z SUBSET x /\
     closed_in (subtopology euclidean m) (x DIFF z) /\
     separates_in m x {a} {b} /\
     open oo /\ frontier oo SUBSET x /\ ~(a IN closure oo) /\ ~(b IN closure oo) /\
     FINITE vv /\ vv SUBSET z /\ connected (z DIFF vv) /\ z SUBSET closure (z DIFF vv) /\
     (!y. y IN z DIFF vv
          ==> y IN closure (m DIFF (x UNION closure oo)) /\
              !e. &0 < e ==> ?n. open n /\ y IN n /\ n SUBSET ball(y,e) /\
                                 connected (n DIFF (x UNION closure oo)))
     ==> separates_in m (x DIFF z) {a} {b}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`m:real^3->bool`; `x:real^3->bool`; `a:real^3`; `b:real^3`]
    MOI_S3ST_SEP_OPEN) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^3->bool` (X_CHOOSE_THEN `v:real^3->bool`
    STRIP_ASSUME_TAC)) THEN
  ABBREV_TAC `gg = m DIFF (x UNION closure oo:real^3->bool)` THEN
  SUBGOAL_THEN `((z DIFF vv) INTER closure (gg INTER u:real^3->bool)) UNION
                ((z DIFF vv) INTER closure (gg INTER v:real^3->bool)) = z DIFF vv`
  ASSUME_TAC THENL
   [MATCH_MP_TAC(SET_RULE
     `(!y:real^3. y IN d ==> y IN c1 \/ y IN c2) ==> (d INTER c1) UNION (d INTER c2) = d`) THEN
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(y:real^3) IN closure gg` MP_TAC THENL
     [EXPAND_TAC "gg" THEN FIRST_X_ASSUM(MP_TAC o SPEC `y:real^3` o check (fun th ->
        is_forall (concl th) && can (find_term ((=) `connected:(real^3->bool)->bool`)) (concl th))) THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `closure (gg:real^3->bool) = closure (gg INTER u) UNION closure (gg INTER v)`
      (fun th -> REWRITE_TAC[th; IN_UNION]) THEN
    REWRITE_TAC[GSYM CLOSURE_UNION] THEN AP_TERM_TAC THEN EXPAND_TAC "gg" THEN
    UNDISCH_TAC `(u:real^3->bool) UNION v = m DIFF x` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `((z DIFF vv) INTER closure (gg INTER u:real^3->bool)) INTER
                ((z DIFF vv) INTER closure (gg INTER v:real^3->bool)) = {}`
  ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN X_GEN_TAC `y:real^3` THEN
    STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:real^3` o check (fun th -> is_forall (concl th) &&
      can (find_term ((=) `connected:(real^3->bool)->bool`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT2) THEN
    SUBGOAL_THEN `?e. &0 < e /\ ball(y:real^3,e) SUBSET m` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `open (m:real^3->bool)` THEN REWRITE_TAC[OPEN_CONTAINS_BALL] THEN
      DISCH_THEN MATCH_MP_TAC THEN
      SUBGOAL_THEN `(x:real^3->bool) SUBSET m` MP_TAC THENL
       [FIRST_ASSUM(MATCH_ACCEPT_TAC o MATCH_MP CLOSED_IN_IMP_SUBSET); ALL_TAC] THEN
      UNDISCH_TAC `(y:real^3) IN z DIFF vv` THEN UNDISCH_TAC `(z:real^3->bool) SUBSET x` THEN
      SET_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `n:real^3->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `n DIFF (x UNION closure oo) = n INTER (gg:real^3->bool)` SUBST_ALL_TAC THENL
     [EXPAND_TAC "gg" THEN UNDISCH_TAC `n SUBSET ball(y:real^3,e)` THEN
      UNDISCH_TAC `ball(y:real^3,e) SUBSET m` THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `~(n INTER gg INTER (u:real^3->bool) = {}) /\
                  ~(n INTER gg INTER (v:real^3->bool) = {})` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN REWRITE_TAC[INTER_ASSOC] THENL
       [MP_TAC(ISPECL [`n:real^3->bool`; `gg INTER u:real^3->bool`]
          OPEN_INTER_CLOSURE_EQ_EMPTY);
        MP_TAC(ISPECL [`n:real^3->bool`; `gg INTER v:real^3->bool`]
          OPEN_INTER_CLOSURE_EQ_EMPTY)] THEN
      ASM_REWRITE_TAC[GSYM INTER_ASSOC] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN EXISTS_TAC `y:real^3` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `n INTER gg SUBSET (v:real^3->bool)` MP_TAC THENL
     [MATCH_MP_TAC MOI_S3ST_CONN_SIDE THEN EXISTS_TAC `u:real^3->bool` THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `~(n INTER gg INTER (v:real^3->bool) = {})` THEN
      UNDISCH_TAC `(u:real^3->bool) UNION v = m DIFF x` THEN
      EXPAND_TAC "gg" THEN SET_TAC[];
      UNDISCH_TAC `~(n INTER gg INTER (u:real^3->bool) = {})` THEN
      UNDISCH_TAC `DISJOINT (u:real^3->bool) v` THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(z DIFF vv) INTER closure (gg INTER u:real^3->bool) = {} \/
                (z DIFF vv) INTER closure (gg INTER v:real^3->bool) = {}` MP_TAC THENL
   [UNDISCH_TAC `connected (z DIFF vv:real^3->bool)` THEN
    REWRITE_TAC[CONNECTED_CLOSED_IN_EQ; NOT_EXISTS_THM] THEN
    DISCH_THEN(MP_TAC o SPECL [`(z DIFF vv) INTER closure (gg INTER u:real^3->bool)`;
                               `(z DIFF vv) INTER closure (gg INTER v:real^3->bool)`]) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[CLOSED_IN_CLOSED_INTER; CLOSED_CLOSURE] THEN
    CONV_TAC TAUT;
    ALL_TAC] THEN
  STRIP_TAC THENL
   [MATCH_MP_TAC MOI_S3ST_SEP_SWAP THEN MATCH_MP_TAC MOI_S3ST_MERGE_HALF THEN
    MAP_EVERY EXISTS_TAC [`oo:real^3->bool`; `vv:real^3->bool`; `v:real^3->bool`;
                          `u:real^3->bool`] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `DISJOINT (u:real^3->bool) v` THEN UNDISCH_TAC `(u:real^3->bool) UNION v = m DIFF x` THEN
    SET_TAC[];
    MATCH_MP_TAC MOI_S3ST_MERGE_HALF THEN
    MAP_EVERY EXISTS_TAC [`oo:real^3->bool`; `vv:real^3->bool`; `u:real^3->bool`;
                          `v:real^3->bool`] THEN
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Part 2: local sides of a finite combinatorial surface with               *)
(* boundary in real^3 at its interior points that are not vertices (the     *)
(* relative interior of a triangle: LOCAL_TRI; of an edge, which then lies  *)
(* in exactly two triangles: LOCAL_EDGE), and a surface that is locally the *)
(* plane stays connected, and dense in itself, after removing a finite set. *)
(* ------------------------------------------------------------------------- *)

let MOI_S3ST_RELINT_COVER = prove
 (`!(c:(real^N->bool)->bool) y.
     simplicial_complex c /\ y IN UNIONS c ==> ?s. s IN c /\ y IN relative_interior s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[simplicial_complex; IN_UNIONS] THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC
    (X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`t:real^N->bool`; `y:real^N`] IN_RELATIVE_INTERIOR_OF_FACE) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[SIMPLEX_IMP_CONVEX]; ALL_TAC] THEN
  ASM_MESON_TAC[]);;

let MOI_S3ST_LOCAL_SIDES = prove
 (`!(cc:(real^3->bool)->bool) y.
     FINITE cc /\ combinatorial_manifold_with_boundary 2 cc /\
     y IN UNIONS cc /\ ~(y IN surface_boundary cc) /\ ~({y} IN cc)
     ==> ?r0. &0 < r0 /\
              !r. &0 < r /\ r <= r0
                  ==> ?u v. open u /\ open v /\ connected u /\ connected v /\
                            DISJOINT u v /\ u UNION v = ball(y,r) DIFF UNIONS cc /\
                            y IN closure u /\ y IN closure v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `cc:(real^3->bool)->bool` MOI_S8TA_CMB_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `cc:(real^3->bool)->bool` MOI_S8TA_CMB_DIM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`cc:(real^3->bool)->bool`; `y:real^3`] MOI_S3ST_RELINT_COVER) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real^3->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(y:real^3) IN s` ASSUME_TAC THENL
   [ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `aff_dim (s:real^3->bool) = &1 \/ aff_dim s = &2` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `~(aff_dim (s:real^3->bool) = -- &1) /\ ~(aff_dim s = &0) /\
                  aff_dim s <= &2` MP_TAC THENL
     [REPEAT CONJ_TAC THENL
       [REWRITE_TAC[AFF_DIM_EQ_MINUS1] THEN ASM SET_TAC[];
        REWRITE_TAC[AFF_DIM_EQ_0] THEN DISCH_THEN(X_CHOOSE_THEN `w:real^3` SUBST_ALL_TAC) THEN
        UNDISCH_TAC `(y:real^3) IN {w}` THEN REWRITE_TAC[IN_SING] THEN
        DISCH_THEN SUBST_ALL_TAC THEN ASM_MESON_TAC[];
        ASM_MESON_TAC[]];
      MP_TAC(ISPEC `s:real^3->bool` AFF_DIM_GE) THEN INT_ARITH_TAC];
    MP_TAC(ISPECL [`cc:(real^3->bool)->bool`; `s:real^3->bool`] MOI_S8TB_EDGE_CARD) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN GEN_TAC THEN DISCH_TAC THEN
      MATCH_MP_TAC MOI_S8TA_CMB_CHART2 THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    STRIP_TAC THENL
     [UNDISCH_TAC `~((y:real^3) IN surface_boundary cc)` THEN
      MATCH_MP_TAC(TAUT `p ==> ~p ==> q`) THEN
      REWRITE_TAC[surface_boundary; IN_UNIONS; IN_ELIM_THM] THEN
      EXISTS_TAC `s:real^3->bool` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `{t | t IN cc /\ aff_dim t = &2 /\ (s:real^3->bool) SUBSET t} HAS_SIZE 2`
    MP_TAC THENL
     [ASM_REWRITE_TAC[HAS_SIZE] THEN
      MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `cc:(real^3->bool)->bool` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      ALL_TAC] THEN
    CONV_TAC(LAND_CONV HAS_SIZE_CONV) THEN
    DISCH_THEN(X_CHOOSE_THEN `q:real^3->bool` (X_CHOOSE_THEN `q':real^3->bool`
      STRIP_ASSUME_TAC)) THEN
    MP_TAC(ISPECL [`cc:(real^3->bool)->bool`; `s:real^3->bool`; `q:real^3->bool`;
                   `q':real^3->bool`; `y:real^3`] LOCAL_EDGE) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `r0:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `r0:real` THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `r:real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `r:real`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `u:real^3->bool` (X_CHOOSE_THEN `v:real^3->bool` STRIP_ASSUME_TAC))) THEN
    MAP_EVERY EXISTS_TAC [`u:real^3->bool`; `v:real^3->bool`] THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(s:real^3->bool) SUBSET q` ASSUME_TAC THENL
     [UNDISCH_TAC `{t | t IN cc /\ aff_dim t = &2 /\ (s:real^3->bool) SUBSET t} = {q,q'}` THEN
      REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY] THEN
      DISCH_THEN(MP_TAC o SPEC `q:real^3->bool`) THEN SIMP_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `ball(y:real^3,r) INTER UNIONS cc = ball(y,r) INTER (q UNION q')` THEN
      UNDISCH_TAC `(u:real^3->bool) UNION v = ball(y,r) DIFF (q UNION q')` THEN SET_TAC[];
      UNDISCH_TAC `ball(y:real^3,r) INTER (q UNION q') SUBSET closure u INTER closure v` THEN
      MP_TAC(ISPECL [`y:real^3`; `r:real`] CENTRE_IN_BALL) THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(y:real^3) IN s` THEN UNDISCH_TAC `(s:real^3->bool) SUBSET q` THEN
      SET_TAC[]];
    MP_TAC(ISPECL [`cc:(real^3->bool)->bool`; `s:real^3->bool`; `y:real^3`] LOCAL_TRI) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `r0:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `r0:real` THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `r:real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `r:real`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `u:real^3->bool` (X_CHOOSE_THEN `v:real^3->bool` STRIP_ASSUME_TAC))) THEN
    MAP_EVERY EXISTS_TAC [`u:real^3->bool`; `v:real^3->bool`] THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `ball(y:real^3,r) INTER UNIONS cc = ball(y,r) INTER affine hull s` THEN
      UNDISCH_TAC `(u:real^3->bool) UNION v = ball(y,r) DIFF affine hull s` THEN SET_TAC[];
      UNDISCH_TAC `ball(y:real^3,r) INTER affine hull s SUBSET closure u INTER closure v` THEN
      MP_TAC(ISPECL [`y:real^3`; `r:real`] CENTRE_IN_BALL) THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`affine:(real^3->bool)->bool`; `s:real^3->bool`] HULL_SUBSET) THEN
      UNDISCH_TAC `(y:real^3) IN s` THEN SET_TAC[]]]);;

(* A connected set that is locally the plane stays connected after removing *)
(* a finite set, and the rest is dense (PATH_CONNECTED_CONNECTED_DIFF).     *)

let MOI_S3ST_MANIFOLD_DIFF_FINITE = prove
 (`!(s:real^N->bool) f.
     connected s /\ FINITE f /\
     (!y. y IN s ==> ?u. open_in (subtopology euclidean s) u /\ y IN u /\
                         u homeomorphic (:real^2))
     ==> connected (s DIFF f) /\ s SUBSET closure (s DIFF f)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!y:real^N. y IN s
                 ==> ?u. open_in (subtopology euclidean s) u /\ y IN u /\
                         path_connected (u DIFF f) /\ y IN closure (u DIFF f)`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:real^N`) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `u:real^N->bool` THEN
    REWRITE_TAC[homeomorphic; homeomorphism] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `h:real^N->real^2` (X_CHOOSE_THEN `k:real^2->real^N`
        STRIP_ASSUME_TAC)))) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(u:real^N->bool) DIFF f = IMAGE k ((:real^2) DIFF IMAGE h (u INTER f))`
    SUBST1_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `COUNTABLE (IMAGE (h:real^N->real^2) (u INTER f))` ASSUME_TAC THENL
     [MATCH_MP_TAC FINITE_IMP_COUNTABLE THEN MATCH_MP_TAC FINITE_IMAGE THEN
      ASM_SIMP_TAC[FINITE_INTER];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC PATH_CONNECTED_CONTINUOUS_IMAGE THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
        ASM_REWRITE_TAC[SUBSET_UNIV];
        MATCH_MP_TAC PATH_CONNECTED_OPEN_DIFF_COUNTABLE THEN
        ASM_REWRITE_TAC[OPEN_UNIV; CONNECTED_UNIV; DIMINDEX_2; LE_REFL]];
      ALL_TAC] THEN
    SUBGOAL_THEN `closure ((:real^2) DIFF IMAGE h (u INTER f:real^N->bool)) = (:real^2)`
    ASSUME_TAC THENL
     [ASM_SIMP_TAC[CLOSURE_COMPLEMENT; COUNTABLE_EMPTY_INTERIOR; DIFF_EMPTY]; ALL_TAC] THEN
    MP_TAC(ISPECL [`k:real^2->real^N`; `(:real^2) DIFF IMAGE h (u INTER f:real^N->bool)`;
                   `closure (IMAGE (k:real^2->real^N)
                              ((:real^2) DIFF IMAGE h (u INTER f:real^N->bool)))`]
      IMAGE_CLOSURE_SUBSET) THEN
    ASM_REWRITE_TAC[CLOSED_CLOSURE; CLOSURE_SUBSET] THEN
    MATCH_MP_TAC(SET_RULE `(y:real^N) IN u ==> u SUBSET t ==> y IN t`) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `b /\ (b ==> a) ==> a /\ b`) THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET] THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:real^N`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real^N->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(u:real^N->bool) SUBSET s` ASSUME_TAC THENL
     [ASM_MESON_TAC[OPEN_IN_IMP_SUBSET]; ALL_TAC] THEN
    MP_TAC(ISPECL [`u DIFF f:real^N->bool`; `s DIFF f:real^N->bool`] SUBSET_CLOSURE) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; ASM SET_TAC[]];
    DISCH_TAC THEN MATCH_MP_TAC PATH_CONNECTED_IMP_CONNECTED THEN
    MATCH_MP_TAC PATH_CONNECTED_CONNECTED_DIFF THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:real^N`) THEN ASM_REWRITE_TAC[] THEN MESON_TAC[]]);;

(* A chart (open subset homeomorphic to the plane) can be shrunk into any  *)
(* open neighbourhood of a point.                                            *)

let MOI_S3ST_CHART_SHRINK = prove
 (`!(t:real^N->bool) u w y.
     open_in (subtopology euclidean t) u /\ y IN u /\ u homeomorphic (:real^2) /\
     open_in (subtopology euclidean t) w /\ y IN w
     ==> ?u'. open_in (subtopology euclidean t) u' /\ y IN u' /\ u' SUBSET w /\
              u' homeomorphic (:real^2)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (X_CHOOSE_THEN `h:real^N->real^2` (X_CHOOSE_THEN `k:real^2->real^N`
      ASSUME_TAC) o REWRITE_RULE[homeomorphic]) STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `open (IMAGE (h:real^N->real^2) (u INTER w))` MP_TAC THENL
   [SUBGOAL_THEN `open_in (subtopology euclidean (:real^2)) (IMAGE (h:real^N->real^2) (u INTER w))`
    MP_TAC THENL
     [MATCH_MP_TAC HOMEOMORPHISM_IMP_OPEN_MAP THEN
      MAP_EVERY EXISTS_TAC [`k:real^2->real^N`; `u:real^N->bool`] THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC OPEN_IN_SUBSET_TRANS THEN EXISTS_TAC `t:real^N->bool` THEN
      REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC OPEN_IN_INTER THEN ASM_REWRITE_TAC[];
        SET_TAC[];
        ASM_MESON_TAC[OPEN_IN_IMP_SUBSET]];
      REWRITE_TAC[SUBTOPOLOGY_UNIV; GSYM OPEN_IN]];
    ALL_TAC] THEN
  REWRITE_TAC[OPEN_CONTAINS_BALL] THEN DISCH_THEN(MP_TAC o SPEC `(h:real^N->real^2) y`) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `IMAGE (k:real^2->real^N) (ball((h:real^N->real^2) y,e))` THEN
  SUBGOAL_THEN `homeomorphism ((:real^2),u) (k:real^2->real^N,h)` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[HOMEOMORPHISM_SYM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_IN_TRANS THEN EXISTS_TAC `u:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC HOMEOMORPHISM_IMP_OPEN_MAP THEN
    MAP_EVERY EXISTS_TAC [`h:real^N->real^2`; `(:real^2)`] THEN
    ASM_REWRITE_TAC[SUBTOPOLOGY_UNIV; GSYM OPEN_IN; OPEN_BALL];
    REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `(h:real^N->real^2) y` THEN
    REWRITE_TAC[CENTRE_IN_BALL] THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `homeomorphism (u,(:real^2)) (h:real^N->real^2,k)` THEN
    REWRITE_TAC[homeomorphism] THEN ASM_MESON_TAC[];
    UNDISCH_TAC `ball((h:real^N->real^2) y,e) SUBSET IMAGE h (u INTER w)` THEN
    UNDISCH_TAC `homeomorphism (u,(:real^2)) (h:real^N->real^2,k)` THEN
    REWRITE_TAC[homeomorphism] THEN SET_TAC[];
    MATCH_MP_TAC(ISPECL [`IMAGE (k:real^2->real^N) (ball((h:real^N->real^2) y,e))`;
                         `ball((h:real^N->real^2) y,e)`; `(:real^2)`] HOMEOMORPHIC_TRANS) THEN
    ASM_SIMP_TAC[HOMEOMORPHIC_BALL_UNIV] THEN
    REWRITE_TAC[homeomorphic] THEN
    MAP_EVERY EXISTS_TAC [`h:real^N->real^2`; `k:real^2->real^N`] THEN
    MATCH_MP_TAC HOMEOMORPHISM_OF_SUBSETS THEN
    MAP_EVERY EXISTS_TAC [`u:real^N->bool`; `(:real^2)`] THEN ASM_REWRITE_TAC[SUBSET_UNIV] THEN
    UNDISCH_TAC `homeomorphism (u,(:real^2)) (h:real^N->real^2,k)` THEN
    REWRITE_TAC[homeomorphism] THEN SET_TAC[]]);;

let MOI_S3ST_SB_CLOSED = prove
 (`!c:(real^N->bool)->bool. simplicial_complex c ==> closed (surface_boundary c)`,
  GEN_TAC THEN REWRITE_TAC[simplicial_complex] THEN STRIP_TAC THEN
  REWRITE_TAC[surface_boundary] THEN MATCH_MP_TAC CLOSED_UNIONS THEN CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `c:(real^N->bool)->bool` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[SIMPLEX_IMP_CLOSED]]);;

(* The interior of a finite connected combinatorial surface with boundary   *)
(* minus a finite set: connected, and dense in the interior.                *)

let MOI_S3ST_INT_DIFF_FINITE = prove
 (`!(cc:(real^N->bool)->bool) f.
     FINITE cc /\ combinatorial_manifold_with_boundary 2 cc /\ connected (UNIONS cc) /\
     FINITE f
     ==> connected ((UNIONS cc DIFF surface_boundary cc) DIFF f) /\
         (UNIONS cc DIFF surface_boundary cc) SUBSET
         closure ((UNIONS cc DIFF surface_boundary cc) DIFF f)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC MOI_S3ST_MANIFOLD_DIFF_FINITE THEN
  ASM_SIMP_TAC[INT_CONNECTED] THEN
  X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
  MP_TAC(ISPEC `cc:(real^N->bool)->bool` SURF_CHARTS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `y:real^N` o CONJUNCT1) THEN ASM_REWRITE_TAC[moi_s28_locally_r2] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `closed (surface_boundary (cc:(real^N->bool)->bool))` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S3ST_SB_CLOSED THEN ASM_MESON_TAC[MOI_S8TA_CMB_FACTS]; ALL_TAC] THEN
  MP_TAC(ISPECL [`UNIONS cc:real^N->bool`; `u:real^N->bool`;
                 `UNIONS cc DIFF surface_boundary (cc:(real^N->bool)->bool)`; `y:real^N`]
    MOI_S3ST_CHART_SHRINK) THEN
  ASM_SIMP_TAC[OPEN_IN_DIFF_CLOSED] THEN
  DISCH_THEN(X_CHOOSE_THEN `u':real^N->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `u':real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC OPEN_IN_SUBSET_TRANS THEN EXISTS_TAC `UNIONS cc:real^N->bool` THEN
  ASM_REWRITE_TAC[] THEN SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Part 3: single deletion SD.  The interior z of a finite                  *)
(* combinatorial surface with boundary lying on a closed separating set x   *)
(* can be deleted if the surface is part of a closed connected              *)
(* combinatorial surface e in x with both points outside e: by 26.6 one     *)
(* side of z is the bounded component of the complement of e, the other     *)
(* lies in the outside, and the merge lemma applies.                        *)
(* ------------------------------------------------------------------------- *)

let MOI_S3ST_266 = REWRITE_RULE[MOISE_266_STATEMENT]
  (MP SEP_266 (CONJ EVEN_CROSSING (CONJ LOCAL_TRI LOCAL_EDGE)));;

let MOI_S3ST_TWO_COMP_SIDE = prove
 (`!(k:real^3->bool) b u.
     closed k /\ components ((:real^3) DIFF k) = {b, outside k} /\ ~(b = outside k) /\
     connected u /\ u SUBSET (:real^3) DIFF k
     ==> u SUBSET b \/ u SUBSET outside k`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `open (b:real^3->bool) /\ open (outside k:real^3->bool)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC OPEN_COMPONENTS THEN
    EXISTS_TAC `(:real^3) DIFF k` THEN ASM_SIMP_TAC[GSYM closed; IN_INSERT];
    ALL_TAC] THEN
  SUBGOAL_THEN `DISJOINT (b:real^3->bool) (outside k)` ASSUME_TAC THENL
   [REWRITE_TAC[DISJOINT] THEN
    MP_TAC(ISPECL [`(:real^3) DIFF k`; `b:real^3->bool`; `outside k:real^3->bool`]
      COMPONENTS_NONOVERLAP) THEN
    ASM_REWRITE_TAC[IN_INSERT];
    ALL_TAC] THEN
  SUBGOAL_THEN `(:real^3) DIFF k = b UNION outside k` ASSUME_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [UNIONS_COMPONENTS] THEN
    ASM_REWRITE_TAC[UNIONS_2];
    ALL_TAC] THEN
  ASM_CASES_TAC `(u:real^3->bool) INTER b = {}` THENL
   [DISJ2_TAC THEN UNDISCH_TAC `(u:real^3->bool) SUBSET (:real^3) DIFF k` THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(u:real^3->bool) INTER b = {}` THEN SET_TAC[];
    DISJ1_TAC THEN MATCH_MP_TAC MOI_S3ST_CONN_SIDE THEN
    EXISTS_TAC `outside k:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `DISJOINT (b:real^3->bool) (outside k)` THEN
    UNDISCH_TAC `(u:real^3->bool) SUBSET (:real^3) DIFF k` THEN ASM_REWRITE_TAC[] THEN
    SET_TAC[]]);;

(* At a point y of the closed surface k (26.6), the two local sides u, v of *)
(* an open neighbourhood w lie one in the bounded component, one outside.   *)

let MOI_S3ST_SIDE_SPLIT = prove
 (`!(k:real^3->bool) bb u v w y.
     closed k /\ components ((:real^3) DIFF k) = {bb, outside k} /\ ~(bb = outside k) /\
     frontier bb = k /\ frontier (outside k) = k /\ y IN k /\
     connected u /\ connected v /\
     u SUBSET (:real^3) DIFF k /\ v SUBSET (:real^3) DIFF k /\
     open w /\ y IN w /\ w SUBSET k UNION (u UNION v)
     ==> (u SUBSET bb /\ v SUBSET outside k) \/ (v SUBSET bb /\ u SUBSET outside k)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `DISJOINT (bb:real^3->bool) (outside k) /\ DISJOINT bb k /\
                DISJOINT (outside k) (k:real^3->bool)` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REWRITE_TAC[DISJOINT] THEN
      MP_TAC(ISPECL [`(:real^3) DIFF k`; `bb:real^3->bool`; `outside k:real^3->bool`]
        COMPONENTS_NONOVERLAP) THEN
      ASM_REWRITE_TAC[IN_INSERT];
      MP_TAC(ISPECL [`(:real^3) DIFF k`; `bb:real^3->bool`] IN_COMPONENTS_SUBSET) THEN
      ASM_REWRITE_TAC[IN_INSERT] THEN SET_TAC[];
      MP_TAC(ISPEC `k:real^3->bool` OUTSIDE_NO_OVERLAP) THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!c:real^3->bool. y IN closure c ==> ~(w INTER c = {})` ASSUME_TAC THENL
   [X_GEN_TAC `c:real^3->bool` THEN REWRITE_TAC[CLOSURE_APPROACHABLE] THEN DISCH_TAC THEN
    UNDISCH_TAC `open (w:real^3->bool)` THEN REWRITE_TAC[OPEN_CONTAINS_BALL] THEN
    DISCH_THEN(MP_TAC o SPEC `y:real^3`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `r:real`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `q:real^3` STRIP_ASSUME_TAC) THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN EXISTS_TAC `q:real^3` THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `ball(y:real^3,r) SUBSET w` THEN REWRITE_TAC[SUBSET; IN_BALL] THEN
    DISCH_THEN MATCH_MP_TAC THEN ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(w INTER (bb:real^3->bool) = {}) /\ ~(w INTER outside (k:real^3->bool) = {})`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THENL
     [UNDISCH_TAC `frontier bb = (k:real^3->bool)`;
      UNDISCH_TAC `frontier (outside k) = (k:real^3->bool)`] THEN
    REWRITE_TAC[frontier] THEN UNDISCH_TAC `(y:real^3) IN k` THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:real^3->bool`; `bb:real^3->bool`; `u:real^3->bool`]
    MOI_S3ST_TWO_COMP_SIDE) THEN
  MP_TAC(ISPECL [`k:real^3->bool`; `bb:real^3->bool`; `v:real^3->bool`]
    MOI_S3ST_TWO_COMP_SIDE) THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `~(w INTER (bb:real^3->bool) = {})` THEN
  UNDISCH_TAC `~(w INTER outside (k:real^3->bool) = {})` THEN
  UNDISCH_TAC `(w:real^3->bool) SUBSET k UNION (u UNION v)` THEN
  UNDISCH_TAC `DISJOINT (bb:real^3->bool) (outside k)` THEN
  UNDISCH_TAC `DISJOINT (bb:real^3->bool) k` THEN
  UNDISCH_TAC `DISJOINT (outside k) (k:real^3->bool)` THEN
  SET_TAC[]);;

let MOI_S3ST_SD = prove
 (`!(m:real^3->bool) x cc e a b.
     open m /\ closed_in (subtopology euclidean m) x /\ separates_in m x {a} {b} /\
     FINITE cc /\ combinatorial_manifold_with_boundary 2 cc /\ connected (UNIONS cc) /\
     FINITE e /\ combinatorial_manifold 2 e /\ connected (UNIONS e) /\
     UNIONS cc SUBSET UNIONS e /\ UNIONS e SUBSET x /\
     closed (UNIONS e DIFF (UNIONS cc DIFF surface_boundary cc)) /\
     closed_in (subtopology euclidean m) (x DIFF (UNIONS cc DIFF surface_boundary cc)) /\
     a IN outside (UNIONS e) /\ b IN outside (UNIONS e)
     ==> separates_in m (x DIFF (UNIONS cc DIFF surface_boundary cc)) {a} {b}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `z = UNIONS cc DIFF surface_boundary (cc:(real^3->bool)->bool)` THEN
  ASM_CASES_TAC `UNIONS e:real^3->bool = {}` THENL
   [SUBGOAL_THEN `(z:real^3->bool) = {}` SUBST1_TAC THENL
     [EXPAND_TAC "z" THEN UNDISCH_TAC `UNIONS cc SUBSET UNIONS (e:(real^3->bool)->bool)` THEN
      REWRITE_TAC[ASSUME `UNIONS e:real^3->bool = {}`] THEN SET_TAC[];
      ASM_REWRITE_TAC[DIFF_EMPTY]];
    ALL_TAC] THEN
  SUBGOAL_THEN `closed (UNIONS e:real^3->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC CLOSED_UNIONS THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `e:(real^3->bool)->bool` MOI_S8TA_CMB_FACTS) THEN
    ASM_SIMP_TAC[MOI_S8TA_CM_CMB] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN
    REWRITE_TAC[simplicial_complex] THEN MESON_TAC[SIMPLEX_IMP_CLOSED];
    ALL_TAC] THEN
  MP_TAC(SPEC `e:(real^3->bool)->bool` MOI_S3ST_266) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `bb:real^3->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `open (bb:real^3->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC OPEN_COMPONENTS THEN EXISTS_TAC `(:real^3) DIFF UNIONS e` THEN
    ASM_SIMP_TAC[GSYM closed; IN_INSERT];
    ALL_TAC] THEN
  SUBGOAL_THEN `open (outside (UNIONS e):real^3->bool) /\
                DISJOINT bb (outside (UNIONS e):real^3->bool)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_COMPONENTS THEN EXISTS_TAC `(:real^3) DIFF UNIONS e` THEN
      ASM_SIMP_TAC[GSYM closed; IN_INSERT];
      REWRITE_TAC[DISJOINT] THEN
      MP_TAC(ISPECL [`(:real^3) DIFF UNIONS e`; `bb:real^3->bool`;
                     `outside (UNIONS e):real^3->bool`] COMPONENTS_NONOVERLAP) THEN
      ASM_REWRITE_TAC[IN_INSERT]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!c:real^3->bool. c SUBSET outside (UNIONS e) ==> DISJOINT c (closure bb)`
  (LABEL_TAC "dout") THENL
   [X_GEN_TAC `c:real^3->bool` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`outside (UNIONS e):real^3->bool`; `bb:real^3->bool`]
      OPEN_INTER_CLOSURE_EQ_EMPTY) THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `DISJOINT bb (outside (UNIONS e):real^3->bool)` THEN
    UNDISCH_TAC `(c:real^3->bool) SUBSET outside (UNIONS e)` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^3->bool) SUBSET m` ASSUME_TAC THENL
   [FIRST_ASSUM(MATCH_ACCEPT_TAC o MATCH_MP CLOSED_IN_IMP_SUBSET); ALL_TAC] THEN
  SUBGOAL_THEN `(z:real^3->bool) SUBSET x` ASSUME_TAC THENL
   [EXPAND_TAC "z" THEN UNDISCH_TAC `UNIONS cc SUBSET UNIONS (e:(real^3->bool)->bool)` THEN
    UNDISCH_TAC `UNIONS e SUBSET (x:real^3->bool)` THEN SET_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `vv = {y:real^3 | {y} IN cc} INTER z` THEN
  SUBGOAL_THEN `FINITE (vv:real^3->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "vv" THEN MATCH_MP_TAC FINITE_INTER THEN DISJ1_TAC THEN
    MP_TAC(ISPECL [`\y:real^3. {y}`; `cc:(real^3->bool)->bool`] FINITE_IMAGE_INJ) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN SET_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`cc:(real^3->bool)->bool`; `vv:real^3->bool`] MOI_S3ST_INT_DIFF_FINITE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC MOI_S3ST_MERGE THEN
  MAP_EVERY EXISTS_TAC [`bb:real^3->bool`; `vv:real^3->bool`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [USE_THEN "dout" (MP_TAC o SPEC `{a:real^3}`) THEN
    REWRITE_TAC[SING_SUBSET; ASSUME `(a:real^3) IN outside (UNIONS e)`] THEN SET_TAC[];
    USE_THEN "dout" (MP_TAC o SPEC `{b:real^3}`) THEN
    REWRITE_TAC[SING_SUBSET; ASSUME `(b:real^3) IN outside (UNIONS e)`] THEN SET_TAC[];
    EXPAND_TAC "vv" THEN SET_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(y:real^3) IN UNIONS cc /\ ~(y IN surface_boundary cc) /\ ~({y} IN cc) /\
                y IN z /\ y IN UNIONS e` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(y:real^3) IN z DIFF vv` THEN EXPAND_TAC "vv" THEN EXPAND_TAC "z" THEN
    UNDISCH_TAC `UNIONS cc SUBSET UNIONS (e:(real^3->bool)->bool)` THEN
    REWRITE_TAC[IN_DIFF; IN_INTER; IN_ELIM_THM] THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`cc:(real^3->bool)->bool`; `y:real^3`] MOI_S3ST_LOCAL_SIDES) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `r0:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `?r1. &0 < r1 /\ ball(y:real^3,r1) SUBSET m /\
                     ball(y,r1) INTER (x DIFF z) = {}` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `closed_in (subtopology euclidean m) (x DIFF z:real^3->bool)` THEN
    REWRITE_TAC[CLOSED_IN_CLOSED] THEN
    DISCH_THEN(X_CHOOSE_THEN `f:real^3->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(y:real^3) IN m DIFF f` MP_TAC THENL
     [UNDISCH_TAC `(x:real^3->bool) DIFF z = m INTER f` THEN
      UNDISCH_TAC `(y:real^3) IN z` THEN UNDISCH_TAC `(z:real^3->bool) SUBSET x` THEN
      UNDISCH_TAC `(x:real^3->bool) SUBSET m` THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `open (m DIFF f:real^3->bool)` MP_TAC THENL
     [MATCH_MP_TAC OPEN_DIFF THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[OPEN_CONTAINS_BALL] THEN DISCH_THEN(MP_TAC o SPEC `y:real^3`) THEN
    MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC `r:real` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `ball(y:real^3,r) SUBSET m DIFF f` THEN
    UNDISCH_TAC `(x:real^3->bool) DIFF z = m INTER f` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?r2. &0 < r2 /\ ball(y:real^3,r2) INTER (UNIONS e DIFF z) = {}`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `open ((:real^3) DIFF (UNIONS e DIFF z))` MP_TAC THENL
     [ASM_REWRITE_TAC[GSYM closed]; ALL_TAC] THEN
    REWRITE_TAC[OPEN_CONTAINS_BALL] THEN DISCH_THEN(MP_TAC o SPEC `y:real^3`) THEN
    ANTS_TAC THENL [UNDISCH_TAC `(y:real^3) IN z` THEN SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN SET_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `rr = min r0 (min r1 r2)` THEN
  SUBGOAL_THEN `&0 < rr /\ rr <= r0 /\ rr <= r1 /\ rr <= r2` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "rr" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!r. &0 < r /\ r <= rr
                    ==> ball(y:real^3,r) SUBSET m /\
                        connected (ball(y,r) DIFF (x UNION closure bb)) /\
                        y IN closure (ball(y,r) DIFF (x UNION closure bb))`
  (LABEL_TAC "loc") THENL
   [X_GEN_TAC `r:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `ball(y:real^3,r) SUBSET ball(y,r1) /\ ball(y,r) SUBSET ball(y,r2)`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC SUBSET_BALL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `ball(y:real^3,r) SUBSET ball(y,r1)` THEN
      UNDISCH_TAC `ball(y:real^3,r1) SUBSET m` THEN SET_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `r:real` o check (fun th -> is_forall (concl th) &&
      can (find_term ((=) `r0:real`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real^3->bool` (X_CHOOSE_THEN `v:real^3->bool`
      STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `ball(y:real^3,r) DIFF x = u UNION v` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `ball(y:real^3,r) SUBSET ball(y,r1)` THEN
      UNDISCH_TAC `ball(y:real^3,r1) INTER (x DIFF z) = {}` THEN
      UNDISCH_TAC `UNIONS cc SUBSET UNIONS (e:(real^3->bool)->bool)` THEN
      UNDISCH_TAC `UNIONS e SUBSET (x:real^3->bool)` THEN
      EXPAND_TAC "z" THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(u:real^3->bool) SUBSET (:real^3) DIFF UNIONS e /\
                  (v:real^3->bool) SUBSET (:real^3) DIFF UNIONS e` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(u:real^3->bool) UNION v = ball(y,r) DIFF UNIONS cc` THEN
      UNDISCH_TAC `ball(y:real^3,r) SUBSET ball(y,r2)` THEN
      UNDISCH_TAC `ball(y:real^3,r2) INTER (UNIONS e DIFF z) = {}` THEN
      EXPAND_TAC "z" THEN SET_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`UNIONS e:real^3->bool`; `bb:real^3->bool`; `u:real^3->bool`;
                   `v:real^3->bool`; `ball(y:real^3,r)`; `y:real^3`] MOI_S3ST_SIDE_SPLIT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[OPEN_BALL; CENTRE_IN_BALL] THEN
      UNDISCH_TAC `(u:real^3->bool) UNION v = ball(y,r) DIFF UNIONS cc` THEN
      UNDISCH_TAC `UNIONS cc SUBSET UNIONS (e:(real^3->bool)->bool)` THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `ball(y:real^3,r) DIFF (x UNION closure bb) = (u UNION v) DIFF closure bb`
    SUBST1_TAC THENL
     [UNDISCH_TAC `ball(y:real^3,r) DIFF x = u UNION v` THEN SET_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPEC `bb:real^3->bool` CLOSURE_SUBSET) THEN DISCH_TAC THEN
    DISCH_THEN(DISJ_CASES_THEN STRIP_ASSUME_TAC) THENL
     [SUBGOAL_THEN `DISJOINT (v:real^3->bool) (closure bb)` ASSUME_TAC THENL
       [USE_THEN "dout" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `(u UNION v) DIFF closure bb = (v:real^3->bool)` SUBST1_TAC THENL
       [UNDISCH_TAC `DISJOINT (v:real^3->bool) (closure bb)` THEN
        UNDISCH_TAC `(u:real^3->bool) SUBSET bb` THEN
        UNDISCH_TAC `(bb:real^3->bool) SUBSET closure bb` THEN SET_TAC[];
        ASM_REWRITE_TAC[]];
      SUBGOAL_THEN `DISJOINT (u:real^3->bool) (closure bb)` ASSUME_TAC THENL
       [USE_THEN "dout" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `(u UNION v) DIFF closure bb = (u:real^3->bool)` SUBST1_TAC THENL
       [UNDISCH_TAC `DISJOINT (u:real^3->bool) (closure bb)` THEN
        UNDISCH_TAC `(v:real^3->bool) SUBSET bb` THEN
        UNDISCH_TAC `(bb:real^3->bool) SUBSET closure bb` THEN SET_TAC[];
        ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [USE_THEN "loc" (MP_TAC o SPEC `rr:real`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL]; ALL_TAC] THEN
    STRIP_TAC THEN
    MATCH_MP_TAC(SET_RULE `!s t:real^3->bool. s SUBSET t /\ (y:real^3) IN s ==> y IN t`) THEN
    EXISTS_TAC `closure (ball(y:real^3,rr) DIFF (x UNION closure bb))` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_CLOSURE THEN
    UNDISCH_TAC `ball(y:real^3,rr) SUBSET m` THEN SET_TAC[];
    X_GEN_TAC `d:real` THEN DISCH_TAC THEN
    EXISTS_TAC `ball(y:real^3,min d rr)` THEN
    USE_THEN "loc" (MP_TAC o SPEC `min d rr`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[OPEN_BALL; CENTRE_IN_BALL; REAL_LT_MIN] THEN
    MATCH_MP_TAC SUBSET_BALL THEN REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Part 4: the pieces of a torus cut along two disjoint                     *)
(* essential polygons.  The frontier of a PL solid torus is connected and   *)
(* locally connected (PL_SOLID_TORUS_BASIC), so the complement of the two   *)
(* polygons has finitely many open components, each with closure a PL      *)
(* annulus with the two polygons as ends (28.6).                            *)
(* ------------------------------------------------------------------------- *)

let MOI_S3ST_ANN_SYM = prove
 (`!(a:real^N->bool) j0 j1. pl_annulus_with_ends a j0 j1 ==> pl_annulus_with_ends a j1 j0`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_annulus_with_ends; GSYM moi_fps_ann] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^2->real^N` (X_CHOOSE_THEN `g:real^N->real^2`
    STRIP_ASSUME_TAC)) THEN
  X_CHOOSE_THEN `sw:real^2->real^2` (X_CHOOSE_THEN `sw':real^2->real^2` STRIP_ASSUME_TAC)
    MOI_S8PL_ANN_SWAP THEN
  MAP_EVERY EXISTS_TAC [`(f:real^2->real^N) o (sw:real^2->real^2)`;
                        `(sw':real^2->real^2) o (g:real^N->real^2)`] THEN
  ASM_REWRITE_TAC[IMAGE_o] THEN MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
  EXISTS_TAC `moi_fps_ann` THEN ASM_REWRITE_TAC[]);;

let MOI_S3ST_ANN_MODEL_ENDS = prove
 (`relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]) SUBSET moi_fps_ann /\
   relative_frontier(interval[--vector[&2;&2]:real^2,vector[&2;&2]]) SUBSET moi_fps_ann /\
   DISJOINT (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]))
            (relative_frontier(interval[--vector[&2;&2]:real^2,vector[&2;&2]]))`,
  REWRITE_TAC[MOI_S8PL_RF12; moi_fps_ann; SUBSET; DISJOINT; EXTENSION; IN_ELIM_THM;
              IN_DIFF; IN_INTER; NOT_IN_EMPTY; IN_INTERVAL; DIMINDEX_2; FORALL_2;
              VECTOR_2; VECTOR_NEG_COMPONENT] THEN
  REAL_ARITH_TAC);;

let MOI_S3ST_ANN_ENDS = prove
 (`!(a:real^N->bool) j0 j1.
     pl_annulus_with_ends a j0 j1
     ==> j0 SUBSET a /\ j1 SUBSET a /\ DISJOINT j0 j1 /\ ~(j0 = {}) /\ ~(j1 = {}) /\
         compact a /\ compact j0 /\ compact j1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_annulus_with_ends; GSYM moi_fps_ann] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^2->real^N` (X_CHOOSE_THEN `g:real^N->real^2`
    (CONJUNCTS_THEN2 MP_TAC (CONJUNCTS_THEN2 SUBST1_TAC SUBST1_TAC)))) THEN
  REWRITE_TAC[pl_homeomorphism; homeomorphism] THEN STRIP_TAC THEN
  MP_TAC MOI_S3ST_ANN_MODEL_ENDS THEN STRIP_TAC THEN
  MP_TAC(SPEC `&1` MOI_S8PL_RF_FACTS) THEN MP_TAC(SPEC `&2` MOI_S8PL_RF_FACTS) THEN
  REWRITE_TAC[REAL_LT_01; REAL_ARITH `&0 < &2`] THEN
  DISCH_THEN(STRIP_ASSUME_TAC) THEN DISCH_THEN(STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `r1 = relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])` THEN
  ABBREV_TAC `r2 = relative_frontier(interval[--vector[&2;&2]:real^2,vector[&2;&2]])` THEN
  SUBGOAL_THEN `compact (a:real^N->bool)` ASSUME_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq (concl th) &&
      rand (concl th) = `a:real^N->bool`)) THEN
    MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[MOI_S8PL_ANN_CLOSED];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[IMAGE_EQ_EMPTY] THEN REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `IMAGE (f:real^2->real^N) moi_fps_ann = a` THEN
    UNDISCH_TAC `(r1:real^2->bool) SUBSET moi_fps_ann` THEN SET_TAC[];
    UNDISCH_TAC `IMAGE (f:real^2->real^N) moi_fps_ann = a` THEN
    UNDISCH_TAC `(r2:real^2->bool) SUBSET moi_fps_ann` THEN SET_TAC[];
    UNDISCH_TAC `!x:real^2. x IN moi_fps_ann ==> (g:real^N->real^2) (f x) = x` THEN
    UNDISCH_TAC `(r1:real^2->bool) SUBSET moi_fps_ann` THEN
    UNDISCH_TAC `(r2:real^2->bool) SUBSET moi_fps_ann` THEN
    UNDISCH_TAC `DISJOINT (r1:real^2->bool) r2` THEN SET_TAC[];
    MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `moi_fps_ann` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `moi_fps_ann` THEN ASM_REWRITE_TAC[]]);;

(* Finitely many open components, each meeting a fixed compact set.        *)

let MOI_S3ST_FINITE_COMPONENTS = prove
 (`!(s:real^N->bool) k.
     compact k /\ k SUBSET s /\
     (!w. w IN components s ==> open_in (subtopology euclidean s) w /\ ~(w INTER k = {}))
     ==> FINITE (components s)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "cw"))) THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [COMPACT_EQ_HEINE_BOREL_SUBTOPOLOGY]) THEN
  DISCH_THEN(MP_TAC o SPEC `{w INTER k | w IN components (s:real^N->bool)}`) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[FORALL_IN_GSPEC] THEN X_GEN_TAC `w:real^N->bool` THEN DISCH_TAC THEN
      USE_THEN "cw" (MP_TAC o CONJUNCT1 o C MATCH_MP (ASSUME `(w:real^N->bool) IN components s`)) THEN
      REWRITE_TAC[OPEN_IN_OPEN] THEN
      DISCH_THEN(X_CHOOSE_THEN `o1:real^N->bool` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `o1:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(k:real^N->bool) SUBSET s` THEN SET_TAC[];
      REWRITE_TAC[SUBSET; IN_UNIONS; EXISTS_IN_GSPEC; IN_INTER] THEN
      X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
      EXISTS_TAC `connected_component s (x:real^N)` THEN
      SUBGOAL_THEN `(x:real^N) IN s` ASSUME_TAC THENL
       [UNDISCH_TAC `(k:real^N->bool) SUBSET s` THEN UNDISCH_TAC `(x:real^N) IN k` THEN
        SET_TAC[];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[IN_COMPONENTS] THEN CONJ_TAC THENL
       [EXISTS_TAC `x:real^N` THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[IN] THEN ASM_REWRITE_TAC[CONNECTED_COMPONENT_REFL_EQ]]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `f1:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`\w:real^N->bool. w INTER k`; `f1:(real^N->bool)->bool`;
                 `components (s:real^N->bool)`] FINITE_IMAGE_INJ_GENERAL) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`w1:real^N->bool`; `w2:real^N->bool`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`s:real^N->bool`; `w1:real^N->bool`; `w2:real^N->bool`]
      COMPONENTS_NONOVERLAP) THEN
    ASM_REWRITE_TAC[] THEN
    USE_THEN "cw" (MP_TAC o CONJUNCT2 o C MATCH_MP (ASSUME `(w1:real^N->bool) IN components s`)) THEN
    UNDISCH_TAC `(w1:real^N->bool) INTER k = w2 INTER k` THEN SET_TAC[];
    ALL_TAC] THEN
  DISCH_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `{w | w IN components (s:real^N->bool) /\ w INTER k IN f1}` THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `w:real^N->bool` THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[] THEN
  USE_THEN "cw" (MP_TAC o CONJUNCT2 o C MATCH_MP (ASSUME `(w:real^N->bool) IN components s`)) THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(p:real^N) IN UNIONS f1` MP_TAC THENL
   [UNDISCH_TAC `(k:real^N->bool) SUBSET UNIONS f1` THEN UNDISCH_TAC `(p:real^N) IN k` THEN
    SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[IN_UNIONS] THEN DISCH_THEN(X_CHOOSE_THEN `c:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `?w1:real^N->bool. w1 IN components s /\ c = w1 INTER k` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(f1:(real^N->bool)->bool) SUBSET {w INTER k | w IN components s}` THEN
    UNDISCH_TAC `(c:real^N->bool) IN f1` THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(w:real^N->bool) = w1` SUBST1_TAC THENL
   [MP_TAC(ISPECL [`s:real^N->bool`; `w:real^N->bool`; `w1:real^N->bool`]
      COMPONENTS_NONOVERLAP) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(p:real^N) IN c` THEN UNDISCH_TAC `(c:real^N->bool) = w1 INTER k` THEN
    UNDISCH_TAC `(p:real^N) IN w` THEN SET_TAC[];
    ASM_MESON_TAC[]]);;

let MOI_S3ST_SPHERE1_FACTS = prove
 (`!j:real^N->bool. pl_sphere 1 j ==> compact j /\ connected j /\ ~(j = {})`,
  GEN_TAC THEN REWRITE_TAC[pl_sphere] THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
    (X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[homeomorphism] o CONJUNCT1 o
    GEN_REWRITE_RULE I [pl_homeomorphism]) THEN
  SUBGOAL_THEN `compact (k:real^N->bool) /\ convex k /\ aff_dim k = &2` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[SIMPLEX_IMP_COMPACT; SIMPLEX_IMP_CONVEX; AFF_DIM_SIMPLEX]; ALL_TAC] THEN
  UNDISCH_TAC `IMAGE (f:real^N->real^N) (relative_frontier k) = j` THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_SIMP_TAC[COMPACT_RELATIVE_FRONTIER];
    MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONNECTED_SPHERE_GEN THEN ASM_SIMP_TAC[COMPACT_IMP_BOUNDED] THEN
    INT_ARITH_TAC;
    REWRITE_TAC[IMAGE_EQ_EMPTY; RELATIVE_FRONTIER_EQ_EMPTY] THEN DISCH_TAC THEN
    MP_TAC(ISPEC `k:real^N->bool` AFFINE_BOUNDED_EQ_TRIVIAL) THEN
    ASM_SIMP_TAC[COMPACT_IMP_BOUNDED] THEN STRIP_TAC THEN
    UNDISCH_TAC `aff_dim (k:real^N->bool) = &2` THEN
    ASM_REWRITE_TAC[AFF_DIM_EMPTY; AFF_DIM_SING] THEN INT_ARITH_TAC]);;

let MOI_S3ST_TORUS_FR = prove
 (`!s:real^3->bool.
     pl_solid_torus s
     ==> compact (frontier s) /\ connected (frontier s) /\ locally connected (frontier s)`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPEC `s:real^3->bool` (CONJUNCT2 PL_SOLID_TORUS_BASIC)) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[pl_homeomorphism] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^(2,2)finite_sum->real^3`
    (X_CHOOSE_THEN `g:real^3->real^(2,2)finite_sum` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `pl_torus_model homeomorphic frontier (s:real^3->bool)` ASSUME_TAC THENL
   [REWRITE_TAC[homeomorphic] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `compact (interval[--vec 1:real^2,vec 1]) /\ convex (interval[--vec 1:real^2,vec 1]) /\
                ~(aff_dim (interval[--vec 1:real^2,vec 1]) = &1)` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[COMPACT_INTERVAL; CONVEX_INTERVAL] THEN
    SUBGOAL_THEN `~(interior (interval[--vec 1:real^2,vec 1]) = {})` MP_TAC THENL
     [REWRITE_TAC[INTERIOR_CLOSED_INTERVAL; INTERVAL_NE_EMPTY] THEN
      REWRITE_TAC[VECTOR_NEG_COMPONENT; VEC_COMPONENT] THEN REAL_ARITH_TAC;
      SIMP_TAC[AFF_DIM_NONEMPTY_INTERIOR; DIMINDEX_2] THEN INT_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `compact pl_torus_model /\ connected pl_torus_model /\
                locally connected pl_torus_model` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[pl_torus_model] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_PCROSS THEN ASM_SIMP_TAC[COMPACT_RELATIVE_FRONTIER];
      MATCH_MP_TAC CONNECTED_PCROSS THEN CONJ_TAC THEN
      MATCH_MP_TAC CONNECTED_SPHERE_GEN THEN ASM_SIMP_TAC[COMPACT_IMP_BOUNDED];
      MATCH_MP_TAC LOCALLY_CONNECTED_PCROSS THEN CONJ_TAC THEN
      MATCH_MP_TAC LOCALLY_CONNECTED_SPHERE_GEN THEN ASM_SIMP_TAC[COMPACT_IMP_BOUNDED]];
    ALL_TAC] THEN
  ASM_MESON_TAC[HOMEOMORPHIC_COMPACTNESS; HOMEOMORPHIC_CONNECTEDNESS;
                HOMEOMORPHIC_LOCAL_CONNECTEDNESS]);;

(* The complement of two disjoint compact sets in a compact locally          *)
(* connected set: open components, finitely many if every closure meets     *)
(* both sets.                                                                *)

let MOI_S3ST_TWO_PIECES_FINITE = prove
 (`!(t:real^3->bool) j j1.
     compact t /\ locally connected t /\ compact j /\ compact j1 /\
     j SUBSET t /\ j1 SUBSET t /\ DISJOINT j j1 /\
     (!w. w IN components (t DIFF (j UNION j1))
          ==> ~(closure w INTER j = {}) /\ ~(closure w INTER j1 = {}))
     ==> FINITE (components (t DIFF (j UNION j1))) /\
         (!w. w IN components (t DIFF (j UNION j1))
              ==> open_in (subtopology euclidean t) w)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "cl")))))))) THEN
  SUBGOAL_THEN `open_in (subtopology euclidean t) (t DIFF (j UNION j1:real^3->bool))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC OPEN_IN_DIFF_CLOSED THEN MATCH_MP_TAC CLOSED_UNION THEN
    ASM_SIMP_TAC[COMPACT_IMP_CLOSED];
    ALL_TAC] THEN
  SUBGOAL_THEN `!w. w IN components (t DIFF (j UNION j1))
                    ==> open_in (subtopology euclidean (t DIFF (j UNION j1))) (w:real^3->bool)`
  ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC OPEN_IN_COMPONENTS_LOCALLY_CONNECTED THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LOCALLY_OPEN_SUBSET THEN
    EXISTS_TAC `t:real^3->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [ALL_TAC;
    GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC OPEN_IN_TRANS THEN
    EXISTS_TAC `t DIFF (j UNION j1:real^3->bool)` THEN ASM_SIMP_TAC[]] THEN
  MP_TAC(ISPECL [`j:real^3->bool`; `j1:real^3->bool`] SEPARATION_NORMAL) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN ASM_REWRITE_TAC[GSYM DISJOINT]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^3->bool` (X_CHOOSE_THEN `v:real^3->bool`
    STRIP_ASSUME_TAC)) THEN
  MATCH_MP_TAC MOI_S3ST_FINITE_COMPONENTS THEN
  EXISTS_TAC `t DIFF (u UNION v:real^3->bool)` THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC COMPACT_DIFF THEN ASM_SIMP_TAC[OPEN_UNION];
    UNDISCH_TAC `(j:real^3->bool) SUBSET u` THEN UNDISCH_TAC `(j1:real^3->bool) SUBSET v` THEN
    SET_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `w:real^3->bool` THEN DISCH_TAC THEN ASM_SIMP_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(w:real^3->bool) SUBSET u UNION v /\ connected w /\ ~(w = {})`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[IN_COMPONENTS_SUBSET; IN_COMPONENTS_CONNECTED; IN_COMPONENTS_NONEMPTY;
                  SET_RULE `w SUBSET t DIFF s /\ w INTER (t DIFF (u UNION v)) = {}
                            ==> w SUBSET u UNION (v:real^3->bool)`];
    ALL_TAC] THEN
  USE_THEN "cl" (MP_TAC o C MATCH_MP (ASSUME `(w:real^3->bool) IN components (t DIFF (j UNION j1))`)) THEN
  SUBGOAL_THEN `closure u INTER (v:real^3->bool) = {} /\ closure v INTER (u:real^3->bool) = {}`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN ONCE_REWRITE_TAC[INTER_COMM] THENL
     [MP_TAC(ISPECL [`v:real^3->bool`; `u:real^3->bool`] OPEN_INTER_CLOSURE_EQ_EMPTY);
      MP_TAC(ISPECL [`u:real^3->bool`; `v:real^3->bool`] OPEN_INTER_CLOSURE_EQ_EMPTY)] THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM SET_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `(w:real^3->bool) INTER v = {}` THENL
   [SUBGOAL_THEN `closure w SUBSET closure (u:real^3->bool)` MP_TAC THENL
     [MATCH_MP_TAC SUBSET_CLOSURE THEN ASM SET_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `closure u INTER (v:real^3->bool) = {}` THEN
    UNDISCH_TAC `(j1:real^3->bool) SUBSET v` THEN SET_TAC[];
    SUBGOAL_THEN `(w:real^3->bool) SUBSET v` ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_S3ST_CONN_SIDE THEN EXISTS_TAC `u:real^3->bool` THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `closure w SUBSET closure (v:real^3->bool)` MP_TAC THENL
     [MATCH_MP_TAC SUBSET_CLOSURE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `closure v INTER (u:real^3->bool) = {}` THEN
    UNDISCH_TAC `(j:real^3->bool) SUBSET u` THEN SET_TAC[]]);;

(* 28.6 for two disjoint essential polygons j, j1 of the frontier of a PL   *)
(* solid torus: the complement is nonempty, with finitely many components,  *)
(* each open in the frontier, with closure a PL annulus with ends j, j1.    *)

let MOI_S3ST_TORUS_PIECES = prove
 (`!(s:real^3->bool) j j1.
     MOISE_286_STATEMENT /\ pl_solid_torus s /\
     pl_sphere 1 j /\ j SUBSET frontier s /\
     ~(?d. d SUBSET frontier s /\ pl_cell_with_boundary 2 d j) /\
     pl_sphere 1 j1 /\ j1 SUBSET frontier s /\
     ~(?d. d SUBSET frontier s /\ pl_cell_with_boundary 2 d j1) /\
     DISJOINT j j1
     ==> ~(frontier s DIFF (j UNION j1) = {}) /\
         FINITE (components (frontier s DIFF (j UNION j1))) /\
         (!w. w IN components (frontier s DIFF (j UNION j1))
              ==> open_in (subtopology euclidean (frontier s)) w /\
                  pl_annulus_with_ends (closure w) j j1 /\
                  closure w SUBSET frontier s /\
                  closure w DIFF (j UNION j1) = w)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `s:real^3->bool` MOI_S3ST_TORUS_FR) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `j:real^3->bool` MOI_S3ST_SPHERE1_FACTS) THEN
  MP_TAC(ISPEC `j1:real^3->bool` MOI_S3ST_SPHERE1_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!w. w IN components (frontier s DIFF (j UNION j1))
                    ==> pl_annulus_with_ends (closure w) j (j1:real^3->bool)`
  (LABEL_TAC "ann") THENL
   [GEN_TAC THEN REWRITE_TAC[components; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:real^3` (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC)) THEN
    UNDISCH_TAC `MOISE_286_STATEMENT` THEN REWRITE_TAC[MOISE_286_STATEMENT] THEN
    DISCH_THEN(MP_TAC o SPECL [`s:real^3->bool`; `{j:real^3->bool,j1}`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY; FORALL_IN_INSERT; NOT_IN_EMPTY] THEN
      REPEAT CONJ_TAC THENL
       [SUBGOAL_THEN `~(j:real^3->bool = j1)` ASSUME_TAC THENL
         [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC `DISJOINT (j1:real^3->bool) j1` THEN
          UNDISCH_TAC `~(j1:real^3->bool = {})` THEN SET_TAC[];
          ASM_SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY; IN_INSERT; NOT_IN_EMPTY] THEN
          ARITH_TAC];
        REWRITE_TAC[pairwise; IN_INSERT; NOT_IN_EMPTY] THEN
        ASM_MESON_TAC[DISJOINT_SYM];
        REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN ASM_MESON_TAC[]];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `x:real^3`) THEN
    ASM_REWRITE_TAC[UNIONS_2] THEN
    REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
    DISCH_THEN(X_CHOOSE_THEN `j0:real^3->bool` (X_CHOOSE_THEN `j2:real^3->bool`
      STRIP_ASSUME_TAC)) THEN
    REPEAT(FIRST_X_ASSUM SUBST_ALL_TAC) THEN
    ASM_MESON_TAC[MOI_S3ST_ANN_SYM];
    ALL_TAC] THEN
  SUBGOAL_THEN `closed (frontier s:real^3->bool)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[COMPACT_IMP_CLOSED]; ALL_TAC] THEN
  MP_TAC(ISPECL [`frontier s:real^3->bool`; `j:real^3->bool`; `j1:real^3->bool`]
    MOI_S3ST_TWO_PIECES_FINITE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN GEN_TAC THEN DISCH_TAC THEN
    USE_THEN "ann" (MP_TAC o MATCH_MP MOI_S3ST_ANN_ENDS o C MATCH_MP
      (ASSUME `(w:real^3->bool) IN components (frontier s DIFF (j UNION j1))`)) THEN
    UNDISCH_TAC `~(j:real^3->bool = {})` THEN UNDISCH_TAC `~(j1:real^3->bool = {})` THEN
    SET_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [DISCH_TAC THEN
    UNDISCH_TAC `connected (frontier s:real^3->bool)` THEN
    REWRITE_TAC[CONNECTED_CLOSED_IN_EQ; NOT_EXISTS_THM] THEN
    DISCH_THEN(MP_TAC o SPECL [`j:real^3->bool`; `j1:real^3->bool`]) THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CLOSED_SUBSET THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED];
      MATCH_MP_TAC CLOSED_SUBSET THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED];
      UNDISCH_TAC `frontier s DIFF (j UNION j1:real^3->bool) = {}` THEN
      UNDISCH_TAC `(j:real^3->bool) SUBSET frontier s` THEN
      UNDISCH_TAC `(j1:real^3->bool) SUBSET frontier s` THEN SET_TAC[];
      ASM_REWRITE_TAC[GSYM DISJOINT]];
    ALL_TAC] THEN
  X_GEN_TAC `w:real^3->bool` THEN DISCH_TAC THEN ASM_SIMP_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC CLOSURE_MINIMAL THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`frontier s DIFF (j UNION j1:real^3->bool)`; `w:real^3->bool`]
      IN_COMPONENTS_SUBSET) THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
    MP_TAC(ISPECL [`frontier s DIFF (j UNION j1:real^3->bool)`; `w:real^3->bool`]
      CLOSED_IN_COMPONENT) THEN
    ASM_REWRITE_TAC[CLOSED_IN_INTER_CLOSURE] THEN
    SUBGOAL_THEN `closure w SUBSET (frontier s:real^3->bool)` MP_TAC THENL
     [MATCH_MP_TAC CLOSURE_MINIMAL THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`frontier s DIFF (j UNION j1:real^3->bool)`; `w:real^3->bool`]
        IN_COMPONENTS_SUBSET) THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
      SET_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* Part 5: model facts for Steps 2-4.  M = interior g(cyl) is simply        *)
(* connected; the revolved cells are compact and connected; the axis path   *)
(* from g qlo to g qhi avoids g(v); a path hugging the frontier of the      *)
(* model avoids g of the inner cells rev(dd j), j <= n, and the centre; the *)
(* outer cells rev(dd j), j >= n, stay away from the centre.               *)
(* ------------------------------------------------------------------------- *)

let MOI_S3ST_CYL_CONVEX = prove
 (`convex moi_s32_cyl /\ convex (interior moi_s32_cyl)`,
  MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
   [ALL_TAC; SIMP_TAC[CONVEX_INTERIOR]] THEN
  REWRITE_TAC[MOI_S3GF_CYL_EQ] THEN
  REPEAT(MATCH_MP_TAC CONVEX_INTER THEN CONJ_TAC) THEN
  REWRITE_TAC[CONVEX_HALFSPACE_COMPONENT_LE; CONVEX_HALFSPACE_COMPONENT_GE] THEN
  SUBGOAL_THEN `{x:real^3 | x$1 pow 2 + x$3 pow 2 <= &1} =
                {x | (\x:real^3. vector[x$1; x$3]:real^2) x IN cball(vec 0,&1)}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_CBALL_0; NORM_LE_SQUARE; DOT_2; VECTOR_2] THEN
    GEN_TAC THEN REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC;
    MATCH_MP_TAC CONVEX_LINEAR_PREIMAGE THEN REWRITE_TAC[CONVEX_CBALL] THEN
    REWRITE_TAC[linear; CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2; VECTOR_ADD_COMPONENT;
                VECTOR_MUL_COMPONENT] THEN
    REAL_ARITH_TAC]);;

let MOI_S3ST_M_SIMPLY_CONNECTED = prove
 (`!(g:real^3->real^3) v. moi_s32_model g v ==> simply_connected (moi_s32_open g)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`] MOI_S3GF_MODEL_OPEN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`] MOI_S3GF_MODEL_HOMEO) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `g':real^3->real^3`) THEN
  SUBGOAL_THEN `interior moi_s32_cyl homeomorphic IMAGE (g:real^3->real^3) (interior moi_s32_cyl)`
  MP_TAC THENL
   [REWRITE_TAC[homeomorphic] THEN
    MAP_EVERY EXISTS_TAC [`g:real^3->real^3`; `g':real^3->real^3`] THEN
    MATCH_MP_TAC HOMEOMORPHISM_OF_SUBSETS THEN
    MAP_EVERY EXISTS_TAC [`moi_s32_cyl`; `IMAGE (g:real^3->real^3) moi_s32_cyl`] THEN
    ASM_REWRITE_TAC[MOI_S3GF_CYL_PARTS] THEN MATCH_MP_TAC IMAGE_SUBSET THEN
    REWRITE_TAC[MOI_S3GF_CYL_PARTS];
    ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o SYM o MATCH_MP HOMEOMORPHIC_SIMPLY_CONNECTED_EQ) THEN
  MATCH_MP_TAC CONVEX_IMP_SIMPLY_CONNECTED THEN REWRITE_TAC[MOI_S3ST_CYL_CONVEX]);;

let MOI_S3ST_REV_DD = prove
 (`!(g:real^3->real^3) v pp dd s2.
     moi_s32_tower g v pp dd s2
     ==> !j. compact (revolution (dd j)) /\ connected (revolution (dd j)) /\
             pp j IN revolution (dd j)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN X_GEN_TAC `j:int` THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                 `dd:int->real^3->bool`; `s2:int->real^3->bool`] MOI_S3CL_DD_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(STRIP_ASSUME_TAC o SPEC `j:int`) THEN
  REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[MOI_S3RV_REV_IMAGE] THEN MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
    ASM_SIMP_TAC[MOI_S3RV_ROT_CONTINUOUS; COMPACT_PCROSS; COMPACT_SPHERE];
    ASM_SIMP_TAC[MOI_S3RV_REV_IMAGE] THEN MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN
    ASM_SIMP_TAC[MOI_S3RV_ROT_CONTINUOUS] THEN MATCH_MP_TAC CONNECTED_PCROSS THEN
    ASM_SIMP_TAC[CONNECTED_SPHERE; DIMINDEX_2; LE_REFL];
    MP_TAC(ISPEC `(dd:int->real^3->bool) j` MOI_S3CL_REV_SUPER) THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[]]);;

(* The axis segment from qlo to qhi: in the open cylinder, off v.          *)

let MOI_S3ST_AXIS_PATH = prove
 (`!(g:real^3->real^3) v.
     moi_s32_model g v
     ==> connected (IMAGE g (segment[moi_s32_qlo,moi_s32_qhi])) /\
         IMAGE g (segment[moi_s32_qlo,moi_s32_qhi]) SUBSET moi_s32_open g /\
         g moi_s32_qlo IN IMAGE g (segment[moi_s32_qlo,moi_s32_qhi]) /\
         g moi_s32_qhi IN IMAGE g (segment[moi_s32_qlo,moi_s32_qhi]) /\
         DISJOINT (IMAGE g (segment[moi_s32_qlo,moi_s32_qhi])) (IMAGE g v)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `segment[moi_s32_qlo,moi_s32_qhi] SUBSET interior moi_s32_cyl /\
                segment[moi_s32_qlo,moi_s32_qhi] SUBSET moi_s32_axis` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN MATCH_MP_TAC HULL_MINIMAL THEN
      REWRITE_TAC[MOI_S3ST_CYL_CONVEX; INSERT_SUBSET; EMPTY_SUBSET; MOI_S3GF_MODEL_POINTS];
      REWRITE_TAC[SUBSET; IN_SEGMENT; moi_s32_axis; moi_s32_qlo; moi_s32_qhi; IN_ELIM_THM] THEN
      REPEAT STRIP_TAC THEN
      ASM_REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; VECTOR_3] THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_s32_model]) THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`] MOI_S3GF_MODEL_OPEN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN REWRITE_TAC[CONNECTED_SEGMENT] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `moi_s32_cyl` THEN
    ASM_MESON_TAC[MOI_S3GF_CYL_PARTS; SUBSET_TRANS];
    MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[ENDS_IN_SEGMENT];
    MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[ENDS_IN_SEGMENT];
    MP_TAC MOI_S3GF_CYL_PARTS THEN
    UNDISCH_TAC `DISJOINT (v:real^3->bool) moi_s32_axis` THEN
    UNDISCH_TAC `(v:real^3->bool) SUBSET interior moi_s32_cyl` THEN
    UNDISCH_TAC `segment[moi_s32_qlo,moi_s32_qhi] SUBSET interior moi_s32_cyl` THEN
    UNDISCH_TAC `segment[moi_s32_qlo,moi_s32_qhi] SUBSET moi_s32_axis` THEN
    UNDISCH_TAC `!x y. x IN moi_s32_cyl /\ y IN moi_s32_cyl /\ (g:real^3->real^3) x = g y
                       ==> x = y` THEN
    SET_TAC[]]);;

(* A path from g qlo to g qhi in M avoiding the centre and the images of   *)
(* the inner cells rev(dd j), j <= n (they lie in a compact subset of the  *)
(* open cylinder: TOWER_LOW; the path runs along the axis and close to the  *)
(* frontier, RIM_PATH).                                                    *)

let MOI_S3ST_INNER_PATH = prove
 (`!(g:real^3->real^3) v pp dd s2 n.
     moi_s32_model g v /\ moi_s32_tower g v pp dd s2
     ==> ?c. connected c /\ c SUBSET moi_s32_open g /\
             g moi_s32_qlo IN c /\ g moi_s32_qhi IN c /\ ~(g (vec 0) IN c) /\
             DISJOINT c (IMAGE g (UNIONS {revolution (dd j) | j <= n}))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                 `dd:int->real^3->bool`; `s2:int->real^3->bool`] MOI_S3CL_TOWER_LOW) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `&1 / &4`) THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN DISCH_THEN(X_CHOOSE_TAC `jj:int`) THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                 `dd:int->real^3->bool`; `s2:int->real^3->bool`] MOI_S3ST_REV_DD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                 `dd:int->real^3->bool`; `s2:int->real^3->bool`] MOI_S3CL_REV_CYL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_s32_model]) THEN
  ABBREV_TAC `kk = cball(vec 0:real^3,&1 / &4) UNION
                   UNIONS {revolution ((dd:int->real^3->bool) j) | jj < j /\ j <= n}` THEN
  SUBGOAL_THEN `compact (kk:real^3->bool) /\ kk SUBSET interior moi_s32_cyl /\
                (vec 0:real^3) IN kk /\
                UNIONS {revolution ((dd:int->real^3->bool) j) | j <= n} SUBSET kk`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "kk" THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_UNION THEN REWRITE_TAC[COMPACT_CBALL] THEN
      MATCH_MP_TAC COMPACT_UNIONS THEN CONJ_TAC THENL
       [ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN MATCH_MP_TAC FINITE_IMAGE THEN
        REWRITE_TAC[FINITE_INT_SEG];
        REWRITE_TAC[FORALL_IN_GSPEC] THEN ASM_REWRITE_TAC[]];
      REWRITE_TAC[UNION_SUBSET; UNIONS_SUBSET; FORALL_IN_GSPEC] THEN CONJ_TAC THENL
       [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `ball(vec 0:real^3,&1 / &2)` THEN
        SIMP_TAC[MOI_S3CL_BALL_CYL; REAL_LE_REFL] THEN
        REWRITE_TAC[SUBSET; IN_CBALL; IN_BALL] THEN REAL_ARITH_TAC;
        X_GEN_TAC `j:int` THEN DISCH_TAC THEN
        MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `v:real^3->bool` THEN
        ASM_REWRITE_TAC[]];
      REWRITE_TAC[IN_UNION; CENTRE_IN_CBALL] THEN CONV_TAC REAL_RAT_REDUCE_CONV;
      REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC] THEN X_GEN_TAC `j:int` THEN DISCH_TAC THEN
      ASM_CASES_TAC `j <= jj:int` THENL
       [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `ball(vec 0:real^3,&1 / &4)` THEN
        CONJ_TAC THENL
         [UNDISCH_TAC `!j. j <= jj ==> revolution ((dd:int->real^3->bool) j) SUBSET
                                       ball(vec 0,&1 / &4)` THEN
          DISCH_THEN(MP_TAC o SPEC `j:int`) THEN ASM_REWRITE_TAC[];
          MP_TAC(ISPECL [`vec 0:real^3`; `&1 / &4`] BALL_SUBSET_CBALL) THEN SET_TAC[]];
        MATCH_MP_TAC(SET_RULE `(x:real^3->bool) IN f ==> x SUBSET a UNION UNIONS f`) THEN
        REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `j:int` THEN ASM_REWRITE_TAC[] THEN
        ASM_INT_ARITH_TAC]];
    ALL_TAC] THEN
  ABBREV_TAC `sh = {x:real^3 | x IN moi_s32_cyl /\ (x$2 = -- &1 \/ x$2 = &1 \/
                                                  x$1 = &1 /\ x$3 = &0)}` THEN
  MP_TAC(SPECL [`&1`; `&0`] MOI_S3CL_SHADOW) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < setdist(kk:real^3->bool,sh)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_LT_LE; SETDIST_POS_LE] THEN
    ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN
    ASM_SIMP_TAC[SETDIST_EQ_0_COMPACT_CLOSED; COMPACT_IMP_CLOSED] THEN
    REWRITE_TAC[DE_MORGAN_THM] THEN REPEAT CONJ_TAC THENL
     [ASM SET_TAC[];
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `vector[&0; &1; &0]:real^3` THEN
      EXPAND_TAC "sh" THEN REWRITE_TAC[IN_ELIM_THM; MOI_S3GF_CYL_EQ; IN_INTER; VECTOR_3] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV;
      ASM SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(SPECL [`&1`; `&0`; `min (&1 / &4) (setdist(kk:real^3->bool,sh) / &2)`]
    MOI_S3CL_RIM_PATH) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `c0:real^3->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!x:real^3. x IN c0 ==> ~(x IN kk) \/ (x IN moi_s32_axis /\ ~(x = vec 0))`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^3`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(DISJ_CASES_THEN2 (fun th -> REWRITE_TAC[th]) MP_TAC o CONJUNCT2) THEN
    DISCH_THEN(X_CHOOSE_THEN `x':real^3` STRIP_ASSUME_TAC) THEN
    DISJ1_TAC THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`kk:real^3->bool`; `sh:real^3->bool`; `x:real^3`; `x':real^3`]
      SETDIST_LE_DIST) THEN
    ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `IMAGE (g:real^3->real^3) c0` THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`] MOI_S3GF_MODEL_OPEN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN
  SUBGOAL_THEN `(c0:real^3->bool) SUBSET interior moi_s32_cyl` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^3. x IN c0 ==> x IN moi_s32_cyl` ASSUME_TAC THENL
   [MP_TAC MOI_S3GF_CYL_PARTS THEN UNDISCH_TAC `(c0:real^3->bool) SUBSET interior moi_s32_cyl` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(vec 0:real^3) IN moi_s32_cyl` ASSUME_TAC THENL
   [MP_TAC MOI_S3GF_CYL_PARTS THEN MP_TAC MOI_S3GF_MODEL_POINTS THEN SET_TAC[]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `moi_s32_cyl` THEN
    ASM_MESON_TAC[MOI_S3GF_CYL_PARTS; SUBSET_TRANS];
    MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `x:real^3` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(x:real^3) = vec 0` SUBST_ALL_TAC THENL
     [UNDISCH_TAC `!x y. x IN moi_s32_cyl /\ y IN moi_s32_cyl /\ (g:real^3->real^3) x = g y
                         ==> x = y` THEN
      DISCH_THEN(MP_TAC o SPECL [`x:real^3`; `vec 0:real^3`]) THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `!x:real^3. x IN c0 ==> ~(x IN kk) \/ x IN moi_s32_axis /\ ~(x = vec 0)` THEN
    DISCH_THEN(MP_TAC o SPEC `vec 0:real^3`) THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_IMAGE] THEN
    X_GEN_TAC `z:real^3` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `x:real^3` STRIP_ASSUME_TAC)
      (X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `?j. j <= n /\ (y:real^3) IN revolution ((dd:int->real^3->bool) j)`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(y:real^3) IN UNIONS {revolution ((dd:int->real^3->bool) j) | j <= n}` THEN
      REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(x:real^3) = y` SUBST_ALL_TAC THENL
     [UNDISCH_TAC `!x y. x IN moi_s32_cyl /\ y IN moi_s32_cyl /\ (g:real^3->real^3) x = g y
                         ==> x = y` THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[] THEN
      CONJ_TAC THENL
       [UNDISCH_TAC `!j. revolution ((dd:int->real^3->bool) j) SUBSET v /\
                         revolution (dd j) SUBSET moi_s32_cyl` THEN
        DISCH_THEN(MP_TAC o SPEC `j:int`) THEN UNDISCH_TAC `(y:real^3) IN revolution (dd (j:int))` THEN
        SET_TAC[];
        ASM_MESON_TAC[]];
      ALL_TAC] THEN
    UNDISCH_TAC `!x:real^3. x IN c0 ==> ~(x IN kk) \/ x IN moi_s32_axis /\ ~(x = vec 0)` THEN
    DISCH_THEN(MP_TAC o SPEC `y:real^3`) THEN ASM_REWRITE_TAC[DE_MORGAN_THM] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `UNIONS {revolution ((dd:int->real^3->bool) j) | j <= n} SUBSET kk` THEN
      UNDISCH_TAC `(y:real^3) IN UNIONS {revolution ((dd:int->real^3->bool) j) | j <= n}` THEN
      SET_TAC[];
      UNDISCH_TAC `DISJOINT (v:real^3->bool) moi_s32_axis` THEN
      UNDISCH_TAC `!j. revolution ((dd:int->real^3->bool) j) SUBSET v /\
                       revolution (dd j) SUBSET moi_s32_cyl` THEN
      DISCH_THEN(MP_TAC o SPEC `j:int`) THEN UNDISCH_TAC `(y:real^3) IN revolution (dd (j:int))` THEN
      SET_TAC[]]]);;

(* The outer cells rev(dd j), j >= n, stay away from the centre P'.       *)

let MOI_S3ST_OUTER_AWAY = prove
 (`!(g:real^3->real^3) v pp dd s2 n.
     moi_s32_model g v /\ moi_s32_tower g v pp dd s2
     ==> ?u. open u /\ g (vec 0) IN u /\
             DISJOINT u (IMAGE g (UNIONS {revolution (dd j) | n <= j}))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                 `dd:int->real^3->bool`; `s2:int->real^3->bool`] MOI_S3CL_TOWER_FAR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC o SPEC `n:int`) THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                 `dd:int->real^3->bool`; `s2:int->real^3->bool`] MOI_S3CL_REV_CYL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_s32_model]) THEN
  SUBGOAL_THEN `ball(vec 0:real^3,min r (&1 / &2)) SUBSET interior moi_s32_cyl` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S3CL_BALL_CYL THEN REAL_ARITH_TAC; ALL_TAC] THEN
  EXISTS_TAC `IMAGE (g:real^3->real^3) (ball(vec 0,min r (&1 / &2)))` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MOI_S3CL_G_OPEN THEN EXISTS_TAC `v:real^3->bool` THEN
    ASM_REWRITE_TAC[OPEN_BALL];
    MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[CENTRE_IN_BALL] THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC(SET_RULE
     `!c. (!x y. x IN c /\ y IN c /\ (g:real^3->real^3) x = g y ==> x = y) /\
          s SUBSET c /\ t SUBSET c /\ DISJOINT s t
          ==> DISJOINT (IMAGE g s) (IMAGE g t)`) THEN
    EXISTS_TAC `moi_s32_cyl` THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MP_TAC MOI_S3GF_CYL_PARTS THEN
      UNDISCH_TAC `ball(vec 0:real^3,min r (&1 / &2)) SUBSET interior moi_s32_cyl` THEN
      SET_TAC[];
      REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC] THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC(SET_RULE
       `(!t. t IN f ==> DISJOINT s t) ==> DISJOINT (s:real^3->bool) (UNIONS f)`) THEN
      REWRITE_TAC[FORALL_IN_GSPEC] THEN X_GEN_TAC `j:int` THEN DISCH_TAC THEN
      UNDISCH_TAC `!j. n <= j ==> DISJOINT (revolution ((dd:int->real^3->bool) j)) (ball(vec 0,r))` THEN
      DISCH_THEN(MP_TAC o SPEC `j:int`) THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`vec 0:real^3`; `min r (&1 / &2)`; `r:real`] SUBSET_BALL) THEN
      ANTS_TAC THENL [REAL_ARITH_TAC; SET_TAC[]]]]);;

(* Points of the axis in the cylinder: their images are off g(v).          *)

let MOI_S3ST_AXIS_NOT_V = prove
 (`!(g:real^3->real^3) v x.
     moi_s32_model g v /\ x IN moi_s32_axis /\ x IN moi_s32_cyl ==> ~(g x IN IMAGE g v)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_s32_model]) THEN
  REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(y:real^3) IN moi_s32_cyl` ASSUME_TAC THENL
   [MP_TAC MOI_S3GF_CYL_PARTS THEN
    UNDISCH_TAC `(v:real^3->bool) SUBSET interior moi_s32_cyl` THEN
    UNDISCH_TAC `(y:real^3) IN v` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^3) = y` SUBST_ALL_TAC THENL
   [UNDISCH_TAC `!x y. x IN moi_s32_cyl /\ y IN moi_s32_cyl /\ (g:real^3->real^3) x = g y
                       ==> x = y` THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `DISJOINT (v:real^3->bool) moi_s32_axis` THEN
  UNDISCH_TAC `(y:real^3) IN v` THEN UNDISCH_TAC `(y:real^3) IN moi_s32_axis` THEN
  SET_TAC[]);;

let MOI_S3ST_POINTS_NOT_V = prove
 (`!(g:real^3->real^3) v.
     moi_s32_model g v
     ==> ~(g (vec 0) IN IMAGE g v) /\ ~(g moi_s32_qlo IN IMAGE g v) /\
         ~(g moi_s32_qhi IN IMAGE g v) /\ ~(g moi_s32_qlo = g moi_s32_qhi)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC MOI_S3GF_MODEL_POINTS THEN MP_TAC MOI_S3GF_CYL_PARTS THEN
  DISCH_THEN STRIP_ASSUME_TAC THEN DISCH_THEN STRIP_ASSUME_TAC THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`] MOI_S3ST_AXIS_NOT_V) THEN
    ASM SET_TAC[];
    MATCH_MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`] MOI_S3ST_AXIS_NOT_V) THEN
    ASM SET_TAC[];
    MATCH_MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`] MOI_S3ST_AXIS_NOT_V) THEN
    ASM SET_TAC[];
    FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_s32_model]) THEN DISCH_TAC THEN
    SUBGOAL_THEN `moi_s32_qlo = moi_s32_qhi` MP_TAC THENL
     [UNDISCH_TAC `!x y. x IN moi_s32_cyl /\ y IN moi_s32_cyl /\ (g:real^3->real^3) x = g y
                         ==> x = y` THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      REWRITE_TAC[moi_s32_qlo; moi_s32_qhi; CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV]]);;

(* Every subset of g(v) has g of any point of the axis in its outside: the *)
(* axis joins it to the frontier of g(cyl), whose complement is connected   *)
(* and unbounded.                                                          *)

let MOI_S3ST_OUTSIDE = prove
 (`!(g:real^3->real^3) v s x.
     moi_s32_model g v /\ s SUBSET IMAGE g v /\ x IN moi_s32_axis /\ x IN moi_s32_cyl
     ==> g x IN outside s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `q1 = vector[&0; &1; &0]:real^3` THEN
  SUBGOAL_THEN `(q1:real^3) IN moi_s32_cyl /\ q1 IN moi_s32_axis /\
                ~(q1 IN interior moi_s32_cyl)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "q1" THEN
    REWRITE_TAC[moi_s32_cyl; moi_s32_axis; MOI_S3GF_INTERIOR_CYL; IN_ELIM_THM; VECTOR_3] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN `segment[x:real^3,q1] SUBSET moi_s32_cyl /\
                segment[x:real^3,q1] SUBSET moi_s32_axis` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN MATCH_MP_TAC HULL_MINIMAL THEN
      ASM_REWRITE_TAC[MOI_S3ST_CYL_CONVEX; INSERT_SUBSET; EMPTY_SUBSET];
      UNDISCH_TAC `(x:real^3) IN moi_s32_axis` THEN UNDISCH_TAC `(q1:real^3) IN moi_s32_axis` THEN
      REWRITE_TAC[SUBSET; IN_SEGMENT; moi_s32_axis; IN_ELIM_THM] THEN
      REPEAT STRIP_TAC THEN
      ASM_REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_s32_model]) THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`] MOI_S3GF_MODEL_HOMEO) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `g':real^3->real^3`) THEN
  ABBREV_TAC `k = IMAGE (g:real^3->real^3) (segment[x,q1]) UNION
                  ((:real^3) DIFF IMAGE g moi_s32_cyl)` THEN
  SUBGOAL_THEN `connected ((:real^3) DIFF IMAGE (g:real^3->real^3) moi_s32_cyl)` ASSUME_TAC THENL
   [MATCH_MP_TAC(ISPECL [`IMAGE (g:real^3->real^3) moi_s32_cyl`; `moi_s32_cyl`]
      CONNECTED_COMPLEMENT_HOMEOMORPHIC_CONVEX_COMPACT) THEN
    REWRITE_TAC[DIMINDEX_3; MOI_S3ST_CYL_CONVEX; MOI_S3GF_CYL_COMPACT] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ONCE_REWRITE_TAC[HOMEOMORPHIC_SYM] THEN
    REWRITE_TAC[homeomorphic] THEN
    MAP_EVERY EXISTS_TAC [`g:real^3->real^3`; `g':real^3->real^3`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(g:real^3->real^3) q1 IN closure ((:real^3) DIFF IMAGE g moi_s32_cyl)`
  ASSUME_TAC THENL
   [REWRITE_TAC[CLOSURE_COMPLEMENT; IN_DIFF; IN_UNIV] THEN
    MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`] MOI_S3GF_MODEL_INTERIOR) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(q1:real^3) = y` SUBST_ALL_TAC THENL
     [UNDISCH_TAC `!x y. x IN moi_s32_cyl /\ y IN moi_s32_cyl /\ (g:real^3->real^3) x = g y
                         ==> x = y` THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      MP_TAC MOI_S3GF_CYL_PARTS THEN UNDISCH_TAC `(y:real^3) IN interior moi_s32_cyl` THEN
      SET_TAC[];
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `connected (k:real^3->bool)` ASSUME_TAC THENL
   [SUBGOAL_THEN `k = IMAGE (g:real^3->real^3) (segment[x,q1]) UNION
                      ((g q1) INSERT ((:real^3) DIFF IMAGE g moi_s32_cyl))` SUBST1_TAC THENL
     [EXPAND_TAC "k" THEN
      MP_TAC(ISPECL [`x:real^3`; `q1:real^3`] ENDS_IN_SEGMENT) THEN SET_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC CONNECTED_UNION THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN REWRITE_TAC[CONNECTED_SEGMENT] THEN
      ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
      MATCH_MP_TAC CONNECTED_INTERMEDIATE_CLOSURE THEN
      EXISTS_TAC `(:real^3) DIFF IMAGE (g:real^3->real^3) moi_s32_cyl` THEN
      ASM_REWRITE_TAC[INSERT_SUBSET; CLOSURE_SUBSET] THEN SET_TAC[];
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `(g:real^3->real^3) q1` THEN
      REWRITE_TAC[IN_INTER; IN_INSERT] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
      REWRITE_TAC[ENDS_IN_SEGMENT]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(k:real^3->bool) SUBSET (:real^3) DIFF s` ASSUME_TAC THENL
   [EXPAND_TAC "k" THEN REWRITE_TAC[UNION_SUBSET] THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_DIFF; IN_UNIV] THEN
      X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
      SUBGOAL_THEN `~((g:real^3->real^3) y IN IMAGE g v)` MP_TAC THENL
       [MATCH_MP_TAC MOI_S3ST_AXIS_NOT_V THEN ASM SET_TAC[]; ASM SET_TAC[]];
      MP_TAC MOI_S3GF_CYL_PARTS THEN
      UNDISCH_TAC `(v:real^3->bool) SUBSET interior moi_s32_cyl` THEN
      UNDISCH_TAC `(s:real^3->bool) SUBSET IMAGE (g:real^3->real^3) v` THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~bounded (k:real^3->bool)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `bounded (k UNION IMAGE (g:real^3->real^3) moi_s32_cyl)` MP_TAC THENL
     [ASM_REWRITE_TAC[BOUNDED_UNION] THEN MATCH_MP_TAC COMPACT_IMP_BOUNDED THEN
      MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[MOI_S3GF_CYL_COMPACT];
      SUBGOAL_THEN `k UNION IMAGE (g:real^3->real^3) moi_s32_cyl = (:real^3)` SUBST1_TAC THENL
       [EXPAND_TAC "k" THEN SET_TAC[]; REWRITE_TAC[NOT_BOUNDED_UNIV]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(g:real^3->real^3) x IN k` ASSUME_TAC THENL
   [EXPAND_TAC "k" THEN REWRITE_TAC[IN_UNION] THEN DISJ1_TAC THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[ENDS_IN_SEGMENT];
    ALL_TAC] THEN
  REWRITE_TAC[outside; IN_ELIM_THM] THEN CONJ_TAC THENL
   [ASM SET_TAC[];
    DISCH_TAC THEN
    SUBGOAL_THEN `(k:real^3->bool) SUBSET
                  connected_component ((:real^3) DIFF s) ((g:real^3->real^3) x)`
    MP_TAC THENL
     [MATCH_MP_TAC CONNECTED_COMPONENT_MAXIMAL THEN ASM_REWRITE_TAC[];
      ASM_MESON_TAC[BOUNDED_SUBSET]]]);;

(* ------------------------------------------------------------------------- *)
(* Part 6: bookkeeping for the barriers.  Only finitely many level           *)
(* regions meet a small neighbourhood of a point of M other than P'; basic  *)
(* facts on the tori and the members; every barrier made of closed parts of *)
(* the even tori, a subfamily of the members and P' is closed in M;          *)
(* deleting the parts of members off K.                                     *)
(* ------------------------------------------------------------------------- *)

let MOI_S3ST_LVL_LF = prove
 (`!(g:real^3->real^3) v pp dd s2 x.
     moi_s32_model g v /\ moi_s32_tower g v pp dd s2 /\
     x IN moi_s32_open g /\ ~(x = g (vec 0))
     ==> ?u. open u /\ x IN u /\ FINITE {i:int | ~(moi_s32_lvl g dd i INTER u = {})}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                 `dd:int->real^3->bool`; `s2:int->real^3->bool`; `x:real^3`]
    MOI_S3IT_LOCAL_FINITE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^3->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `u:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `jj = {j:int | ~(IMAGE (g:real^3->real^3) (revolution (dd j)) INTER u = {})}` THEN
  MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `{i:int | &2 * i IN jj} UNION {i:int | &2 * i + &1 IN jj} UNION
              {i:int | &2 * i + &2 IN jj}` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[FINITE_UNION] THEN REPEAT CONJ_TAC THEN
    MATCH_MP_TAC FINITE_IMAGE_INJ THEN ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
    EXPAND_TAC "jj" THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_UNION; moi_s32_lvl] THEN
    X_GEN_TAC `i:int` THEN SET_TAC[]]);;

let MOI_S3ST_GV_FACTS = prove
 (`!(g:real^3->real^3) v.
     moi_s32_model g v
     ==> IMAGE g v SUBSET moi_s32_open g /\ bounded (IMAGE g v) /\
         compact (IMAGE g moi_s32_cyl) /\ open (moi_s32_open g)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`] MOI_S3GF_MODEL_OPEN) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_s32_model]) THEN
  SUBGOAL_THEN `compact (IMAGE (g:real^3->real^3) moi_s32_cyl)` ASSUME_TAC THENL
   [MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[MOI_S3GF_CYL_COMPACT];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC BOUNDED_SUBSET THEN EXISTS_TAC `IMAGE (g:real^3->real^3) moi_s32_cyl` THEN
    ASM_SIMP_TAC[COMPACT_IMP_BOUNDED] THEN MATCH_MP_TAC IMAGE_SUBSET THEN
    MP_TAC MOI_S3GF_CYL_PARTS THEN
    UNDISCH_TAC `(v:real^3->bool) SUBSET interior moi_s32_cyl` THEN SET_TAC[];
    FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC]);;

let MOI_S3ST_TORUS_BASICS = prove
 (`!(g:real^3->real^3) v pp dd s2.
     moi_s32_model g v /\ moi_s32_tower g v pp dd s2
     ==> !k. pl_solid_torus (s2 k) /\
             compact (frontier (s2 k)) /\ connected (frontier (s2 k)) /\
             frontier (s2 k) SUBSET IMAGE g (revolution (dd k)) /\
             frontier (s2 k) SUBSET IMAGE g v /\
             frontier (s2 k) SUBSET moi_s32_open g /\
             ~(g (vec 0) IN frontier (s2 k)) /\ ~(g moi_s32_qlo IN frontier (s2 k)) /\
             ~(g moi_s32_qhi IN frontier (s2 k))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `k:int` THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                 `dd:int->real^3->bool`; `s2:int->real^3->bool`] MOI_S3GF_TOWER_TORI) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(STRIP_ASSUME_TAC o SPEC `k:int`) THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                 `dd:int->real^3->bool`; `s2:int->real^3->bool`] MOI_S3I2_TORI_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(STRIP_ASSUME_TAC o SPEC `k:int` o CONJUNCT1) THEN
  MP_TAC(ISPEC `(s2:int->real^3->bool) k` MOI_S3ST_TORUS_FR) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN ASM SET_TAC[]);;

let MOI_S3ST_TORI_DISJ = prove
 (`!(g:real^3->real^3) v pp dd s2 i k.
     moi_s32_model g v /\ moi_s32_tower g v pp dd s2 /\ ~(i = k)
     ==> DISJOINT (frontier (s2 (&2 * i))) (frontier (s2 (&2 * k)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                 `dd:int->real^3->bool`; `s2:int->real^3->bool`; `&2 * i:int`; `&2 * k:int`]
    MOI_S3I2_FAR_TORI) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_INT_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                 `dd:int->real^3->bool`; `s2:int->real^3->bool`] MOI_S3I2_TORI_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN
  DISCH_THEN(fun th -> MP_TAC(SPEC `&2 * i:int` th) THEN MP_TAC(SPEC `&2 * k:int` th)) THEN
  SET_TAC[]);;

let MOI_S3ST_LVL_TORUS = prove
 (`!(g:real^3->real^3) v pp dd s2 i k.
     moi_s32_model g v /\ moi_s32_tower g v pp dd s2 /\ ~(k = i) /\ ~(k = i + &1)
     ==> DISJOINT (moi_s32_lvl g dd i) (frontier (s2 (&2 * k)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                 `dd:int->real^3->bool`; `s2:int->real^3->bool`; `i:int`; `k:int`]
    MOI_S3IT_LVL_AWAY) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                 `dd:int->real^3->bool`; `s2:int->real^3->bool`] MOI_S3GF_TOWER_TORI) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `&2 * k:int`) THEN SET_TAC[]);;

let MOI_S3ST_TORI_IN_LVL = prove
 (`!(g:real^3->real^3) v pp dd s2 i.
     moi_s32_tower g v pp dd s2
     ==> frontier (s2 (&2 * i)) SUBSET moi_s32_lvl g dd i /\
         frontier (s2 (&2 * i + &2)) SUBSET moi_s32_lvl g dd i`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                 `dd:int->real^3->bool`; `s2:int->real^3->bool`] MOI_S3GF_TOWER_TORI) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> MP_TAC(SPEC `&2 * i:int` th) THEN MP_TAC(SPEC `&2 * i + &2:int` th)) THEN
  REWRITE_TAC[moi_s32_lvl] THEN SET_TAC[]);;

let MOI_S3ST_MEMBER = prove
 (`!(g:real^3->real^3) v pp dd s2 lev fam c.
     moi_s32_model g v /\ moi_s32_tower g v pp dd s2 /\
     moi_s32_state g dd s2 lev fam /\ c IN fam
     ==> compact c /\ connected c /\ ~(c = {}) /\ c SUBSET IMAGE g v /\
         c SUBSET moi_s32_open g /\
         ~(g (vec 0) IN c) /\ ~(g moi_s32_qlo IN c) /\ ~(g moi_s32_qhi IN c) /\
         ?cc. FINITE cc /\ combinatorial_manifold_with_boundary 2 cc /\ UNIONS cc = c /\
              surface_boundary cc = c INTER moi_s32_evens s2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                 `dd:int->real^3->bool`; `s2:int->real^3->bool`; `lev:int->bool`;
                 `fam:(real^3->bool)->bool`; `c:real^3->bool`] MOI_S3IT_MEMBER_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`] MOI_S3ST_POINTS_NOT_V) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`] MOI_S3ST_GV_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `moi_s32_state g dd s2 lev fam` THEN REWRITE_TAC[moi_s32_state] THEN
  DISCH_THEN(MP_TAC o SPEC `c:real^3->bool` o CONJUNCT1 o CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `i':int` (X_CHOOSE_THEN `cc:(real^3->bool)->bool`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `compact (c:real^3->bool)` ASSUME_TAC THENL
   [REWRITE_TAC[COMPACT_EQ_BOUNDED_CLOSED] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[BOUNDED_SUBSET];
      MP_TAC(ISPEC `cc:(real^3->bool)->bool` MOI_S6G_CM_CLOSED) THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(c:real^3->bool) SUBSET moi_s32_open g` ASSUME_TAC THENL
   [ASM_MESON_TAC[SUBSET_TRANS]; ALL_TAC] THEN
  SUBGOAL_THEN `~((g:real^3->real^3) (vec 0) IN c) /\ ~(g moi_s32_qlo IN c) /\
                ~(g moi_s32_qhi IN c)` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN EXISTS_TAC `cc:(real^3->bool)->bool` THEN ASM_REWRITE_TAC[]);;

let MOI_S3ST_STATE_LF = prove
 (`!(g:real^3->real^3) dd s2 lev fam.
     moi_s32_state g dd s2 lev fam
     ==> ?lf. !c. c IN fam ==> c SUBSET moi_s32_lvl g dd (lf c)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s32_state] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!c. ?i. c IN fam ==> c SUBSET moi_s32_lvl g dd i` MP_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_TAC `lf:(real^3->bool)->int`) THEN
  EXISTS_TAC `lf:(real^3->bool)->int` THEN ASM_REWRITE_TAC[]);;

let MOI_S3ST_IN_COND_EMPTY = prove
 (`!p (t:real^3->bool) y. y IN (if p then t else {}) <=> p /\ y IN t`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[NOT_IN_EMPTY]);;

(* Every barrier made of closed parts tp i of the even tori T_(2i), i in s, *)
(* a subfamily ff of the members and P' is closed in M (locally finite).   *)

let MOI_S3ST_BARRIER_CLOSED = prove
 (`!(g:real^3->real^3) v pp dd s2 lev fam ff s tp.
     moi_s32_model g v /\ moi_s32_tower g v pp dd s2 /\
     moi_s32_state g dd s2 lev fam /\ ff SUBSET fam /\
     (!i. i IN s ==> closed (tp i) /\ tp i SUBSET frontier (s2 (&2 * i)))
     ==> closed_in (subtopology euclidean (moi_s32_open g))
                   (UNIONS {tp i | i IN s} UNION UNIONS ff UNION {g (vec 0)})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_TAC `lf:(real^3->bool)->int` o MATCH_MP MOI_S3ST_STATE_LF) THEN
  ABBREV_TAC `a = \i:int. (if i IN s then (tp:int->real^3->bool) i else {}) UNION
                          UNIONS {c | c IN ff /\ (lf:(real^3->bool)->int) c = i}` THEN
  SUBGOAL_THEN `UNIONS {(tp:int->real^3->bool) i | i IN (s:int->bool)} UNION
                UNIONS (ff:(real^3->bool)->bool) UNION {(g:real^3->real^3) (vec 0)} =
                UNIONS {(a:int->real^3->bool) i | i IN (:int)} UNION {g (vec 0)}`
  SUBST1_TAC THENL
   [MATCH_MP_TAC(SET_RULE `(x UNION y:real^3->bool) = w ==> x UNION y UNION z = w UNION z`) THEN
    GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `y:real^3` THEN
    EXPAND_TAC "a" THEN
    REWRITE_TAC[UNIONS_GSPEC] THEN
    REWRITE_TAC[IN_ELIM_THM; IN_UNIONS; IN_UNION; IN_UNIV; MOI_S3ST_IN_COND_EMPTY] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                 `dd:int->real^3->bool`; `s2:int->real^3->bool`] MOI_S3ST_TORUS_BASICS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`] MOI_S3ST_GV_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!i. (a:int->real^3->bool) i SUBSET moi_s32_lvl g dd i` ASSUME_TAC THENL
   [X_GEN_TAC `i:int` THEN EXPAND_TAC "a" THEN REWRITE_TAC[UNION_SUBSET] THEN CONJ_TAC THENL
     [COND_CASES_TAC THEN REWRITE_TAC[EMPTY_SUBSET] THEN
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `frontier ((s2:int->real^3->bool) (&2 * i))` THEN
      ASM_SIMP_TAC[] THEN
      MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                     `dd:int->real^3->bool`; `s2:int->real^3->bool`; `i:int`]
        MOI_S3ST_TORI_IN_LVL) THEN ASM_SIMP_TAC[];
      REWRITE_TAC[UNIONS_SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `c:real^3->bool` THEN
      STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_S3I2_LF_CLOSED_IN THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `i:int` THEN EXPAND_TAC "a" THEN MATCH_MP_TAC CLOSED_UNION THEN CONJ_TAC THENL
     [COND_CASES_TAC THEN ASM_SIMP_TAC[CLOSED_EMPTY]; ALL_TAC] THEN
    MATCH_MP_TAC CLOSED_UNIONS THEN CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `{c | c IN fam /\ c SUBSET moi_s32_lvl (g:real^3->real^3) dd i}` THEN
      CONJ_TAC THENL
       [UNDISCH_TAC `moi_s32_state g dd s2 lev fam` THEN REWRITE_TAC[moi_s32_state] THEN
        STRIP_TAC THEN ASM_REWRITE_TAC[];
        GEN_REWRITE_TAC I [SUBSET] THEN REWRITE_TAC[IN_ELIM_THM] THEN
        X_GEN_TAC `c:real^3->bool` THEN STRIP_TAC THEN
        CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
        FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]];
      REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `c:real^3->bool` THEN STRIP_TAC THEN
      MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
      MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                     `dd:int->real^3->bool`; `s2:int->real^3->bool`; `lev:int->bool`;
                     `fam:(real^3->bool)->bool`; `c:real^3->bool`] MOI_S3ST_MEMBER) THEN
      ANTS_TAC THENL [ASM SET_TAC[]; SIMP_TAC[]]];
    X_GEN_TAC `i:int` THEN MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `moi_s32_lvl (g:real^3->real^3) dd i` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `IMAGE (g:real^3->real^3) v` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_S3IT_LVL_IN_V THEN
    MAP_EVERY EXISTS_TAC [`pp:int->real^3`; `s2:int->real^3->bool`] THEN ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                   `dd:int->real^3->bool`; `s2:int->real^3->bool`] MOI_S3I2_TORI_FACTS) THEN
    ASM_SIMP_TAC[];
    X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                   `dd:int->real^3->bool`; `s2:int->real^3->bool`; `x:real^3`]
      MOI_S3ST_LVL_LF) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC `u:real^3->bool` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{i:int | ~(moi_s32_lvl (g:real^3->real^3) dd i INTER u = {})}` THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `!i. (a:int->real^3->bool) i SUBSET moi_s32_lvl g dd i` THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN SET_TAC[]]);;

let MOI_S3ST_SUBFAM_CLOSED = prove
 (`!(g:real^3->real^3) v pp dd s2 lev fam ff.
     moi_s32_model g v /\ moi_s32_tower g v pp dd s2 /\
     moi_s32_state g dd s2 lev fam /\ ff SUBSET fam
     ==> closed_in (subtopology euclidean (moi_s32_open g)) (moi_s32_set g s2 ff)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                 `dd:int->real^3->bool`; `s2:int->real^3->bool`; `lev:int->bool`;
                 `fam:(real^3->bool)->bool`; `ff:(real^3->bool)->bool`; `(:int)`;
                 `\i:int. frontier ((s2:int->real^3->bool) (&2 * i))`]
    MOI_S3ST_BARRIER_CLOSED) THEN
  REWRITE_TAC[moi_s32_set; moi_s32_evens] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[IN_UNIV; SUBSET_REFL; FRONTIER_CLOSED]);;

(* Deleting the parts off K of the members in d.                           *)

let MOI_S3ST_DEL_EQ = prove
 (`!(g:real^3->real^3) s2 fam d.
     pairwise DISJOINT fam /\ d SUBSET fam /\ (!c. c IN fam ==> ~(g (vec 0) IN c))
     ==> moi_s32_set g s2 fam DIFF UNIONS (IMAGE (\c. c DIFF moi_s32_evens s2) d) =
         moi_s32_set g s2 (fam DIFF d)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pairwise; moi_s32_set] THEN STRIP_TAC THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `y:real^3` THEN
  REWRITE_TAC[IN_DIFF; IN_UNION; IN_UNIONS; EXISTS_IN_IMAGE; IN_SING] THEN
  ASM_CASES_TAC `(y:real^3) IN moi_s32_evens s2` THEN ASM_REWRITE_TAC[] THEN
  EQ_TAC THENL
   [STRIP_TAC THENL
     [DISJ1_TAC THEN EXISTS_TAC `t:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
      DISCH_TAC THEN UNDISCH_TAC `~(?x. x IN d /\ (y:real^3) IN x)` THEN
      REWRITE_TAC[] THEN EXISTS_TAC `t:real^3->bool` THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[]];
    STRIP_TAC THENL
     [CONJ_TAC THENL
       [DISJ1_TAC THEN EXISTS_TAC `t:real^3->bool` THEN ASM_REWRITE_TAC[];
        DISCH_THEN(X_CHOOSE_THEN `c:real^3->bool` STRIP_ASSUME_TAC) THEN
        SUBGOAL_THEN `DISJOINT (c:real^3->bool) t` MP_TAC THENL
         [FIRST_X_ASSUM MATCH_MP_TAC THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
          ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN ASM_MESON_TAC[];
          ASM SET_TAC[]]];
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[SUBSET]]]);;

(* ------------------------------------------------------------------------- *)
(* Part 7: every level i carries a Type 3 bridge, a member c in the          *)
(* level region with ends j on T_(2i) and j' on T_(2i+2).  Otherwise the      *)
(* barrier is the disjoint union of the closed sets A (the tori T_(2k),      *)
(* k <= i, the members inside g(rev(dd j)), j <= 2i+2, off the outer tori,    *)
(* and P') and B (the rest, which stays away from P'); A misses a path       *)
(* hugging the frontier of the model and B misses the axis path, so neither *)
(* separates, against 30.1 (MOISE_301).                                      *)
(* ------------------------------------------------------------------------- *)

let MOI_S3ST_DISJ_UNIONS = prove
 (`!(s:real^3->bool) (f:int->real^3->bool) P.
     DISJOINT s (UNIONS {f k | P k}) <=> !k. P k ==> DISJOINT s (f k)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[UNIONS_GSPEC] THEN SET_TAC[]);;

let MOI_S3ST_LVL_SUB = prove
 (`!(g:real^3->real^3) dd i P.
     P (&2 * i) /\ P (&2 * i + &1) /\ P (&2 * i + &2)
     ==> moi_s32_lvl g dd i SUBSET IMAGE g (UNIONS {revolution (dd j) | P j})`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[moi_s32_lvl; UNION_SUBSET] THEN
  REPEAT CONJ_TAC THEN MATCH_MP_TAC IMAGE_SUBSET THEN
  MATCH_MP_TAC(SET_RULE `(x:real^3->bool) IN f ==> x SUBSET UNIONS f`) THEN
  REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[]);;

let MOI_S3ST_TORUS_IN_Q = prove
 (`!(g:real^3->real^3) v pp dd s2 P k.
     moi_s32_tower g v pp dd s2 /\ P k
     ==> frontier (s2 k) SUBSET IMAGE g (UNIONS {revolution (dd j) | P j})`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_TRANS THEN
  EXISTS_TAC `IMAGE (g:real^3->real^3) (revolution ((dd:int->real^3->bool) k))` THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                   `dd:int->real^3->bool`; `s2:int->real^3->bool`] MOI_S3GF_TOWER_TORI) THEN
    ASM_SIMP_TAC[];
    MATCH_MP_TAC IMAGE_SUBSET THEN
    MATCH_MP_TAC(SET_RULE `(x:real^3->bool) IN f ==> x SUBSET UNIONS f`) THEN
    REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[]]);;

(* A member not in the inner family A misses the inner tori T_(2k), k <= i, *)
(* and lies in g of the cells rev(dd j), j >= 2i (no bridge at level i).    *)

let MOI_S3ST_FAMB_FACT = prove
 (`!(g:real^3->real^3) v pp dd s2 fam i c.
     moi_s32_model g v /\ moi_s32_tower g v pp dd s2 /\ moi_s32_reduced g dd s2 fam /\
     (!c j j'. ~(c IN fam /\ c SUBSET moi_s32_lvl g dd i /\ pl_annulus_with_ends c j j' /\
                 c INTER moi_s32_evens s2 = j UNION j' /\
                 moi_s32_ess s2 (&2 * i) j /\ moi_s32_ess s2 (&2 * i + &2) j')) /\
     c IN fam /\
     ~(c SUBSET IMAGE g (UNIONS {revolution (dd j) | j <= &2 * i + &2}) /\
       DISJOINT c (UNIONS {frontier (s2 (&2 * k)) | i + &1 <= k}))
     ==> DISJOINT c (UNIONS {frontier (s2 (&2 * k)) | k <= i}) /\
         c SUBSET IMAGE g (UNIONS {revolution (dd j) | &2 * i <= j})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `moi_s32_reduced g dd s2 fam` THEN REWRITE_TAC[moi_s32_reduced] THEN
  DISCH_THEN(MP_TAC o SPEC `c:real^3->bool` o CONJUNCT2) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:int` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ty"))) THEN
  SUBGOAL_THEN `!m:int. ~(m = k) /\ ~(m = k + &1)
                        ==> DISJOINT (c:real^3->bool)
                                     (frontier ((s2:int->real^3->bool) (&2 * m)))`
  (LABEL_TAC "away") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                   `dd:int->real^3->bool`; `s2:int->real^3->bool`; `k:int`; `m:int`]
      MOI_S3ST_LVL_TORUS) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(c:real^3->bool) SUBSET moi_s32_lvl g dd k` THEN SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[MOI_S3ST_DISJ_UNIONS] THEN
  ASM_CASES_TAC `(k:int) <= i - &1` THENL
   [UNDISCH_TAC `~((c:real^3->bool) SUBSET
                    IMAGE g (UNIONS {revolution ((dd:int->real^3->bool) j) | j <= &2 * i + &2}) /\
                   DISJOINT c (UNIONS {frontier ((s2:int->real^3->bool) (&2 * k)) |
                                       i + &1 <= k}))` THEN
    MATCH_MP_TAC(TAUT `p ==> ~p ==> q`) THEN REWRITE_TAC[MOI_S3ST_DISJ_UNIONS] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `moi_s32_lvl (g:real^3->real^3) dd k` THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(BETA_RULE(ISPECL [`g:real^3->real^3`; `dd:int->real^3->bool`; `k:int`;
                                     `\j:int. j <= &2 * i + &2`] MOI_S3ST_LVL_SUB)) THEN
      ASM_INT_ARITH_TAC;
      X_GEN_TAC `l:int` THEN DISCH_TAC THEN USE_THEN "away" MATCH_MP_TAC THEN
      ASM_INT_ARITH_TAC];
    ALL_TAC] THEN
  DISJ_CASES_TAC(TAUT `~(k:int = i) \/ k = i`) THENL
   [CONJ_TAC THENL
     [X_GEN_TAC `m:int` THEN DISCH_TAC THEN USE_THEN "away" MATCH_MP_TAC THEN
      ASM_INT_ARITH_TAC;
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `moi_s32_lvl (g:real^3->real^3) dd k` THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(BETA_RULE(ISPECL [`g:real^3->real^3`; `dd:int->real^3->bool`; `k:int`;
                                     `\j:int. &2 * i <= j`] MOI_S3ST_LVL_SUB)) THEN
      ASM_INT_ARITH_TAC];
    ALL_TAC] THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  SUBGOAL_THEN `(c:real^3->bool) SUBSET
                IMAGE g (UNIONS {revolution ((dd:int->real^3->bool) j) | j <= &2 * i + &2})`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `moi_s32_lvl (g:real^3->real^3) dd i` THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(BETA_RULE(ISPECL [`g:real^3->real^3`; `dd:int->real^3->bool`; `i:int`;
                                   `\j:int. j <= &2 * i + &2`] MOI_S3ST_LVL_SUB)) THEN
    INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~DISJOINT (c:real^3->bool) (frontier ((s2:int->real^3->bool) (&2 * i + &2)))` ASSUME_TAC THENL
   [DISCH_TAC THEN
    UNDISCH_TAC `~((c:real^3->bool) SUBSET
                    IMAGE g (UNIONS {revolution ((dd:int->real^3->bool) j) | j <= &2 * i + &2}) /\
                   DISJOINT c (UNIONS {frontier ((s2:int->real^3->bool) (&2 * k)) |
                                       i + &1 <= k}))` THEN
    ASM_REWRITE_TAC[MOI_S3ST_DISJ_UNIONS] THEN X_GEN_TAC `l:int` THEN DISCH_TAC THEN
    ASM_CASES_TAC `l:int = i + &1` THENL
     [ASM_REWRITE_TAC[INT_ARITH `&2 * (i + &1):int = &2 * i + &2`];
      USE_THEN "away" MATCH_MP_TAC THEN ASM_INT_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `frontier ((s2:int->real^3->bool) (&2 * i + &2)) SUBSET moi_s32_evens s2 /\
                DISJOINT (frontier (s2 (&2 * i))) (frontier (s2 (&2 * i + &2)))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[moi_s32_evens] THEN
      MATCH_MP_TAC(SET_RULE `(x:real^3->bool) IN f ==> x SUBSET UNIONS f`) THEN
      REWRITE_TAC[IN_ELIM_THM; IN_UNIV] THEN EXISTS_TAC `i + &1:int` THEN
      REWRITE_TAC[INT_ARITH `&2 * (i + &1):int = &2 * i + &2`];
      MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                     `dd:int->real^3->bool`; `s2:int->real^3->bool`; `i:int`; `i + &1:int`]
        MOI_S3ST_TORI_DISJ) THEN
      ASM_REWRITE_TAC[INT_ARITH `&2 * (i + &1):int = &2 * i + &2`] THEN
      DISCH_THEN MATCH_MP_TAC THEN INT_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `q /\ p ==> p /\ q`) THEN CONJ_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `moi_s32_lvl (g:real^3->real^3) dd i` THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(BETA_RULE(ISPECL [`g:real^3->real^3`; `dd:int->real^3->bool`; `i:int`;
                                   `\j:int. &2 * i <= j`] MOI_S3ST_LVL_SUB)) THEN
    INT_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `m:int` THEN DISCH_TAC THEN
  DISJ_CASES_TAC(TAUT `~(m:int = i) \/ m = i`) THENL
   [USE_THEN "away" MATCH_MP_TAC THEN ASM_INT_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  REMOVE_THEN "ty" (DISJ_CASES_THEN2 ASSUME_TAC MP_TAC) THENL
   [UNDISCH_TAC `~DISJOINT (c:real^3->bool) (frontier ((s2:int->real^3->bool) (&2 * i + &2)))` THEN
    UNDISCH_TAC `frontier ((s2:int->real^3->bool) (&2 * i + &2)) SUBSET moi_s32_evens s2` THEN
    UNDISCH_TAC `DISJOINT (c:real^3->bool) (moi_s32_evens s2)` THEN SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `j:real^3->bool` (X_CHOOSE_THEN `j':real^3->bool`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC))))) THEN
  SUBGOAL_THEN
   `(moi_s32_ess s2 (&2 * i) j /\ moi_s32_ess s2 (&2 * i) j') \/
    (moi_s32_ess s2 (&2 * i + &2) j /\ moi_s32_ess s2 (&2 * i) j') \/
    (moi_s32_ess s2 (&2 * i) j /\ moi_s32_ess s2 (&2 * i + &2) j') \/
    (moi_s32_ess s2 (&2 * i + &2) j /\ moi_s32_ess s2 (&2 * i + &2) j')` MP_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  STRIP_TAC THENL
   [(* both ends on T_(2i): then c misses T_(2i+2) *)
    SUBGOAL_THEN `(c:real^3->bool) INTER moi_s32_evens s2 SUBSET frontier (s2 (&2 * i))`
    ASSUME_TAC THENL
     [ASM_REWRITE_TAC[UNION_SUBSET] THEN ASM_MESON_TAC[moi_s32_ess]; ALL_TAC] THEN
    UNDISCH_TAC `~DISJOINT (c:real^3->bool) (frontier ((s2:int->real^3->bool) (&2 * i + &2)))` THEN
    UNDISCH_TAC `frontier ((s2:int->real^3->bool) (&2 * i + &2)) SUBSET moi_s32_evens s2` THEN
    UNDISCH_TAC `DISJOINT (frontier ((s2:int->real^3->bool) (&2 * i)))
                          (frontier (s2 (&2 * i + &2)))` THEN
    UNDISCH_TAC `(c:real^3->bool) INTER moi_s32_evens s2 SUBSET frontier (s2 (&2 * i))` THEN
    SET_TAC[];
    (* j on T_(2i+2), j' on T_(2i): a bridge with the ends swapped *)
    FIRST_X_ASSUM(MP_TAC o SPECL [`c:real^3->bool`; `j':real^3->bool`; `j:real^3->bool`]) THEN
    ASM_SIMP_TAC[MOI_S3ST_ANN_SYM] THEN SET_TAC[];
    (* j on T_(2i), j' on T_(2i+2): a bridge *)
    FIRST_X_ASSUM(MP_TAC o SPECL [`c:real^3->bool`; `j:real^3->bool`; `j':real^3->bool`]) THEN
    ASM_REWRITE_TAC[];
    (* both ends on T_(2i+2): then c misses T_(2i) *)
    SUBGOAL_THEN `(c:real^3->bool) INTER moi_s32_evens s2 SUBSET frontier (s2 (&2 * i + &2))`
    ASSUME_TAC THENL
     [ASM_REWRITE_TAC[UNION_SUBSET] THEN ASM_MESON_TAC[moi_s32_ess]; ALL_TAC] THEN
    SUBGOAL_THEN `frontier ((s2:int->real^3->bool) (&2 * i)) SUBSET moi_s32_evens s2`
    ASSUME_TAC THENL
     [REWRITE_TAC[moi_s32_evens] THEN
      MATCH_MP_TAC(SET_RULE `(x:real^3->bool) IN f ==> x SUBSET UNIONS f`) THEN
      REWRITE_TAC[IN_ELIM_THM; IN_UNIV] THEN MESON_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `frontier ((s2:int->real^3->bool) (&2 * i)) SUBSET moi_s32_evens s2` THEN
    UNDISCH_TAC `DISJOINT (frontier ((s2:int->real^3->bool) (&2 * i)))
                          (frontier (s2 (&2 * i + &2)))` THEN
    UNDISCH_TAC `(c:real^3->bool) INTER moi_s32_evens s2 SUBSET
                 frontier (s2 (&2 * i + &2))` THEN
    SET_TAC[]]);;

let MOI_S3ST_BRIDGE_EXISTS = prove
 (`!(g:real^3->real^3) v pp dd s2 fam i.
     MOISE_301_STATEMENT /\ moi_s32_model g v /\ moi_s32_tower g v pp dd s2 /\
     moi_s32_reduced g dd s2 fam
     ==> ?c j j'. c IN fam /\ c SUBSET moi_s32_lvl g dd i /\ pl_annulus_with_ends c j j' /\
                 c INTER moi_s32_evens s2 = j UNION j' /\
                 moi_s32_ess s2 (&2 * i) j /\ moi_s32_ess s2 (&2 * i + &2) j'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
  DISCH_THEN(ASSUME_TAC o REWRITE_RULE[NOT_EXISTS_THM]) THEN
  SUBGOAL_THEN `moi_s32_state g dd s2 (:int) fam` ASSUME_TAC THENL
   [UNDISCH_TAC `moi_s32_reduced g dd s2 fam` THEN SIMP_TAC[moi_s32_reduced]; ALL_TAC] THEN
  SUBGOAL_THEN `pairwise DISJOINT (fam:(real^3->bool)->bool) /\
                separates_in (moi_s32_open g) (moi_s32_set g s2 fam)
                             {(g:real^3->real^3) moi_s32_qlo} {g moi_s32_qhi}`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `moi_s32_state g dd s2 (:int) fam` THEN SIMP_TAC[moi_s32_state]; ALL_TAC] THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                 `dd:int->real^3->bool`; `s2:int->real^3->bool`] MOI_S3ST_TORUS_BASICS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                 `dd:int->real^3->bool`; `s2:int->real^3->bool`] MOI_S3I2_TORI_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`] MOI_S3ST_GV_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`] MOI_S3ST_POINTS_NOT_V) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!c. c IN fam ==> c SUBSET IMAGE (g:real^3->real^3) v /\ ~(g (vec 0) IN c)`
  ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                   `dd:int->real^3->bool`; `s2:int->real^3->bool`; `(:int)`;
                   `fam:(real^3->bool)->bool`; `c:real^3->bool`] MOI_S3ST_MEMBER) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((g:real^3->real^3) moi_s32_qlo IN moi_s32_set g s2 fam) /\
                ~(g moi_s32_qhi IN moi_s32_set g s2 fam)` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`moi_s32_open g`; `moi_s32_set g s2 fam`;
                   `(g:real^3->real^3) moi_s32_qlo`; `(g:real^3->real^3) moi_s32_qhi`]
      MOI_S3ST_SEP_OPEN) THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `kin = UNIONS {frontier ((s2:int->real^3->bool) (&2 * k)) | k <= i}` THEN
  ABBREV_TAC `kout = UNIONS {frontier ((s2:int->real^3->bool) (&2 * k)) | i + &1 <= k}` THEN
  ABBREV_TAC `qi = IMAGE (g:real^3->real^3)
                     (UNIONS {revolution ((dd:int->real^3->bool) j) | j <= &2 * i + &2})` THEN
  ABBREV_TAC `q2 = IMAGE (g:real^3->real^3)
                     (UNIONS {revolution ((dd:int->real^3->bool) j) | &2 * i <= j})` THEN
  ABBREV_TAC `famA = {c:real^3->bool | c IN fam /\ c SUBSET qi /\ DISJOINT c kout}` THEN
  ABBREV_TAC `famB = {c:real^3->bool | c IN fam /\ ~(c SUBSET qi /\ DISJOINT c kout)}` THEN
  SUBGOAL_THEN `famA SUBSET fam /\ famB SUBSET fam /\ famA UNION famB = fam /\
                DISJOINT famA (famB:(real^3->bool)->bool)` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["famA"; "famB"] THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!c:real^3->bool. c IN famB ==> DISJOINT c kin /\ c SUBSET q2` ASSUME_TAC THENL
   [X_GEN_TAC `c:real^3->bool` THEN EXPAND_TAC "famB" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    STRIP_TAC THEN MAP_EVERY EXPAND_TAC ["kin"; "q2"] THEN
    MATCH_MP_TAC MOI_S3ST_FAMB_FACT THEN
    MAP_EVERY EXISTS_TAC [`v:real^3->bool`; `pp:int->real^3`; `fam:(real^3->bool)->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `kin SUBSET qi /\ kout SUBSET q2 /\ kout SUBSET IMAGE (g:real^3->real^3) v /\
                DISJOINT kin kout /\ ~(g (vec 0) IN kout)` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["kin"; "kout"; "qi"; "q2"] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC] THEN X_GEN_TAC `k:int` THEN DISCH_TAC THEN
      MATCH_MP_TAC(BETA_RULE(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                                     `dd:int->real^3->bool`; `s2:int->real^3->bool`;
                                     `\j:int. j <= &2 * i + &2`] MOI_S3ST_TORUS_IN_Q)) THEN
      ASM_REWRITE_TAC[] THEN ASM_INT_ARITH_TAC;
      REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC] THEN X_GEN_TAC `k:int` THEN DISCH_TAC THEN
      MATCH_MP_TAC(BETA_RULE(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                                     `dd:int->real^3->bool`; `s2:int->real^3->bool`;
                                     `\j:int. &2 * i <= j`] MOI_S3ST_TORUS_IN_Q)) THEN
      ASM_REWRITE_TAC[] THEN ASM_INT_ARITH_TAC;
      REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC] THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[MOI_S3ST_DISJ_UNIONS] THEN X_GEN_TAC `l:int` THEN DISCH_TAC THEN
      ONCE_REWRITE_TAC[DISJOINT_SYM] THEN REWRITE_TAC[MOI_S3ST_DISJ_UNIONS] THEN
      X_GEN_TAC `m:int` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                     `dd:int->real^3->bool`; `s2:int->real^3->bool`; `l:int`; `m:int`]
        MOI_S3ST_TORI_DISJ) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_INT_ARITH_TAC;
      REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM] THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `UNIONS famA SUBSET qi /\ DISJOINT (UNIONS famA) kout /\
                UNIONS famB SUBSET q2 /\ DISJOINT kin (UNIONS famB) /\
                UNIONS famB SUBSET IMAGE (g:real^3->real^3) v /\
                ~(g (vec 0) IN UNIONS famB) /\
                DISJOINT (UNIONS famA) (UNIONS famB)` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [EXPAND_TAC "famA" THEN REWRITE_TAC[UNIONS_SUBSET; IN_ELIM_THM] THEN SIMP_TAC[];
      MATCH_MP_TAC(SET_RULE `(!s. s IN f ==> DISJOINT s k) ==> DISJOINT (UNIONS f) (k:real^3->bool)`) THEN
      EXPAND_TAC "famA" THEN REWRITE_TAC[IN_ELIM_THM] THEN SIMP_TAC[];
      REWRITE_TAC[UNIONS_SUBSET] THEN ASM_SIMP_TAC[];
      MATCH_MP_TAC(SET_RULE `(!s. s IN f ==> DISJOINT s k) ==> DISJOINT (k:real^3->bool) (UNIONS f)`) THEN
      ASM_SIMP_TAC[];
      REWRITE_TAC[UNIONS_SUBSET] THEN ASM SET_TAC[];
      REWRITE_TAC[IN_UNIONS] THEN ASM SET_TAC[];
      MATCH_MP_TAC(SET_RULE `(!s t. s IN f /\ t IN h ==> DISJOINT s t)
                             ==> DISJOINT (UNIONS f) (UNIONS (h:(real^3->bool)->bool))`) THEN
      MAP_EVERY X_GEN_TAC [`s:real^3->bool`; `t:real^3->bool`] THEN STRIP_TAC THEN
      UNDISCH_TAC `pairwise DISJOINT (fam:(real^3->bool)->bool)` THEN
      REWRITE_TAC[pairwise] THEN DISCH_THEN MATCH_MP_TAC THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_s32_evens s2 = kin UNION kout` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["kin"; "kout"] THEN REWRITE_TAC[moi_s32_evens; UNIONS_GSPEC] THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_UNION; IN_UNIV] THEN
    MESON_TAC[INT_ARITH `!k i:int. k <= i \/ i + &1 <= k`];
    ALL_TAC] THEN
  SUBGOAL_THEN `(kin UNION UNIONS famA UNION {(g:real^3->real^3) (vec 0)}) UNION
                (kout UNION UNIONS famB) = moi_s32_set g s2 fam` (LABEL_TAC "xab") THENL
   [REWRITE_TAC[moi_s32_set] THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `famA UNION famB = (fam:(real^3->bool)->bool)` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[UNIONS_UNION] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `DISJOINT (kin UNION UNIONS famA UNION {(g:real^3->real^3) (vec 0)})
                         (kout UNION UNIONS famB)` ASSUME_TAC THENL
   [UNDISCH_TAC `DISJOINT kin (kout:real^3->bool)` THEN
    UNDISCH_TAC `DISJOINT (kin:real^3->bool) (UNIONS famB)` THEN
    UNDISCH_TAC `DISJOINT (UNIONS famA) (kout:real^3->bool)` THEN
    UNDISCH_TAC `DISJOINT (UNIONS famA) (UNIONS (famB:(real^3->bool)->bool))` THEN
    UNDISCH_TAC `~((g:real^3->real^3) (vec 0) IN kout)` THEN
    UNDISCH_TAC `~((g:real^3->real^3) (vec 0) IN UNIONS famB)` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `closed_in (subtopology euclidean (moi_s32_open g))
                  (kin UNION UNIONS famA UNION {(g:real^3->real^3) (vec 0)})` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                   `dd:int->real^3->bool`; `s2:int->real^3->bool`; `(:int)`;
                   `fam:(real^3->bool)->bool`; `famA:(real^3->bool)->bool`; `{k:int | k <= i}`;
                   `\k:int. frontier ((s2:int->real^3->bool) (&2 * k))`]
      MOI_S3ST_BARRIER_CLOSED) THEN
    BETA_TAC THEN REWRITE_TAC[IN_ELIM_THM] THEN
    ASM_REWRITE_TAC[FRONTIER_CLOSED; SUBSET_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `closed_in (subtopology euclidean (moi_s32_open g)) (kout UNION UNIONS famB)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                   `dd:int->real^3->bool`; `s2:int->real^3->bool`; `(:int)`;
                   `fam:(real^3->bool)->bool`; `famB:(real^3->bool)->bool`;
                   `{k:int | i + &1 <= k}`;
                   `\k:int. frontier ((s2:int->real^3->bool) (&2 * k))`]
      MOI_S3ST_BARRIER_CLOSED) THEN
    BETA_TAC THEN REWRITE_TAC[IN_ELIM_THM] THEN
    ASM_REWRITE_TAC[FRONTIER_CLOSED; SUBSET_REFL] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                   `dd:int->real^3->bool`; `s2:int->real^3->bool`; `&2 * i:int`]
      MOI_S3ST_OUTER_AWAY) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `u:real^3->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `kout UNION UNIONS famB =
                  (kout UNION UNIONS famB UNION {(g:real^3->real^3) (vec 0)}) DIFF
                  (moi_s32_open g INTER u)` SUBST1_TAC THENL
     [UNDISCH_TAC `(kout:real^3->bool) SUBSET q2` THEN
      UNDISCH_TAC `UNIONS famB SUBSET (q2:real^3->bool)` THEN
      UNDISCH_TAC `DISJOINT u (q2:real^3->bool)` THEN
      UNDISCH_TAC `(g:real^3->real^3) (vec 0) IN u` THEN
      UNDISCH_TAC `(g:real^3->real^3) (vec 0) IN moi_s32_open g` THEN
      SET_TAC[];
      MATCH_MP_TAC CLOSED_IN_DIFF THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC OPEN_IN_OPEN_INTER THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [MOISE_301_STATEMENT]) THEN
  DISCH_THEN(MP_TAC o SPECL
   [`moi_s32_open g`; `kin UNION UNIONS famA UNION {(g:real^3->real^3) (vec 0)}`;
    `(kout:real^3->bool) UNION UNIONS (famB:(real^3->bool)->bool)`; `{(g:real^3->real^3) moi_s32_qlo}`;
    `{(g:real^3->real^3) moi_s32_qhi}`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[CLOSED_IN_SING; CONNECTED_SING; NOT_INSERT_EMPTY] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MOI_S3ST_M_SIMPLY_CONNECTED THEN EXISTS_TAC `v:real^3->bool` THEN
      ASM_REWRITE_TAC[];
      ASM SET_TAC[];
      UNDISCH_TAC `~((g:real^3->real^3) moi_s32_qlo IN moi_s32_set g s2 fam)` THEN
      USE_THEN "xab" (fun th -> REWRITE_TAC[GSYM th]) THEN SET_TAC[];
      UNDISCH_TAC `~((g:real^3->real^3) moi_s32_qhi IN moi_s32_set g s2 fam)` THEN
      USE_THEN "xab" (fun th -> REWRITE_TAC[GSYM th]) THEN SET_TAC[];
      UNDISCH_TAC `~((g:real^3->real^3) moi_s32_qlo IN moi_s32_set g s2 fam)` THEN
      USE_THEN "xab" (fun th -> REWRITE_TAC[GSYM th]) THEN SET_TAC[];
      UNDISCH_TAC `~((g:real^3->real^3) moi_s32_qhi IN moi_s32_set g s2 fam)` THEN
      USE_THEN "xab" (fun th -> REWRITE_TAC[GSYM th]) THEN SET_TAC[]];
    ALL_TAC] THEN
  STRIP_TAC THENL
   [MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                   `dd:int->real^3->bool`; `s2:int->real^3->bool`; `&2 * i + &2:int`]
      MOI_S3ST_INNER_PATH) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `c0:real^3->bool` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`moi_s32_open g`;
                   `kin UNION UNIONS famA UNION {(g:real^3->real^3) (vec 0)}`;
                   `{(g:real^3->real^3) moi_s32_qlo}`; `{(g:real^3->real^3) moi_s32_qhi}`;
                   `c0:real^3->bool`] MOI_S3CL_SEP_CONN) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `DISJOINT (c0:real^3->bool) qi` THEN
    UNDISCH_TAC `(kin:real^3->bool) SUBSET qi` THEN
    UNDISCH_TAC `UNIONS famA SUBSET (qi:real^3->bool)` THEN
    UNDISCH_TAC `(c0:real^3->bool) SUBSET moi_s32_open g` THEN
    UNDISCH_TAC `~((g:real^3->real^3) (vec 0) IN c0)` THEN
    UNDISCH_TAC `(g:real^3->real^3) moi_s32_qlo IN c0` THEN
    UNDISCH_TAC `(g:real^3->real^3) moi_s32_qhi IN c0` THEN
    SET_TAC[];
    MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`] MOI_S3ST_AXIS_PATH) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`moi_s32_open g`; `(kout:real^3->bool) UNION UNIONS (famB:(real^3->bool)->bool)`;
                   `{(g:real^3->real^3) moi_s32_qlo}`; `{(g:real^3->real^3) moi_s32_qhi}`;
                   `IMAGE (g:real^3->real^3) (segment[moi_s32_qlo,moi_s32_qhi])`]
      MOI_S3CL_SEP_CONN) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `DISJOINT (IMAGE (g:real^3->real^3) (segment[moi_s32_qlo,moi_s32_qhi]))
                          (IMAGE g v)` THEN
    UNDISCH_TAC `kout SUBSET IMAGE (g:real^3->real^3) v` THEN
    UNDISCH_TAC `UNIONS famB SUBSET IMAGE (g:real^3->real^3) v` THEN
    UNDISCH_TAC `IMAGE (g:real^3->real^3) (segment[moi_s32_qlo,moi_s32_qhi]) SUBSET
                 moi_s32_open g` THEN
    UNDISCH_TAC `(g:real^3->real^3) moi_s32_qlo IN
                 IMAGE g (segment[moi_s32_qlo,moi_s32_qhi])` THEN
    UNDISCH_TAC `(g:real^3->real^3) moi_s32_qhi IN
                 IMAGE g (segment[moi_s32_qlo,moi_s32_qhi])` THEN
    SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Part 8: tools for the deletions of Steps 2-4.  LIMIT_PIECES: if the       *)
(* barrier x0 minus any finite set of pieces (each inside a level region,   *)
(* finitely many per level) is closed and separates, so does x0 minus all    *)
(* of them (MOI_S32_LIMIT along the levels).  GLUE2: gluing two surfaces     *)
(* along closed unions of boundary components.  ANN_IN_TORUS: two disjoint   *)
(* essential polygons of an even torus bound an annulus in it (28.6).  The  *)
(* closed surfaces Sigma for the members of Types 1-3 (SIGMA2, SIGMA3), and  *)
(* SD_MEMBER: deleting a member off K keeps the separation when it lies in  *)
(* a closed surface of the barrier.                                         *)
(* ------------------------------------------------------------------------- *)

let MOI_S3ST_LIMIT_PIECES = prove
 (mk_imp(moi_n3 MOI_S32_LIMIT,
  `!(g:real^3->real^3) v pp dd s2 (x0:real^3->bool) (idx:A->bool) (pc:A->real^3->bool)
     (lv:A->int).
     moi_s32_model g v /\ moi_s32_tower g v pp dd s2 /\
     (!a. a IN idx ==> pc a SUBSET moi_s32_lvl g dd (lv a)) /\
     (!i. FINITE {a | a IN idx /\ lv a = i}) /\
     g (vec 0) IN x0 /\ ~(g moi_s32_qlo IN x0) /\ ~(g moi_s32_qhi IN x0) /\
     closed_in (subtopology euclidean (moi_s32_open g)) (x0 DIFF UNIONS (IMAGE pc idx)) /\
     (!d. FINITE d /\ d SUBSET idx
          ==> closed_in (subtopology euclidean (moi_s32_open g))
                        (x0 DIFF UNIONS (IMAGE pc d)) /\
              separates_in (moi_s32_open g) (x0 DIFF UNIONS (IMAGE pc d))
                           {g moi_s32_qlo} {g moi_s32_qhi})
     ==> separates_in (moi_s32_open g) (x0 DIFF UNIONS (IMAGE pc idx))
                      {g moi_s32_qlo} {g moi_s32_qhi}`),
  DISCH_THEN(LABEL_TAC "lim") THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  X_CHOOSE_THEN `e:num->int` STRIP_ASSUME_TAC MOI_S3IT_INT_ENUM THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                 `dd:int->real^3->bool`; `s2:int->real^3->bool`] MOI_S3I2_TORI_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`] MOI_S3ST_GV_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`] MOI_S3ST_POINTS_NOT_V) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!a:A. a IN idx ==> ~((g:real^3->real^3) (vec 0) IN pc a)` ASSUME_TAC THENL
   [X_GEN_TAC `a:A` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(pc:A->real^3->bool) a SUBSET IMAGE (g:real^3->real^3) v` MP_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `moi_s32_lvl (g:real^3->real^3) dd ((lv:A->int) a)` THEN
      ASM_SIMP_TAC[] THEN MATCH_MP_TAC MOI_S3IT_LVL_IN_V THEN
      MAP_EVERY EXISTS_TAC [`pp:int->real^3`; `s2:int->real^3->bool`] THEN ASM_REWRITE_TAC[];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `dn = \n:num. {a:A | a IN idx /\ ?k. k < n /\ (lv:A->int) a = (e:num->int) k}` THEN
  SUBGOAL_THEN `!n. FINITE ((dn:num->A->bool) n) /\ dn n SUBSET idx` ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "dn" THEN CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `UNIONS (IMAGE (\k. {a:A | a IN idx /\ (lv:A->int) a = (e:num->int) k})
                                {k | k < n})` THEN
      CONJ_TAC THENL
       [REWRITE_TAC[FINITE_UNIONS; FORALL_IN_IMAGE] THEN
        ASM_SIMP_TAC[FINITE_IMAGE; FINITE_NUMSEG_LT];
        REWRITE_TAC[SUBSET; IN_UNIONS; EXISTS_IN_IMAGE; IN_ELIM_THM] THEN MESON_TAC[]];
      SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. closed_in (subtopology euclidean (moi_s32_open g))
                  (x0 DIFF UNIONS (IMAGE (pc:A->real^3->bool) ((dn:num->A->bool) n))) /\
        separates_in (moi_s32_open g) (x0 DIFF UNIONS (IMAGE pc (dn n)))
                     {(g:real^3->real^3) moi_s32_qlo} {g moi_s32_qhi}`
  ASSUME_TAC THENL
   [GEN_TAC THEN FIRST_ASSUM(MP_TAC o SPEC `(dn:num->A->bool) n`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `DISJOINT (x0 DIFF UNIONS (IMAGE (pc:A->real^3->bool) idx))
             ({(g:real^3->real^3) moi_s32_qlo} UNION {g moi_s32_qhi}) /\
    g (vec 0) IN x0 DIFF UNIONS (IMAGE pc idx) /\
    (!n. g (vec 0) IN x0 DIFF UNIONS (IMAGE pc ((dn:num->A->bool) n)))`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM SET_TAC[];
      REWRITE_TAC[IN_DIFF; IN_UNIONS; EXISTS_IN_IMAGE] THEN ASM_MESON_TAC[];
      GEN_TAC THEN REWRITE_TAC[IN_DIFF; IN_UNIONS; EXISTS_IN_IMAGE] THEN
      ASM_MESON_TAC[SUBSET]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN moi_s32_open g /\ ~(x = (g:real^3->real^3) (vec 0))
        ==> ?u n0. open u /\ x IN u /\
                   !n. n0 <= n
                       ==> (x0 DIFF UNIONS (IMAGE (pc:A->real^3->bool) ((dn:num->A->bool) n)))
                           INTER u =
                           (x0 DIFF UNIONS (IMAGE pc idx)) INTER u`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                   `dd:int->real^3->bool`; `s2:int->real^3->bool`; `x:real^3`]
      MOI_S3ST_LVL_LF) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `u:real^3->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN
     `FINITE {k:num | (e:num->int) k IN
                      {i:int | ~(moi_s32_lvl (g:real^3->real^3) dd i INTER u = {})}}`
    MP_TAC THENL
     [MATCH_MP_TAC FINITE_IMAGE_INJ THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[num_FINITE; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_TAC `nn:num`) THEN
    MAP_EVERY EXISTS_TAC [`u:real^3->bool`; `nn + 1`] THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `y:real^3` THEN
    REWRITE_TAC[IN_INTER; IN_DIFF; IN_UNIONS; EXISTS_IN_IMAGE] THEN EQ_TAC THENL
     [STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `a:A` STRIP_ASSUME_TAC) THEN
      UNDISCH_TAC `~(?x. x IN (dn:num->A->bool) n /\ (y:real^3) IN (pc:A->real^3->bool) x)` THEN
      REWRITE_TAC[] THEN EXISTS_TAC `a:A` THEN ASM_REWRITE_TAC[] THEN
      EXPAND_TAC "dn" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(X_CHOOSE_TAC `k:num` o SPEC `(lv:A->int) a` o check (fun th ->
        is_forall(concl th) && is_exists(snd(dest_forall(concl th))))) THEN
      EXISTS_TAC `k:num` THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `(k:num) <= nn` MP_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `!a:A. a IN idx ==> (pc:A->real^3->bool) a SUBSET
                                        moi_s32_lvl (g:real^3->real^3) dd ((lv:A->int) a)` THEN
        DISCH_THEN(MP_TAC o SPEC `a:A`) THEN ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `(y:real^3) IN u` THEN UNDISCH_TAC `(y:real^3) IN (pc:A->real^3->bool) a` THEN
        SET_TAC[];
        UNDISCH_TAC `nn + 1 <= n` THEN ARITH_TAC];
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[SUBSET]];
    ALL_TAC] THEN
  USE_THEN "lim" MATCH_MP_TAC THEN
  EXISTS_TAC `\n. x0 DIFF UNIONS (IMAGE (pc:A->real^3->bool) ((dn:num->A->bool) n))` THEN
  EXISTS_TAC `(g:real^3->real^3) (vec 0)` THEN REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[CONNECTED_SING; SING_SUBSET]);;

(* A component of k UNION kc (closed, disjoint) meeting k lies in k.       *)

let MOI_S3ST_COMP_IN = prove
 (`!(k:real^3->bool) kc b.
     closed k /\ closed kc /\ DISJOINT k kc /\ b IN components (k UNION kc) /\
     ~(b INTER k = {})
     ==> b SUBSET k`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP IN_COMPONENTS_CONNECTED) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP IN_COMPONENTS_SUBSET) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [CONNECTED_CLOSED]) THEN
  REWRITE_TAC[NOT_EXISTS_THM] THEN
  DISCH_THEN(MP_TAC o SPECL [`k:real^3->bool`; `kc:real^3->bool`]) THEN
  ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

let MOI_S3ST_GLUE2 = prove
 (`!(c:(real^3->bool)->bool) d k kc kd.
     FINITE c /\ combinatorial_manifold_with_boundary 2 c /\
     FINITE d /\ combinatorial_manifold_with_boundary 2 d /\
     surface_boundary c = k UNION kc /\ surface_boundary d = k UNION kd /\
     closed k /\ closed kc /\ closed kd /\ DISJOINT k kc /\ DISJOINT k kd /\
     UNIONS c INTER UNIONS d = k
     ==> ?e. FINITE e /\ combinatorial_manifold_with_boundary 2 e /\
             UNIONS e = UNIONS c UNION UNIONS d /\ surface_boundary e = kc UNION kd /\
             (kc = {} /\ kd = {} ==> combinatorial_manifold 2 e)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `d:(real^3->bool)->bool`; `k:real^3->bool`]
    MOI_S6G_SURF_GLUE_BODY) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[SUBSET_UNION] THEN CONJ_TAC THEN X_GEN_TAC `b:real^3->bool` THEN
    STRIP_TAC THEN MATCH_MP_TAC MOI_S3ST_COMP_IN THENL
     [EXISTS_TAC `kc:real^3->bool`; EXISTS_TAC `kd:real^3->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `e:(real^3->bool)->bool` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM SET_TAC[];
    STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[UNION_EMPTY]]);;

(* Two disjoint essential polygons of a PL torus bound an annulus in it.   *)

let MOI_S3ST_ANN_IN_TORUS = prove
 (`!(s2:int->real^3->bool) t j j1.
     MOISE_286_STATEMENT /\ pl_solid_torus (s2 t) /\
     moi_s32_ess s2 t j /\ moi_s32_ess s2 t j1 /\ DISJOINT j j1
     ==> ?a d. pl_annulus_with_ends a j j1 /\ a SUBSET frontier (s2 t) /\ compact a /\
               connected a /\ FINITE d /\ combinatorial_manifold_with_boundary 2 d /\
               UNIONS d = a /\ surface_boundary d = j UNION j1`,
  REWRITE_TAC[moi_s32_ess] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`(s2:int->real^3->bool) t`; `j:real^3->bool`; `j1:real^3->bool`]
    MOI_S3ST_TORUS_PIECES) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (CONJUNCTS_THEN2 (K ALL_TAC) (LABEL_TAC "pc"))) THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN DISCH_THEN(X_CHOOSE_TAC `y:real^3`) THEN
  ABBREV_TAC `w = connected_component (frontier ((s2:int->real^3->bool) t) DIFF
                                       (j UNION j1)) y` THEN
  REMOVE_THEN "pc" (MP_TAC o SPEC `w:real^3->bool`) THEN
  EXPAND_TAC "w" THEN ASM_REWRITE_TAC[CONNECTED_COMPONENT_IN_COMPONENTS] THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`closure w:real^3->bool`; `j:real^3->bool`; `j1:real^3->bool`]
    ANNULUS_COMPLEX) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `d:(real^3->bool)->bool` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`closure w:real^3->bool`; `d:(real^3->bool)->bool`] THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[MOI_S3ST_ANN_ENDS]);;

(* A triangulated surface without boundary is a combinatorial manifold.     *)

let MOI_S3ST_TYPE1_CM = prove
 (`!cc:(real^3->bool)->bool.
     FINITE cc /\ combinatorial_manifold_with_boundary 2 cc /\ surface_boundary cc = {}
     ==> combinatorial_manifold 2 cc`,
  REPEAT STRIP_TAC THEN MP_TAC(ISPEC `cc:(real^3->bool)->bool` SURF_LOCAL) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[MOI_S8TA_CMB_FACTS] THEN
    MP_TAC(ISPEC `cc:(real^3->bool)->bool` SURF_CHARTS) THEN
    ASM_REWRITE_TAC[DIFF_EMPTY; NOT_IN_EMPTY] THEN MESON_TAC[];
    ASM_SIMP_TAC[]]);;

let MOI_S3ST_EVENS_IN_V = prove
 (`!(g:real^3->real^3) v pp dd s2.
     moi_s32_model g v /\ moi_s32_tower g v pp dd s2
     ==> moi_s32_evens s2 SUBSET IMAGE g v /\
         (!i. frontier (s2 (&2 * i)) SUBSET moi_s32_evens s2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                 `dd:int->real^3->bool`; `s2:int->real^3->bool`] MOI_S3ST_TORUS_BASICS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN CONJ_TAC THENL
   [REWRITE_TAC[moi_s32_evens; UNIONS_SUBSET; FORALL_IN_GSPEC] THEN ASM_REWRITE_TAC[];
    GEN_TAC THEN REWRITE_TAC[moi_s32_evens] THEN
    MATCH_MP_TAC(SET_RULE `(x:real^3->bool) IN f ==> x SUBSET UNIONS f`) THEN
    REWRITE_TAC[IN_ELIM_THM; IN_UNIV] THEN MESON_TAC[]]);;

(* Type 2: the annulus c with both ends on one even torus, glued to an      *)
(* annulus of the torus between its ends, is a closed surface.              *)

let MOI_S3ST_SIGMA2 = prove
 (`!(s2:int->real^3->bool) kk cc c j j' t.
     MOISE_286_STATEMENT /\ pl_solid_torus (s2 t) /\ frontier (s2 t) SUBSET kk /\
     FINITE cc /\ combinatorial_manifold_with_boundary 2 cc /\ UNIONS cc = c /\
     surface_boundary cc = c INTER kk /\
     pl_annulus_with_ends c j j' /\ c INTER kk = j UNION j' /\
     moi_s32_ess s2 t j /\ moi_s32_ess s2 t j'
     ==> ?e a. FINITE e /\ combinatorial_manifold 2 e /\ connected (UNIONS e) /\
               UNIONS e = c UNION a /\ closed a /\ a SUBSET kk`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:real^3->bool`; `j:real^3->bool`; `j':real^3->bool`] MOI_S3ST_ANN_ENDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:real^3->bool`; `j:real^3->bool`; `j':real^3->bool`] ANNULUS_COMPLEX) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d0:(real^3->bool)->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`s2:int->real^3->bool`; `t:int`; `j:real^3->bool`; `j':real^3->bool`]
    MOI_S3ST_ANN_IN_TORUS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^3->bool` (X_CHOOSE_THEN `d:(real^3->bool)->bool`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`a:real^3->bool`; `j:real^3->bool`; `j':real^3->bool`] MOI_S3ST_ANN_ENDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`cc:(real^3->bool)->bool`; `d:(real^3->bool)->bool`;
                 `j UNION j':real^3->bool`; `{}:real^3->bool`; `{}:real^3->bool`]
    MOI_S3ST_GLUE2) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[UNION_EMPTY; CLOSED_EMPTY; DISJOINT_EMPTY] THEN
    ASM_SIMP_TAC[CLOSED_UNION; COMPACT_IMP_CLOSED] THEN
    UNDISCH_TAC `(a:real^3->bool) SUBSET frontier ((s2:int->real^3->bool) t)` THEN
    UNDISCH_TAC `frontier ((s2:int->real^3->bool) t) SUBSET kk` THEN
    UNDISCH_TAC `(c:real^3->bool) INTER kk = j UNION j'` THEN
    UNDISCH_TAC `(j:real^3->bool) SUBSET c` THEN UNDISCH_TAC `(j':real^3->bool) SUBSET c` THEN
    UNDISCH_TAC `(j:real^3->bool) SUBSET a` THEN UNDISCH_TAC `(j':real^3->bool) SUBSET a` THEN
    SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:(real^3->bool)->bool` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`e:(real^3->bool)->bool`; `a:real^3->bool`] THEN
  ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONNECTED_UNION THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ASM SET_TAC[]]);;

(* Type 3 (not the chosen bridge b of its level): c, an annulus of T_t      *)
(* from j to the low end jh of b, b, and an annulus of T_(t+2) from the     *)
(* high end jl of b to j' form a closed surface.                            *)

let MOI_S3ST_SIGMA3 = prove
 (`!(s2:int->real^3->bool) kk cc c j j' cb b jh jl t.
     MOISE_286_STATEMENT /\ pl_solid_torus (s2 t) /\ pl_solid_torus (s2 (t + &2)) /\
     frontier (s2 t) SUBSET kk /\ frontier (s2 (t + &2)) SUBSET kk /\
     DISJOINT (frontier (s2 t)) (frontier (s2 (t + &2))) /\
     FINITE cc /\ combinatorial_manifold_with_boundary 2 cc /\ UNIONS cc = c /\
     surface_boundary cc = c INTER kk /\
     pl_annulus_with_ends c j j' /\ c INTER kk = j UNION j' /\
     moi_s32_ess s2 t j /\ moi_s32_ess s2 (t + &2) j' /\
     FINITE cb /\ combinatorial_manifold_with_boundary 2 cb /\ UNIONS cb = b /\
     surface_boundary cb = b INTER kk /\
     pl_annulus_with_ends b jh jl /\ b INTER kk = jh UNION jl /\
     moi_s32_ess s2 t jh /\ moi_s32_ess s2 (t + &2) jl /\ DISJOINT c b
     ==> ?e a. FINITE e /\ combinatorial_manifold 2 e /\ connected (UNIONS e) /\
               UNIONS e = c UNION a /\ closed a /\ a SUBSET kk UNION b`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:real^3->bool`; `j:real^3->bool`; `j':real^3->bool`] MOI_S3ST_ANN_ENDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`b:real^3->bool`; `jh:real^3->bool`; `jl:real^3->bool`] MOI_S3ST_ANN_ENDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:real^3->bool`; `j:real^3->bool`; `j':real^3->bool`] ANNULUS_COMPLEX) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d0:(real^3->bool)->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`b:real^3->bool`; `jh:real^3->bool`; `jl:real^3->bool`] ANNULUS_COMPLEX) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:(real^3->bool)->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(j:real^3->bool) SUBSET frontier ((s2:int->real^3->bool) t) /\
                (j':real^3->bool) SUBSET frontier (s2 (t + &2)) /\
                (jh:real^3->bool) SUBSET frontier (s2 t) /\
                (jl:real^3->bool) SUBSET frontier (s2 (t + &2))` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[moi_s32_ess]; ALL_TAC] THEN
  SUBGOAL_THEN `DISJOINT (j:real^3->bool) jh /\ DISJOINT (jl:real^3->bool) j' /\
                DISJOINT (jh:real^3->bool) j'` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`s2:int->real^3->bool`; `t:int`; `j:real^3->bool`; `jh:real^3->bool`]
    MOI_S3ST_ANN_IN_TORUS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `a1:real^3->bool` (X_CHOOSE_THEN `e1:(real^3->bool)->bool`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`s2:int->real^3->bool`; `t + &2:int`; `jl:real^3->bool`; `j':real^3->bool`]
    MOI_S3ST_ANN_IN_TORUS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `a2:real^3->bool` (X_CHOOSE_THEN `e2:(real^3->bool)->bool`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`a1:real^3->bool`; `j:real^3->bool`; `jh:real^3->bool`] MOI_S3ST_ANN_ENDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`a2:real^3->bool`; `jl:real^3->bool`; `j':real^3->bool`] MOI_S3ST_ANN_ENDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`cc:(real^3->bool)->bool`; `e1:(real^3->bool)->bool`; `j:real^3->bool`;
                 `j':real^3->bool`; `jh:real^3->bool`] MOI_S3ST_GLUE2) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN
    UNDISCH_TAC `(a1:real^3->bool) SUBSET frontier ((s2:int->real^3->bool) t)` THEN
    UNDISCH_TAC `(c:real^3->bool) INTER kk = j UNION j'` THEN
    UNDISCH_TAC `frontier ((s2:int->real^3->bool) t) SUBSET kk` THEN
    UNDISCH_TAC `DISJOINT (frontier ((s2:int->real^3->bool) t)) (frontier (s2 (t + &2)))` THEN
    UNDISCH_TAC `(j':real^3->bool) SUBSET frontier ((s2:int->real^3->bool) (t + &2))` THEN
    UNDISCH_TAC `(j:real^3->bool) SUBSET c` THEN UNDISCH_TAC `(j:real^3->bool) SUBSET a1` THEN
    SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `f1:(real^3->bool)->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`f1:(real^3->bool)->bool`; `cb:(real^3->bool)->bool`; `jh:real^3->bool`;
                 `j':real^3->bool`; `jl:real^3->bool`] MOI_S3ST_GLUE2) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN REPEAT CONJ_TAC THENL
     [SET_TAC[];
      UNDISCH_TAC `(a1:real^3->bool) SUBSET frontier ((s2:int->real^3->bool) t)` THEN
      UNDISCH_TAC `(b:real^3->bool) INTER kk = jh UNION jl` THEN
      UNDISCH_TAC `frontier ((s2:int->real^3->bool) t) SUBSET kk` THEN
      UNDISCH_TAC `DISJOINT (frontier ((s2:int->real^3->bool) t)) (frontier (s2 (t + &2)))` THEN
      UNDISCH_TAC `(jl:real^3->bool) SUBSET frontier ((s2:int->real^3->bool) (t + &2))` THEN
      UNDISCH_TAC `DISJOINT (c:real^3->bool) b` THEN
      UNDISCH_TAC `(jh:real^3->bool) SUBSET b` THEN UNDISCH_TAC `(jh:real^3->bool) SUBSET a1` THEN
      SET_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `f2:(real^3->bool)->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`f2:(real^3->bool)->bool`; `e2:(real^3->bool)->bool`; `j' UNION jl:real^3->bool`;
                 `{}:real^3->bool`; `{}:real^3->bool`] MOI_S3ST_GLUE2) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[UNION_EMPTY; CLOSED_EMPTY; DISJOINT_EMPTY] THEN
    ASM_SIMP_TAC[CLOSED_UNION; COMPACT_IMP_CLOSED] THEN CONJ_TAC THENL
     [SET_TAC[];
      UNDISCH_TAC `(a2:real^3->bool) SUBSET frontier ((s2:int->real^3->bool) (t + &2))` THEN
      UNDISCH_TAC `(a1:real^3->bool) SUBSET frontier ((s2:int->real^3->bool) t)` THEN
      UNDISCH_TAC `(c:real^3->bool) INTER kk = j UNION j'` THEN
      UNDISCH_TAC `(b:real^3->bool) INTER kk = jh UNION jl` THEN
      UNDISCH_TAC `frontier ((s2:int->real^3->bool) (t + &2)) SUBSET kk` THEN
      UNDISCH_TAC `DISJOINT (frontier ((s2:int->real^3->bool) t)) (frontier (s2 (t + &2)))` THEN
      UNDISCH_TAC `(j:real^3->bool) SUBSET frontier ((s2:int->real^3->bool) t)` THEN
      UNDISCH_TAC `(jh:real^3->bool) SUBSET frontier ((s2:int->real^3->bool) t)` THEN
      UNDISCH_TAC `(j':real^3->bool) SUBSET c` THEN UNDISCH_TAC `(j':real^3->bool) SUBSET a2` THEN
      UNDISCH_TAC `(jl:real^3->bool) SUBSET b` THEN UNDISCH_TAC `(jl:real^3->bool) SUBSET a2` THEN
      SET_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:(real^3->bool)->bool` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`e:(real^3->bool)->bool`; `a1 UNION b UNION a2:real^3->bool`] THEN
  ASM_SIMP_TAC[CLOSED_UNION; COMPACT_IMP_CLOSED] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONNECTED_UNION THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONNECTED_UNION THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONNECTED_UNION THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
        ASM_REWRITE_TAC[] THEN ASM SET_TAC[]];
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[]];
    SET_TAC[];
    ASM SET_TAC[]]);;

let MOI_S3ST_QPTS = prove
 (`vec 0 IN moi_s32_cyl /\ moi_s32_qlo IN moi_s32_cyl /\ moi_s32_qhi IN moi_s32_cyl /\
   vec 0 IN moi_s32_axis /\ moi_s32_qlo IN moi_s32_axis /\ moi_s32_qhi IN moi_s32_axis`,
  MP_TAC MOI_S3GF_MODEL_POINTS THEN MP_TAC MOI_S3GF_CYL_PARTS THEN SET_TAC[]);;

(* Deleting a member c off K: c and a closed set a in the rest of the      *)
(* barrier form a closed surface (Sigma), so SD applies.                   *)

let MOI_S3ST_SD_MEMBER = prove
 (`!(g:real^3->real^3) v pp dd s2 lev fam ff c e a.
     moi_s32_model g v /\ moi_s32_tower g v pp dd s2 /\ moi_s32_state g dd s2 lev fam /\
     ff SUBSET fam /\ c IN ff /\
     separates_in (moi_s32_open g) (moi_s32_set g s2 ff) {g moi_s32_qlo} {g moi_s32_qhi} /\
     FINITE e /\ combinatorial_manifold 2 e /\ connected (UNIONS e) /\
     UNIONS e = c UNION a /\ closed a /\
     a SUBSET moi_s32_evens s2 UNION UNIONS (ff DELETE c)
     ==> separates_in (moi_s32_open g) (moi_s32_set g s2 (ff DELETE c))
                      {g moi_s32_qlo} {g moi_s32_qhi}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(c:real^3->bool) IN fam` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                 `dd:int->real^3->bool`; `s2:int->real^3->bool`; `lev:int->bool`;
                 `fam:(real^3->bool)->bool`; `c:real^3->bool`] MOI_S3ST_MEMBER) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`] MOI_S3ST_GV_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                 `dd:int->real^3->bool`; `s2:int->real^3->bool`] MOI_S3ST_EVENS_IN_V) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `pairwise DISJOINT (fam:(real^3->bool)->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `moi_s32_state g dd s2 lev fam` THEN SIMP_TAC[moi_s32_state]; ALL_TAC] THEN
  SUBGOAL_THEN `!c':real^3->bool. c' IN ff DELETE c ==> DISJOINT c c' /\ c' SUBSET IMAGE (g:real^3->real^3) v`
  ASSUME_TAC THENL
   [REWRITE_TAC[IN_DELETE] THEN X_GEN_TAC `c':real^3->bool` THEN STRIP_TAC THEN CONJ_TAC THENL
     [UNDISCH_TAC `pairwise DISJOINT (fam:(real^3->bool)->bool)` THEN
      REWRITE_TAC[pairwise] THEN DISCH_THEN MATCH_MP_TAC THEN ASM SET_TAC[];
      MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                     `dd:int->real^3->bool`; `s2:int->real^3->bool`; `lev:int->bool`;
                     `fam:(real^3->bool)->bool`; `c':real^3->bool`] MOI_S3ST_MEMBER) THEN
      ANTS_TAC THENL [ASM SET_TAC[]; SIMP_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `UNIONS cc DIFF surface_boundary cc = (c:real^3->bool) DIFF moi_s32_evens s2`
  ASSUME_TAC THENL [ASM_REWRITE_TAC[] THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `moi_s32_set g s2 ff DIFF ((c:real^3->bool) DIFF moi_s32_evens s2) =
                moi_s32_set g s2 (ff DELETE c)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`g:real^3->real^3`; `s2:int->real^3->bool`; `ff:(real^3->bool)->bool`;
                   `{c:real^3->bool}`] MOI_S3ST_DEL_EQ) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL [ASM_MESON_TAC[PAIRWISE_MONO]; ALL_TAC] THEN
      CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      X_GEN_TAC `c':real^3->bool` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                     `dd:int->real^3->bool`; `s2:int->real^3->bool`; `lev:int->bool`;
                     `fam:(real^3->bool)->bool`; `c':real^3->bool`] MOI_S3ST_MEMBER) THEN
      ANTS_TAC THENL [ASM SET_TAC[]; SIMP_TAC[]];
      REWRITE_TAC[IMAGE_CLAUSES; UNIONS_1] THEN BETA_TAC THEN DISCH_THEN SUBST1_TAC THEN
      AP_TERM_TAC THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `closed_in (subtopology euclidean (moi_s32_open g)) (moi_s32_set g s2 ff) /\
                closed_in (subtopology euclidean (moi_s32_open g))
                          (moi_s32_set g s2 (ff DELETE c))` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC MOI_S3ST_SUBFAM_CLOSED THEN
    MAP_EVERY EXISTS_TAC [`v:real^3->bool`; `pp:int->real^3`; `dd:int->real^3->bool`;
                          `lev:int->bool`; `fam:(real^3->bool)->bool`] THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(c:real^3->bool) UNION a SUBSET moi_s32_set g s2 ff` ASSUME_TAC THENL
   [REWRITE_TAC[moi_s32_set] THEN
    UNDISCH_TAC `(a:real^3->bool) SUBSET moi_s32_evens s2 UNION UNIONS (ff DELETE c)` THEN
    UNDISCH_TAC `(c:real^3->bool) IN ff` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `closed (((c:real^3->bool) UNION a) DIFF (c DIFF moi_s32_evens s2))`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `((c:real^3->bool) UNION a) DIFF (c DIFF moi_s32_evens s2) =
                  (c INTER moi_s32_evens s2) UNION a` SUBST1_TAC THENL
     [UNDISCH_TAC `(a:real^3->bool) SUBSET moi_s32_evens s2 UNION UNIONS (ff DELETE c)` THEN
      UNDISCH_TAC `!c':real^3->bool. c' IN ff DELETE c ==> DISJOINT c c' /\ c' SUBSET IMAGE (g:real^3->real^3) v` THEN
      SET_TAC[];
      MATCH_MP_TAC CLOSED_UNION THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        concl th = `surface_boundary cc = (c:real^3->bool) INTER moi_s32_evens s2`)) THEN
      MP_TAC(ISPEC `cc:(real^3->bool)->bool` MOI_S6G_CM_CLOSED) THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(g:real^3->real^3) moi_s32_qlo IN outside (c UNION a) /\
                g moi_s32_qhi IN outside (c UNION a)` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `(c:real^3->bool) UNION a SUBSET IMAGE (g:real^3->real^3) v` ASSUME_TAC THENL
     [MATCH_MP_TAC(SET_RULE
       `!k u w c a:real^3->bool.
          c SUBSET w /\ k SUBSET w /\ a SUBSET k UNION u /\ u SUBSET w
          ==> c UNION a SUBSET w`) THEN
      MAP_EVERY EXISTS_TAC [`moi_s32_evens s2`; `UNIONS (ff DELETE (c:real^3->bool))`] THEN
      ASM_REWRITE_TAC[UNIONS_SUBSET] THEN ASM_SIMP_TAC[];
      CONJ_TAC THEN MATCH_MP_TAC MOI_S3ST_OUTSIDE THEN EXISTS_TAC `v:real^3->bool` THEN
      ASM_REWRITE_TAC[MOI_S3ST_QPTS]];
    ALL_TAC] THEN
  SUBGOAL_THEN `separates_in (moi_s32_open g)
                 (moi_s32_set g s2 ff DIFF (UNIONS cc DIFF surface_boundary cc))
                 {(g:real^3->real^3) moi_s32_qlo} {g moi_s32_qhi}` MP_TAC THENL
   [MATCH_MP_TAC MOI_S3ST_SD THEN EXISTS_TAC `e:(real^3->bool)->bool` THEN
    ASM_REWRITE_TAC[SUBSET_UNION];
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Part 9 (Phase 1): with one bridge bb i chosen in every level (Part 7),    *)
(* every other member is deleted off K: Type 1 against itself, Type 2       *)
(* against an annulus of its torus (SIGMA2), Type 3 against two annuli and   *)
(* the bridge of its level (SIGMA3); finitely many by induction, then all   *)
(* by LIMIT_PIECES.  The barrier K + the bridges + P' still separates.      *)
(* ------------------------------------------------------------------------- *)

let MOI_S3ST_PHASE1_STEP = prove
 (`!(g:real^3->real^3) v pp dd s2 fam bb ja jb ff c.
     MOISE_286_STATEMENT /\ moi_s32_model g v /\ moi_s32_tower g v pp dd s2 /\
     moi_s32_reduced g dd s2 fam /\
     (!i. bb i IN fam /\ bb i SUBSET moi_s32_lvl g dd i /\
          pl_annulus_with_ends (bb i) (ja i) (jb i) /\
          bb i INTER moi_s32_evens s2 = ja i UNION jb i /\
          moi_s32_ess s2 (&2 * i) (ja i) /\ moi_s32_ess s2 (&2 * i + &2) (jb i)) /\
     IMAGE bb (:int) SUBSET ff /\ ff SUBSET fam /\ c IN ff /\ ~(c IN IMAGE bb (:int)) /\
     separates_in (moi_s32_open g) (moi_s32_set g s2 ff) {g moi_s32_qlo} {g moi_s32_qhi}
     ==> separates_in (moi_s32_open g) (moi_s32_set g s2 (ff DELETE c))
                      {g moi_s32_qlo} {g moi_s32_qhi}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `moi_s32_state g dd s2 (:int) fam` ASSUME_TAC THENL
   [UNDISCH_TAC `moi_s32_reduced g dd s2 fam` THEN SIMP_TAC[moi_s32_reduced]; ALL_TAC] THEN
  SUBGOAL_THEN `pairwise DISJOINT (fam:(real^3->bool)->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `moi_s32_state g dd s2 (:int) fam` THEN SIMP_TAC[moi_s32_state]; ALL_TAC] THEN
  SUBGOAL_THEN `(c:real^3->bool) IN fam` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                 `dd:int->real^3->bool`; `s2:int->real^3->bool`; `(:int)`;
                 `fam:(real^3->bool)->bool`; `c:real^3->bool`] MOI_S3ST_MEMBER) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                 `dd:int->real^3->bool`; `s2:int->real^3->bool`] MOI_S3ST_EVENS_IN_V) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                 `dd:int->real^3->bool`; `s2:int->real^3->bool`] MOI_S3ST_TORUS_BASICS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  UNDISCH_TAC `moi_s32_reduced g dd s2 fam` THEN REWRITE_TAC[moi_s32_reduced] THEN
  DISCH_THEN(MP_TAC o SPEC `c:real^3->bool` o CONJUNCT2) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:int` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ty"))) THEN
  MATCH_MP_TAC MOI_S3ST_SD_MEMBER THEN
  MAP_EVERY EXISTS_TAC [`v:real^3->bool`; `pp:int->real^3`; `dd:int->real^3->bool`;
                        `(:int)`; `fam:(real^3->bool)->bool`] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `frontier ((s2:int->real^3->bool) (&2 * k + &2)) SUBSET moi_s32_evens s2 /\
                DISJOINT (frontier (s2 (&2 * k))) (frontier (s2 (&2 * k + &2)))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `k + &1:int` o check (fun th ->
        is_forall(concl th) &&
        can (find_term (fun t -> t = `moi_s32_evens s2`)) (concl th) &&
        not (is_imp(snd(dest_forall(concl th)))))) THEN
      REWRITE_TAC[INT_ARITH `&2 * (k + &1):int = &2 * k + &2`];
      MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                     `dd:int->real^3->bool`; `s2:int->real^3->bool`; `k:int`; `k + &1:int`]
        MOI_S3ST_TORI_DISJ) THEN
      ASM_REWRITE_TAC[INT_ARITH `&2 * (k + &1):int = &2 * k + &2`] THEN
      DISCH_THEN MATCH_MP_TAC THEN INT_ARITH_TAC];
    ALL_TAC] THEN
  REMOVE_THEN "ty" (DISJ_CASES_THEN2 ASSUME_TAC MP_TAC) THENL
   [MAP_EVERY EXISTS_TAC [`cc:(real^3->bool)->bool`; `{}:real^3->bool`] THEN
    ASM_REWRITE_TAC[UNION_EMPTY; CLOSED_EMPTY; EMPTY_SUBSET] THEN
    MATCH_MP_TAC MOI_S3ST_TYPE1_CM THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `DISJOINT (c:real^3->bool) (moi_s32_evens s2)` THEN SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `j:real^3->bool` (X_CHOOSE_THEN `j':real^3->bool`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC))))) THEN
  SUBGOAL_THEN `DISJOINT (c:real^3->bool) (bb (k:int)) /\ bb k IN ff DELETE c`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `~((c:real^3->bool) = bb (k:int))` ASSUME_TAC THENL
     [UNDISCH_TAC `~((c:real^3->bool) IN IMAGE bb (:int))` THEN
      REWRITE_TAC[IN_IMAGE; IN_UNIV] THEN MESON_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `pairwise DISJOINT (fam:(real^3->bool)->bool)` THEN
      REWRITE_TAC[pairwise] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[IN_DELETE] THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `IMAGE (bb:int->real^3->bool) (:int) SUBSET ff` THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_UNIV] THEN SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                 `dd:int->real^3->bool`; `s2:int->real^3->bool`; `(:int)`;
                 `fam:(real^3->bool)->bool`; `(bb:int->real^3->bool) k`] MOI_S3ST_MEMBER) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `cb:(real^3->bool)->bool` STRIP_ASSUME_TAC o last o CONJUNCTS) THEN
  SUBGOAL_THEN
   `(moi_s32_ess s2 (&2 * k) j /\ moi_s32_ess s2 (&2 * k) j') \/
    (moi_s32_ess s2 (&2 * k + &2) j /\ moi_s32_ess s2 (&2 * k + &2) j') \/
    (moi_s32_ess s2 (&2 * k) j /\ moi_s32_ess s2 (&2 * k + &2) j') \/
    (moi_s32_ess s2 (&2 * k + &2) j /\ moi_s32_ess s2 (&2 * k) j')` MP_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  STRIP_TAC THENL
   [MP_TAC(ISPECL [`s2:int->real^3->bool`; `moi_s32_evens s2`; `cc:(real^3->bool)->bool`;
                   `c:real^3->bool`; `j:real^3->bool`; `j':real^3->bool`; `&2 * k:int`]
      MOI_S3ST_SIGMA2) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `e:(real^3->bool)->bool` THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `a:real^3->bool` THEN SIMP_TAC[] THEN SET_TAC[];
    MP_TAC(ISPECL [`s2:int->real^3->bool`; `moi_s32_evens s2`; `cc:(real^3->bool)->bool`;
                   `c:real^3->bool`; `j:real^3->bool`; `j':real^3->bool`; `&2 * k + &2:int`]
      MOI_S3ST_SIGMA2) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `e:(real^3->bool)->bool` THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `a:real^3->bool` THEN SIMP_TAC[] THEN SET_TAC[];
    MP_TAC(ISPECL [`s2:int->real^3->bool`; `moi_s32_evens s2`; `cc:(real^3->bool)->bool`;
                   `c:real^3->bool`; `j:real^3->bool`; `j':real^3->bool`;
                   `cb:(real^3->bool)->bool`; `(bb:int->real^3->bool) k`;
                   `(ja:int->real^3->bool) k`; `(jb:int->real^3->bool) k`; `&2 * k:int`]
      MOI_S3ST_SIGMA3) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `e:(real^3->bool)->bool` THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `a:real^3->bool` THEN SIMP_TAC[] THEN
    UNDISCH_TAC `(bb:int->real^3->bool) k IN ff DELETE c` THEN SET_TAC[];
    MP_TAC(ISPECL [`s2:int->real^3->bool`; `moi_s32_evens s2`; `cc:(real^3->bool)->bool`;
                   `c:real^3->bool`; `j':real^3->bool`; `j:real^3->bool`;
                   `cb:(real^3->bool)->bool`; `(bb:int->real^3->bool) k`;
                   `(ja:int->real^3->bool) k`; `(jb:int->real^3->bool) k`; `&2 * k:int`]
      MOI_S3ST_SIGMA3) THEN
    ASM_SIMP_TAC[MOI_S3ST_ANN_SYM] THEN
    ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `e:(real^3->bool)->bool` THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `a:real^3->bool` THEN SIMP_TAC[] THEN
    UNDISCH_TAC `(bb:int->real^3->bool) k IN ff DELETE c` THEN SET_TAC[]]);;

let MOI_S3ST_PHASE1 = prove
 (mk_imp(moi_n3 MOI_S32_LIMIT,
  `!(g:real^3->real^3) v pp dd s2 fam bb ja jb.
     MOISE_286_STATEMENT /\ moi_s32_model g v /\ moi_s32_tower g v pp dd s2 /\
     moi_s32_reduced g dd s2 fam /\
     (!i. bb i IN fam /\ bb i SUBSET moi_s32_lvl g dd i /\
          pl_annulus_with_ends (bb i) (ja i) (jb i) /\
          bb i INTER moi_s32_evens s2 = ja i UNION jb i /\
          moi_s32_ess s2 (&2 * i) (ja i) /\ moi_s32_ess s2 (&2 * i + &2) (jb i))
     ==> separates_in (moi_s32_open g) (moi_s32_set g s2 (IMAGE bb (:int)))
                      {g moi_s32_qlo} {g moi_s32_qhi}`),
  DISCH_THEN(LABEL_TAC "lim") THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `moi_s32_state g dd s2 (:int) fam` ASSUME_TAC THENL
   [UNDISCH_TAC `moi_s32_reduced g dd s2 fam` THEN SIMP_TAC[moi_s32_reduced]; ALL_TAC] THEN
  SUBGOAL_THEN `pairwise DISJOINT (fam:(real^3->bool)->bool) /\
                (!i. FINITE {c | c IN fam /\ c SUBSET moi_s32_lvl g dd i}) /\
                separates_in (moi_s32_open g) (moi_s32_set g s2 fam)
                             {(g:real^3->real^3) moi_s32_qlo} {g moi_s32_qhi}`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `moi_s32_state g dd s2 (:int) fam` THEN SIMP_TAC[moi_s32_state]; ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (bb:int->real^3->bool) (:int) SUBSET fam` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_UNIV] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!c. c IN fam ==> ~((g:real^3->real^3) (vec 0) IN c)` ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                   `dd:int->real^3->bool`; `s2:int->real^3->bool`; `(:int)`;
                   `fam:(real^3->bool)->bool`; `c:real^3->bool`] MOI_S3ST_MEMBER) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!d. d SUBSET fam
                    ==> moi_s32_set g s2 fam DIFF
                        UNIONS (IMAGE (\c. c DIFF moi_s32_evens s2) d) =
                        moi_s32_set (g:real^3->real^3) s2 (fam DIFF d)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_S3ST_DEL_EQ THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `moi_s32_set g s2 (IMAGE bb (:int)) =
                moi_s32_set g s2 fam DIFF
                UNIONS (IMAGE (\c. c DIFF moi_s32_evens s2)
                              (fam DIFF IMAGE (bb:int->real^3->bool) (:int)))`
  SUBST1_TAC THENL
   [FIRST_X_ASSUM(fun th -> W(fun (_,w) ->
      MP_TAC(SPEC `fam DIFF IMAGE (bb:int->real^3->bool) (:int)` th))) THEN
    REWRITE_TAC[SUBSET_DIFF] THEN DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN
    UNDISCH_TAC `IMAGE (bb:int->real^3->bool) (:int) SUBSET fam` THEN SET_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(X_CHOOSE_TAC `lf:(real^3->bool)->int` o MATCH_MP MOI_S3ST_STATE_LF) THEN
  USE_THEN "lim" (MATCH_MP_TAC o
    MATCH_MP (INST_TYPE [`:real^3->bool`,`:A`] MOI_S3ST_LIMIT_PIECES)) THEN
  MAP_EVERY EXISTS_TAC [`v:real^3->bool`; `pp:int->real^3`; `dd:int->real^3->bool`;
                        `s2:int->real^3->bool`; `lf:(real^3->bool)->int`] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`] MOI_S3ST_GV_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~((g:real^3->real^3) moi_s32_qlo IN moi_s32_set g s2 fam) /\
                ~(g moi_s32_qhi IN moi_s32_set g s2 fam)` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`moi_s32_open g`; `moi_s32_set g s2 fam`;
                   `(g:real^3->real^3) moi_s32_qlo`; `(g:real^3->real^3) moi_s32_qhi`]
      MOI_S3ST_SEP_OPEN) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SET_TAC[]];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[IN_DIFF] THEN X_GEN_TAC `c:real^3->bool` THEN STRIP_TAC THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `c:real^3->bool` THEN
    REWRITE_TAC[SUBSET_DIFF] THEN ASM_SIMP_TAC[];
    GEN_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{c | c IN fam /\ c SUBSET moi_s32_lvl (g:real^3->real^3) dd i}` THEN
    ASM_REWRITE_TAC[] THEN GEN_REWRITE_TAC I [SUBSET] THEN REWRITE_TAC[IN_ELIM_THM; IN_DIFF] THEN
    X_GEN_TAC `c:real^3->bool` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN ASM_SIMP_TAC[];
    REWRITE_TAC[moi_s32_set; IN_UNION; IN_SING];
    FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                   `dd:int->real^3->bool`; `s2:int->real^3->bool`; `(:int)`;
                   `fam:(real^3->bool)->bool`; `IMAGE (bb:int->real^3->bool) (:int)`]
      MOI_S3ST_SUBFAM_CLOSED) THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `fam DIFF IMAGE (bb:int->real^3->bool) (:int)` o check (fun th ->
      is_forall(concl th) && can (find_term (fun t -> t = `moi_s32_set g s2 fam`)) (concl th))) THEN
    REWRITE_TAC[SUBSET_DIFF] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    UNDISCH_TAC `IMAGE (bb:int->real^3->bool) (:int) SUBSET fam` THEN SET_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `d:(real^3->bool)->bool` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(d:(real^3->bool)->bool) SUBSET fam` ASSUME_TAC THENL
   [UNDISCH_TAC `(d:(real^3->bool)->bool) SUBSET fam DIFF IMAGE bb (:int)` THEN SET_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `d:(real^3->bool)->bool` o check (fun th ->
    is_forall(concl th) && can (find_term (fun t -> t = `moi_s32_set g s2 fam`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC MOI_S3ST_SUBFAM_CLOSED THEN
    MAP_EVERY EXISTS_TAC [`v:real^3->bool`; `pp:int->real^3`; `dd:int->real^3->bool`;
                          `(:int)`; `fam:(real^3->bool)->bool`] THEN
    ASM_REWRITE_TAC[SUBSET_DIFF];
    ALL_TAC] THEN
  UNDISCH_TAC `(d:(real^3->bool)->bool) SUBSET fam DIFF IMAGE bb (:int)` THEN
  UNDISCH_TAC `FINITE (d:(real^3->bool)->bool)` THEN
  SPEC_TAC(`d:(real^3->bool)->bool`,`d:(real^3->bool)->bool`) THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[DIFF_EMPTY]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`c:real^3->bool`; `t:(real^3->bool)->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih") STRIP_ASSUME_TAC) THEN DISCH_TAC THEN
  SUBGOAL_THEN `(t:(real^3->bool)->bool) SUBSET fam DIFF IMAGE bb (:int) /\
                (c:real^3->bool) IN fam /\ ~(c IN IMAGE bb (:int))` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(c:real^3->bool) INSERT t SUBSET fam DIFF IMAGE bb (:int)` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `separates_in (moi_s32_open g) (moi_s32_set g s2 (fam DIFF t))
                             {(g:real^3->real^3) moi_s32_qlo} {g moi_s32_qhi}` ASSUME_TAC THENL
   [REMOVE_THEN "ih" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `fam DIFF ((c:real^3->bool) INSERT t) = (fam DIFF t) DELETE c` SUBST1_TAC THENL
   [SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC MOI_S3ST_PHASE1_STEP THEN
  MAP_EVERY EXISTS_TAC [`v:real^3->bool`; `pp:int->real^3`; `dd:int->real^3->bool`;
                        `fam:(real^3->bool)->bool`; `bb:int->real^3->bool`;
                        `ja:int->real^3->bool`; `jb:int->real^3->bool`] THEN
  ASM_REWRITE_TAC[SUBSET_DIFF; IN_DIFF] THEN
  UNDISCH_TAC `(t:(real^3->bool)->bool) SUBSET fam DIFF IMAGE bb (:int)` THEN
  UNDISCH_TAC `IMAGE (bb:int->real^3->bool) (:int) SUBSET fam` THEN
  SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Part 10 (Phase 2, first part): the bridges of distinct levels are         *)
(* distinct and disjoint; on T_(2i) the high end jb (i-1) of the bridge     *)
(* below and the low end ja i of the bridge of level i are disjoint          *)
(* essential polygons, so T_(2i) minus both is a finite union of open       *)
(* annuli (TORUS_PIECES); facts on these pieces.                            *)
(* ------------------------------------------------------------------------- *)

let MOI_S3ST_CLOSED_DIFF_OPEN_IN = prove
 (`!(t:real^3->bool) d.
     closed t /\ (!w. w IN d ==> open_in (subtopology euclidean t) (w INTER t))
     ==> closed (t DIFF UNIONS d)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `t DIFF UNIONS d = t DIFF UNIONS {w INTER t | w IN (d:(real^3->bool)->bool)}`
  SUBST1_TAC THENL
   [REWRITE_TAC[UNIONS_GSPEC] THEN SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC CLOSED_IN_CLOSED_TRANS THEN EXISTS_TAC `t:real^3->bool` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CLOSED_IN_DIFF THEN
  REWRITE_TAC[CLOSED_IN_REFL] THEN MATCH_MP_TAC OPEN_IN_UNIONS THEN
  REWRITE_TAC[FORALL_IN_GSPEC] THEN ASM_REWRITE_TAC[]);;

let MOI_S3ST_TORI_MEET = prove
 (`!(g:real^3->real^3) v pp dd s2 m n.
     moi_s32_model g v /\ moi_s32_tower g v pp dd s2 /\
     ~DISJOINT (frontier (s2 (&2 * m))) (frontier (s2 (&2 * n)))
     ==> m = n`,
  MESON_TAC[MOI_S3ST_TORI_DISJ]);;

let MOI_S3ST_BB_INJ = prove
 (`!(g:real^3->real^3) v pp dd s2 fam bb ja jb.
     moi_s32_model g v /\ moi_s32_tower g v pp dd s2 /\
     (!i. bb i IN fam /\ bb i SUBSET moi_s32_lvl g dd i /\
          pl_annulus_with_ends (bb i) (ja i) (jb i) /\
          bb i INTER moi_s32_evens s2 = ja i UNION jb i /\
          moi_s32_ess s2 (&2 * i) (ja i) /\ moi_s32_ess s2 (&2 * i + &2) (jb i))
     ==> !i k. bb i = bb k ==> i = k`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `!m:int. ~((ja:int->real^3->bool) m = {}) /\ ~((jb:int->real^3->bool) m = {}) /\
                        ja m SUBSET frontier ((s2:int->real^3->bool) (&2 * m)) /\
                        jb m SUBSET frontier (s2 (&2 * (m + &1)))`
  ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[INT_ARITH `&2 * (m + &1):int = &2 * m + &2`] THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o SPEC `m:int`) THEN
    MP_TAC(ISPECL [`(bb:int->real^3->bool) m`; `(ja:int->real^3->bool) m`;
                   `(jb:int->real^3->bool) m`] MOI_S3ST_ANN_ENDS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[moi_s32_ess];
    ALL_TAC] THEN
  SUBGOAL_THEN `(ja:int->real^3->bool) i UNION jb i = ja k UNION jb k` ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> MP_TAC(CONJUNCT1(CONJUNCT2(CONJUNCT2(CONJUNCT2(SPEC `i:int` th))))) THEN
      MP_TAC(CONJUNCT1(CONJUNCT2(CONJUNCT2(CONJUNCT2(SPEC `k:int` th)))))) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!m n:int. ~DISJOINT (frontier ((s2:int->real^3->bool) (&2 * m)))
                                    (frontier (s2 (&2 * n))) ==> m = n`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_S3ST_TORI_MEET THEN
    MAP_EVERY EXISTS_TAC [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                          `dd:int->real^3->bool`; `s2:int->real^3->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(i:int = k \/ i = k + &1) /\ (i + &1 = k \/ i + &1 = k + &1)` MP_TAC THENL
   [CONJ_TAC THENL
     [SUBGOAL_THEN `~DISJOINT (frontier ((s2:int->real^3->bool) (&2 * i))) (frontier (s2 (&2 * k))) \/
                    ~DISJOINT (frontier ((s2:int->real^3->bool) (&2 * i)))
                              (frontier (s2 (&2 * (k + &1))))` MP_TAC THENL
       [FIRST_X_ASSUM(K ALL_TAC) THEN
        FIRST_X_ASSUM(fun th -> MP_TAC(SPEC `i:int` th) THEN MP_TAC(SPEC `k:int` th)) THEN
        UNDISCH_TAC `(ja:int->real^3->bool) i UNION jb i = ja k UNION jb k` THEN SET_TAC[];
        ASM_MESON_TAC[]];
      SUBGOAL_THEN `~DISJOINT (frontier ((s2:int->real^3->bool) (&2 * (i + &1))))
                              (frontier (s2 (&2 * k))) \/
                    ~DISJOINT (frontier ((s2:int->real^3->bool) (&2 * (i + &1))))
                              (frontier (s2 (&2 * (k + &1))))` MP_TAC THENL
       [FIRST_X_ASSUM(K ALL_TAC) THEN
        FIRST_X_ASSUM(fun th -> MP_TAC(SPEC `i:int` th) THEN MP_TAC(SPEC `k:int` th)) THEN
        UNDISCH_TAC `(ja:int->real^3->bool) i UNION jb i = ja k UNION jb k` THEN SET_TAC[];
        ASM_MESON_TAC[]]];
    INT_ARITH_TAC]);;

let MOI_S3ST_PH2_ENDS = prove
 (`!(g:real^3->real^3) v pp dd s2 fam bb ja jb i.
     moi_s32_model g v /\ moi_s32_tower g v pp dd s2 /\ pairwise DISJOINT fam /\
     (!i. bb i IN fam /\ bb i SUBSET moi_s32_lvl g dd i /\
          pl_annulus_with_ends (bb i) (ja i) (jb i) /\
          bb i INTER moi_s32_evens s2 = ja i UNION jb i /\
          moi_s32_ess s2 (&2 * i) (ja i) /\ moi_s32_ess s2 (&2 * i + &2) (jb i))
     ==> DISJOINT (jb (i - &1)) (ja i) /\
         moi_s32_ess s2 (&2 * i) (jb (i - &1)) /\ moi_s32_ess s2 (&2 * i) (ja i)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o SPEC `i:int`) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o SPEC `i - &1:int`) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[INT_ARITH `&2 * (i - &1) + &2:int = &2 * i`]) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~((bb:int->real^3->bool) (i - &1) = bb i)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                   `dd:int->real^3->bool`; `s2:int->real^3->bool`; `fam:(real^3->bool)->bool`;
                   `bb:int->real^3->bool`; `ja:int->real^3->bool`; `jb:int->real^3->bool`]
      MOI_S3ST_BB_INJ) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPECL [`i - &1:int`; `i:int`]) THEN
    ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `DISJOINT ((bb:int->real^3->bool) (i - &1)) (bb i)` MP_TAC THENL
   [UNDISCH_TAC `pairwise DISJOINT (fam:(real^3->bool)->bool)` THEN
    REWRITE_TAC[pairwise] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(bb:int->real^3->bool) i`; `(ja:int->real^3->bool) i`;
                 `(jb:int->real^3->bool) i`] MOI_S3ST_ANN_ENDS) THEN
  MP_TAC(ISPECL [`(bb:int->real^3->bool) (i - &1)`; `(ja:int->real^3->bool) (i - &1)`;
                 `(jb:int->real^3->bool) (i - &1)`] MOI_S3ST_ANN_ENDS) THEN
  ASM_REWRITE_TAC[] THEN SET_TAC[]);;

(* The pieces of T_(2i): components of T_(2i) minus jb (i-1) and ja i.     *)

let MOI_S3ST_PIECE_FACTS = prove
 (`!(g:real^3->real^3) v pp dd s2 fam bb ja jb i w.
     MOISE_286_STATEMENT /\ moi_s32_model g v /\ moi_s32_tower g v pp dd s2 /\
     pairwise DISJOINT fam /\
     (!i. bb i IN fam /\ bb i SUBSET moi_s32_lvl g dd i /\
          pl_annulus_with_ends (bb i) (ja i) (jb i) /\
          bb i INTER moi_s32_evens s2 = ja i UNION jb i /\
          moi_s32_ess s2 (&2 * i) (ja i) /\ moi_s32_ess s2 (&2 * i + &2) (jb i)) /\
     w IN components (frontier (s2 (&2 * i)) DIFF (jb (i - &1) UNION ja i))
     ==> w SUBSET frontier (s2 (&2 * i)) /\ DISJOINT w (jb (i - &1) UNION ja i) /\
         ~(w = {}) /\ closure w = w UNION jb (i - &1) UNION ja i /\
         closure w SUBSET frontier (s2 (&2 * i)) /\ compact (closure w) /\
         pl_annulus_with_ends (closure w) (jb (i - &1)) (ja i) /\
         open_in (subtopology euclidean (frontier (s2 (&2 * i)))) w /\
         (!k. DISJOINT w (bb k)) /\ ~(g (vec 0) IN w) /\ w SUBSET IMAGE g v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                 `dd:int->real^3->bool`; `s2:int->real^3->bool`; `fam:(real^3->bool)->bool`;
                 `bb:int->real^3->bool`; `ja:int->real^3->bool`; `jb:int->real^3->bool`;
                 `i:int`] MOI_S3ST_PH2_ENDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                 `dd:int->real^3->bool`; `s2:int->real^3->bool`] MOI_S3ST_TORUS_BASICS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(STRIP_ASSUME_TAC o SPEC `&2 * i:int`) THEN
  MP_TAC(ISPECL [`(s2:int->real^3->bool) (&2 * i)`; `(jb:int->real^3->bool) (i - &1)`;
                 `(ja:int->real^3->bool) i`] MOI_S3ST_TORUS_PIECES) THEN
  SUBGOAL_THEN `moi_s32_ess s2 (&2 * i) ((ja:int->real^3->bool) i)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `moi_s32_ess s2 (&2 * i) ((jb:int->real^3->bool) (i - &1))` THEN
    UNDISCH_TAC `moi_s32_ess s2 (&2 * i) ((ja:int->real^3->bool) i)` THEN
    DISCH_THEN(STRIP_ASSUME_TAC o REWRITE_RULE[moi_s32_ess]) THEN
    DISCH_THEN(STRIP_ASSUME_TAC o REWRITE_RULE[moi_s32_ess]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `w:real^3->bool` o last o CONJUNCTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(w:real^3->bool) SUBSET frontier ((s2:int->real^3->bool) (&2 * i)) DIFF (jb (i - &1) UNION ja i) /\
                ~(w = {})` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC IN_COMPONENTS_SUBSET THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC IN_COMPONENTS_NONEMPTY THEN
      EXISTS_TAC `frontier ((s2:int->real^3->bool) (&2 * i)) DIFF (jb (i - &1) UNION ja i)` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`closure w:real^3->bool`; `(jb:int->real^3->bool) (i - &1)`;
                 `(ja:int->real^3->bool) i`] MOI_S3ST_ANN_ENDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `(w:real^3->bool) SUBSET frontier ((s2:int->real^3->bool) (&2 * i)) DIFF
                                        (jb (i - &1) UNION ja i)` THEN SET_TAC[];
    UNDISCH_TAC `(w:real^3->bool) SUBSET frontier ((s2:int->real^3->bool) (&2 * i)) DIFF
                                        (jb (i - &1) UNION ja i)` THEN SET_TAC[];
    MP_TAC(ISPEC `w:real^3->bool` CLOSURE_SUBSET) THEN
    UNDISCH_TAC `closure (w:real^3->bool) DIFF ((jb:int->real^3->bool) (i - &1) UNION ja i) = w` THEN
    UNDISCH_TAC `(jb:int->real^3->bool) (i - &1) SUBSET closure w` THEN
    UNDISCH_TAC `(ja:int->real^3->bool) i SUBSET closure w` THEN SET_TAC[];
    X_GEN_TAC `k:int` THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o SPEC `k:int`) THEN
    SUBGOAL_THEN `(w:real^3->bool) INTER bb (k:int) SUBSET
                  frontier ((s2:int->real^3->bool) (&2 * i)) INTER (ja k UNION jb k)` ASSUME_TAC THENL
     [SUBGOAL_THEN `frontier ((s2:int->real^3->bool) (&2 * i)) SUBSET moi_s32_evens s2`
      MP_TAC THENL
       [MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                       `dd:int->real^3->bool`; `s2:int->real^3->bool`] MOI_S3ST_EVENS_IN_V) THEN
        ASM_SIMP_TAC[];
        UNDISCH_TAC `(bb:int->real^3->bool) k INTER moi_s32_evens s2 = ja k UNION jb k` THEN
        UNDISCH_TAC `(w:real^3->bool) SUBSET frontier ((s2:int->real^3->bool) (&2 * i)) DIFF (jb (i - &1) UNION ja i)` THEN
        SET_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `(ja:int->real^3->bool) k SUBSET frontier ((s2:int->real^3->bool) (&2 * k)) /\
                  (jb:int->real^3->bool) k SUBSET frontier (s2 (&2 * (k + &1)))`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[INT_ARITH `&2 * (k + &1):int = &2 * k + &2`] THEN
      UNDISCH_TAC `moi_s32_ess s2 (&2 * k) ((ja:int->real^3->bool) k)` THEN
      UNDISCH_TAC `moi_s32_ess s2 (&2 * k + &2) ((jb:int->real^3->bool) k)` THEN
      SIMP_TAC[moi_s32_ess];
      ALL_TAC] THEN
    ASM_CASES_TAC `k:int = i` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN
      MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                     `dd:int->real^3->bool`; `s2:int->real^3->bool`; `i:int`; `i + &1:int`]
        MOI_S3ST_TORI_DISJ) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN INT_ARITH_TAC; ALL_TAC] THEN
      UNDISCH_TAC `(w:real^3->bool) INTER bb (i:int) SUBSET
                   frontier ((s2:int->real^3->bool) (&2 * i)) INTER (ja i UNION jb i)` THEN
      UNDISCH_TAC `(jb:int->real^3->bool) i SUBSET frontier ((s2:int->real^3->bool) (&2 * (i + &1)))` THEN
      UNDISCH_TAC `(w:real^3->bool) SUBSET frontier ((s2:int->real^3->bool) (&2 * i)) DIFF (jb (i - &1) UNION ja i)` THEN
      SET_TAC[];
      ALL_TAC] THEN
    ASM_CASES_TAC `k:int = i - &1` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN
      MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                     `dd:int->real^3->bool`; `s2:int->real^3->bool`; `i:int`; `i - &1:int`]
        MOI_S3ST_TORI_DISJ) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN INT_ARITH_TAC; ALL_TAC] THEN
      UNDISCH_TAC `(w:real^3->bool) INTER bb (i - &1:int) SUBSET
                   frontier ((s2:int->real^3->bool) (&2 * i)) INTER (ja (i - &1) UNION jb (i - &1))` THEN
      UNDISCH_TAC `(ja:int->real^3->bool) (i - &1) SUBSET
                   frontier ((s2:int->real^3->bool) (&2 * (i - &1)))` THEN
      UNDISCH_TAC `(w:real^3->bool) SUBSET frontier ((s2:int->real^3->bool) (&2 * i)) DIFF (jb (i - &1) UNION ja i)` THEN
      SET_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                   `dd:int->real^3->bool`; `s2:int->real^3->bool`; `i:int`; `k:int`]
      MOI_S3ST_TORI_DISJ) THEN
    MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                   `dd:int->real^3->bool`; `s2:int->real^3->bool`; `i:int`; `k + &1:int`]
      MOI_S3ST_TORI_DISJ) THEN
    ASM_REWRITE_TAC[] THEN
    ANTS_TAC THENL [ASM_INT_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `(w:real^3->bool) INTER bb (k:int) SUBSET
                 frontier ((s2:int->real^3->bool) (&2 * i)) INTER (ja k UNION jb k)` THEN
    UNDISCH_TAC `(ja:int->real^3->bool) k SUBSET frontier ((s2:int->real^3->bool) (&2 * k))` THEN
    UNDISCH_TAC `(jb:int->real^3->bool) k SUBSET frontier ((s2:int->real^3->bool) (&2 * (k + &1)))` THEN
    SET_TAC[];
    UNDISCH_TAC `~((g:real^3->real^3) (vec 0) IN frontier ((s2:int->real^3->bool) (&2 * i)))` THEN
    UNDISCH_TAC `(w:real^3->bool) SUBSET frontier ((s2:int->real^3->bool) (&2 * i)) DIFF
                                        (jb (i - &1) UNION ja i)` THEN SET_TAC[];
    UNDISCH_TAC `frontier ((s2:int->real^3->bool) (&2 * i)) SUBSET IMAGE (g:real^3->real^3) v` THEN
    UNDISCH_TAC `(w:real^3->bool) SUBSET frontier ((s2:int->real^3->bool) (&2 * i)) DIFF
                                        (jb (i - &1) UNION ja i)` THEN SET_TAC[]]);;

(* The barrier K + bridges + P' minus some pieces d: the tori minus d, the  *)
(* bridges and P' (pieces miss the bridges and P').                        *)

let MOI_S3ST_PH2_SET = prove
 (`!(g:real^3->real^3) v pp dd s2 fam bb ja jb d.
     MOISE_286_STATEMENT /\ moi_s32_model g v /\ moi_s32_tower g v pp dd s2 /\
     pairwise DISJOINT fam /\
     (!i. bb i IN fam /\ bb i SUBSET moi_s32_lvl g dd i /\
          pl_annulus_with_ends (bb i) (ja i) (jb i) /\
          bb i INTER moi_s32_evens s2 = ja i UNION jb i /\
          moi_s32_ess s2 (&2 * i) (ja i) /\ moi_s32_ess s2 (&2 * i + &2) (jb i)) /\
     (!w. w IN d ==> ?i. w IN components (frontier (s2 (&2 * i)) DIFF (jb (i - &1) UNION ja i)))
     ==> moi_s32_set g s2 (IMAGE bb (:int)) DIFF UNIONS d =
         UNIONS {frontier (s2 (&2 * i)) DIFF UNIONS d | i IN (:int)} UNION
         UNIONS (IMAGE bb (:int)) UNION {g (vec 0)}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `DISJOINT (UNIONS d) (UNIONS (IMAGE (bb:int->real^3->bool) (:int))) /\
                ~((g:real^3->real^3) (vec 0) IN UNIONS d)` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `!w:real^3->bool. w IN d ==> (!k. DISJOINT w ((bb:int->real^3->bool) k)) /\
                                               ~((g:real^3->real^3) (vec 0) IN w)`
    MP_TAC THENL
     [X_GEN_TAC `w:real^3->bool` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `w:real^3->bool` o check (fun th ->
        is_forall(concl th) && fst(dest_var(fst(dest_forall(concl th)))) = "w")) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `i:int`) THEN
      MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                     `dd:int->real^3->bool`; `s2:int->real^3->bool`; `fam:(real^3->bool)->bool`;
                     `bb:int->real^3->bool`; `ja:int->real^3->bool`; `jb:int->real^3->bool`;
                     `i:int`; `w:real^3->bool`] MOI_S3ST_PIECE_FACTS) THEN
      ASM_SIMP_TAC[];
      REWRITE_TAC[DISJOINT; INTER_UNIONS] THEN
      REWRITE_TAC[IN_UNIONS; EXTENSION; NOT_IN_EMPTY; IN_ELIM_THM; IN_INTER; IN_IMAGE;
                  IN_UNIV] THEN
      MESON_TAC[IN_DISJOINT]];
    ALL_TAC] THEN
  REWRITE_TAC[moi_s32_set; moi_s32_evens; UNIONS_GSPEC; IN_UNIV] THEN
  SUBGOAL_THEN `{a:real^3 | ?i. a IN frontier ((s2:int->real^3->bool) (&2 * i)) DIFF UNIONS d} =
                {a | ?i. a IN frontier (s2 (&2 * i))} DIFF UNIONS d` SUBST1_TAC THENL
   [SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC(SET_RULE
   `!kk b u p:real^3. DISJOINT u b /\ ~(p IN u)
                      ==> (kk UNION b UNION {p}) DIFF u = (kk DIFF u) UNION b UNION {p}`) THEN
  ASM_REWRITE_TAC[]);;

let MOI_S3ST_PH2_CLOSED = prove
 (`!(g:real^3->real^3) v pp dd s2 lev fam bb ja jb d.
     MOISE_286_STATEMENT /\ moi_s32_model g v /\ moi_s32_tower g v pp dd s2 /\
     moi_s32_state g dd s2 lev fam /\
     (!i. bb i IN fam /\ bb i SUBSET moi_s32_lvl g dd i /\
          pl_annulus_with_ends (bb i) (ja i) (jb i) /\
          bb i INTER moi_s32_evens s2 = ja i UNION jb i /\
          moi_s32_ess s2 (&2 * i) (ja i) /\ moi_s32_ess s2 (&2 * i + &2) (jb i)) /\
     (!w. w IN d ==> ?i. w IN components (frontier (s2 (&2 * i)) DIFF (jb (i - &1) UNION ja i)))
     ==> closed_in (subtopology euclidean (moi_s32_open g))
                   (moi_s32_set g s2 (IMAGE bb (:int)) DIFF UNIONS d)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `pairwise DISJOINT (fam:(real^3->bool)->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `moi_s32_state g dd s2 lev fam` THEN SIMP_TAC[moi_s32_state]; ALL_TAC] THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                 `dd:int->real^3->bool`; `s2:int->real^3->bool`; `fam:(real^3->bool)->bool`;
                 `bb:int->real^3->bool`; `ja:int->real^3->bool`; `jb:int->real^3->bool`;
                 `d:(real^3->bool)->bool`] MOI_S3ST_PH2_SET) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                 `dd:int->real^3->bool`; `s2:int->real^3->bool`; `lev:int->bool`;
                 `fam:(real^3->bool)->bool`; `IMAGE (bb:int->real^3->bool) (:int)`; `(:int)`;
                 `\i:int. frontier ((s2:int->real^3->bool) (&2 * i)) DIFF UNIONS d`]
    MOI_S3ST_BARRIER_CLOSED) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[IN_UNIV; SUBSET_DIFF] THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_UNIV] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `i:int` THEN MATCH_MP_TAC MOI_S3ST_CLOSED_DIFF_OPEN_IN THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                 `dd:int->real^3->bool`; `s2:int->real^3->bool`] MOI_S3ST_TORUS_BASICS) THEN
  ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN DISCH_TAC THEN
  X_GEN_TAC `w:real^3->bool` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `w:real^3->bool` o check (fun th ->
    is_forall(concl th) && fst(dest_var(fst(dest_forall(concl th)))) = "w")) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `i':int`) THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                 `dd:int->real^3->bool`; `s2:int->real^3->bool`; `fam:(real^3->bool)->bool`;
                 `bb:int->real^3->bool`; `ja:int->real^3->bool`; `jb:int->real^3->bool`;
                 `i':int`; `w:real^3->bool`] MOI_S3ST_PIECE_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_CASES_TAC `i':int = i` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    SUBGOAL_THEN `(w:real^3->bool) INTER frontier ((s2:int->real^3->bool) (&2 * i)) = w`
    SUBST1_TAC THENL
     [UNDISCH_TAC `(w:real^3->bool) SUBSET frontier ((s2:int->real^3->bool) (&2 * i))` THEN
      SET_TAC[];
      ASM_REWRITE_TAC[]];
    MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                   `dd:int->real^3->bool`; `s2:int->real^3->bool`; `i':int`; `i:int`]
      MOI_S3ST_TORI_DISJ) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `(w:real^3->bool) INTER frontier ((s2:int->real^3->bool) (&2 * i)) = {}`
    SUBST1_TAC THENL
     [UNDISCH_TAC `(w:real^3->bool) SUBSET frontier ((s2:int->real^3->bool) (&2 * i'))` THEN
      UNDISCH_TAC `DISJOINT (frontier ((s2:int->real^3->bool) (&2 * i')))
                            (frontier (s2 (&2 * i)))` THEN SET_TAC[];
      REWRITE_TAC[OPEN_IN_EMPTY]]]);;

(* One deletion of Phase 2: a piece w of T_(2i) other than w0 i, against   *)
(* the closed surface closure (w0 i) UNION closure w.                      *)

let MOI_S3ST_PH2_STEP = prove
 (`!(g:real^3->real^3) v pp dd s2 lev fam bb ja jb w0 d w i.
     MOISE_286_STATEMENT /\ moi_s32_model g v /\ moi_s32_tower g v pp dd s2 /\
     moi_s32_state g dd s2 lev fam /\
     (!i. bb i IN fam /\ bb i SUBSET moi_s32_lvl g dd i /\
          pl_annulus_with_ends (bb i) (ja i) (jb i) /\
          bb i INTER moi_s32_evens s2 = ja i UNION jb i /\
          moi_s32_ess s2 (&2 * i) (ja i) /\ moi_s32_ess s2 (&2 * i + &2) (jb i)) /\
     (!i. w0 i IN components (frontier (s2 (&2 * i)) DIFF (jb (i - &1) UNION ja i))) /\
     (!w'. w' IN d ==> ?i'. w' IN components (frontier (s2 (&2 * i')) DIFF
                                                (jb (i' - &1) UNION ja i')) /\
                            ~(w' = w0 i')) /\
     w IN components (frontier (s2 (&2 * i)) DIFF (jb (i - &1) UNION ja i)) /\
     ~(w = w0 i) /\ ~(w IN d) /\
     separates_in (moi_s32_open g) (moi_s32_set g s2 (IMAGE bb (:int)) DIFF UNIONS d)
                  {g moi_s32_qlo} {g moi_s32_qhi}
     ==> separates_in (moi_s32_open g)
                      (moi_s32_set g s2 (IMAGE bb (:int)) DIFF UNIONS (w INSERT d))
                      {g moi_s32_qlo} {g moi_s32_qhi}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `pairwise DISJOINT (fam:(real^3->bool)->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `moi_s32_state g dd s2 lev fam` THEN SIMP_TAC[moi_s32_state]; ALL_TAC] THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                 `dd:int->real^3->bool`; `s2:int->real^3->bool`; `fam:(real^3->bool)->bool`;
                 `bb:int->real^3->bool`; `ja:int->real^3->bool`; `jb:int->real^3->bool`;
                 `i:int`; `w:real^3->bool`] MOI_S3ST_PIECE_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th -> is_eq (concl th) &&
    lhs (concl th) = `closure (w:real^3->bool)`)) THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                 `dd:int->real^3->bool`; `s2:int->real^3->bool`; `fam:(real^3->bool)->bool`;
                 `bb:int->real^3->bool`; `ja:int->real^3->bool`; `jb:int->real^3->bool`;
                 `i:int`; `(w0:int->real^3->bool) i`] MOI_S3ST_PIECE_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th -> is_eq (concl th) &&
    lhs (concl th) = `closure ((w0:int->real^3->bool) i)`)) THEN
  MP_TAC(ISPECL [`closure w:real^3->bool`; `(jb:int->real^3->bool) (i - &1)`;
                 `(ja:int->real^3->bool) i`] MOI_S3ST_ANN_ENDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`closure w:real^3->bool`; `(jb:int->real^3->bool) (i - &1)`;
                 `(ja:int->real^3->bool) i`] ANNULUS_COMPLEX) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `cw:(real^3->bool)->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`closure ((w0:int->real^3->bool) i)`; `(jb:int->real^3->bool) (i - &1)`;
                 `(ja:int->real^3->bool) i`] ANNULUS_COMPLEX) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `ch:(real^3->bool)->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `DISJOINT (w:real^3->bool) ((w0:int->real^3->bool) i)` ASSUME_TAC THENL
   [REWRITE_TAC[DISJOINT] THEN
    MP_TAC(ISPECL [`frontier ((s2:int->real^3->bool) (&2 * i)) DIFF
                    ((jb:int->real^3->bool) (i - &1) UNION ja i)`;
                   `w:real^3->bool`; `(w0:int->real^3->bool) i`] COMPONENTS_NONOVERLAP) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `closure ((w0:int->real^3->bool) i) INTER closure w = jb (i - &1) UNION ja i /\
                closure ((w0:int->real^3->bool) i) INTER w = {} /\
                closure (w:real^3->bool) DIFF w = jb (i - &1) UNION ja i`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `DISJOINT (w:real^3->bool) ((w0:int->real^3->bool) i)` THEN
    UNDISCH_TAC `DISJOINT (w:real^3->bool) ((jb:int->real^3->bool) (i - &1) UNION ja i)` THEN
    UNDISCH_TAC `DISJOINT ((w0:int->real^3->bool) i) ((jb:int->real^3->bool) (i - &1) UNION ja i)` THEN
    UNDISCH_TAC `w UNION (jb:int->real^3->bool) (i - &1) UNION ja i = closure w` THEN
    UNDISCH_TAC `(w0:int->real^3->bool) i UNION (jb:int->real^3->bool) (i - &1) UNION ja i =
                 closure (w0 i)` THEN
    SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`ch:(real^3->bool)->bool`; `cw:(real^3->bool)->bool`;
                 `(jb:int->real^3->bool) (i - &1) UNION ja i`;
                 `{}:real^3->bool`; `{}:real^3->bool`] MOI_S3ST_GLUE2) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[UNION_EMPTY; CLOSED_EMPTY; DISJOINT_EMPTY] THEN
    ASM_SIMP_TAC[CLOSED_UNION; COMPACT_IMP_CLOSED];
    ALL_TAC] THEN
  REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:(real^3->bool)->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!w':real^3->bool. w' IN d
                ==> ?i'. w' IN components (frontier ((s2:int->real^3->bool) (&2 * i')) DIFF
                                           ((jb:int->real^3->bool) (i' - &1) UNION ja i'))`
  ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!w':real^3->bool. w' IN d
                ==> DISJOINT w' (closure ((w0:int->real^3->bool) i) UNION closure w)`
  ASSUME_TAC THENL
   [X_GEN_TAC `w':real^3->bool` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `w':real^3->bool` o check (fun th ->
      is_forall(concl th) && fst(dest_var(fst(dest_forall(concl th)))) = "w'" &&
      can (find_term (fun t -> is_var t && fst(dest_var t) = "w0")) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `i':int` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                   `dd:int->real^3->bool`; `s2:int->real^3->bool`; `fam:(real^3->bool)->bool`;
                   `bb:int->real^3->bool`; `ja:int->real^3->bool`; `jb:int->real^3->bool`;
                   `i':int`; `w':real^3->bool`] MOI_S3ST_PIECE_FACTS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_CASES_TAC `i':int = i` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN
      SUBGOAL_THEN `DISJOINT (w':real^3->bool) w /\ DISJOINT w' ((w0:int->real^3->bool) i)`
      MP_TAC THENL
       [REWRITE_TAC[DISJOINT] THEN CONJ_TAC THENL
         [MP_TAC(ISPECL [`frontier ((s2:int->real^3->bool) (&2 * i)) DIFF
                          ((jb:int->real^3->bool) (i - &1) UNION ja i)`;
                         `w':real^3->bool`; `w:real^3->bool`] COMPONENTS_NONOVERLAP) THEN
          ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
          MP_TAC(ISPECL [`frontier ((s2:int->real^3->bool) (&2 * i)) DIFF
                          ((jb:int->real^3->bool) (i - &1) UNION ja i)`;
                         `w':real^3->bool`; `(w0:int->real^3->bool) i`] COMPONENTS_NONOVERLAP) THEN
          ASM_REWRITE_TAC[]];
        UNDISCH_TAC `DISJOINT (w':real^3->bool) ((jb:int->real^3->bool) (i - &1) UNION ja i)` THEN
        UNDISCH_TAC `w UNION (jb:int->real^3->bool) (i - &1) UNION ja i = closure w` THEN
        UNDISCH_TAC `(w0:int->real^3->bool) i UNION (jb:int->real^3->bool) (i - &1) UNION ja i =
                     closure (w0 i)` THEN
        SET_TAC[]];
      MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                     `dd:int->real^3->bool`; `s2:int->real^3->bool`; `i':int`; `i:int`]
        MOI_S3ST_TORI_DISJ) THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(w':real^3->bool) SUBSET frontier ((s2:int->real^3->bool) (&2 * i'))` THEN
      UNDISCH_TAC `closure (w:real^3->bool) SUBSET frontier ((s2:int->real^3->bool) (&2 * i))` THEN
      UNDISCH_TAC `closure ((w0:int->real^3->bool) i) SUBSET
                   frontier ((s2:int->real^3->bool) (&2 * i))` THEN
      SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`] MOI_S3ST_GV_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                 `dd:int->real^3->bool`; `s2:int->real^3->bool`] MOI_S3ST_EVENS_IN_V) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `closure ((w0:int->real^3->bool) i) UNION closure w SUBSET
                moi_s32_set g s2 (IMAGE (bb:int->real^3->bool) (:int)) DIFF UNIONS d`
  ASSUME_TAC THENL
   [MATCH_MP_TAC(SET_RULE
     `!t kk x s:real^3->bool. s SUBSET t /\ t SUBSET kk /\ kk SUBSET x /\
                                (!w'. w' IN d ==> DISJOINT w' s)
                                ==> s SUBSET x DIFF UNIONS d`) THEN
    MAP_EVERY EXISTS_TAC [`frontier ((s2:int->real^3->bool) (&2 * i))`; `moi_s32_evens s2`] THEN
    ASM_REWRITE_TAC[UNION_SUBSET] THEN REWRITE_TAC[moi_s32_set] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `UNIONS cw DIFF surface_boundary cw = (w:real^3->bool)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `DISJOINT (w:real^3->bool) ((jb:int->real^3->bool) (i - &1) UNION ja i)` THEN
    UNDISCH_TAC `w UNION (jb:int->real^3->bool) (i - &1) UNION ja i = closure w` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_s32_set g s2 (IMAGE bb (:int)) DIFF UNIONS ((w:real^3->bool) INSERT d) =
                (moi_s32_set g s2 (IMAGE (bb:int->real^3->bool) (:int)) DIFF UNIONS d) DIFF w`
  SUBST1_TAC THENL [REWRITE_TAC[UNIONS_INSERT] THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(moi_s32_set g s2 (IMAGE (bb:int->real^3->bool) (:int)) DIFF UNIONS d) DIFF w =
                (moi_s32_set g s2 (IMAGE bb (:int)) DIFF UNIONS d) DIFF
                (UNIONS cw DIFF surface_boundary cw)` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `closure ((w0:int->real^3->bool) i) UNION closure w SUBSET IMAGE (g:real^3->real^3) v`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                   `dd:int->real^3->bool`; `s2:int->real^3->bool`] MOI_S3ST_TORUS_BASICS) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `&2 * i:int`) THEN
    UNDISCH_TAC `closure (w:real^3->bool) SUBSET frontier ((s2:int->real^3->bool) (&2 * i))` THEN
    UNDISCH_TAC `closure ((w0:int->real^3->bool) i) SUBSET
                 frontier ((s2:int->real^3->bool) (&2 * i))` THEN
    SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_S3ST_SD THEN EXISTS_TAC `e:(real^3->bool)->bool` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MOI_S3ST_PH2_CLOSED THEN
    MAP_EVERY EXISTS_TAC [`v:real^3->bool`; `pp:int->real^3`; `dd:int->real^3->bool`;
                          `lev:int->bool`; `fam:(real^3->bool)->bool`;
                          `ja:int->real^3->bool`; `jb:int->real^3->bool`] THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC CONNECTED_UNION THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    REWRITE_TAC[SUBSET_UNION];
    SUBGOAL_THEN `(closure ((w0:int->real^3->bool) i) UNION closure w) DIFF w =
                  closure (w0 i)` SUBST1_TAC THENL
     [UNDISCH_TAC `closure ((w0:int->real^3->bool) i) INTER w = {}` THEN
      UNDISCH_TAC `closure (w:real^3->bool) DIFF w = (jb:int->real^3->bool) (i - &1) UNION ja i` THEN
      UNDISCH_TAC `closure ((w0:int->real^3->bool) i) INTER closure w =
                   (jb:int->real^3->bool) (i - &1) UNION ja i` THEN
      SET_TAC[];
      ASM_SIMP_TAC[COMPACT_IMP_CLOSED]];
    SUBGOAL_THEN `(moi_s32_set g s2 (IMAGE (bb:int->real^3->bool) (:int)) DIFF UNIONS d) DIFF w =
                  moi_s32_set g s2 (IMAGE bb (:int)) DIFF UNIONS ((w:real^3->bool) INSERT d)`
    SUBST1_TAC THENL [REWRITE_TAC[UNIONS_INSERT] THEN SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC MOI_S3ST_PH2_CLOSED THEN
    MAP_EVERY EXISTS_TAC [`v:real^3->bool`; `pp:int->real^3`; `dd:int->real^3->bool`;
                          `lev:int->bool`; `fam:(real^3->bool)->bool`;
                          `ja:int->real^3->bool`; `jb:int->real^3->bool`] THEN
    ASM_REWRITE_TAC[FORALL_IN_INSERT] THEN EXISTS_TAC `i:int` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOI_S3ST_OUTSIDE THEN EXISTS_TAC `v:real^3->bool` THEN
    ASM_REWRITE_TAC[MOI_S3ST_QPTS];
    MATCH_MP_TAC MOI_S3ST_OUTSIDE THEN EXISTS_TAC `v:real^3->bool` THEN
    ASM_REWRITE_TAC[MOI_S3ST_QPTS]]);;

let MOI_S3ST_PH2_COMPS = prove
 (`!(g:real^3->real^3) v pp dd s2 fam bb ja jb i.
     MOISE_286_STATEMENT /\ moi_s32_model g v /\ moi_s32_tower g v pp dd s2 /\
     pairwise DISJOINT fam /\
     (!i. bb i IN fam /\ bb i SUBSET moi_s32_lvl g dd i /\
          pl_annulus_with_ends (bb i) (ja i) (jb i) /\
          bb i INTER moi_s32_evens s2 = ja i UNION jb i /\
          moi_s32_ess s2 (&2 * i) (ja i) /\ moi_s32_ess s2 (&2 * i + &2) (jb i))
     ==> FINITE (components (frontier (s2 (&2 * i)) DIFF (jb (i - &1) UNION ja i))) /\
         ?w. w IN components (frontier (s2 (&2 * i)) DIFF (jb (i - &1) UNION ja i))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                 `dd:int->real^3->bool`; `s2:int->real^3->bool`; `fam:(real^3->bool)->bool`;
                 `bb:int->real^3->bool`; `ja:int->real^3->bool`; `jb:int->real^3->bool`;
                 `i:int`] MOI_S3ST_PH2_ENDS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN (STRIP_ASSUME_TAC o REWRITE_RULE[moi_s32_ess]))) THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                 `dd:int->real^3->bool`; `s2:int->real^3->bool`] MOI_S3ST_TORUS_BASICS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(STRIP_ASSUME_TAC o SPEC `&2 * i:int`) THEN
  MP_TAC(ISPECL [`(s2:int->real^3->bool) (&2 * i)`; `(jb:int->real^3->bool) (i - &1)`;
                 `(ja:int->real^3->bool) i`] MOI_S3ST_TORUS_PIECES) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY] o check (fun th ->
    is_neg(concl th) && is_eq(rand(concl th)))) THEN
  DISCH_THEN(X_CHOOSE_TAC `y:real^3`) THEN
  EXISTS_TAC `connected_component (frontier ((s2:int->real^3->bool) (&2 * i)) DIFF
                                   ((jb:int->real^3->bool) (i - &1) UNION ja i)) y` THEN
  ASM_REWRITE_TAC[CONNECTED_COMPONENT_IN_COMPONENTS]);;

let MOI_S3ST_PH2_TORUS_EQ = prove
 (`!(g:real^3->real^3) v pp dd s2 fam bb ja jb w0 i.
     MOISE_286_STATEMENT /\ moi_s32_model g v /\ moi_s32_tower g v pp dd s2 /\
     pairwise DISJOINT fam /\
     (!i. bb i IN fam /\ bb i SUBSET moi_s32_lvl g dd i /\
          pl_annulus_with_ends (bb i) (ja i) (jb i) /\
          bb i INTER moi_s32_evens s2 = ja i UNION jb i /\
          moi_s32_ess s2 (&2 * i) (ja i) /\ moi_s32_ess s2 (&2 * i + &2) (jb i)) /\
     (!i. w0 i IN components (frontier (s2 (&2 * i)) DIFF (jb (i - &1) UNION ja i)))
     ==> frontier (s2 (&2 * i)) DIFF
         UNIONS {w | ?k. w IN components (frontier (s2 (&2 * k)) DIFF (jb (k - &1) UNION ja k)) /\
                         ~(w = w0 k)} =
         closure (w0 i)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                 `dd:int->real^3->bool`; `s2:int->real^3->bool`; `fam:(real^3->bool)->bool`;
                 `bb:int->real^3->bool`; `ja:int->real^3->bool`; `jb:int->real^3->bool`;
                 `i:int`; `(w0:int->real^3->bool) i`] MOI_S3ST_PIECE_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `y:real^3` THEN
  REWRITE_TAC[IN_DIFF; IN_UNIONS; IN_ELIM_THM] THEN EQ_TAC THENL
   [STRIP_TAC THEN ASM_REWRITE_TAC[IN_UNION] THEN
    ASM_CASES_TAC `(y:real^3) IN (jb:int->real^3->bool) (i - &1) UNION ja i` THENL
     [UNDISCH_TAC `(y:real^3) IN (jb:int->real^3->bool) (i - &1) UNION ja i` THEN
      REWRITE_TAC[IN_UNION] THEN MESON_TAC[];
      ALL_TAC] THEN
    DISJ1_TAC THEN
    ABBREV_TAC `c = connected_component (frontier ((s2:int->real^3->bool) (&2 * i)) DIFF
                                          ((jb:int->real^3->bool) (i - &1) UNION ja i)) y` THEN
    SUBGOAL_THEN `(c:real^3->bool) IN components (frontier ((s2:int->real^3->bool) (&2 * i)) DIFF
                                          ((jb:int->real^3->bool) (i - &1) UNION ja i)) /\
                  (y:real^3) IN c` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "c" THEN REWRITE_TAC[CONNECTED_COMPONENT_IN_COMPONENTS] THEN
      GEN_REWRITE_TAC (RAND_CONV) [IN] THEN
      REWRITE_TAC[CONNECTED_COMPONENT_REFL_EQ] THEN ASM_REWRITE_TAC[IN_DIFF];
      ALL_TAC] THEN
    ASM_CASES_TAC `c = (w0:int->real^3->bool) i` THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `~(?t. (?k. t IN components (frontier ((s2:int->real^3->bool) (&2 * k)) DIFF
                                             ((jb:int->real^3->bool) (k - &1) UNION ja k)) /\
                            ~(t = (w0:int->real^3->bool) k)) /\ (y:real^3) IN t)` THEN
    MATCH_MP_TAC(TAUT `p ==> ~p ==> q`) THEN
    EXISTS_TAC `c:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `i:int` THEN ASM_REWRITE_TAC[];
    DISCH_TAC THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real^3->bool` (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `k:int` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
    MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                   `dd:int->real^3->bool`; `s2:int->real^3->bool`; `fam:(real^3->bool)->bool`;
                   `bb:int->real^3->bool`; `ja:int->real^3->bool`; `jb:int->real^3->bool`;
                   `k:int`; `t:real^3->bool`] MOI_S3ST_PIECE_FACTS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_CASES_TAC `k:int = i` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN
      MP_TAC(ISPECL [`frontier ((s2:int->real^3->bool) (&2 * i)) DIFF
                      ((jb:int->real^3->bool) (i - &1) UNION ja i)`;
                     `t:real^3->bool`; `(w0:int->real^3->bool) i`] COMPONENTS_NONOVERLAP) THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(y:real^3) IN closure ((w0:int->real^3->bool) i)` THEN
      UNDISCH_TAC `(y:real^3) IN t` THEN
      UNDISCH_TAC `DISJOINT (t:real^3->bool) ((jb:int->real^3->bool) (i - &1) UNION ja i)` THEN
      UNDISCH_TAC `closure ((w0:int->real^3->bool) i) =
                   w0 i UNION (jb:int->real^3->bool) (i - &1) UNION ja i` THEN
      SET_TAC[];
      MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                     `dd:int->real^3->bool`; `s2:int->real^3->bool`; `k:int`; `i:int`]
        MOI_S3ST_TORI_DISJ) THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(y:real^3) IN closure ((w0:int->real^3->bool) i)` THEN
      UNDISCH_TAC `(y:real^3) IN t` THEN
      UNDISCH_TAC `(t:real^3->bool) SUBSET frontier ((s2:int->real^3->bool) (&2 * k))` THEN
      UNDISCH_TAC `closure ((w0:int->real^3->bool) i) SUBSET
                   frontier ((s2:int->real^3->bool) (&2 * i))` THEN
      SET_TAC[]]]);;

(* Phase 2: all the pieces other than w0 i deleted; what remains is the    *)
(* chain set with hh i = closure (w0 i).                                    *)

let MOI_S3ST_PHASE2 = prove
 (mk_imp(moi_n3 MOI_S32_LIMIT,
  `!(g:real^3->real^3) v pp dd s2 fam bb ja jb w0.
     MOISE_286_STATEMENT /\ moi_s32_model g v /\ moi_s32_tower g v pp dd s2 /\
     moi_s32_state g dd s2 (:int) fam /\
     (!i. bb i IN fam /\ bb i SUBSET moi_s32_lvl g dd i /\
          pl_annulus_with_ends (bb i) (ja i) (jb i) /\
          bb i INTER moi_s32_evens s2 = ja i UNION jb i /\
          moi_s32_ess s2 (&2 * i) (ja i) /\ moi_s32_ess s2 (&2 * i + &2) (jb i)) /\
     (!i. w0 i IN components (frontier (s2 (&2 * i)) DIFF (jb (i - &1) UNION ja i))) /\
     separates_in (moi_s32_open g) (moi_s32_set g s2 (IMAGE bb (:int)))
                  {g moi_s32_qlo} {g moi_s32_qhi}
     ==> closed_in (subtopology euclidean (moi_s32_open g))
                   (moi_s32_chainset g (\i. closure (w0 i)) bb) /\
         separates_in (moi_s32_open g) (moi_s32_chainset g (\i. closure (w0 i)) bb)
                      {g moi_s32_qlo} {g moi_s32_qhi}`),
  DISCH_THEN(LABEL_TAC "lim") THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `pairwise DISJOINT (fam:(real^3->bool)->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `moi_s32_state g dd s2 (:int) fam` THEN SIMP_TAC[moi_s32_state]; ALL_TAC] THEN
  ABBREV_TAC `p2 = {w:real^3->bool | ?k. w IN components (frontier ((s2:int->real^3->bool) (&2 * k))
                                                 DIFF ((jb:int->real^3->bool) (k - &1) UNION ja k)) /\
                                         ~(w = (w0:int->real^3->bool) k)}` THEN
  SUBGOAL_THEN `?lv:(real^3->bool)->int.
                  !w. w IN p2
                      ==> w IN components (frontier ((s2:int->real^3->bool) (&2 * lv w)) DIFF
                                           ((jb:int->real^3->bool) (lv w - &1) UNION ja (lv w))) /\
                          ~(w = (w0:int->real^3->bool) (lv w))`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `!w:real^3->bool. ?k. w IN p2
                    ==> w IN components (frontier ((s2:int->real^3->bool) (&2 * k)) DIFF
                                         ((jb:int->real^3->bool) (k - &1) UNION ja k)) /\
                        ~(w = (w0:int->real^3->bool) k)` MP_TAC THENL
     [EXPAND_TAC "p2" THEN REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[];
      REWRITE_TAC[SKOLEM_THM]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!d. d SUBSET p2
                    ==> !w:real^3->bool. w IN d
                        ==> ?i. w IN components (frontier ((s2:int->real^3->bool) (&2 * i)) DIFF
                                                 ((jb:int->real^3->bool) (i - &1) UNION ja i))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXISTS_TAC `(lv:(real^3->bool)->int) w` THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_s32_chainset g (\i. closure ((w0:int->real^3->bool) i)) bb =
                moi_s32_set g s2 (IMAGE (bb:int->real^3->bool) (:int)) DIFF UNIONS p2`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                   `dd:int->real^3->bool`; `s2:int->real^3->bool`; `fam:(real^3->bool)->bool`;
                   `bb:int->real^3->bool`; `ja:int->real^3->bool`; `jb:int->real^3->bool`;
                   `p2:(real^3->bool)->bool`] MOI_S3ST_PH2_SET) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[SUBSET_REFL];
      ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN
    SUBGOAL_THEN `!i. frontier ((s2:int->real^3->bool) (&2 * i)) DIFF UNIONS p2 =
                      closure ((w0:int->real^3->bool) i)` (fun th -> REWRITE_TAC[th]) THENL
     [GEN_TAC THEN EXPAND_TAC "p2" THEN MATCH_MP_TAC MOI_S3ST_PH2_TORUS_EQ THEN
      MAP_EVERY EXISTS_TAC [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                            `dd:int->real^3->bool`; `fam:(real^3->bool)->bool`;
                            `bb:int->real^3->bool`] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[moi_s32_chainset; UNIONS_GSPEC; UNIONS_IMAGE] THEN
    GEN_REWRITE_TAC I [EXTENSION] THEN
    REWRITE_TAC[IN_ELIM_THM; IN_UNION; IN_UNIV; IN_SING] THEN MESON_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC MOI_S3ST_PH2_CLOSED THEN
    MAP_EVERY EXISTS_TAC [`v:real^3->bool`; `pp:int->real^3`; `dd:int->real^3->bool`;
                          `(:int)`; `fam:(real^3->bool)->bool`;
                          `ja:int->real^3->bool`; `jb:int->real^3->bool`] THEN
    ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[SUBSET_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `!d. FINITE d ==> d SUBSET p2
                    ==> separates_in (moi_s32_open g)
                          (moi_s32_set g s2 (IMAGE (bb:int->real^3->bool) (:int)) DIFF UNIONS d)
                          {(g:real^3->real^3) moi_s32_qlo} {g moi_s32_qhi}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC[UNIONS_0; DIFF_EMPTY]; ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`x:real^3->bool`; `t:(real^3->bool)->bool`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih") STRIP_ASSUME_TAC) THEN DISCH_TAC THEN
    SUBGOAL_THEN `(t:(real^3->bool)->bool) SUBSET p2 /\ (x:real^3->bool) IN p2`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(x:real^3->bool) INSERT t SUBSET p2` THEN SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC MOI_S3ST_PH2_STEP THEN
    MAP_EVERY EXISTS_TAC [`v:real^3->bool`; `pp:int->real^3`; `dd:int->real^3->bool`;
                          `(:int)`; `fam:(real^3->bool)->bool`;
                          `ja:int->real^3->bool`; `jb:int->real^3->bool`;
                          `w0:int->real^3->bool`; `(lv:(real^3->bool)->int) x`] THEN
    ASM_SIMP_TAC[] THEN
    X_GEN_TAC `w':real^3->bool` THEN DISCH_TAC THEN
    EXISTS_TAC `(lv:(real^3->bool)->int) w'` THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall(concl th) && fst(dest_var(fst(dest_forall(concl th)))) = "w" &&
      can (find_term (fun t -> is_var t && fst(dest_var t) = "lv")) (concl th))) THEN
    UNDISCH_TAC `(t:(real^3->bool)->bool) SUBSET p2` THEN
    UNDISCH_TAC `(w':real^3->bool) IN t` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `UNIONS p2 = UNIONS (IMAGE (\w:real^3->bool. w) p2)` SUBST1_TAC THENL
   [REWRITE_TAC[IMAGE_ID]; ALL_TAC] THEN
  USE_THEN "lim" (MATCH_MP_TAC o
    MATCH_MP (INST_TYPE [`:real^3->bool`,`:A`] MOI_S3ST_LIMIT_PIECES)) THEN
  MAP_EVERY EXISTS_TAC [`v:real^3->bool`; `pp:int->real^3`; `dd:int->real^3->bool`;
                        `s2:int->real^3->bool`; `lv:(real^3->bool)->int`] THEN
  ASM_REWRITE_TAC[IMAGE_ID] THEN
  SUBGOAL_THEN `~((g:real^3->real^3) moi_s32_qlo IN moi_s32_set g s2 (IMAGE bb (:int))) /\
                ~(g moi_s32_qhi IN moi_s32_set g s2 (IMAGE (bb:int->real^3->bool) (:int)))`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`moi_s32_open g`; `moi_s32_set g s2 (IMAGE (bb:int->real^3->bool) (:int))`;
                   `(g:real^3->real^3) moi_s32_qlo`; `(g:real^3->real^3) moi_s32_qhi`]
      MOI_S3ST_SEP_OPEN) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`] MOI_S3ST_GV_FACTS) THEN
      ASM_SIMP_TAC[];
      SET_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `w:real^3->bool` THEN DISCH_TAC THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `frontier ((s2:int->real^3->bool) (&2 * (lv:(real^3->bool)->int) w))` THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                     `dd:int->real^3->bool`; `s2:int->real^3->bool`; `fam:(real^3->bool)->bool`;
                     `bb:int->real^3->bool`; `ja:int->real^3->bool`; `jb:int->real^3->bool`;
                     `(lv:(real^3->bool)->int) w`; `w:real^3->bool`] MOI_S3ST_PIECE_FACTS) THEN
      ASM_SIMP_TAC[];
      MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                     `dd:int->real^3->bool`; `s2:int->real^3->bool`;
                     `(lv:(real^3->bool)->int) w`] MOI_S3ST_TORI_IN_LVL) THEN
      ASM_SIMP_TAC[]];
    X_GEN_TAC `i:int` THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `components (frontier ((s2:int->real^3->bool) (&2 * i)) DIFF
                            ((jb:int->real^3->bool) (i - &1) UNION ja i))` THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                     `dd:int->real^3->bool`; `s2:int->real^3->bool`; `fam:(real^3->bool)->bool`;
                     `bb:int->real^3->bool`; `ja:int->real^3->bool`; `jb:int->real^3->bool`;
                     `i:int`] MOI_S3ST_PH2_COMPS) THEN
      ASM_SIMP_TAC[];
      GEN_REWRITE_TAC I [SUBSET] THEN REWRITE_TAC[IN_ELIM_THM] THEN
      X_GEN_TAC `w:real^3->bool` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN ASM_SIMP_TAC[]];
    REWRITE_TAC[moi_s32_set; IN_UNION; IN_SING];
    MATCH_MP_TAC MOI_S3ST_PH2_CLOSED THEN
    MAP_EVERY EXISTS_TAC [`v:real^3->bool`; `pp:int->real^3`; `dd:int->real^3->bool`;
                          `(:int)`; `fam:(real^3->bool)->bool`;
                          `ja:int->real^3->bool`; `jb:int->real^3->bool`] THEN
    ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[SUBSET_REFL];
    X_GEN_TAC `d:(real^3->bool)->bool` THEN STRIP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC MOI_S3ST_PH2_CLOSED THEN
      MAP_EVERY EXISTS_TAC [`v:real^3->bool`; `pp:int->real^3`; `dd:int->real^3->bool`;
                            `(:int)`; `fam:(real^3->bool)->bool`;
                            `ja:int->real^3->bool`; `jb:int->real^3->bool`] THEN
      ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* Part 11: Steps 2-4 and the final deletion (STEPS24).  The bridges bb i   *)
(* (Part 7, with ends ja i on T_(2i), jb i on T_(2i+2)), Phase 1, a         *)
(* component w0 i of T_(2i) minus jb (i-1) and ja i, Phase 2; the chain is  *)
(* hh i = closure (w0 i), jl i = jb (i-1), jh i = ja i.                     *)
(* MOISE_267 is an antecedent of the statement and is not used.             *)
(* ------------------------------------------------------------------------- *)

let STEPS24 = prove
 (MOI_S32_STEPS24,
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (K ALL_TAC)
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "lim")))) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `moi_s32_state g dd s2 (:int) fam` ASSUME_TAC THENL
   [UNDISCH_TAC `moi_s32_reduced g dd s2 fam` THEN SIMP_TAC[moi_s32_reduced]; ALL_TAC] THEN
  SUBGOAL_THEN `pairwise DISJOINT (fam:(real^3->bool)->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `moi_s32_state g dd s2 (:int) fam` THEN SIMP_TAC[moi_s32_state]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. ?c j j'. c IN fam /\ c SUBSET moi_s32_lvl g dd i /\ pl_annulus_with_ends c j j' /\
                 c INTER moi_s32_evens s2 = j UNION j' /\
                 moi_s32_ess s2 (&2 * i) j /\ moi_s32_ess s2 (&2 * i + &2) j'`
  MP_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC MOI_S3ST_BRIDGE_EXISTS THEN
    MAP_EVERY EXISTS_TAC [`v:real^3->bool`; `pp:int->real^3`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `bb:int->real^3->bool` (X_CHOOSE_THEN `ja:int->real^3->bool`
    (X_CHOOSE_THEN `jb:int->real^3->bool` (LABEL_TAC "br")))) THEN
  SUBGOAL_THEN `separates_in (moi_s32_open g) (moi_s32_set g s2 (IMAGE bb (:int)))
                             {(g:real^3->real^3) moi_s32_qlo} {g moi_s32_qhi}`
  ASSUME_TAC THENL
   [USE_THEN "lim" (MATCH_MP_TAC o MATCH_MP MOI_S3ST_PHASE1) THEN
    MAP_EVERY EXISTS_TAC [`v:real^3->bool`; `pp:int->real^3`; `dd:int->real^3->bool`;
                          `fam:(real^3->bool)->bool`; `ja:int->real^3->bool`;
                          `jb:int->real^3->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!i. ?w. w IN components (frontier ((s2:int->real^3->bool) (&2 * i)) DIFF
                                         ((jb:int->real^3->bool) (i - &1) UNION ja i))`
  MP_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                   `dd:int->real^3->bool`; `s2:int->real^3->bool`; `fam:(real^3->bool)->bool`;
                   `bb:int->real^3->bool`; `ja:int->real^3->bool`; `jb:int->real^3->bool`;
                   `i:int`] MOI_S3ST_PH2_COMPS) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN DISCH_THEN(X_CHOOSE_TAC `w0:int->real^3->bool`) THEN
  MP_TAC(MATCH_MP MOI_S3ST_PHASE2 (ASSUME (moi_n3 MOI_S32_LIMIT))) THEN
  DISCH_THEN(MP_TAC o SPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                             `dd:int->real^3->bool`; `s2:int->real^3->bool`;
                             `fam:(real^3->bool)->bool`; `bb:int->real^3->bool`;
                             `ja:int->real^3->bool`; `jb:int->real^3->bool`;
                             `w0:int->real^3->bool`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MAP_EVERY EXISTS_TAC [`\i. closure ((w0:int->real^3->bool) i)`; `bb:int->real^3->bool`;
                        `\i. (jb:int->real^3->bool) (i - &1)`; `ja:int->real^3->bool`] THEN
  REWRITE_TAC[moi_s32_chain; INT_ARITH `(i + &1) - &1:int = i`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `i:int` THEN
    MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                   `dd:int->real^3->bool`; `s2:int->real^3->bool`; `fam:(real^3->bool)->bool`;
                   `bb:int->real^3->bool`; `ja:int->real^3->bool`; `jb:int->real^3->bool`;
                   `i:int`; `(w0:int->real^3->bool) i`] MOI_S3ST_PIECE_FACTS) THEN
    ASM_SIMP_TAC[];
    MAP_EVERY X_GEN_TAC [`i:int`; `k:int`] THEN DISCH_TAC THEN
    UNDISCH_TAC `pairwise DISJOINT (fam:(real^3->bool)->bool)` THEN
    REWRITE_TAC[pairwise] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN
    MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                   `dd:int->real^3->bool`; `s2:int->real^3->bool`; `fam:(real^3->bool)->bool`;
                   `bb:int->real^3->bool`; `ja:int->real^3->bool`; `jb:int->real^3->bool`]
      MOI_S3ST_BB_INJ) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPECL [`i:int`; `k:int`]) THEN
    ASM_REWRITE_TAC[]]);;

